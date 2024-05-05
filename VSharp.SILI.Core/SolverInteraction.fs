namespace VSharp.Core

open System.Collections.Generic
open FSharpx.Collections
open VSharp

module public SolverInteraction =

    type unsatCore() = class end

    type satInfo = {
        mdl : model
        typeConstraints : (term * bool) list
    }
    type unsatInfo = { core : term[] }

    type smtResult =
        | SmtSat of satInfo
        | SmtUnsat of unsatInfo
        | SmtUnknown of string

    type ISolver =
        abstract CheckSat : term -> smtResult

        abstract Check : unit -> smtResult
        abstract Assert : term -> unit
        abstract Push : unit -> unit
        abstract Pop : unit -> unit

        abstract SetMaxBufferSize : int -> unit

    let mutable private solver : ISolver option = None
    let mutable private onSolverStarted : unit -> unit = id
    let mutable private onSolverStopped : unit -> unit = id

    let private unlimitedIterations = -1
    let mutable private maxIterations = unlimitedIterations

    let configureSolver s = solver <- Some s
    let setOnSolverStarted action = onSolverStarted <- action
    let setOnSolverStopped action = onSolverStopped <- action

    let setMaxBufferSize size =
        match solver with
        | Some s -> s.SetMaxBufferSize size
        | None -> ()

    let private checkSatWithCtx state context =
        let formula = state.pc.SolverConditions |> Seq.append context |> conjunction
        match solver with
        | Some s ->
            onSolverStarted()
            let result = s.CheckSat formula
            onSolverStopped()
            result
        | None -> SmtUnknown ""

    let checkSat state =
        checkSatWithCtx state Seq.empty

    let rec private createContext (unequal : HashSet<term * term>) =
        let createCondition (a1, a2) =
            ((a1 === zeroAddress()) &&& (a2 === zeroAddress())) ||| (!!(a1 === a2))
        Seq.map createCondition unequal

    let inline private isIterLimitReached iter = maxIterations <> unlimitedIterations && iter >= maxIterations

    let rec private checkSatInternalHelper currentIter (solver : ISolver) state =
        if isIterLimitReached currentIter then
            SmtUnknown "iteration threshold is reached"
        else
            let result =
                match solver.Check() with
                | SmtSat {mdl = model; typeConstraints = typeConstraints} as satWithModel ->
                    try
                        match TypeSolver.solveTypes model state typeConstraints with
                        | TypeUnsat ->
                            SmtUnsat {core = Array.empty} |> Some
                        | TypeSat ->
                            assert(state.pc.Conditions |> conjunction |> model.Eval |> isTrue)
                            satWithModel |> Some
                        | TypeUnsatWithCore core ->
                            conjunction core |> solver.Assert
                            None
                    with :? InsufficientInformationException as e ->
                        SmtUnknown e.Message |> Some
                | result -> result |> Some
            match result with
            | Some result -> result
            | None -> checkSatInternalHelper (currentIter + 1) solver state

    let private checkSatInternal solver state = checkSatInternalHelper 0 solver state

    let checkSatWithSubtyping (state : state) =
        match TypeSolver.checkInequality state, solver with
        | _, None -> SmtUnknown "no solver were provided"
        | None, _ -> SmtUnsat {core = Array.empty}
        | Some unequal, Some solver ->
            onSolverStarted()
            solver.Push()

            createContext unequal |> conjunction |> solver.Assert
            state.pc.SolverConditions |> conjunction |> solver.Assert
            let result = checkSatInternal solver state

            solver.Pop()
            onSolverStopped()

            result
