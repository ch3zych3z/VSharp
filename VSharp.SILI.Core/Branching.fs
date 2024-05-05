namespace VSharp.Core

open VSharp
open Memory

module internal Branching =

    let checkSat state = SolverInteraction.checkSatWithSubtyping state

    let commonGuardedStatedApplyk f state term mergeResults k =
        match term.term with
        | Union gvs ->
            let filterUnsat (g, v) k =
                let pc = state.pc.Copy()
                pc.AddCondition(g)
                if pc.IsFalse then k None
                else Some (pc, v) |> k
            Cps.List.choosek filterUnsat gvs (fun pcs ->
            match pcs with
            | [] -> k []
            | (pc, v)::pcs ->
                let copyState (pc, v) k = f (state.Copy pc) v k
                Cps.List.mapk copyState pcs (fun results ->
                    state.pc <- pc
                    f state v (fun r ->
                    r::results |> mergeResults |> k)))
        | _ -> f state term (List.singleton >> k)
    let guardedStatedApplyk f state term k = commonGuardedStatedApplyk f state term State.mergeResults k
    let guardedStatedApply f state term = guardedStatedApplyk (Cps.ret2 f) state term id

    let guardedStatedMap mapper state term =
        commonGuardedStatedApplyk (fun state term k -> mapper state term |> k) state term id id

    let mutable branchesReleased = false

    let commonStatedConditionalExecutionk (state : state) conditionInvocation thenBranch elseBranch merge2Results k =
        let execution thenState elseState condition k =
            assert (condition <> True() && condition <> False())
            thenBranch thenState (fun thenResult ->
            elseBranch elseState (fun elseResult ->
            merge2Results thenResult elseResult |> k))
        conditionInvocation state (fun (condition, conditionState) ->
        let pc = state.pc
        assert(pc.Conditions |> conjunction |> state.model.Eval |> isTrue)
        let evaled = state.model.Eval condition
        let notCondition = !!condition
        if isTrue evaled then
            assert(state.model.Eval notCondition |> isFalse)
            let elsePc = pc.Copy()
            let thenPc = pc.Copy()
            elsePc.AddCondition(notCondition)
            if elsePc.IsFalse then
                thenBranch conditionState (List.singleton >> k)
            elif not branchesReleased then
                conditionState.pc <- elsePc
                match checkSat conditionState with
                | SolverInteraction.SmtUnsat _ ->
                    conditionState.pc <- thenPc
                    conditionState.pc.AddCondition condition
                    TypeSolver.refineTypes conditionState
                    thenBranch conditionState (List.singleton >> k)
                | SolverInteraction.SmtUnknown _ ->
                    conditionState.pc <- thenPc
                    conditionState.pc.AddCondition condition
                    TypeSolver.refineTypes conditionState
                    thenBranch conditionState (List.singleton >> k)
                | SolverInteraction.SmtSat model ->
                    let thenState = conditionState
                    thenState.pc <- thenPc
                    let elseState = conditionState.Copy elsePc
                    elseState.model <- model.mdl
                    assert(elsePc.Conditions |> conjunction |> elseState.model.Eval |> isTrue)
                    thenState.pc.AddCondition condition
                    TypeSolver.refineTypes thenState
                    execution thenState elseState condition k
            else
                conditionState.pc.AddCondition condition
                thenBranch conditionState (List.singleton >> k)
        elif isFalse evaled then
            assert(state.model.Eval notCondition |> isTrue)
            let thenPc = state.pc.Copy()
            let elsePc = thenPc.Copy()
            thenPc.AddCondition condition
            if thenPc.IsFalse then
                elseBranch conditionState (List.singleton >> k)
            elif not branchesReleased then
                conditionState.pc <- thenPc
                match checkSat conditionState with
                | SolverInteraction.SmtUnsat _ ->
                    conditionState.pc <- elsePc
                    conditionState.pc.AddCondition notCondition
                    TypeSolver.refineTypes conditionState
                    elseBranch conditionState (List.singleton >> k)
                | SolverInteraction.SmtUnknown _ ->
                    conditionState.pc <- elsePc
                    conditionState.pc.AddCondition notCondition
                    TypeSolver.refineTypes conditionState
                    elseBranch conditionState (List.singleton >> k)
                | SolverInteraction.SmtSat model ->
                    let thenState = conditionState
                    let elseState = conditionState.Copy elsePc
                    elsePc.AddCondition notCondition
                    thenState.model <- model.mdl
                    assert(thenPc.Conditions |> conjunction |> thenState.model.Eval |> isTrue)
                    TypeSolver.refineTypes elseState
                    execution thenState elseState condition k
            else
                conditionState.pc <- elsePc
                elsePc.AddCondition notCondition
                elseBranch conditionState (List.singleton >> k)
        else __unreachable__())

    let statedConditionalExecutionWithMergek state conditionInvocation thenBranch elseBranch k =
        commonStatedConditionalExecutionk state conditionInvocation thenBranch elseBranch State.merge2Results k
    let statedConditionalExecutionWithMerge state conditionInvocation thenBranch elseBranch =
        statedConditionalExecutionWithMergek state conditionInvocation thenBranch elseBranch id
