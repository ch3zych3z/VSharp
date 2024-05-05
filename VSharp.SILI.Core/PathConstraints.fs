namespace VSharp.Core

open System
open System.Collections.Generic
open VSharp

type ITypeConstraints =
    abstract Constraints : typesConstraints with get
    abstract AddressesTypes : Dictionary<term, candidates> with get
    abstract TypeMocks : Dictionary<Type list, ITypeMock> with get
    abstract ClassesParams : symbolicType array with get, set
    abstract MethodsParams : symbolicType array with get, set
    abstract AddConstraint : term -> typeConstraints -> unit
    abstract AddSupertypeConstraint : term -> Type -> unit
    abstract Item : term -> candidates option with get
    abstract Item : term -> candidates with set
    abstract IsValid : bool with get

    abstract Conditions : conditions
    abstract AddConditions : term list -> term list

    abstract Copy : unit -> ITypeConstraints

type EqualityConstraints private (conditions, notNullAddresses) =

    let mutable conditions = conditions

    new() = EqualityConstraints(Conditions.empty, HashSet<term>())

    member x.MkNotNull(address) = notNullAddresses.Add(address) |> ignore

    member private x.AddCondition(cond) =
        let mutable isParsed = true
        match cond with
        | { term = NotNullAddress(address, _) } ->
            x.MkNotNull(address)
        | _ -> isParsed <- false

        if isParsed then
            conditions <- Conditions.add conditions cond
        isParsed

    member x.AddConditions(constraints) = List.filter (x.AddCondition >> not) constraints

    member x.Conditions with get() = conditions

    member x.Copy() =
        let notNullAddressesCopy = HashSet()
        for address in notNullAddresses do
            notNullAddressesCopy.Add(address) |> ignore

        EqualityConstraints(conditions, notNullAddressesCopy)

type PathConstraints private (
        typeConstraints : ITypeConstraints,
        equalityConstraints : EqualityConstraints,
        logicalConstraints,
        pathCondition
    ) =
    let mutable logicalConstraints = logicalConstraints
    let mutable pathCondition = pathCondition

    let rec parseConjunctions acc conds k =
        match conds with
        | [] -> k acc
        | { term = Conjunction(conds1) } :: conds2 ->
            parseConjunctions acc conds1 (fun conjuncts1 ->
            parseConjunctions conjuncts1 conds2 k)
        | cond :: conds -> parseConjunctions (cond :: acc) conds k

    let addConditions conditions =
        let newLogicalConstraints =
            conditions
            |> equalityConstraints.AddConditions
            |> typeConstraints.AddConditions
        logicalConstraints <- List.fold Conditions.add logicalConstraints newLogicalConstraints
        pathCondition <- List.fold Conditions.add pathCondition conditions

    new(typeConstraints : ITypeConstraints) =
        PathConstraints(typeConstraints, EqualityConstraints(), Conditions.empty, Conditions.empty)

    member x.AddCondition(cond) = parseConjunctions List.empty (List.singleton cond) addConditions

    member x.Conditions with get() =
        seq {
            yield! Conditions.toSeq equalityConstraints.Conditions
            yield! Conditions.toSeq typeConstraints.Conditions
            yield! Conditions.toSeq logicalConstraints
        }

    member x.SolverConditions with get() =
        seq {
            yield! Conditions.toSeq equalityConstraints.Conditions
            yield! Conditions.toSeq logicalConstraints
        }

    member x.TypeConstraints with get() = typeConstraints

    member x.PathCondition with get() = pathCondition

    member x.LogicalConstraints with get() = logicalConstraints

    member x.IsFalse with get() =
        Conditions.isFalse logicalConstraints

    member x.IsEmpty with get() =
        Conditions.isEmpty equalityConstraints.Conditions
        && Conditions.isEmpty typeConstraints.Conditions
        && Conditions.isEmpty logicalConstraints

    // member x.Union (conditions : seq<term>) =
    //     // TODO: make separate Union method for every constraint kind
    //     Seq.iter x.AddCondition conditions

    member x.Copy() =
        PathConstraints(
            typeConstraints.Copy(),
            equalityConstraints.Copy(),
            logicalConstraints,
            pathCondition
        )
