namespace VSharp.Core

open System
open System.Collections.Generic

open VSharp

type typeStorage private (conditions, constraints, addressesTypes, typeMocks, classesParams, methodsParams) =
    let mutable classesParams = classesParams
    let mutable methodsParams = methodsParams
    let mutable conditions = conditions

    new() =
        let constraints = typesConstraints()
        let addressesTypes = Dictionary<term, candidates>()
        let typeMocks = Dictionary<Type list, ITypeMock>()
        let classesParams : symbolicType[] = Array.empty
        let methodsParams : symbolicType[] = Array.empty
        let conditions = Conditions.empty
        typeStorage(conditions, constraints, addressesTypes, typeMocks, classesParams, methodsParams)

    member x.Constraints with get() = constraints
    member x.AddressesTypes with get() = addressesTypes
    member x.TypeMocks with get() = typeMocks
    member x.ClassesParams
        with get() = classesParams
        and set newClassesParams =
            classesParams <- newClassesParams
    member x.MethodsParams
        with get() = methodsParams
        and set newMethodsParams =
            methodsParams <- newMethodsParams

    member x.Copy() =
        let newConstraints = constraints.Copy()
        let newTypeMocks = Dictionary<Type list, ITypeMock>()
        let newAddressesTypes = Dictionary()
        for entry in addressesTypes do
            let address = entry.Key
            let addressCandidates = entry.Value
            let changeMock (m : ITypeMock) =
                let superTypes = Seq.toList m.SuperTypes
                let mock = ref (EmptyTypeMock() :> ITypeMock)
                if newTypeMocks.TryGetValue(superTypes, mock) then mock.Value
                else
                    let newMock = m.Copy()
                    newTypeMocks.Add(superTypes, newMock)
                    newMock
            let newCandidates = addressCandidates.Copy(changeMock)
            newAddressesTypes.Add(address, newCandidates)
        typeStorage(conditions, newConstraints, newAddressesTypes, newTypeMocks, classesParams, methodsParams)

    member x.AddConstraint address typeConstraint =
        constraints.Add address typeConstraint

    member x.AddSupertypeConstraint address supertype =
        constraints.AddSuperType address supertype

    member x.AddConditions newConditions =
        let equalityConstraints = Dictionary<term, HashSet<Type>>()
        let supertypeConstraints = Dictionary<term, HashSet<Type>>()
        let subtypeConstraints = Dictionary<term, HashSet<Type>>()
        let inequalityConstraints = Dictionary<term, HashSet<Type>>()
        let notSupertypeConstraints = Dictionary<term, HashSet<Type>>()
        let notSubtypeConstraints = Dictionary<term, HashSet<Type>>()
        let addresses = ResizeArray<term>()

        // Creating type constraints from path condition
        let add (dict : Dictionary<term, HashSet<Type>>) address typ =
            let types =
                let types = ref null
                if dict.TryGetValue(address, types) then types.Value
                else
                    let typesSet = HashSet<_>()
                    dict.Add(address, typesSet)
                    addresses.Add address
                    typesSet
            types.Add typ |> ignore

        let parseConstraints notParsed condition =
            let mutable isParsed = true
            match condition.term with
            | Constant(_, TypeCasting.TypeSubtypeTypeSource _, _) ->
                internalfail "TypeSolver is not fully implemented"
            | Constant(_, TypeCasting.RefEqTypeSource(address, typ), _) ->
                add equalityConstraints address typ
            | Constant(_, TypeCasting.RefSubtypeTypeSource(address, typ), _) ->
                add supertypeConstraints address typ
            | Constant(_, TypeCasting.TypeSubtypeRefSource(typ, address), _) ->
                add subtypeConstraints address typ
            | Constant(_, TypeCasting.RefSubtypeRefSource _, _) ->
                internalfail "TypeSolver is not fully implemented"
            | Negation({term = Constant(_, TypeCasting.TypeSubtypeTypeSource _, _)}) ->
                internalfail "TypeSolver is not fully implemented"
            | Negation({term = Constant(_, TypeCasting.RefSubtypeTypeSource(address, typ), _)}) ->
                add notSupertypeConstraints address typ
            | Negation({term = Constant(_, TypeCasting.RefEqTypeSource(address, typ), _)}) ->
                add inequalityConstraints address typ
            | Negation({term = Constant(_, TypeCasting.TypeSubtypeRefSource(typ, address), _)}) ->
                add notSubtypeConstraints address typ
            | Negation({term = Constant(_, TypeCasting.RefSubtypeRefSource _, _)}) ->
                internalfail "TypeSolver is not fully implemented"
            | _ -> isParsed <- false

            if isParsed then
                conditions <- Conditions.add conditions condition
                notParsed
            else condition :: notParsed

        let notParsed = List.fold parseConstraints [] newConditions

        let toList (d : Dictionary<term, HashSet<Type>>) address =
            let set = ref null
            if d.TryGetValue(address, set) then List.ofSeq set.Value
            else List.empty
        // Adding type constraints
        for address in addresses do
            let typeConstraints =
                typeConstraints.Create
                    (toList equalityConstraints address)
                    (toList supertypeConstraints address)
                    (toList subtypeConstraints address)
                    (toList inequalityConstraints address)
                    (toList notSupertypeConstraints address)
                    (toList notSubtypeConstraints address)
            constraints.Add address typeConstraints

        notParsed

    member x.Item
        with get (address : term) =
            let t = ref (candidates.Empty())
            if addressesTypes.TryGetValue(address, t) then Some t.Value
            else None
        and set (address : term) (candidates : candidates) =
            assert(candidates.IsEmpty |> not)
            addressesTypes[address] <- candidates

    member x.IsValid with get() = addressesTypes.Count = constraints.Count

    interface ITypeConstraints with
        member x.AddConditions conditions = x.AddConditions conditions
        member x.Copy() = x.Copy()
        member x.Conditions = conditions
        member x.AddConstraint address typeConstraint = x.AddConstraint address typeConstraint
        member x.AddSupertypeConstraint address supertype = x.AddSupertypeConstraint address supertype
        member x.AddressesTypes = x.AddressesTypes
        member x.ClassesParams
            with get() = x.ClassesParams
            and set value = x.ClassesParams <- value
        member x.Constraints = x.Constraints
        member x.IsValid = x.IsValid
        member x.MethodsParams
            with get() = x.MethodsParams
            and set value = x.MethodsParams <- value
        member x.TypeMocks with get() = x.TypeMocks
        member x.Item
            with get address = x[address]
        member x.Item with set address value = x[address] <- value
