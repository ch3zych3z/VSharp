namespace VSharp.Core

open System
open System.Reflection
open System.Collections.Generic
open FSharpx.Collections
open VSharp
open VSharp.Core

// ------------------------------------------------- Type mocks -------------------------------------------------

[<StructuralEquality; NoComparison>]
type functionResultConstantSource = {mock : MethodMock; callIndex : int; concreteThis : concreteHeapAddress; args : term list}
with
    interface ISymbolicConstantSource with
        override x.TypeOfLocation = x.mock.Method.ReturnType
        override x.SubTerms = []
        override x.Time = VectorTime.zero
    override x.ToString() =
        let args = x.args |> List.map toString |> join ", "
        $"{x.mock.Method.Name}({args}):{x.callIndex}"

and MethodMock(method : IMethod, typeMock : ITypeMock) =
    let mutable callIndex = 0
    let callResults = ResizeArray<term>()

    member x.Method : IMethod = method
    member x.Type : ITypeMock = typeMock
    interface IMethodMock with
        override x.BaseMethod =
            match method.MethodBase with
            | :? MethodInfo as mi -> mi
            | _ -> __notImplemented__()

        override x.Call concretizedThis args =
            let returnType = method.ReturnType
            if returnType = typeof<Void> then None
            else
                let src : functionResultConstantSource = {mock = x; callIndex = callIndex; concreteThis = concretizedThis; args = args}
                let result = Memory.makeSymbolicValue src (toString src) returnType
                callIndex <- callIndex + 1
                callResults.Add result
                Some result

        override x.GetImplementationClauses() = callResults.ToArray()

    member private x.SetIndex idx = callIndex <- idx
    member private x.SetClauses clauses =
        callResults.Clear()
        callResults.AddRange clauses

    member internal x.Copy(newTypeMock : ITypeMock) =
        let result = MethodMock(method, newTypeMock)
        result.SetIndex callIndex
        result.SetClauses callResults
        result

type TypeMock private (supertypes : Type seq, methodMocks : IDictionary<IMethod, MethodMock>) =
    do
        if supertypes |> Seq.exists (fun s -> s.ContainsGenericParameters) then
            __insufficientInformation__ "Mocks of generic types are not completely supported yet..."

    let uid = Guid.NewGuid()
    new(supertypes) = TypeMock(supertypes, Dictionary<IMethod, MethodMock>())
    interface ITypeMock with
        override x.Name =
            // TODO: generate prettier name without GUIDs
            let supertypeNames = supertypes |> Seq.map (fun t -> t.Name) |> join "_"
            $"Mock_{supertypeNames}_{uid}"
        override x.SuperTypes = supertypes
        override x.IsValueType = supertypes |> Seq.exists (fun t -> t = typeof<ValueType> || t.IsValueType)
        override x.MethodMock m =
            Dict.getValueOrUpdate methodMocks m (fun () -> MethodMock(m, x)) :> IMethodMock
        override x.MethodMocks with get() = methodMocks.Values |> Seq.cast<_>
        override x.Copy() = x.WithSupertypes supertypes
    override x.ToString() = (x :> ITypeMock).Name
    member x.WithSupertypes(supertypes' : Type seq) =
        let newMethods = Dictionary<_,_>()
        let result = TypeMock(supertypes', newMethods)
        methodMocks |> Seq.iter (fun kvp -> newMethods.Add(kvp.Key, kvp.Value.Copy(result)))
        result


// ------------------------------------------------- Type solver core -------------------------------------------------

type typeConstraints = { supertypes : Type list; subtypes : Type list; notSubtypes : Type list; notSupertypes : Type list; mock : ITypeMock option }

type typeSolvingResult =
    | TypeSat of typeModel
    | TypeUnsat

module TypeSolver =
    type private substitution = pdict<Type, symbolicType>

    let rec private enumerateNonAbstractSupertypes predicate (typ : Type) =
        if typ = null || typ.IsAbstract then []
        else
            let supertypes = enumerateNonAbstractSupertypes predicate typ.BaseType
            if predicate typ then typ::supertypes else supertypes

    let private enumerateTypes (supertypes : Type list) (mock : Type list -> ITypeMock) validate (assemblies : Assembly seq) =
        seq {
            let mutable sure = true
            yield! supertypes |> Seq.filter validate |> Seq.map ConcreteType
            let assemblies =
                match supertypes |> Seq.tryFind (fun u -> u.IsNotPublic) with
                | Some u -> [u.Assembly] :> _ seq
                | None -> sure <- false; assemblies
            for assembly in assemblies do
                yield! assembly.GetExportedTypes() |> Seq.filter validate |> Seq.map ConcreteType

                if supertypes |> Seq.forall (fun t -> (t.IsPublic || t.IsNestedPublic) && ((*TODO: remove it if generic mocks are supported*)t.ContainsGenericParameters |> not)) then
                    yield mock supertypes |> MockType

        }

    let private enumerateNonAbstractTypes supertypes mock validate (assemblies : Assembly seq) =
        enumerateTypes supertypes mock (fun t -> not t.IsAbstract && validate t) assemblies

    let private isContradicting (c : typeConstraints) =
        // X <: u and u <: t and X </: t
        c.supertypes |> List.exists (fun u -> c.notSupertypes |> List.exists u.IsAssignableTo)
        || // u <: X and t <: u and t </: X
        c.subtypes |> List.exists (fun u -> c.notSubtypes |> List.exists u.IsAssignableFrom)
        || // u <: X and X <: t and u </: t
        c.subtypes |> List.exists (fun u -> c.supertypes |> List.exists (u.IsAssignableTo >> not))
        || // No multiple inheritance -- X <: u and X <: t and u </: t and t </: u and t, u are classes
        c.supertypes |> List.exists (fun u -> c.supertypes |> List.exists (fun t -> u.IsClass && t.IsClass && (not <| u.IsAssignableTo t) && (not <| u.IsAssignableFrom t)))
        || // u </: X and X <: u when u is sealed
        c.supertypes |> List.exists (fun u -> u.IsSealed && c.notSubtypes |> List.contains u)

    let rec private substitute (subst : substitution) (t : Type) =
        if not t.IsGenericType then t
        elif t.IsGenericParameter then
            if PersistentDict.contains t subst then
                match subst.[t] with
                | ConcreteType u -> u
                | _ -> t
            else t
//        elif t.HasElementType then
//            let e' = t.GetElementType() |> substPartially subst
        else
            let args = t.GetGenericArguments()
            let args' = args |> Array.map (substitute subst)
            if Array.forall2 (=) args args' then t
            else t.GetGenericTypeDefinition().MakeGenericType(args')

    let private satisfiesTypeParameterConstraints (parameter : Type) subst (t : Type) =
        let (&&&) = Microsoft.FSharp.Core.Operators.(&&&)
        let isReferenceType = parameter.GenericParameterAttributes &&& GenericParameterAttributes.ReferenceTypeConstraint = GenericParameterAttributes.ReferenceTypeConstraint
        let isNotNullableValueType = parameter.GenericParameterAttributes &&& GenericParameterAttributes.NotNullableValueTypeConstraint = GenericParameterAttributes.NotNullableValueTypeConstraint
        let hasDefaultConstructor = parameter.GenericParameterAttributes &&& GenericParameterAttributes.DefaultConstructorConstraint = GenericParameterAttributes.NotNullableValueTypeConstraint
        // TODO: check 'managed' constraint
        (not t.ContainsGenericParameters) &&
        (not isReferenceType || not t.IsValueType) &&
        (not isNotNullableValueType || (t.IsValueType && Nullable.GetUnderlyingType t = null)) &&
        (not hasDefaultConstructor || t.GetConstructor(Type.EmptyTypes) <> null) &&
        (parameter.GetGenericParameterConstraints() |> Array.forall (substitute subst >> t.IsAssignableTo))

    let private satisfiesConstraints (constraints : typeConstraints) subst (candidate : Type) =
        // TODO: need to find subst to generic parameters satisfying constraints
        constraints.subtypes |> List.forall (substitute subst >> candidate.IsAssignableFrom) &&
        constraints.supertypes |> List.forall (substitute subst >> candidate.IsAssignableTo) &&
        constraints.notSubtypes |> List.forall (substitute subst >> candidate.IsAssignableFrom >> not) &&
        constraints.notSupertypes |> List.forall (substitute subst >> candidate.IsAssignableTo >> not)

    let private typeCandidates getMock subst constraints =
        match constraints.supertypes |> List.tryFind (fun t -> t.IsSealed) with
        | Some t ->
            if TypeUtils.isDelegate t then
                // Forcing mock usage for delegate types
                let mock = getMock constraints.mock constraints.supertypes
                MockType mock |> Seq.singleton
            else
                ConcreteType t |> Seq.singleton
        | _ ->
            let validate = satisfiesConstraints constraints subst
            match constraints.subtypes with
            | [] -> enumerateNonAbstractTypes constraints.supertypes (getMock constraints.mock) validate (AssemblyManager.GetAssemblies())
            | t :: _ -> enumerateNonAbstractSupertypes validate t |> Seq.map ConcreteType

    let private typeParameterCandidates getMock subst (parameter : Type, constraints : typeConstraints) =
        let validate typ = satisfiesTypeParameterConstraints parameter subst typ
        let supertypes = constraints.supertypes |> List.map (substitute subst)
        enumerateTypes supertypes getMock validate (AssemblyManager.GetAssemblies())

    let rec private collectTypeVariables (acc : Type list) (typ : Type) =
        if typ.IsGenericParameter then
            if List.contains typ acc then acc
            else
                typ.GetGenericParameterConstraints() |> Array.fold collectTypeVariables (typ::acc)
        elif typ.HasElementType then
            collectTypeVariables acc (typ.GetElementType())
        elif not typ.IsGenericType then acc
        else
            typ.GetGenericArguments() |> Array.fold collectTypeVariables acc

    let private getMock (typeMocks : IDictionary<Type list, ITypeMock>) (current : ITypeMock option) (supertypes : Type list) =
        let supertypes = supertypes |> List.sortBy (fun t -> {t=t})
        Dict.getValueOrUpdate typeMocks supertypes (fun () ->
            match current with
            | Some (:? TypeMock as current)  ->
                let newMock = current.WithSupertypes supertypes
                typeMocks.Add(supertypes, newMock)
                newMock :> ITypeMock
            | Some _  -> __unreachable__()
            | None -> TypeMock(supertypes) :> ITypeMock)

    let private generateConstraints (model : model) (state : state) =
        match model with
        | StateModel _ ->
            let mocks = Dictionary<term, ITypeMock>()
            let supertypeConstraints = Dictionary<term, List<Type>>()
            let subtypeConstraints = Dictionary<term, List<Type>>()
            let notSupertypeConstraints = Dictionary<term, List<Type>>()
            let notSubtypeConstraints = Dictionary<term, List<Type>>()
            let addresses = HashSet<term>()

            let add dict address typ =
                match model.Eval address with
                | {term = ConcreteHeapAddress addr} when addr <> VectorTime.zero ->
                    addresses.Add address |> ignore
                    let list = Dict.getValueOrUpdate dict address (fun () -> List<_>())
                    if not <| list.Contains typ then
                        list.Add typ
                | {term = ConcreteHeapAddress _} -> ()
                | term -> internalfailf "Unexpected address %O in subtyping constraint!" term

            PC.toSeq state.pc |> Seq.iter (term >> function
                | Constant(_, TypeCasting.TypeSubtypeTypeSource _, _) -> internalfail "TypeSolver is not fully implemented"
                | Constant(_, TypeCasting.RefSubtypeTypeSource(address, typ), _) -> add supertypeConstraints address typ
                | Constant(_, TypeCasting.TypeSubtypeRefSource(typ, address), _) -> add subtypeConstraints address typ
                | Constant(_, TypeCasting.RefSubtypeRefSource _, _) -> internalfail "TypeSolver is not fully implemented"
                | Negation({term = Constant(_, TypeCasting.TypeSubtypeTypeSource _, _)})-> internalfail "TypeSolver is not fully implemented"
                | Negation({term = Constant(_, TypeCasting.RefSubtypeTypeSource(address, typ), _)}) -> add notSupertypeConstraints address typ
                | Negation({term = Constant(_, TypeCasting.TypeSubtypeRefSource(typ, address), _)}) -> add notSubtypeConstraints address typ
                | Negation({term = Constant(_, TypeCasting.RefSubtypeRefSource _, _)}) -> internalfail "TypeSolver is not fully implemented"
                | _ -> ())
            let toList (d : Dictionary<term, List<Type>>) addr =
                let l = Dict.tryGetValue d addr null
                if l = null then [] else List.ofSeq l
            let addresses = List.ofSeq addresses
            let constraints =
                addresses
                |> Seq.map (fun addr ->
                    {supertypes = toList supertypeConstraints addr
                     subtypes = toList subtypeConstraints addr
                     notSupertypes = toList notSupertypeConstraints addr
                     notSubtypes = toList notSubtypeConstraints addr
                     mock = if mocks.ContainsKey addr then Some mocks.[addr] else None})
                |> List.ofSeq
            addresses, constraints
        | PrimitiveModel _ -> __unreachable__()

    let private generateGenericConstraints (typeVars : Type list) =
        // TODO: divide dependent constraints into groups by dependence
        let isIndependent (t : Type) =
            t.GetGenericParameterConstraints()
            |> Array.exists (fun c -> c.IsGenericParameter)
            |> not
        let parameterConstraints (t : Type) =
            let constraints = {
                supertypes = t.GetGenericParameterConstraints() |> List.ofArray
                notSupertypes = []
                subtypes = []
                notSubtypes = []
                mock = None
            }
            t, constraints
        let indep, dep = List.partition isIndependent typeVars
        let getConstraints = List.map parameterConstraints
        getConstraints indep, [getConstraints dep]

    let private refineMock getMock constraints mock =
        if List.isEmpty constraints.subtypes |> not || isContradicting constraints then
            None
        else
            Some (getMock (Some mock) constraints.supertypes)

    let private refineModel getMock (typeModel : typeModel) addresses typesConstraints =
        let addressesTypes = typeModel.addressesTypes

        let refinable, rest =
            List.zip addresses typesConstraints
            |> List.partition (fun (address, _) -> addressesTypes.ContainsKey address)

        List.iter (fun (address, constraints) ->
            let types = addressesTypes[address]
            let refineType symbolicType =
                match symbolicType with
                | ConcreteType typ ->
                    if satisfiesConstraints constraints (pdict.Empty()) typ then
                        Some symbolicType
                    else None
                | MockType mock ->
                    refineMock getMock constraints mock
                    |> Option.bind (MockType >> Some)
            // TODO: do it lazy way by mock modification
            addressesTypes[address] <- Seq.choose refineType types
            ) refinable
        rest

    let private solveConstraints typesConstraints (getCandidates : _ -> seq<symbolicType>) =
        let rec solveConstraintsRec = function
            | [] -> Some []
            | constraints :: rest ->
                let candidates = getCandidates constraints
                match (Seq.tryHead candidates, solveConstraintsRec rest) with
                | Some _, Some candidatesRest -> Some (candidates :: candidatesRest)
                | _ -> None
        solveConstraintsRec typesConstraints

    let private solveTypesConstraints getMock typesConstraints subst =
        typeCandidates getMock subst
        |> solveConstraints typesConstraints

    let private solveGenericConstraints getMock indTypesConstraints subst =
        let indCandidates =
            typeParameterCandidates getMock subst
            |> solveConstraints indTypesConstraints
        match indCandidates with
        | None -> None
        | Some candidates ->
            let candidates = List.map Seq.head candidates
            let types, _  = List.unzip indTypesConstraints
            List.zip types candidates
            |> PersistentDict.ofSeq
            |> Some

    let private solve (getMock : ITypeMock option -> Type list -> ITypeMock) (inputConstraints : typeConstraints list) (typeParameters : Type[]) =
        if List.exists isContradicting inputConstraints then None
        else
            let decodeTypeSubst (subst : substitution) =
                let getSubst (typ : Type) =
                    if typ.IsGenericParameter then PersistentDict.find subst typ else ConcreteType typ
                Array.map getSubst typeParameters

            let typeVars = typeParameters |> Array.fold collectTypeVariables []
            let typeVars = inputConstraints |> List.fold (fun acc constraints ->
                            let acc = constraints.supertypes |> List.fold collectTypeVariables acc
                            let acc = constraints.subtypes |> List.fold collectTypeVariables acc
                            let acc = constraints.notSupertypes |> List.fold collectTypeVariables acc
                            let acc = constraints.notSubtypes |> List.fold collectTypeVariables acc
                            acc) typeVars

            let indGC, depGC = generateGenericConstraints typeVars
            let subst = solveGenericConstraints (getMock None) indGC (pdict.Empty())
            match subst with
            | None -> None
            | Some subst ->
                 // TODO: do solving dependent generic constraints in more complex way
                 let depGC = List.concat depGC
                 let rec solveTypesVarsRec subst = function
                     | [] ->
                         match solveTypesConstraints getMock inputConstraints subst with
                         | None -> None
                         | Some candidates -> Some (candidates, decodeTypeSubst subst)
                     | (t, c) :: rest ->
                         let candidates = typeParameterCandidates (getMock None) subst (t, c)
                         let rec tryCandidates subst = function
                             | Seq.Empty -> None
                             | Seq.Cons(cand, cands) ->
                                 match solveTypesVarsRec (PersistentDict.add t cand subst) rest with
                                 | None -> tryCandidates subst cands
                                 | x -> x
                         tryCandidates subst candidates

                 solveTypesVarsRec subst depGC

    let solveMethodParameters (typeModel : typeModel) (m : IMethod) =
        let declaringType = m.DeclaringType
        let methodBase = m.MethodBase
        let needToSolve =
            declaringType.IsGenericType && Array.isEmpty typeModel.classesParams
            || methodBase.IsGenericMethod && Array.isEmpty typeModel.methodsParams
        if not needToSolve then Some(typeModel.classesParams, typeModel.methodsParams)
        else
            let typeGenericParameters = declaringType.GetGenericArguments() |> Array.filter (fun t -> t.IsGenericParameter)
            let methodGenericParameters = if m.IsConstructor then Array.empty else m.GenericArguments |> Array.filter (fun t -> t.IsGenericParameter)
            let solvingResult = solve (getMock (Dictionary())) [] (Array.append typeGenericParameters methodGenericParameters)
            match solvingResult with
            | Some (_, typeParams) ->
                let classParams, methodParams = Array.splitAt typeGenericParameters.Length typeParams
                typeModel.classesParams <- classParams
                typeModel.methodsParams <- methodParams
                Some(classParams, methodParams)
            | None -> None

    let solveTypes (model : model) (state : state) =
        let dictContainsEmpty (dict: Dictionary<_, seq<_>>) =
            let mutable isEmpty = false
            for entry in dict do
                isEmpty <- isEmpty || (Seq.isEmpty entry.Value)
            isEmpty

        let m = CallStack.stackTrace state.stack |> List.last
        let declaringType = m.DeclaringType
        let typeGenericArguments = declaringType.GetGenericArguments()
        let methodGenericArguments = if m.IsConstructor then Array.empty else m.GenericArguments
        let addresses, constraints = generateConstraints model state
        match model with
        | StateModel(modelState, typeModel) ->
            let getMock = getMock state.typeMocks
            let addresses, constraints =
                refineModel getMock typeModel addresses constraints
                |> List.unzip
            if dictContainsEmpty typeModel.addressesTypes then TypeUnsat else
                match solve getMock constraints (Array.append typeGenericArguments methodGenericArguments) with
                | None -> TypeUnsat
                | Some (candidates, typeParams) ->
                    // TODO: do not use refineTypes, fix boxedLocations usage for PrimitiveModel
                    let refineTypes addr types =
                         match Seq.tryHead types with
                         | Some (ConcreteType t) ->
                             if t.IsValueType then
                                 let value = makeDefaultValue t
                                 modelState.boxedLocations <- PersistentDict.add addr value modelState.boxedLocations
                         | _ -> ()
                    let getConcreteAddress addr =
                        match model.Eval addr with
                        | {term = ConcreteHeapAddress addr} -> addr
                        | {term = HeapRef({term = ConcreteHeapAddress addr}, _)} -> addr
                        | _-> __unreachable__()
                    List.iter2
                        (fun addr types -> typeModel.addressesTypes.Add(addr, types); refineTypes (getConcreteAddress addr) types)
                        addresses
                        candidates
                    let classParams, methodParams = Array.splitAt typeGenericArguments.Length typeParams
                    typeModel.classesParams <- classParams
                    typeModel.methodsParams <- methodParams

                    for entry in typeModel.addressesTypes do
                        let addr, types = entry.Key, entry.Value
                        modelState.allocatedTypes <- PersistentDict.add (getConcreteAddress addr) (Seq.head types) modelState.allocatedTypes
                    TypeSat typeModel
        | PrimitiveModel _ -> __unreachable__()

    let checkSatWithSubtyping state =
        match SolverInteraction.checkSat state with
        | SolverInteraction.SmtSat ({mdl = StateModel(modelState, _) as model} as satInfo) ->
            try
                match solveTypes model state with
                | TypeUnsat -> SolverInteraction.SmtUnsat {core = Array.empty}
                | TypeSat typeModel ->
                    SolverInteraction.SmtSat {satInfo with mdl = StateModel(modelState, typeModel)}
            with :? InsufficientInformationException as e ->
                SolverInteraction.SmtUnknown e.Message
        | result -> result

    let getCallVirtCandidates state (thisRef : heapAddress) (thisType: Type) (ancestorMethod : IMethod) =
        match thisRef with
        | {term = HeapRef({term = ConcreteHeapAddress thisAddress}, _)} when VectorTime.less VectorTime.zero thisAddress ->
            thisAddress, [state.allocatedTypes.[thisAddress]] :> seq<symbolicType>
        | _ ->
            match state.model with
            | StateModel (_, typeModel) as model ->
                match model.Eval thisRef with
                | {term = HeapRef({term = ConcreteHeapAddress thisAddress}, _)} ->
                    let addresses, inputConstraints = generateConstraints state.model state
                    let constraints =
                        match List.tryFindIndex ((=)thisRef) addresses with
                        | Some index -> inputConstraints[index]
                        | None -> {
                                subtypes = []
                                supertypes = []
                                notSubtypes = []
                                notSupertypes = []
                                mock = None
                            }
                    let constraints = [{ constraints with supertypes = thisType :: constraints.supertypes }]

                    let checkOverrides = function
                        | ConcreteType t ->
                            Reflection.canOverrideMethod t (ancestorMethod.MethodBase :?> MethodInfo)
                        | MockType _ -> true

                    let candidates =
                        match refineModel (getMock state.typeMocks) typeModel [thisRef] constraints with
                        | [] -> typeModel[thisRef].Value
                        | (_, constraints) :: _ ->
                            match solve (getMock state.typeMocks) [constraints] [||] with
                            | Some (candidates :: _, _) ->
                                typeModel.addressesTypes[thisRef] <- candidates
                                candidates
                            | _ -> Seq.empty

                    let overridingMethods = Seq.filter checkOverrides candidates

                    thisAddress, overridingMethods
                | _ -> __unreachable__()
            | PrimitiveModel _ -> __unreachable__()
