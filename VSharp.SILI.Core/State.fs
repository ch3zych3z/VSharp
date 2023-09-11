namespace VSharp.Core

open System
open System.Collections.Generic
open System.Reflection
open VSharp
open VSharp.Core
open VSharp.Core.GenericUtils
open VSharp.Utils

type typeVariables = mappedStack<typeWrapper, Type> * Type list stack

type stackBufferKey = concreteHeapAddress

type concreteMemorySource =
    | HeapSource
    | StructFieldSource of concreteMemorySource * fieldId
    | BoxedLocationSource of concreteHeapAddress
    | ClassFieldSource of concreteHeapAddress * fieldId
    | ArrayIndexSource of concreteHeapAddress * int list
    | ArrayLowerBoundSource of concreteHeapAddress * int
    | ArrayLengthSource of concreteHeapAddress * int
    | StaticFieldSource of Type * fieldId
    with
    member x.StructField fieldId =
        match x with
        | HeapSource -> HeapSource
        | _ -> StructFieldSource(x, fieldId)

type IConcreteMemory =
    abstract Copy : unit -> IConcreteMemory
    abstract Contains : concreteHeapAddress -> bool
    abstract VirtToPhys : concreteHeapAddress -> obj
    abstract TryVirtToPhys : concreteHeapAddress -> obj option
    abstract PhysToVirt : obj -> concreteHeapAddress
    abstract TryPhysToVirt : obj -> concreteHeapAddress option
    abstract TryPhysToVirt : concreteMemorySource -> concreteHeapAddress option
    abstract AllocateRefType : concreteHeapAddress -> obj -> unit
    abstract AllocateValueType : concreteHeapAddress -> concreteMemorySource -> obj -> unit
    abstract ReadClassField : concreteHeapAddress -> fieldId -> obj
    abstract ReadArrayIndex : concreteHeapAddress -> int list -> obj
    // TODO: too expensive! use Seq.iter2 instead with lazy indices sequence
    abstract GetAllArrayData : concreteHeapAddress -> seq<int list * obj>
    abstract ReadArrayLowerBound : concreteHeapAddress -> int -> obj
    abstract ReadArrayLength : concreteHeapAddress -> int -> obj
    abstract WriteClassField : concreteHeapAddress -> fieldId -> obj -> unit
    abstract WriteArrayIndex : concreteHeapAddress -> int list -> obj -> unit
    abstract InitializeArray : concreteHeapAddress -> RuntimeFieldHandle -> unit
    abstract FillArray : concreteHeapAddress -> int -> int -> obj -> unit
    abstract CopyArray : concreteHeapAddress -> concreteHeapAddress -> int64 -> int64 -> int64 -> unit
    abstract CopyCharArrayToString : concreteHeapAddress -> concreteHeapAddress -> unit
    abstract CopyCharArrayToStringLen : concreteHeapAddress -> concreteHeapAddress -> int -> unit
    abstract Remove : concreteHeapAddress -> unit

type MockingType =
    | Default
    | Extern

type IMethodMock =
    abstract BaseMethod : System.Reflection.MethodInfo
    abstract MockingType : MockingType
    abstract Call : term option -> term list -> term
    abstract GetImplementationClauses : unit -> term array
    abstract Copy : unit -> IMethodMock

type ITypeMock =
    abstract Name : string
    abstract SuperTypes : Type seq
    abstract IsValueType : bool
    abstract Copy : unit -> ITypeMock

type private EmptyTypeMock() =
    let mockIsNotReady () = internalfail "Empty mock"
    interface ITypeMock with
        override x.Name = mockIsNotReady()
        override x.SuperTypes = mockIsNotReady()
        override x.IsValueType = mockIsNotReady()
        override x.Copy() = mockIsNotReady()

type symbolicType =
    | ConcreteType of Type
    | MockType of ITypeMock

// TODO: is it good idea to add new constructor for recognizing cilStates that construct RuntimeExceptions?
type exceptionRegister =
    | Unhandled of term * bool * string // Exception term * is runtime exception * stack trace
    | Caught of term * string // Exception term * stack trace
    | NoException
    with
    member x.GetError () =
        match x with
        | Unhandled(error, _, _) -> error
        | Caught(error, _) -> error
        | _ -> internalfail "no error"
    member x.TransformToCaught () =
        match x with
        | Unhandled(e, _, s) -> Caught(e, s)
        | _ -> internalfail "unable TransformToCaught"
    member x.TransformToUnhandled () =
        match x with
        | Caught(e, s) -> Unhandled(e, false, s)
        | _ -> internalfail "unable TransformToUnhandled"
    member x.UnhandledError =
        match x with
        | Unhandled _ -> true
        | _ -> false
    member x.ExceptionTerm =
        match x with
        | Unhandled (error, _, _)
        | Caught(error, _) -> Some error
        | _ -> None
    member x.StackTrace =
        match x with
        | Unhandled (_, _, s)
        | Caught(_, s) -> Some s
        | _ -> None
    static member map f x =
        match x with
        | Unhandled(e, isRuntime, s) -> Unhandled(f e, isRuntime, s)
        | Caught(e, s) -> Caught(f e, s)
        | NoException -> NoException

type arrayCopyInfo =
    {srcAddress : heapAddress; contents : arrayRegion; srcIndex : term; dstIndex : term; length : term; srcSightType : Type; dstSightType : Type} with
        override x.ToString() =
            sprintf "    source address: %O, from %O ranging %O elements into %O index with cast to %O;\n\r    updates: %O" x.srcAddress x.srcIndex x.length x.dstIndex x.dstSightType (MemoryRegion.toString "        " x.contents)

type model =
    | PrimitiveModel of IDictionary<ISymbolicConstantSource, term>
    | StateModel of state
with
    member x.Complete value =
        match x with
        | StateModel state when state.complete ->
            // TODO: ideally, here should go the full-fledged substitution, but we try to improve the performance a bit...
            match value.term with
            | Constant(_, _, typ) -> makeDefaultValue typ
            | HeapRef({term = Constant _}, t) -> nullRef t
            | _ -> value
        | _ -> value

    static member EvalDict (subst : IDictionary<ISymbolicConstantSource, term>) source term typ complete =
        let value = ref (Nop())
        if subst.TryGetValue(source, value) then value.Value
        elif complete then makeDefaultValue typ
        else term

    member x.Eval term =
        Substitution.substitute (function
            | { term = Constant(_, (:? IStatedSymbolicConstantSource as source), typ) } as term ->
                match x with
                | StateModel state -> source.Compose state
                | PrimitiveModel subst -> model.EvalDict subst source term typ true
            | { term = Constant(_, source, typ) } as term ->
                let subst, complete =
                    match x with
                    | PrimitiveModel dict -> dict, true
                    | StateModel state ->
                        match state.model with
                        | PrimitiveModel dict -> dict, state.complete
                        | _ -> __unreachable__()
                model.EvalDict subst source term typ complete
            | term -> term) id id term

// TODO: use set instead of list? #type
and typeConstraints =
    {
        mutable supertypes : Type list
        mutable subtypes : Type list
        mutable notSubtypes : Type list
        mutable notSupertypes : Type list
    }
with
    static member Empty() =
        let empty = List.empty
        { subtypes = empty; supertypes = empty; notSubtypes = empty; notSupertypes = empty }

    static member FromSuperTypes (superTypes : Type list) =
        let empty = List.empty
        let superTypes = List.filter (fun t -> t <> typeof<obj>) superTypes |> List.distinct
        { subtypes = empty; supertypes = superTypes; notSubtypes = empty; notSupertypes = empty }

    static member Create supertypes subtypes notSupertypes notSubtypes =
        let supertypes = List.filter (fun t -> t <> typeof<obj>) supertypes |> List.distinct
        let subtypes = List.distinct subtypes
        let notSupertypes = List.distinct notSupertypes
        let notSubtypes = List.distinct notSubtypes
        { subtypes = subtypes; supertypes = supertypes; notSubtypes = notSubtypes; notSupertypes = notSupertypes }

    member x.Merge(other : typeConstraints) : bool =
        let mutable changed = false
        if x.supertypes <> other.supertypes then
            changed <- true
            x.supertypes <- x.supertypes @ other.supertypes |> List.distinct
        if x.subtypes <> other.subtypes then
            changed <- true
            x.subtypes <- x.subtypes @ other.subtypes |> List.distinct
        if x.notSubtypes <> other.notSubtypes then
            changed <- true
            x.notSubtypes <- x.notSubtypes @ other.notSubtypes |> List.distinct
        if x.notSupertypes <> other.notSupertypes then
            changed <- true
            x.notSupertypes <- x.notSupertypes @ other.notSupertypes |> List.distinct
        changed

    member x.IsContradicting() =
        let nonComparable (t : Type) (u : Type) =
            u.IsClass && t.IsClass && (not <| u.IsAssignableTo t) && (not <| u.IsAssignableFrom t)
            || t.IsSealed && u.IsInterface && not (t.IsAssignableTo u)
        // X <: u and u <: t and X </: t
        x.supertypes |> List.exists (fun u -> x.notSupertypes |> List.exists u.IsAssignableTo)
        || // u <: X and t <: u and t </: X
        x.subtypes |> List.exists (fun u -> x.notSubtypes |> List.exists u.IsAssignableFrom)
        || // u <: X and X <: t and u </: t
        x.subtypes |> List.exists (fun u -> x.supertypes |> List.exists (u.IsAssignableTo >> not))
        || // No multiple inheritance -- X <: u and X <: t and u </: t and t </: u and t, u are classes
        x.supertypes |> List.exists (fun u -> x.supertypes |> List.exists (nonComparable u))
        || // u </: X and X <: u when u is sealed
        x.supertypes |> List.exists (fun u -> u.IsSealed && x.notSubtypes |> List.contains u)

    member x.AddSuperType(superType : Type) =
        if superType <> typeof<obj> then
            x.supertypes <- superType :: x.supertypes |> List.distinct

    member x.Copy() =
        {
            supertypes = x.supertypes
            subtypes = x.subtypes
            notSubtypes = x.notSubtypes
            notSupertypes = x.notSupertypes
        }

and typesConstraints private (newAddresses, constraints) =

    new () =
        let newAddresses = HashSet<term>()
        let allConstraints = Dictionary<term, typeConstraints>()
        typesConstraints(newAddresses, allConstraints)

    member x.Copy() =
        let copiedNewAddresses = HashSet<term>(newAddresses)
        let copiedConstraints = Dictionary<term, typeConstraints>()
        for entry in constraints do
            copiedConstraints.Add(entry.Key, entry.Value.Copy())
        typesConstraints(copiedNewAddresses, copiedConstraints)

    member private x.AddNewAddress address =
        newAddresses.Add address |> ignore

    member x.ClearNewAddresses() =
        newAddresses.Clear()

    member x.NewAddresses with get() = newAddresses

    member x.Add (address : term) (typeConstraint : typeConstraints) =
        let current = ref (typeConstraints.Empty())
        if constraints.TryGetValue(address, current) then
            let changed = current.Value.Merge typeConstraint
            if changed then x.AddNewAddress address
        else
            constraints.Add(address, typeConstraint)
            x.AddNewAddress address

    member x.AddSuperType address superType =
        let typeConstraint = List.singleton superType |> typeConstraints.FromSuperTypes
        x.Add address typeConstraint

    member x.CheckInequality() =
        let mutable isValid = true
        let unequal = HashSet<term * term>()
        for entry1 in constraints do
            let address1 = entry1.Key
            let typeConstraints1 = entry1.Value
            for entry2 in constraints do
                let address2 = entry2.Key
                let typeConstraints2 = entry2.Value
                let typeConstraints = typeConstraints1.Copy()
                let different = address1 <> address2
                if different then
                    typeConstraints.Merge typeConstraints2 |> ignore
                if typeConstraints.IsContradicting() then
                    if different then unequal.Add(address1, address2) |> ignore
                    else isValid <- false
        isValid, unequal

    interface System.Collections.IEnumerable with
        member this.GetEnumerator() =
          upcast constraints.GetEnumerator()

    interface IEnumerable<KeyValuePair<term, typeConstraints>> with
        override this.GetEnumerator() =
          constraints.GetEnumerator()

    member x.Item(address : term) =
        constraints[address].Copy()

    member x.Count with get() = constraints.Count

and typeStorage private (constraints, addressesTypes, typeMocks, classesParams, methodsParams) =
    let mutable classesParams = classesParams
    let mutable methodsParams = methodsParams

    new() =
        let constraints = typesConstraints()
        let addressesTypes = Dictionary<term, candidates>()
        let typeMocks = Dictionary<Type list, ITypeMock>()
        let classesParams : symbolicType[] = Array.empty
        let methodsParams : symbolicType[] = Array.empty
        typeStorage(constraints, addressesTypes, typeMocks, classesParams, methodsParams)

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
        typeStorage(newConstraints, newAddressesTypes, newTypeMocks, classesParams, methodsParams)

    member x.AddConstraint address typeConstraint =
        constraints.Add address typeConstraint

    member x.Item
        with get (address : term) =
            let t = ref (candidates.Empty())
            if addressesTypes.TryGetValue(address, t) then Some t.Value
            else None
        and set (address : term) (candidates : candidates) =
            assert(candidates.IsEmpty |> not)
            addressesTypes[address] <- candidates

    member x.IsValid with get() = addressesTypes.Count = constraints.Count

and CandidateGroups = {
    publicBuiltIn : seq<candidate>
    publicUser : seq<candidate>
    privateUser : seq<candidate>
    rest : seq<candidate>
}
with
    static member GroupBy (userAssembly : Assembly) (items: _ seq) (toCandidate : _ -> candidate) toType =
        let items = List.ofSeq items
        let isPublicBuiltIn (t : Type) = TypeUtils.isPublic t && Reflection.isBuiltInType t
        let isPublicUser (t: Type) = TypeUtils.isPublic t && t.Assembly = userAssembly
        let isPrivateUser (t: Type) = not (TypeUtils.isPublic t) && t.Assembly = userAssembly

        let inline getCandidates p items = List.partition (toType >> p) items
        let publicBuiltIn, rest = getCandidates isPublicBuiltIn items
        let publicUser, rest = getCandidates isPublicUser rest
        let privateUser, rest = getCandidates isPrivateUser rest
        {
            publicBuiltIn = publicBuiltIn |> List.map toCandidate
            publicUser = publicUser |> List.map toCandidate
            privateUser = privateUser |> List.map toCandidate
            rest = rest |> List.map toCandidate
        }

    member x.Filter shouldBeTaken =
        {
            publicBuiltIn = Seq.choose shouldBeTaken x.publicBuiltIn
            publicUser = Seq.choose shouldBeTaken x.publicUser
            privateUser = Seq.choose shouldBeTaken x.privateUser
            rest = Seq.choose shouldBeTaken x.rest
        }

    member x.Joined =
        seq {
            yield! x.publicBuiltIn
            yield! x.publicUser
            yield! x.privateUser
            yield! x.rest
        }

    member x.Eval() =
        {
            publicBuiltIn = Seq.toList x.publicBuiltIn
            publicUser = Seq.toList x.publicUser
            privateUser = Seq.toList x.privateUser
            rest = Seq.toList x.rest
        }

and candidates private(typeGroups : CandidateGroups, genericGroups: CandidateGroups, mock, userAssembly) =

    let orderedCandidates = seq {
        yield! typeGroups.Joined
        yield! genericGroups.Joined
    }

    new(cs : seq<candidate> , mock: ITypeMock option, userAssembly : Assembly) =
        let cs = Seq.distinct cs
        let takeGeneric = function | GenericCandidate c -> Some c | _ -> None
        let takeNonGeneric = function | Candidate t -> Some t | _ -> None

        let types = cs |> Seq.choose takeNonGeneric
        let genericTypes = cs |> Seq.choose takeGeneric

        let typeGroups = CandidateGroups.GroupBy userAssembly types Candidate id
        let getTypeDef (gt : genericCandidate) = gt.Typedef
        let genericGroups = CandidateGroups.GroupBy userAssembly genericTypes GenericCandidate getTypeDef

        candidates(typeGroups, genericGroups, mock, userAssembly)

    member x.IsEmpty
        with get() =
            match mock with
            | Some _ -> false
            | None -> Seq.isEmpty x.Types

    member x.Types =
        seq {
            yield! orderedCandidates |> Seq.collect (fun c -> c.Types) |> Seq.map ConcreteType
            if mock.IsSome then yield mock.Value |> MockType
        }

    member x.Candidates = orderedCandidates

    static member Empty() =
        candidates(Seq.empty, None, Reflection.mscorlibAssembly)

    member x.Copy(changeMock: ITypeMock -> ITypeMock) =
        let newMock = Option.map changeMock mock
        candidates(typeGroups, genericGroups, newMock, userAssembly)

    member x.Pick() = Seq.head x.Types

    member x.Filter shouldBeTaken (refineMock : ITypeMock -> ITypeMock option) =
        let types = typeGroups.Filter shouldBeTaken
        let generics = genericGroups.Filter shouldBeTaken
        let mock = Option.bind refineMock mock
        candidates(types, generics, mock, userAssembly)

    member x.Take(count) =
        let types =
            match mock with
            | Some _ -> Seq.truncate (count - 1) orderedCandidates
            | None -> Seq.truncate count orderedCandidates
        candidates(types, mock, userAssembly)

    member x.Eval() =
        candidates(typeGroups.Eval(), genericGroups.Eval(), mock, userAssembly)

and candidate =
    | GenericCandidate of genericCandidate
    | Candidate of Type
with
    member x.IsAbstract =
        match x with
        | Candidate t -> t.IsAbstract
        | GenericCandidate gc -> gc.Typedef.IsAbstract

    member x.TypeDef =
        match x with
        | Candidate t -> t
        | GenericCandidate gc -> gc.Typedef

    member x.Types =
        match x with
        | Candidate t -> Seq.singleton t
        | GenericCandidate gc -> gc.Types

    member x.Copy() =
        match x with
        | Candidate _ as c -> c
        | GenericCandidate gc -> gc.Copy() |> GenericCandidate

and parameterSubstitutions private (
    parameters,
    layers,
    maxDepths: Dictionary<Type, int>,
    parameterConstraints: Dictionary<Type, typeConstraints>,
    depth,
    getCandidates,
    unrollCandidateSubstitutions: seq<pdict<Type,candidate>> -> seq<pdict<Type,Type>>,
    satisfiesConstraints,
    makeGenericCandidate: Type -> int -> genericCandidate option,
    childDepth) =

    let updateConstraints parameterConstraints =
        parameterSubstitutions(
            parameters,
            layers,
            maxDepths,
            parameterConstraints,
            depth,
            getCandidates,
            unrollCandidateSubstitutions,
            satisfiesConstraints,
            makeGenericCandidate,
            childDepth)

    let makeGeneric param typ =
        let depth = childDepth param maxDepths depth
        if depth <= 0 then None
        else makeGenericCandidate typ depth

    let processLayer (substs: parameterSubstitution seq) layer =
        let paramCandidates subst param =
            let candidates: candidates = makeGeneric param |> getCandidates
            let filtered = candidates.Filter (satisfiesConstraints subst parameterConstraints[param] param) (fun _ -> None)
            filtered.Candidates
        seq {
            for subst in substs do
                yield!
                    layer
                    |> List.ofSeq
                    |> List.map (paramCandidates subst)
                    |> List.cartesian
                    |> Seq.map (Seq.zip layer >> PersistentDict.ofSeq)
                    |> unrollCandidateSubstitutions
                    |> Seq.map (PersistentDict.fold (fun dict k v -> PersistentDict.add k v dict) subst)
        }

    let args: parameterSubstitution seq =
        Seq.fold processLayer (Seq.singleton PersistentDict.empty) layers

    static member Create parameterTypes depth getCandidates unrollCandidateSubstitutions satisfiesConstraints makeGenericCandidate childDepth =
        let layers, maxDepths, isCycled = makeLayers parameterTypes
        if isCycled || depth <= 0 then None
        else
            let parameterConstraints = Dictionary<Type, typeConstraints>()
            for t in parameterTypes do
                parameterConstraints.Add(t, typeConstraints.Empty())
            parameterSubstitutions(
                parameterTypes,
                layers,
                maxDepths,
                parameterConstraints,
                depth,
                getCandidates,
                unrollCandidateSubstitutions,
                satisfiesConstraints,
                makeGenericCandidate,
                childDepth)
            |> Some

    member x.AddConstraints (newConstraints: Dictionary<Type, typeConstraints>) =
        let newParameterConstraints = Dictionary<Type, typeConstraints>()
        for KeyValue(param, constraints) in parameterConstraints do
            let constraints = constraints.Copy()
            constraints.Merge newConstraints[param] |> ignore
            newParameterConstraints.Add(param, constraints)

        updateConstraints newParameterConstraints

    member val Substitutions = args

and genericCandidate private (
    typedef: Type,
    depth,
    parameterSubstitutions: parameterSubstitutions,
    selfConstraints,
    satisfiesConstraints) =

    do
        assert(depth >= 0)
        assert typedef.IsGenericTypeDefinition

    let parameters = typedef.GetGenericArguments()
    let interfaces = typedef.GetInterfaces()
    let interfacesDefs = interfaces |> Array.map TypeUtils.getTypeDef
    let genericInterfaces = interfaces |> Array.filter (fun t -> t.IsGenericType)
    let supertypes = TypeUtils.getSupertypes typedef
    let supertypesDefs = supertypes |> List.map TypeUtils.getTypeDef
    let propagateConstraints (constraints: typeConstraints) =
        propagate typedef supertypesDefs parameters genericInterfaces constraints.supertypes constraints.subtypes

    let propagateNotConstraints (constraints: typeConstraints) =
        let inline filterSingleGeneric (ts : Type list) =
            ts |> List.filter (fun t -> t.IsGenericType && t.GetGenericArguments().Length = 1)
        let notSupertypes = filterSingleGeneric constraints.notSupertypes
        let notSubtypes = filterSingleGeneric constraints.notSubtypes
        propagateNotConstraints typedef supertypesDefs parameters genericInterfaces notSupertypes notSubtypes

    let types =
        parameterSubstitutions.Substitutions
        |> Seq.map (substitute typedef)

    static member Create (typedef: Type) depth makeSubstitution satisfiesConstraints =
        if depth <= 0 then None
        else
            option {
                let makeGenericCandidate t d =
                    genericCandidate.Create t d makeSubstitution satisfiesConstraints
                let parameters = typedef.GetGenericArguments()
                let! paramSubsts = makeSubstitution parameters depth makeGenericCandidate
                let selfConstraints = typeConstraints.Empty()
                return genericCandidate(typedef, depth, paramSubsts, selfConstraints, satisfiesConstraints)
            }

    member x.AddConstraints constraints =
        let selfConstraints = selfConstraints.Copy()
        selfConstraints.Merge constraints |> ignore

        let isSupertypeValid interfacesDefs supertypesDefs (supertype: Type) =
            let supertypeDef = TypeUtils.getTypeDef supertype
            if supertypeDef.IsInterface && not typedef.IsInterface then Array.contains supertypeDef interfacesDefs
            else List.contains supertypeDef supertypesDefs

        let isSubtypeValid (subtype: Type) =
            if subtype.IsInterface && not typedef.IsInterface then false
            else
                let supertypesDefs = TypeUtils.getSupertypes subtype |> List.map TypeUtils.getTypeDef
                isSupertypeValid [||] supertypesDefs typedef

        let newIsEmptied =
            List.forall (isSupertypeValid interfacesDefs supertypesDefs) constraints.supertypes |> not
            || List.forall isSubtypeValid constraints.subtypes |> not

        if newIsEmptied then None
        else
            let fromNotInterfaces, fromNotSupertypes, fromNotSubtypes = propagateNotConstraints constraints
            match propagateConstraints constraints with
            | Some (fromInterfaces, fromSupertypes, fromSubtypes) ->
                let parameterConstraints = Dictionary<Type, typeConstraints>()
                for i = 0 to parameters.Length - 1 do
                    let item (arr: _ array) = arr[i]
                    let fromSupertypes = fromSupertypes |> List.map item
                    let fromSubtypes = fromSubtypes |> List.map item
                    let toSupertypes, toSubtypes = fromInterfaces |> List.map item |> List.unzip
                    let fromClasses = fromSubtypes @ fromSupertypes |> List.concat
                    let toSupertypes, toSubtypes = List.concat toSupertypes, List.concat toSubtypes

                    let fromNotSupertypes = fromNotSupertypes |> List.map item
                    let fromNotSubtypes = fromNotSubtypes |> List.map item
                    let toNotSupertypes, toNotSubtypes = fromNotInterfaces |> List.map item |> List.unzip
                    let fromNotClasses = fromNotSubtypes @ fromNotSupertypes |> List.concat
                    let toNotSupertypes, toNotSubtypes = List.concat toNotSupertypes, List.concat toNotSubtypes

                    let constraints =
                        typeConstraints.Create
                            (fromClasses @ toSupertypes)
                            (fromClasses @ toSubtypes)
                            (fromNotClasses @ toNotSupertypes)
                            (fromNotClasses @ toNotSubtypes)
                    parameterConstraints.Add(parameters[i], constraints)
                let newParameterSubstitutions = parameterSubstitutions.AddConstraints parameterConstraints
                genericCandidate(typedef, depth, newParameterSubstitutions, selfConstraints, satisfiesConstraints) |> Some
            | None -> None

    member val Typedef = typedef

    member val Types =
        types
        |> Seq.truncate 1000 // TODO: make another way to prevent long iteration through types
        |> Seq.filter (satisfiesConstraints selfConstraints)

    member x.IsEmpty = Seq.isEmpty x.Types

    member x.Copy() =
        let copiedSelfConstraints = selfConstraints.Copy()
        genericCandidate(typedef, depth, parameterSubstitutions, copiedSelfConstraints, satisfiesConstraints)

and IErrorReporter =
    abstract ConfigureState : state -> unit
    abstract ReportError : string -> term -> unit
    abstract ReportFatalError : string -> term -> unit

and
    [<ReferenceEquality>]
    state = {
        mutable pc : pathCondition
        mutable typeStorage : typeStorage
        mutable evaluationStack : evaluationStack
        mutable stack : callStack                                          // Arguments and local variables
        mutable stackBuffers : pdict<stackKey, stackBufferRegion>          // Buffers allocated via stackAlloc
        mutable classFields : pdict<fieldId, heapRegion>                   // Fields of classes in heap
        mutable arrays : pdict<arrayType, arrayRegion>                     // Contents of arrays in heap
        mutable lengths : pdict<arrayType, vectorRegion>                   // Lengths by dimensions of arrays in heap
        mutable lowerBounds : pdict<arrayType, vectorRegion>               // Lower bounds by dimensions of arrays in heap
        mutable staticFields : pdict<fieldId, staticsRegion>               // Static fields of types without type variables
        mutable boxedLocations : pdict<Type, heapRegion>                   // Value types boxed in heap
        mutable initializedTypes : symbolicTypeSet                         // Types with initialized static members
        concreteMemory : IConcreteMemory                                   // Fully concrete objects
        mutable allocatedTypes : pdict<concreteHeapAddress, symbolicType>  // Types of heap locations allocated via new
        mutable typeVariables : typeVariables                              // Type variables assignment in the current state
        mutable delegates : pdict<concreteHeapAddress, term>               // Subtypes of System.Delegate allocated in heap
        mutable currentTime : vectorTime                                   // Current timestamp (and next allocated address as well) in this state
        mutable startingTime : vectorTime                                  // Timestamp before which all allocated addresses will be considered symbolic
        mutable exceptionsRegister : exceptionRegister                     // Heap-address of exception object
        mutable model : model                                              // Concrete valuation of symbolics
        complete : bool                                                    // If true, reading of undefined locations would result in default values
        methodMocks : IDictionary<IMethod, IMethodMock>
    }

and IStatedSymbolicConstantSource =
    inherit ISymbolicConstantSource
    abstract Compose : state -> term
