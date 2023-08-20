module VSharp.Core.GenericUtils

open System
open System.Collections.Generic
open VSharp

type parameterSubstitution = pdict<Type, Type>

let substitute (typedef: Type) (subst: parameterSubstitution) =
    if typedef.IsGenericTypeDefinition then
        let args =
            typedef.GetGenericArguments()
            |> Array.map (PersistentDict.find subst)
        typedef.MakeGenericType args
    else typedef

let private collectDependencies parameters =
    let rec folder (acc, depth) t =
        let deps, maxDepth = getConstraintDependencies acc t
        deps, max maxDepth depth
    and getConstraintDependencies acc (typ: Type) =
        if typ.IsGenericParameter then typ :: acc, 0
        elif typ.IsGenericType then
            let deps, maxDepth =
                typ.GetGenericArguments()
                |> Array.fold folder (acc, 0)
            deps, maxDepth + 1
        else acc, 0

    let dependencies = Dictionary<Type, Type list>()
    let maxDepths = Dictionary<Type, int>()
    let addParameterDependencies (typ: Type) =
        assert typ.IsGenericParameter
        let parameterDependencies, depth = typ.GetGenericParameterConstraints() |> Array.fold folder ([], 0)
        dependencies.Add(typ, parameterDependencies)
        maxDepths.Add(typ, depth)

    parameters |> Array.iter addParameterDependencies
    dependencies, maxDepths

let private reverseDependencies (dependencies: Dictionary<Type, Type list>) =
    let setValue value (keyValue: KeyValuePair<_, _>) = KeyValuePair(keyValue.Key, value)
    let reversedDeps = dependencies |> Seq.map (setValue []) |> Dictionary
    let depsCnt = dependencies |> Seq.map (setValue 0) |> Dictionary
    let addDependency dep param =
        depsCnt[dep] <- depsCnt[dep] + 1
        reversedDeps[param] <- dep :: reversedDeps[param]

    for entry in dependencies do
        let parameter, paramDependencies = entry.Key, entry.Value
        List.iter (addDependency parameter) paramDependencies

    reversedDeps, depsCnt

let private refineMaxDepths (dependencies: Dictionary<Type, Type list>) (maxDepths: Dictionary<Type, int>) =
    let newMaxDepths = Dictionary<Type, int>()
    let mutable isCycled = false
    let rec dfs t =
        newMaxDepths.Add(t, -1)
        let mutable maxDepth = 0
        for dep in dependencies[t] do
            if newMaxDepths.ContainsKey t then
                if newMaxDepths[t] = -1 then isCycled <- true
                else
                    maxDepth <- newMaxDepths[t] + maxDepths[t] |> max maxDepth
            else
                maxDepth <- dfs dep |> max maxDepth
        newMaxDepths[t] <- maxDepth
        newMaxDepths[t] + maxDepths[t]

    for entry in dependencies do
        dfs entry.Key |> ignore
    newMaxDepths, isCycled

let layerDependencies (dependencies: Dictionary<Type, Type list>) (counts: Dictionary<Type, int>) =
    let extractZeroes () =
        let zeroes =
            List<Type>(seq {
                for entry in counts do
                    let typ, cnt = entry.Key, entry.Value
                    if cnt = 0 then
                        yield typ
            })
        for zero in zeroes do
            counts.Remove(zero) |> ignore
        zeroes

    let layers = List<List<Type>>()
    while counts.Count > 0 do
        let zeroes = extractZeroes()
        layers.Add(zeroes)
        for zero in zeroes do
            for dep in dependencies[zero] do
                counts[dep] <- counts[dep] - 1

    layers |> Seq.map (fun list -> list :> seq<_>)

let private trackIndices (typ: Type) (supertype: Type) =
    let rec helper (typ: Type) (supertype: Type) indices =
        if not typ.IsGenericType then [||]
        elif not supertype.IsGenericType then Array.replicate (typ.GetGenericArguments().Length) []
        elif typ.GetGenericTypeDefinition() = supertype.GetGenericTypeDefinition() then indices
        else
            let bt = typ.BaseType
            let btArgs = TypeUtils.getArgs bt

            let mapping = Dictionary<Type, List<int>>()
            let add i t = if mapping.ContainsKey t then mapping[t].Add(i) else mapping.Add(t, List([i]))
            let get t = if mapping.ContainsKey t then List.ofSeq mapping[t] else []
            Array.iteri add btArgs
            let track = Array.map get btArgs |> helper bt supertype

            let typArgs = TypeUtils.getArgs typ
            let traceback = List.collect (fun i -> get typArgs[i] |> List.collect (fun i -> track[i]) |> List.distinct)
            Array.map traceback indices

    Array.init (TypeUtils.getArgs typ).Length List.singleton |> helper typ supertype

let makeLayers parameters =
    let dependencies, maxDepths = collectDependencies parameters
    let revDeps, counts = reverseDependencies dependencies
    let maxDepths, isCycled = refineMaxDepths revDeps maxDepths
    let layers = if isCycled then Seq.empty else layerDependencies revDeps counts
    layers, maxDepths, isCycled

let rec propagateInterface parameters (interfaces: Type array) (supertype : Type) =
    let supertypeDef = TypeUtils.getTypeDef supertype
    let supertypeDefArgs = TypeUtils.getArgs supertypeDef
    let supertypeArgs = TypeUtils.getArgs supertype
    option {
        let! index = interfaces |> Array.tryFindIndex (fun t -> t.GetGenericTypeDefinition() = supertypeDef)
        let interfaceParams = interfaces[index].GetGenericArguments()
        let res = parameters |> Array.map (fun t -> KeyValuePair(t, ([],[]))) |> Dictionary

        let update (parameters: Type array) (res: Dictionary<_,_>) fromSupertypes fromSubtypes fromInterfaces =
            for i = 0 to parameters.Length - 1 do
                if parameters[i].IsGenericParameter then
                    let item (arr: _ array) = arr[i]
                    let fromSupertypes = fromSupertypes |> List.map item
                    let fromSubtypes = fromSubtypes |> List.map item
                    let toSupertypes, toSubtypes = fromInterfaces |> List.map item |> List.unzip
                    let fromClasses = fromSubtypes @ fromSupertypes |> List.concat
                    let toSupertypes, toSubtypes = List.concat toSupertypes, List.concat toSubtypes

                    let supertypes, subtypes = res[parameters[i]]
                    res[parameters[i]] <- fromClasses @ toSupertypes @ supertypes, fromClasses @ toSubtypes @ subtypes

        let updateWithVariance i (param: Type) =
            let typ = supertypeArgs[i]
            if res.ContainsKey param then
                let supertypes, subtypes = res[param]

                res[param] <-
                    match supertypeDefArgs[i] with
                    | TypeUtils.Invariant -> typ :: supertypes, typ :: subtypes
                    | TypeUtils.Covariant -> typ :: supertypes, subtypes
                    | TypeUtils.Contravariant -> supertypes, typ :: subtypes
                |> Some
            elif param.IsGenericType then
                option {
                    let typedef = param.GetGenericTypeDefinition()
                    let paramParams = param.GetGenericArguments()

                    let! fromInterfaces, fromSupertypes, fromSubtypes =
                        propagate
                        <| typedef
                        <| (TypeUtils.getSupertypes param |> List.map TypeUtils.getTypeDef)
                        <| typedef.GetGenericArguments()
                        <| param.GetInterfaces()
                        <| [typ]
                        <| []

                    update paramParams res fromSupertypes fromSubtypes fromInterfaces
                    return! Some ()
                }
            else
                let isSuitable =
                    match supertypeDefArgs[i] with
                    | TypeUtils.Invariant -> param = typ
                    | TypeUtils.Covariant -> param.IsAssignableTo typ
                    | TypeUtils.Contravariant -> param.IsAssignableFrom typ
                if isSuitable then Some ()
                else None

        if Array.mapi updateWithVariance interfaceParams |> List.ofArray |> Option.sequenceM id |> Option.isSome then
            return parameters |> Array.map (fun p -> res[p])
        else return! None
    }

and propagateSupertype typedef supertypes (supertype: Type) =
    let supertypeDef = TypeUtils.getTypeDef supertype
    let supertypeArgs = TypeUtils.getArgs supertype
    if List.contains supertypeDef supertypes then
        trackIndices typedef supertype
        |> Array.map (List.map (fun i -> supertypeArgs[i]))
        |> Some
    else None

and propagateSubtype typedef (parameters: _ array) subtype =
    let subtypeDef = TypeUtils.getTypeDef subtype
    let subtypeArgs = TypeUtils.getArgs subtype
    if TypeUtils.getSupertypes subtype |> List.map TypeUtils.getTypeDef |> List.contains typedef then
        let subtypes = Array.init parameters.Length (fun _ -> List<Type>())
        let add i = List.iter (fun j -> subtypes[j].Add subtypeArgs[i])
        trackIndices subtypeDef typedef |> Array.iteri add
        Array.map List.ofSeq subtypes |> Some
    else None

and propagate typedef supertypesDefs parameters interfaces (supertypes: Type list) (subtypes: Type list) =
    option {
        let sptInterfaces, supertypes = supertypes |> List.partition (fun t -> t.IsInterface)
        let sbtInterfaces, subtypes = subtypes |> List.partition (fun t -> t.IsInterface)

        let! fromInterfaces = sptInterfaces |> List.map (propagateInterface parameters interfaces) |> Option.sequenceM id
        let! fromSupertypes = supertypes |> List.map (propagateSupertype typedef supertypesDefs) |> Option.sequenceM id
        let! fromSubtypes = subtypes |> List.map (propagateSubtype typedef parameters) |> Option.sequenceM id
        if List.isEmpty sbtInterfaces |> not then return! None
        else return fromInterfaces, fromSupertypes, fromSubtypes
    }

let propagateNotSupertype typedef supertypes (notSupertype: Type) =
    assert(notSupertype.GetGenericArguments().Length = 1)
    propagateSupertype typedef supertypes notSupertype
    |> Option.defaultValue (typedef.GetGenericArguments() |> Array.map (fun _ -> []))

let propagateNotSubtype typedef (parameters: _ array) (notSubtype: Type) =
    assert(notSubtype.GetGenericArguments().Length = 1)
    propagateSubtype typedef parameters notSubtype
    |> Option.defaultValue (typedef.GetGenericArguments() |> Array.map (fun _ -> []))

let propagateNotConstraints typedef supertypesDefs parameters interfaces (notSupertypes: Type list) (notSubtypes: Type list) =
    let nSptInterfaces, nSupertypes = notSupertypes |> List.partition (fun t -> t.IsInterface)
    let _, nSubtypes = notSubtypes |> List.partition (fun t -> t.IsInterface)

    let fromNotSupertypes = nSupertypes |> List.map (propagateNotSupertype typedef supertypesDefs)
    let fromNotSubtypes = nSubtypes |> List.map (propagateNotSubtype typedef parameters)
    let fromNotInterfaces =
        nSptInterfaces
        |> List.map (
            propagateInterface parameters interfaces
            >> Option.defaultValue (typedef.GetGenericArguments() |> Array.map(fun _ -> [], [])))
    fromNotInterfaces, fromNotSupertypes, fromNotSubtypes
