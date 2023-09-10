namespace VSharp

open System
open System.Collections.Generic
open System.Runtime.InteropServices
open System.Runtime.CompilerServices

module public Seq =
    let foldi f st xs =
        let i = ref (-1)
        Seq.fold (fun s t ->
            i := !i + 1
            f s !i t) st xs

    let public cons x xs = seq {
        yield x
        yield! xs
    }

    let public (|Cons|Empty|) s =
        if Seq.isEmpty s then Empty
        else Cons (Seq.head s, Seq.tail s)

module public List =
    let rec private mappedPartitionAcc f left right = function
        | [] -> (List.rev left, List.rev right)
        | x::xs ->
            match f x with
            | Some m -> mappedPartitionAcc f (m::left) right xs
            | None -> mappedPartitionAcc f left (x::right) xs

    let public mappedPartition f xs =
        mappedPartitionAcc f [] [] xs

    let rec public map2Different f xs1 xs2 =
        match xs1, xs2 with
        | Seq.Empty, [] -> []
        | Seq.Empty, x2::xs2' -> f None (Some x2) :: map2Different f xs1 xs2'
        | Seq.Cons(x1, xs1'), [] -> f (Some x1) None :: map2Different f xs1' xs2
        | Seq.Cons(x1, xs1'), x2::xs2' -> f (Some x1) (Some x2) :: map2Different f xs1' xs2'

    let public append3 xs ys zs = List.append xs (List.append ys zs)

    let rec public filterMap2 mapper xs ys =
        match xs, ys with
        | [], [] -> []
        | x::xs, y::ys ->
            let z = mapper x y
            optCons (filterMap2 mapper xs ys) z
        | _ -> internalfail "filterMap2 expects lists of equal lengths"

    let public unique = function
        | [] -> internalfail "unexpected non-empty list"
        | x::xs ->
            assert(List.forall ((=)x) xs)
            x

    let rec public cartesian = function
        | [xs] -> Seq.map List.singleton xs
        | xs::xss ->
            seq {
                let xssCartesian = cartesian xss
                if Seq.isEmpty xssCartesian |> not then
                    for x in xs do
                        for xs' in xssCartesian do
                            yield x::xs'
            }
        | [] -> Seq.empty

    let public cartesianMap mapper = cartesian >> Seq.map mapper

    let lastAndRest xs =
        let rec lastAndRest x xs k =
            match xs with
            | [] -> k x []
            | y::ys -> lastAndRest y ys (fun c cs -> k c (x::cs))
        match xs with
        | [] -> internalfail "List.last of empty list!"
        | x::xs -> lastAndRest x xs makePair

    let rec mapLast f = function
        | [x] -> [f x]
        | x::xs -> x::(mapLast f xs)
        | [] -> []

module public Map =
    let public add2 (map : Map<'a, 'b>) key value = map.Add(key, value)

    let foldMap mapping state table =
        let mapFolder (map, state) key value =
            let newValue, newState = mapping key state value
            (Map.add key newValue map, newState)
        Map.fold mapFolder (Map.empty, state) table

    let filterMap mapping map =
        Map.fold
            (fun m k v ->
                match mapping k v with
                | Some v' -> Map.add k v' m
                | None -> m)
            Map.empty map

    let findOrDefaultWith k map defThunk =
        let optionValue = Map.tryFind k map
        Option.defaultWith defThunk optionValue

module public Dict =
    let public getValueOrUpdate (dict : IDictionary<'a, 'b>) key fallback =
        if dict.ContainsKey(key) then dict.[key]
        else
            let newVal = fallback()
            // NOTE: 'fallback' action may add 'key' to 'dict'
            if dict.ContainsKey(key) then dict.[key]
                else
                    dict.Add(key, newVal)
                    newVal

    let public setValueOrUpdate (dict : IDictionary<'a, 'b>) key value =
        if dict.ContainsKey(key) then dict.[key] <- value
        else dict.Add(key, value)

    let public tryGetValue (dict : IDictionary<'a, 'b>) key defaultValue =
        if dict.ContainsKey(key) then dict.[key]
        else defaultValue

    let public tryGetValue2 (dict : IDictionary<'a, 'b>) key defaultValue =
        if dict.ContainsKey(key) then dict.[key]
        else defaultValue()

    let public ofSeq<'a, 'b when 'a : equality> (s : seq<'a * 'b>) : IDictionary<'a, 'b> =
        let result = new Dictionary<'a, 'b>()
        Seq.iter result.Add s
        result :> IDictionary<'a, 'b>

    let public equals (dict1 : IDictionary<'a,'b>) (dict2 : IDictionary<'a, 'b>) =
        dict1.Keys.Count = dict2.Keys.Count &&
        dict1.Keys |> Seq.forall (fun k -> dict2.ContainsKey(k) && obj.Equals(dict2.[k], dict1.[k]));

    let public toString format separator keyMapper valueMapper sorter (d : IDictionary<'a, 'b>) =
        d
        |> Seq.sortBy (fun kv -> sorter kv.Key)
        |> Seq.map (fun kv -> sprintf format (keyMapper kv.Key) (valueMapper kv.Value))
        |> join separator


type 'a stack = 'a list

module public Stack =

    let bottomAndRest = List.lastAndRest

    let pop = function
        | [] -> failwith "Attempt to pop an empty stack"
        | head :: tl -> head, tl

    let drop count s = List.skip count s

    let push stack element = element::stack

    let dup = function
        | [] -> failwith "Dup on empty stack"
        | head :: tl -> head :: head :: tl

    let empty = List.empty

    let singleton = List.singleton

    let isEmpty = List.isEmpty

    let middle idx stack = List.item ((List.length stack) - idx - 1) stack

    let size = List.length

    let tryFindBottom = List.tryFindBack

    let exists = List.exists

    let map = List.map

    let union = List.append

    let fold = List.fold

module Array =

    // TODO: rewrite without recursion
    let rec allIndicesViaLens lbs lens =
        let rank = List.length lens
        assert(List.length lbs = rank)
        seq {
            match lbs, lens with
            | lb :: lbs, len :: lens ->
                let ub = len - lb - 1
                for i = lb to ub do
                    for tail in allIndicesViaLens lbs lens do
                        i :: tail
            | _ -> List.empty
        }

    // TODO: rewrite without recursion
    let rec allIndicesViaBound lbs ubs =
        let rank = List.length ubs
        assert(List.length lbs = rank)
        seq {
            match lbs, ubs with
            | lb :: lbs, ub :: lens ->
                for i = lb to ub do
                    for tail in allIndicesViaLens lbs lens do
                        i :: tail
            | _ -> List.empty
        }

    let fillFast<'a> (arr : Array) (value : 'a) =
        let bytePtr = &MemoryMarshal.GetArrayDataReference arr
        let ptr = &Unsafe.As<byte, 'a>(&bytePtr)
        let span = MemoryMarshal.CreateSpan<'a>(&ptr, arr.Length)
        span.Fill value

    // Fills zero-initialized array with value
    let fill (arr : Array) (value : obj) =
        match value with
        | null -> () // Do nothing because arr is already filled with nulls
        | _ ->
            let t = value.GetType()
            if arr = null || (t.IsValueType && Nullable.GetUnderlyingType(t) = null && value = System.Runtime.Serialization.FormatterServices.GetUninitializedObject(t)) then
                // Do nothing because arr is already filled with nulls
                ()
            else
                let elementType = arr.GetType().GetElementType()
                match value with
                | :? int as i when elementType = typeof<int> -> fillFast arr i
                | :? byte as i when elementType = typeof<byte> -> fillFast arr i
                | :? char as i when elementType = typeof<char> -> fillFast arr i
                | :? uint as i when elementType = typeof<uint> -> fillFast arr i
                | :? int64 as i when elementType = typeof<int64> -> fillFast arr i
                | :? uint64 as i when elementType = typeof<uint64> -> fillFast arr i
                | :? sbyte as i when elementType = typeof<sbyte> -> fillFast arr i
                | :? int16 as i when elementType = typeof<int16> -> fillFast arr i
                | :? uint16 as i when elementType = typeof<uint16> -> fillFast arr i
                | :? double as i when elementType = typeof<double> -> fillFast arr i
                | :? float as i when elementType = typeof<float> -> fillFast arr i
                | _ ->
                    // Slow case
                    Logger.trace "Slowly filling array with %d elements..." arr.Length
                    let rank = arr.Rank
                    let dims = Array.init rank id
                    let lengths = Array.map arr.GetLength dims
                    let lowerBounds = Array.map arr.GetLowerBound dims
                    let indices = allIndicesViaLens (Array.toList lowerBounds) (Array.toList lengths)
                    for i in indices do
                        arr.SetValue(value, Array.ofList i)

    let delinearizeArrayIndex idx (lengths : int array) (lowerBounds : int array) =
        let detachOne (acc, lensProd) dim =
            let curOffset = acc / lensProd
            let lb = if lowerBounds = null then 0 else lowerBounds.[dim]
            let curIndex = curOffset + lb
            let rest = acc % lensProd
            let lensProd = if dim = lengths.Length - 1 then 1 else lensProd / lengths.[dim + 1]
            curIndex, (rest, lensProd)
        let mutable lenProd = 1
        for i in 1 .. lengths.Length - 1 do
            lenProd <- lenProd * lengths.[i]
        Array.mapFold detachOne (idx, lenProd) (Array.init lengths.Length id) |> fst


    let mapToOneDArray mapper (arr : Array) : obj[] =
        if arr = null then null
        else
            let dest = Array.zeroCreate<obj> arr.Length
            let mutable i = 0
            for e in arr do
                dest.[i] <- mapper e
                i <- i + 1
            dest

module Option =
    let rec public sequenceM f list =
        let (>>=) x f = Option.bind f x
        let ret = Some
        match list with
        | [] -> ret []
        | h :: t -> f h >>= (fun h -> sequenceM f t >>= (fun t -> ret (h :: t)))
