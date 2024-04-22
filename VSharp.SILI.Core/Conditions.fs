namespace VSharp.Core
open VSharp

// represents conjunction of conditions
type conditions = pset<term>

// Invariants:
// - conditions does not contain True
// - if conditions contains False then False is the only element in PC

module internal Conditions =

    let public empty : conditions = PersistentSet.empty<term>
    let public isEmpty pc = PersistentSet.isEmpty pc

    let public toSeq pc = PersistentSet.toSeq pc

    let private falsePC() = PersistentSet.add empty (False())

    let public isFalse pc =
        let isFalsePC = PersistentSet.contains (False()) pc
        if isFalsePC then assert(toSeq pc |> Seq.length = 1)
        isFalsePC

    let rec public add pc cond : conditions =
        match cond with
        | True -> pc
        | False -> falsePC()
        | _ when isFalse pc -> falsePC()
        | _ when PersistentSet.contains !!cond pc -> falsePC()
        | {term = Disjunction xs} ->
            let xs' = xs |> List.filter (fun x -> PersistentSet.contains !!x pc |> not)
            match xs' with
            | _ when List.isEmpty xs' -> falsePC()
            | _ when List.length xs' = List.length xs -> PersistentSet.add pc cond
            | _ -> add pc (disjunction xs')
        | _ ->
            let notCond = !!cond
            let pc' = pc |> PersistentSet.fold (fun pc e ->
                match e with
                | {term = Disjunction xs} when List.contains notCond xs ->
                    let e' = xs |> List.filter ((<>) notCond) |> disjunction
                    PersistentSet.add (PersistentSet.remove pc e) e'
                | _ -> pc) pc
            PersistentSet.add pc' cond

    let public mapPC mapper (pc : conditions) : conditions =
        let mapAndAdd acc cond k =
            let acc' = mapper cond |> add acc
            if isFalse acc' then falsePC() else k acc'
        Cps.Seq.foldlk mapAndAdd empty (toSeq pc) id
    let public mapSeq mapper (pc : conditions) = toSeq pc |> Seq.map mapper

    let toStringSeq pc = Seq.map toString pc |> Seq.sort |> join " /\ "

    let toString pc = mapSeq toString pc |> Seq.sort |> join " /\ "

    let union (pc1 : conditions) (pc2 : conditions) = Seq.fold add pc1 (toSeq pc2)
