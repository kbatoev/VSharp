namespace VSharp.Interpreter.IL

open System.Collections.Generic
open VSharp
open CilStateOperations
open VSharp.Core

type SearchDirections =
    | Step
    | Compose of cilState list

type IndexedQueue() =
    let q = List<cilState>()
    member x.Add s = q.Add s

    member x.Remove s = let ok = q.Remove s in assert(ok)
    member x.GetStates () = List.ofSeq q


[<AbstractClass>]
type ISearcher() =
    abstract member PickNext : IndexedQueue -> cilState option
    abstract member GetSearchDirection : cilState -> SearchDirections
    member x.GetResults initialState (q : IndexedQueue) =
        let (|CilStateWithIIE|_|) (cilState : cilState) = cilState.iie
        let isResult (s : cilState) = s.startingIP = initialState.startingIP

        let allStates = q.GetStates() |> List.filter isResult
        let iieStates = List.filter isIIEState allStates
        let errors = List.filter isError allStates

        match iieStates, errors with
        | CilStateWithIIE iie :: _ , _ -> raise iie
        | _ :: _, _ -> __unreachable__()
        | _, _ :: _ -> internalfailf "exception handling is not implemented yet"
        | _ when allStates = [] -> internalfailf "No states were obtained. Most likely such a situation is a bug. Check it!"
        | _ -> allStates


type DummySearcher() =
    inherit ISearcher() with
        let maxBound = 10u // 10u is caused by number of iterations for tests: Always18, FirstEvenGreaterThen7
        member private x.Used (cilState : cilState) =
            PersistentDict.contains cilState.ip cilState.level && PersistentDict.find cilState.level cilState.ip >= maxBound
        override x.GetSearchDirection _ = Step
        override x.PickNext q =
            let canBePropagated (s : cilState) = not (isIIEState s || isError s) && s.CanBeExpanded() && not <| x.Used s
            let states = (q.GetStates()) |> List.filter canBePropagated
            match states with
            | x :: _ -> Some x
            | [] -> None

