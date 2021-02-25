namespace VSharp.Interpreter.IL

open System.Collections.Generic
open VSharp
open CilStateOperations
open VSharp.Core

type IndexedQueue() =
    let q = List<cilState>()
    member x.Add s = q.Add s

    member x.Remove s = let ok = q.Remove s in assert(ok)
    member x.GetStates () = List.ofSeq q

[<AbstractClass>]
type ISearcher() =
    let maxBound = 10u // 10u is caused by number of iterations for tests: Always18, FirstEvenGreaterThen7
    abstract member PickNext : IndexedQueue -> cilState option

    member x.Used (cilState : cilState) =
        let ip = currentIp cilState
        PersistentDict.contains ip cilState.level && PersistentDict.find cilState.level ip >= maxBound

    member x.GetResults initialState (q : IndexedQueue) =
        let (|CilStateWithIIE|_|) (cilState : cilState) = cilState.iie
        let isResult (s : cilState) = s.startingIP = initialState.startingIP

        let allStates = q.GetStates() |> List.filter isResult
        let iieStates = List.filter isIIEState allStates
        let nonErrors = List.filter (isError >> not) allStates

        match iieStates with
        | CilStateWithIIE iie :: _ -> raise iie
        | _ :: _ -> __unreachable__()
//        | _, _ :: _ -> internalfailf "exception handling is not implemented yet"
        | _ when nonErrors = [] -> internalfailf "No states were obtained. Most likely such a situation is a bug. Check it!"
        | _ -> nonErrors


type DummySearcher() =
    inherit ISearcher() with
        override x.PickNext q =
            let canBePropagated (s : cilState) =
                not (isIIEState s || isUnhandledError s) && isExecutable s && not <| x.Used s
            let states = (q.GetStates()) |> List.filter canBePropagated
            match states with
            | x :: _ -> Some x
            | [] -> None

