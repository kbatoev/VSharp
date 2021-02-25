namespace VSharp.Interpreter.IL


type CFASearcher() =
    inherit ISearcher() with
        let maxBound = 10u // 10u is caused by number of iterations for tests: Always18, FirstEvenGreaterThen7
        member private x.Used (cilState : cilState) =
            let ip = currentIp cilState
            PersistentDict.contains ip cilState.level && PersistentDict.find cilState.level ip >= maxBound
        override x.GetSearchDirection _ = Step
        override x.PickNext q =
            let canBePropagated (s : cilState) = not (isIIEState s || isUnhandledError s) && s.CanBeExpanded() && not <| x.Used s
            let states = (q.GetStates()) |> List.filter canBePropagated
            match states with
            | x :: _ -> Some x
            | [] -> None





