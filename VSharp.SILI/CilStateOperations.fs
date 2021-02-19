namespace VSharp.Interpreter.IL

open VSharp
open System.Text
open System.Reflection
open VSharp.Core
open VSharp.Core.API
open ipOperations

type cilState =
    { ip : ip
      state : state
      filterResult : term option
      iie : InsufficientInformationException option
      level : level
      startingIP : ipEntry
      popsCount : int * int      // minimum and currentValue
    }
    member x.CanBeExpanded () =
        match x.ip with
        | {label = Instruction _} :: []
        | _ :: _ :: _ -> true
        | {label = Exit} :: [] -> false
        | [] -> __unreachable__()
        | _ -> true
    member x.HasException = Option.isSome x.state.exceptionsRegister.ExceptionTerm

module internal CilStateOperations =

    let makeCilState curV state =
        { ip = [curV]
          state = state
          filterResult = None
          iie = None
          level = PersistentDict.empty
          startingIP = curV
          popsCount = 0,0
        }

    let makeInitialState m state = makeCilState (instruction m 0) state

    let isIIEState (s : cilState) = Option.isSome s.iie
    let isError (s : cilState) = s.HasException
    let currentIp (s : cilState) = List.head s.ip
    let pushToIp (ip : ipEntry) (cilState : cilState) = {cilState with ip = ip :: cilState.ip}

    let rec withLastIp (ip : ipEntry) (cilState : cilState) =
        match cilState.ip with
        | _ :: ips -> {cilState with ip = ip :: ips}
        | [] -> __unreachable__()
//        | {label = Exit} :: ips -> moveCurrentIp ips
//        | {label = Instruction _} as ip :: ips ->
//            let nextIps = CFG.moveCurrentIp ip
//            assert(List.length nextIps = 1)
//            List.head nextIps :: ips
//        | [] -> __unreachable__()
//        | _ -> __notImplemented__()
    let withIp (ip : ip) (cilState : cilState) = {cilState with ip = ip}

    let composeIps (oldIp : ip) (newIp : ip) = newIp @ oldIp
//        match newIps, oldIps with
//        | {label = Exit} :: [] as exit, [] -> exit
//        | {label = Exit} :: [], _ -> oldIps // no need to moveCurrentIp, maybe we want to execute current ip
//        | _ -> newIps @ oldIps

    let compose (cilState1 : cilState) (cilState2 : cilState) =
        assert(currentIp cilState1 = cilState2.startingIP)

        let level =
            PersistentDict.fold (fun (acc : level) k v ->
                let oldValue = if PersistentDict.contains k acc then PersistentDict.find acc k else 0u
                PersistentDict.add k (v + oldValue) acc
            ) cilState1.level cilState2.level

        let ip = composeIps cilState1.ip (List.tail cilState2.ip)
        let states = Memory.ComposeStates cilState1.state cilState2.state id
        let leftOpStack = List.skip (-1 * fst cilState2.popsCount) cilState1.state.opStack
        let makeResultState (state : state) =
            let state' = {state with opStack = leftOpStack @ state.opStack}
            {cilState2 with state = state'; ip = ip; level = level; popsCount = cilState1.popsCount
                            startingIP = cilState1.startingIP}
        List.map makeResultState states



    let incrementLevel (cilState : cilState) k =
        let lvl = cilState.level
        let newValue = if PersistentDict.contains k lvl then PersistentDict.find lvl k + 1u else 1u
        {cilState with level = PersistentDict.add k newValue lvl}

    // ------------------------------- Helper functions for cilState and state interaction -------------------------------
    let stateOf (cilState : cilState) = cilState.state
    let popStackOf (cilState : cilState) = {cilState with state = Memory.PopStack cilState.state}

    let withCurrentTime time (cilState : cilState) = {cilState with state = {cilState.state with currentTime = time}}

    let withOpStack opStack (cilState : cilState) = {cilState with state = {cilState.state with opStack = opStack}}
    let withCallSiteResults callSiteResults (cilState : cilState) = {cilState with state = {cilState.state with callSiteResults = callSiteResults}}
    let addToCallSiteResults callSite res (cilState : cilState) =
        let s = cilState.state
        {cilState with state = {s with callSiteResults = Map.add callSite res s.callSiteResults}}

    let withState state (cilState : cilState) = {cilState with state = state}
    let changeState (cilState : cilState) state = {cilState with state = state}
    let withResult result (cilState : cilState) = {cilState with state = {cilState.state with returnRegister = Some result}}
    let withNoResult (cilState : cilState) = {cilState with state = {cilState.state with returnRegister = None}}
    let withResultState result (state : state) = {state with returnRegister = Some result}

    let pushToOpStack v (cilState : cilState) = {cilState with state = {cilState.state with opStack = v :: cilState.state.opStack}}
//    let addReturnPoint p (cilState : cilState) = {cilState with returnPoints = p :: cilState.returnPoints}
    let withException exc (cilState : cilState) = {cilState with state = {cilState.state with exceptionsRegister = exc}}

    let popOperationalStack (cilState : cilState) =
        match cilState.state.opStack with
        | t :: ts -> t, withOpStack ts cilState
        | [] -> __unreachable__()

    let pushNewObjForValueTypes (afterCall : cilState) =
        let ref, cilState = popOperationalStack afterCall
        let value = Memory.ReadSafe cilState.state ref
        pushToOpStack value afterCall

    let private isStaticConstructor (m : MethodBase) =
        m.IsStatic && m.Name = ".cctor"

    let rec moveCurrentIp (cilState : cilState) : cilState list =
        match cilState.ip with
        | {label = Instruction offset; method = m} :: _ ->
            let cfg = CFG.findCfg m
            let opCode = Instruction.parseInstruction m offset
            let m = cfg.methodBase
            let newIps =
                if Instruction.isLeaveOpCode opCode || opCode = Emit.OpCodes.Endfinally
                then cfg.graph.[offset] |> Seq.map (ipOperations.instruction m) |> List.ofSeq
                else
                    let nextTargets = Instruction.findNextInstructionOffsetAndEdges opCode cfg.ilBytes offset
                    match nextTargets with
                    | UnconditionalBranch nextInstruction
                    | FallThrough nextInstruction -> ipOperations.instruction m nextInstruction :: []
                    | Return -> ipOperations.exit m :: []
                    | ExceptionMechanism -> ipOperations.findingHandler m offset :: []
                    | ConditionalBranch targets -> targets |> List.map (ipOperations.instruction m)
            List.map (fun ip -> withLastIp ip cilState) newIps
        | {label = Exit} :: [] -> cilState :: []
        | {label = Exit; method = m} :: ips' when isStaticConstructor m -> {cilState with ip = ips'} :: []
        | {label = Exit} :: ({label = Instruction offset; method = m} as ip) :: ips' ->
            //TODO: assert(isCallIp ip)
            let callSite = Instruction.parseCallSite m offset
            let cilState =
                if callSite.HasNonVoidResult then
                    let result = cilState.state.opStack |> List.head |> Some
                    addToCallSiteResults callSite result cilState
                elif callSite.opCode = Emit.OpCodes.Newobj && callSite.calledMethod.DeclaringType.IsValueType then
                    pushNewObjForValueTypes cilState
                else cilState
            cilState |> popStackOf |> withIp (ip :: ips') |> moveCurrentIp
        | {label = Exit} :: {label = Exit} :: _ -> __unreachable__()
        | _ -> __notImplemented__()

    // ------------------------------- Helper functions for cilState -------------------------------

    let createCallSite source called offset opCode =
        {sourceMethod = source; calledMethod = called; offset = offset; opCode = opCode}

    let pushResultOnOpStack (cilState : cilState) (res, state) =
        if res <> Terms.Nop then cilState |> withState state |> pushToOpStack res
        else withState state cilState

    let pushResultToOperationalStack (cilStates : cilState list)  =
        cilStates |> List.map (fun (cilState : cilState) ->
            let state = cilState.state
            if state.exceptionsRegister.UnhandledError then cilState // TODO: check whether opStack = [] is needed
            else
                let opStack =
                    match state.returnRegister with
                    | None -> state.opStack
                    | Some r -> r :: state.opStack
                let state = {state with returnRegister = None; opStack = opStack}
                {cilState with state = state})

    let StatedConditionalExecutionCIL (cilState : cilState) (condition : state -> (term * state -> 'a) -> 'a) (thenBranch : cilState -> ('c list -> 'a) -> 'a) (elseBranch : cilState -> ('c list -> 'a) -> 'a) (k : 'c list -> 'a) =
        StatedConditionalExecution cilState.state condition
            (fun state k -> thenBranch {cilState with state = state} k)
            (fun state k -> elseBranch {cilState with state = state} k)
            (fun x y -> List.append x y |> List.singleton)
            (List.head >> k)
    let GuardedApplyCIL (cilState : cilState) term (f : cilState -> term -> ('a list -> 'b) -> 'b) (k : 'a list -> 'b) =
        GuardedStatedApplyk
            (fun state term k -> f {cilState with state = state} term k)
            cilState.state term id (List.concat >> k)

    let StatedConditionalExecutionAppendResultsCIL (cilState : cilState) conditionInvocation (thenBranch : (cilState -> (cilState list -> 'a) -> 'a)) elseBranch k =
         StatedConditionalExecution cilState.state conditionInvocation
            (fun state k -> thenBranch {cilState with state = state} k)
            (fun state k -> elseBranch {cilState with state = state} k)
            (fun x y -> [x; y])
            (List.concat >> k)

    let BranchOnNullCIL (cilState : cilState) term thenBranch elseBranch k =
        StatedConditionalExecutionAppendResultsCIL cilState
            (fun state k -> k (IsNullReference term, state))
            thenBranch
            elseBranch
            k

    // ------------------------------- Pretty printing for cilState -------------------------------
    let private dumpSection section (sb : StringBuilder) =
        sprintf "--------------- %s: ---------------" section |> sb.AppendLine

    let private dumpSectionValue section value (sb : StringBuilder) =
        sb |> dumpSection section |> (fun sb -> sb.AppendLine value)

    let private dumpDict section sort keyToString valueToString (sb : StringBuilder) d =
        if PersistentDict.isEmpty d then sb
        else
            let sb = dumpSection section sb
            PersistentDict.dump d sort keyToString valueToString |> sb.AppendLine

    let ipAndMethodBase2String (ip : ipEntry) =
        sprintf "Method: %O, label = %O" ip.method ip.label

    // TODO: print filterResult and IIE ?
    let dump (cilState : cilState) : string =
        let sb = dumpSectionValue "IP" (sprintf "%O" cilState.ip) (StringBuilder())
        let sb = dumpDict "Level" id ipAndMethodBase2String id sb cilState.level

        let stateDump = VSharp.Core.API.Memory.Dump cilState.state
        let sb = dumpSectionValue "State" stateDump sb

        if sb.Length = 0 then "<EmptyCilState>" else sb.ToString()
