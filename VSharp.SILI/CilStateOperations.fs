namespace VSharp.Interpreter.IL

open VSharp
open System.Text
open System.Reflection
open VSharp.Core
open VSharp.Core.API
open ipEntryOperations

type cilState =
    { ip : ip
      state : state
      filterResult : term option
      iie : InsufficientInformationException option
      level : level
      startingIP : ipEntry
      initialOpStackSize : uint32
    }

module internal CilStateOperations =

    let makeCilState curV initialOpStackSize state =
        { ip = [curV]
          state = state
          filterResult = None
          iie = None
          level = PersistentDict.empty
          startingIP = curV
          initialOpStackSize = initialOpStackSize
        }

    let makeInitialState m state = makeCilState (instruction m 0) 0u state

    let isIIEState (s : cilState) = Option.isSome s.iie

    let isExecutable (s : cilState) =
        match s.ip with
        | [] -> __unreachable__()
        | {label = Exit} :: [] -> false
        | _ -> true

    let isError (s : cilState) =
        match s.state.exceptionsRegister with
        | NoException -> false
        | _ -> true
    let isUnhandledError (s : cilState) =
        match s.state.exceptionsRegister with
        | Unhandled _ -> true
        | _ -> false

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
    let startingIpOf (cilState : cilState) = cilState.startingIP

    let composeIps (oldIp : ip) (newIp : ip) = newIp @ oldIp
//        match newIps, oldIps with
//        | {label = Exit} :: [] as exit, [] -> exit
//        | {label = Exit} :: [], _ -> oldIps // no need to moveCurrentIp, maybe we want to execute current ip
//        | _ -> newIps @ oldIps

    let composePopsCount (min1, cnt1) (_, cnt2) =
        let cnt = cnt1 + cnt2
        min min1 cnt, cnt

    let compose (cilState1 : cilState) (cilState2 : cilState) =
        assert(currentIp cilState1 = cilState2.startingIP)

        let level =
            PersistentDict.fold (fun (acc : level) k v ->
                let oldValue = if PersistentDict.contains k acc then PersistentDict.find acc k else 0u
                PersistentDict.add k (v + oldValue) acc
            ) cilState1.level cilState2.level

        let iie = None // we might concretize state, so we should try executed instructions again
        let ip = composeIps (List.tail cilState1.ip) cilState2.ip
        let states = Memory.ComposeStates cilState1.state cilState2.state id
        let leftOpStack = List.skip (int cilState2.initialOpStackSize) cilState1.state.opStack
        let makeResultState (state : state) =
            let state' = {state with opStack = state.opStack @ leftOpStack}
            {cilState2 with state = state'; ip = ip; level = level; initialOpStackSize = cilState1.initialOpStackSize
                            startingIP = cilState1.startingIP; iie = iie}
        List.map makeResultState states

    let incrementLevel (cilState : cilState) k =
        let lvl = cilState.level
        let newValue = if PersistentDict.contains k lvl then PersistentDict.find lvl k + 1u else 1u
        {cilState with level = PersistentDict.add k newValue lvl}

    // ------------------------------- Helper functions for cilState and state interaction -------------------------------
    let stateOf (cilState : cilState) = cilState.state
    let popStackOf (cilState : cilState) =
        let s = Memory.PopStack cilState.state
        let ip = List.tail cilState.ip
        {cilState with state = s; ip = ip}

    let withCurrentTime time (cilState : cilState) = {cilState with state = {cilState.state with currentTime = time}}

    let withOpStack opStack (cilState : cilState) = {cilState with state = {cilState.state with opStack = opStack}}
    let withCallSiteResults callSiteResults (cilState : cilState) = {cilState with state = {cilState.state with callSiteResults = callSiteResults}}
    let addToCallSiteResults callSite res (cilState : cilState) =
        let s = cilState.state
        {cilState with state = {s with callSiteResults = Map.add callSite res s.callSiteResults}}

    let withState state (cilState : cilState) = {cilState with state = state}
    let changeState (cilState : cilState) state = {cilState with state = state}

    let withNoResult (cilState : cilState) = {cilState with state = {cilState.state with returnRegister = None}}

    let pushToOpStack v (cilState : cilState) = {cilState with state = {cilState.state with opStack = v :: cilState.state.opStack}}
    let withException exc (cilState : cilState) = {cilState with state = {cilState.state with exceptionsRegister = exc}}

    let popOperationalStack (cilState : cilState) =
        match cilState.state.opStack with
        | t :: ts -> t, withOpStack ts cilState
        | [] -> __unreachable__()

    let pushNewObjForValueTypes (afterCall : cilState) =
        let ref, cilState = popOperationalStack afterCall
        let value = Memory.ReadSafe cilState.state ref
        pushToOpStack value cilState

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
                then cfg.graph.[offset] |> Seq.map (instruction m) |> List.ofSeq
                else
                    let nextTargets = Instruction.findNextInstructionOffsetAndEdges opCode cfg.ilBytes offset
                    match nextTargets with
                    | UnconditionalBranch nextInstruction
                    | FallThrough nextInstruction -> instruction m nextInstruction :: []
                    | Return -> exit m :: []
                    | ExceptionMechanism -> findingHandler m offset :: []
                    | ConditionalBranch targets -> targets |> List.map (instruction m)
            List.map (fun ip -> withLastIp ip cilState) newIps
        | {label = Exit} :: [] ->
            // TODO: add popStackOf here (golds will change)
            //|> withCurrentTime [] //TODO: #ask Misha about current time
            cilState :: []
        | {label = Exit; method = m} :: ips' when isStaticConstructor m ->
            cilState |> popStackOf |> withIp ips' |> List.singleton
        | {label = Exit} :: ({label = Instruction offset; method = m} as ip) :: ips' ->
            //TODO: assert(isCallIp ip)
            let callSite = Instruction.parseCallSite m offset
            let cilState =
                if callSite.HasNonVoidResult then
                    let result =
                        match cilState.state.opStack with
                        | res :: _ -> res
                        | [] -> __unreachable__()
                    addToCallSiteResults callSite (Some result) cilState
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

    let private dumpIp (ip : ip) =
        List.fold (fun acc entry -> sprintf "%s\n%O" acc entry) "" ip

    let ipAndMethodBase2String (ip : ipEntry) =
        sprintf "Method: %O, label = %O" ip.method ip.label

    // TODO: print filterResult and IIE ?
    let dump (cilState : cilState) : string =
        let sb = dumpSectionValue "Starting ip" (sprintf "%O" cilState.startingIP) (StringBuilder())
        let sb = dumpSectionValue "IP" (dumpIp cilState.ip) sb
        let sb = dumpSectionValue "IIE" (sprintf "%O" cilState.iie) sb
        let sb = dumpSectionValue "Initial OpStack Size" (sprintf "%O" cilState.initialOpStackSize) sb
        let sb = dumpDict "Level" id ipAndMethodBase2String id sb cilState.level

        let stateDump = VSharp.Core.API.Memory.Dump cilState.state
        let sb = dumpSectionValue "State" stateDump sb

        if sb.Length = 0 then "<EmptyCilState>" else sb.ToString()
