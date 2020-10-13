namespace VSharp.Analyzer

open System.Reflection
open System.Collections.Generic

open System.Reflection.Emit
open VSharp.Interpreter.IL
open CFG
open FSharpx.Collections
open VSharp
open VSharp.Core

module Properties =
    let internal exitVertexOffset = -1
    let internal exitVertexNumber = -1

    let internal initialVertexOffset = 0
    let internal initialVertexNumber = 0

module public CFA =
    //let mutable stepItp : StepInterpreter option = None
//    let configureInterpreter itp = stepItp <- Some itp


    type Vertex private(id, m : MethodBase, label : vertexLabel, opStack : operationalStack) =
        static let ids : Dictionary<MethodBase, int> = Dictionary<_,_>()
        let lemmas = Lemmas(m, label)
        let paths = Paths(m, label)
        let queries = Queries(m, label)
        let solver = null //Solver.SolverPool.mkSolver()
        let errors = List<cilState>()
        let incomingEdges: List<Edge> = List<_>()
        let outgoingEdges: List<Edge> = List<_>()
        member x.AddErroredStates (newErrors : cilState list) =
            errors.AddRange(newErrors)

        member x.Id with get() = id
        member x.Lemmas = lemmas
        member x.Paths with get () = paths
        member x.Queries = queries
        member x.Solver = solver
        member x.IncomingEdges = incomingEdges
        member x.OutgoingEdges = outgoingEdges
        member x.Label with get() = label
        member x.OpStack with get() = opStack
        member x.Method with get() = m
        member x.CommonPropagatePath lvl state =
            let pc = List.filter (fun cond -> cond <> Terms.True) state.pc
            let state = {state with pc = pc}
            let newPc = List.fold (fun pc cond -> pc &&& cond) Terms.True state.pc
            if newPc <> Terms.False then
                x.Paths.Add {lvl = lvl; state = state}
                true
            else false
        member x.IsMethodStartVertex with get() = label = FromCFG(0)
        member x.IsMethodExitVertex with get() = label = MethodCommonExit
        override x.ToString() =
            sprintf "(Method = %O, Label = %O, id = %d)\n" m label id +
            sprintf "Edges count = %d\n" x.OutgoingEdges.Count +
            "Edges: \n" + Seq.fold (fun acc edge -> acc + edge.ToString() + "\n") "" x.OutgoingEdges
        static member CreateVertex method label opStack =
            let id = Dict.getValueOrUpdate ids method (always 0)
            ids.[method] <- id + 1
            Vertex(id, method, label, opStack)
    and
        [<AbstractClass>]
        Edge(src : Vertex, dst : Vertex) =
        abstract member Type : string
        abstract member PropagatePath : ILInterpreter -> path -> Vertex list
        member x.PrintLog msg obj = Logger.printLog Logger.Trace "[%s]\n%s: %O" (x.commonToString()) msg obj
        member x.Src = src
        member x.Dst = dst
        member x.Method = x.Src.Method
        member x.CommonPropagatePath lvl state = if dst.CommonPropagatePath lvl state then [dst] else []
        override x.ToString() = x.commonToString()
        member x.commonToString() = sprintf "%s ID:[%d --> %d] Label:[%O --> %O] Method:%O" x.Type x.Src.Id x.Dst.Id x.Src.Label x.Dst.Label x.Method


    type 'a unitBlock =
        {
            entity : 'a
            entryPoint : Vertex
            exitVertex : Vertex
            vertices : Dictionary<int, Vertex>
        }
        with
        member x.AddVertex (v : Vertex) =
            if not <| x.vertices.ContainsKey v.Id then
                x.vertices.Add(v.Id, v)
        member x.WithEntryPoint v = {x with entryPoint = v}
        member x.WithExitVertex v = {x with exitVertex = v}
        member x.FindCallVertex id = x.vertices.[id]

        static member private CreateEmpty entity method entryOffset exitOffset =
            let entry = Vertex.CreateVertex method entryOffset []
            let exit = Vertex.CreateVertex method exitOffset []
            let vertices = Dictionary<int, Vertex>()
            vertices.Add(entry.Id, entry)
            vertices.Add(exit.Id, exit)
            {
                entity = entity
                entryPoint = entry
                exitVertex = exit
                vertices = vertices
            }
        static member CreateEmptyForMethod (method : MethodBase) =
            unitBlock<'a>.CreateEmpty method method (FromCFG Properties.initialVertexOffset) MethodCommonExit
        static member CreateEmptyForFinallyClause (m : MethodBase) (ehc : ExceptionHandlingClause) =
            let entryOffset = ehc.HandlerOffset
            // TODO: check if this formula is forever true
            let exitOffset = ehc.HandlerOffset + ehc.HandlerLength - 1
            unitBlock<'a>.CreateEmpty ehc m (FromCFG entryOffset) (FromCFG exitOffset)
        override x.ToString() =
            Seq.fold (fun acc vertex -> acc + "\n" + vertex.ToString()) "" x.vertices.Values

    type cfa =
            {
              cfg : cfg
              body : MethodBase unitBlock
              finallyHandlers : Dictionary<offset, ExceptionHandlingClause unitBlock>
              dstVertexForInsufficientInformationEdge : Vertex
            }
        with
            member x.TryFindVertexWithOffset offset =
                let tryFindInBlock (block : 'a unitBlock) =
                    block.vertices |> Seq.tryFind (fun kvp -> kvp.Value.Label = FromCFG offset)
                let acc = tryFindInBlock x.body
                Seq.fold (fun acc handlerBlock -> if Option.isNone acc then tryFindInBlock handlerBlock else acc) acc x.finallyHandlers.Values

            member x.Method = x.cfg.methodBase
            member x.FindOrCreateFinallyHandler (ehc : ExceptionHandlingClause) =
                let offset = ehc.HandlerOffset
                if x.finallyHandlers.ContainsKey offset then x.finallyHandlers.[offset]
                else
                    let block = unitBlock<ExceptionHandlingClause>.CreateEmptyForFinallyClause x.Method ehc
                    x.finallyHandlers.Add(offset, block)
                    block

            member x.WithEntryPoint v = {x with body = x.body.WithEntryPoint v}
            member x.WithExitVertex v = {x with body = x.body.WithExitVertex v}
            member x.WithFinallyEntryPoint offset v = x.finallyHandlers.[offset].WithEntryPoint v |> ignore; x
            member x.WithFinallyExitVertex offset v = x.finallyHandlers.[offset].WithExitVertex v |> ignore; x
            override x.ToString() =
                let separator = "\n"
                "Method: " + x.Method.ToString() + separator +
                x.body.ToString() + separator +
                Seq.fold (fun acc block -> acc + block.ToString() + separator) "" (x.finallyHandlers.Values)



    type StepEdge(src : Vertex, dst : Vertex, effect : state) =
        inherit Edge(src, dst)
        do
            Prelude.releaseAssert(Map.isEmpty effect.callSiteResults)
        override x.Type = "StepEdge"
        override x.PropagatePath _ (path : path) =
            Memory.ComposeStates path.state effect (fun state ->
                x.PrintLog "composition left"  <| Memory.Dump path.state
                x.PrintLog "composition right" <| Memory.Dump effect
                x.PrintLog "composition result" <| Memory.Dump state
                assert(path.state.frames = state.frames)
                x.CommonPropagatePath (path.lvl + 1u) state)

        member x.Effect = effect
        member x.VisibleVariables() = __notImplemented__()

        override x.ToString() =
            sprintf "%s\neffect = %O\npc = %O\n" (base.ToString()) (API.Memory.Dump effect) effect.pc

    type CallEdge(src : Vertex, dst : Vertex, callSite : callSite, thisOption : term option, args : term list) =
        inherit Edge(src, dst)
        override x.Type = "Call"
        override x.PropagatePath interpreter (path : path) =
            let addCallSiteResult callSiteResults callSite res = Map.add callSite res callSiteResults
            let k cilStates =
                let states = List.map (fun (cilState : cilState) -> cilState.state) cilStates
                let propagateStateAfterCall acc state =
                    assert(path.state.frames = state.frames)
                    assert(path.state.stack = state.stack)
//                    x.PrintLog "composition left" path.state
//                    x.PrintLog "composition this" thisOption
//                    x.PrintLog "composition args" args
//                    x.PrintLog "composition result" state
                    let result' = x.CommonPropagatePath (path.lvl + 1u) {state with callSiteResults = addCallSiteResult path.state.callSiteResults callSite state.returnRegister
                                                                                    returnRegister = None}
                    acc @ result'
                List.fold propagateStateAfterCall [] states
            let k1 results = results |> List.unzip |> snd |> k
            let fillTerm term = Memory.FillHoles path.state term fst
            let concreteArgs = List.map fillTerm args
            let concreteThis = Option.map fillTerm thisOption
            let concreteCilState = cilState.MakeEmpty (Instruction src.Label.Offset) (Instruction dst.Label.Offset) path.state

            match callSite.opCode with
            | Instruction.Call     ->
                interpreter.CommonCall callSite.calledMethod concreteCilState concreteThis concreteArgs k1
            | Instruction.NewObj   ->
                // TODO: why opStack?! too complex, make it simpler
                let cilStates = interpreter.CommonNewObj callSite.calledMethod {concreteCilState with opStack = List.rev concreteArgs} id
                cilStates |> List.map (fun (cilState : cilState) -> {cilState with state = {cilState.state with returnRegister = cilState.opStack |> List.head |> Some}}) |> k
            | Instruction.CallVirt -> interpreter.CommonCallVirt callSite.calledMethod concreteCilState (Option.get concreteThis) concreteArgs k1
            | _ ->  __notImplemented__()
        member x.ExitNodeForCall() = __notImplemented__()
        member x.CallVariables() = __notImplemented__()

    type InsufficientInformationEdge(offset, src : Vertex, this, opStack, cfa : cfa) =
        inherit Edge(src, cfa.dstVertexForInsufficientInformationEdge)
        override x.Type = "InsufficientInformationEdge"
        member x.FindDestinationVertex (cilState : cilState) =
            let offset = cilState.ip.Offset
            let vertex = cfa.TryFindVertexWithOffset offset
            match vertex with
            | None -> internalfailf "vertex with offset %x does not exist in cfa" offset
            | Some kvp -> kvp.Value
        override x.PropagatePath interpreter (path : path) =
            let canBePropagated = function
                | Instruction offset -> cfa.TryFindVertexWithOffset offset |> Option.isNone
                | Exit               -> false
                | FindingHandler _   -> __unreachable__()

            let fillTerm term = Memory.FillHoles path.state term fst
            let opStack = List.map fillTerm opStack
            let this    = Option.map fillTerm this
            let cilState = { cilState.MakeEmpty (Instruction offset) ip.Exit path.state with this = this; opStack = opStack }
            let iieWasThrownAgain, resultStates = interpreter.ExecuteInstructionsWhile canBePropagated cfa.cfg offset cilState
            Prelude.releaseAssert(not iieWasThrownAgain)
            resultStates
            |> List.map (fun (cilState : cilState) ->
                let vertex = x.FindDestinationVertex cilState
                let propagated = vertex.CommonPropagatePath path.lvl cilState.state
                propagated, vertex)
            |> List.filter fst
            |> List.map snd


    module cfaBuilder =
        let private alreadyComputedCFAs = Dictionary<MethodBase, cfa>()

        let private createEmptyCFA cfg method =
            {
              cfg = cfg
              body = unitBlock<MethodBase>.CreateEmptyForMethod method
              finallyHandlers = Dictionary<_,_>()
              dstVertexForInsufficientInformationEdge = Vertex.CreateVertex method InsufficientInformationLabel []
            }

        let private addEdge (edge : Edge) =
            edge.Src.OutgoingEdges.Add edge
            edge.Dst.IncomingEdges.Add edge

        let private executeInstructions cfg cilState =
            assert (cilState.ip.CanBeExpanded())
            let interpreter = ILInterpreter()
            let startingOffset = cilState.ip.Offset
            let endOffset =
                let lastOffset = Seq.last cfg.sortedOffsets
                if startingOffset = lastOffset then cfg.ilBytes.Length
                else
                    let index = cfg.sortedOffsets.BinarySearch startingOffset
                    cfg.sortedOffsets.[index + 1]
            let isOffsetOfCurrentVertex (ip : ip) = ip <> Exit && startingOffset <= ip.Offset && ip.Offset < endOffset
            interpreter.ExecuteInstructionsWhile isOffsetOfCurrentVertex cfg startingOffset cilState
        let computeCFAForMethod (initialCilState : cilState) (cfa : cfa) (used : Dictionary<vertexLabel * operationalStack, int>) (block : MethodBase unitBlock) =
            let cfg = cfa.cfg
            let executeSeparatedOpCode offset (opCode : System.Reflection.Emit.OpCode) (cilState : cilState) =
                let calledMethod = InstructionsSet.resolveMethodFromMetadata cfg (offset + opCode.Size)
                let callSite = { sourceMethod = cfg.methodBase; offset = offset; calledMethod = calledMethod; opCode = opCode }
                let args, stackWithoutCallArgs, neededResult, this =
                    let args, cilState = InstructionsSet.retrieveActualParameters calledMethod cilState
                    let this, cilState, neededResult =
                        match calledMethod with
                        | :? ConstructorInfo when opCode = OpCodes.Newobj -> None, cilState, true
                        | :? ConstructorInfo ->
                            let this, cilState = InstructionsSet.popStack cilState
                            this, cilState, false
                        | :? MethodInfo as methodInfo when not calledMethod.IsStatic || opCode = System.Reflection.Emit.OpCodes.Callvirt -> // TODO: check if condition `opCode = OpCodes.Callvirt` needed
                            let this, cilState = InstructionsSet.popStack cilState
                            this, cilState, methodInfo.ReturnType <> typedefof<System.Void>
                        | :? MethodInfo as methodInfo ->
                            None, cilState, methodInfo.ReturnType <> typedefof<System.Void>
                        | _ -> internalfailf "unknown methodBase %O" calledMethod
                    args, cilState.opStack, neededResult, this
                let nextOffset =
                    match Instruction.findNextInstructionOffsetAndEdges opCode cfg.ilBytes offset with
                    | FallThrough nextOffset -> nextOffset
                    | _ -> __unreachable__()
                let stackAfterCall =
                    // TODO: this is a temporary hack for newobj opcode, replace it with [HeapRef concreteAddress] when heapAddressKey.isAllocated would use vectorTime!
                    if neededResult then Terms.MakeFunctionResultConstant callSite :: stackWithoutCallArgs
                    else stackWithoutCallArgs
                // TODO: why no exceptions?
                nextOffset, this, args, { cilState with opStack = stackAfterCall }

            let rec computeCFAForBlock (block : unitBlock<'a>) =
                let createOrGetVertex = function
                    | Instruction offset, opStack when used.ContainsKey(FromCFG offset, opStack) ->
                        block.vertices.[used.[FromCFG offset, opStack]]
                    | Instruction offset, opStack ->
                        let vertex = Vertex.CreateVertex cfg.methodBase (FromCFG offset) opStack
                        block.AddVertex vertex
                        vertex
                    | Exit, [] -> block.exitVertex
                    | _ -> __unreachable__()

                // note: entry point and exit vertex must have been already added to unit block
                let rec bypass (vertex : Vertex) =
                    let id, label, opStack = vertex.Id, vertex.Label, vertex.OpStack
                    if used.ContainsKey (label, opStack) || label = InsufficientInformationLabel || label = MethodCommonExit then
                        Logger.printLog Logger.Trace "Again went to label = %O\nnopStack = %O" label opStack
                    else
                    let offset = label.Offset
                    let wasAdded = used.TryAdd((label, opStack), id)
                    Prelude.releaseAssert(wasAdded)
                    let srcVertex = block.vertices.[id]
                    Logger.printLog Logger.Trace "[Starting computing cfa for label = %O]\nopStack = %O" label opStack
                    match cfg.offsetsDemandingCall.ContainsKey offset with
                    | true ->
                        let opCode, calledMethod = cfg.offsetsDemandingCall.[offset]
                        let callSite = {sourceMethod = cfg.methodBase; offset = offset; calledMethod = calledMethod; opCode = opCode}
                        let nextOffset, this, args, cilState' = executeSeparatedOpCode offset opCode {initialCilState with ip = Instruction offset; opStack = opStack}
                        let dstVertex = createOrGetVertex (Instruction nextOffset, cilState'.opStack)
                        block.AddVertex dstVertex
                        addEdge <| CallEdge(srcVertex, dstVertex, callSite, this, args)
                        bypass dstVertex
                    | _ ->
                        let insufficientExceptionThrown, newStates = executeInstructions cfg {initialCilState with ip = Instruction offset; opStack = opStack}
                        if insufficientExceptionThrown then addEdge <| InsufficientInformationEdge(offset, srcVertex, initialCilState.this, opStack, cfa)
                        let goodStates = List.filter (fun (cilState : cilState) -> not cilState.HasException) newStates
                        let erroredStates = List.filter (fun (cilState : cilState) -> cilState.HasException) newStates
                        goodStates |> List.iter (fun (cilState' : cilState) ->
                            let dstVertex = createOrGetVertex (cilState'.ip, cilState'.opStack)
                            if not cilState'.leaveInstructionExecuted then addEdge <| StepEdge(srcVertex, dstVertex, cilState'.state)
                            else
                                Prelude.releaseAssert(List.isEmpty cilState'.opStack)
                                addEdgesToFinallyBlocks initialCilState.state srcVertex dstVertex
                            bypass dstVertex)
                        srcVertex.AddErroredStates erroredStates
                bypass block.entryPoint
            and addEdgesToFinallyBlocks emptyEffect (srcVertex : Vertex) (dstVertex : Vertex) =
                let method = cfg.methodBase
                let ehcs = method.GetMethodBody().ExceptionHandlingClauses
                           |> Seq.filter Instruction.isFinallyClause
                           |> Seq.filter (Instruction.shouldExecuteFinallyClause srcVertex.Label.Offset dstVertex.Label.Offset)
                           |> Seq.sortWith (fun ehc1 ehc2 -> ehc1.HandlerOffset - ehc2.HandlerOffset)
                let chainSequentialFinallyBlocks prevVertex (ehc : ExceptionHandlingClause) =
                    let finallyBlock = cfa.FindOrCreateFinallyHandler ehc
                    addEdge <| StepEdge(prevVertex, finallyBlock.entryPoint, emptyEffect)
                    computeCFAForBlock finallyBlock
                    finallyBlock.exitVertex
                let lastVertex = ehcs |> Seq.fold chainSequentialFinallyBlocks srcVertex
                addEdge <| StepEdge (lastVertex, dstVertex, emptyEffect)
            computeCFAForBlock block

        let computeCFA (ilmm: ILMethodMetadata) : cfa =
            let methodBase = ilmm.methodBase
            match alreadyComputedCFAs.ContainsKey methodBase with
            | true -> alreadyComputedCFAs.[methodBase]
            | _ ->
                let initialState, this, _ = ExplorerBase.FormInitialStateWithoutStatics ilmm
                Prelude.releaseAssert(Map.isEmpty initialState.callSiteResults && Option.isNone initialState.returnRegister)

//                Logger.printLog Logger.Trace "emptyState for method %O = %O" methodBase emptyState
                let cfg = CFG.build methodBase
                let cfa = createEmptyCFA cfg methodBase

                let used = Dictionary<vertexLabel * operationalStack, int>()
                let initialCilState = {cilState.MakeEmpty ip.Exit ip.Exit initialState with this = this} //DIRTY: ip.Exit ip.Exit
                computeCFAForMethod initialCilState cfa used cfa.body
                alreadyComputedCFAs.[methodBase] <- cfa
                Logger.printLog Logger.Trace "Computed cfa: %O" cfa
                cfa

type StepInterpreter() =
    inherit ILInterpreter()
    let visitedVertices : persistent<Dictionary<CFA.Vertex, uint32>> =
        let r = new persistent<_>(always (Dictionary<_,_>()), id) in r.Reset(); r
    let incrementCounter vertex =
        if not <| visitedVertices.Value.ContainsKey vertex then
            visitedVertices.Value.[vertex] <- 1u
        else visitedVertices.Value.[vertex] <- 1u + visitedVertices.Value.[vertex]
    override x.ReproduceEffect codeLoc state k = x.ExploreAndCompose codeLoc state k
    override x.CreateInstance exceptionType arguments state =
        let error = Nop
        (error, {state with exceptionsRegister = Unhandled error}) |> List.singleton
    member x.ForwardExploration (cfa : CFA.cfa) codeLoc initialState this (k : (term * state) list -> 'a) =
        let k =
            visitedVertices.Save()
            let k x = visitedVertices.Restore(); k x
            k

        let maxBorder = 50u
        let used (vertex : CFA.Vertex) =
            if vertex.IsMethodExitVertex then true
            elif visitedVertices.Value.ContainsKey vertex then
                visitedVertices.Value.[vertex] >= maxBorder
            else incrementCounter vertex
                 false

        let rec dfs lvl (vertex : CFA.Vertex) =
            if used vertex then ()
            else
                incrementCounter vertex
                let edges = vertex.OutgoingEdges
                let shouldGetAllPaths = true // TODO: resolve this problem: when set to ``true'' recursion works but very long, when set to ``false'' method recursion doesn't work at all
                let paths : path list = vertex.Paths.OfLevel shouldGetAllPaths lvl
                let newDsts = edges |> Seq.fold (fun acc (edge : CFA.Edge) ->
                    let propagated = Seq.map (edge.PropagatePath x) paths |> Seq.fold (@) acc
                    List.distinct propagated) []
                List.iter (dfs (lvl + 1u)) newDsts
        cfa.body.entryPoint.Paths.Add {lvl = 0u; state = initialState}
        dfs 0u cfa.body.entryPoint
        let resultStates = List.init (maxBorder |> int) (fun lvl -> cfa.body.exitVertex.Paths.OfLevel true (lvl |> uint32) |> List.ofSeq)
                         |> List.concat
                         |> List.map (fun (path : path) ->
                             let state = path.state
                             match state.returnRegister with
                             | None -> Nop, state
                             | Some res -> res, state)
        k resultStates

    override x.Invoke codeLoc =
        match codeLoc with
        | :? ILMethodMetadata as ilmm ->
            try
                let cfa = CFA.cfaBuilder.computeCFA ilmm
                x.ForwardExploration cfa codeLoc
            with
            | :? InsufficientInformationException -> base.Invoke codeLoc

        | _ -> internalfail "unhandled ICodeLocation instance"

