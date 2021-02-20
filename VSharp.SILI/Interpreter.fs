namespace VSharp.Interpreter.IL

open System.Collections.Generic
open System.Reflection
open System.Reflection.Emit
open InstructionsSet
open CilStateOperations
open VSharp
open VSharp.Core
open ipEntryOperations

type cfg = CFG.cfgData

type public MethodInterpreter(searcher : ISearcher (*ilInterpreter : ILInterpreter, funcId : IFunctionIdentifier, cfg : cfg*)) =
    inherit ExplorerBase()

    member x.Interpret (_ : IFunctionIdentifier) (initialState : cilState) =
        let q = IndexedQueue()
        q.Add initialState

        let step s =
            match searcher.GetSearchDirection(s) with
            | Step ->
                let goodStates, incompleteStates, errors = ILInterpreter(x).ExecuteOnlyOneInstruction s
                goodStates @ incompleteStates @ errors
            | Compose states -> List.map (compose s) states |> List.concat
            |> List.iter q.Add

        let rec iter s =
            q.Remove s
            step s
            Option.iter iter (searcher.PickNext q)

        Option.iter iter (searcher.PickNext q)
        searcher.GetResults initialState q

    override x.Invoke funcId initialState k =
        let cilStates = x.InitializeStatics initialState funcId.Method.DeclaringType List.singleton
        assert(List.length cilStates = 1)
        let cilState = List.head cilStates
        x.Interpret funcId cilState |> k

    override x.MakeMethodIdentifier m = { methodBase = m } :> IMethodIdentifier

and public ILInterpreter(methodInterpreter : MethodInterpreter) as this =
    do
        opcode2Function.[hashFunction OpCodes.Call]           <- this.Call
        opcode2Function.[hashFunction OpCodes.Callvirt]       <- this.CallVirt
        opcode2Function.[hashFunction OpCodes.Newobj]         <- this.NewObj
        opcode2Function.[hashFunction OpCodes.Ldsfld]         <- zipWithOneOffset <| this.LdsFld false
        opcode2Function.[hashFunction OpCodes.Ldsflda]        <- zipWithOneOffset <| this.LdsFld true
        opcode2Function.[hashFunction OpCodes.Stsfld]         <- zipWithOneOffset <| this.StsFld
        opcode2Function.[hashFunction OpCodes.Ldfld]          <- zipWithOneOffset <| this.LdFld false
        opcode2Function.[hashFunction OpCodes.Ldflda]         <- zipWithOneOffset <| this.LdFld true
        opcode2Function.[hashFunction OpCodes.Stfld]          <- zipWithOneOffset <| this.StFld
        opcode2Function.[hashFunction OpCodes.Ldelem]         <- zipWithOneOffset <| this.LdElem
        opcode2Function.[hashFunction OpCodes.Ldelem_I1]      <- zipWithOneOffset <| fun _ _ -> this.LdElemTyp TypeUtils.int8Type
        opcode2Function.[hashFunction OpCodes.Ldelem_I2]      <- zipWithOneOffset <| fun _ _ -> this.LdElemTyp TypeUtils.int16Type
        opcode2Function.[hashFunction OpCodes.Ldelem_I4]      <- zipWithOneOffset <| fun _ _ -> this.LdElemTyp TypeUtils.int32Type
        opcode2Function.[hashFunction OpCodes.Ldelem_I8]      <- zipWithOneOffset <| fun _ _ -> this.LdElemTyp TypeUtils.int64Type
        opcode2Function.[hashFunction OpCodes.Ldelem_R4]      <- zipWithOneOffset <| fun _ _ -> this.LdElemTyp TypeUtils.float32TermType
        opcode2Function.[hashFunction OpCodes.Ldelem_R8]      <- zipWithOneOffset <| fun _ _ -> this.LdElemTyp TypeUtils.float64TermType
        opcode2Function.[hashFunction OpCodes.Ldelem_U1]      <- zipWithOneOffset <| fun _ _ -> this.LdElemTyp TypeUtils.uint8Type
        opcode2Function.[hashFunction OpCodes.Ldelem_U2]      <- zipWithOneOffset <| fun _ _ -> this.LdElemTyp TypeUtils.uint16Type
        opcode2Function.[hashFunction OpCodes.Ldelem_U4]      <- zipWithOneOffset <| fun _ _ -> this.LdElemTyp TypeUtils.uint32Type
        opcode2Function.[hashFunction OpCodes.Ldelem_Ref]     <- zipWithOneOffset <| fun _ _ -> this.LdElemRef
        opcode2Function.[hashFunction OpCodes.Stelem]         <- zipWithOneOffset <| this.StElem
        opcode2Function.[hashFunction OpCodes.Stelem_I1]      <- zipWithOneOffset <| fun _ _ -> this.StElemTyp TypeUtils.int8Type
        opcode2Function.[hashFunction OpCodes.Stelem_I2]      <- zipWithOneOffset <| fun _ _ -> this.StElemTyp TypeUtils.int16Type
        opcode2Function.[hashFunction OpCodes.Stelem_I4]      <- zipWithOneOffset <| fun _ _ -> this.StElemTyp TypeUtils.int32Type
        opcode2Function.[hashFunction OpCodes.Stelem_I8]      <- zipWithOneOffset <| fun _ _ -> this.StElemTyp TypeUtils.int64Type
        opcode2Function.[hashFunction OpCodes.Stelem_R4]      <- zipWithOneOffset <| fun _ _ -> this.StElemTyp TypeUtils.float32TermType
        opcode2Function.[hashFunction OpCodes.Stelem_R8]      <- zipWithOneOffset <| fun _ _ -> this.StElemTyp TypeUtils.float64TermType
        opcode2Function.[hashFunction OpCodes.Stelem_Ref]     <- zipWithOneOffset <| fun _ _ -> this.StElemRef
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_I1]    <- zipWithOneOffset <| fun _ _ -> this.ConvOvf TypeUtils.int8Type TypeUtils.int32Type
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_I2]    <- zipWithOneOffset <| fun _ _ -> this.ConvOvf TypeUtils.int16Type TypeUtils.int32Type
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_I4]    <- zipWithOneOffset <| fun _ _ -> this.ConvOvf TypeUtils.int32Type TypeUtils.int32Type
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_I8]    <- zipWithOneOffset <| fun _ _ -> this.ConvOvf TypeUtils.int64Type TypeUtils.int64Type
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_U1]    <- zipWithOneOffset <| fun _ _ -> this.ConvOvf TypeUtils.uint8Type TypeUtils.int32Type
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_U2]    <- zipWithOneOffset <| fun _ _ -> this.ConvOvf TypeUtils.uint16Type TypeUtils.int32Type
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_U4]    <- zipWithOneOffset <| fun _ _ -> this.ConvOvf TypeUtils.uint32Type TypeUtils.int32Type
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_U8]    <- zipWithOneOffset <| fun _ _ -> this.ConvOvf TypeUtils.uint64Type TypeUtils.int64Type
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_I1_Un] <- zipWithOneOffset <| fun _ _ -> this.ConvOvfUn TypeUtils.uint32Type TypeUtils.int8Type TypeUtils.int32Type
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_I2_Un] <- zipWithOneOffset <| fun _ _ -> this.ConvOvfUn TypeUtils.uint32Type TypeUtils.int16Type TypeUtils.int32Type
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_I4_Un] <- zipWithOneOffset <| fun _ _ -> this.ConvOvfUn TypeUtils.uint32Type TypeUtils.int32Type TypeUtils.int32Type
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_I8_Un] <- zipWithOneOffset <| fun _ _ -> this.ConvOvfUn TypeUtils.uint64Type TypeUtils.int64Type TypeUtils.int64Type
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_U1_Un] <- zipWithOneOffset <| fun _ _ -> this.ConvOvfUn TypeUtils.uint32Type TypeUtils.uint8Type TypeUtils.int32Type
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_U2_Un] <- zipWithOneOffset <| fun _ _ -> this.ConvOvfUn TypeUtils.uint32Type TypeUtils.uint16Type TypeUtils.int32Type
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_U4_Un] <- zipWithOneOffset <| fun _ _ -> this.ConvOvfUn TypeUtils.uint32Type TypeUtils.uint32Type TypeUtils.int32Type
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_U8_Un] <- zipWithOneOffset <| fun _ _ -> this.ConvOvfUn TypeUtils.uint64Type TypeUtils.uint64Type TypeUtils.int64Type
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_I]     <- Options.HandleNativeInt opcode2Function.[hashFunction OpCodes.Conv_Ovf_I4]    opcode2Function.[hashFunction OpCodes.Conv_Ovf_I8]
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_I_Un]  <- Options.HandleNativeInt opcode2Function.[hashFunction OpCodes.Conv_Ovf_I4_Un] opcode2Function.[hashFunction OpCodes.Conv_Ovf_I8_Un]
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_U]     <- Options.HandleNativeInt opcode2Function.[hashFunction OpCodes.Conv_Ovf_U4]    opcode2Function.[hashFunction OpCodes.Conv_Ovf_U8]
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_U_Un]  <- Options.HandleNativeInt opcode2Function.[hashFunction OpCodes.Conv_Ovf_U4_Un] opcode2Function.[hashFunction OpCodes.Conv_Ovf_U8_Un]
        opcode2Function.[hashFunction OpCodes.Castclass]      <- zipWithOneOffset <| this.CastClass
        opcode2Function.[hashFunction OpCodes.Ldlen]          <- zipWithOneOffset <| fun _ _ -> this.LdLen
        opcode2Function.[hashFunction OpCodes.Ldvirtftn]      <- zipWithOneOffset <| this.LdVirtFtn
        opcode2Function.[hashFunction OpCodes.Box]            <- zipWithOneOffset <| this.Box
        opcode2Function.[hashFunction OpCodes.Unbox]          <- zipWithOneOffset <| this.Unbox
        opcode2Function.[hashFunction OpCodes.Unbox_Any]      <- zipWithOneOffset <| this.UnboxAny
        opcode2Function.[hashFunction OpCodes.Add_Ovf_Un]     <- zipWithOneOffset <| fun _ _ -> this.Add_ovf_un
        opcode2Function.[hashFunction OpCodes.Sub_Ovf_Un]     <- zipWithOneOffset <| fun _ _ -> this.Sub_ovf_un
        opcode2Function.[hashFunction OpCodes.Mul_Ovf_Un]     <- zipWithOneOffset <| fun _ _ -> this.Mul_ovf_un
        opcode2Function.[hashFunction OpCodes.Add_Ovf]        <- zipWithOneOffset <| fun _ _ -> this.Add_ovf
        opcode2Function.[hashFunction OpCodes.Sub_Ovf]        <- zipWithOneOffset <| fun _ _ -> this.Sub_ovf
        opcode2Function.[hashFunction OpCodes.Mul_Ovf]        <- zipWithOneOffset <| fun _ _ -> this.Mul_ovf
        opcode2Function.[hashFunction OpCodes.Div]            <- zipWithOneOffset <| fun _ _ -> this.Div
        opcode2Function.[hashFunction OpCodes.Div_Un]         <- zipWithOneOffset <| fun _ _ -> this.DivUn
        opcode2Function.[hashFunction OpCodes.Rem]            <- zipWithOneOffset <| fun _ _ -> this.Rem
        opcode2Function.[hashFunction OpCodes.Rem_Un]         <- zipWithOneOffset <| fun _ _ -> this.RemUn
        opcode2Function.[hashFunction OpCodes.Newarr]         <- zipWithOneOffset <| this.Newarr

    let internalImplementations : Map<string, (cilState -> term option -> term list -> cilState list)> =
        Map.ofList [
            "System.Int32 System.Array.GetLength(this, System.Int32)", this.CommonGetArrayLength
            "System.Int32 System.Array.GetLowerBound(this, System.Int32)", this.GetArrayLowerBound
            "System.Void System.Runtime.CompilerServices.RuntimeHelpers.InitializeArray(System.Array, System.RuntimeFieldHandle)", this.CommonInitializeArray
        ]
    let __corruptedStack__() = raise (System.InvalidProgramException())

    member private x.Raise createException (cilState : cilState) k =
        //TODO: exception handling
        let statesWithCreatedExceptions : cilState list = createException cilState
        k statesWithCreatedExceptions

    member private x.AccessArray accessor (cilState : cilState) upperBound index k =
        let checkArrayBounds upperBound x =
            let lowerBound = Concrete 0 Types.TLength
            let notTooSmall = Arithmetics.(>>=) x lowerBound
            let notTooLarge = Arithmetics.(<<) x upperBound
            notTooSmall &&& notTooLarge
        StatedConditionalExecutionAppendResultsCIL cilState
            (fun state k -> k (checkArrayBounds upperBound index, state))
            accessor
            (x.Raise x.IndexOutOfRangeException)
            k

    member private x.AccessArrayDimension accessor (cilState : cilState) (this : term) (dimension : term) =
        let upperBound = Memory.ArrayRank cilState.state this
        x.AccessArray (accessor this dimension) cilState upperBound dimension id
    member private x.CommonGetArrayLength (cilState : cilState) thisOption args =
        match args with
        | dimensionsKey :: [] ->
            let arrayLengthByDimension arrayRef index cilState (k : cilState list -> 'a) =
                cilState |> pushToOpStack (Memory.ArrayLengthByDimension cilState.state arrayRef index) |> List.singleton |> k
            x.AccessArrayDimension arrayLengthByDimension cilState (Option.get thisOption) dimensionsKey
        | _ -> internalfail "unexpected number of arguments"

    member private x.GetArrayLowerBound (cilState : cilState) (this : term option) args =
        match args with
        | dimension :: [] ->
            let arrayLowerBoundByDimension arrayRef index (cilState : cilState) k =
                cilState |> pushToOpStack (Memory.ArrayLowerBoundByDimension cilState.state arrayRef index) |> List.singleton |> k
            x.AccessArrayDimension arrayLowerBoundByDimension cilState (Option.get this) dimension
        | _ -> internalfail "unexpected number of arguments"

    member private x.NpeOrInvokeStatementCIL (cilState : cilState) (this : term) statement (k : cilState list -> 'a) =
         StatedConditionalExecutionCIL cilState
            (fun state k -> k (IsNullReference this, state))
            (x.Raise x.NullReferenceException)
            statement
            k

    member private x.CommonInitializeArray (cilState : cilState) _ (args : term list) =
        match args with
        | arrayRef :: handleTerm :: [] ->
            x.NpeOrInvokeStatementCIL cilState arrayRef (fun cilState k ->
            x.NpeOrInvokeStatementCIL cilState handleTerm (fun cilState k ->
            let results : state list = VSharp.System.Runtime_CompilerServices_RuntimeHelpers.InitializeArray cilState.state arrayRef handleTerm
            let cilResults = List.map (fun state -> withState state cilState) results
            k cilResults) k) id
        | _ -> internalfail "unexpected number of arguments"
    member private x.InlineMethodBaseCallIfNeeded (methodBase : MethodBase) (cilState : cilState) (k : cilState list -> 'a) =
        // because we have correspondence between ips and frames
        assert(let ip = currentIp cilState in ip.method = methodBase && ip.label = Instruction 0)

        let s = cilState.state
        let thisOption = if methodBase.IsStatic then None else Some <| Memory.ReadThis s methodBase
        let args = methodBase.GetParameters() |> Seq.map (Memory.ReadArgument s) |> List.ofSeq
        let fullMethodName = Reflection.GetFullMethodName methodBase
        let (&&&) = Microsoft.FSharp.Core.Operators.(&&&)
        let moveIp (cilState : cilState) =
            let ip =
                match cilState.ip with
                | ip :: _ -> {label = Exit; method = ip.method}
                | _ -> __unreachable__()
            cilState |> withLastIp ip

        if Map.containsKey fullMethodName internalImplementations then
            (internalImplementations.[fullMethodName] cilState thisOption args) |> (List.map moveIp >> k)
        elif Map.containsKey fullMethodName Loader.internalImplementations then
            let thisAndArguments = optCons args thisOption
            internalCall Loader.internalImplementations.[fullMethodName] thisAndArguments s (List.map (changeState cilState >> moveIp) >> k)
        elif Map.containsKey fullMethodName Loader.concreteExternalImplementations then
            // TODO: check that all parameters were specified
            let methodInfo = Loader.concreteExternalImplementations.[fullMethodName]
            let thisOption, args =
                match thisOption, methodInfo.IsStatic with
                | Some this, true -> None, this :: args
                | None, false -> internalfail "Calling non-static concrete implementation for static method"
                | _ -> thisOption, args
            let s = Memory.PopStack s
            let state = methodInterpreter.ReduceFunctionSignature s methodInfo thisOption (Specified args) false id
            // NOTE: callsite of cilState is explicitly untouched
            cilState |> withState state |> withLastIp (instruction methodInfo 0) |> List.singleton |> k
        elif int (methodBase.GetMethodImplementationFlags() &&& MethodImplAttributes.InternalCall) <> 0 then
            internalfailf "new extern method: %s" fullMethodName
        elif methodBase.GetMethodBody() <> null then
            cilState |> List.singleton |> k
        else
            internalfail "non-extern method without body!"

    member x.CallMethodFromTermType (cilState : cilState) (*this parameters *) termType (calledMethod : MethodInfo) (k : cilState list -> 'a) =
        let t = termType |> Types.ToDotNetType
        let genericCalledMethod = if calledMethod.IsGenericMethod then calledMethod.GetGenericMethodDefinition() else calledMethod
        let genericMethodInfo =
            match genericCalledMethod.DeclaringType with
            | t1 when t1.IsInterface ->
                let createSignature (m : MethodInfo) =
                    m.GetParameters() |> Seq.map (fun p -> (p.ParameterType |> safeGenericTypeDefinition).FullName)
                    |> join ","
                let onlyLastName (m : MethodInfo) =
                    match m.Name.LastIndexOf('.') with
                    | i when i < 0 -> m.Name
                    | i -> m.Name.Substring(i + 1)
                let sign = createSignature genericCalledMethod
                let lastName = onlyLastName genericCalledMethod
                let methods =
                    match t with
                    | _ when t.IsArray -> t.GetMethods()
                    | _ -> t.GetInterfaceMap(t1).TargetMethods
                methods |> Seq.find (fun mi -> createSignature mi = sign && onlyLastName mi = lastName)
            | _ ->
                let (|||) = Microsoft.FSharp.Core.Operators.(|||)
                let allMethods = t.GetMethods(BindingFlags.Instance ||| BindingFlags.Public ||| BindingFlags.NonPublic)
                Seq.find (fun (mi : MethodInfo) -> mi.GetBaseDefinition() = genericCalledMethod.GetBaseDefinition()) allMethods
        let targetMethod = if genericMethodInfo.IsGenericMethod then genericMethodInfo.MakeGenericMethod(calledMethod.GetGenericArguments()) else genericMethodInfo
        if targetMethod.IsAbstract
            then x.CallAbstract (methodInterpreter.MakeMethodIdentifier targetMethod) cilState k
            else
                // TODO: this is a hack, because we don't must have FillHoles to obtain "this" right type before allocating it on frame
                let this = Memory.ReadThis cilState.state calledMethod
                let args = calledMethod.GetParameters() |> Seq.map (Memory.ReadArgument cilState.state) |> List.ofSeq
                let cilState = popStackOf cilState
                methodInterpreter.ReduceFunctionSignature cilState.state targetMethod (Some this) (Specified args) false (fun rightState ->
                x.InlineMethodBaseCallIfNeeded targetMethod {cilState with state = rightState} k)

    member x.CallVirtualMethod (ancestorMethod : MethodInfo) (cilState : cilState) (k : cilState list -> 'a) =
        let methodId = methodInterpreter.MakeMethodIdentifier ancestorMethod
        let this = Memory.ReadThis cilState.state ancestorMethod
        let callVirtual (cilState : cilState) this k =
            let baseType = BaseTypeOfHeapRef cilState.state this
            let callForConcreteType typ state k =
                x.CallMethodFromTermType state typ ancestorMethod k
            let tryToCallForBaseType (cilState : cilState) (k : cilState list -> 'a) =
                StatedConditionalExecutionAppendResultsCIL cilState
                    (fun state k -> k (API.Types.TypeIsRef baseType this, state))
                    (callForConcreteType baseType)
                    (x.CallAbstract methodId)
                    k
            let baseDotNetType = Types.ToDotNetType baseType
            if baseDotNetType.IsInterface
                then x.CallAbstract methodId cilState k
                else tryToCallForBaseType cilState k
        GuardedApplyCIL cilState this callVirtual k

    member x.CallAbstract funcId cilState k =
        methodInterpreter.CallAbstractMethod funcId cilState k

    member private x.ConvOvf targetType typeForStack (cilState : cilState) = // TODO: think about getting rid of typeForStack
        let typIsLessTyp : Dictionary<symbolicType, list<symbolicType>> = Dictionary<_,_>()
        typIsLessTyp.[TypeUtils.int8Type] <- [TypeUtils.int8Type; TypeUtils.int16Type; TypeUtils.int32Type; TypeUtils.int64Type]
        typIsLessTyp.[TypeUtils.int16Type] <- [TypeUtils.int16Type; TypeUtils.int32Type; TypeUtils.int64Type]
        typIsLessTyp.[TypeUtils.int32Type] <- [TypeUtils.int32Type; TypeUtils.int64Type]
        typIsLessTyp.[TypeUtils.int64Type] <- [TypeUtils.int64Type]

        typIsLessTyp.[TypeUtils.uint8Type] <- [TypeUtils.uint8Type; TypeUtils.uint16Type; TypeUtils.uint32Type; TypeUtils.uint64Type]
        typIsLessTyp.[TypeUtils.uint16Type] <- [TypeUtils.uint16Type; TypeUtils.uint32Type; TypeUtils.uint64Type]
        typIsLessTyp.[TypeUtils.uint32Type] <- [TypeUtils.uint32Type; TypeUtils.uint64Type]
        typIsLessTyp.[TypeUtils.uint64Type] <- [TypeUtils.uint64Type]
        let less leftTyp rightTyp = List.contains rightTyp typIsLessTyp.[leftTyp]

        let minMax : Dictionary<symbolicType, int64 * int64> = Dictionary<_,_>()
        minMax.[TypeUtils.int8Type] <- (System.SByte.MinValue |> int64, System.SByte.MaxValue |> int64)
        minMax.[TypeUtils.int16Type] <- (System.Int16.MinValue |> int64, System.Int16.MaxValue |> int64)
        minMax.[TypeUtils.int32Type] <- (System.Int32.MinValue |> int64, System.Int32.MaxValue |> int64)
        minMax.[TypeUtils.int64Type] <- (System.Int64.MinValue, System.Int64.MaxValue)
        minMax.[TypeUtils.uint8Type] <- (System.Byte.MinValue |> int64, System.Byte.MaxValue |> int64)
        minMax.[TypeUtils.uint16Type] <- (System.UInt16.MinValue |> int64, System.UInt16.MaxValue |> int64)
        minMax.[TypeUtils.uint32Type] <- (System.UInt32.MinValue |> int64, System.UInt32.MaxValue |> int64)
        minMax.[TypeUtils.uint64Type] <- (System.UInt64.MinValue |> int64, System.UInt64.MaxValue |> int64)


        let getSegment leftTyp rightTyp =
            let min1, max1 = minMax.[leftTyp]
            let min2, max2 = minMax.[rightTyp]
            match min1 < min2, max1 < max2 with
            | true, true   -> min2, max1
            | true, false  -> min2, max2
            | false, true  -> min1, max1
            | false, false -> min1, max2

        let canCastWithoutOverflow term targetTermType =
            let (<<=) = API.Arithmetics.(<<=)
            assert(TypeUtils.isInteger term)
            let termType = Terms.TypeOf term
            if less termType targetTermType then True
            elif termType = TypeUtils.int64Type && targetTermType = TypeUtils.uint64Type then
                let int64Zero = MakeNumber (0 |> int64)
                int64Zero <<= term
            elif termType = TypeUtils.uint64Type && targetTermType = TypeUtils.int64Type then
                let uint64RightBorder = MakeNumber (System.Int64.MaxValue |> uint64)
                term <<= uint64RightBorder
            else
                let min, max = getSegment termType targetTermType
                let leftBorder  = Concrete min termType // must save type info, because min is int64
                let rightBorder = Concrete max termType // must save type info, because max is int64
                (leftBorder <<= term) &&& (term <<= rightBorder)
        match cilState.state.opStack with
        | t :: stack ->
            StatedConditionalExecutionCIL (withOpStack stack cilState)
                (fun state k -> k (canCastWithoutOverflow t targetType, state))
                (fun cilState k ->
                    let castedResult = castUnchecked typeForStack (Types.Cast t targetType) cilState.state
                    pushToOpStack castedResult cilState |> List.singleton |> k)
                (x.Raise x.OverflowException)
                id
        | _ -> __corruptedStack__()
    member private x.ConvOvfUn unsignedSightType targetType typeForStack (cilState : cilState) = // TODO: think about getting rid of typeForStack
        match cilState.state.opStack with
        | t :: stack ->
            let unsignedT = castUnchecked unsignedSightType t cilState.state
            x.ConvOvf targetType typeForStack (withOpStack (unsignedT::stack) cilState)
        | _ -> __corruptedStack__()
    member private x.CommonCastClass (cilState : cilState) (term : term) (typ : symbolicType) k =
        let term = castReferenceToPointerIfNeeded term typ cilState.state
        StatedConditionalExecutionAppendResultsCIL cilState
            (fun state k -> k (IsNullReference term ||| Types.IsCast typ term, state))
            (fun cilState k -> cilState |> pushToOpStack (Types.Cast term typ) |> List.singleton |> k)
            (x.Raise x.InvalidCastException)
            k
    member private x.CastClass (cfg : cfg) offset (cilState : cilState) : cilState list =
        match cilState.state.opStack with
        | term :: stack ->
            let typ = resolveTermTypeFromMetadata cilState.state cfg (offset + OpCodes.Castclass.Size)
            x.CommonCastClass (withOpStack stack cilState) term typ pushResultToOperationalStack
        | _ -> __corruptedStack__()


    member private x.PushNewObjResultOnOpStack (cilState : cilState) reference (calledMethod : MethodBase) =
        let valueOnStack =
            if calledMethod.DeclaringType.IsValueType then
                  Memory.ReadSafe cilState.state reference
            else reference
        pushToOpStack valueOnStack cilState

//    member private x.RenewCallSiteResultsAndOpStack (initialState : state) (callSite : callSite) (cilState : cilState) =
//        let cilState : cilState = cilState |> withOpStack initialState.opStack |> withCallSiteResults initialState.callSiteResults
//        let resultState = cilState.state
//        match resultState.returnRegister with
//        | Some res as rr ->
//            assert(callSite.HasNonVoidResult)
//            cilState |> pushToOpStack res |> addToCallSiteResults callSite res |> withNoResult
//        | None when callSite.opCode = OpCodes.Newobj ->
//            let reference = Memory.ReadThis initialState callSite.calledMethod
//            x.PushNewObjResultOnOpStack cilState reference callSite.calledMethod
//        | None -> cilState

    member x.CommonCall (calledMethodBase : MethodBase) (cilState : cilState) (k : cilState list -> 'a) =
        let call cilState k = x.InlineMethodBaseCallIfNeeded calledMethodBase cilState k
        match calledMethodBase.IsStatic with
        | true -> call cilState k
        | false ->
            let this = Memory.ReadThis cilState.state calledMethodBase
            x.NpeOrInvokeStatementCIL cilState this call k
    member x.RetrieveCalledMethodAndArgs (opCode : OpCode) (calledMethodBase : MethodBase) (cilState : cilState) =
        let args, cilState = retrieveActualParameters calledMethodBase cilState
        let this, cilState = if calledMethodBase.IsStatic || opCode = OpCodes.Newobj then None, cilState
                             else popOperationalStack cilState |> mapfst Some
        this, args, cilState

    member x.Call (cfg : cfg) offset _ (cilState : cilState) =
        let calledMethod = resolveMethodFromMetadata cfg (offset + OpCodes.Call.Size)
        methodInterpreter.InitializeStatics cilState calledMethod.DeclaringType (fun cilState ->
        let this, args, cilState = x.RetrieveCalledMethodAndArgs OpCodes.Call calledMethod cilState
        methodInterpreter.ReduceFunctionSignatureCIL cilState calledMethod this (Specified args) false (fun cilState ->
        x.CommonCall calledMethod cilState id))
     member x.CommonCallVirt (ancestorMethodBase : MethodBase) (cilState : cilState) (k : cilState list -> 'a) =
        let this = Memory.ReadThis cilState.state ancestorMethodBase
        let call (cilState : cilState) k =
            if ancestorMethodBase.DeclaringType.IsSubclassOf typedefof<System.Delegate> && ancestorMethodBase.Name = "Invoke" then
                Lambdas.invokeDelegate cilState this k
            elif ancestorMethodBase.IsVirtual && not ancestorMethodBase.IsFinal then
                let methodInfo = ancestorMethodBase :?> MethodInfo
                x.CallVirtualMethod methodInfo cilState k
            else
                x.InlineMethodBaseCallIfNeeded ancestorMethodBase cilState k
        x.NpeOrInvokeStatementCIL cilState this call k
    member x.CallVirt (cfg : cfg) offset _ (cilState : cilState) =
        let ancestorMethod = resolveMethodFromMetadata cfg (offset + OpCodes.Call.Size)
        let this, args, cilState = x.RetrieveCalledMethodAndArgs OpCodes.Callvirt ancestorMethod cilState
        // NOTE: there is no need to initialize statics, because they were initialized before ``newobj'' execution
        // NOTE: It is not quite strict to ReduceFunctionSignature here because, but it does not matter because signatures of virtual methods are the same
        methodInterpreter.ReduceFunctionSignature cilState.state ancestorMethod this (Specified args) false (fun state ->
        x.CommonCallVirt ancestorMethod (withState state cilState) id)
    member x.ReduceArrayCreation (arrayType : System.Type) (cilState : cilState) (parameters : term list) k =
        let arrayTyp = Types.FromDotNetType cilState.state arrayType
        let reference, state = Memory.AllocateDefaultArray cilState.state parameters arrayTyp
        withResultState reference state |> changeState cilState |> List.singleton |> k
    member x.CommonCreateDelegate (ctor : ConstructorInfo) (cilState : cilState) (args : term list) (k : cilState list -> 'a) =
        let target, methodPtr =
            assert(List.length args = 2)
            args.[0], args.[1]

        let retrieveMethodInfo methodPtr =
            match methodPtr.term with
            | Concrete(:? MethodInfo as mi, _) -> mi
            | _ -> __unreachable__()

        let invoke cilState =
            GuardedApplyCIL cilState methodPtr
                (fun cilState methodPtr k ->
                    BranchOnNullCIL cilState target
                        (x.Raise x.NullReferenceException)
                        (x.InlineMethodBaseCallIfNeeded (retrieveMethodInfo methodPtr))
                        k)

        let typ = Types.FromDotNetType cilState.state ctor.DeclaringType
        Lambdas.make invoke typ (fun lambda ->
        let deleg, state = Memory.AllocateDelegate cilState.state lambda
        let state = withResultState deleg state
        withState state cilState |> List.singleton |> k)
    member x.CommonNewObj isCallNeeded (constructorInfo : ConstructorInfo) (cilState : cilState) (args : term list) (k : cilState list -> 'a) : 'a =
        __notImplemented__()
//        let typ = constructorInfo.DeclaringType
//        let constructedTermType = typ |> Types.FromDotNetType cilState.state
//        let blockCase (cilState : cilState) =
//            let callConstructor (cilState : cilState) reference afterCall =
//                if isCallNeeded then
//                    methodInterpreter.ReduceFunctionSignatureCIL cilState constructorInfo (Some reference) (Specified args) false (fun cilState ->
//                    x.InlineMethodBaseCallIfNeeded constructorInfo cilState afterCall)
//                else withResultState reference cilState.state |> changeState cilState |> List.singleton
//            let referenceTypeCase (cilState : cilState) =
//                let ref, state = Memory.AllocateDefaultClass cilState.state constructedTermType
//                callConstructor (withState state cilState) ref (List.map (pushToOpStack ref))
//            let valueTypeCase (cilState : cilState) =
//                let freshValue = Memory.DefaultOf constructedTermType
//                let ref, state = Memory.AllocateTemporaryLocalVariable cilState.state typ freshValue
//                let modifyResult (cilState : cilState) =
//                    let value = Memory.ReadSafe cilState.state ref
//                    pushToOpStack value cilState
//                callConstructor (withState state cilState) ref (List.map modifyResult)
//            if Types.IsValueType constructedTermType then valueTypeCase cilState
//            else referenceTypeCase cilState
//        let nonDelegateCase (cilState : cilState) =
//            if typ.IsArray && constructorInfo.GetMethodBody() = null
//                then x.ReduceArrayCreation typ cilState args id
//                else blockCase cilState
//        if Reflection.IsDelegateConstructor constructorInfo
//            then x.CommonCreateDelegate constructorInfo cilState args k
//            else nonDelegateCase cilState |> k

    member x.NewObj (cfg : cfg) offset _ (cilState : cilState) =
        let calledMethod = resolveMethodFromMetadata cfg (offset + OpCodes.Newobj.Size)
        assert(calledMethod.IsConstructor)

        let constructorInfo = calledMethod :?> ConstructorInfo
        let typ = constructorInfo.DeclaringType
        methodInterpreter.InitializeStatics cilState constructorInfo.DeclaringType (fun cilState ->
        let this, args, cilState = x.RetrieveCalledMethodAndArgs OpCodes.Newobj calledMethod cilState
        assert(Option.isNone this)

        let constructedTermType = typ |> Types.FromDotNetType cilState.state
        let wasConstructorCalled (beforeCall : cilState) (afterCall : cilState) =
               List.length afterCall.state.frames = List.length beforeCall.state.frames

        let modifyValueResultIfConstructorWasCalled (beforeCall : cilState) (afterCall : cilState) =
            if wasConstructorCalled beforeCall afterCall then pushNewObjForValueTypes afterCall
            else afterCall

        let blockCase (cilState : cilState) =
            let callConstructor (cilState : cilState) reference afterCall =
                methodInterpreter.ReduceFunctionSignatureCIL cilState constructorInfo (Some reference) (Specified args) false (fun cilState ->
                x.InlineMethodBaseCallIfNeeded constructorInfo cilState afterCall)

            if Types.IsValueType constructedTermType then
                let freshValue = Memory.DefaultOf constructedTermType
                let ref, state = Memory.AllocateTemporaryLocalVariable cilState.state typ freshValue
                let cilState = cilState |> withState state |> pushToOpStack ref //NOTE: ref is used to retrieve constructed struct
                callConstructor cilState ref (List.map (modifyValueResultIfConstructorWasCalled cilState))
            else
                let ref, state = Memory.AllocateDefaultClass cilState.state constructedTermType
                let cilState = cilState |> withState state |> pushToOpStack ref //NOTE: ref is used as result afterCall
                callConstructor cilState ref id

        if Reflection.IsDelegateConstructor constructorInfo then
            x.CommonCreateDelegate constructorInfo cilState args id
        elif typ.IsArray && constructorInfo.GetMethodBody() = null then
            x.ReduceArrayCreation typ cilState args id
        else blockCase cilState)

    member x.LdsFld addressNeeded (cfg : cfg) offset (cilState : cilState) =
        let fieldInfo = resolveFieldFromMetadata cfg (offset + OpCodes.Ldsfld.Size)
        assert (fieldInfo.IsStatic)
        methodInterpreter.InitializeStatics cilState fieldInfo.DeclaringType (fun cilState ->
        let declaringTermType = fieldInfo.DeclaringType |> Types.FromDotNetType cilState.state
        let fieldId = Reflection.wrapField fieldInfo
        let value = if addressNeeded
                    then StaticField(declaringTermType, fieldId) |> Ref
                    else Memory.ReadStaticField cilState.state declaringTermType fieldId
        pushToOpStack value cilState :: [])
    member private x.StsFld (cfg : cfg) offset (cilState : cilState) =
        let fieldInfo = resolveFieldFromMetadata cfg (offset + OpCodes.Stsfld.Size)
        let state = cilState.state
        assert (fieldInfo.IsStatic)
        let declaringTermType = fieldInfo.DeclaringType |> Types.FromDotNetType state
        let fieldId = Reflection.wrapField fieldInfo
        match state.opStack with
        | value :: stack ->
            methodInterpreter.InitializeStatics cilState fieldInfo.DeclaringType (fun cilState ->
            let fieldType = fieldInfo.FieldType |> Types.FromDotNetType cilState.state
            let value = castUnchecked fieldType value cilState.state
            let state = Memory.WriteStaticField cilState.state declaringTermType fieldId value
            cilState |> withState state |> withOpStack stack |> List.singleton)
        | _ -> __corruptedStack__()
    member x.LdFld addressNeeded (cfg : cfg) offset (cilState : cilState) =
        let fieldInfo = resolveFieldFromMetadata cfg (offset + OpCodes.Ldfld.Size)
        assert (not fieldInfo.IsStatic)
        match cilState.state.opStack with
        | target :: stack ->
            let loadWhenTargetIsNotNull (cilState : cilState) k =
                let k1 value = pushToOpStack value cilState |> List.singleton |> k
                let fieldId = Reflection.wrapField fieldInfo
                if addressNeeded then Memory.ReferenceField target fieldId |> k1
                else Memory.ReadField cilState.state target fieldId |> k1
            x.NpeOrInvokeStatementCIL (withOpStack stack cilState) target loadWhenTargetIsNotNull id
        | _ -> __corruptedStack__()
    member x.StFld (cfg : cfg) offset (cilState : cilState) =
        let fieldInfo = resolveFieldFromMetadata cfg (offset + OpCodes.Stfld.Size)
        assert (not fieldInfo.IsStatic)
        match cilState.state.opStack with
        | value :: targetRef :: stack ->
            let storeWhenTargetIsNotNull (cilState : cilState) k =
                let fieldType = fieldInfo.FieldType |> Types.FromDotNetType cilState.state
                let fieldId = Reflection.wrapField fieldInfo
                let reference = Memory.ReferenceField targetRef fieldId
                let value = castUnchecked fieldType value cilState.state
                Memory.WriteSafe cilState.state reference value |> List.map (changeState cilState) |> k
            x.NpeOrInvokeStatementCIL (withOpStack stack cilState) targetRef storeWhenTargetIsNotNull id
        | _ -> __corruptedStack__()
    member private x.LdElemWithCast cast (cilState : cilState) : cilState list =
        match cilState.state.opStack with
        | index :: arrayRef :: stack ->
            let uncheckedLdElem (cilState : cilState) k =
                let value = Memory.ReadArrayIndex cilState.state arrayRef [index]
                let castedValue = cast value cilState.state
                pushToOpStack castedValue cilState |> List.singleton |> k
            let checkedLdElem (cilState : cilState) k =
                let length = Memory.ArrayLengthByDimension cilState.state arrayRef (MakeNumber 0)
                x.AccessArray uncheckedLdElem cilState length index k
            x.NpeOrInvokeStatementCIL (withOpStack stack cilState) arrayRef checkedLdElem id
        | _ -> __corruptedStack__()
    member private x.LdElemTyp typ (cilState : cilState) = x.LdElemWithCast (castUnchecked typ) cilState
    member private x.LdElem (cfg : cfg) offset (cilState : cilState) =
        let typ = resolveTermTypeFromMetadata cilState.state cfg (offset + OpCodes.Ldelem.Size)
        x.LdElemTyp typ cilState
    member private x.LdElemRef = x.LdElemWithCast always
    member private x.StElemWithCast cast (cilState : cilState) =
        match cilState.state.opStack with
        | value :: index :: arrayRef :: stack ->
            let checkedStElem (cilState : cilState) (k : cilState list -> 'a) =
                let typeOfValue = TypeOf value
                let uncheckedStElem (cilState : cilState) (k : cilState list -> 'a) =
                    let typedValue = cast value cilState.state
                    Memory.WriteArrayIndex cilState.state arrayRef [index] typedValue |> List.map (changeState cilState) |> k
                let checkTypeMismatchBasedOnTypeOfValue cond (cilState : cilState) =
                    StatedConditionalExecutionAppendResultsCIL cilState
                        (fun state k -> k (cond, state))
                        uncheckedStElem
                        (x.Raise x.ArrayTypeMismatchException)
                let rec checkTypeMismatch (cilState : cilState) (k : cilState list -> 'a) =
                    let baseType = arrayRef |> BaseTypeOfHeapRef cilState.state |> Types.ElementType
                    if Types.IsValueType typeOfValue then
                        checkTypeMismatchBasedOnTypeOfValue (Types.TypeIsType typeOfValue baseType) cilState k
                    else
                        checkTypeMismatchBasedOnTypeOfValue (Types.RefIsType value baseType) cilState k
                let length = Memory.ArrayLengthByDimension cilState.state arrayRef (MakeNumber 0)
                x.AccessArray checkTypeMismatch cilState length index k
            x.NpeOrInvokeStatementCIL (withOpStack stack cilState) arrayRef checkedStElem id
        | _ -> __corruptedStack__()
    member private x.StElemTyp typ (cilState : cilState) =
        x.StElemWithCast (castUnchecked typ) cilState
    member private x.StElem (cfg : cfg) offset (cilState : cilState) =
        let typ = resolveTermTypeFromMetadata cilState.state cfg (offset + OpCodes.Stelem.Size)
        x.StElemTyp typ cilState
    member private x.StElemRef = x.StElemWithCast always
    member private x.LdLen (cilState : cilState) =
        match cilState.state.opStack with
        | arrayRef :: stack ->
            let ldlen (cilState : cilState) k =
                let length = Memory.ArrayLengthByDimension cilState.state arrayRef (MakeNumber 0)
                pushToOpStack length cilState |> List.singleton |> k
            x.NpeOrInvokeStatementCIL (withOpStack stack cilState) arrayRef ldlen id
        | _ -> __corruptedStack__()
    member private x.LdVirtFtn (_ : cfg) _ (_ : cilState) =
        __notImplemented__()
//        let ancestorMethodBase = resolveMethodFromMetadata cfg (offset + OpCodes.Ldvirtftn.Size)
//        match cilState.opStack with
//        | this :: stack ->
//            let ldvirtftn (cilState : cilState) k =
//                assert(isReference this)
//                let t = this |> SightTypeOfRef |> Types.ToDotNetType
//                let methodInfo = t.GetMethod(ancestorMethodBase.Name, allBindingFlags)
//                let methodPtr = Terms.Concrete methodInfo (Types.FromDotNetType cilState.state (methodInfo.GetType()))
//                k [methodPtr, cilState]
//            x.NpeOrInvokeStatement {cilState with opStack = stack} this ldvirtftn pushFunctionResults
//        | _ -> __corruptedStack__()
    member x.BoxNullable (t : System.Type) v (cilState : cilState) : cilState list =
        __notImplemented__()
//        // TODO: move it to Reflection.fs; add more validation in case if .NET implementation does not have these methods
//        let boxValue (cilState : cilState) =
//            match cilState.state.returnRegister with
//            | None -> __unreachable__()
//            | Some value ->
//                let address, state = Memory.BoxValueType cilState.state value
//                cilState |> withState state |> withResult address
//
//        let hasValueMethodInfo = t.GetMethod("get_HasValue")
//        let hasValueCase (cilState : cilState) k =
//            let valueMethodInfo = t.GetMethod("get_Value")
//            methodInterpreter.ReduceFunctionSignature cilState.state valueMethodInfo (Some v) (Specified []) false (fun state ->
//            x.InlineMethodBaseCallIfNeeded valueMethodInfo (withState state cilState) ((List.map boxValue) >> k))
//        let boxNullable (hasValue, cilState : cilState) (k : cilState list -> 'a) =
//            StatedConditionalExecutionAppendResultsCIL cilState
//                (fun state k -> k (hasValue, state))
//                hasValueCase
//                (fun cilState k -> cilState |> withResult NullRef |> List.singleton |> k)
//                k
//
//        methodInterpreter.ReduceFunctionSignatureCIL cilState hasValueMethodInfo (Some v) (Specified []) false (fun cilState ->
//        x.InlineMethodBaseCallIfNeeded hasValueMethodInfo cilState (fun hasValueResults ->
//        let hasValueResults = hasValueResults |> List.map (fun cilState -> Option.get cilState.state.returnRegister, cilState)
//        Cps.List.mapk boxNullable hasValueResults (List.concat >> pushResultToOperationalStack)))


    member x.Box (cfg : cfg) offset (cilState : cilState) =

        let t = resolveTypeFromMetadata cfg (offset + OpCodes.Box.Size)
        let termType = Types.FromDotNetType cilState.state t
        match cilState.state.opStack with
        | v :: stack ->
            if Types.IsValueType termType then
                let cilState = withOpStack stack cilState
                if Types.TypeIsNullable termType then x.BoxNullable t v cilState
                else allocateValueTypeInHeap v cilState
            else [cilState]
        | _ -> __corruptedStack__()
    member private x.UnboxCommon (cilState : cilState) (obj : term) (t : System.Type) (handleRestResults : term * state -> term * state) (k : cilState list -> 'a) =
        let nonExceptionCont (cilState : cilState) res state k =
            cilState |> withState state |> pushToOpStack res |> List.singleton |> k
        let termType = Types.FromDotNetType cilState.state t
        assert(IsReference obj)
        assert(Types.IsValueType termType)
        let nullCase (cilState : cilState) (k : cilState list -> 'a) : 'a =
            if Types.TypeIsNullable termType then
                let nullableTerm = Memory.DefaultOf termType
                let address, state = Memory.BoxValueType cilState.state nullableTerm
                let res, state = handleRestResults (HeapReferenceToBoxReference address, state)
                nonExceptionCont cilState res state k
            else
                x.Raise x.NullReferenceException cilState k
        let canCastValueTypeToNullableTargetCase (cilState : cilState) =
            let underlyingTypeOfNullableT = System.Nullable.GetUnderlyingType t
            StatedConditionalExecutionAppendResultsCIL cilState
                (fun state k -> k (Types.RefIsType obj (Types.FromDotNetType state underlyingTypeOfNullableT), state))
                (fun cilState k ->
                    let value = Memory.ReadSafe cilState.state obj
                    let nullableTerm = Memory.DefaultOf termType
                    let valueField, hasValueField = Reflection.fieldsOfNullable t
                    let nullableTerm = Memory.WriteStructField nullableTerm valueField value
                    let nullableTerm = Memory.WriteStructField nullableTerm hasValueField (MakeBool true)
                    let address, state = Memory.BoxValueType cilState.state nullableTerm
                    let res, state = handleRestResults(address, state)
                    nonExceptionCont cilState res state k)
                (x.Raise x.InvalidCastException)
        let nonNullCase (cilState : cilState) =
            if Types.TypeIsNullable termType then
                canCastValueTypeToNullableTargetCase cilState
            else
                StatedConditionalExecutionAppendResultsCIL cilState
                    (fun state k -> k (Types.IsCast termType obj, state)) // TODO: Why not Types.RefIsType method?
                    (fun cilState k ->
                        let res, state = handleRestResults(Types.Cast obj termType |> HeapReferenceToBoxReference, cilState.state)
                        cilState |> withState state |> pushToOpStack res |> List.singleton |> k)
                    (x.Raise x.InvalidCastException)

        BranchOnNullCIL cilState obj
            nullCase
            nonNullCase
            k

    member private x.Unbox (cfg : cfg) offset (cilState : cilState) =
        let t = resolveTypeFromMetadata cfg (offset + OpCodes.Unbox.Size)
        match cilState.state.opStack with
        | _ :: _ when t.IsGenericParameter -> __notImplemented__() // TODO: Nullable.GetUnderlyingType for generics; use meta-information of generic type parameter
        | obj :: stack ->
            let state = {cilState.state with opStack = stack}
            x.UnboxCommon (withOpStack stack cilState) obj t id pushResultToOperationalStack
        | _ -> __corruptedStack__()

    member private x.UnboxAny (cfg : cfg) offset (cilState : cilState) =
        let t = resolveTypeFromMetadata cfg (offset + OpCodes.Unbox_Any.Size)
        let state = cilState.state
        let termType = Types.FromDotNetType state t
        let valueType = Types.FromDotNetType state typeof<System.ValueType>

        match cilState.state.opStack with
        | _ :: _ when t.IsGenericParameter -> __insufficientInformation__ "Can't introduce generic type X for equation: T = Nullable<X>"  // TODO: Nullable.GetUnderlyingType for generics; use meta-information of generic type parameter
        | obj :: stack ->
            StatedConditionalExecutionAppendResultsCIL (withOpStack stack cilState)
                (fun state k -> k (Types.TypeIsType termType valueType, state))
                (fun cilState k ->
                    let handleRestResults (address, state : state) = Memory.ReadSafe state address, state
                    x.UnboxCommon cilState obj t handleRestResults k)
                (fun state k -> x.CommonCastClass state obj termType k)
                pushResultToOperationalStack
        | _ -> __corruptedStack__()

    member private this.CommonDivRem performAction (cilState : cilState) =
        let integerCase (cilState : cilState) x y minusOne minValue =
            assert(TypeOf x = TypeOf y)
            StatedConditionalExecutionCIL cilState
                (fun state k -> k (Arithmetics.IsZero y, state))
                (this.Raise this.InvalidCastException)
                (fun cilState ->
                    StatedConditionalExecutionCIL cilState
                        (fun state k -> k ((x === minValue) &&& (y === minusOne), state))
                        (this.Raise this.InvalidCastException)
                        (fun cilState k -> cilState |> pushToOpStack (performAction x y) |> List.singleton |> k))
                id
        match cilState.state.opStack with
        | TypeUtils.Float y :: TypeUtils.Float x :: stack ->
            cilState |> withOpStack (performAction x y :: stack) |> List.singleton
        | TypeUtils.Int64 y :: x :: stack
        | TypeUtils.UInt64 y :: x :: stack
        | y :: TypeUtils.Int64 x :: stack
        | y :: TypeUtils.UInt64 x :: stack ->
            integerCase (withOpStack stack cilState) x y TypeUtils.Int64.MinusOne TypeUtils.Int64.MinValue
        | y :: x :: stack ->
            integerCase (withOpStack stack cilState) x y TypeUtils.Int32.MinusOne TypeUtils.Int32.MinValue
        | _ -> __corruptedStack__()
    member private this.Div (cilState : cilState) =
        let div x y = API.PerformBinaryOperation OperationType.Divide x y id
        this.CommonDivRem div cilState

    member private this.Rem (cilState : cilState) =
        let rem x y = API.PerformBinaryOperation OperationType.Remainder x y id
        this.CommonDivRem rem cilState

    member private this.CommonUnsignedDivRem isRem performAction (cilState : cilState) =
        match cilState.state.opStack with
        | y :: x :: stack when TypeUtils.isInteger x && TypeUtils.isInteger y ->
            let x = makeUnsignedInteger x id
            let y = makeUnsignedInteger y id
            StatedConditionalExecutionCIL (withOpStack stack cilState)
                (fun state k -> k (Arithmetics.IsZero y, state))
                (this.Raise this.DivideByZeroException)
                (fun cilState k -> cilState |> pushToOpStack (performAction x y) |> List.singleton |> k)
                id
        | TypeUtils.Float _ :: _
        | _ :: TypeUtils.Float _ :: _ when isRem -> internalfailf "Rem.Un is unspecified for Floats"
        | _ -> __corruptedStack__()
    member private this.DivUn (cilState : cilState) =
        let div x y = API.PerformBinaryOperation OperationType.Divide x y id
        this.CommonUnsignedDivRem false div cilState

    member private this.RemUn cilState =
        let rem x y = API.PerformBinaryOperation OperationType.Remainder x y id
        this.CommonUnsignedDivRem true rem cilState

    member private this.UnsignedCheckOverflow checkOverflowForUnsigned (cilState : cilState) =
        match cilState.state.opStack with
        | TypeUtils.Int64 y :: x :: stack
        | y :: TypeUtils.Int64 x :: stack
        | TypeUtils.UInt64 y :: x :: stack
        | y :: TypeUtils.UInt64 x :: stack ->
            let x = makeUnsignedInteger x id
            let y = makeUnsignedInteger y id
            let max = TypeUtils.UInt64.MaxValue
            let zero = TypeUtils.UInt64.Zero
            checkOverflowForUnsigned zero max x y (withOpStack stack cilState)  // TODO: maybe rearrange x and y if y is concrete and x is symbolic
        | y :: x :: stack when TypeUtils.isInteger x && TypeUtils.isInteger y ->
            let x, y = makeUnsignedInteger x id, makeUnsignedInteger y id
            let max = TypeUtils.UInt32.MaxValue
            let zero = TypeUtils.UInt32.Zero
            checkOverflowForUnsigned zero max x y (withOpStack stack cilState) // TODO: maybe rearrange x and y if y is concrete and x is symbolic
        | _ -> __corruptedStack__()
    member private this.SignedCheckOverflow checkOverflow (cilState : cilState) =
        match cilState.state.opStack with
        | TypeUtils.Int64 y :: x :: stack
        | y :: TypeUtils.Int64 x :: stack ->
            let min = TypeUtils.Int64.MinValue
            let max = TypeUtils.Int64.MaxValue
            let zero = TypeUtils.Int64.Zero
            let minusOne = TypeUtils.Int64.MinusOne
            checkOverflow min max zero minusOne x y (withOpStack stack cilState) // TODO: maybe rearrange x and y if y is concrete and x is symbolic
        | TypeUtils.UInt64 _ :: _ :: _
        | _ :: TypeUtils.UInt64 _ :: _ -> __unreachable__() // instead of add_ovf should be called add_ovf_un
        | TypeUtils.Float _ :: _
        | _ :: TypeUtils.Float _ :: _ -> __unreachable__() // only integers
        | y :: x :: stack ->
            let min = TypeUtils.Int32.MinValue
            let max = TypeUtils.Int32.MaxValue
            let zero = TypeUtils.Int32.Zero
            let minusOne = TypeUtils.Int32.MinusOne
            checkOverflow min max zero minusOne x y (withOpStack stack cilState) // TODO: maybe rearrange x and y if y is concrete and x is symbolic
        | _ -> __corruptedStack__()
    member private this.Add_ovf (cilState : cilState) =
        // min <= x + y <= max
        let checkOverflow min max zero _ x y cilState =
            let (>>=) = API.Arithmetics.(>>=)
            let xMoreThan0 state k = k (x >>= zero, state)
            let yMoreThan0 state k = k (y >>= zero, state)
            let checkOverflowWhenMoreThan0 (state : state) k = // x >= 0 && y >= 0
                PerformBinaryOperation OperationType.Subtract max y (fun diff ->
                k (diff >>= x, state))
            let checkOverflowWhenLessThan0 (state : state) k =
                PerformBinaryOperation OperationType.Subtract min y (fun diff ->
                k (x >>= diff, state))
            let add (cilState : cilState) k = // no overflow
                PerformBinaryOperation OperationType.Add x y (fun sum -> pushToOpStack sum cilState |> List.singleton |> k)
            StatedConditionalExecutionCIL cilState xMoreThan0
                (fun cilState -> // x >= 0
                    StatedConditionalExecutionCIL cilState yMoreThan0
                        (fun cilState -> // y >= 0
                            StatedConditionalExecutionCIL cilState
                                checkOverflowWhenMoreThan0
                                add
                                (this.Raise this.OverflowException))
                        add)
                (fun cilState -> // x < 0
                    StatedConditionalExecutionCIL cilState yMoreThan0
                        add
                        (fun cilState -> // x < 0 && y < 0
                            StatedConditionalExecutionCIL cilState
                                checkOverflowWhenLessThan0
                                add
                                (this.Raise this.OverflowException)))
                id
        this.SignedCheckOverflow checkOverflow cilState
    member private this.Mul_ovf (cilState : cilState) =
        // min <= x * y <= max
        let checkOverflow min max zero _ x y cilState =
            let (>>=) = API.Arithmetics.(>>=)
            let (>>) = API.Arithmetics.(>>)
            let isZero state k = k ((x === zero) ||| (y === zero), state)
            let xMoreThan0 state k = k (x >> zero, state)
            let yMoreThan0 state k = k (y >> zero, state)
            let checkOverflowWhenXM0YM0 (state : state) k = // x > 0 && y > 0
                PerformBinaryOperation OperationType.Divide max y (fun quotient ->
                k (quotient >>= x, state))
            let checkOverflowWhenXL0YL0 (state : state) k = // x < 0 && y < 0
                PerformBinaryOperation OperationType.Divide max y (fun quotient ->
                k (x >>= quotient, state))
            let checkOverflowWhenXM0YL0 (state : state) k = // x > 0 && y < 0
                PerformBinaryOperation OperationType.Divide min x (fun quotient ->
                k (y >>= quotient, state))
            let checkOverflowWhenXL0YM0 (state : state) k = // x < 0 && y > 0
                PerformBinaryOperation OperationType.Divide min y (fun quotient ->
                k (x >>= quotient, state))
            let mul (cilState : cilState) k = // no overflow
                PerformBinaryOperation OperationType.Multiply x y (fun res -> pushToOpStack res cilState |> List.singleton |> k)
            StatedConditionalExecutionCIL cilState isZero
                (fun cilState k -> cilState |> pushToOpStack zero |> List.singleton |> k)
                (fun cilState ->
                    StatedConditionalExecutionCIL cilState
                        xMoreThan0
                        (fun cilState -> // x > 0
                            StatedConditionalExecutionCIL cilState yMoreThan0
                                (fun cilState -> // y > 0
                                    StatedConditionalExecutionCIL cilState
                                        checkOverflowWhenXM0YM0
                                        mul
                                        (this.Raise this.OverflowException))
                                (fun cilState -> // y < 0
                                    StatedConditionalExecutionCIL cilState
                                        checkOverflowWhenXM0YL0
                                        mul
                                        (this.Raise this.OverflowException)))
                        (fun cilState -> // x < 0
                            StatedConditionalExecutionCIL cilState
                                yMoreThan0
                                (fun cilState -> // y > 0
                                    StatedConditionalExecutionCIL cilState
                                        checkOverflowWhenXL0YM0
                                        mul
                                        (this.Raise this.OverflowException))
                                (fun cilState k -> // y < 0
                                    StatedConditionalExecutionCIL cilState
                                        checkOverflowWhenXL0YL0
                                        mul
                                        (this.Raise this.OverflowException)
                                        k)))
                id
        this.SignedCheckOverflow checkOverflow cilState
    member private this.Add_ovf_un (cilState : cilState) =
        let checkOverflowForUnsigned _ max x y cilState =
            let (>>=) = API.Arithmetics.(>>=)
            StatedConditionalExecutionCIL cilState
                (fun state k ->
                    PerformBinaryOperation OperationType.Subtract max x (fun diff ->
                    k (diff >>= y, state)))
                (fun cilState k -> PerformBinaryOperation OperationType.Add x y (fun res ->
                    cilState |> pushToOpStack res |> List.singleton |> k))
                (this.Raise this.OverflowException)
                id
        this.UnsignedCheckOverflow checkOverflowForUnsigned cilState
    member private this.Mul_ovf_un (cilState : cilState) =
        let checkOverflowForUnsigned zero max x y cilState =
            let (>>=) = API.Arithmetics.(>>=)
            let isZero state k = k ((x === zero) ||| (y === zero), state)
            StatedConditionalExecutionCIL cilState isZero
                (fun cilState k -> pushToOpStack zero cilState |> List.singleton |> k)
                (fun cilState k ->
                    StatedConditionalExecutionCIL cilState
                        (fun state k ->
                            PerformBinaryOperation OperationType.Divide max x (fun quotient ->
                            k (quotient >>= y, state)))
                        (fun cilState k ->
                            PerformBinaryOperation OperationType.Multiply x y (fun res ->
                                cilState |> pushToOpStack res |> List.singleton |> k))
                        (this.Raise this.OverflowException)
                        k)
                id
        this.UnsignedCheckOverflow checkOverflowForUnsigned cilState
    member private this.Sub_ovf_un (cilState : cilState) =
        let checkOverflowForUnsigned _ _ x y cilState =
            let (>>=) = API.Arithmetics.(>>=)
            StatedConditionalExecutionCIL cilState
                (fun state k -> k (x >>= y, state))
                (fun (cilState : cilState) k -> // no overflow
                    PerformBinaryOperation OperationType.Subtract x y (fun res ->
                    cilState |> pushToOpStack res |> List.singleton |> k))
                (this.Raise this.OverflowException)
                id
        this.UnsignedCheckOverflow checkOverflowForUnsigned cilState
    member private this.Sub_ovf (cilState : cilState) =
        // there is no way to reduce current operation to [x `Add_Ovf` (-y)]
        // min <= x - y <= max
        let checkOverflowForSigned min max zero minusOne x y cilState =
                let (>>=) = API.Arithmetics.(>>=)
                let xGreaterEqualZero state k = k (x >>= zero, state)
                let sub (cilState : cilState) k = // no overflow
                    PerformBinaryOperation OperationType.Subtract x y (fun res ->
                    cilState |> pushToOpStack res |> List.singleton |> k)
                StatedConditionalExecutionCIL cilState
                    xGreaterEqualZero
                    (fun cilState -> // x >= 0 => max - x >= 0 => no overflow for [-1 * (max - x)]
                        StatedConditionalExecutionCIL cilState
                            (fun state k ->
                                PerformBinaryOperation OperationType.Subtract max x (fun diff ->
                                PerformBinaryOperation OperationType.Multiply diff minusOne (fun minusDiff ->
                                k (y >>= minusDiff, state)))) // y >= -(max - x)
                            sub
                            (this.Raise this.OverflowException))
                    (fun cilState -> // x < 0 => no overflow for [min - x] # x < 0 => [min - x] != min => no overflow for (-1) * [min - x]
                        StatedConditionalExecutionCIL cilState
                           (fun state k ->
                                PerformBinaryOperation OperationType.Subtract min x (fun diff ->
                                PerformBinaryOperation OperationType.Multiply diff minusOne (fun minusDiff ->
                                k (minusDiff >>= y, state)))) // -(min - x) >= y
                            sub
                            (this.Raise this.OverflowException))
                    id
        this.SignedCheckOverflow checkOverflowForSigned cilState
    member private x.Newarr (cfg : cfg) offset (cilState : cilState) =
        let (>>=) = API.Arithmetics.(>>=)
        let elemType = resolveTermTypeFromMetadata cilState.state cfg (offset + OpCodes.Newarr.Size)
        match cilState.state.opStack with
        | numElements :: stack ->
            StatedConditionalExecutionCIL (withOpStack stack cilState)
                (fun state k -> k (numElements >>= TypeUtils.Int32.Zero, state))
                (fun cilState k ->
                    let ref, state = Memory.AllocateDefaultArray cilState.state [numElements] (ArrayType(elemType, Vector))
                    cilState |> withState state |> pushToOpStack ref |> List.singleton |> k)
                (this.Raise this.OverflowException)
                id
        | _ -> __corruptedStack__()

    member x.CreateInstance args = methodInterpreter.CreateInstance args

    member x.InvalidProgramException cilState = methodInterpreter.InvalidProgramException cilState
    member x.NullReferenceException cilState = methodInterpreter.NullReferenceException cilState
    member x.IndexOutOfRangeException cilState = methodInterpreter.IndexOutOfRangeException cilState
    member x.ArrayTypeMismatchException cilState = methodInterpreter.ArrayTypeMismatchException cilState
    member x.DivideByZeroException cilState = methodInterpreter.DivideByZeroException cilState
    member x.OverflowException (cilState : cilState) : cilState list = methodInterpreter.OverflowException cilState
    member x.ArithmeticException cilState = methodInterpreter.ArithmeticException cilState
    member x.TypeInitializerException qualifiedTypeName innerException cilState =
        methodInterpreter.TypeInitializerException qualifiedTypeName innerException cilState
    member x.InvalidCastException cilState = methodInterpreter.InvalidCastException cilState

    // -------------------------------- ExplorerBase operations -------------------------------------

    member x.ExecuteAllInstructionsForCFGEdges (cfg : cfg) (cilState : cilState) : (cilState list * cilState list * cilState list) =
        let ip = currentIp cilState
        assert(ip.CanBeExpanded())
        let startingOffset = ip.Offset()
        let endOffset =
            let lastOffset = Seq.last cfg.sortedOffsets
            let rec binarySearch l r =
                if l + 1 = r then l
                else
                    let mid = (l + r) / 2
                    if cfg.sortedOffsets.[mid] <= startingOffset then binarySearch mid r
                    else binarySearch l mid
            let index = binarySearch 0 (Seq.length cfg.sortedOffsets)
            if cfg.sortedOffsets.[index] = lastOffset then cfg.ilBytes.Length
            else cfg.sortedOffsets.[index + 1]

        let isIpOfCurrentBasicBlock (ip : ipEntry) =
            match ip.label with
            | Instruction i when ip.method = cfg.methodBase -> startingOffset <= i && i < endOffset
            | _ -> false
        x.ExecuteAllInstructionsWhile isIpOfCurrentBasicBlock cilState

    member x.ExecuteOnlyOneInstruction (cilState : cilState) : (cilState list * cilState list * cilState list)  =
        x.ExecuteAllInstructionsWhile (always false) cilState

    // returns finishedStates, incompleteStates, erroredStates
    member x.ExecuteAllInstructionsWhile (condition : ipEntry -> bool) (cilState : cilState) : (cilState list * cilState list * cilState list)  =
        let rec executeAllInstructions (finishedStates, incompleteStates, errors) cilState =
            let ip = currentIp cilState
            try
                let allStates : cilState list = x.ExecuteInstruction {cilState with iie = None}
                let newErrors, goodStates = allStates |> List.partition (fun (cilState : cilState) -> cilState.HasException)
                let errors = errors @ newErrors //TODO: check it

                match goodStates with
                | list when List.forall (currentIp >> condition) list ->
                    List.fold executeAllInstructions (finishedStates, incompleteStates, errors) list
                | list -> list @ finishedStates, incompleteStates, errors
            with
            | :? InsufficientInformationException as iie ->
                let iieCilState = { cilState with iie = Some iie} |> withLastIp ip
                finishedStates, iieCilState :: incompleteStates, errors
        executeAllInstructions ([],[],[]) cilState

    member x.IncrementLevelIfNeeded (cfg : cfg) (offset : offset) (cilState : cilState) : cilState =
        let isRecursiveVertex offset =
            if cfg.dfsOut.ContainsKey offset then
                let t1 = cfg.dfsOut.[offset]
                cfg.reverseGraph.[offset] |> Seq.exists (fun w -> cfg.dfsOut.[w] <= t1)
            else false
        if offset = 0 || isRecursiveVertex offset then
            incrementLevel cilState (instruction cfg.methodBase offset)
        else cilState

    member x.RenewOpStackBalance opCode (cfg : cfg) (offset : offset) (cilState : cilState) =
         // TODO: what occurs with opStack after exception?
        let calledMethod =
            match opCode with
            | Instruction.Call | Instruction.CallVirt | Instruction.Calli | Instruction.NewObj ->
                resolveMethodFromMetadata cfg (offset + opCode.Size) |> Some
            | _ -> None
        let oldMin, oldBalance = cilState.popsCount
        let newBalance = oldBalance + Instruction.calculateOpStackChange opCode calledMethod
        let newMinimum =  min newBalance oldMin
        {cilState with popsCount = (newMinimum, newBalance)}

    member x.ExecuteInstruction (cilState : cilState) =
        Logger.trace "ExecuteInstruction:\n%s" (dump cilState)
        match cilState.ip with
        | {label = Instruction offset; method = m} :: _ ->
            let cfg = CFG.findCfg m
            let opCode = Instruction.parseInstruction m offset
            let newIps = moveCurrentIp cilState |> List.map (fun cilState -> cilState.ip)
            let newSts = opcode2Function.[hashFunction opCode] cfg offset newIps cilState

            let renewInstructionsInfo cilState =
                let cilState = x.RenewOpStackBalance opCode cfg offset cilState
                x.IncrementLevelIfNeeded cfg offset cilState
            newSts |> List.map renewInstructionsInfo
        | {label = Exit} :: _ -> moveCurrentIp cilState
        | [] -> __unreachable__()
        | _ -> __notImplemented__()
