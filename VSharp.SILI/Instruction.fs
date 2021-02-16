namespace VSharp.Interpreter.IL

open System

open VSharp
open System.Reflection
open System.Reflection.Emit
open VSharp.Core

exception IncorrectCIL of string

type offset = int
type term = VSharp.Core.term
type state = VSharp.Core.state

type operationalStack = term list

type ip = VSharp.Core.ip
type level = VSharp.Core.level

type ipTransition =
    | FallThrough of offset
    | Return
    | UnconditionalBranch of offset
    | ConditionalBranch of offset list
    | ExceptionMechanism


module internal NumberCreator =
    let public extractInt32 (ilBytes : byte []) pos =
        System.BitConverter.ToInt32(ilBytes, pos)
    let public extractUnsignedInt32 (ilBytes : byte []) pos =
        System.BitConverter.ToUInt32(ilBytes, pos)
    let public extractUnsignedInt16 (ilBytes : byte []) pos =
        System.BitConverter.ToUInt16(ilBytes, pos)
    let public extractInt64 (ilBytes : byte []) pos =
        System.BitConverter.ToInt64(ilBytes, pos)
    let public extractInt8 (ilBytes : byte []) pos =
        ilBytes.[pos] |> sbyte |> int
    let public extractUnsignedInt8 (ilBytes : byte []) pos =
        ilBytes.[pos]
    let public extractFloat64 (ilBytes : byte []) pos =
        System.BitConverter.ToDouble(ilBytes, pos)
    let public extractFloat32 (ilBytes : byte []) pos =
        System.BitConverter.ToSingle(ilBytes, pos)

module internal Instruction =

    let opStackBalanceChange : int [] = Array.create 29 0
    do
        opStackBalanceChange.[int <| StackBehaviour.Pop0] <- 0
        opStackBalanceChange.[int <| StackBehaviour.Pop1] <- -1
        opStackBalanceChange.[int <| StackBehaviour.Pop1_pop1] <- -2
        opStackBalanceChange.[int <| StackBehaviour.Popi] <- -1
        opStackBalanceChange.[int <| StackBehaviour.Popi_pop1] <- -2
        opStackBalanceChange.[int <| StackBehaviour.Popi_popi] <- -2
        opStackBalanceChange.[int <| StackBehaviour.Popi_popi8] <- -2
        opStackBalanceChange.[int <| StackBehaviour.Popi_popi_popi] <- -3
        opStackBalanceChange.[int <| StackBehaviour.Popi_popr4] <- -2
        opStackBalanceChange.[int <| StackBehaviour.Popi_popr8] <- -2
        opStackBalanceChange.[int <| StackBehaviour.Popref] <- -1
        opStackBalanceChange.[int <| StackBehaviour.Popref_pop1] <- -2
        opStackBalanceChange.[int <| StackBehaviour.Popref_popi] <- -2
        opStackBalanceChange.[int <| StackBehaviour.Popref_popi_popi] <- -3
        opStackBalanceChange.[int <| StackBehaviour.Popref_popi_popi8] <- -3
        opStackBalanceChange.[int <| StackBehaviour.Popref_popi_popr4] <- -3
        opStackBalanceChange.[int <| StackBehaviour.Popref_popi_popr8] <- -3
        opStackBalanceChange.[int <| StackBehaviour.Popref_popi_popref] <- -3
        opStackBalanceChange.[int <| StackBehaviour.Push0] <- 0
        opStackBalanceChange.[int <| StackBehaviour.Push1] <- 1
        opStackBalanceChange.[int <| StackBehaviour.Push1_push1] <- 2
        opStackBalanceChange.[int <| StackBehaviour.Pushi] <- 1
        opStackBalanceChange.[int <| StackBehaviour.Pushi8] <- 1
        opStackBalanceChange.[int <| StackBehaviour.Pushr4] <- 1
        opStackBalanceChange.[int <| StackBehaviour.Pushr8] <- 1
        opStackBalanceChange.[int <| StackBehaviour.Pushref] <- 1
        opStackBalanceChange.[int <| StackBehaviour.Varpop] <- 0 // should not be called
        opStackBalanceChange.[int <| StackBehaviour.Varpush] <- 0 // should not be called
        opStackBalanceChange.[int <| StackBehaviour.Popref_popi_pop1] <- -3

    let private extractToken = NumberCreator.extractInt32

    let resolveFieldFromMetadata methodBase ilBytes = extractToken ilBytes >> Reflection.resolveField methodBase
    let resolveTypeFromMetadata methodBase ilBytes = extractToken ilBytes >> Reflection.resolveType methodBase
    let resolveMethodFromMetadata methodBase ilBytes = extractToken ilBytes >> Reflection.resolveMethod methodBase
    let resolveTokenFromMetadata methodBase ilBytes = extractToken ilBytes >> Reflection.resolveToken methodBase

    let private isSingleByteOpCodeValue = (<) 0
    let private isSingleByteOpCode = (<>) 0xFEuy

    let private equalSizeOpCodesCount = 0x100
    let private singleByteOpCodes = Array.create equalSizeOpCodesCount OpCodes.Nop;
    let private twoBytesOpCodes = Array.create equalSizeOpCodesCount OpCodes.Nop;

    let private fillOpCodes =
        let (&&&) = Microsoft.FSharp.Core.Operators.(&&&)
        let resolve (field : FieldInfo) =
            match field.GetValue() with
            | :? OpCode as opCode -> let value = int opCode.Value
                                     if isSingleByteOpCodeValue value then singleByteOpCodes.[value] <- opCode
                                     else twoBytesOpCodes.[value &&& 0xFF] <- opCode
            | _ -> ()

        typeof<OpCodes>.GetRuntimeFields() |> Seq.iter resolve

    let private operandType2operandSize = [| 4; 4; 4; 8; 4; 0; -1; 8; 4; 4; 4; 4; 4; 4; 2; 1; 1; 4; 1|]

    let private jumpTargetsForNext (opCode : OpCode) _ pos =
        let nextInstruction = pos + opCode.Size + operandType2operandSize.[int opCode.OperandType]
        FallThrough nextInstruction

    let private jumpTargetsForBranch (opCode : OpCode) ilBytes pos =
        let offset =
            match opCode.OperandType with
            | OperandType.InlineBrTarget -> NumberCreator.extractInt32 ilBytes (pos + opCode.Size)
            | _ -> NumberCreator.extractInt8 ilBytes (pos + opCode.Size)

        let nextInstruction = pos + opCode.Size + operandType2operandSize.[int opCode.OperandType]
        if offset = 0 && opCode <> OpCodes.Leave && opCode <> OpCodes.Leave_S
        then FallThrough nextInstruction
        else UnconditionalBranch <| offset + nextInstruction

    let private inlineBrTarget extract (opCode : OpCode) ilBytes pos =
        let offset = extract ilBytes (pos + opCode.Size)
        let nextInstruction = pos + opCode.Size + operandType2operandSize.[int opCode.OperandType]
        ConditionalBranch [nextInstruction; nextInstruction + offset]

    let private inlineSwitch (opCode : OpCode) ilBytes pos =
        let n = NumberCreator.extractUnsignedInt32 ilBytes (pos + opCode.Size) |> int
        let nextInstruction = pos + opCode.Size + 4 * n + 4
        let nextOffsets =
            List.init n (fun x -> nextInstruction + NumberCreator.extractInt32 ilBytes (pos + opCode.Size + 4 * (x + 1)))
        ConditionalBranch <| nextInstruction :: nextOffsets

    let private jumpTargetsForReturn _ _ _ = Return
    let private jumpTargetsForThrow _ _ _ = ExceptionMechanism

    let findNextInstructionOffsetAndEdges (opCode : OpCode) =
        match opCode.FlowControl with
        | FlowControl.Next
        | FlowControl.Call
        | FlowControl.Break
        | FlowControl.Meta -> jumpTargetsForNext
        | FlowControl.Branch -> jumpTargetsForBranch
        | FlowControl.Cond_Branch ->
            match opCode.OperandType with
            | OperandType.InlineBrTarget -> inlineBrTarget NumberCreator.extractInt32
            | OperandType.ShortInlineBrTarget -> inlineBrTarget NumberCreator.extractInt8
            | OperandType.InlineSwitch -> inlineSwitch
            | _ -> __notImplemented__()
        | FlowControl.Return -> jumpTargetsForReturn
        | FlowControl.Throw -> jumpTargetsForThrow
        | _ -> __notImplemented__()
        <| opCode

    let isLeaveOpCode (opCode : OpCode) = opCode = OpCodes.Leave || opCode = OpCodes.Leave_S

    let private isCallOpCode (opCode : OpCode) =
        opCode = OpCodes.Call
        || opCode = OpCodes.Calli
        || opCode = OpCodes.Callvirt
        || opCode = OpCodes.Tailcall
    let private isNewObjOpCode (opCode : OpCode) =
        opCode = OpCodes.Newobj
    let isDemandingCallOpCode (opCode : OpCode) =
        isCallOpCode opCode || isNewObjOpCode opCode
    let isFinallyClause (ehc : ExceptionHandlingClause) =
        ehc.Flags = ExceptionHandlingClauseOptions.Finally
    let shouldExecuteFinallyClause (src : offset) (dst : offset) (ehc : ExceptionHandlingClause) =
//        let srcOffset, dstOffset = src.Offset(), dst.Offset()
        let isInside offset = ehc.TryOffset <= offset && offset < ehc.TryOffset + ehc.TryLength
        isInside src && not <| isInside dst

    let internal (|Ret|_|) (opCode : OpCode) = if opCode = OpCodes.Ret then Some () else None
    let (|Call|_|) (opCode : OpCode) = if opCode = OpCodes.Call then Some () else None
    let (|CallVirt|_|) (opCode : OpCode) = if opCode = OpCodes.Callvirt then Some () else None
    let (|Calli|_|) (opCode : OpCode) = if opCode = OpCodes.Calli then Some () else None
    let (|TailCall|_|) (opCode : OpCode) = if opCode = OpCodes.Tailcall then Some () else None
    let (|NewObj|_|) (opCode : OpCode) = if opCode = OpCodes.Newobj then Some () else None


    let parseInstruction (m : MethodBase) pos =
        let ilBytes = m.GetMethodBody().GetILAsByteArray()
        let b1 = ilBytes.[pos]
        if isSingleByteOpCode b1 then singleByteOpCodes.[int b1]
        elif pos + 1 >= ilBytes.Length then raise (IncorrectCIL("Prefix instruction FE without suffix!"))
        else twoBytesOpCodes.[int ilBytes.[pos + 1]]

    let parseCallSite (m : MethodBase) pos =
        let opCode = parseInstruction m pos
        let ilBytes = m.GetMethodBody().GetILAsByteArray()
        let calledMethod = resolveMethodFromMetadata m ilBytes (pos + opCode.Size)
        {sourceMethod = m; calledMethod = calledMethod; opCode = opCode; offset = pos}

    let private resultAddition (m : MethodBase) = if Reflection.HasNonVoidResult m then 1 else 0

    let calculateOpStackChange (opCode : OpCode) (*m : MethodBase*) (calledMethod : MethodBase option) : int =
        match opCode, calledMethod with
        | Ret, None -> 0 // we remove result from current frame and add it to previous one
        | _, None -> opStackBalanceChange.[int <| opCode.StackBehaviourPop] + opStackBalanceChange.[int <| opCode.StackBehaviourPush]
        | NewObj, Some c -> 1 - c.GetParameters().Length
        | Call, Some c
        | Calli, Some c
        | CallVirt, Some c -> resultAddition c - (c.GetParameters().Length + if c.IsStatic then 0 else 1)
        | _ -> __unreachable__()
