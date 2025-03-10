namespace VSharp.Interpreter.IL

open System
open System.Collections.Generic
open System.Diagnostics
open System.Reflection
open System.Reflection.Emit
open FSharpx.Collections
open CilStateOperations
open VSharp
open VSharp.CSharpUtils
open VSharp.Core
open VSharp.Interpreter.IL
open IpOperations
open MethodBody

type cfg = CfgInfo

module TypeUtils =
    open Types

    let float64Type = typedefof<double>
    let float32Type = typedefof<float32>
    let int8Type = typedefof<int8>
    let int16Type = typedefof<int16>
    let int32Type = typedefof<int32>
    let int64Type = typedefof<int64>
    let uint8Type = typedefof<uint8>
    let uint16Type = typedefof<uint16>
    let uint32Type = typedefof<uint32>
    let uint64Type = typedefof<uint64>
    let charType = typedefof<char>
    let intPtr = typedefof<IntPtr>
    let uintPtr = typedefof<UIntPtr>

    let isIntegralTerm term = Terms.TypeOf term |> TypeUtils.isIntegral
    let isLong term = TypeOf term |> TypeUtils.isLongType
    let isBool term = Terms.TypeOf term |> IsBool

    module Char =
        let Zero() = MakeNumber Unchecked.defaultof<char>
    module Int8 =
        let Zero() = MakeNumber 0y
    module UInt8 =
        let Zero() = MakeNumber 0uy
    module Int16 =
        let Zero() = MakeNumber 0s
    module UInt16 =
        let Zero() = MakeNumber 0us
    module Int32 =
        let Zero() = MakeNumber 0
        let One() = MakeNumber 1
        let MinusOne() = MakeNumber -1
        let MinValue() = MakeNumber Int32.MinValue
        let MaxValue() = MakeNumber Int32.MaxValue
    module UInt32 =
        let Zero() = MakeNumber 0u
        let MaxValue() = MakeNumber UInt32.MaxValue
    module Int64 =
        let Zero() = MakeNumber 0L
        let MinusOne() = MakeNumber -1L
        let MinValue() = MakeNumber Int64.MinValue
        let MaxValue() = MakeNumber Int64.MaxValue
    module UInt64 =
        let Zero() = MakeNumber 0UL
        let MaxValue() = MakeNumber UInt64.MaxValue

module internal InstructionsSet =

    let idTransformation term k = k term

    // ------------------------------------ Metadata Interaction ------------------------------------

    let resolveFieldFromMetadata (m : Method) offset = m.ResolveFieldFromMetadata offset
    let resolveTypeFromMetadata (m : Method) offset = m.ResolveTypeFromMetadata offset
    let resolveMethodFromMetadata (m : Method) offset = m.ResolveMethodFromMetadata offset
    let resolveTokenFromMetadata (m : Method) offset = m.ResolveTokenFromMetadata offset

    // ------------------------------- CIL instructions -------------------------------

    let referenceLocalVariable index (method : Method) =
        let lvi = method.LocalVariables[index]
        let stackKey = LocalVariableKey(lvi, method)
        Ref (PrimitiveStackLocation stackKey)

    let getArgTerm index (method : Method) =
        let pi = method.Parameters[index]
        PrimitiveStackLocation (ParameterKey pi) |> Ref

    let castUnchecked typ term : term = Types.Cast term typ
    let ldc numberCreator t (m : Method) shiftedOffset (cilState : cilState) =
        let num = numberCreator m.ILBytes shiftedOffset
        push (Concrete num t) cilState

    let ldloc numberCreator (m : Method) shiftedOffset (cilState : cilState) =
        let index = numberCreator m.ILBytes shiftedOffset
        let reference = referenceLocalVariable index m
        let term = Memory.Read cilState.state reference
        push term cilState
    let ldarg numberCreator (m : Method) shiftedOffset (cilState : cilState) =
        let argumentIndex = numberCreator m.ILBytes shiftedOffset
        let arg =
            let state = cilState.state
            let this = if m.HasThis then Some <| Memory.ReadThis state m else None
            match this, m.HasThis with
            | None, _
            | Some _, false ->
                let term = getArgTerm argumentIndex m
                Memory.Read state term
            | Some this, _ when argumentIndex = 0 -> this
            | Some _, true ->
                let term = getArgTerm (argumentIndex - 1) m
                Memory.Read state term
        push arg cilState
    let ldarga numberCreator (m : Method) shiftedOffset (cilState : cilState) =
        let argumentIndex = numberCreator m.ILBytes shiftedOffset
        let address =
            let this = if m.IsStatic then None else Some <| Memory.ReadThis cilState.state m
            match this with
            | None -> getArgTerm argumentIndex m
            | Some _ when argumentIndex = 0 -> internalfail "can't load address of ``this''"
            | Some _ -> getArgTerm (argumentIndex - 1) m
        push address cilState

    let stloc numberCreator (m : Method) shiftedOffset (cilState : cilState) =
        let variableIndex = numberCreator m.ILBytes shiftedOffset
        let right = pop cilState
        let location = referenceLocalVariable variableIndex m
        let typ = TypeOfLocation location
        let value = Types.Cast right typ
        write cilState location value
    let private simplifyConditionResult state res k =
        if Contradicts state !!res then k (True())
        elif Contradicts state res then k (False())
        else k res
    let performCILUnaryOperation op (cilState : cilState) =
        let x = pop cilState
        API.PerformUnaryOperation op x (fun interimRes ->
        let res = if Terms.TypeOf x |> Types.IsBool then simplifyConditionResult cilState.state interimRes id else interimRes
        push res cilState)

    let performCILBinaryOperation op operand1Transform operand2Transform resultTransform (cilState : cilState) =
        let arg2, arg1 = pop2 cilState
        operand1Transform arg1 (fun arg1 ->
        operand2Transform arg2 (fun arg2 ->
        API.PerformBinaryOperation op arg1 arg2 (fun interimRes ->
        resultTransform interimRes (fun res ->
        push res cilState))))
    let standardPerformBinaryOperation op =
        performCILBinaryOperation op idTransformation idTransformation idTransformation
    let dup (cilState : cilState) =
        let x = pop cilState
        push x cilState
        push x cilState

    let isCallIp (ip : ip) =
        match ip with
        | Instruction(offset, m) ->
            let opCode = parseInstruction m offset
            isDemandingCallOpCode opCode
        | _ -> false

    let ret (m : Method) (cilState : cilState) =
        let resultTyp = m.ReturnType
        if resultTyp <> typeof<Void> then
            let res = pop cilState
            let castedResult = Types.Cast res resultTyp
            push castedResult cilState
        match cilState.ipStack with
        | _ :: ips -> cilState.ipStack <- (Exit m) :: ips
        | [] -> __unreachable__()

    let transform2BooleanTerm pc (term : term) =
        let check term =
            match TypeOf term with
            | _ when IsRefOrPtr term -> !!(IsNullReference term)
            | Types.Bool -> term
            | t when t = TypeUtils.charType -> term !== TypeUtils.Char.Zero()
            | t when t = TypeUtils.int8Type -> term !== TypeUtils.Int8.Zero()
            | t when t = TypeUtils.uint8Type -> term !== TypeUtils.UInt8.Zero()
            | t when t = TypeUtils.int16Type -> term !== TypeUtils.Int16.Zero()
            | t when t = TypeUtils.uint16Type -> term !== TypeUtils.UInt16.Zero()
            | t when t = TypeUtils.int32Type -> term !== TypeUtils.Int32.Zero()
            | t when t = TypeUtils.uint32Type -> term !== TypeUtils.UInt32.Zero()
            | t when t = TypeUtils.int64Type -> term !== TypeUtils.Int64.Zero()
            | t when t = TypeUtils.uint64Type -> term !== TypeUtils.UInt64.Zero()
            | t when t = TypeUtils.intPtr -> term !== MakeNumber IntPtr.Zero
            | t when t = TypeUtils.uintPtr -> term !== MakeNumber UIntPtr.Zero
            | t when t.IsEnum -> term !== MakeNumber (Activator.CreateInstance t)
            | _ -> __notImplemented__()
        GuardedApplyExpressionWithPC pc term check

    let binaryOperationWithBoolResult op operand1Transformation operand2Transformation (cilState : cilState) =
        performCILBinaryOperation op operand1Transformation operand2Transformation (simplifyConditionResult cilState.state) cilState

    let ceq (cilState : cilState) =
        let y, x = peek2 cilState
        let transform =
            if TypeUtils.isBool x || TypeUtils.isBool y
            then fun t k -> k (transform2BooleanTerm cilState.state.pc t)
            else idTransformation
        binaryOperationWithBoolResult OperationType.Equal transform transform cilState
    let starg numCreator (m : Method) offset (cilState : cilState) =
        let argumentIndex = numCreator m.ILBytes offset
        let argTerm =
           let this = if m.IsStatic then None else Some <| Memory.ReadThis cilState.state m
           match this with
           | None -> getArgTerm argumentIndex m
           | Some this when argumentIndex = 0 -> this
           | Some _ -> getArgTerm (argumentIndex - 1) m
        let value = pop cilState
        let states = Memory.Write cilState.state argTerm value
        states |> List.map (changeState cilState)
    let brcommon condTransform (m : Method) (offset : offset) (cilState : cilState) =
        let cond = pop cilState
        let oldIp = currentIp cilState
        let ipThen, ipElse =
           match conditionalBranchTarget m offset with
           | offsetThen, [offsetElse] -> moveInstruction offsetThen oldIp, moveInstruction offsetElse oldIp
           | _ -> __unreachable__()
        StatedConditionalExecutionCIL cilState
           (fun state k -> k (condTransform <| transform2BooleanTerm state.pc cond, state))
           (fun cilState k -> setCurrentIp ipThen cilState; k [cilState])
           (fun cilState k -> setCurrentIp ipElse cilState; k [cilState])
           id
    let brfalse = brcommon id
    let brtrue = brcommon (!!)
    let applyAndBranch additionalFunction brtrueFunction (m : Method) offset (cilState : cilState) =
        additionalFunction cilState
        brtrueFunction m offset cilState
    let boolToInt b =
        BranchExpressions (fun k -> k b) (fun k -> k <| TypeUtils.Int32.One()) (fun k -> k <| TypeUtils.Int32.Zero()) id
    let bitwiseOrBoolOperation bitwiseOp boolOp (cilState : cilState) =
        let arg2, arg1 = peek2 cilState
        let typ1, typ2 = TypeOf arg1, TypeOf arg2
        match typ1, typ2 with
        | Types.Bool, Types.Bool ->
            binaryOperationWithBoolResult boolOp idTransformation idTransformation cilState
        | _ when TypeUtils.isIntegral typ1 && TypeUtils.isIntegral typ2 ->
            standardPerformBinaryOperation bitwiseOp cilState
        // Bitwise operations for pointers are pointless (unless result will be checked on null), so returning pointer
        | _ when TypeUtils.isPointer typ1 ->
            pop cilState |> ignore
        | _ when TypeUtils.isPointer typ2 ->
            pop2 cilState |> ignore
            push arg2 cilState
        | Types.Bool, typ2 when TypeUtils.isIntegral typ2 ->
            let newArg1 = boolToInt arg1
            performCILBinaryOperation bitwiseOp (fun _ k -> k newArg1) idTransformation idTransformation cilState
        | typ1, Types.Bool when TypeUtils.isIntegral typ1 ->
            let newArg2 = boolToInt arg2
            performCILBinaryOperation bitwiseOp idTransformation (fun _ k -> k newArg2) idTransformation cilState
        | typ1, typ2 -> internalfail $"unhandled case for bitwise operation {bitwiseOp} and types: {typ1} {typ2}"
    let bitwiseOrBoolNot (cilState : cilState) =
        let arg = peek cilState
        let op =
            match TypeOf arg with
            | Types.Bool -> OperationType.LogicalNot
            | _ -> OperationType.BitwiseNot
        performCILUnaryOperation op cilState
    let retrieveActualParameters (method : Method) (cilState : cilState) =
        let paramsNumber = method.Parameters.Length
        let parameters, evaluationStack = EvaluationStack.PopMany paramsNumber cilState.state.evaluationStack
        let castParameter parameter (parInfo : ParameterInfo) =
            if method.IsDelegateConstructor && TypeUtils.isPointer parInfo.ParameterType then parameter
            else Types.Cast parameter parInfo.ParameterType
        setEvaluationStack evaluationStack cilState
        Seq.map2 castParameter (List.rev parameters) method.Parameters |> List.ofSeq

    let makeUnsignedInteger term k =
        match TypeOf term with
        | Types.Bool -> k <| Types.Cast term TypeUtils.uint32Type
        | t when t = typeof<double> || t = typeof<float> -> k term
        | t when TypeUtils.isIntegral t -> k <| Types.Cast term (TypeUtils.signedToUnsigned t) // no specs found about overflows
        | _ -> k term
    let performUnsignedIntegerOperation op (cilState : cilState) =
        let arg2, arg1 = peek2 cilState
        if TypeUtils.isIntegralTerm arg1 && TypeUtils.isIntegralTerm arg2 then
            performCILBinaryOperation op makeUnsignedInteger makeUnsignedInteger idTransformation cilState
        else internalfailf "arguments for %O are not Integers!" op
    let ldstr (m : Method) offset (cilState : cilState) =
        let stringToken = NumberCreator.extractInt32 m.ILBytes (offset + Offset.from OpCodes.Ldstr.Size)
        let string = m.Module.ResolveString stringToken
        let reference = Memory.AllocateString string cilState.state
        push reference cilState
    let allocateValueTypeInHeap v (cilState : cilState) =
        let address = Memory.BoxValueType cilState.state v
        push address cilState
    let ldnull (cilState : cilState) = push (NullRef typeof<obj>) cilState
    let convu (cilState : cilState) =
        let ptr = pop cilState |> MakeUIntPtr
        push ptr cilState
    let convi (cilState : cilState) =
        let ptr = pop cilState |> MakeIntPtr
        push ptr cilState
    let castTopOfOperationalStack targetType (cilState : cilState) =
        let t = pop cilState
        let termForStack = Types.Cast t targetType
        push termForStack cilState
    let ldloca numberCreator (m : Method) shiftedOffset (cilState : cilState) =
        let index = numberCreator m.ILBytes shiftedOffset
        let term = referenceLocalVariable index m
        push term cilState
    let switch (m : Method) offset (cilState : cilState) =
        let value = pop cilState
        let origPc = cilState.state.pc
        let value = makeUnsignedInteger value id
        let checkOneCase (guard, newIp) cilState kRestCases =
            StatedConditionalExecutionCIL cilState
                (fun state k -> k (guard, state))
                (fun cilState k -> setCurrentIp newIp cilState; k [cilState])
                (fun otherState k ->
                    otherState.state.pc <- origPc // ignore pc because we always know that cases do not overlap
                    kRestCases otherState k)
        let oldIp = currentIp cilState
        let fallThroughIp, restIps =
            match conditionalBranchTarget m offset with
            | fall, rests -> moveInstruction fall oldIp, List.map (fun x -> moveInstruction x oldIp) rests
        let casesAndOffsets = List.mapi (fun i offset -> value === MakeNumber i, offset) restIps
        let bound = makeUnsignedInteger (List.length restIps |> MakeNumber) id
        let fallThroughGuard = Arithmetics.GreaterOrEqualUn value bound
        Cps.List.foldrk checkOneCase cilState ((fallThroughGuard, fallThroughIp)::casesAndOffsets) (fun _ k -> k []) id
    let ldtoken (m : Method) offset (cilState : cilState) =
        let memberInfo = resolveTokenFromMetadata m (offset + Offset.from OpCodes.Ldtoken.Size)
        let state = cilState.state
        let res =
            match memberInfo with
            | :? FieldInfo as fi -> Memory.ObjectToTerm state fi.FieldHandle typeof<RuntimeFieldHandle>
            | :? Type as t -> Memory.ObjectToTerm state t.TypeHandle typeof<RuntimeTypeHandle>
            | :? MethodInfo as mi -> Memory.ObjectToTerm state mi.MethodHandle typeof<RuntimeMethodHandle>
            | _ -> internalfailf "Could not resolve token"
        push res cilState
    let ldftn (m : Method) offset (cilState : cilState) =
        let methodInfo = resolveMethodFromMetadata m (offset + Offset.from OpCodes.Ldftn.Size)
        let methodPtr = Terms.Concrete methodInfo (methodInfo.GetType())
        push methodPtr cilState
    let initobj (m : Method) offset (cilState : cilState) =
        let targetAddress = pop cilState
        let typ = resolveTypeFromMetadata m (offset + Offset.from OpCodes.Initobj.Size)
        let states = Memory.Write cilState.state targetAddress (Memory.DefaultOf typ)
        states |> List.map (changeState cilState)

    let clt = binaryOperationWithBoolResult OperationType.Less idTransformation idTransformation
    let cgt = binaryOperationWithBoolResult OperationType.Greater idTransformation idTransformation
    let cltun = binaryOperationWithBoolResult OperationType.Less_Un makeUnsignedInteger makeUnsignedInteger
    let bgeHelper (cilState : cilState) =
        let arg1, arg2 = peek2 cilState
        let typ1, typ2 = Terms.TypeOf arg1, Terms.TypeOf arg2
        if Types.isIntegral typ1 && Types.isIntegral typ2 then clt cilState
        elif Types.IsReal typ1 && Types.IsReal typ2 then cltun cilState
        else __notImplemented__()
    let isinst (m : Method) offset (cilState : cilState) =
        let object = pop cilState
        let typ = resolveTypeFromMetadata m (offset + Offset.from OpCodes.Isinst.Size)
        StatedConditionalExecutionCIL cilState
            (fun state k -> k (IsNullReference object, state))
            (fun cilState k -> push (NullRef typeof<obj>) cilState; k [cilState])
            (fun cilState k ->
                StatedConditionalExecutionCIL cilState
                    (fun state k -> k (Types.IsCast cilState.state object typ, state))
                    (fun cilState k -> push object cilState; k [cilState])
                    (fun cilState k -> push (NullRef typeof<obj>) cilState; k [cilState])
                    k)
            id
    let cgtun (cilState : cilState) =
        let arg2, arg1 = peek2 cilState
        if IsReference arg2 && IsReference arg1 then
            binaryOperationWithBoolResult OperationType.NotEqual idTransformation idTransformation cilState
        else binaryOperationWithBoolResult OperationType.Greater_Un makeUnsignedInteger makeUnsignedInteger cilState
    let sizeofInstruction (m : Method) offset (cilState : cilState) =
        let typ = resolveTypeFromMetadata m (offset + Offset.from OpCodes.Sizeof.Size)
        let size = Types.SizeOf typ
        push (MakeNumber size) cilState
    let endfilter (cilState : cilState) =
        let value, newStack = EvaluationStack.Pop cilState.state.evaluationStack
        setEvaluationStack newStack cilState
        popExceptionRegister cilState
        cilState.filterResult <- Some value
    let endfinally _ =
        // Should be handled in makeStep function
        __unreachable__()
    let br (m : Method) offset (cilState : cilState) =
        let oldIp = currentIp cilState
        let newIp = moveInstruction (unconditionalBranchTarget m offset) oldIp
        setCurrentIp newIp cilState

    let rec private constrainedImpl this method args cilState =
        let state = cilState.state
        let thisType = TypeOfLocation this
        let isValueType = Types.IsValueType thisType
        let implements = lazy(Reflection.typeImplementsMethod thisType method)
        match this.term with
        | Ref _ when isValueType && implements.Value ->
            push this cilState
            pushMany args cilState
        | Ref _ when isValueType ->
            let thisStruct = read cilState this
            let heapRef = Memory.BoxValueType state thisStruct
            push heapRef cilState
            pushMany args cilState
        | Ref _ ->
            let this = read cilState this
            push this cilState
            pushMany args cilState
        | Ptr(pointerBase, sightType, offset) ->
            match TryPtrToRef state pointerBase sightType offset with
            | Some(PrimitiveStackLocation _ as address) ->
                let this = Ref address
                constrainedImpl this method args cilState
            | _ ->
                // Inconsistent pointer, call will fork and filter this state
                push this cilState
                pushMany args cilState
        | _ -> internalfail $"Calling 'callvirt' with '.constrained': unexpected 'this' {this}"

    // '.constrained' is prefix, which is used before 'callvirt' or 'call' instruction
    // used before 'call' instruction, only if member is static and declared in interface
    let constrained (m : Method) offset (cilState : cilState) =
        let typ = resolveTypeFromMetadata m (offset + Offset.from OpCodes.Constrained.Size)
        let method =
            match findNextInstructionOffsetAndEdges OpCodes.Constrained m.ILBytes offset with
            | FallThrough offset ->
                let method = resolveMethodFromMetadata m (offset + Offset.from OpCodes.Callvirt.Size)
                // Method can not be constructor, because it's called via 'callvirt'
                assert(method :? MethodInfo)
                method :?> MethodInfo
            | _ -> __unreachable__()
        // IL specification is silent about this case, but 'method' may be static
        if method.IsStatic then
            // In this case, next called static method will be called via type 'typ'
            assert(List.isEmpty cilState.prefixContext)
            pushPrefixContext cilState (Constrained typ)
        else
            let n = method.GetParameters().Length
            let state = cilState.state
            let args, evaluationStack = EvaluationStack.PopMany n state.evaluationStack
            setEvaluationStack evaluationStack cilState
            let thisForCallVirt = pop cilState
            constrainedImpl thisForCallVirt method args cilState

    let localloc (cilState : cilState) =
        let size = pop cilState
        let ref = Memory.AllocateVectorArray cilState.state size typeof<byte>
        match ref.term with
        | HeapRef({term = ConcreteHeapAddress concreteAddress} as address, t) ->
            assert(TypeUtils.isArrayType t)
            addStackArray cilState concreteAddress
            let arrayType = Types.SymbolicTypeToArrayType t
            let ref = Ref (ArrayIndex(address, [MakeNumber 0], arrayType))
            push ref cilState
        | _ -> internalfail $"localloc: unexpected array reference {ref}"

    let private fallThroughImpl stackSizeBefore newIp cilState =
        // if not constructing runtime exception
        if not <| isUnhandledExceptionOrError cilState && Memory.CallStackSize cilState.state = stackSizeBefore then
            setCurrentIp newIp cilState

    let fallThrough (m : Method) offset cilState op =
        assert(not <| isUnhandledExceptionOrError cilState)
        let stackSizeBefore = Memory.CallStackSize cilState.state
        let oldIp = currentIp cilState
        let newIp = moveInstruction (fallThroughTarget m offset) oldIp
        op m offset cilState
        fallThroughImpl stackSizeBefore newIp cilState
        [cilState]

    let forkThrough (m : Method) offset cilState op =
        assert(not <| isUnhandledExceptionOrError cilState)
        let stackSizeBefore = Memory.CallStackSize cilState.state
        let oldIp = currentIp cilState
        let newIp = moveInstruction (fallThroughTarget m offset) oldIp
        let cilStates = op m offset cilState
        List.iter (fallThroughImpl stackSizeBefore newIp) cilStates
        cilStates

    let readParameter (parameter : ParameterInfo) cilState =
        if parameter.ParameterType.IsByRef then
            let key = ParameterKey parameter
            let stackRef = Memory.ReadLocalVariable cilState.state key
            read cilState stackRef
        else
            Memory.ReadArgument cilState.state parameter

open InstructionsSet

type UnknownMethodException(message : string, methodInfo : Method, interpreterStackTrace : string) =
    inherit Exception(message)
    member x.Method with get() = methodInfo
    member x.InterpreterStackTrace with get() = interpreterStackTrace

// Interface for internal calls interaction
type IInterpreter =
    abstract Raise : (cilState -> unit) -> cilState -> (cilState list -> 'a) -> 'a
    abstract NpeOrInvoke : cilState -> term -> (cilState -> (cilState list -> 'a) -> 'a) -> (cilState list -> 'a) -> 'a
    abstract InvalidProgramException : cilState -> unit
    abstract NullReferenceException : cilState -> unit
    abstract ArgumentException : cilState -> unit
    abstract ArgumentNullException : cilState -> unit
    abstract ArgumentOutOfRangeException : cilState -> unit
    abstract IndexOutOfRangeException : cilState -> unit
    abstract ArrayTypeMismatchException : cilState -> unit
    abstract RankException : cilState -> unit
    abstract DivideByZeroException : cilState -> unit
    abstract OverflowException : cilState -> unit
    abstract ArithmeticException : cilState -> unit
    abstract TypeInitializerException : string -> term -> cilState -> unit
    abstract InvalidCastException : cilState -> unit
    abstract OutOfMemoryException : cilState -> unit
    abstract AccessArrayDimension : (term -> term -> cilState -> (cilState list -> cilState list) -> cilState list) -> cilState -> term -> term -> cilState list
    abstract AccessArray : (cilState -> (cilState list -> 'a) -> 'a) -> cilState -> term -> term -> (cilState list -> 'a) -> 'a

type ILInterpreter() as this =

    // ------------------------------- Environment interaction -------------------------------

    member x.InternalCall (originMethod : Method) (methodInfo : MethodInfo) (argsAndThis : term list) cilState k =
        let neededParams = methodInfo.GetParameters() |> Array.map (fun p -> p.ParameterType)
        let parameters : obj[] =
            match neededParams with
            | [| t1; t2; t3 |] when t1 = typeof<IInterpreter> && t2 = typeof<cilState> && t3 = typeof<term list> ->
                [| x :> IInterpreter; cilState; argsAndThis |]
            | [| t1; t2 |] when t1 = typeof<state> && t2 = typeof<term list> ->
                [| cilState.state; argsAndThis |]
            | _ -> internalfail $"InternalCall: unsupported signature of internal call {neededParams}"

        let result =
            try
                methodInfo.Invoke(null, parameters)
            with
            | :? TargetInvocationException as targetException ->
                Logger.error $"InternalCall got TargetInvocationException {targetException.Message}"
                let actualException = targetException.GetBaseException()
                Logger.error $"TargetInvocationException.GetBaseException {actualException.Message}"
                raise actualException
            | e ->
                Logger.error $"InternalCall got exception {e.Message}"
                reraise()

        match result with
        | :? term as result when not originMethod.HasNonVoidResult ->
            assert(result = Nop())
            k [cilState]
        | :? term as result when originMethod.HasNonVoidResult ->
            assert(result <> Nop())
            push result cilState
            k [cilState]
        | :? ((term * state) list) as results when originMethod.HasNonVoidResult ->
            results |> List.map (fun (t, s) -> let s' = changeState cilState s in push t s'; s') |> k
        | :? ((term * state) list) as results ->
            results |> List.map (fun (_, s) -> changeState cilState s) |> k
        | :? (cilState list) as results ->
            k results
        | _ -> internalfail "Internal call should return 'term' or tuple 'term * state' or 'cilState list'!"

    member x.ConfigureErrorReporter errorReporter fatalErrorReporter =
        configureErrorReporter errorReporter fatalErrorReporter

    member x.Raise createException (cilState : cilState) k =
        createException cilState
        k [cilState]

    member private x.AccessMultidimensionalArray accessor (cilState : cilState) lengths indices (k : cilState list -> 'a) =
        let checkArrayBounds lengths indices =
            let checkOneBound acc (length, index) =
                let lowerBound = Concrete 0 Types.TLength
                let notTooSmall = Arithmetics.(>>=) index lowerBound
                let notTooLarge = Arithmetics.(<<) index length
                acc &&& notTooSmall &&& notTooLarge
            assert(List.length lengths = List.length indices)
            let upperBoundsAndIndices = List.zip lengths indices
            List.fold checkOneBound (True()) upperBoundsAndIndices
        StatedConditionalExecutionCIL cilState
            (fun state k -> k (checkArrayBounds lengths indices, state))
            accessor
            (x.Raise x.IndexOutOfRangeException)
            k

    member private x.AccessArray accessor (cilState : cilState) length index k =
        x.AccessMultidimensionalArray accessor cilState [length] [index] k

    member private x.AccessArrayDimension accessor (cilState : cilState) (this : term) (dimension : term) =
        let upperBound = Memory.ArrayRank cilState.state this
        x.AccessArray (accessor this dimension) cilState upperBound dimension id

    member x.NpeOrInvokeStatementCIL (cilState : cilState) (this : term) statement (k : cilState list -> 'a) =
        let additionalCheck cilState k =
            StatedConditionalExecutionCIL cilState
                (fun state k -> k (!!(IsBadRef this), state))
                statement
                (fun cilState k ->
                    ErrorReporter.ReportFatalError cilState "access violation"
                    k [])
                k
        StatedConditionalExecutionCIL cilState
            (fun state k -> k (!!(IsNullReference this), state))
            additionalCheck
            (x.Raise x.NullReferenceException)
            k

    member private x.ShouldMock (method : Method) =
        method.IsShimmed && ExternMocker.ShimSupported || method.IsExternalMethod && not method.IsQCall

    member private x.InstantiateThisIfNeed state thisOption (method : Method) =
        match thisOption with
        | Some this ->
            let thisType = TypeOfLocation this
            if Types.IsValueType thisType && (method :> IMethod).IsConstructor then
                let newThis = Memory.DefaultOf thisType
                let states = Memory.Write state this newThis
                assert(List.length states = 1 && LanguagePrimitives.PhysicalEquality state (List.head states))
        | None -> ()

    member private x.IsArrayGetOrSet (method : Method) =
        let name = method.Name
        (name = "Set" || name = "Get") && typeof<System.Array>.IsAssignableFrom(method.DeclaringType)

    static member InitFunctionFrameCIL (cilState : cilState) (method : Method) this paramValues =
        Memory.InitFunctionFrame cilState.state method this (paramValues |> Option.bind (List.map Some >> Some))
        pushToIp (instruction method 0<offsets>) cilState

    static member CheckDisallowNullAttribute (method : Method) (argumentsOpt : term list option) (cilState : cilState) shouldReportError k =
        if not <| method.CheckAttributes then
            [cilState] |> k
        else
            let assumptions =
                match argumentsOpt with
                | Some arguments ->
                    let parameters = method.Parameters
                    let getDisallowNullAssumption index argument =
                        if Attribute.IsDefined(parameters[index], typeof<CodeAnalysis.DisallowNullAttribute>)
                            then Some <| !!(IsNullReference argument)
                            else None
                    arguments |> Seq.mapi getDisallowNullAssumption |> Seq.choose id
                | None ->
                    let getDisallowNullAssumption (parameter : ParameterInfo) =
                        if Attribute.IsDefined(parameter, typeof<CodeAnalysis.DisallowNullAttribute>)
                            then Some <| !!(IsNullReference (readParameter parameter cilState))
                            else None
                    method.Parameters |> Seq.map getDisallowNullAssumption |> Seq.choose id

            if Seq.isEmpty assumptions then
                [cilState] |> k
            else
                let assumptions = conjunction assumptions
                let message = "DisallowNull attribute violation"
                StatedConditionalExecutionCIL cilState
                    (fun state k -> k (assumptions, state))
                    (fun cilState k -> k [cilState])
                    (fun cilState k ->
                        if shouldReportError then ErrorReporter.ReportError cilState message
                        k [])
                    k

    static member CheckNotNullAttribute (method : Method) (cilState : cilState) shouldReportError k =
        if not <| method.CheckAttributes then
            [cilState] |> k
        else
            let retValueAssumption =
                match method.ReturnParameter with
                | Some returnParameter when Attribute.IsDefined(returnParameter, typeof<CodeAnalysis.NotNullAttribute>) ->
                    let res = pop cilState
                    push res cilState
                    Some <| !!(IsNullReference res)
                | _ -> None

            let getNotNullAssumption (parameter : ParameterInfo) =
                if Attribute.IsDefined(parameter, typeof<CodeAnalysis.NotNullAttribute>)
                    then Some <| !!(IsNullReference (readParameter parameter cilState))
                    else None
            let assumptions = method.Parameters |> Seq.map getNotNullAssumption |> Seq.cons retValueAssumption |> Seq.choose id

            if Seq.isEmpty assumptions then
                [cilState] |> k
            else
                let assumptions = conjunction assumptions
                let message = "NotNull attribute violation"
                StatedConditionalExecutionCIL cilState
                    (fun state k -> k (assumptions, state))
                    (fun cilState k -> k [cilState])
                    (fun cilState k ->
                        if shouldReportError then ErrorReporter.ReportError cilState message
                        k [])
                    k

    member private x.InitStaticFieldWithDefaultValue state (f : FieldInfo) =
        assert f.IsStatic
        let fieldType = f.FieldType
        let declaringType = f.DeclaringType
        let value =
            if f.IsLiteral then
                match f.GetValue(null) with // argument means class with field f, so we have null, because f is a static field
                | null -> NullRef fieldType
                | :? string as str -> Memory.AllocateString str state
                | v when f.FieldType.IsPrimitive || f.FieldType.IsEnum -> Concrete v fieldType
                | _ -> __unreachable__()
            elif TypeUtils.isImplementationDetails declaringType then
                Memory.AllocateArrayFromFieldInfo state f
            else Memory.DefaultOf fieldType
        let fieldId = Reflection.wrapField f
        Memory.WriteStaticField state declaringType fieldId value

    member private x.InvokeArrayGetOrSet (cilState : cilState) (method : Method) thisOption args =
        let name = method.Name
        match thisOption with
        | Some arrayRef when name = "Get" ->
            let typ = Some method.ReturnType
            x.LdElemCommon typ cilState arrayRef args
        | Some arrayRef when name = "Set" ->
            let value, indices = List.lastAndRest args
            let typ = TypeOf value |> Some
            x.StElemCommon typ cilState arrayRef indices value
        | _ -> __unreachable__()

    // NOTE: When executing ldsfld, call and so on, we should previously initialize statics.
    // NOTE: Continuation 'whenInitializedCont' contains exploration of current instruction 'I' on ipStack.
    // NOTE: If statics was already initialized or we have no static constructor,
    //       then we can continue to explore instructions in continuation 'whenInitializedCont'.
    // NOTE: Otherwise, we need to add static constructor to ipStack (so queue will explore it instruction by instruction)
    //       without calling continuation 'whenInitializedCont'.
    // NOTE: After exploration of static constructor, queue will contain the same instruction 'I',
    //       that caused statics initialization, so queue will try again to explore this instruction,
    //       but at that moment statics will be already initialized

    member x.InitializeStatics (cilState : cilState) (t : Type) whenInitializedCont =
        match t with
        | _ when t.IsGenericParameter -> whenInitializedCont cilState
        | _ ->
            let typeInitialized = Memory.IsTypeInitialized cilState.state t
            match typeInitialized with
            | True -> whenInitializedCont cilState
            | _ ->
                let fields = t.GetFields(Reflection.staticBindingFlags)
                let staticConstructor = t.GetConstructors(Reflection.staticBindingFlags) |> Array.tryHead
                Seq.iter (x.InitStaticFieldWithDefaultValue cilState.state) fields
                Memory.InitializeStaticMembers cilState.state t
                match staticConstructor with
                | Some cctor ->
                    let cctor = Application.getMethod cctor
                    x.CommonCall cctor [] None cilState id
                | None -> whenInitializedCont cilState
                // TODO: make assumption ``Memory.withPathCondition state (!!typeInitialized)''

    member private x.ConcreteInvokeCatch (e : Exception) cilState isRuntime =
        let state = cilState.state
        let error = Memory.AllocateConcreteObject state e (e.GetType())
        x.CommonThrow cilState error isRuntime

    member private x.TryConcreteInvoke (method : Method) (args : term list) thisOption (cilState : cilState) =
        let state = cilState.state
        if method.CanCallConcrete then
            // Before term args, type args are located
            let termArgs = List.skip (List.length args - method.Parameters.Length) args
            let objArgs = List.choose (TryTermToObj state) termArgs
            let hasThis = Option.isSome thisOption
            let thisObj = Option.bind (TryTermToObj state) thisOption
            match thisObj with
            | _ when List.length objArgs <> List.length termArgs -> false
            | None when hasThis -> false
            | _ ->
                try
                    let result = method.Invoke thisObj (List.toArray objArgs)
                    let resultType = TypeUtils.getTypeOfConcrete result
                    let returnType = method.ReturnType
                    match resultType with
                    | _ when resultType <> null && resultType.IsValueType && returnType.IsInterface ->
                        // When return type is interface, but real type is struct,
                        // it should be boxed, so allocating it in heap
                        let resultTerm = Memory.AllocateConcreteObject cilState.state result resultType
                        push resultTerm cilState
                    | _ when returnType <> typeof<Void> ->
                        // Case when method returns something
                        let typ = TypeUtils.mostConcreteType resultType method.ReturnType
                        let resultTerm = Memory.ObjectToTerm cilState.state result typ
                        push resultTerm cilState
                    | _ -> ()
                with :? TargetInvocationException as e ->
                    let isRuntime = method.IsRuntimeException
                    x.ConcreteInvokeCatch e.InnerException cilState isRuntime
                true
        else false

    member private x.InlineOrCall (method : Method) (args : term list) thisOption (cilState : cilState) k =
        let _, genericArgs, _ = method.Generalize()
        let wrapType arg = Concrete arg typeof<Type>
        // TODO: do not wrap types, pass them through state.typeVariables!
        let typeArgs = genericArgs |> Seq.map wrapType |> List.ofSeq
        let typeAndMethodArgs = typeArgs @ args
        x.InstantiateThisIfNeed cilState.state thisOption method

        let fallThroughCall (cilState : cilState) =
            if isUnhandledExceptionOrError cilState |> not then
                ILInterpreter.FallThroughCall cilState
            cilState

        if x.TryConcreteInvoke method typeAndMethodArgs thisOption cilState then
            fallThroughCall cilState |> List.singleton |> k
        elif method.IsFSharpInternalCall then
            let thisAndArguments = optCons typeAndMethodArgs thisOption
            let internalCall = method.GetInternalCall
            x.InternalCall method internalCall thisAndArguments cilState (List.map fallThroughCall >> k)
        elif method.IsCSharpInternalCall then
            assert method.HasBody
            ILInterpreter.InitFunctionFrameCIL cilState method thisOption (Some args)
            [cilState] |> k
        // TODO: add Address function for array and return Ptr #do
        elif x.IsArrayGetOrSet method then
            x.InvokeArrayGetOrSet cilState method thisOption typeAndMethodArgs |> List.map fallThroughCall |> k
        elif ExternMocker.ExtMocksSupported && x.ShouldMock method then
            let mockMethod = ExternMockAndCall cilState.state method None []
            match mockMethod with
            | Some symVal ->
                push symVal cilState
            | None -> ()
            fallThroughCall cilState |> List.singleton |> k
        elif method.IsExternalMethod then
            let stackTrace = Memory.StackTraceString cilState.state.stack
            let message = "Not supported extern method"
            UnknownMethodException(message, method, stackTrace) |> raise
        elif method.IsInternalCall then
            assert(not <| method.IsImplementedInternalCall)
            let stackTrace = Memory.StackTraceString cilState.state.stack
            let message = "Not supported internal call"
            UnknownMethodException(message, method, stackTrace) |> raise
        elif method.IsNotImplementedIntrinsic then
            let stackTrace = Memory.StackTraceString cilState.state.stack
            let message = "Not supported intrinsic method"
            UnknownMethodException(message, method, stackTrace) |> raise
        elif method.HasBody then
            ILInterpreter.InitFunctionFrameCIL cilState method thisOption (Some args)
            [cilState] |> k
        else internalfailf $"Non-extern method {method.FullName} without body!"

    member private x.CommonCall (method : Method) args thisOption (cilState : cilState) k =
        let inlineOrCall state k =
            x.InlineOrCall method args thisOption state k
        ILInterpreter.CheckDisallowNullAttribute method (Some args) cilState true (fun states ->
        Cps.List.mapk inlineOrCall states (List.concat >> k))

    member x.CallAbstract targetType (ancestorMethod : MethodWithBody) (this : term) (arguments : term list) cilState k =
        let thisType = MostConcreteTypeOfRef cilState.state this
        let candidateTypes = ResolveCallVirt cilState.state this thisType ancestorMethod |> List.ofSeq
        let invokeMock cilState k =
            let mockMethod =
                if ancestorMethod.DeclaringType.IsInterface then
                    ancestorMethod
                else
                    ancestorMethod.ResolveOverrideInType targetType
            let returnValue = MethodMockAndCall cilState.state mockMethod (Some this) []
            match returnValue with
            | Some symVal ->
                push symVal cilState
            | None -> ()
            match tryCurrentLoc cilState with
            | Some loc ->
                // Moving ip to next instruction after mocking method result
                fallThrough loc.method loc.offset cilState (fun _ _ _ -> ()) |> k
            | _ -> __unreachable__()
        let rec dispatch (candidates : symbolicType list) cilState k =
            match candidates with
            | [MockType _] ->
                KeepOnlyMock cilState.state this
                invokeMock cilState k
            | ConcreteType candidateType :: rest ->
                let overridden =
                    ancestorMethod.ResolveOverrideInType candidateType :?> Method
                if overridden.InCoverageZone || candidateType.IsAssignableTo targetType && targetType.Assembly = candidateType.Assembly then
                    StatedConditionalExecutionCIL cilState
                        (fun cilState k -> k (API.Types.TypeIsRef cilState candidateType this, cilState))
                        (fun cilState k ->
                            let this = Types.Cast this overridden.ReflectedType
                            x.CommonCall overridden arguments (Some this) cilState k)
                        (dispatch rest)
                        k
                else
                    dispatch rest cilState k
            | MockType _ :: _ ->
                __unreachable__()
            | [] ->
                __insufficientInformation__ $"Trying to 'CallVirt' method {ancestorMethod} without mocks"
        dispatch candidateTypes cilState k

    member private x.ConvOvf targetType (cilState : cilState) =
        let supersetsOf =
            PersistentDict.ofSeq [
                TypeUtils.int8Type,    [|TypeUtils.int8Type; TypeUtils.int16Type; TypeUtils.int32Type; TypeUtils.int64Type|]
                TypeUtils.int16Type,   [|TypeUtils.int16Type; TypeUtils.int32Type; TypeUtils.int64Type|]
                TypeUtils.int32Type,   [|TypeUtils.int32Type; TypeUtils.int64Type|]
                TypeUtils.int64Type,   [|TypeUtils.int64Type|]
                TypeUtils.uint8Type,   [|TypeUtils.uint8Type; TypeUtils.uint16Type; TypeUtils.uint32Type; TypeUtils.uint64Type|]
                TypeUtils.uint16Type,  [|TypeUtils.uint16Type; TypeUtils.uint32Type; TypeUtils.uint64Type|]
                TypeUtils.uint32Type,  [|TypeUtils.uint32Type; TypeUtils.uint64Type|]
                TypeUtils.uint64Type,  [|TypeUtils.uint64Type|]
                TypeUtils.float32Type, [|TypeUtils.float32Type; TypeUtils.float64Type|]
                TypeUtils.float64Type, [|TypeUtils.float64Type|] ]
        let isSubset leftTyp rightTyp = Array.contains rightTyp supersetsOf[leftTyp]
        let minMaxOf =
            PersistentDict.ofSeq [
                TypeUtils.int8Type,    (SByte.MinValue  :> IConvertible, SByte.MaxValue  :> IConvertible)
                TypeUtils.int16Type,   (Int16.MinValue  :> IConvertible, Int16.MaxValue  :> IConvertible)
                TypeUtils.int32Type,   (Int32.MinValue  :> IConvertible, Int32.MaxValue  :> IConvertible)
                TypeUtils.int64Type,   (Int64.MinValue  :> IConvertible, Int64.MaxValue  :> IConvertible)
                TypeUtils.uint8Type,   (Byte.MinValue   :> IConvertible, Byte.MaxValue   :> IConvertible)
                TypeUtils.uint16Type,  (UInt16.MinValue :> IConvertible, UInt16.MaxValue :> IConvertible)
                TypeUtils.uint32Type,  (UInt32.MinValue :> IConvertible, UInt32.MaxValue :> IConvertible)
                TypeUtils.uint64Type,  (UInt64.MinValue :> IConvertible, UInt64.MaxValue :> IConvertible)
                TypeUtils.float32Type, (Single.MinValue :> IConvertible, Single.MaxValue :> IConvertible)
                TypeUtils.float64Type, (Double.MinValue :> IConvertible, Double.MaxValue :> IConvertible) ]
        let getSegment leftTyp rightTyp =
            let min1, max1 = minMaxOf[leftTyp]
            let min2, max2 = minMaxOf[rightTyp]
            let c = System.Globalization.CultureInfo.CurrentCulture
            match min1.ToDouble(c) < min2.ToDouble(c), max1.ToDouble(c) < max2.ToDouble(c) with
            | true, true   -> min2, max1
            | true, false  -> min2, max2
            | false, true  -> min1, max1
            | false, false -> min1, max2
        let canCastWithoutOverflow term targetType =
            let (<<=) = API.Arithmetics.(<<=)
            assert(Terms.TypeOf term |> Types.IsNumeric)
            let t = Terms.TypeOf term
            if isSubset t targetType then True()
            elif t = TypeUtils.int64Type && targetType = TypeUtils.uint64Type then
                let int64Zero = MakeNumber (0 |> int64)
                int64Zero <<= term
            elif t = TypeUtils.uint64Type && targetType = TypeUtils.int64Type then
                let uint64RightBorder = MakeNumber (Int64.MaxValue |> uint64)
                term <<= uint64RightBorder
            else
                let min, max = getSegment t targetType
                let leftBorder  = Concrete min t // must save type info, because min is int64
                let rightBorder = Concrete max t // must save type info, because max is int64
                (leftBorder <<= term) &&& (term <<= rightBorder)
        let t = pop cilState
        StatedConditionalExecutionCIL cilState
            (fun state k -> k (canCastWithoutOverflow t targetType, state))
            (fun cilState k ->
                let castedResult = Types.Cast t targetType
                push castedResult cilState
                k [cilState])
            (x.Raise x.OverflowException)
            id

    member private x.ConvOvfUn unsignedSightType targetType (cilState : cilState) =
        let t = pop cilState
        let unsignedT = Types.Cast t unsignedSightType
        push unsignedT cilState
        x.ConvOvf targetType cilState

    member private x.CommonCastClass (cilState : cilState) (term : term) (typ : Type) k =
        StatedConditionalExecutionCIL cilState
            (fun state k -> k (IsNullReference term ||| Types.IsCast state term typ, state))
            (fun cilState k ->
                push (Types.Cast term typ) cilState
                k [cilState])
            (x.Raise x.InvalidCastException)
            k
    member private x.CastClass (m : Method) offset (cilState : cilState) : cilState list =
        let term = pop cilState
        let typ = resolveTypeFromMetadata m (offset + Offset.from OpCodes.Castclass.Size)
        x.CommonCastClass cilState term typ id

    member private x.PushNewObjResultOnEvaluationStack (cilState : cilState) reference (calledMethod : MethodBase) =
        let valueOnStack =
            if calledMethod.DeclaringType.IsValueType then read cilState reference
            else reference
        push valueOnStack cilState

    member x.RetrieveCalledMethodAndArgs (opCode : OpCode) (calledMethod : Method) (cilState : cilState) =
        let args = retrieveActualParameters calledMethod cilState
        let hasThis = calledMethod.HasThis && opCode <> OpCodes.Newobj
        let this = if hasThis then pop cilState |> Some else None
        this, args

    member x.Call (m : Method) offset (cilState : cilState) =
        let prefixContext = popPrefixContext cilState
        let calledMethodBase = resolveMethodFromMetadata m (offset + Offset.from OpCodes.Call.Size)
        let calledMethod =
            match prefixContext with
            | Some (Constrained t) ->
                assert(calledMethodBase :? MethodInfo)
                let methodInfo = calledMethodBase :?> MethodInfo
                let m = Reflection.resolveOverridingMethod t methodInfo
                Application.getMethod m
            | None -> Application.getMethod calledMethodBase
        let getArgsAndCall cilState =
            let thisOpt, args = x.RetrieveCalledMethodAndArgs OpCodes.Call calledMethod cilState
            match thisOpt with
            | Some this -> x.NpeOrInvokeStatementCIL cilState this (x.CommonCall calledMethod args thisOpt) id
            | None -> x.CommonCall calledMethod args thisOpt cilState id
        x.InitializeStatics cilState calledMethod.DeclaringType getArgsAndCall

    member private x.CallDelegate this args (ancestorMethod : Method) (cilState : cilState) =
        assert ancestorMethod.IsDelegate
        match this with
        | NonNullRef as this ->
            match Memory.ReadDelegate cilState.state this with
            | Some (ConcreteDelegate info) ->
                let mi = Application.getMethod info.methodInfo
                // [NOTE] target is ref to closure: when we have it, 'this' = target, otherwise 'this' = thisOption
                let this =
                    match info.target with
                    | NullRef _ -> this
                    | target -> target
                x.CommonCallVirt mi this args cilState
            | Some (CombinedDelegate delegates) ->
                assert(List.length delegates > 1)
                let argTypes = List.map TypeOf args
                let targets = List<term>()
                let methods = List<MethodInfo>()
                for d in delegates do
                    match d with
                    | ConcreteDelegate {target = NonNullRef as target; methodInfo = mi} ->
                        targets.Add target
                        methods.Add mi
                    | ConcreteDelegate {methodInfo = mi} ->
                        targets.Add this
                        methods.Add mi
                    | _ ->
                        assert(IsReference d)
                        targets.Add d
                        let mi = (ancestorMethod :> IMethod).MethodBase :?> MethodInfo
                        methods.Add mi
                let method = Reflection.createCombinedDelegate methods argTypes |> Application.getMethod
                let args = Seq.append args targets |> Seq.toList
                x.CommonCall method args None cilState id
            | Some ref ->
                assert(IsReference ref)
                x.CommonCallVirt ancestorMethod ref args cilState
            | _ -> x.CommonCallVirt ancestorMethod this args cilState
        | _ -> x.Raise x.NullReferenceException cilState id

    member x.CommonCallVirt (ancestorMethod : Method) this args cilState =
        let callVirtual (cilState : cilState) this k =
            let baseType = MostConcreteTypeOfRef cilState.state this
            // Forcing CallAbstract for delegates to generate mocks
            let canBeOverriden() = ancestorMethod.CanBeOverriden baseType && not baseType.IsSealed
            if baseType.IsAbstract || canBeOverriden() || ancestorMethod.IsDelegate then
                x.CallAbstract baseType ancestorMethod this args cilState k
            else
                let targetMethod = ancestorMethod.ResolveOverrideInType baseType
                if targetMethod.IsAbstract then
                    x.CallAbstract baseType (targetMethod :?> Method) this args cilState k
                else
                    let this = Types.Cast this targetMethod.ReflectedType
                    x.CommonCall (targetMethod :?> Method) args (Some this) cilState k

        // NOTE: there is no need to initialize statics, because they were initialized before ``newobj'' execution
        let call (cilState : cilState) k =
            if ancestorMethod.IsVirtual && not ancestorMethod.IsFinal then
                GuardedApplyCIL cilState this callVirtual k
            else
                let actualThis = Types.Cast this ancestorMethod.ReflectedType
                x.CommonCall ancestorMethod args (Some actualThis) cilState k

        x.NpeOrInvokeStatementCIL cilState this call id

    member x.CallVirt (m : Method) offset (cilState : cilState) =
        let ancestorMethod = resolveMethodFromMetadata m (offset + Offset.from OpCodes.Call.Size) |> Application.getMethod
        let thisOption, args = x.RetrieveCalledMethodAndArgs OpCodes.Callvirt ancestorMethod cilState
        let this =
            match thisOption with
            | Some this -> this
            | None -> internalfailf "None this in callvirt"

        if ancestorMethod.IsDelegate then x.CallDelegate this args ancestorMethod cilState
        else x.CommonCallVirt ancestorMethod this args cilState

    member x.ReduceArrayCreation (arrayType : Type) (cilState : cilState) (lengths : term list) k =
        Memory.AllocateDefaultArray cilState.state lengths arrayType |> k

    member x.Ret (m : Method) (cilState : cilState) =
        ret m cilState
        ILInterpreter.CheckNotNullAttribute m cilState true id

    member x.CommonCreateDelegate (ctor : Method) (cilState : cilState) (args : term list) k =
        assert(List.length args = 2)
        let target, methodPtr = args[0], args[1]
        let retrieveMethodInfo methodPtr =
            match methodPtr.term with
            | Concrete(:? MethodInfo as mi, _) -> mi
            | _ -> __unreachable__()
        let methodInfo = retrieveMethodInfo methodPtr
        let delegateType = ctor.DeclaringType
        Memory.AllocateDelegate cilState.state methodInfo target delegateType |> k

    member x.NewObj (m : Method) offset (cilState : cilState) =
        let calledMethod = resolveMethodFromMetadata m (offset + Offset.from OpCodes.Newobj.Size) |> Application.getMethod
        assert (calledMethod :> IMethod).IsConstructor
        let constructorInfo = calledMethod
        let typ = constructorInfo.DeclaringType
        x.InitializeStatics cilState constructorInfo.DeclaringType (fun cilState ->
        let this, args = x.RetrieveCalledMethodAndArgs OpCodes.Newobj calledMethod cilState
        assert(Option.isNone this)

        let blockCase (cilState : cilState) =
            let ref =
                if Types.IsValueType typ || TypeUtils.isPointer typ then
                    let freshValue = Memory.DefaultOf typ
                    Memory.AllocateTemporaryLocalVariable cilState.state -1 typ freshValue
                else Memory.AllocateDefaultClass cilState.state typ
            push ref cilState
            x.CommonCall constructorInfo args (Some ref) cilState id

        let k reference =
            let newIp = moveInstruction (fallThroughTarget m offset) (currentIp cilState)
            push reference cilState
            setCurrentIp newIp cilState
            [cilState]

        if constructorInfo.IsDelegateConstructor then
            x.CommonCreateDelegate constructorInfo cilState args k
        elif typ.IsArray && not constructorInfo.HasBody then
            try
                // TODO: can lower bounds be specified via newobj?
                x.ReduceArrayCreation typ cilState args k
            with
            | :? OutOfMemoryException -> x.Raise x.OutOfMemoryException cilState id
        else blockCase cilState)

    member x.LdsFld addressNeeded (m : Method) offset (cilState : cilState) =
        let newIp = moveInstruction (fallThroughTarget m offset) (currentIp cilState)
        let fieldInfo = resolveFieldFromMetadata m (offset + Offset.from OpCodes.Ldsfld.Size)
        assert fieldInfo.IsStatic
        let declaringType = fieldInfo.DeclaringType
        x.InitializeStatics cilState declaringType (fun cilState ->
        let fieldId = Reflection.wrapField fieldInfo
        let value =
            if addressNeeded && not (TypeUtils.isImplementationDetails declaringType) then
                StaticField(declaringType, fieldId) |> Ref
            else Memory.ReadStaticField cilState.state declaringType fieldId
        push value cilState
        setCurrentIp newIp cilState
        [cilState])

    member private x.StsFld (m : Method) offset (cilState : cilState) =
        let newIp = moveInstruction (fallThroughTarget m offset) (currentIp cilState) // TODO: remove this copy-paste
        let fieldInfo = resolveFieldFromMetadata m (offset + Offset.from OpCodes.Stsfld.Size)
        assert fieldInfo.IsStatic
        x.InitializeStatics cilState fieldInfo.DeclaringType (fun cilState ->
        let declaringType = fieldInfo.DeclaringType
        let fieldId = Reflection.wrapField fieldInfo
        let value = pop cilState
        let fieldType = fieldInfo.FieldType
        let value = Types.Cast value fieldType
        Memory.WriteStaticField cilState.state declaringType fieldId value
        setCurrentIp newIp cilState
        [cilState])

    member x.Ldobj (m : Method) offset (cilState : cilState) =
        let address = pop cilState
        let typ = resolveTypeFromMetadata m (offset + Offset.from OpCodes.Ldobj.Size)
        let readValue cilState k =
            let actualType = MostConcreteTypeOfRef cilState.state address
            let value =
                if typ.IsAssignableFrom actualType then
                    let value = read cilState address
                    Types.Cast value typ
                else
                    let address = Types.Cast address (typ.MakePointerType())
                    read cilState address
            push value cilState
            List.singleton cilState |> k
        x.NpeOrInvokeStatementCIL cilState address readValue id

    member x.Stobj (m : Method) offset (cilState : cilState) =
        let value, ref = pop2 cilState
        let typ = resolveTypeFromMetadata m (offset + Offset.from OpCodes.Stobj.Size)
        let store cilState k =
            let value = Types.Cast value typ
            write cilState ref value |> k
        x.NpeOrInvokeStatementCIL cilState ref store id

    member x.LdFldWithFieldInfo (fieldInfo : FieldInfo) addressNeeded (cilState : cilState) =
        assert(not fieldInfo.IsStatic)
        let target = pop cilState
        let loadWhenTargetIsNotNull (cilState : cilState) k =
            let fieldId = Reflection.wrapField fieldInfo
            let t = fieldInfo.DeclaringType
            let value =
                match t with
                | TypeUtils.Native when addressNeeded -> target
                | TypeUtils.Native -> read cilState target
                | _ when addressNeeded -> Memory.ReferenceField cilState.state target fieldId
                | _ -> readField cilState target fieldId
            push value cilState
            k [cilState]
        x.NpeOrInvokeStatementCIL cilState target loadWhenTargetIsNotNull id

    member x.LdFld addressNeeded (m : Method) offset (cilState : cilState) =
        let fieldInfo = resolveFieldFromMetadata m (offset + Offset.from OpCodes.Ldfld.Size)
        x.LdFldWithFieldInfo fieldInfo addressNeeded cilState

    member x.StFld (m : Method) offset (cilState : cilState) =
        let fieldInfo = resolveFieldFromMetadata m (offset + Offset.from OpCodes.Stfld.Size)
        assert(not fieldInfo.IsStatic)
        let value, targetRef = pop2 cilState
        let storeWhenTargetIsNotNull (cilState : cilState) k =
            let fieldType = fieldInfo.FieldType
            let value = Types.Cast value fieldType
            let reference =
                if TypeUtils.isPointer fieldInfo.DeclaringType then targetRef
                else Reflection.wrapField fieldInfo |> Memory.ReferenceField cilState.state targetRef
            write cilState reference value |> k
        x.NpeOrInvokeStatementCIL cilState targetRef storeWhenTargetIsNotNull id

    member private x.LdElemCommon (typ : Type option) (cilState : cilState) arrayRef indices =
        let arrayType = MostConcreteTypeOfRef cilState.state arrayRef
        let uncheckedLdElem (cilState : cilState) k =
            let value = readIndex cilState arrayRef indices typ
            push value cilState
            k [cilState]
        let checkedLdElem (cilState : cilState) k =
            let dims = List.init (Types.RankOf arrayType) MakeNumber
            let lengths = List.map (Memory.ArrayLengthByDimension cilState.state arrayRef) dims
            x.AccessMultidimensionalArray uncheckedLdElem cilState lengths indices k // TODO: if ptr, do net use check #do
        x.NpeOrInvokeStatementCIL cilState arrayRef checkedLdElem id
    member private x.LdElemWithCast typ (cilState : cilState) : cilState list =
        let index, arrayRef = pop2 cilState
        x.LdElemCommon typ cilState arrayRef [index]
    member private x.LdElemTyp typ (cilState : cilState) = x.LdElemWithCast (Some typ) cilState
    member private x.LdElem (m : Method) offset (cilState : cilState) =
        let typ = resolveTypeFromMetadata m (offset + Offset.from OpCodes.Ldelem.Size)
        x.LdElemTyp typ cilState
    member private x.LdElemRef = x.LdElemWithCast None
    member private x.LdElema (m : Method) offset (cilState : cilState) =
        let typ = resolveTypeFromMetadata m (offset + Offset.from OpCodes.Ldelema.Size)
        let index, arrayRef = pop2 cilState
        let index = Types.Cast index typeof<int>
        let referenceLocation (cilState : cilState) k =
            let value = Memory.ReferenceArrayIndex cilState.state arrayRef [index] (Some typ)
            push value cilState
            k [cilState]
        let checkTypeMismatch (cilState : cilState) (k : cilState list -> 'a) =
            let elementType = MostConcreteTypeOfRef cilState.state arrayRef |> Types.ElementType
            StatedConditionalExecutionCIL cilState
                (fun state k -> k (Types.TypeIsType typ elementType &&& Types.TypeIsType elementType typ, state))
                referenceLocation
                (x.Raise x.ArrayTypeMismatchException)
                k
        let checkIndex (cilState : cilState) k =
            let length = Memory.ArrayLengthByDimension cilState.state arrayRef (MakeNumber 0)
            x.AccessArray checkTypeMismatch cilState length index k
        x.NpeOrInvokeStatementCIL cilState arrayRef checkIndex id
    member private x.StElemCommon (typ : Type option) (cilState : cilState) arrayRef indices value =
        let arrayType = MostConcreteTypeOfRef cilState.state arrayRef
        let baseType = Types.ElementType arrayType
        let checkedStElem (cilState : cilState) (k : cilState list -> 'a) =
            let typeOfValue = TypeOf value
            let uncheckedStElem (cilState : cilState) (k : cilState list -> 'a) =
                writeIndex cilState arrayRef indices value typ |> k
            let checkTypeMismatch (cilState : cilState) (k : cilState list -> 'a) =
                let condition =
                    if Types.IsValueType typeOfValue then True()
                    else Types.RefIsAssignableToType cilState.state value baseType
                StatedConditionalExecutionCIL cilState
                    (fun state k -> k (condition, state))
                    uncheckedStElem
                    (x.Raise x.ArrayTypeMismatchException)
                    k
            let dims = List.init (Types.RankOf arrayType) MakeNumber
            let lengths = List.map (Memory.ArrayLengthByDimension cilState.state arrayRef) dims
            x.AccessMultidimensionalArray checkTypeMismatch cilState lengths indices k
        x.NpeOrInvokeStatementCIL cilState arrayRef checkedStElem id
    member private x.StElemWithCast typ (cilState : cilState) =
        let value, index, arrayRef = pop3 cilState
        x.StElemCommon typ cilState arrayRef [index] value
    member private x.StElemTyp typ (cilState : cilState) =
        x.StElemWithCast (Some typ) cilState
    member private x.StElem cfg offset (cilState : cilState) =
        let typ = resolveTypeFromMetadata cfg (offset + Offset.from OpCodes.Stelem.Size)
        x.StElemWithCast (Some typ) cilState
    member private x.StElemRef = x.StElemWithCast None
    member private x.LdLen (cilState : cilState) =
        let arrayRef = pop cilState
        let ldlen (cilState : cilState) k =
            let length = Memory.ArrayLengthByDimension cilState.state arrayRef (MakeNumber 0)
            push length cilState
            k [cilState]
        x.NpeOrInvokeStatementCIL cilState arrayRef ldlen id

    member private x.LdVirtFtn (m : Method) offset (cilState : cilState) =
        let ancestorMethodBase = resolveMethodFromMetadata m (offset + Offset.from OpCodes.Ldvirtftn.Size)
        let this = pop cilState
        let ldvirtftn (cilState : cilState) k =
            assert(IsReference this)
            let thisType = MostConcreteTypeOfRef cilState.state this
            let ancestorMethod = Application.getMethod ancestorMethodBase
            let overriden = ancestorMethod.ResolveOverrideInType thisType
            let methodInfo = (overriden :> IMethod).MethodBase
            let methodInfoType = methodInfo.GetType()
            let methodPtr = Terms.Concrete methodInfo methodInfoType
            push methodPtr cilState
            k [cilState]
        x.NpeOrInvokeStatementCIL cilState this ldvirtftn id

    member private x.Ldind t (cilState : cilState) =
        let address = pop cilState
        let load cilState k =
            let castedAddress =
                if TypeOfLocation address = t then address
                else Types.Cast address (t.MakePointerType())
            let value = read cilState castedAddress
            push value cilState
            k (List.singleton cilState)
        x.NpeOrInvokeStatementCIL cilState address load id

    member private x.Stind valueCast (cilState : cilState) =
        let value, address = pop2 cilState
        let store cilState k =
            let value = valueCast value
            write cilState address value |> k
        x.NpeOrInvokeStatementCIL cilState address store id

    member x.BoxNullable (t : Type) (v : term) (cilState : cilState) : cilState list =
        // TODO: move it to Reflection.fs; add more validation in case if .NET implementation does not have these fields
        let boxValue (cilState : cilState) =
            let value = pop cilState
            let address = Memory.BoxValueType cilState.state value
            push address cilState
        let hasValueCase (cilState : cilState) k =
            let valueFieldInfo = t.GetField("value", Reflection.instanceBindingFlags)
            push v cilState
            let cilStates = x.LdFldWithFieldInfo valueFieldInfo false cilState
            List.iter boxValue cilStates
            k cilStates
        let boxNullable (hasValue, cilState : cilState) k =
            StatedConditionalExecutionCIL cilState
                (fun state k -> k (hasValue, state))
                hasValueCase
                (fun cilState k ->
                    push (NullRef t) cilState
                    k [cilState])
                k
        let hasValueFieldInfo = t.GetField("hasValue", Reflection.instanceBindingFlags)
        let hasValueResults =
            push v cilState
            x.LdFldWithFieldInfo hasValueFieldInfo false cilState
            |> List.map (fun cilState -> (pop cilState, cilState))
        Cps.List.mapk boxNullable hasValueResults List.concat

    member x.Box (m : Method) offset (cilState : cilState) =
        let t = resolveTypeFromMetadata m (offset + Offset.from OpCodes.Box.Size)
        if Types.IsValueType t then
            let v = pop cilState
            if Types.IsNullable t then x.BoxNullable t v cilState
            else
                let v = Types.Cast v t
                allocateValueTypeInHeap v cilState
                [cilState]
        else [cilState]
    member private x.UnboxCommon cilState obj t handleRestResults k =
        let nonExceptionCont (cilState : cilState) res k =
            push res cilState
            k [cilState]
        assert(IsReference obj)
        assert(Types.IsValueType t)
        let nullCase (cilState : cilState) k =
            if Types.IsNullable t then
                let nullableTerm = Memory.DefaultOf t
                let address = Memory.BoxValueType cilState.state nullableTerm
                let ref = HeapReferenceToBoxReference address
                let res = handleRestResults cilState ref
                nonExceptionCont cilState res k
            else
                x.Raise x.NullReferenceException cilState k
        let nullableCase (cilState : cilState) =
            let underlyingTypeOfNullableT = Nullable.GetUnderlyingType t
            StatedConditionalExecutionCIL cilState
                (fun state k -> k (Types.RefIsType state obj underlyingTypeOfNullableT, state))
                (fun cilState k ->
                    let value = HeapReferenceToBoxReference obj |> read cilState
                    let nullableTerm = Memory.DefaultOf t
                    let valueField, hasValueField = Reflection.fieldsOfNullable t
                    let nullableTerm =
                        writeStructField cilState nullableTerm valueField value
                    let nullableTerm =
                        writeStructField cilState nullableTerm hasValueField (MakeBool true)
                    let address = Memory.BoxValueType cilState.state nullableTerm
                    let ref = HeapReferenceToBoxReference address
                    let res = handleRestResults cilState ref
                    nonExceptionCont cilState res k)
                (x.Raise x.InvalidCastException)
        let nonNullCase (cilState : cilState) =
            if Types.IsNullable t then
                nullableCase cilState
            else
                StatedConditionalExecutionCIL cilState
                    (fun state k -> k (Types.IsCast state obj t, state))
                    (fun cilState k ->
                        let ref = Types.Cast obj t |> HeapReferenceToBoxReference
                        let res = handleRestResults cilState ref
                        push res cilState
                        k [cilState])
                    (x.Raise x.InvalidCastException)
        BranchOnNullCIL cilState obj
            nullCase
            nonNullCase
            k

    member private x.SetExceptionIP cilState =
        let codeLocations = List.map (Option.get << ip2codeLocation) cilState.ipStack
        setCurrentIp (SearchingForHandler(None, List.empty, codeLocations, List.empty)) cilState

    member private x.CommonThrow cilState error isRuntime =
        let codeLocations =
            List.takeUntil isFilter cilState.ipStack
            |> List.map (Option.get << ip2codeLocation)
        let stackTrace = List.map toString codeLocations |> join ","
        setCurrentIpSafe (SearchingForHandler(None, List.empty, codeLocations, List.empty)) cilState
        setException (Unhandled(error, isRuntime, stackTrace)) cilState

    member private x.Throw (cilState : cilState) =
        let error = peek cilState
        let isRuntime = (currentMethod cilState).IsRuntimeException
        BranchOnNullCIL cilState error
            (x.Raise x.NullReferenceException)
            (fun cilState k ->
                x.CommonThrow cilState error isRuntime
                clearEvaluationStackLastFrame cilState
                k [cilState])
            id

    member private x.Rethrow (cilState : cilState) =
        let state = cilState.state
        assert(Option.isSome state.exceptionsRegister.ExceptionTerm)
        state.exceptionsRegister <- state.exceptionsRegister.TransformToUnhandled()
        x.SetExceptionIP cilState
        List.singleton cilState

    member private x.MoveToFinally cilState ehcs (tryBlocks : HashSet<offset * offset>) (location : codeLocation) isSecondBypass =
        let mutable ehcs = ehcs
        let mutable finallyHandlerIp = None
        let offset = location.offset
        while not (Option.isSome finallyHandlerIp || List.isEmpty ehcs) do
            let ehc = List.head ehcs
            ehcs <- List.tail ehcs
            match ehc.ehcType with
            | _ when x.InHandlerBlock offset ehc ->
                if isSecondBypass then moveDownExceptionRegister cilState
                else popExceptionRegister cilState
            | Finally ->
                finallyHandlerIp <- Some (Instruction(ehc.handlerOffset, location.method))
            | Fault when isSecondBypass ->
                finallyHandlerIp <- Some (Instruction(ehc.handlerOffset, location.method))
            | _ when tryBlocks.Add(ehc.tryOffset, ehc.tryLength) ->
                if isSecondBypass then moveDownExceptionRegister cilState
                else popExceptionRegister cilState
            | _ -> ()
        finallyHandlerIp, ehcs

    member private x.LeaveToFinally cilState ehcs (location : codeLocation) =
        let tryBlocks = HashSet<offset * offset>()
        x.MoveToFinally cilState ehcs tryBlocks location false

    member private x.BypassToFinally cilState ehcs (currentLocation : codeLocation) handlerLoc =
        let tryBlocks = HashSet<offset * offset>()
        let currentMethod = currentLocation.method
        match handlerLoc with
        | Some handlerLoc when currentMethod = handlerLoc.method ->
            let handlers = currentMethod.ExceptionHandlers
            let catchHandler = handlers |> Array.find (fun ehc -> ehc.handlerOffset = handlerLoc.offset)
            tryBlocks.Add(catchHandler.tryOffset, catchHandler.tryLength) |> ignore
        | _ -> ()
        x.MoveToFinally cilState ehcs tryBlocks currentLocation true

    // Searching for handler, found list of 'try/catch' blocks and sorted them and now choose one acceptable
    // Look through blocks, if it is suitable catch, continue execution with 'SecondBypass'
    // If it is filter, push exception register and continue execution with 'InFilterHandler'
    // If suitable block was not found, try again with 'sortedBlocks = tail' sortedBlocks
    member private x.FindCatch ehcs (observed : ExceptionHandlingClause list) (location : codeLocation) locations framesToPop cilState =
        let state = cilState.state
        let errorRef = state.exceptionsRegister.GetError()
        let exceptionType = lazy(MostConcreteTypeOfRef state errorRef)
        let mutable ehcs = ehcs
        let observed = List<ExceptionHandlingClause>(observed)
        let mutable nextIp = None
        let offset = location.offset
        while not (Option.isSome nextIp || List.isEmpty ehcs) do
            let ehc = List.head ehcs
            ehcs <- List.tail ehcs
            observed.Add ehc
            match ehc.ehcType with
            | _ when x.InHandlerBlock offset ehc -> ()
            | Catch t when TypeUtils.isSubtypeOrEqual exceptionType.Value t ->
                // Check type and go
                let handlerLocation = Some {method = location.method; offset = ehc.handlerOffset}
                let observed = List.ofSeq observed
                nextIp <- Some (SecondBypass(None, None, observed, Some location, framesToPop, handlerLocation))
            | Filter o ->
                // Start executing filter
                let method = location.method
                push errorRef cilState
                newExceptionRegister cilState
                let handlerOffset = ehc.handlerOffset
                let filterHandler = instruction method o
                let observed = List.ofSeq observed
                nextIp <- Some (InFilterHandler(filterHandler, handlerOffset, ehcs, observed, locations, framesToPop))
            | _ -> () // Handler is non-suitable catch or finally
        nextIp

    member private x.EHCBetween (src : offset) (dst : offset) (ehc : ExceptionHandlingClause) =
        x.InEHCBlock src ehc && not (x.InEHCBlock dst ehc)

    member private x.Leave (m : Method) offset (cilState : cilState) =
        let dst = unconditionalBranchTarget m offset
        let loc = { offset = offset; method = m }
        let ehcs = x.SortEHCBlocks loc |> List.filter (x.EHCBetween offset dst)
        let finallyHandlerIp, otherEchs = x.LeaveToFinally cilState ehcs loc
        let currentIp =
            match finallyHandlerIp with
            | None ->
                assert(List.isEmpty otherEchs)
                Instruction(dst, m)
            | Some ip -> leave ip otherEchs dst m
        setCurrentIpSafe currentIp cilState

    member private x.Unbox (m : Method) offset (cilState : cilState) =
        let t = resolveTypeFromMetadata m (offset + Offset.from OpCodes.Unbox.Size)
        let obj = pop cilState
        // TODO: Nullable.GetUnderlyingType for generics; use meta-information of generic type parameter
        if t.IsGenericParameter then
            let iie = createInsufficientInformation "Unboxing generic parameter"
            cilState.iie <- Some iie
            [cilState]
        else
            x.UnboxCommon cilState obj t (fun _ x -> x) id
    member private x.UnboxAny (m : Method) offset (cilState : cilState) =
        let t = resolveTypeFromMetadata m (offset + Offset.from OpCodes.Unbox_Any.Size)
        let valueType = typeof<ValueType>
        let obj = pop cilState
        // TODO: Nullable.GetUnderlyingType for generics; use meta-information of generic type parameter
        if t.IsGenericParameter then
            let iie = createInsufficientInformation "Can't introduce generic type X for equation: T = Nullable<X>"
            cilState.iie <- Some iie
            [cilState]
        else
            StatedConditionalExecutionCIL cilState
                (fun state k -> k (Types.TypeIsType t valueType, state))
                (fun cilState k ->
                    let handleRestResults cilState address = read cilState address
                    x.UnboxCommon cilState obj t handleRestResults k)
                (fun state k -> x.CommonCastClass state obj t k)
                id

    member private this.CommonDivRem performAction (cilState : cilState) =
        let integerCase (cilState : cilState) x y minusOne minValue =
            StatedConditionalExecutionCIL cilState
                (fun state k -> k (Arithmetics.IsZero y, state))
                (this.Raise this.DivideByZeroException)
                (fun cilState ->
                    StatedConditionalExecutionCIL cilState
                        (fun state k -> k ((x === minValue) &&& (y === minusOne), state))
                        (this.Raise this.OverflowException)
                        (fun cilState k ->
                            push (performAction x y) cilState
                            k [cilState]))
                id
        let y, x = pop2 cilState
        match y, x with
        | FloatT, FloatT ->
            push (performAction x y) cilState
            [cilState]
        | Int64T, _
        | UInt64T, _
        | _, Int64T
        | _, UInt64T -> integerCase cilState x y (TypeUtils.Int64.MinusOne()) (TypeUtils.Int64.MinValue())
        | _ -> integerCase cilState x y (TypeUtils.Int32.MinusOne()) (TypeUtils.Int32.MinValue())
        | _ -> __unreachable__()
    member private this.Div (cilState : cilState) =
        let div x y = API.PerformBinaryOperation OperationType.Divide x y id
        this.CommonDivRem div cilState

    member private this.Rem (cilState : cilState) =
        let rem x y = API.PerformBinaryOperation OperationType.Remainder x y id
        this.CommonDivRem rem cilState

    member private this.CommonUnsignedDivRem isRem performAction (cilState : cilState) =
        let y, x = pop2 cilState
        let divRem x y =
            let x = makeUnsignedInteger x id
            let y = makeUnsignedInteger y id
            StatedConditionalExecutionCIL cilState
                (fun state k -> k (Arithmetics.IsZero y, state))
                (this.Raise this.DivideByZeroException)
                (fun cilState k ->
                    push (performAction x y) cilState
                    k [cilState])
                id
        match y, x with
        | _ when TypeUtils.isIntegralTerm x && TypeUtils.isIntegralTerm y ->
            divRem x y
        | DetachedPtrTerm offset2, DetachedPtrTerm offset1 ->
            divRem offset1 offset2
        | FloatT, _
        | _, FloatT when isRem -> internalfailf "Rem.Un is unspecified for Floats"
        | _ when IsRefOrPtr x || IsRefOrPtr y -> __insufficientInformation__ "trying to div/rem pointers"
        | _ -> internalfailf "incompatible operands for %s" (if isRem then "Rem.Un" else "Div.Un")

    member private this.DivUn (cilState : cilState) =
        let div x y = API.PerformBinaryOperation OperationType.Divide_Un x y id
        this.CommonUnsignedDivRem false div cilState

    member private this.RemUn cilState =
        let rem x y = API.PerformBinaryOperation OperationType.Remainder_Un x y id
        this.CommonUnsignedDivRem true rem cilState

    member private this.UnsignedCheckOverflow checkOverflowForUnsigned (cilState : cilState) =
        let y, x = pop2 cilState
        match y, x with
        | Int64T, _
        | _, Int64T
        | UInt64T, _
        | _, UInt64T ->
            let x = makeUnsignedInteger x id
            let y = makeUnsignedInteger y id
            let max = TypeUtils.UInt64.MaxValue()
            let zero = TypeUtils.UInt64.Zero()
            checkOverflowForUnsigned zero max x y cilState // TODO: maybe rearrange x and y if y is concrete and x is symbolic
        | _ when TypeUtils.isIntegralTerm x && TypeUtils.isIntegralTerm y ->
            let x, y = makeUnsignedInteger x id, makeUnsignedInteger y id
            let max = TypeUtils.UInt32.MaxValue()
            let zero = TypeUtils.UInt32.Zero()
            checkOverflowForUnsigned zero max x y cilState // TODO: maybe rearrange x and y if y is concrete and x is symbolic
        | _ -> internalfailf "incompatible operands for UnsignedCheckOverflow"
    member private this.SignedCheckOverflow checkOverflow (cilState : cilState) =
        let y, x = pop2 cilState
        match y, x with
        | Int64T, _
        | _, Int64T ->
            let min = TypeUtils.Int64.MinValue()
            let max = TypeUtils.Int64.MaxValue()
            let zero = TypeUtils.Int64.Zero()
            let minusOne = TypeUtils.Int64.MinusOne()
            checkOverflow min max zero minusOne x y cilState // TODO: maybe rearrange x and y if y is concrete and x is symbolic
        | UInt64T, _
        | _, UInt64T -> __unreachable__() // instead of add_ovf should be called add_ovf_un
        | FloatT, _
        | _, FloatT -> __unreachable__() // only integers
        | _ ->
            let min = TypeUtils.Int32.MinValue()
            let max = TypeUtils.Int32.MaxValue()
            let zero = TypeUtils.Int32.Zero()
            let minusOne = TypeUtils.Int32.MinusOne()
            checkOverflow min max zero minusOne x y cilState // TODO: maybe rearrange x and y if y is concrete and x is symbolic
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
                PerformBinaryOperation OperationType.Add x y (fun sum ->
                    push sum cilState
                    k [cilState])
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
                PerformBinaryOperation OperationType.Multiply x y (fun res ->
                    push res cilState
                    k [cilState])
            StatedConditionalExecutionCIL cilState isZero
                (fun cilState k ->
                    push zero cilState
                    k [cilState])
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
                    push res cilState
                    k [cilState]))
                (this.Raise this.OverflowException)
                id
        this.UnsignedCheckOverflow checkOverflowForUnsigned cilState
    member private this.Mul_ovf_un (cilState : cilState) =
        let checkOverflowForUnsigned zero max x y cilState =
            let isZero state k = k ((x === zero) ||| (y === zero), state)
            let zeroCase cilState k =
                push zero cilState
                List.singleton cilState |> k
            let checkOverflow cilState k =
                let evalCondition state k =
                    PerformBinaryOperation OperationType.Divide max x (fun quotient ->
                    k (Arithmetics.GreaterOrEqualUn quotient y, state))
                let mul cilState k =
                    PerformBinaryOperation OperationType.Multiply x y (fun res ->
                    push res cilState
                    List.singleton cilState |> k)
                StatedConditionalExecutionCIL cilState
                    evalCondition
                    mul
                    (this.Raise this.OverflowException)
                    k
            StatedConditionalExecutionCIL cilState
                isZero
                zeroCase
                checkOverflow
                id
        this.UnsignedCheckOverflow checkOverflowForUnsigned cilState
    member private this.Sub_ovf_un (cilState : cilState) =
        let checkOverflowForUnsigned _ _ x y cilState =
            let (>>=) = API.Arithmetics.(>>=)
            StatedConditionalExecutionCIL cilState
                (fun state k -> k (x >>= y, state))
                (fun (cilState : cilState) k -> // no overflow
                    PerformBinaryOperation OperationType.Subtract x y (fun res ->
                    push res cilState
                    k [cilState]))
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
                    push res cilState
                    k [cilState])
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

    member private x.Newarr (m : Method) offset (cilState : cilState) =
        let (>>=) = API.Arithmetics.(>>=)
        let elemType = resolveTypeFromMetadata m (offset + Offset.from OpCodes.Newarr.Size)
        let numElements = pop cilState
        let allocate cilState k =
            try
                let ref = Memory.AllocateVectorArray cilState.state numElements elemType
                push ref cilState
                k [cilState]
            with
            | :? OutOfMemoryException -> x.Raise x.OutOfMemoryException cilState k
        StatedConditionalExecutionCIL cilState
            (fun state k -> k (numElements >>= TypeUtils.Int32.Zero(), state))
            allocate
            (this.Raise this.OverflowException)
            id

    member x.CreateException (exceptionType : Type) arguments cilState =
        assert(not exceptionType.IsValueType)
        let stackTrace = Memory.StackTrace cilState.state.stack |> List.map toString |> join "\n"
        Logger.info $"{exceptionType}!\nStack trace:\n{stackTrace}"
        clearEvaluationStackLastFrame cilState
        let constructors = exceptionType.GetConstructors()
        let argumentsLength = List.length arguments
        let argumentsTypes = List.map TypeOf arguments
        let suitable (ci : ConstructorInfo) =
            let parameters = ci.GetParameters()
            parameters.Length = argumentsLength
            && parameters |> Seq.forall2 (fun p1 p2 -> p2.ParameterType.IsAssignableFrom p1) argumentsTypes
        let ctors = Array.filter suitable constructors
        assert(Array.length ctors = 1)
        let ctor = Application.getMethod ctors[0]
        assert ctor.HasRuntimeExceptionImpl
        let proxyCtor = Application.getMethod ctor.RuntimeExceptionImpl
        let success = x.TryConcreteInvoke proxyCtor arguments None cilState
        assert success

    member x.InvalidProgramException cilState =
        x.CreateException typeof<InvalidProgramException> [] cilState
    member x.NullReferenceException cilState =
        x.CreateException typeof<NullReferenceException> [] cilState
    member x.ArgumentException cilState =
        x.CreateException typeof<ArgumentException> [] cilState
    member x.ArgumentNullException cilState =
        x.CreateException typeof<ArgumentNullException> [] cilState
    member x.ArgumentOutOfRangeException cilState =
        x.CreateException typeof<ArgumentOutOfRangeException> [] cilState
    member x.IndexOutOfRangeException cilState =
        x.CreateException typeof<IndexOutOfRangeException> [] cilState
    member x.ArrayTypeMismatchException cilState =
        x.CreateException typeof<ArrayTypeMismatchException> [] cilState
    member x.RankException cilState =
        x.CreateException typeof<RankException> [] cilState
    member x.DivideByZeroException cilState =
        x.CreateException typeof<DivideByZeroException> [] cilState
    member x.OverflowException cilState =
        x.CreateException typeof<OverflowException> [] cilState
    member x.ArithmeticException cilState =
        x.CreateException typeof<ArithmeticException> [] cilState
    member x.TypeInitializerException qualifiedTypeName innerException (cilState : cilState) =
        let typeName = Memory.AllocateString qualifiedTypeName cilState.state
        let args = [typeName; innerException]
        x.CreateException typeof<TypeInitializationException> args cilState
    member x.InvalidCastException (cilState : cilState) =
        let message = Memory.AllocateString "Specified cast is not valid." cilState.state
        x.CreateException typeof<InvalidCastException> [message] cilState
    member x.OutOfMemoryException (cilState : cilState) =
        x.CreateException typeof<OutOfMemoryException> [] cilState

    // -------------------------------- ExplorerBase operations -------------------------------------

    member x.ExecuteOneInstruction (cilState : cilState) : cilState list * cilState list * cilState list =
        x.ExecuteAllInstructionsWhile (always false) cilState

    // returns finishedStates, incompleteStates, erroredStates
    member x.ExecuteAllInstructionsWhile (condition : ip -> bool) (cilState : cilState) =
        let rec executeAllInstructions (finishedStates, incompleteStates, errors) cilState k =
            let ip = currentIp cilState
            try
                let allStates = x.MakeStep cilState
                let newErrors, restStates = List.partition isUnhandledExceptionOrError allStates
                let errors = errors @ newErrors
                let newIieStates, goodStates = List.partition isIIEState restStates
                let incompleteStates = newIieStates @ incompleteStates
                match goodStates with
                | _ when List.forall (currentIp >> condition) goodStates ->
                    Cps.List.foldlk executeAllInstructions (finishedStates, incompleteStates, errors) goodStates k
                | _ -> (goodStates @ finishedStates, incompleteStates, errors) |> k
            with
            | :? InsufficientInformationException as iie ->
                cilState.iie <- Some iie
                setCurrentIp ip cilState
                (finishedStates, cilState :: incompleteStates, errors) |> k
        executeAllInstructions ([],[],[]) cilState id

    member private x.IncrementLevelIfNeeded (m : Method) (offset : offset) (cilState : cilState) =
        if offset = 0<offsets> || m.CFG.IsLoopEntry offset then
            incrementLevel cilState {offset = offset; method = m}

    member private x.DecrementMethodLevel (cilState : cilState) method =
        let key = {offset = 0<offsets>; method = method}
        decrementLevel cilState key

    member private x.InTryBlock offset (clause : ExceptionHandlingClause) =
        clause.tryOffset <= offset && offset < clause.tryOffset + clause.tryLength

    member private x.InHandlerBlock offset (clause : ExceptionHandlingClause) =
        clause.handlerOffset <= offset && offset < clause.handlerOffset + clause.handlerLength

    member private x.InEHCBlock offset (clause : ExceptionHandlingClause) =
        x.InTryBlock offset clause || x.InHandlerBlock offset clause

    member private x.SortEHCBlocks (location : codeLocation) =
        let method = location.method
        let offset = location.offset
        let filteredBlocks = method.ExceptionHandlers |> Array.filter (x.InEHCBlock offset)
        filteredBlocks |> Array.sortBy (fun x -> x.handlerOffset + x.handlerLength) |> Array.toList

    static member private FallThroughCall (cilState : cilState) =
        match cilState.ipStack with
        | InstructionEndingIp(offset, caller) as ip :: _ ->
            // TODO: assert (isCallIp ip)
            let newIp = moveInstruction (fallThroughTarget caller offset) ip
            setCurrentIp newIp cilState
            let callOpCode, calledMethod = caller.ParseCallSite offset
            if callOpCode = OpCodes.Newobj && (calledMethod.DeclaringType.IsValueType || TypeUtils.isPointer calledMethod.DeclaringType) then
                pushNewObjForValueTypes cilState
        | _ -> __unreachable__()

    member private x.PushExceptionRegisterIfNeeded (cilState : cilState) (method : Method) (offset : offset) =
        let tryBlocks = HashSet<offset * offset>()
        for handler in method.ExceptionHandlers do
            let tryStart = handler.tryOffset
            if tryStart = offset && tryBlocks.Add(tryStart, handler.tryLength) then
                newExceptionRegister cilState

    member x.MakeStep (cilState : cilState) =
        cilState.stepsNumber <- cilState.stepsNumber + 1u
        let exit m =
            x.DecrementMethodLevel cilState m
            Logger.info $"Done with method {m}"
            match cilState.ipStack with
            | [ Exit _ ] -> ()
            | Exit m :: _ when m.IsStaticConstructor ->
                popFrameOf cilState
            | Exit _ :: _ ->
                popFrameOf cilState
                ILInterpreter.FallThroughCall cilState
            | _ -> __unreachable__()
        let rec makeStep' ip k =
            match ip with
            // Normal execution
            // Also on entering try block we push new exception register
            | Instruction(offset, m) ->
                if offset = 0<offsets> then Logger.info $"Starting to explore method {m}"
                x.PushExceptionRegisterIfNeeded cilState m offset
                x.ExecuteInstruction m offset cilState |> k
            // Exiting method
            | Exit m ->
                exit m
                k [cilState]
            // Finished executing finally block, some more blocks to explore left
            // Replace last ip with instruction and pop last exception register
            | Leave(EndFinally as Instruction(offset, _), ehcs, dst, m) ->
                let loc = { offset = offset; method = m }
                let finallyHandlerIp, otherEhcs = x.LeaveToFinally cilState ehcs loc
                let currentIp =
                    match finallyHandlerIp with
                    | None ->
                        assert(List.isEmpty otherEhcs)
                        Instruction(dst, m)
                    | Some ip -> leave ip otherEhcs dst m
                replaceLastIp currentIp cilState
                clearEvaluationStackLastFrame cilState
                popExceptionRegister cilState
                k [cilState]
            // Continue executing finally block
            | Leave(ip, _, _, _) ->
                makeStep' ip k
            // Searching for handler, no locations left where blocks can be
            | SearchingForHandler(_, _, [], framesToPop) ->
                let ip = SecondBypass(None, None, List.empty, None, framesToPop, None)
                setCurrentIpSafe ip cilState
                k [cilState]
            // Searching for handler
            | SearchingForHandler(sortedBlocks, observed, (location :: otherLocations as locations), framesToPop) ->
                let ehcs =
                    match sortedBlocks with
                    | Some blocks -> blocks
                    | None -> x.SortEHCBlocks location
                let nextIp = x.FindCatch ehcs observed location locations framesToPop cilState
                match nextIp with
                | Some ip -> setCurrentIpSafe ip cilState
                | None ->
                    // Going to next method
                    let ip = SearchingForHandler(None, List.empty, otherLocations, framesToPop @ [location])
                    setCurrentIpSafe ip cilState
                k [cilState]
            // Exception occured while executing filter and no handlers were found
            // Exception means we return to searching for handler after filter block
            | InFilterHandler(EmptySecondBypass, _, ehcs, observed, locations, framesToPop) ->
                let newIp = SearchingForHandler(Some ehcs, observed, locations, framesToPop)
                cilState.filterResult <- None
                replaceLastIp newIp cilState
                popExceptionRegister cilState
                toUnhandledException cilState
                k [cilState]
            // Executing instructions inside filter block
            // Check filter result, if it is 'None' then continue execution
            // If result is 'Some', start conditional execution on filter result
            | InFilterHandler(ip, offset, ehcs, observed, (location :: _ as locations), framesToPop) ->
                match cilState.filterResult with
                | None -> makeStep' ip k
                | Some t ->
                    StatedConditionalExecutionCIL
                        cilState
                        (fun state k -> k (transform2BooleanTerm state.pc t, state))
                        (fun cilState k ->
                            cilState.filterResult <- None
                            let handlerLoc = Some { method = location.method; offset = offset }
                            let ipTrue = SecondBypass(None, None, observed, Some location, framesToPop, handlerLoc)
                            replaceLastIp ipTrue cilState
                            k [cilState])
                        (fun cilState k ->
                            cilState.filterResult <- None
                            let ipFalse = SearchingForHandler(Some ehcs, observed, locations, framesToPop)
                            replaceLastIp ipFalse cilState
                            k [cilState])
                        k
            // Finished executing all finally blocks, and no handler was found
            // We have to check if exception occured in a filter handler ('InFilterHandler' is on some location below in IP stack)
            // If we were in filter, continue searching for handler after filter block
            // Else we set terminating state for program (setting ip 'SearchingForHandler(Some [], [], [])')
            | EmptySecondBypass ->
                let isInFilter = List.tryFind ipIsInFilter cilState.ipStack
                match isInFilter with
                | Some (InFilterHandler(_, _, ehcs, observed, locations, framesToPop)) ->
                    let ip = SearchingForHandler(Some ehcs, observed, locations, framesToPop)
                    popFrameOf cilState
                    replaceLastIp ip cilState
                    popExceptionRegister cilState
                    toUnhandledException cilState
                | _ ->
                    setCurrentIp emptySearchingForHandler cilState
                    toUnhandledException cilState
                k [cilState]
            // Starting to explore catch clause
            // Set exception to caught and push exception object on stack
            | EmptySecondBypassWithCatch(codeLocation) ->
                let ip = Instruction(codeLocation.offset, codeLocation.method)
                setCurrentIpSafe ip cilState
                clearEvaluationStackLastFrame cilState
                toCaughtException cilState
                push (cilState.state.exceptionsRegister.GetError()) cilState
                k [cilState]
            // Finished executing finally block in second bypass
            // We move down exception as it is end of try block
            // Then we go and look for another block
            | SecondBypass(Some EndFinally, ehcs, lastEhcs, lastLocation, locations, codeLocation) ->
                let ip = SecondBypass(None, ehcs, lastEhcs, lastLocation, locations, codeLocation)
                moveDownExceptionRegister cilState
                toUnhandledException cilState
                setCurrentIp ip cilState
                k [cilState]
            // Executing finally block in second bypass
            | SecondBypass(Some ip, _, _, _, _, _) ->
                makeStep' ip k
            // Searching for finally block to execute
            | SecondBypass(None, sortedBlocks, lastBlocks, lastLocation, locations, codeLocation) ->
                let ehcs, lastBlocks, currentLocation =
                    match sortedBlocks, locations, lastLocation with
                    | Some sortedBlocks, location :: _, _ -> sortedBlocks, lastBlocks, location
                    | Some sortedBlocks, _, Some lastLocation -> sortedBlocks, lastBlocks, lastLocation
                    | None, location :: _, _ -> x.SortEHCBlocks location, lastBlocks, location
                    | _, _, Some lastLocation -> lastBlocks, List.empty, lastLocation
                    | _ -> internalfail $"SecondBypass: unexpected ip {ip}"
                let finallyHandlerIp, otherEhcs = x.BypassToFinally cilState ehcs currentLocation codeLocation
                let otherEhcs, locations =
                    match finallyHandlerIp with
                    | None ->
                        assert(List.isEmpty otherEhcs)
                        let locations =
                            match locations with
                            | _ :: otherLocations ->
                                if List.isEmpty otherLocations |> not || Option.isSome codeLocation then
                                    popFrameOf cilState
                                    clearEvaluationStackLastFrame cilState
                                otherLocations
                            | _ -> locations
                        None, locations
                    | Some _ ->
                        toCaughtException cilState
                        Some otherEhcs, locations
                let ip = SecondBypass(finallyHandlerIp, otherEhcs, lastBlocks, lastLocation, locations, codeLocation)
                setCurrentIpSafe ip cilState
                k [cilState]
            | _ -> __notImplemented__()
        makeStep' (currentIp cilState) id

    member private x.ExecuteInstruction m offset (cilState : cilState) =
        let opCode = parseInstruction m offset

        let opcodeValue = LanguagePrimitives.EnumOfValue opCode.Value
        let newSts =
            match opcodeValue with
            | OpCodeValues.Br
            | OpCodeValues.Br_S -> br m offset cilState; [cilState]
            | OpCodeValues.Add ->
                (fun _ _ -> standardPerformBinaryOperation OperationType.Add) |> fallThrough m offset cilState // TODO: check float overflow [spec]
            | OpCodeValues.Mul -> (fun _ _ -> standardPerformBinaryOperation OperationType.Multiply) |> fallThrough m offset cilState
            | OpCodeValues.Sub -> (fun _ _ -> standardPerformBinaryOperation OperationType.Subtract) |> fallThrough m offset cilState
            | OpCodeValues.Shl -> (fun _ _ -> standardPerformBinaryOperation OperationType.ShiftLeft) |> fallThrough m offset cilState
            | OpCodeValues.Shr -> (fun _ _ -> standardPerformBinaryOperation OperationType.ShiftRight) |> fallThrough m offset cilState
            | OpCodeValues.Shr_Un -> (fun _ _ -> standardPerformBinaryOperation OperationType.ShiftRight_Un) |> fallThrough m offset cilState
            | OpCodeValues.Ceq -> (fun _ _ -> ceq) |> fallThrough m offset cilState
            | OpCodeValues.Cgt -> (fun _ _ -> cgt) |> fallThrough m offset cilState
            | OpCodeValues.Cgt_Un -> (fun _ _ -> cgtun) |> fallThrough m offset cilState
            | OpCodeValues.Clt -> (fun _ _ -> clt) |> fallThrough m offset cilState
            | OpCodeValues.Clt_Un -> (fun _ _ -> cltun) |> fallThrough m offset cilState
            | OpCodeValues.And -> (fun _ _ -> bitwiseOrBoolOperation OperationType.BitwiseAnd OperationType.LogicalAnd) |> fallThrough m offset cilState
            | OpCodeValues.Or -> (fun _ _ -> bitwiseOrBoolOperation OperationType.BitwiseOr OperationType.LogicalOr) |> fallThrough m offset cilState
            | OpCodeValues.Xor -> (fun _ _ -> bitwiseOrBoolOperation OperationType.BitwiseXor OperationType.LogicalXor) |> fallThrough m offset cilState
            | OpCodeValues.Neg -> (fun _ _ -> performCILUnaryOperation OperationType.UnaryMinus) |> fallThrough m offset cilState
            | OpCodeValues.Not -> (fun _ _ -> bitwiseOrBoolNot) |> fallThrough m offset cilState
            | OpCodeValues.Stloc -> stloc (fun ilBytes offset -> NumberCreator.extractUnsignedInt16 ilBytes (offset + Offset.from OpCodes.Stloc.Size) |> int) |> forkThrough m offset cilState
            | OpCodeValues.Stloc_0 -> stloc (fun _ _ -> 0) |> forkThrough m offset cilState
            | OpCodeValues.Stloc_1 -> stloc (fun _ _ -> 1) |> forkThrough m offset cilState
            | OpCodeValues.Stloc_2 -> stloc (fun _ _ -> 2) |> forkThrough m offset cilState
            | OpCodeValues.Stloc_3 -> stloc (fun _ _ -> 3) |> forkThrough m offset cilState
            | OpCodeValues.Stloc_S -> stloc (fun ilBytes offset -> NumberCreator.extractUnsignedInt8 ilBytes (offset + Offset.from OpCodes.Stloc_S.Size) |> int) |> forkThrough m offset cilState
            | OpCodeValues.Starg -> starg (fun ilBytes offset -> NumberCreator.extractUnsignedInt16 ilBytes (offset + Offset.from OpCodes.Starg.Size) |> int) |> forkThrough m offset cilState
            | OpCodeValues.Starg_S -> starg (fun ilBytes offset -> NumberCreator.extractUnsignedInt8 ilBytes (offset + Offset.from OpCodes.Starg_S.Size) |> int) |> forkThrough m offset cilState
            | OpCodeValues.Ldc_I4 -> ldc (fun ilBytes offset -> NumberCreator.extractInt32 ilBytes (offset + Offset.from OpCodes.Ldc_I4.Size)) typedefof<int32> |> fallThrough m offset cilState
            | OpCodeValues.Ldc_I4_0 -> ldc (fun _ _ -> 0) typedefof<int32> |> fallThrough m offset cilState
            | OpCodeValues.Ldc_I4_1 -> ldc (fun _ _ -> 1) typedefof<int32> |> fallThrough m offset cilState
            | OpCodeValues.Ldc_I4_2 -> ldc (fun _ _ -> 2) typedefof<int32> |> fallThrough m offset cilState
            | OpCodeValues.Ldc_I4_3 -> ldc (fun _ _ -> 3) typedefof<int32> |> fallThrough m offset cilState
            | OpCodeValues.Ldc_I4_4 -> ldc (fun _ _ -> 4) typedefof<int32> |> fallThrough m offset cilState
            | OpCodeValues.Ldc_I4_5 -> ldc (fun _ _ -> 5) typedefof<int32> |> fallThrough m offset cilState
            | OpCodeValues.Ldc_I4_6 -> ldc (fun _ _ -> 6) typedefof<int32> |> fallThrough m offset cilState
            | OpCodeValues.Ldc_I4_7 -> ldc (fun _ _ -> 7) typedefof<int32> |> fallThrough m offset cilState
            | OpCodeValues.Ldc_I4_8 -> ldc (fun _ _ -> 8) typedefof<int32> |> fallThrough m offset cilState
            | OpCodeValues.Ldc_I4_M1 -> ldc (fun _ _ -> -1) typedefof<int32> |> fallThrough m offset cilState
            | OpCodeValues.Ldc_I4_S -> ldc (fun ilBytes offset -> NumberCreator.extractInt8 ilBytes (offset + Offset.from OpCodes.Ldc_I4_S.Size)) typedefof<int32> |> fallThrough m offset cilState
            | OpCodeValues.Ldc_I8 -> ldc (fun ilBytes offset -> NumberCreator.extractInt64 ilBytes (offset + Offset.from OpCodes.Ldc_I8.Size)) typedefof<int64> |> fallThrough m offset cilState
            | OpCodeValues.Ldc_R4 -> ldc (fun ilBytes offset -> NumberCreator.extractFloat32 ilBytes (offset + Offset.from OpCodes.Ldc_R4.Size)) typedefof<float32> |> fallThrough m offset cilState
            | OpCodeValues.Ldc_R8 -> ldc (fun ilBytes offset -> NumberCreator.extractFloat64 ilBytes (offset + Offset.from OpCodes.Ldc_R8.Size)) typedefof<double> |> fallThrough m offset cilState
            | OpCodeValues.Ldarg -> ldarg (fun ilBytes offset -> NumberCreator.extractUnsignedInt16 ilBytes (offset + Offset.from OpCodes.Ldarg.Size) |> int) |> fallThrough m offset cilState
            | OpCodeValues.Ldarg_0 -> ldarg (fun _ _ -> 0) |> fallThrough m offset cilState
            | OpCodeValues.Ldarg_1 -> ldarg (fun _ _ -> 1) |> fallThrough m offset cilState
            | OpCodeValues.Ldarg_2 -> ldarg (fun _ _ -> 2) |> fallThrough m offset cilState
            | OpCodeValues.Ldarg_3 -> ldarg (fun _ _ -> 3) |> fallThrough m offset cilState
            | OpCodeValues.Ldarg_S -> ldarg (fun ilBytes offset -> NumberCreator.extractUnsignedInt8 ilBytes (offset + Offset.from OpCodes.Ldarg_S.Size) |> int) |> fallThrough m offset cilState
            | OpCodeValues.Nop -> fallThrough m offset cilState (fun _ _ _ -> ())
            | OpCodeValues.Ldloc -> ldloc (fun ilBytes offset -> NumberCreator.extractUnsignedInt16 ilBytes (offset + Offset.from OpCodes.Ldloc.Size) |> int) |> fallThrough m offset cilState
            | OpCodeValues.Ldloc_0 -> ldloc (fun _ _ -> 0) |> fallThrough m offset cilState
            | OpCodeValues.Ldloc_1 -> ldloc (fun _ _ -> 1) |> fallThrough m offset cilState
            | OpCodeValues.Ldloc_2 -> ldloc (fun _ _ -> 2) |> fallThrough m offset cilState
            | OpCodeValues.Ldloc_3 -> ldloc (fun _ _ -> 3) |> fallThrough m offset cilState
            | OpCodeValues.Ldloc_S -> ldloc (fun ilBytes offset -> NumberCreator.extractUnsignedInt8 ilBytes (offset + Offset.from OpCodes.Ldloc_S.Size) |> int) |> fallThrough m offset cilState
            | OpCodeValues.Ldloca -> ldloca (fun ilBytes offset -> NumberCreator.extractUnsignedInt16 ilBytes (offset + Offset.from OpCodes.Ldloca.Size) |> int) |> fallThrough m offset cilState
            | OpCodeValues.Ldloca_S -> ldloca (fun ilBytes offset -> NumberCreator.extractUnsignedInt8 ilBytes (offset + Offset.from OpCodes.Ldloca_S.Size) |> int) |> fallThrough m offset cilState
            | OpCodeValues.Ret -> this.Ret m cilState
            | OpCodeValues.Dup -> (fun _ _ -> dup) |> fallThrough m offset cilState

            // branching
            | OpCodeValues.Brfalse -> brfalse m offset cilState
            | OpCodeValues.Brfalse_S -> brfalse m offset cilState
            | OpCodeValues.Brtrue -> brtrue m offset cilState
            | OpCodeValues.Brtrue_S -> brtrue m offset cilState
            | OpCodeValues.Beq -> applyAndBranch ceq brtrue m offset cilState
            | OpCodeValues.Beq_S -> applyAndBranch ceq brtrue m offset cilState
            | OpCodeValues.Bge -> applyAndBranch bgeHelper brfalse m offset cilState
            | OpCodeValues.Bge_S -> applyAndBranch bgeHelper brfalse m offset cilState

            | OpCodeValues.Bgt -> applyAndBranch cgt brtrue m offset cilState
            | OpCodeValues.Bgt_S -> applyAndBranch cgt brtrue m offset cilState
            | OpCodeValues.Bgt_Un -> applyAndBranch cgtun brtrue m offset cilState
            | OpCodeValues.Bgt_Un_S -> applyAndBranch cgtun brtrue m offset cilState
            | OpCodeValues.Ble -> applyAndBranch cgt brfalse m offset cilState
            | OpCodeValues.Ble_S -> applyAndBranch cgt brfalse m offset cilState
            | OpCodeValues.Ble_Un -> applyAndBranch cgtun brfalse m offset cilState
            | OpCodeValues.Ble_Un_S -> applyAndBranch cgtun brfalse m offset cilState
            | OpCodeValues.Blt -> applyAndBranch clt brtrue m offset cilState
            | OpCodeValues.Blt_S -> applyAndBranch clt brtrue m offset cilState
            | OpCodeValues.Blt_Un -> applyAndBranch cltun brtrue m offset cilState
            | OpCodeValues.Blt_Un_S -> applyAndBranch cltun brtrue m offset cilState
            | OpCodeValues.Bne_Un -> applyAndBranch ceq brfalse m offset cilState
            | OpCodeValues.Bne_Un_S -> applyAndBranch ceq brfalse m offset cilState
            | OpCodeValues.Bge_Un -> applyAndBranch cltun brfalse m offset cilState
            | OpCodeValues.Bge_Un_S -> applyAndBranch cltun brfalse m offset cilState

            | OpCodeValues.Ldstr -> ldstr |> fallThrough m offset cilState
            | OpCodeValues.Ldnull -> (fun _ _ -> ldnull) |> fallThrough m offset cilState
            | OpCodeValues.Conv_I1 -> (fun _ _ -> castTopOfOperationalStack TypeUtils.int8Type) |> fallThrough m offset cilState
            | OpCodeValues.Conv_I2 -> (fun _ _ -> castTopOfOperationalStack TypeUtils.int16Type) |> fallThrough m offset cilState
            | OpCodeValues.Conv_I4 -> (fun _ _ -> castTopOfOperationalStack TypeUtils.int32Type) |> fallThrough m offset cilState
            | OpCodeValues.Conv_I8 -> (fun _ _ -> castTopOfOperationalStack TypeUtils.int64Type) |> fallThrough m offset cilState
            | OpCodeValues.Conv_R4 -> (fun _ _ -> castTopOfOperationalStack TypeUtils.float32Type) |> fallThrough m offset cilState
            | OpCodeValues.Conv_R8 -> (fun _ _ -> castTopOfOperationalStack TypeUtils.float64Type) |> fallThrough m offset cilState
            | OpCodeValues.Conv_U1 -> (fun _ _ -> castTopOfOperationalStack TypeUtils.uint8Type) |> fallThrough m offset cilState
            | OpCodeValues.Conv_U2 -> (fun _ _ -> castTopOfOperationalStack TypeUtils.uint16Type) |> fallThrough m offset cilState
            | OpCodeValues.Conv_U4 -> (fun _ _ -> castTopOfOperationalStack TypeUtils.uint32Type) |> fallThrough m offset cilState
            | OpCodeValues.Conv_U8 -> (fun _ _ -> castTopOfOperationalStack TypeUtils.uint64Type) |> fallThrough m offset cilState
            | OpCodeValues.Conv_I -> (fun _ _ -> convi) |> fallThrough m offset cilState
            | OpCodeValues.Conv_U -> (fun _ _ -> convu) |> fallThrough m offset cilState
            | OpCodeValues.Conv_R_Un -> (fun _ _ -> castTopOfOperationalStack TypeUtils.float64Type) |> fallThrough m offset cilState
            | OpCodeValues.Switch -> switch m offset cilState
            | OpCodeValues.Ldtoken -> ldtoken |> fallThrough m offset cilState
            | OpCodeValues.Ldftn -> ldftn |> fallThrough m offset cilState
            | OpCodeValues.Pop -> (fun _ _ -> pop >> ignore) |> fallThrough m offset cilState
            | OpCodeValues.Initobj -> initobj |> forkThrough m offset cilState
            | OpCodeValues.Ldarga -> ldarga (fun ilBytes offset -> NumberCreator.extractUnsignedInt16 ilBytes (offset + Offset.from OpCodes.Ldarga.Size) |> int) |> fallThrough m offset cilState
            | OpCodeValues.Ldarga_S -> ldarga (fun ilBytes offset -> NumberCreator.extractUnsignedInt8 ilBytes (offset + Offset.from OpCodes.Ldarga_S.Size) |> int) |> fallThrough m offset cilState
            | OpCodeValues.Ldind_I4 -> (fun _ _ -> x.Ldind TypeUtils.int32Type) |> forkThrough m offset cilState
            | OpCodeValues.Ldind_I1 -> (fun _ _ -> x.Ldind TypeUtils.int8Type) |> forkThrough m offset cilState
            | OpCodeValues.Ldind_I2 -> (fun _ _ -> x.Ldind TypeUtils.int16Type) |> forkThrough m offset cilState
            | OpCodeValues.Ldind_I8 -> (fun _ _ -> x.Ldind TypeUtils.int64Type) |> forkThrough m offset cilState
            | OpCodeValues.Ldind_U1 -> (fun _ _ -> x.Ldind TypeUtils.uint8Type) |> forkThrough m offset cilState
            | OpCodeValues.Ldind_U2 -> (fun _ _ -> x.Ldind TypeUtils.uint16Type) |> forkThrough m offset cilState
            | OpCodeValues.Ldind_U4 -> (fun _ _ -> x.Ldind TypeUtils.uint32Type) |> forkThrough m offset cilState
            | OpCodeValues.Ldind_R4 -> (fun _ _ -> x.Ldind TypeUtils.float32Type) |> forkThrough m offset cilState
            | OpCodeValues.Ldind_R8 -> (fun _ _ -> x.Ldind TypeUtils.float64Type) |> forkThrough m offset cilState
            | OpCodeValues.Ldind_Ref -> (fun _ _ -> x.Ldind TypeUtils.intPtr) |> forkThrough m offset cilState
            | OpCodeValues.Ldind_I -> (fun _ _ -> x.Ldind TypeUtils.intPtr) |> forkThrough m offset cilState
            | OpCodeValues.Isinst -> isinst |> forkThrough m offset cilState
            | OpCodeValues.Stobj -> x.Stobj |> forkThrough m offset cilState
            | OpCodeValues.Ldobj -> x.Ldobj |> forkThrough m offset cilState
            | OpCodeValues.Stind_I1 -> (fun _ _ -> x.Stind (castUnchecked TypeUtils.int8Type)) |> forkThrough m offset cilState
            | OpCodeValues.Stind_I2 -> (fun _ _ -> x.Stind (castUnchecked TypeUtils.int16Type)) |> forkThrough m offset cilState
            | OpCodeValues.Stind_I4 -> (fun _ _ -> x.Stind (castUnchecked TypeUtils.int32Type)) |> forkThrough m offset cilState
            | OpCodeValues.Stind_I8 -> (fun _ _ -> x.Stind (castUnchecked TypeUtils.int64Type)) |> forkThrough m offset cilState
            | OpCodeValues.Stind_R4 -> (fun _ _ -> x.Stind (castUnchecked TypeUtils.float32Type)) |> forkThrough m offset cilState
            | OpCodeValues.Stind_R8 -> (fun _ _ -> x.Stind (castUnchecked TypeUtils.float64Type)) |> forkThrough m offset cilState
            | OpCodeValues.Stind_Ref -> (fun _ _ -> x.Stind id) |> forkThrough m offset cilState
            | OpCodeValues.Stind_I -> (fun _ _ -> x.Stind MakeIntPtr) |> forkThrough m offset cilState
            | OpCodeValues.Sizeof -> sizeofInstruction |> fallThrough m offset cilState
            | OpCodeValues.Leave
            | OpCodeValues.Leave_S -> x.Leave m offset cilState; [cilState]
            | OpCodeValues.Endfinally -> (fun _ _ -> endfinally) |> fallThrough m offset cilState
            | OpCodeValues.Rethrow -> x.Rethrow cilState
            | OpCodeValues.Endfilter -> endfilter cilState; [cilState]
            | OpCodeValues.Localloc -> (fun _ _ -> localloc) |> fallThrough m offset cilState
            // TODO: notImplemented instructions
            | OpCodeValues.Stelem_I -> (fun _ _ _ -> __notImplemented__()) |> fallThrough m offset cilState
            | OpCodeValues.Ldelem_I -> (fun _ _ _ -> __notImplemented__()) |> fallThrough m offset cilState
            | OpCodeValues.Arglist -> (fun _ _ _ -> __notImplemented__()) |> fallThrough m offset cilState
            | OpCodeValues.Jmp -> (fun _ _ _ -> __notImplemented__()) |> fallThrough m offset cilState
            | OpCodeValues.Break -> (fun _ _ _ -> __notImplemented__()) |> fallThrough m offset cilState
            | OpCodeValues.Calli -> (fun _ _ _ -> __notImplemented__()) |> fallThrough m offset cilState
            | OpCodeValues.Ckfinite -> (fun _ _ _ -> __notImplemented__()) |> fallThrough m offset cilState
            | OpCodeValues.Constrained_ -> constrained |> fallThrough m offset cilState
            | OpCodeValues.Cpblk -> (fun _ _ _ -> __notImplemented__()) |> fallThrough m offset cilState
            | OpCodeValues.Cpobj -> (fun _ _ _ -> __notImplemented__()) |> fallThrough m offset cilState
            | OpCodeValues.Mkrefany -> (fun _ _ _ -> __notImplemented__()) |> fallThrough m offset cilState
            | OpCodeValues.Prefix1 -> (fun _ _ _ -> __notImplemented__()) |> fallThrough m offset cilState
            | OpCodeValues.Prefix2 -> (fun _ _ _ -> __notImplemented__()) |> fallThrough m offset cilState
            | OpCodeValues.Prefix3 -> (fun _ _ _ -> __notImplemented__()) |> fallThrough m offset cilState
            | OpCodeValues.Prefix4 -> (fun _ _ _ -> __notImplemented__()) |> fallThrough m offset cilState
            | OpCodeValues.Prefix5 -> (fun _ _ _ -> __notImplemented__()) |> fallThrough m offset cilState
            | OpCodeValues.Prefix6 -> (fun _ _ _ -> __notImplemented__()) |> fallThrough m offset cilState
            | OpCodeValues.Prefix7 -> (fun _ _ _ -> __notImplemented__()) |> fallThrough m offset cilState
            | OpCodeValues.Prefixref -> (fun _ _ _ -> __notImplemented__()) |> fallThrough m offset cilState
            | OpCodeValues.Readonly_ -> fallThrough m offset cilState (fun _ _ _ -> ())
            | OpCodeValues.Refanytype -> (fun _ _ _ -> __notImplemented__()) |> fallThrough m offset cilState
            | OpCodeValues.Refanyval -> (fun _ _ _ -> __notImplemented__()) |> fallThrough m offset cilState
            | OpCodeValues.Tail_ -> (fun _ _ _ -> __notImplemented__()) |> fallThrough m offset cilState
            | OpCodeValues.Unaligned_ -> (fun _ _ _ -> __notImplemented__()) |> fallThrough m offset cilState
            | OpCodeValues.Volatile_ -> fallThrough m offset cilState (fun _ _ _ -> ())
            | OpCodeValues.Initblk -> (fun _ _ _ -> __notImplemented__()) |> fallThrough m offset cilState

            | OpCodeValues.Call -> this.Call m offset cilState
            | OpCodeValues.Callvirt -> this.CallVirt m offset cilState
            | OpCodeValues.Newobj -> this.NewObj m offset cilState
            | OpCodeValues.Ldsfld -> this.LdsFld false m offset cilState
            | OpCodeValues.Ldsflda -> this.LdsFld true m offset cilState
            | OpCodeValues.Stsfld -> this.StsFld m offset cilState
            | OpCodeValues.Ldfld -> this.LdFld false |> forkThrough m offset cilState
            | OpCodeValues.Ldflda -> this.LdFld true |> forkThrough m offset cilState
            | OpCodeValues.Stfld -> this.StFld |> forkThrough m offset cilState
            | OpCodeValues.Ldelem -> this.LdElem |> forkThrough m offset cilState
            | OpCodeValues.Ldelema -> this.LdElema |> forkThrough m offset cilState
            | OpCodeValues.Ldelem_I1 -> (fun _ _ -> this.LdElemTyp TypeUtils.int8Type) |> forkThrough m offset cilState
            | OpCodeValues.Ldelem_I2 -> (fun _ _ -> this.LdElemTyp TypeUtils.int16Type) |> forkThrough m offset cilState
            | OpCodeValues.Ldelem_I4 -> (fun _ _ -> this.LdElemTyp TypeUtils.int32Type) |> forkThrough m offset cilState
            | OpCodeValues.Ldelem_I8 -> (fun _ _ -> this.LdElemTyp TypeUtils.int64Type) |> forkThrough m offset cilState
            | OpCodeValues.Ldelem_R4 -> (fun _ _ -> this.LdElemTyp TypeUtils.float32Type) |> forkThrough m offset cilState
            | OpCodeValues.Ldelem_R8 -> (fun _ _ -> this.LdElemTyp TypeUtils.float64Type) |> forkThrough m offset cilState
            | OpCodeValues.Ldelem_U1 -> (fun _ _ -> this.LdElemTyp TypeUtils.uint8Type) |> forkThrough m offset cilState
            | OpCodeValues.Ldelem_U2 -> (fun _ _ -> this.LdElemTyp TypeUtils.uint16Type) |> forkThrough m offset cilState
            | OpCodeValues.Ldelem_U4 -> (fun _ _ -> this.LdElemTyp TypeUtils.uint32Type) |> forkThrough m offset cilState
            | OpCodeValues.Ldelem_Ref -> (fun _ _ -> this.LdElemRef) |> forkThrough m offset cilState
            | OpCodeValues.Stelem -> (fun _ _ -> this.StElem m offset) |> forkThrough m offset cilState
            | OpCodeValues.Stelem_I1 -> (fun _ _ -> this.StElemTyp TypeUtils.int8Type) |> forkThrough m offset cilState
            | OpCodeValues.Stelem_I2 -> (fun _ _ -> this.StElemTyp TypeUtils.int16Type) |> forkThrough m offset cilState
            | OpCodeValues.Stelem_I4 -> (fun _ _ -> this.StElemTyp TypeUtils.int32Type) |> forkThrough m offset cilState
            | OpCodeValues.Stelem_I8 -> (fun _ _ -> this.StElemTyp TypeUtils.int64Type) |> forkThrough m offset cilState
            | OpCodeValues.Stelem_R4 -> (fun _ _ -> this.StElemTyp TypeUtils.float32Type) |> forkThrough m offset cilState
            | OpCodeValues.Stelem_R8 -> (fun _ _ -> this.StElemTyp TypeUtils.float64Type) |> forkThrough m offset cilState
            | OpCodeValues.Stelem_Ref -> (fun _ _ -> this.StElemRef) |> forkThrough m offset cilState
            | OpCodeValues.Conv_Ovf_I1 -> (fun _ _ -> this.ConvOvf TypeUtils.int8Type) |> forkThrough m offset cilState
            | OpCodeValues.Conv_Ovf_I2 -> (fun _ _ -> this.ConvOvf TypeUtils.int16Type) |> forkThrough m offset cilState
            | OpCodeValues.Conv_Ovf_I4 -> (fun _ _ -> this.ConvOvf TypeUtils.int32Type) |> forkThrough m offset cilState
            | OpCodeValues.Conv_Ovf_I8 -> (fun _ _ -> this.ConvOvf TypeUtils.int64Type) |> forkThrough m offset cilState
            | OpCodeValues.Conv_Ovf_I -> (fun _ _ -> convi) |> fallThrough m offset cilState
            | OpCodeValues.Conv_Ovf_U1 -> (fun _ _ -> this.ConvOvf TypeUtils.uint8Type) |> forkThrough m offset cilState
            | OpCodeValues.Conv_Ovf_U2 -> (fun _ _ -> this.ConvOvf TypeUtils.uint16Type) |> forkThrough m offset cilState
            | OpCodeValues.Conv_Ovf_U4 -> (fun _ _ -> this.ConvOvf TypeUtils.uint32Type) |> forkThrough m offset cilState
            | OpCodeValues.Conv_Ovf_U8 -> (fun _ _ -> this.ConvOvf TypeUtils.uint64Type) |> forkThrough m offset cilState
            | OpCodeValues.Conv_Ovf_U -> (fun _ _ -> convu) |> fallThrough m offset cilState
            | OpCodeValues.Conv_Ovf_I1_Un -> (fun _ _ -> this.ConvOvfUn TypeUtils.uint32Type TypeUtils.int8Type) |> forkThrough m offset cilState
            | OpCodeValues.Conv_Ovf_I2_Un -> (fun _ _ -> this.ConvOvfUn TypeUtils.uint32Type TypeUtils.int16Type) |> forkThrough m offset cilState
            | OpCodeValues.Conv_Ovf_I4_Un -> (fun _ _ -> this.ConvOvfUn TypeUtils.uint32Type TypeUtils.int32Type) |> forkThrough m offset cilState
            | OpCodeValues.Conv_Ovf_I8_Un -> (fun _ _ -> this.ConvOvfUn TypeUtils.uint64Type TypeUtils.int64Type) |> forkThrough m offset cilState
            | OpCodeValues.Conv_Ovf_I_Un -> (fun _ _ -> convi) |> fallThrough m offset cilState
            | OpCodeValues.Conv_Ovf_U1_Un -> (fun _ _ -> this.ConvOvfUn TypeUtils.uint32Type TypeUtils.uint8Type) |> forkThrough m offset cilState
            | OpCodeValues.Conv_Ovf_U2_Un -> (fun _ _ -> this.ConvOvfUn TypeUtils.uint32Type TypeUtils.uint16Type) |> forkThrough m offset cilState
            | OpCodeValues.Conv_Ovf_U4_Un -> (fun _ _ -> this.ConvOvfUn TypeUtils.uint32Type TypeUtils.uint32Type) |> forkThrough m offset cilState
            | OpCodeValues.Conv_Ovf_U8_Un -> (fun _ _ -> this.ConvOvfUn TypeUtils.uint64Type TypeUtils.uint64Type) |> forkThrough m offset cilState
            | OpCodeValues.Conv_Ovf_U_Un -> (fun _ _ -> convu) |> fallThrough m offset cilState
            | OpCodeValues.Castclass -> this.CastClass |> forkThrough m offset cilState
            | OpCodeValues.Ldlen -> (fun _ _ -> this.LdLen) |> forkThrough m offset cilState
            | OpCodeValues.Ldvirtftn -> this.LdVirtFtn |> forkThrough m offset cilState
            | OpCodeValues.Box -> this.Box |> forkThrough m offset cilState
            | OpCodeValues.Unbox -> this.Unbox |> forkThrough m offset cilState
            | OpCodeValues.Unbox_Any -> this.UnboxAny |> forkThrough m offset cilState
            | OpCodeValues.Add_Ovf_Un -> (fun _ _ -> this.Add_ovf_un) |> forkThrough m offset cilState
            | OpCodeValues.Sub_Ovf_Un -> (fun _ _ -> this.Sub_ovf_un) |> forkThrough m offset cilState
            | OpCodeValues.Mul_Ovf_Un -> (fun _ _ -> this.Mul_ovf_un) |> forkThrough m offset cilState
            | OpCodeValues.Add_Ovf -> (fun _ _ -> this.Add_ovf) |> forkThrough m offset cilState
            | OpCodeValues.Sub_Ovf -> (fun _ _ -> this.Sub_ovf) |> forkThrough m offset cilState
            | OpCodeValues.Mul_Ovf -> (fun _ _ -> this.Mul_ovf) |> forkThrough m offset cilState
            | OpCodeValues.Div -> (fun _ _ -> this.Div) |> forkThrough m offset cilState
            | OpCodeValues.Div_Un -> (fun _ _ -> this.DivUn) |> forkThrough m offset cilState
            | OpCodeValues.Rem -> (fun _ _ -> this.Rem) |> forkThrough m offset cilState
            | OpCodeValues.Rem_Un -> (fun _ _ -> this.RemUn) |> forkThrough m offset cilState
            | OpCodeValues.Newarr -> this.Newarr |> forkThrough m offset cilState
            | OpCodeValues.Throw -> this.Throw cilState
            | _ -> __unreachable__()

        let renewInstructionsInfo cilState =
            if not <| isUnhandledExceptionOrError cilState then
                x.IncrementLevelIfNeeded m offset cilState
        newSts |> List.iter renewInstructionsInfo
        newSts

// ------------------------------------ IExceptionManager implementation ------------------------------------

    interface IInterpreter with
        override x.Raise createException cilState k =
            x.Raise createException cilState k
        override x.NpeOrInvoke cilState ref statement k =
            x.NpeOrInvokeStatementCIL cilState ref statement k
        override x.InvalidProgramException cilState = x.InvalidProgramException cilState
        override x.NullReferenceException cilState = x.NullReferenceException cilState
        override x.ArgumentException cilState = x.ArgumentException cilState
        override x.ArgumentNullException cilState = x.ArgumentNullException cilState
        override x.ArgumentOutOfRangeException cilState = x.ArgumentOutOfRangeException cilState
        override x.IndexOutOfRangeException cilState = x.IndexOutOfRangeException cilState
        override x.ArrayTypeMismatchException cilState = x.ArrayTypeMismatchException cilState
        override x.RankException cilState = x.RankException cilState
        override x.DivideByZeroException cilState = x.DivideByZeroException cilState
        override x.OverflowException cilState = x.OverflowException cilState
        override x.ArithmeticException cilState = x.ArithmeticException cilState
        override x.TypeInitializerException qualifiedTypeName innerException cilState =
            x.TypeInitializerException qualifiedTypeName innerException cilState
        override x.InvalidCastException cilState = x.InvalidCastException cilState
        override x.OutOfMemoryException cilState = x.OutOfMemoryException cilState
        override x.AccessArrayDimension accessor cilState this dim = x.AccessArrayDimension accessor cilState this dim
        override x.AccessArray accessor cilState length index k = x.AccessArray accessor cilState length index k
