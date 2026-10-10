import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsAllocationSource

/-! Remaining source branches of the cursor-aware `extSloads` helper. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def extSloadsBufferFrame (frame : Frame) (ptr : UInt256) (morpho : AccountAddress)
    (slots : List Value) (out : ByteArray) : Frame :=
  { extSloadsSizeFrame frame ptr morpho slots out with
    locals := (extSloadsSizeFrame frame ptr morpho slots out).locals.insert cursorName
      (uint256Value (nextCursor ptr (UInt256.ofNat out.size))) }

def extSloadsDecodedFrame (frame : Frame) (ptr : UInt256) (morpho : AccountAddress)
    (slots : List Value) (out : ByteArray) (values : List Value) : Frame :=
  { extSloadsBufferFrame frame ptr morpho slots out with
    locals := (extSloadsBufferFrame frame ptr morpho slots out).locals.insert decodedName
      (.array values) }

def decodedArraySize (values : List Value) : UInt256 := UInt256.ofNat (32 + 32 * values.length)

def extSloadsFinalCursor (ptr : UInt256) (out : ByteArray) (values : List Value) : UInt256 :=
  nextCursor (nextCursor ptr (UInt256.ofNat out.size)) (decodedArraySize values)

def extSloadsResultFrame (frame : Frame) (ptr : UInt256) (morpho : AccountAddress)
    (slots : List Value) (out : ByteArray) (values : List Value) : Frame :=
  { extSloadsDecodedFrame frame ptr morpho slots out values with
    locals := (extSloadsDecodedFrame frame ptr morpho slots out values).locals.insert
      cursorName (uint256Value (extSloadsFinalCursor ptr out values)) }

theorem extSloadsBodyCallReverts {cfg : Config} {frame : Frame} {evm evm' : State}
    (ptr : UInt256) (morpho : AccountAddress) (slots : List Value) (out : ByteArray)
    (hcall : typedCallViaEVM cfg evm morpho "extSloads" 0 [.array slots]
      (false, evm', out) false) :
    ExecFuncBody cfg (extSloadsFrame frame ptr morpho slots) evm extSloadsFunction.body
      .reverted := by
  apply ExecFuncBody.execBlockRevert
  refine ExecBlock.consNormal (extSloadsRawCall ptr morpho slots false out hcall) ?_
  exact ABlock.start.requireRevert (by
    simp only [evalExpr?, extSloadsCallFrame,
      store_get_ne _ _ (by decide : (returnDataName == callOkName) = false),
      store_get_self, EvalResult.ofOption])

theorem extSloadsBufferPrefix {cfg : Config} {frame : Frame} {evm evm' : State}
    (ptr : UInt256) (morpho : AccountAddress) (slots : List Value) (out : ByteArray)
    (hlookup : lookupCallable? frame.contract allocateFunction.name =
      some allocateFunction.toCallable)
    (hcall : typedCallViaEVM cfg evm morpho "extSloads" 0 [.array slots]
      (true, evm', out) false)
    (hout : out.size < UInt256.size)
    (hfit : allocationFits ptr (UInt256.ofNat out.size))
    {result : ExecResult}
    (htail : ExecBlock cfg (extSloadsBufferFrame frame ptr morpho slots out) evm'
      (extSloadsFunction.body.drop 4) result) :
    ExecBlock cfg (extSloadsFrame frame ptr morpho slots) evm extSloadsFunction.body
      result := by
  refine ExecBlock.consNormal (extSloadsRawCall ptr morpho slots true out hcall) ?_
  apply (ABlock.start.requireStep ?_).run
  · apply (ABlock.start.letStep (returnDataLengthSource (store_get_self _ _ _))).run
    refine ExecBlock.consNormal ?_ htail
    refine allocateCallReturns (cfg := cfg) (evm := evm')
      (frame := extSloadsSizeFrame frame ptr morpho slots out)
      (ptr := ptr) (size := UInt256.ofNat out.size) cursorName ?_ ?_ ?_ hfit
    · simpa only [extSloadsSizeFrame, extSloadsCallFrame, extSloadsFrame] using hlookup
    · simp only [evalExpr?, extSloadsSizeFrame, extSloadsCallFrame, extSloadsFrame,
        store_get_ne _ _ (by decide : (sizeName == cursorName) = false),
        store_get_ne _ _ (by decide : (returnDataName == cursorName) = false),
        store_get_ne _ _ (by decide : (callOkName == cursorName) = false),
        store_get_ne _ _ (by decide : ("morpho" == cursorName) = false),
        store_get_ne _ _ (by decide : ("slot" == cursorName) = false),
        store_get_self, EvalResult.ofOption]
    · simp only [evalExpr?, extSloadsSizeFrame, store_get_self, EvalResult.ofOption,
        uint256Value, UInt256.toNat_ofNat_of_lt hout]
  · simp only [evalExpr?, extSloadsCallFrame,
      store_get_ne _ _ (by decide : (returnDataName == callOkName) = false),
      store_get_self, EvalResult.ofOption]

theorem extSloadsBufferFrame_data (frame : Frame) (ptr : UInt256) (morpho : AccountAddress)
    (slots : List Value) (out : ByteArray) :
    (extSloadsBufferFrame frame ptr morpho slots out).locals.get? returnDataName =
      some (.bytes out) := by
  simp only [extSloadsBufferFrame, extSloadsSizeFrame, extSloadsCallFrame,
    store_get_ne _ _ (by decide : (cursorName == returnDataName) = false),
    store_get_ne _ _ (by decide : (sizeName == returnDataName) = false), store_get_self]

-- LIBRARY CANDIDATE: evaluation of ABI decoding from a local byte string.
theorem abiDecodeSource {cfg : Config} {frame : Frame} {evm : State}
    {name : Ident} {out : ByteArray} {ty : ABIType}
    (hdata : frame.locals.get? name = some (.bytes out)) :
    evalExpr? cfg frame evm (.abiDecode ty (.var name)) =
      match ABI.decodeReturnValueWithMode? cfg.abiDecodeMode ty out with
      | some value => .ok value
      | none => .revert := by
  simp only [evalExpr?, hdata, EvalResult.ofOption, bind, EvalResult.bind]
  cases ABI.decodeReturnValueWithMode? cfg.abiDecodeMode ty out <;> rfl

theorem extSloadsBodyDecodeReverts {cfg : Config} {frame : Frame} {evm evm' : State}
    (ptr : UInt256) (morpho : AccountAddress) (slots : List Value) (out : ByteArray)
    (hlookup : lookupCallable? frame.contract allocateFunction.name =
      some allocateFunction.toCallable)
    (hcall : typedCallViaEVM cfg evm morpho "extSloads" 0 [.array slots]
      (true, evm', out) false)
    (hout : out.size < UInt256.size)
    (hfit : allocationFits ptr (UInt256.ofNat out.size))
    (hdecode : ABI.decodeReturnValueWithMode? cfg.abiDecodeMode
      (.dynamicArray (.elem (.bytes ⟨31, by decide⟩))) out = none) :
    ExecFuncBody cfg (extSloadsFrame frame ptr morpho slots) evm extSloadsFunction.body
      .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply extSloadsBufferPrefix ptr morpho slots out hlookup hcall hout hfit
  apply ExecBlock.consRevert
  apply ExecStmt.letDeclRevert
  rw [abiDecodeSource (extSloadsBufferFrame_data frame ptr morpho slots out), hdecode]

theorem decodedArraySizeSource {cfg : Config} {frame : Frame} {evm : State}
    {values : List Value}
    (hget : frame.locals.get? decodedName = some (.array values))
    (hsize : 32 + 32 * values.length < UInt256.size) :
    evalExpr? cfg frame evm arraySizeExpr = .ok (uint256Value (decodedArraySize values)) := by
  simp only [arraySizeExpr, evalExpr?, hget, readLocalPath?, bind, EvalResult.bind, pure,
    evalBinaryOp?, uint256Value, decodedArraySize, UInt256.toNat_ofNat_of_lt hsize,
    Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]

theorem extSloadsDecodedFrame_cursor {cfg : Config} {frame : Frame} {evm : State}
    (ptr : UInt256) (morpho : AccountAddress) (slots : List Value) (out : ByteArray)
    (values : List Value) :
    evalExpr? cfg (extSloadsDecodedFrame frame ptr morpho slots out values) evm
      (.var cursorName) = .ok (uint256Value (nextCursor ptr (UInt256.ofNat out.size))) := by
  simp only [evalExpr?, extSloadsDecodedFrame, extSloadsBufferFrame,
    store_get_ne _ _ (by decide : (decodedName == cursorName) = false),
    store_get_self, EvalResult.ofOption]

theorem extSloadsBodyArrayReverts {cfg : Config} {frame : Frame} {evm evm' : State}
    (ptr : UInt256) (morpho : AccountAddress) (slots values : List Value) (out : ByteArray)
    (hlookup : lookupCallable? frame.contract allocateFunction.name =
      some allocateFunction.toCallable)
    (hcall : typedCallViaEVM cfg evm morpho "extSloads" 0 [.array slots]
      (true, evm', out) false)
    (hout : out.size < UInt256.size)
    (hfit : allocationFits ptr (UInt256.ofNat out.size))
    (hdecode : ABI.decodeReturnValueWithMode? cfg.abiDecodeMode
      (.dynamicArray (.elem (.bytes ⟨31, by decide⟩))) out = some (.array values))
    (hsize : 32 + 32 * values.length < UInt256.size)
    (harray : ¬ allocationFits (nextCursor ptr (UInt256.ofNat out.size))
      (decodedArraySize values)) :
    ExecFuncBody cfg (extSloadsFrame frame ptr morpho slots) evm extSloadsFunction.body
      .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply extSloadsBufferPrefix ptr morpho slots out hlookup hcall hout hfit
  apply (ABlock.start.letStep (by
    rw [abiDecodeSource (extSloadsBufferFrame_data frame ptr morpho slots out), hdecode])).run
  apply ExecBlock.consRevert
  refine allocateCallReverts (cfg := cfg) (evm := evm')
    (frame := extSloadsDecodedFrame frame ptr morpho slots out values)
    cursorName ?_ (extSloadsDecodedFrame_cursor ptr morpho slots out values)
    (decodedArraySizeSource (store_get_self _ _ _) hsize) harray
  simpa only [extSloadsDecodedFrame, extSloadsBufferFrame, extSloadsSizeFrame,
    extSloadsCallFrame, extSloadsFrame] using hlookup

theorem extSloadsBodyReturns {cfg : Config} {frame : Frame} {evm evm' : State}
    (ptr : UInt256) (morpho : AccountAddress) (slots values : List Value) (out : ByteArray)
    (hlookup : lookupCallable? frame.contract allocateFunction.name =
      some allocateFunction.toCallable)
    (hcall : typedCallViaEVM cfg evm morpho "extSloads" 0 [.array slots]
      (true, evm', out) false)
    (hout : out.size < UInt256.size)
    (hfit : allocationFits ptr (UInt256.ofNat out.size))
    (hdecode : ABI.decodeReturnValueWithMode? cfg.abiDecodeMode
      (.dynamicArray (.elem (.bytes ⟨31, by decide⟩))) out = some (.array values))
    (hsize : 32 + 32 * values.length < UInt256.size)
    (harray : allocationFits (nextCursor ptr (UInt256.ofNat out.size))
      (decodedArraySize values)) :
    ExecFuncBody cfg (extSloadsFrame frame ptr morpho slots) evm extSloadsFunction.body
      (.returned (extSloadsResultFrame frame ptr morpho slots out values) evm'
        (some [.array values, uint256Value (extSloadsFinalCursor ptr out values)])) := by
  apply ExecFuncBody.execBlockRet
  apply extSloadsBufferPrefix ptr morpho slots out hlookup hcall hout hfit
  apply (ABlock.start.letStep (by
    rw [abiDecodeSource (extSloadsBufferFrame_data frame ptr morpho slots out), hdecode])).run
  refine ExecBlock.consNormal (solm' := extSloadsResultFrame frame ptr morpho slots out values)
    (evm' := evm') ?_ ?_
  · refine allocateCallReturns (cfg := cfg) (evm := evm')
      (frame := extSloadsDecodedFrame frame ptr morpho slots out values)
      cursorName ?_ (extSloadsDecodedFrame_cursor ptr morpho slots out values)
      (decodedArraySizeSource (store_get_self _ _ _) hsize) harray
    simpa only [extSloadsDecodedFrame, extSloadsBufferFrame, extSloadsSizeFrame,
      extSloadsCallFrame, extSloadsFrame] using hlookup
  · apply ExecBlock.consReturn
    apply ExecStmt.return
    simp only [evalExprs?, evalExpr?, extSloadsResultFrame, extSloadsDecodedFrame,
      store_get_ne _ _ (by decide : (cursorName == decodedName) = false),
      store_get_self, EvalResult.ofOption, bind, EvalResult.bind, pure]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
