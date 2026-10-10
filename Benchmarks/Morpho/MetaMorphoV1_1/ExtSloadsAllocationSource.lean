import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsAllocationSyntax
import Benchmarks.Morpho.MetaMorphoV1_1.AllocationSource

/-! The return-buffer reservation uses the actual external-call result. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem extSloadsFunction_lookup :
    lookupCallable? contract extSloadsFunction.name = some extSloadsFunction.toCallable := by
  rfl

def extSloadsFrame (frame : Frame) (ptr : UInt256) (morpho : AccountAddress)
    (slots : List Value) : Frame :=
  { frame with
    locals := (((∅ : Store).insert cursorName (uint256Value ptr)).insert "slot"
      (.array slots)).insert "morpho" (.address morpho) }

def extSloadsCallFrame (frame : Frame) (ptr : UInt256) (morpho : AccountAddress)
    (slots : List Value) (ok : Bool) (out : ByteArray) : Frame :=
  { extSloadsFrame frame ptr morpho slots with
    locals := ((extSloadsFrame frame ptr morpho slots).locals.insert callOkName
      (.bool ok)).insert returnDataName (.bytes out) }

def extSloadsSizeFrame (frame : Frame) (ptr : UInt256) (morpho : AccountAddress)
    (slots : List Value) (out : ByteArray) : Frame :=
  { extSloadsCallFrame frame ptr morpho slots true out with
    locals := (extSloadsCallFrame frame ptr morpho slots true out).locals.insert sizeName
      (.int (Int.ofNat out.size)) }

theorem extSloadsFrame_target (cfg : Config) (frame : Frame) (evm : State)
    (ptr : UInt256) (morpho : AccountAddress) (slots : List Value) :
    evalExpr? cfg (extSloadsFrame frame ptr morpho slots) evm (.var "morpho") =
      .ok (.address morpho) := by
  simp only [evalExpr?, extSloadsFrame, store_get_self, EvalResult.ofOption]

theorem extSloadsFrame_args (cfg : Config) (frame : Frame) (evm : State)
    (ptr : UInt256) (morpho : AccountAddress) (slots : List Value) :
    evalExprList? cfg (extSloadsFrame frame ptr morpho slots) evm [.var "slot"] =
      .ok [.array slots] := by
  simp only [evalExprList?, evalExpr?, extSloadsFrame,
    store_get_ne _ _ (by decide : ("morpho" == "slot") = false), store_get_self,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem extSloadsRawCall {cfg : Config} {frame : Frame} {evm evm' : State}
    (ptr : UInt256) (morpho : AccountAddress) (slots : List Value)
    (ok : Bool) (out : ByteArray)
    (hcall : typedCallViaEVM cfg evm morpho "extSloads" 0 [.array slots]
      (ok, evm', out) false) :
    ExecStmt cfg (extSloadsFrame frame ptr morpho slots) evm
      (.lowLevelCall (.var "morpho") (.intLit 0)
        (.abiEncodeCall "extSloads" [.var "slot"]) callOkName returnDataName false)
      (.ok (extSloadsCallFrame frame ptr morpho slots ok out) evm') := by
  obtain ⟨input, hencode, hraw⟩ := hcall
  have heth : evalExpr? cfg (extSloadsFrame frame ptr morpho slots) evm (.intLit 0) =
      .ok (.int 0) := by simp only [evalExpr?, pure]
  have hdata : evalExpr? cfg (extSloadsFrame frame ptr morpho slots) evm
      (.abiEncodeCall "extSloads" [.var "slot"]) = .ok (.bytes input) := by
    rw [evalExpr?, extSloadsFrame_args]
    simp only [bind, EvalResult.bind, hencode, EvalResult.ofOption, pure]
  rw [← evm_address_of_address_toNat morpho] at hraw
  cases ok
  · exact ExecStmt.lowLevelCallFailure
      (extSloadsFrame_target cfg frame evm ptr morpho slots) heth hdata hraw
  · exact ExecStmt.lowLevelCallSuccess
      (extSloadsFrame_target cfg frame evm ptr morpho slots) heth hdata hraw

theorem returnDataLengthSource {cfg : Config} {frame : Frame} {evm : State} {out : ByteArray}
    (hget : frame.locals.get? returnDataName = some (.bytes out)) :
    evalExpr? cfg frame evm returnSizeExpr = .ok (.int (Int.ofNat out.size)) := by
  simp only [returnSizeExpr, evalExpr?, hget, readLocalPath?, bind, EvalResult.bind, pure]

theorem reserveReturnBufferReverts {cfg : Config} {frame : Frame} {evm : State}
    {ptr size : UInt256}
    (hlookup : lookupCallable? frame.contract allocateFunction.name =
      some allocateFunction.toCallable)
    (hptr : frame.locals.get? cursorName = some (uint256Value ptr))
    (hsize : frame.locals.get? sizeName = some (uint256Value size))
    (hfit : ¬ allocationFits ptr size) :
    ExecStmt cfg frame evm reserveReturnBuffer .reverted := by
  exact allocateCallReverts cursorName hlookup
    (by simp only [evalExpr?, hptr, EvalResult.ofOption])
    (by simp only [evalExpr?, hsize, EvalResult.ofOption]) hfit

theorem extSloadsBodyBufferReverts {cfg : Config} {frame : Frame} {evm evm' : State}
    (ptr : UInt256) (morpho : AccountAddress) (slots : List Value) (out : ByteArray)
    (hlookup : lookupCallable? frame.contract allocateFunction.name =
      some allocateFunction.toCallable)
    (hcall : typedCallViaEVM cfg evm morpho "extSloads" 0 [.array slots]
      (true, evm', out) false)
    (hout : out.size < UInt256.size)
    (hfit : ¬ allocationFits ptr (UInt256.ofNat out.size)) :
    ExecFuncBody cfg (extSloadsFrame frame ptr morpho slots) evm extSloadsFunction.body
      .reverted := by
  apply ExecFuncBody.execBlockRevert
  refine ExecBlock.consNormal (extSloadsRawCall ptr morpho slots true out hcall) ?_
  apply (ABlock.start.requireStep ?_).run
  · apply (ABlock.start.letStep (returnDataLengthSource (store_get_self _ _ _))).run
    apply ExecBlock.consRevert
    refine reserveReturnBufferReverts (cfg := cfg) (evm := evm')
      (frame := extSloadsSizeFrame frame ptr morpho slots out)
      (ptr := ptr) (size := UInt256.ofNat out.size) ?_ ?_ ?_ hfit
    · simpa only [extSloadsSizeFrame, extSloadsCallFrame, extSloadsFrame] using hlookup
    · simp only [extSloadsSizeFrame, extSloadsCallFrame, extSloadsFrame,
        store_get_ne _ _ (by decide : (sizeName == cursorName) = false),
        store_get_ne _ _ (by decide : (returnDataName == cursorName) = false),
        store_get_ne _ _ (by decide : (callOkName == cursorName) = false),
        store_get_ne _ _ (by decide : ("morpho" == cursorName) = false),
        store_get_ne _ _ (by decide : ("slot" == cursorName) = false), store_get_self]
    · simpa only [uint256Value, UInt256.toNat_ofNat_of_lt hout] using
        (store_get_self (extSloadsCallFrame frame ptr morpho slots true out).locals
          sizeName (.int (Int.ofNat out.size)))
  · simp only [evalExpr?, extSloadsCallFrame,
      store_get_ne _ _ (by decide : (returnDataName == callOkName) = false),
      store_get_self, EvalResult.ofOption]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
