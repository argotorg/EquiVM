import Benchmarks.UniswapV3.Pool.SwapAccountingSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapProtocolEnabled (c : SwapCacheData) : Bool := decide (0 < c.feeProtocol.toNat)

def swapProtocolDelta (c : SwapCacheData) (d : SwapIterationData) : UInt256 :=
  UInt256.div d.feeAmount c.feeProtocol

def swapProtocolUpdatedState (c : SwapCacheData) (s : SwapStateData) (d : SwapIterationData) :
    SwapStateData :=
  {s with protocolFee := uint128Word (s.protocolFee + swapProtocolDelta c d)}

def swapProtocolUpdatedData (c : SwapCacheData) (d : SwapIterationData) : SwapIterationData :=
  {d with feeAmount := UInt256.sub d.feeAmount (swapProtocolDelta c d)}

def swapProtocolState (c : SwapCacheData) (s : SwapStateData) (d : SwapIterationData) :
    SwapStateData :=
  if swapProtocolEnabled c then swapProtocolUpdatedState c s d else s

def swapProtocolData (c : SwapCacheData) (d : SwapIterationData) : SwapIterationData :=
  if swapProtocolEnabled c then swapProtocolUpdatedData c d else d

def swapProtocolDeltaFrame (frame : Frame) (c : SwapCacheData) (d : SwapIterationData) : Frame :=
  {frame with
    locals := frame.locals.insert "delta" (.int (Int.ofNat (swapProtocolDelta c d).toNat))}

def swapProtocolFeeFrame (frame : Frame) (c : SwapCacheData) (d : SwapIterationData) : Frame :=
  swapIterationFrame (swapProtocolDeltaFrame frame c d) (swapProtocolUpdatedData c d)

def swapProtocolUpdateFrame (frame : Frame) (c : SwapCacheData) (s : SwapStateData)
    (d : SwapIterationData) : Frame :=
  swapStateFrame (swapProtocolFeeFrame frame c d) (swapProtocolUpdatedState c s d)

def swapProtocolFrame (frame : Frame) (c : SwapCacheData) (s : SwapStateData)
    (d : SwapIterationData) : Frame :=
  if swapProtocolEnabled c then swapProtocolUpdateFrame frame c s d else frame

def swapProtocolBody : List Stmt :=
  match swapLoopBody[14]! with
  | .ite _ yes _ => yes
  | _ => []

theorem swapProtocolUpdateSource {frame : Frame} {evm : EVM.State}
    (c : SwapCacheData) (s : SwapStateData) (d : SwapIterationData)
    (hc : frame.locals.get? "cache" = some c.value)
    (hs : frame.locals.get? "state" = some s.value)
    (hd : frame.locals.get? "step" = some d.value) (hn : 0 < c.feeProtocol.toNat) :
    ExecBlock config frame evm swapProtocolBody
      (.ok (swapProtocolUpdateFrame frame c s d) evm) := by
  have hfee := evalExpr_structField (name := "feeAmount")
    (evalExpr_var_get (cfg := config) (evm := evm) hd) rfl
  have hdivisor := evalExpr_structField (name := "feeProtocol")
    (evalExpr_var_get (cfg := config) (evm := evm) hc) rfl
  have hex0 : ExecStmt config frame evm swapProtocolBody[0]!
      (.ok (swapProtocolDeltaFrame frame c d) evm) :=
    ExecStmt.letDecl (evalExpr_word_div hfee hdivisor (by omega))
  have hstep : (swapProtocolDeltaFrame frame c d).locals.get? "step" = some d.value := by
    simpa only [swapProtocolDeltaFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
      using hd
  have hdelta : (swapProtocolDeltaFrame frame c d).locals.get? "delta" =
      some (.int (Int.ofNat (swapProtocolDelta c d).toNat)) := Std.HashMap.getElem?_insert_self
  have hex1 : ExecStmt config (swapProtocolDeltaFrame frame c d) evm swapProtocolBody[1]!
      (.ok (swapProtocolFeeFrame frame c d) evm) :=
    ExecStmt.assign
      (evalExpr_word_sub (evalExpr_structField (name := "feeAmount")
        (evalExpr_var_get hstep) rfl) (evalExpr_var_get hdelta))
      (assignLocalField_frame hstep rfl rfl)
  have hstate : (swapProtocolFeeFrame frame c d).locals.get? "state" = some s.value := by
    simpa only [swapProtocolFeeFrame, swapIterationFrame, swapProtocolDeltaFrame,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hs
  have hdelta2 : (swapProtocolFeeFrame frame c d).locals.get? "delta" =
      some (.int (Int.ofNat (swapProtocolDelta c d).toNat)) := by
    simpa only [swapProtocolFeeFrame, swapIterationFrame,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hdelta
  have hex2 : ExecStmt config (swapProtocolFeeFrame frame c d) evm swapProtocolBody[2]!
      (.ok (swapProtocolUpdateFrame frame c s d) evm) :=
    ExecStmt.assign
      (evalExpr_uint128AddCast (evalExpr_structField (name := "protocolFee")
        (evalExpr_var_get hstate) rfl) (evalExpr_var_get hdelta2))
      (assignLocalField_frame hstate rfl rfl)
  exact ExecBlock.consNormal hex0 (ExecBlock.consNormal hex1 (ExecBlock.consNormal hex2 .nil))

theorem swapProtocolSource {frame : Frame} {evm : EVM.State}
    (c : SwapCacheData) (s : SwapStateData) (d : SwapIterationData)
    (hc : frame.locals.get? "cache" = some c.value)
    (hs : frame.locals.get? "state" = some s.value)
    (hd : frame.locals.get? "step" = some d.value) :
    ExecStmt config frame evm swapLoopBody[14]! (.ok (swapProtocolFrame frame c s d) evm) := by
  have hfee := evalExpr_structField (name := "feeProtocol")
    (evalExpr_var_get (cfg := config) (evm := evm) hc) rfl
  have hz : evalExpr? config frame evm (.intLit 0) = .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) :=
    by simp only [evalExpr?, pure]; rfl
  have he := evalExpr_word_gt hfee hz
  simp only [u256_zero_toNat] at he
  by_cases h : 0 < c.feeProtocol.toNat
  · rw [swapProtocolFrame, swapProtocolEnabled, if_pos (decide_eq_true h)]
    apply ExecStmt.iteTrue (by simpa only [h, decide_true] using he)
    exact swapProtocolUpdateSource c s d hc hs hd h
  · rw [swapProtocolFrame, swapProtocolEnabled, if_neg (by simpa only [decide_eq_true_eq] using h)]
    exact ExecStmt.iteFalse (by simpa only [h, decide_false] using he) .nil

theorem swapProtocolState_fits (c : SwapCacheData) (s : SwapStateData) (d : SwapIterationData)
    (hs : s.Fits) : (swapProtocolState c s d).Fits := by
  unfold swapProtocolState
  split
  · exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, uint128Word_lt _, hs.2.2.2.2.2⟩
  · exact hs

end Benchmarks.UniswapV3.Pool
