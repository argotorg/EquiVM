import Benchmarks.UniswapV3.Pool.SwapAccountingSource
import Benchmarks.UniswapV3.Pool.FullMathSource
import Benchmarks.UniswapV3.Pool.SourceCallFrames

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapFeeGrowthValue (s : SwapStateData) (d : SwapIterationData) : UInt256 :=
  fullMathResult d.feeAmount (UInt256.ofNat (2 ^ 128)) s.liquidity

def swapFeeGrowthUpdatedState (s : SwapStateData) (d : SwapIterationData) : SwapStateData :=
  {s with feeGrowth := s.feeGrowth + swapFeeGrowthValue s d}

def swapFeeGrowthState (s : SwapStateData) (d : SwapIterationData) : SwapStateData :=
  if 0 < s.liquidity.toNat then swapFeeGrowthUpdatedState s d else s

def swapFeeGrowthCallFrame (frame : Frame) (s : SwapStateData) (d : SwapIterationData) : Frame :=
  resumeAfterInternalCall frame "__c11" (some [.int (Int.ofNat (swapFeeGrowthValue s d).toNat)])

def swapFeeGrowthUpdateFrame (frame : Frame) (s : SwapStateData) (d : SwapIterationData) : Frame :=
  swapStateFrame (swapFeeGrowthCallFrame frame s d) (swapFeeGrowthUpdatedState s d)

def swapFeeGrowthFrame (frame : Frame) (s : SwapStateData) (d : SwapIterationData) : Frame :=
  if 0 < s.liquidity.toNat then swapFeeGrowthUpdateFrame frame s d else frame

def swapFeeGrowthBody : List Stmt :=
  match swapLoopBody[15]! with
  | .ite _ yes _ => yes
  | _ => []

def swapFeeGrowthArgs : List Expr :=
  [.field (.var "step") "feeAmount", .intLit (2 ^ 128), .field (.var "state") "liquidity"]

theorem evalSwapFeeGrowthArgs {frame : Frame} {evm : EVM.State}
    (s : SwapStateData) (d : SwapIterationData)
    (hs : frame.locals.get? "state" = some s.value)
    (hd : frame.locals.get? "step" = some d.value) :
    evalExprs? config frame evm swapFeeGrowthArgs = .ok [.int (Int.ofNat d.feeAmount.toNat),
      .int (Int.ofNat (UInt256.ofNat (2 ^ 128)).toNat), .int (Int.ofNat s.liquidity.toNat)] := by
  have hfee := evalExpr_structField (name := "feeAmount")
    (evalExpr_var_get (cfg := config) (evm := evm) hd) rfl
  have hliq := evalExpr_structField (name := "liquidity")
    (evalExpr_var_get (cfg := config) (evm := evm) hs) rfl
  simp only [swapFeeGrowthArgs, evalExprs?, hfee, hliq, bind, EvalResult.bind, evalExpr?, pure]
  rfl

theorem swapFeeGrowthCallStmt : swapFeeGrowthBody[0]! =
    .internalCall "FullMath_mulDiv" swapFeeGrowthArgs "__c11" := rfl

theorem swapFeeGrowthAssignValueSource {frame : Frame} {evm : EVM.State}
    (s : SwapStateData) (amount : UInt256)
    (hs : frame.locals.get? "state" = some s.value)
    (hr : frame.locals.get? "__c11" = some (.int (Int.ofNat amount.toNat))) :
    ExecStmt config frame evm swapFeeGrowthBody[1]!
      (.ok (swapStateFrame frame {s with feeGrowth := s.feeGrowth + amount}) evm) :=
  ExecStmt.assign (evalExpr_word_add
    (evalExpr_structField (name := "feeGrowthGlobalX128") (evalExpr_var_get hs) rfl)
    (evalExpr_var_get hr)) (assignLocalField_frame hs rfl rfl)

theorem swapFeeGrowthAssignSource {frame : Frame} {evm : EVM.State}
    (s : SwapStateData) (d : SwapIterationData)
    (hs : frame.locals.get? "state" = some s.value) :
    ExecStmt config (swapFeeGrowthCallFrame frame s d) evm swapFeeGrowthBody[1]!
      (.ok (swapFeeGrowthUpdateFrame frame s d) evm) := by
  have hstate := (resumeAfterInternalCall_get frame "__c11" "state"
    (some [.int (Int.ofNat (swapFeeGrowthValue s d).toNat)]) (by decide)).trans hs
  have hresult : (swapFeeGrowthCallFrame frame s d).locals.get? "__c11" =
      some (.int (Int.ofNat (swapFeeGrowthValue s d).toNat)) := Std.HashMap.getElem?_insert_self
  exact swapFeeGrowthAssignValueSource s (swapFeeGrowthValue s d) hstate hresult

theorem evalSwapFeeGrowthGuard {frame : Frame} {evm : EVM.State} (s : SwapStateData)
    (hs : frame.locals.get? "state" = some s.value) :
    evalExpr? config frame evm (.binary .gt (.field (.var "state") "liquidity") (.intLit 0)) =
      .ok (.bool (decide (0 < s.liquidity.toNat))) := by
  have hliq := evalExpr_structField (name := "liquidity")
    (evalExpr_var_get (cfg := config) (evm := evm) hs) rfl
  have hz : evalExpr? config frame evm (.intLit 0) = .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) :=
    by simp only [evalExpr?, pure]; rfl
  simpa only [u256_zero_toNat] using evalExpr_word_gt hliq hz

theorem SwapStateData.Fits.feeGrowth {s : SwapStateData} (hs : s.Fits) (value : UInt256) :
    SwapStateData.Fits {s with feeGrowth := value} :=
  ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩

theorem swapFeeGrowthState_fits (s : SwapStateData) (d : SwapIterationData) (hs : s.Fits) :
    (swapFeeGrowthState s d).Fits := by
  unfold swapFeeGrowthState
  split
  · exact SwapStateData.Fits.feeGrowth hs (s.feeGrowth + swapFeeGrowthValue s d)
  · exact hs

end Benchmarks.UniswapV3.Pool
