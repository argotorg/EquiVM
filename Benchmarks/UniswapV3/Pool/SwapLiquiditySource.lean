import Benchmarks.UniswapV3.Pool.SwapCrossFlags
import Benchmarks.UniswapV3.Pool.LiquidityDeltaSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapLiquidityNet (zeroForOne : Bool) (net : Int) : Int :=
  if zeroForOne then normalizeInt (.sint ⟨128, by decide⟩) (0 - net) else net

def swapLiquidityRaw (zeroForOne : Bool) (net : Int) : UInt256 :=
  if zeroForOne then UInt256.sub ⟨0⟩ (EVM.wordOfInt net) else EVM.wordOfInt net

def swapLiquidityNegFrame (frame : Frame) (zeroForOne : Bool) (net : Int) : Frame :=
  if zeroForOne then
    {frame with locals := frame.locals.insert "liquidityNet" (.int (swapLiquidityNet true net))}
  else frame

def swapLiquidityValue (s : SwapStateData) (zeroForOne : Bool) (net : Int) : Int :=
  liquidityDeltaResult (Int.ofNat s.liquidity.toNat) (swapLiquidityNet zeroForOne net)

def swapLiquidityState (s : SwapStateData) (zeroForOne : Bool) (net : Int) : SwapStateData :=
  {s with liquidity := EVM.wordOfInt (swapLiquidityValue s zeroForOne net)}

def swapLiquidityCallFrame (frame : Frame) (s : SwapStateData)
    (zeroForOne : Bool) (net : Int) : Frame :=
  resumeAfterInternalCall (swapLiquidityNegFrame frame zeroForOne net) "__c14"
    (some [.int (swapLiquidityValue s zeroForOne net)])

def swapLiquidityFrame (frame : Frame) (s : SwapStateData)
    (zeroForOne : Bool) (net : Int) : Frame :=
  swapStateFrame (swapLiquidityCallFrame frame s zeroForOne net)
    (swapLiquidityState s zeroForOne net)

def swapLiquidityArgs : List Expr :=
  [.field (.var "state") "liquidity", .var "liquidityNet"]

theorem swapLiquidityCallStmt : swapInitializedBody[3]! =
    .internalCall "LiquidityMath_addDelta" swapLiquidityArgs "__c14" := rfl

theorem swapLiquidityNegSource {frame : Frame} {evm : EVM.State}
    (zeroForOne : Bool) (net : Int)
    (hz : frame.locals.get? "zeroForOne" = some (.bool zeroForOne))
    (hn : frame.locals.get? "liquidityNet" = some (.int net)) :
    ExecStmt config frame evm swapInitializedBody[2]!
      (.ok (swapLiquidityNegFrame frame zeroForOne net) evm) := by
  have ez := evalExpr_var_get (cfg := config) (evm := evm) hz
  cases zeroForOne
  · exact ExecStmt.iteFalse ez .nil
  · apply ExecStmt.iteTrue ez
    apply ExecBlock.consNormal (ExecStmt.assign _ (assignLocalVarBase_frame hn)) .nil
    have en := evalExpr_var_get (cfg := config) (evm := evm) hn
    simp only [evalExpr?, en, evalBinaryOp?, castValue?, EvalResult.ofOption,
      bind, EvalResult.bind, pure]
    rfl

theorem evalSwapLiquidityArgs {frame : Frame} {evm : EVM.State}
    (s : SwapStateData) (net : Int)
    (hs : frame.locals.get? "state" = some s.value)
    (hn : frame.locals.get? "liquidityNet" = some (.int net)) :
    evalExprs? config frame evm swapLiquidityArgs =
      .ok [.int (Int.ofNat s.liquidity.toNat), .int net] := by
  have es := evalExpr_structField (name := "liquidity")
    (evalExpr_var_get (cfg := config) (evm := evm) hs) rfl
  have en := evalExpr_var_get (cfg := config) (evm := evm) hn
  simp only [swapLiquidityArgs, evalExprs?, es, en, bind, EvalResult.bind, pure]

theorem swapLiquidityValue_word (s : SwapStateData) (zeroForOne : Bool) (net : Int) :
    Int.ofNat (EVM.wordOfInt (swapLiquidityValue s zeroForOne net)).toNat =
      swapLiquidityValue s zeroForOne net := by
  have hb := liquidityDeltaResult_bounds (Int.ofNat s.liquidity.toNat)
    (swapLiquidityNet zeroForOne net)
  change 0 ≤ swapLiquidityValue s zeroForOne net ∧
    swapLiquidityValue s zeroForOne net < 2 ^ 128 at hb
  rw [wordOfInt_mod, Int.emod_eq_of_lt hb.1 (by have := hb.2; omega)]
  exact Int.toNat_of_nonneg hb.1

theorem swapLiquidityAssignValueSource {frame : Frame} {evm : EVM.State}
    (s : SwapStateData) (value : UInt256)
    (hs : frame.locals.get? "state" = some s.value)
    (hr : frame.locals.get? "__c14" = some (.int (Int.ofNat value.toNat))) :
    ExecStmt config frame evm swapInitializedBody[4]!
      (.ok (swapStateFrame frame {s with liquidity := value}) evm) :=
  ExecStmt.assign (evalExpr_var_get hr) (assignLocalField_frame hs rfl rfl)

theorem SwapStateData.Fits.liquidity {s : SwapStateData} (hs : s.Fits) (value : UInt256)
    (hv : value.toNat < 2 ^ 128) : SwapStateData.Fits {s with liquidity := value} :=
  ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, hv⟩

theorem swapLiquidityState_fits (s : SwapStateData) (zeroForOne : Bool) (net : Int)
    (hs : s.Fits) : (swapLiquidityState s zeroForOne net).Fits := by
  apply hs.liquidity
  have hb := (liquidityDeltaResult_bounds (Int.ofNat s.liquidity.toNat)
    (swapLiquidityNet zeroForOne net)).2
  change swapLiquidityValue s zeroForOne net < 2 ^ 128 at hb
  rw [← swapLiquidityValue_word s zeroForOne net, Int.ofNat_eq_natCast] at hb
  exact_mod_cast hb

theorem swapLiquidityRaw_normalize (zeroForOne : Bool) (net : Int)
    (hn : -(2 ^ 127 : Int) ≤ net ∧ net < 2 ^ 127) :
    normalizeInt (.sint ⟨128, by decide⟩)
      (Int.ofNat (swapLiquidityRaw zeroForOne net).toNat) =
      swapLiquidityNet zeroForOne net := by
  cases zeroForOne
  · exact (normalizeInt_wordOfInt (.sint ⟨128, by decide⟩) net).trans
      (normalizeSint_eq_self ⟨128, by decide⟩ _ hn.1 hn.2)
  · dsimp only [swapLiquidityRaw, swapLiquidityNet, if_true]
    rw [show (⟨0⟩ : UInt256) = EVM.wordOfInt 0 by rfl, ← wordOfInt_sub]
    exact normalizeInt_wordOfInt (.sint ⟨128, by decide⟩) (0 - net)

theorem swapLiquidityNegFrame_get (frame : Frame) (zeroForOne : Bool) (net : Int)
    (name : Ident) (hn : name ≠ "liquidityNet") :
    (swapLiquidityNegFrame frame zeroForOne net).locals.get? name = frame.locals.get? name := by
  cases zeroForOne
  · rfl
  · simp only [swapLiquidityNegFrame, if_true, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, beq_iff_eq, Ne.symm hn, if_false]

theorem swapLiquidityNegFrame_net (frame : Frame) (zeroForOne : Bool) (net : Int)
    (hn : frame.locals.get? "liquidityNet" = some (.int net)) :
    (swapLiquidityNegFrame frame zeroForOne net).locals.get? "liquidityNet" =
      some (.int (swapLiquidityNet zeroForOne net)) := by
  cases zeroForOne
  · exact hn
  · exact Std.HashMap.getElem?_insert_self

theorem swapLiquidityAssignSource {frame : Frame} {evm : EVM.State}
    (s : SwapStateData) (zeroForOne : Bool) (net : Int)
    (hs : frame.locals.get? "state" = some s.value) :
    ExecStmt config (swapLiquidityCallFrame frame s zeroForOne net) evm swapInitializedBody[4]!
      (.ok (swapLiquidityFrame frame s zeroForOne net) evm) := by
  have hs' := (resumeAfterInternalCall_get (swapLiquidityNegFrame frame zeroForOne net)
    "__c14" "state" (some [.int (swapLiquidityValue s zeroForOne net)]) (by decide)).trans
    ((swapLiquidityNegFrame_get frame zeroForOne net "state" (by decide)).trans hs)
  apply swapLiquidityAssignValueSource s (EVM.wordOfInt (swapLiquidityValue s zeroForOne net)) hs'
  rw [swapLiquidityValue_word]
  exact Std.HashMap.getElem?_insert_self

theorem swapLiquidityFrame_parts (frame : Frame) (s : SwapStateData)
    (zeroForOne : Bool) (net : Int) :
    (swapLiquidityFrame frame s zeroForOne net).contract = frame.contract ∧
    (swapLiquidityFrame frame s zeroForOne net).immutables = frame.immutables := by
  cases zeroForOne <;> exact ⟨rfl, rfl⟩

theorem swapLiquidityFrame_state (frame : Frame) (s : SwapStateData)
    (zeroForOne : Bool) (net : Int) :
    (swapLiquidityFrame frame s zeroForOne net).locals.get? "state" =
      some (swapLiquidityState s zeroForOne net).value :=
  Std.HashMap.getElem?_insert_self

theorem swapLiquidityFrame_get (frame : Frame) (s : SwapStateData)
    (zeroForOne : Bool) (net : Int) (name : Ident)
    (hn : name ≠ "state") (hc : name ≠ "__c14") (hl : name ≠ "liquidityNet") :
    (swapLiquidityFrame frame s zeroForOne net).locals.get? name = frame.locals.get? name := by
  unfold swapLiquidityFrame swapStateFrame
  simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, beq_iff_eq,
    Ne.symm hn, if_false]
  exact (resumeAfterInternalCall_get (swapLiquidityNegFrame frame zeroForOne net) "__c14" name
    (some [.int (swapLiquidityValue s zeroForOne net)]) hc).trans
    (swapLiquidityNegFrame_get frame zeroForOne net name hl)

end Benchmarks.UniswapV3.Pool
