import Benchmarks.UniswapV3.Pool.AmountDeltaPrefix
import Benchmarks.UniswapV3.Pool.AmountDeltaBounds

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def amount0DeltaNumeratorFrame (imms : Store) (a : AmountDeltaArgs) : Frame :=
  let locals := (amountDeltaSortedFrame imms false a).locals.insert "numerator1"
    (.int (Int.ofNat (amountDeltaNumerator a).toNat))
  {amountDeltaSortedFrame imms false a with locals := locals}

def amount0DeltaInputsFrame (imms : Store) (a : AmountDeltaArgs) : Frame :=
  let locals := (amount0DeltaNumeratorFrame imms a).locals.insert "numerator2"
    (.int (Int.ofNat (amountDeltaDifference a).toNat))
  {amount0DeltaNumeratorFrame imms a with locals := locals}

def amount0DeltaZeroFrame (imms : Store) (a : AmountDeltaArgs) : Frame :=
  let locals := (amount0DeltaInputsFrame imms a).locals.insert "__cond5" (.int 0)
  {amount0DeltaInputsFrame imms a with locals := locals}

theorem amount0DeltaInputsGet (imms : Store) (a : AmountDeltaArgs) :
    (amount0DeltaInputsFrame imms a).locals.get? "sqrtRatioAX96" =
        some (.int (Int.ofNat (amountDeltaLower a).toNat)) ∧
      (amount0DeltaInputsFrame imms a).locals.get? "sqrtRatioBX96" =
        some (.int (Int.ofNat (amountDeltaUpper a).toNat)) ∧
      (amount0DeltaInputsFrame imms a).locals.get? "numerator1" =
        some (.int (Int.ofNat (amountDeltaNumerator a).toNat)) ∧
      (amount0DeltaInputsFrame imms a).locals.get? "numerator2" =
        some (.int (Int.ofNat (amountDeltaDifference a).toNat)) ∧
      (amount0DeltaInputsFrame imms a).locals.get? "roundUp" = some (.bool a.roundUp) := by
  obtain ⟨ha, hb, _, hr⟩ := amountDeltaSortedGet imms false a
  simp only [amount0DeltaInputsFrame, amount0DeltaNumeratorFrame,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at ha hb hr ⊢
  exact ⟨ha, hb, rfl, rfl, hr⟩

theorem amount0DeltaZeroFrame_eq (imms : Store) (a : AmountDeltaArgs) :
    amount0DeltaZeroFrame imms a =
      {contract := contract, locals := (amount0DeltaZeroFrame imms a).locals, immutables := imms} := by
  unfold amount0DeltaZeroFrame amount0DeltaInputsFrame amount0DeltaNumeratorFrame
    amountDeltaSortedFrame
  split_ifs <;> rfl

theorem amount0DeltaNumeratorSource (imms : Store) (evm : EVM.State) (a : AmountDeltaArgs)
    (hfit : a.Fits) :
    ExecStmt config (amountDeltaSortedFrame imms false a) evm (amountDeltaFunction false).body[2]!
      (.ok (amount0DeltaNumeratorFrame imms a) evm) := by
  have hl := evalExpr_var_get (cfg := config) (evm := evm)
    (amountDeltaSortedGet imms false a).2.2.1
  have hc := evalExpr_intCast (.uint ⟨256, by decide⟩) hl
  rw [normalizeInt_uint256_word] at hc
  have hs := evalExpr_uintShiftLeft ⟨256, by decide⟩ a.liquidity.toNat 96 hc (by decide)
    (by rw [← amountDeltaNumerator_toNat a hfit]; exact (amountDeltaNumerator a).val.isLt)
  rw [← amountDeltaNumerator_toNat a hfit] at hs
  exact ExecStmt.letDecl hs

theorem amount0DeltaDifferenceSource (imms : Store) (evm : EVM.State) (a : AmountDeltaArgs) :
    ExecStmt config (amount0DeltaNumeratorFrame imms a) evm (amountDeltaFunction false).body[3]!
      (.ok (amount0DeltaInputsFrame imms a) evm) := by
  have ha : evalExpr? config (amount0DeltaNumeratorFrame imms a) evm (.var "sqrtRatioAX96") =
      .ok (.int (Int.ofNat (amountDeltaLower a).toNat)) := evalExpr_var_get (by
        simpa only [amount0DeltaNumeratorFrame, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert] using (amountDeltaSortedGet imms false a).1)
  have hb : evalExpr? config (amount0DeltaNumeratorFrame imms a) evm (.var "sqrtRatioBX96") =
      .ok (.int (Int.ofNat (amountDeltaUpper a).toNat)) := evalExpr_var_get (by
        simpa only [amount0DeltaNumeratorFrame, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert] using (amountDeltaSortedGet imms false a).2.1)
  apply ExecStmt.letDecl
  change evalExpr? config _ evm
    (.cast (.binary .sub (.var "sqrtRatioBX96") (.var "sqrtRatioAX96"))
      (.elem (.int (.uint ⟨160, by decide⟩)))) = _
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?, castValue?, EvalResult.ofOption]
  rw [normalizeUIntInt_mask ⟨160, by decide⟩ _ (UInt256.ofNat (2 ^ 160 - 1)) (by decide),
    wordOfInt_sub, wordOfInt_ofNat_toNat, wordOfInt_ofNat_toNat]
  rfl

theorem amount0DeltaInputsSource (imms : Store) (evm : EVM.State) (a : AmountDeltaArgs)
    (hfit : a.Fits) :
    ExecBlock config (amountDeltaFrame imms a) evm ((amountDeltaFunction false).body.take 4)
      (.ok (amount0DeltaInputsFrame imms a) evm) := by
  change ExecBlock config _ evm ((amountDeltaFunction false).body.take 2 ++
    [(amountDeltaFunction false).body[2]!, (amountDeltaFunction false).body[3]!]) _
  exact execBlock_append_ok (amountDeltaPrefixSource imms evm false a)
    (ExecBlock.consNormal (amount0DeltaNumeratorSource imms evm a hfit)
      (ExecBlock.consNormal (amount0DeltaDifferenceSource imms evm a) ExecBlock.nil))

theorem evalAmount0DeltaGuard (imms : Store) (evm : EVM.State) (a : AmountDeltaArgs) :
    evalExpr? config (amount0DeltaInputsFrame imms a) evm
      (.binary .gt (.var "sqrtRatioAX96") (.intLit 0)) =
      .ok (.bool (decide (0 < (amountDeltaLower a).toNat))) := by
  exact evalExpr_word_gt (b := UInt256.ofNat 0)
    (evalExpr_var_get (amount0DeltaInputsGet imms a).1) (by simp only [evalExpr?, pure]; rfl)

theorem amount0DeltaZeroSource (imms : Store) (evm : EVM.State) (a : AmountDeltaArgs)
    (hfit : a.Fits) (hv : amountDeltaValid false a) :
    ExecBlock config (amountDeltaFrame imms a) evm ((amountDeltaFunction false).body.take 6)
      (.ok (amount0DeltaZeroFrame imms a) evm) := by
  have hp : 0 < (amountDeltaLower a).toNat := hv.resolve_left (by decide)
  have hg := evalAmount0DeltaGuard imms evm a
  rw [decide_eq_true hp] at hg
  change ExecBlock config _ evm ((amountDeltaFunction false).body.take 4 ++
    [(amountDeltaFunction false).body[4]!, (amountDeltaFunction false).body[5]!]) _
  exact execBlock_append_ok (amount0DeltaInputsSource imms evm a hfit)
    (ExecBlock.consNormal (ExecStmt.requireTrue hg)
      (ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ExecBlock.nil))

theorem amount0DeltaReverts (imms : Store) (evm : EVM.State) (a : AmountDeltaArgs)
    (hfit : a.Fits) (hv : ¬amountDeltaValid false a) :
    ExecFuncBody config (amountDeltaFrame imms a) evm (amountDeltaFunction false).body .reverted := by
  have hp : ¬0 < (amountDeltaLower a).toNat := fun h ↦ hv (Or.inr h)
  have hg := evalAmount0DeltaGuard imms evm a
  rw [decide_eq_false hp] at hg
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 4 (amountDeltaFunction false).body]
  exact execBlock_append_ok (amount0DeltaInputsSource imms evm a hfit)
    (ExecBlock.consRevert (ExecStmt.requireFalse hg))

end Benchmarks.UniswapV3.Pool
