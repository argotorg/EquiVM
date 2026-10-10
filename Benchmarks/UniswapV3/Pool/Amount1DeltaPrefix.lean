import Benchmarks.UniswapV3.Pool.AmountDeltaPrefix
import Benchmarks.UniswapV3.Pool.AmountDeltaBounds

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def amount1DeltaZeroFrame (imms : Store) (a : AmountDeltaArgs) : Frame :=
  let locals := (amountDeltaSortedFrame imms true a).locals.insert "__cond4" (.int 0)
  {amountDeltaSortedFrame imms true a with locals := locals}

def amount1DeltaCallName (roundUp : Bool) : Ident := if roundUp then "__c2" else "__c3"

noncomputable def amount1DeltaCallFrame (imms : Store) (a : AmountDeltaArgs) : Frame :=
  let locals := (amount1DeltaZeroFrame imms a).locals.insert (amount1DeltaCallName a.roundUp)
    (.int (Int.ofNat (amountDeltaMulResult true a).toNat))
  {amount1DeltaZeroFrame imms a with locals := locals}

noncomputable def amount1DeltaReturnFrame (imms : Store) (a : AmountDeltaArgs) : Frame :=
  let locals := (amount1DeltaCallFrame imms a).locals.insert "__cond4"
    (.int (Int.ofNat (amountDeltaMulResult true a).toNat))
  {amount1DeltaCallFrame imms a with locals := locals}

theorem amount1DeltaZeroFrame_eq (imms : Store) (a : AmountDeltaArgs) :
    amount1DeltaZeroFrame imms a =
      {contract := contract, locals := (amount1DeltaZeroFrame imms a).locals, immutables := imms} := by
  unfold amount1DeltaZeroFrame amountDeltaSortedFrame
  split_ifs <;> rfl

theorem amount1DeltaCallFrame_eq (imms : Store) (a : AmountDeltaArgs) :
    amount1DeltaCallFrame imms a =
      {contract := contract, locals := (amount1DeltaCallFrame imms a).locals, immutables := imms} := by
  unfold amount1DeltaCallFrame amount1DeltaZeroFrame amountDeltaSortedFrame
  split_ifs <;> rfl

def amount1DeltaArgs : List Expr :=
  [.var "liquidity", .cast (.binary .sub (.var "sqrtRatioBX96") (.var "sqrtRatioAX96"))
    (.elem (.int (.uint ⟨160, by decide⟩))), .intLit 79228162514264337593543950336]

theorem evalAmount1DeltaArgs (imms : Store) (evm : EVM.State) (a : AmountDeltaArgs) :
    evalExprs? config (amount1DeltaZeroFrame imms a) evm amount1DeltaArgs =
      .ok [.int (Int.ofNat a.liquidity.toNat), .int (Int.ofNat (amountDeltaDifference a).toNat),
        .int (Int.ofNat (UInt256.ofNat (2 ^ 96)).toNat)] := by
  obtain ⟨ha, hb, hl, _⟩ := amountDeltaSortedGet imms true a
  have hget (name : Ident) (value : Value) (hn : name ≠ "__cond4")
      (hv : (amountDeltaSortedFrame imms true a).locals.get? name = some value) :
      (amount1DeltaZeroFrame imms a).locals.get? name = some value := by
    simpa only [amount1DeltaZeroFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, beq_iff_eq, Ne.symm hn, if_false] using hv
  have hea := evalExpr_var_get (cfg := config) (evm := evm) (hget _ _ (by decide) ha)
  have heb := evalExpr_var_get (cfg := config) (evm := evm) (hget _ _ (by decide) hb)
  have hel := evalExpr_var_get (cfg := config) (evm := evm) (hget _ _ (by decide) hl)
  have hd : evalExpr? config (amount1DeltaZeroFrame imms a) evm
      (.cast (.binary .sub (.var "sqrtRatioBX96") (.var "sqrtRatioAX96"))
        (.elem (.int (.uint ⟨160, by decide⟩)))) =
      .ok (.int (Int.ofNat (amountDeltaDifference a).toNat)) := by
    simp only [evalExpr?, hea, heb, bind, EvalResult.bind, evalBinaryOp?, castValue?, EvalResult.ofOption]
    rw [normalizeUIntInt_mask ⟨160, by decide⟩ _ (UInt256.ofNat (2 ^ 160 - 1)) (by decide),
      wordOfInt_sub, wordOfInt_ofNat_toNat, wordOfInt_ofNat_toNat]
    rfl
  simp only [amount1DeltaArgs, evalExprs?, hel, hd, evalExpr?, bind, EvalResult.bind, pure]
  rfl

theorem amount1DeltaZeroSource (imms : Store) (evm : EVM.State) (a : AmountDeltaArgs) :
    ExecBlock config (amountDeltaFrame imms a) evm ((amountDeltaFunction true).body.take 3)
      (.ok (amount1DeltaZeroFrame imms a) evm) := by
  change ExecBlock config (amountDeltaFrame imms a) evm
    ((amountDeltaFunction true).body.take 2 ++ [(amountDeltaFunction true).body[2]!]) _
  exact execBlock_append_ok (amountDeltaPrefixSource imms evm true a)
    (ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ExecBlock.nil)

end Benchmarks.UniswapV3.Pool
