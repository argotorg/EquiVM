import Benchmarks.CompoundIII.Comet.ConstructorScaleWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def constructorScaleExpr : Expr :=
  .cast (.cast (.binary .exp (.intLit 10) (.var "decimals_"))
    (.elem (.int (.uint ⟨256, by decide⟩)))) (.elem (.int (.uint ⟨64, by decide⟩)))

def constructorScaleImms (c : ConstructorConfig) (w : UInt256) : Store :=
  let imms := (constructorInitialImms c w).insert "baseScale" (.int (Int.ofNat (10 ^ w.toNat)))
  imms.insert "trackingIndexScale" (.int (Int.ofNat c.trackingIndexScale.val))

def constructorSourceScale (c : ConstructorConfig) (w feed : UInt256) : Frame :=
  { constructorSourceInitialImms c w feed with immutables := constructorScaleImms c w }

theorem constructorScaleExpr_eval {c : ConstructorConfig} {w feed : UInt256} {evm : EVM.State}
    (hw : w.toNat ≤ 18) :
    evalExpr? config (constructorSourceInitialImms c w feed) evm constructorScaleExpr =
      .ok (.int (Int.ofNat (10 ^ w.toNat))) := by
  have hd : evalExpr? config (constructorSourceInitialImms c w feed) evm (.var "decimals_") =
      .ok (.int (Int.ofNat w.toNat)) := by
    simp only [evalExpr?, constructorSourceInitialImms, constructorSourcePriceFeed,
      constructorSourceDecimals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      EvalResult.ofOption]
    rfl
  have hp : evalExpr? config (constructorSourceInitialImms c w feed) evm
      (.binary .exp (.intLit 10) (.var "decimals_")) = .ok (.int (Int.ofNat (10 ^ w.toNat))) := by
    simp only [evalExpr?, hd, pure, bind, EvalResult.bind, evalBinaryOp?]
    simp
  have hb := constructorScale_bound hw
  have hn64 : normalizeInt (.uint ⟨64, by decide⟩) (Int.ofNat (10 ^ w.toNat)) =
      Int.ofNat (10 ^ w.toNat) :=
    normalizeInt_uint_eq_self _ _ (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hb)
  have hn256 : normalizeInt (.uint ⟨256, by decide⟩) (Int.ofNat (10 ^ w.toNat)) =
      Int.ofNat (10 ^ w.toNat) :=
    normalizeInt_uint_eq_self _ _ (Int.natCast_nonneg _)
      (Int.ofNat_lt.mpr (lt_trans hb (by decide)))
  have h256 := evalExpr_cast_int (intType := .uint ⟨256, by decide⟩) hp
  rw [hn256] at h256
  have h64 := evalExpr_cast_int (intType := .uint ⟨64, by decide⟩) h256
  rw [hn64] at h64
  exact h64

theorem constructorSourceScale_exec {c : ConstructorConfig} {w feed : UInt256}
    {evm evm' : EVM.State} (hw : w.toNat ≤ 18)
    (hp : ExecBlock config (constructorSourceEntry c) evm (contract.ctor.body.take 16)
      (.ok (constructorSourceInitialImms c w feed) evm')) :
    ExecBlock config (constructorSourceEntry c) evm (contract.ctor.body.take 18)
      (.ok (constructorSourceScale c w feed) evm') := by
  change ExecBlock config _ _ (contract.ctor.body.take 16 ++
    [.setImmutable "baseScale" constructorScaleExpr,
      .setImmutable "trackingIndexScale" (.field (.var "config") "trackingIndexScale")]) _
  apply execBlockAppendOk hp
  refine ExecBlock.consNormal (ExecStmt.setImmutable (value := .int (Int.ofNat (10 ^ w.toNat)))
    (ty := .int (.uint ⟨256, by decide⟩)) (constructorScaleExpr_eval hw) rfl (by
      have hb := constructorScale_bound hw
      simp only [elemValueFits, decide_eq_true_eq]
      exact ⟨Int.natCast_nonneg _,
        Int.ofNat_lt.mpr (lt_trans hb (by decide : (2 : Nat)^64 < 2^256))⟩)) ?_
  refine ExecBlock.consNormal (ExecStmt.setImmutable
    (value := .int (Int.ofNat c.trackingIndexScale.val)) (ty := .int (.uint ⟨256, by decide⟩))
    ?_ rfl (by
      have hb := c.trackingIndexScale.isLt
      simp [elemValueFits]
      omega)) .nil
  apply constructorSourceField (c := c) ?_ rfl
  simp only [constructorSourceInitialImms, constructorSourcePriceFeed, constructorSourceDecimals,
    constructorSourceConfig, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  rfl

theorem constructorSource_scaleGuard {c : ConstructorConfig} {w feed : UInt256} {evm : EVM.State}
    (hw : w.toNat ≤ 18) :
    evalExpr? config (constructorSourceScale c w feed) evm
      (.binary .ge (.immutable "baseScale") (.intLit 1000000)) =
      .ok (.bool (decide (6 ≤ w.toNat))) := by
  have hs : (constructorSourceScale c w feed).immutables.get? "baseScale" =
      some (.int (Int.ofNat (10 ^ w.toNat))) := by
    simp only [constructorSourceScale, constructorScaleImms, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert]
    rfl
  simp only [evalExpr?, hs, EvalResult.ofOption, pure, bind, EvalResult.bind, evalBinaryOp?]
  change EvalResult.ok (Value.bool (decide ((1000000 : Int) ≤ Int.ofNat (10 ^ w.toNat)))) = _
  have he : ((1000000 : Int) ≤ Int.ofNat (10 ^ w.toNat)) ↔ 6 ≤ w.toNat := by
    exact Int.ofNat_le.trans (constructorScale_min hw)
  simp only [he]

theorem constructorSourceScaleChecked_exec {c : ConstructorConfig} {w feed : UInt256}
    {evm evm' : EVM.State} (hw : w.toNat ≤ 18) (hlo : 6 ≤ w.toNat)
    (hp : ExecBlock config (constructorSourceEntry c) evm (contract.ctor.body.take 16)
      (.ok (constructorSourceInitialImms c w feed) evm')) :
    ExecBlock config (constructorSourceEntry c) evm (contract.ctor.body.take 19)
      (.ok (constructorSourceScale c w feed) evm') := by
  have hd := constructorSourceScale_exec hw hp
  change ExecBlock config _ _ (contract.ctor.body.take 18 ++
    [.require (.binary .ge (.immutable "baseScale") (.intLit 1000000))]) _
  apply execBlockAppendOk hd
  exact .consNormal (.requireTrue (by
    rw [constructorSource_scaleGuard hw, decide_eq_true hlo])) .nil

theorem constructorSourceScaleChecked_revert {c : ConstructorConfig} {w feed : UInt256}
    {evm evm' : EVM.State} (hw : w.toNat ≤ 18) (hlo : ¬ 6 ≤ w.toNat)
    (hp : ExecBlock config (constructorSourceEntry c) evm (contract.ctor.body.take 16)
      (.ok (constructorSourceInitialImms c w feed) evm')) :
    ExecBlock config (constructorSourceEntry c) evm contract.ctor.body .reverted := by
  have hd := constructorSourceScale_exec hw hp
  rw [← List.take_append_drop 18 contract.ctor.body]
  apply execBlockAppendOk hd
  exact .consRevert (.requireFalse (by
    rw [constructorSource_scaleGuard hw, decide_eq_false hlo]))

end Benchmarks.CompoundIII.Comet
