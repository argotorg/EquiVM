import Benchmarks.CompoundIII.Comet.ConstructorChecks

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem constructorSource_baseMin (c : ConstructorConfig) (w : UInt256) (evm : EVM.State) :
    evalExpr? config (constructorSourceDecimals c w) evm
      (.field (.var "config") "baseMinForRewards") =
      .ok (.int (Int.ofNat c.baseMinForRewards.val)) := by
  simp only [evalExpr?, constructorSourceDecimals, constructorSourceConfig,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption,
    bind, EvalResult.bind]
  rfl

theorem constructorSource_baseMinGuard (c : ConstructorConfig) (w : UInt256) (evm : EVM.State) :
    evalExpr? config (constructorSourceDecimals c w) evm
      (.binary .ne (.field (.var "config") "baseMinForRewards") (.intLit 0)) =
      .ok (.bool (decide (c.baseMinForRewards.val ≠ 0))) := by
  simp only [evalExpr?, constructorSource_baseMin, pure, bind, EvalResult.bind, evalBinaryOp?]
  simp
  apply Bool.eq_iff_iff.mpr
  simp

theorem constructorSourceChecks_exec {c : ConstructorConfig} {w : UInt256}
    {evm evm' : EVM.State}
    (hp : ExecBlock config (constructorSourceEntry c) evm (contract.ctor.body.take 4)
      (.ok (constructorSourceDecimals c w) evm'))
    (hvalid : ConstructorChecksValid c) :
    ExecBlock config (constructorSourceEntry c) evm (contract.ctor.body.take 7)
      (.ok (constructorSourceDecimals c w) evm') := by
  change ExecBlock config _ _ (contract.ctor.body.take 4 ++
    [.require (.binary .le (.field (.var "config") "storeFrontPriceFactor")
      (.intLit 1000000000000000000)),
      .require (.binary .le (.arrayLength .localVar ⟨"config", [.field "assetConfigs"]⟩)
        (.intLit 24)),
      .require (.binary .ne (.field (.var "config") "baseMinForRewards") (.intLit 0))]) _
  apply execBlockAppendOk hp
  apply ExecBlock.consNormal (.requireTrue (by
    rw [constructorSource_storeFrontGuard, decide_eq_true hvalid.1]))
  apply ExecBlock.consNormal (.requireTrue (by
    rw [constructorSource_assetCountGuard, decide_eq_true hvalid.2.1]))
  exact .consNormal (.requireTrue (by
    rw [constructorSource_baseMinGuard, decide_eq_true hvalid.2.2])) .nil

theorem constructorSourceChecks_revert {c : ConstructorConfig} {w : UInt256}
    {evm evm' : EVM.State}
    (hp : ExecBlock config (constructorSourceEntry c) evm (contract.ctor.body.take 4)
      (.ok (constructorSourceDecimals c w) evm'))
    (hvalid : ¬ ConstructorChecksValid c) :
    ExecBlock config (constructorSourceEntry c) evm contract.ctor.body .reverted := by
  rw [← List.take_append_drop 4 contract.ctor.body]
  apply execBlockAppendOk hp
  by_cases hfactor : c.storeFrontPriceFactor.val ≤ 1000000000000000000
  · apply ExecBlock.consNormal (.requireTrue (by
      rw [constructorSource_storeFrontGuard, decide_eq_true hfactor]))
    by_cases hcount : c.assetConfigs.length ≤ 24
    · apply ExecBlock.consNormal (.requireTrue (by
        rw [constructorSource_assetCountGuard, decide_eq_true hcount]))
      apply ExecBlock.consRevert (.requireFalse (by
        rw [constructorSource_baseMinGuard,
          decide_eq_false (fun hb ↦ hvalid ⟨hfactor, hcount, hb⟩)]))
    · exact .consRevert (.requireFalse (by
        rw [constructorSource_assetCountGuard, decide_eq_false hcount]))
  · exact .consRevert (.requireFalse (by
      rw [constructorSource_storeFrontGuard, decide_eq_false hfactor]))

end Benchmarks.CompoundIII.Comet
