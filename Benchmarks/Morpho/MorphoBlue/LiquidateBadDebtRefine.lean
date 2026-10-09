import Benchmarks.Morpho.MorphoBlue.LiquidateBadBodyRefine

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def liquidateBadInitLocals (locals : Store) : Store :=
  (locals.insert "badDebtShares" (.int 0)).insert "badDebtAssets" (.int 0)

theorem liquidateBadInit (locals imms : Store) (evm : EVM.State) :
    ABlock config evm { contract := contract, locals := locals, immutables := imms }
      (liquidateTransition.body.drop 28)
      { contract := contract, locals := liquidateBadInitLocals locals, immutables := imms }
      (liquidateTransition.body.drop 30) := by
  apply ABlock.letStep (ABlock.letStep ABlock.start _)
  all_goals simp only [evalExpr?, pure]

theorem liquidateBadInit_locals {p account seized shares data assets locals}
    (hl : LiquidateLocals p account seized shares data locals)
    (hg : locals.get? "repaidAssets" = some (.int (Int.ofNat assets.toNat))) :
    LiquidateEventLocals p account seized shares data assets (UInt256.ofNat 0) (UInt256.ofNat 0)
      (liquidateBadInitLocals locals) := by
  refine ⟨(hl.insert _ _ (by decide) (by decide)).insert _ _ (by decide) (by decide), ?_, store_get_self _ _ _, ?_⟩
  · dsimp only [liquidateBadInitLocals]
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
    exact hg
  · dsimp only [liquidateBadInitLocals]
    rw [store_get_ne _ _ (by decide), store_get_self]
    rfl

theorem liquidateBadInit_memory (locals : Store) :
    (liquidateBadInitLocals locals).get? "__memory" = locals.get? "__memory" := by
  dsimp only [liquidateBadInitLocals]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]

inductive LiquidateBadDebtRefines (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (p : MarketParamsWords) (assets seized shares account srcOff len : UInt256) (data : ByteArray)
    (locals imms : Store) (evm : EVM.State) (mem : ByteArray) (fp : UInt256) (R : List UInt256) : Prop where
  | reverted : ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (liquidateTransition.body.drop 28) .reverted → RDrev (deployedRuntime v) g s0 →
      LiquidateBadDebtRefines v ee g s0 p assets seized shares account srcOff len data locals imms evm mem fp R
  | ok {trash badAssets badShares locals' evm' σ' mem' fp' aw' out' k' C'} :
      StateBlock config { contract := contract, locals := locals, immutables := imms }
        evm (liquidateTransition.body.drop 28) { contract := contract, locals := locals', immutables := imms }
        evm' (liquidateTransition.body.drop 31) →
      LiquidateEventLocals p account seized shares data assets badAssets badShares locals' →
      locals'.get? "__memory" = some (.int (Int.ofNat fp'.toNat)) →
      SourceState s0 ee σ' evm' → MorphoHeap mem' fp' 384 → MemoryPrefix mem mem' fp.toNat → fp.toNat ≤ fp'.toNat →
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 2574)
        (liquidateEventTail trash p.id assets seized shares badAssets badShares srcOff len R) mem' aw' out' σ' k' C' →
      LiquidateBadDebtRefines v ee g s0 p assets seized shares account srcOff len data locals imms evm mem fp R

theorem morphoLiquidateBadDebtRefine {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {aw fp assets seized shares account srcOff len : UInt256} {out mem data : ByteArray}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (p : MarketParamsWords) (locals imms : Store)
    (hstack : R.length + 48 ≤ 1024) (hperm : ee.perm = true)
    (ha : account.toNat < EVM.addressModulus) (haccount : calldataWord ee.calldata 164 = account)
    (hl : LiquidateLocals p account seized shares data locals)
    (hassets : locals.get? "repaidAssets" = some (.int (Int.ofNat assets.toNat)))
    (hs : SourceState s0 ee σ evm) (hm : MorphoHeap mem fp 576)
    (hget : locals.get? "__memory" = some (.int (Int.ofNat fp.toNat)))
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 2509)
      (liquidateMarketTail p.id assets seized shares srcOff len R) mem aw out σ k C) :
    LiquidateBadDebtRefines v ee g s0 p assets seized shares account srcOff len data locals imms evm mem fp R := by
  have ab := liquidateBadInit locals imms evm
  have hl0 := liquidateBadInit_locals hl hassets
  have hg0 : (liquidateBadInitLocals locals).get? "__memory" = some (.int (Int.ofNat fp.toNat)) :=
    (liquidateBadInit_memory locals).trans hget
  obtain ⟨a0, k0, C0, rd0⟩ := morphoLiquidateBadDebtGuard (v := v) (by omega) ha haccount h
  have hm0 := (hm.hash p.id (UInt256.ofNat 2)).hash account (solcMappingSlot ⟨2⟩ p.id)
  have ad0 := (heapAdvance_hash mem fp p.id (UInt256.ofNat 2)).trans
    (heapAdvance_hash _ fp account (solcMappingSlot ⟨2⟩ p.id))
  have he := evalWordEqZero (hl0.evalPosition imms evm ⟨2, by decide⟩ ha)
  rw [hs.env, ← hs.accounts] at he
  change evalExpr? _ _ _ _ = .ok (.bool (decide (positionFieldWord σ ee p.id account 2 = ⟨0⟩))) at he
  by_cases hz : positionFieldWord σ ee p.id account 2 = ⟨0⟩
  · rw [if_pos hz] at rd0
    rw [decide_eq_true hz] at he
    obtain hre | ⟨he1, hl1, hg1, hs1, hm1, ad1, rd1⟩ :=
      morphoLiquidateBadBodyRefine (v := v) p _ imms hstack hperm ha haccount hl0 hs hm0 hg0 rd0
    · exact .reverted (ab.run (ExecBlock.consRevert (ExecStmt.iteTrue he hre))) ‹RDrev _ _ _›
    exact .ok ⟨fun tail ↦ ab.run (ExecBlock.consNormal (ExecStmt.iteTrue he he1) tail)⟩
      hl1 hg1 hs1 hm1 (ad0.trans ad1).preserves (by have hh := ad1.cursor; omega) rd1
  · rw [if_neg hz] at rd0
    rw [decide_eq_false hz] at he
    exact .ok ⟨fun tail ↦ ab.run (ExecBlock.consNormal (ExecStmt.iteFalse he ExecBlock.nil) tail)⟩
      hl0 hg0 hs (hm0.weaken (by decide)) ad0.preserves le_rfl rd0

end Benchmarks.Morpho.MorphoBlue
