import Benchmarks.Morpho.MorphoBlue.LiquidateCollateralReach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

inductive LiquidateCollateralRefines (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (p : MarketParamsWords) (assets seized shares account srcOff len : UInt256)
    (locals imms : Store) (evm : EVM.State) (mem : ByteArray) (fp : UInt256) (R : List UInt256) : Prop where
  | reverted : ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (liquidateTransition.body.drop 25) .reverted → RDrev (deployedRuntime v) g s0 →
      LiquidateCollateralRefines v ee g s0 p assets seized shares account srcOff len locals imms evm mem fp R
  | ok {evm' σ' mem' fp' aw' out' k' C'} :
      StateBlock config { contract := contract, locals := locals, immutables := imms }
        evm (liquidateTransition.body.drop 25)
        { contract := contract, locals := locals.insert "__c15" (.int (Int.ofNat seized.toNat)), immutables := imms }
        evm' (liquidateTransition.body.drop 28) → SourceState s0 ee σ' evm' →
      MorphoHeap mem' fp' 576 → HeapAdvance mem fp mem' fp' 64 →
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 2509)
        (liquidateMarketTail p.id assets seized shares srcOff len R) mem' aw' out' σ' k' C' →
      LiquidateCollateralRefines v ee g s0 p assets seized shares account srcOff len locals imms evm mem fp R

theorem morphoLiquidateCollateralRefine {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {aw fp assets seized shares account srcOff len debt : UInt256} {out mem data : ByteArray}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (p : MarketParamsWords) (locals imms : Store)
    (hstack : R.length + 40 ≤ 1024) (ha : account.toNat < EVM.addressModulus)
    (haccount : calldataWord ee.calldata 164 = account) (hperm : ee.perm = true)
    (hl : LiquidateLocals p account seized shares data locals) (hs : SourceState s0 ee σ evm)
    (hm : MorphoHeap mem fp 640) (hget : locals.get? "__c14" = some (.int (Int.ofNat debt.toNat)))
    (hd : debt.toNat < 2 ^ 128)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 2391)
      (debt :: liquidateMarketTail p.id assets seized shares srcOff len R) mem aw out σ k C) :
    LiquidateCollateralRefines v ee g s0 p assets seized shares account srcOff len locals imms evm mem fp R := by
  let e1 := storeMarketField evm p.id ⟨2, by decide⟩ debt
  let σ1 := storeMarketFieldAccounts σ ee p.id ⟨2, by decide⟩ debt
  have hs1 : SourceState s0 ee σ1 e1 := storeMarketField_bridge hs p.id ⟨2, by decide⟩ debt
  have hass0 : ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      liquidateTransition.body[25]! (.ok { contract := contract, locals := locals, immutables := imms } e1) := by
    apply ExecStmt.assign (show evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.var "__c14") = .ok (.int (Int.ofNat debt.toNat)) from by simp only [evalExpr?, hget, EvalResult.ofOption])
    exact assignMarketField evm locals imms (.var "id") p.id ⟨2, by decide⟩ debt hd hl.market (hl.evalId imms evm)
  have ab0 : StateBlock config { contract := contract, locals := locals, immutables := imms } evm
      (liquidateTransition.body.drop 25) { contract := contract, locals := locals, immutables := imms } e1
      (liquidateTransition.body.drop 26) := StateBlock.start.step hass0
  obtain ⟨a0, k0, C0, rd0⟩ := morphoLiquidateDebtStore (v := v) (by omega) hperm hd h
  have hm0 := hm.hash p.id (UInt256.ofNat 3)
  by_cases hc : seized.toNat < 2 ^ 128
  swap
  · exact .reverted (ab0.reverts (morphoToUint128CallReverts seized e1 locals imms
      (.var "seizedAssets") "__c15" (hl.evalSeized imms e1) (Nat.le_of_not_gt hc)))
      (morphoToUint128Reverts (v := v) (by change R.length + 10 + 16 ≤ 1024; omega)
        (hm0.alloc64Guard (by decide)) hm0.size (by rw [hm0.free]; exact hm0.lower)
        hm0.errorGap hm0.errorHi (Nat.le_of_not_gt hc) rd0)
  have he1 := morphoToUint128CallOk seized e1 locals imms (.var "seizedAssets") "__c15" (hl.evalSeized imms e1) hc
  let l1 := locals.insert "__c15" (.int (Int.ofNat seized.toNat))
  have hl1 : LiquidateLocals p account seized shares data l1 := hl.insert _ _ (by decide) (by decide)
  have he5 : evalExpr? config { contract := contract, locals := l1, immutables := imms } e1 (.var "__c15") =
      .ok (.int (Int.ofNat seized.toNat)) := by simp only [evalExpr?, l1, store_get_self, EvalResult.ofOption]
  have ab1 := ab0.step he1
  obtain ⟨a2, k2, C2, rd2⟩ := morphoToUint128Ok (v := v) (by change R.length + 10 + 16 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (hm0.alloc64Guard (by decide)) hc rd0
  obtain ⟨a3, k3, C3, rd3⟩ := morphoLiquidateCollateralReachSub (v := v) (by omega) ha haccount rd2
  have hb : (positionFieldWord σ1 ee p.id account 2).toNat < 2 ^ 128 := by
    change (halfWord true _).toNat < 2 ^ 128
    exact halfWord_bound _ _
  have hb' : (positionFieldWord e1.accountMap e1.executionEnv p.id account 2).toNat < 2 ^ 128 := by
    change (halfWord true _).toNat < 2 ^ 128
    exact halfWord_bound _ _
  by_cases hf : seized.toNat ≤ (positionFieldWord σ1 ee p.id account 2).toNat
  swap
  · exact .reverted (ab1.reverts (ExecStmt.assignExprRevert (evalCheckedUint128SubReverts
      (hl1.evalPosition imms e1 ⟨2, by decide⟩ ha) he5 (by simpa only [hs1.env, ← hs1.accounts] using Nat.lt_of_not_ge hf))))
      (morphoCheckedSub128Reverts (v := v) (by change R.length + 11 + 6 ≤ 1024; omega) hb hc (Nat.lt_of_not_ge hf) rd3)
  have hf' : seized.toNat ≤ (positionFieldWord e1.accountMap e1.executionEnv p.id account 2).toNat := by
    simpa only [hs1.env, ← hs1.accounts] using hf
  have hass : ExecStmt config { contract := contract, locals := l1, immutables := imms } e1
      liquidateTransition.body[27]!
      (.ok { contract := contract, locals := l1, immutables := imms }
        (storePositionPacked e1 p.id account true
          (UInt256.sub (positionFieldWord e1.accountMap e1.executionEnv p.id account 2) seized))) :=
    ExecStmt.assign (evalCheckedUint128SubOk (hl1.evalPosition imms e1 ⟨2, by decide⟩ ha) he5 hb' hf')
      (assignPositionPacked e1 l1 imms _ _ p.id account true _ (by
          change (UInt256.sub (positionFieldWord e1.accountMap e1.executionEnv p.id account 2) seized).toNat < 2 ^ 128
          rw [usub_toNat hf']; omega)
        ha hl1.position (hl1.evalId imms e1) (hl1.evalBorrower imms e1))
  obtain ⟨k4, C4, rd4⟩ := morphoCheckedSub128Ok (v := v) (by change R.length + 11 + 6 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hb hc hf rd3
  obtain ⟨k5, C5, rd5⟩ := morphoStoreUint128High (v := v) (by change R.length + 9 + 7 ≤ 1024; omega)
    hperm (by rw [morphoPatchedValidJumps v]; jump_dest) (by rw [usub_toNat hf]; omega) rd4
  have hs' := storePositionPacked_bridge hs1 p.id account true (UInt256.sub (positionFieldWord σ1 ee p.id account 2) seized)
  have hm1 := hm0.narrow (by decide : 64 ≤ 640)
  have had := (((heapAdvance_hash mem fp p.id (UInt256.ofNat 3)).trans hm0.narrowAdvance).trans
    (heapAdvance_hash _ _ p.id (UInt256.ofNat 2))).trans (heapAdvance_hash _ _ account (solcMappingSlot ⟨2⟩ p.id))
  exact .ok (ab1.step hass) (by simpa only [hs1.env, ← hs1.accounts] using hs')
    ((hm1.hash p.id (UInt256.ofNat 2)).hash account (solcMappingSlot ⟨2⟩ p.id))
    (by simpa only [Nat.add_zero, Nat.zero_add] using had) rd5

end Benchmarks.Morpho.MorphoBlue
