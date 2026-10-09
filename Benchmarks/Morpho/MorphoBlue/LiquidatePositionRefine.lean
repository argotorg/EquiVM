import Benchmarks.Morpho.MorphoBlue.LiquidatePositionReach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

inductive LiquidatePositionRefines (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (p : MarketParamsWords) (assets seized shares account srcOff len : UInt256)
    (locals imms : Store) (evm : EVM.State) (mem : ByteArray) (fp : UInt256) (R : List UInt256) : Prop where
  | reverted : ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (liquidateTransition.body.drop 19) .reverted → RDrev (deployedRuntime v) g s0 →
      LiquidatePositionRefines v ee g s0 p assets seized shares account srcOff len locals imms evm mem fp R
  | static : ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (liquidateTransition.body.drop 19) .staticViolation → RDstatic (deployedRuntime v) g s0 →
      LiquidatePositionRefines v ee g s0 p assets seized shares account srcOff len locals imms evm mem fp R
  | ok {evm' σ' mem' fp' aw' out' k' C'} :
      StateBlock config { contract := contract, locals := locals, immutables := imms }
        evm (liquidateTransition.body.drop 19)
        { contract := contract, locals := locals.insert "__c12" (.int (Int.ofNat shares.toNat)), immutables := imms }
        evm' (liquidateTransition.body.drop 21) → SourceState s0 ee σ' evm' → ee.perm = true →
      MorphoHeap mem' fp' 768 → HeapAdvance mem fp mem' fp' 64 →
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15480)
        ([shares, UInt256.ofNat 2249, UInt256.ofNat 2342] ++ liquidateMarketTail p.id assets seized shares srcOff len R)
        mem' aw' out' σ' k' C' →
      LiquidatePositionRefines v ee g s0 p assets seized shares account srcOff len locals imms evm mem fp R

theorem morphoLiquidatePositionRefine {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {aw fp assets seized shares account srcOff len : UInt256} {out mem : ByteArray}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (p : MarketParamsWords) (data : ByteArray)
    (locals imms : Store) (hstack : R.length + 40 ≤ 1024) (ha : account.toNat < EVM.addressModulus)
    (haccount : calldataWord ee.calldata 164 = account)
    (hl : LiquidateLocals p account seized shares data locals) (hs : SourceState s0 ee σ evm)
    (hm : MorphoHeap mem fp 832)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 2105)
      (assets :: liquidateFinishMathTail p.id seized shares srcOff len R) mem aw out σ k C) :
    LiquidatePositionRefines v ee g s0 p assets seized shares account srcOff len locals imms evm mem fp R := by
  obtain ⟨k1, C1, rd1⟩ := morphoLiquidatePositionReachCast (v := v) (by omega) h
  by_cases hc : shares.toNat < 2 ^ 128
  swap
  · exact .reverted (ExecBlock.consRevert (morphoToUint128CallReverts shares evm locals imms
      (.var "repaidShares") "__c12" (hl.evalShares imms evm) (Nat.le_of_not_gt hc)))
      (morphoToUint128Reverts (v := v) (by change R.length + 8 + 16 ≤ 1024; omega)
        (hm.alloc64Guard (by decide)) hm.size (by rw [hm.free]; exact hm.lower)
        hm.errorGap hm.errorHi (Nat.le_of_not_gt hc) rd1)
  have he1 := morphoToUint128CallOk shares evm locals imms (.var "repaidShares") "__c12" (hl.evalShares imms evm) hc
  let l1 := locals.insert "__c12" (.int (Int.ofNat shares.toNat))
  have hl1 : LiquidateLocals p account seized shares data l1 := hl.insert _ _ (by decide) (by decide)
  have he5 : evalExpr? config { contract := contract, locals := l1, immutables := imms } evm (.var "__c12") =
      .ok (.int (Int.ofNat shares.toNat)) := by simp only [evalExpr?, l1, store_get_self, EvalResult.ofOption]
  have ab1 : StateBlock config { contract := contract, locals := locals, immutables := imms }
      evm (liquidateTransition.body.drop 19) { contract := contract, locals := l1, immutables := imms }
      evm (liquidateTransition.body.drop 20) := StateBlock.start.step he1
  obtain ⟨a2, k2, C2, rd2⟩ := morphoToUint128Ok (v := v) (by change R.length + 8 + 16 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (hm.alloc64Guard (by decide)) hc rd1
  obtain ⟨a3, k3, C3, rd3⟩ := morphoLiquidatePositionReachSub (v := v) (by omega) ha haccount rd2
  have hb : (positionFieldWord σ ee p.id account 1).toNat < 2 ^ 128 := by
    change (halfWord false _).toNat < 2 ^ 128
    exact halfWord_bound _ _
  have hb' : (positionFieldWord evm.accountMap evm.executionEnv p.id account 1).toNat < 2 ^ 128 := by
    change (halfWord false _).toNat < 2 ^ 128
    exact halfWord_bound _ _
  by_cases hf : shares.toNat ≤ (positionFieldWord σ ee p.id account 1).toNat
  swap
  · exact .reverted (ab1.reverts (ExecStmt.assignExprRevert (evalCheckedUint128SubReverts
      (hl1.evalPosition imms evm ⟨1, by decide⟩ ha) he5 (by simpa only [hs.env, ← hs.accounts] using Nat.lt_of_not_ge hf))))
      (morphoCheckedSub128Reverts (v := v) (by change R.length + 11 + 6 ≤ 1024; omega) hb hc (Nat.lt_of_not_ge hf) rd3)
  have hf' : shares.toNat ≤ (positionFieldWord evm.accountMap evm.executionEnv p.id account 1).toNat := by
    simpa only [hs.env, ← hs.accounts] using hf
  have hass : ExecStmt config { contract := contract, locals := l1, immutables := imms }
      evm liquidateTransition.body[20]!
      (.ok { contract := contract, locals := l1, immutables := imms }
        (storePositionPacked evm p.id account false
          (UInt256.sub (positionFieldWord evm.accountMap evm.executionEnv p.id account 1) shares))) :=
    ExecStmt.assign (evalCheckedUint128SubOk (hl1.evalPosition imms evm ⟨1, by decide⟩ ha) he5 hb' hf')
      (assignPositionPacked evm l1 imms _ _ p.id account false _ (by
          change (UInt256.sub (positionFieldWord evm.accountMap evm.executionEnv p.id account 1) shares).toNat < 2 ^ 128
          rw [usub_toNat hf']; omega)
        ha hl1.position (hl1.evalId imms evm) (hl1.evalBorrower imms evm))
  obtain ⟨k4, C4, rd4⟩ := morphoCheckedSub128Ok (v := v) (by change R.length + 11 + 6 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hb hc hf rd3
  by_cases hperm : ee.perm = true
  swap
  · exact .static (ab1.static (execStmt_assign_static hass (by rw [hs.env]; exact Bool.eq_false_iff.mpr hperm)))
      (morphoLiquidatePositionStatic (v := v) (by change R.length + 8 + 6 ≤ 1024; omega) (Bool.eq_false_iff.mpr hperm) rd4)
  obtain ⟨a5, k5, C5, rd5⟩ := morphoLiquidatePositionStore (v := v) (by omega) hperm (by rw [usub_toNat hf]; omega) rd4
  have hs' := storePositionPacked_bridge hs p.id account false (UInt256.sub (positionFieldWord σ ee p.id account 1) shares)
  have hm1 := hm.narrow (by decide : 64 ≤ 832)
  have had := (hm.narrowAdvance.trans (heapAdvance_hash _ _ p.id (UInt256.ofNat 2))).trans
    (heapAdvance_hash _ _ account (solcMappingSlot ⟨2⟩ p.id))
  exact .ok (ab1.step hass) (by simpa only [hs.env, ← hs.accounts] using hs') hperm
    ((hm1.hash p.id (UInt256.ofNat 2)).hash account (solcMappingSlot ⟨2⟩ p.id))
    (by simpa only [Nat.add_zero] using had) rd5

end Benchmarks.Morpho.MorphoBlue
