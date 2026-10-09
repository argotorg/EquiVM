import Benchmarks.Morpho.MorphoBlue.WithdrawCollateralUpdateReach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem CollateralTransferLocals.evalCollateral {p assets account receiver locals}
    (hl : CollateralTransferLocals p assets account receiver locals) (imms : Store) (evm : EVM.State)
    (ha : account.toNat < EVM.addressModulus) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"position", [.mindex (.var "id"), .mindex (.var "onBehalf"), .field "collateral"]⟩) =
      .ok (.int (Int.ofNat (positionFieldWord evm.accountMap evm.executionEnv p.id account 2).toNat)) :=
  evalMorphoPositionField evm locals imms _ _ p.id account 2 hl.position
    (hl.evalId imms evm) (hl.evalAccount imms evm) ha

inductive WithdrawCollateralUpdateRefines (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (p : MarketParamsWords) (assets account receiver : UInt256)
    (locals imms : Store) (evm : EVM.State) (mem : ByteArray) (fp : UInt256) (R : List UInt256) : Prop where
  | reverted : ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (withdrawCollateralTransition.body.drop 12) .reverted → RDrev (deployedRuntime v) g s0 →
      WithdrawCollateralUpdateRefines v ee g s0 p assets account receiver locals imms evm mem fp R
  | static : ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (withdrawCollateralTransition.body.drop 12) .staticViolation → RDstatic (deployedRuntime v) g s0 →
      WithdrawCollateralUpdateRefines v ee g s0 p assets account receiver locals imms evm mem fp R
  | ok {evm' σ' mem' fp' aw' out' k' C'} :
      StateBlock config { contract := contract, locals := locals, immutables := imms }
        evm (withdrawCollateralTransition.body.drop 12)
        { contract := contract, locals := locals.insert "__c3" (.int (Int.ofNat assets.toNat)), immutables := imms }
        evm' (withdrawCollateralTransition.body.drop 14) → SourceState s0 ee σ' evm' → ee.perm = true →
      MorphoHeap mem' fp' 352 → HeapAdvance mem fp mem' fp' 64 →
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5686)
        (withdrawCollateralUpdateTail p.id assets account receiver R)
        mem' aw' out' σ' k' C' →
      WithdrawCollateralUpdateRefines v ee g s0 p assets account receiver locals imms evm mem fp R

theorem morphoWithdrawCollateralUpdateRefine {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {aw fp assets account receiver : UInt256} {out mem : ByteArray}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (p : MarketParamsWords) (locals imms : Store) (hstack : R.length + 36 ≤ 1024) (ha : account.toNat < EVM.addressModulus)
    (hl : CollateralTransferLocals p assets account receiver locals) (hs : SourceState s0 ee σ evm)
    (hm : MorphoHeap mem fp 416)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5630)
      (withdrawCollateralGuardTail p.id assets account receiver R) mem aw out σ k C) :
    WithdrawCollateralUpdateRefines v ee g s0 p assets account receiver locals imms evm mem fp R := by
  obtain ⟨k1, C1, rd1⟩ := morphoWithdrawCollateralReachCast (v := v) (by omega) h
  by_cases hc : assets.toNat < 2 ^ 128
  swap
  · exact .reverted (ExecBlock.consRevert (morphoToUint128CallReverts assets evm locals imms
      (.var "assets") "__c3" (hl.evalAssets imms evm) (Nat.le_of_not_gt hc)))
      (morphoToUint128Reverts (v := v) (by simp only [withdrawCollateralGuardTail, withdrawCollateralUpdateTail, withdrawCollateralHealthTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
        (hm.alloc64Guard (by decide)) hm.size (by rw [hm.free]; exact hm.lower)
        hm.errorGap hm.errorHi (Nat.le_of_not_gt hc) rd1)
  have he1 := morphoToUint128CallOk assets evm locals imms (.var "assets") "__c3" (hl.evalAssets imms evm) hc
  let l1 := locals.insert "__c3" (.int (Int.ofNat assets.toNat))
  have hl1 : CollateralTransferLocals p assets account receiver l1 := hl.insert _ _ (by decide) (by decide)
  have he5 : evalExpr? config { contract := contract, locals := l1, immutables := imms } evm (.var "__c3") =
      .ok (.int (Int.ofNat assets.toNat)) := by simp only [evalExpr?, l1, store_get_self, EvalResult.ofOption]
  have ab1 : StateBlock config { contract := contract, locals := locals, immutables := imms }
      evm (withdrawCollateralTransition.body.drop 12) { contract := contract, locals := l1, immutables := imms }
      evm (withdrawCollateralTransition.body.drop 13) := StateBlock.start.step he1
  obtain ⟨a2, k2, C2, rd2⟩ := morphoToUint128Ok (v := v) (by simp only [withdrawCollateralGuardTail, withdrawCollateralUpdateTail, withdrawCollateralHealthTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (hm.alloc64Guard (by decide)) hc rd1
  obtain ⟨a3, k3, C3, rd3⟩ := morphoWithdrawCollateralReachSub (v := v) (by omega) ha rd2
  have hb : (positionFieldWord σ ee p.id account 2).toNat < 2 ^ 128 := by
    change (halfWord true _).toNat < 2 ^ 128
    exact halfWord_bound _ _
  have hb' : (positionFieldWord evm.accountMap evm.executionEnv p.id account 2).toNat < 2 ^ 128 := by
    change (halfWord true _).toNat < 2 ^ 128
    exact halfWord_bound _ _
  by_cases hf : assets.toNat ≤ (positionFieldWord σ ee p.id account 2).toNat
  swap
  · exact .reverted (ab1.reverts (ExecStmt.assignExprRevert (evalCheckedUint128SubReverts
      (hl1.evalCollateral imms evm ha) he5 (by simpa only [hs.env, ← hs.accounts] using Nat.lt_of_not_ge hf))))
      (morphoCheckedSub128Reverts (v := v) (by simp only [withdrawCollateralGuardTail, withdrawCollateralUpdateTail, withdrawCollateralHealthTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega) hb hc (Nat.lt_of_not_ge hf) rd3)
  have hf' : assets.toNat ≤ (positionFieldWord evm.accountMap evm.executionEnv p.id account 2).toNat := by
    simpa only [hs.env, ← hs.accounts] using hf
  have hass : ExecStmt config { contract := contract, locals := l1, immutables := imms }
      evm withdrawCollateralTransition.body[13]!
      (.ok { contract := contract, locals := l1, immutables := imms }
        (storePositionPacked evm p.id account true
          ((UInt256.sub (positionFieldWord evm.accountMap evm.executionEnv p.id account 2) assets)))) :=
    ExecStmt.assign (evalCheckedUint128SubOk (hl1.evalCollateral imms evm ha) he5 hb' hf')
      (assignPositionPacked evm l1 imms _ _ p.id account true _ (by rw [usub_toNat hf']; omega)
        ha hl1.position (hl1.evalId imms evm) (hl1.evalAccount imms evm))
  obtain ⟨k4, C4, rd4⟩ := morphoCheckedSub128Ok (v := v) (by simp only [withdrawCollateralGuardTail, withdrawCollateralUpdateTail, withdrawCollateralHealthTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hb hc hf rd3
  by_cases hperm : ee.perm = true
  swap
  · exact .static (ab1.static (execStmt_assign_static hass (by rw [hs.env]; exact Bool.eq_false_iff.mpr hperm)))
      (morphoStoreUint128HighStatic (v := v) (by simp only [withdrawCollateralGuardTail, withdrawCollateralUpdateTail, withdrawCollateralHealthTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega) (Bool.eq_false_iff.mpr hperm) rd4)
  obtain ⟨k5, C5, rd5⟩ := morphoStoreUint128High (v := v)
    (by simp only [withdrawCollateralUpdateTail, withdrawCollateralHealthTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    hperm (by rw [morphoPatchedValidJumps v]; jump_dest) (by rw [usub_toNat hf]; omega) rd4
  have hs' := storePositionPacked_bridge hs p.id account true ((UInt256.sub (positionFieldWord σ ee p.id account 2) assets))
  have hm1 := hm.narrow (by decide : 64 ≤ 416)
  have had := (hm.narrowAdvance.trans (heapAdvance_hash _ _ p.id (UInt256.ofNat 2))).trans
    (heapAdvance_hash _ _ account (solcMappingSlot ⟨2⟩ p.id))
  exact .ok (ab1.step hass) (by simpa only [hs.env, ← hs.accounts] using hs') hperm
    ((hm1.hash p.id (UInt256.ofNat 2)).hash account (solcMappingSlot ⟨2⟩ p.id))
    (by simpa only [Nat.add_zero] using had) rd5

end Benchmarks.Morpho.MorphoBlue
