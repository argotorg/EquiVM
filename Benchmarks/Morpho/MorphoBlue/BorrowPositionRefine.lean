import Benchmarks.Morpho.MorphoBlue.BorrowPositionReach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem MarketTransferLocals.evalPositionBorrowShares {p assets shares account receiver locals}
    (hl : MarketTransferLocals p assets shares account receiver locals) (imms : Store) (evm : EVM.State)
    (ha : account.toNat < EVM.addressModulus) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"position", [.mindex (.var "id"), .mindex (.var "onBehalf"), .field "borrowShares"]⟩) =
      .ok (.int (Int.ofNat (positionFieldWord evm.accountMap evm.executionEnv p.id account 1).toNat)) :=
  evalMorphoPositionField evm locals imms _ _ p.id account 1 hl.position
    (hl.evalId imms evm) (hl.evalAccount imms evm) ha

inductive BorrowPositionRefines (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (p : MarketParamsWords) (assets shares account receiver : UInt256)
    (locals imms : Store) (evm : EVM.State) (mem : ByteArray) (fp : UInt256) (R : List UInt256) : Prop where
  | reverted : ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (borrowTransition.body.drop 14) .reverted → RDrev (deployedRuntime v) g s0 →
      BorrowPositionRefines v ee g s0 p assets shares account receiver locals imms evm mem fp R
  | static : ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (borrowTransition.body.drop 14) .staticViolation → RDstatic (deployedRuntime v) g s0 →
      BorrowPositionRefines v ee g s0 p assets shares account receiver locals imms evm mem fp R
  | ok {evm' σ' mem' fp' aw' out' k' C'} :
      StateBlock config { contract := contract, locals := locals, immutables := imms }
        evm (borrowTransition.body.drop 14)
        { contract := contract, locals := locals.insert "__c6" (.int (Int.ofNat shares.toNat)), immutables := imms }
        evm' (borrowTransition.body.drop 16) → SourceState s0 ee σ' evm' → ee.perm = true →
      MorphoHeap mem' fp' 352 → HeapAdvance mem fp mem' fp' 64 →
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15480)
        ([shares, UInt256.ofNat 8645] ++ borrowMarketTail p.id assets shares account receiver R)
        mem' aw' out' σ' k' C' →
      BorrowPositionRefines v ee g s0 p assets shares account receiver locals imms evm mem fp R

theorem morphoBorrowPositionRefine {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {aw fp assets shares account receiver : UInt256} {out mem : ByteArray}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (p : MarketParamsWords) (locals imms : Store) (hstack : R.length + 36 ≤ 1024) (ha : account.toNat < EVM.addressModulus)
    (hl : MarketTransferLocals p assets shares account receiver locals) (hs : SourceState s0 ee σ evm)
    (hm : MorphoHeap mem fp 416)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 8538)
      (borrowUpdateTail p.id assets shares account receiver R) mem aw out σ k C) :
    BorrowPositionRefines v ee g s0 p assets shares account receiver locals imms evm mem fp R := by
  obtain ⟨k1, C1, rd1⟩ := morphoBorrowPositionReachCast (v := v) (by omega) h
  by_cases hc : shares.toNat < 2 ^ 128
  swap
  · exact .reverted (ExecBlock.consRevert (morphoToUint128CallReverts shares evm locals imms
      (.var "shares") "__c6" (hl.evalShares imms evm) (Nat.le_of_not_gt hc)))
      (morphoToUint128Reverts (v := v) (by simp only [borrowUpdateTail, borrowPositionStoreTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
        (hm.alloc64Guard (by decide)) hm.size (by rw [hm.free]; exact hm.lower)
        hm.errorGap hm.errorHi (Nat.le_of_not_gt hc) rd1)
  have he1 := morphoToUint128CallOk shares evm locals imms (.var "shares") "__c6" (hl.evalShares imms evm) hc
  let l1 := locals.insert "__c6" (.int (Int.ofNat shares.toNat))
  have hl1 : MarketTransferLocals p assets shares account receiver l1 := hl.insert _ _ (by decide) (by decide)
  have he5 : evalExpr? config { contract := contract, locals := l1, immutables := imms } evm (.var "__c6") =
      .ok (.int (Int.ofNat shares.toNat)) := by simp only [evalExpr?, l1, store_get_self, EvalResult.ofOption]
  have ab1 : StateBlock config { contract := contract, locals := locals, immutables := imms }
      evm (borrowTransition.body.drop 14) { contract := contract, locals := l1, immutables := imms }
      evm (borrowTransition.body.drop 15) := StateBlock.start.step he1
  obtain ⟨a2, k2, C2, rd2⟩ := morphoToUint128Ok (v := v) (by simp only [borrowUpdateTail, borrowPositionStoreTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (hm.alloc64Guard (by decide)) hc rd1
  obtain ⟨a3, k3, C3, rd3⟩ := morphoBorrowPositionReachAdd (v := v) (by omega) ha rd2
  have hb : (positionFieldWord σ ee p.id account 1).toNat < 2 ^ 128 := by
    change (halfWord false _).toNat < 2 ^ 128
    exact halfWord_bound _ _
  have hb' : (positionFieldWord evm.accountMap evm.executionEnv p.id account 1).toNat < 2 ^ 128 := by
    change (halfWord false _).toNat < 2 ^ 128
    exact halfWord_bound _ _
  by_cases hf : (positionFieldWord σ ee p.id account 1).toNat + shares.toNat < 2 ^ 128
  swap
  · exact .reverted (ab1.reverts (ExecStmt.assignExprRevert (evalCheckedUint128AddReverts
      (hl1.evalPositionBorrowShares imms evm ha) he5 (by simpa only [hs.env, ← hs.accounts] using Nat.le_of_not_gt hf))))
      (morphoCheckedAdd128Reverts (v := v) (by simp only [borrowUpdateTail, borrowPositionStoreTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega) hb hc (Nat.le_of_not_gt hf) rd3)
  have hf' : (positionFieldWord evm.accountMap evm.executionEnv p.id account 1).toNat + shares.toNat < 2 ^ 128 := by
    simpa only [hs.env, ← hs.accounts] using hf
  have hass : ExecStmt config { contract := contract, locals := l1, immutables := imms }
      evm borrowTransition.body[15]!
      (.ok { contract := contract, locals := l1, immutables := imms }
        (storePositionPacked evm p.id account false
          ((positionFieldWord evm.accountMap evm.executionEnv p.id account 1 + shares)))) :=
    ExecStmt.assign (evalCheckedUint128AddOk (hl1.evalPositionBorrowShares imms evm ha) he5 hf')
      (assignPositionPacked evm l1 imms _ _ p.id account false _ (by rw [uadd_toNat, Nat.mod_eq_of_lt (uint128_add_fits_word _ _ hb' hc)]; exact hf')
        ha hl1.position (hl1.evalId imms evm) (hl1.evalAccount imms evm))
  obtain ⟨k4, C4, rd4⟩ := morphoCheckedAdd128Ok (v := v) (by simp only [borrowUpdateTail, borrowPositionStoreTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hb hc hf rd3
  by_cases hperm : ee.perm = true
  swap
  · exact .static (ab1.static (execStmt_assign_static hass (by rw [hs.env]; exact Bool.eq_false_iff.mpr hperm)))
      (morphoBorrowPositionStatic (v := v) (by simp only [borrowUpdateTail, borrowPositionStoreTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega) (Bool.eq_false_iff.mpr hperm) rd4)
  obtain ⟨a5, k5, C5, rd5⟩ := morphoBorrowPositionStore (v := v) (by omega) hperm (by rw [uadd_toNat, Nat.mod_eq_of_lt (uint128_add_fits_word _ _ hb hc)]; exact hf) rd4
  have hs' := storePositionPacked_bridge hs p.id account false ((positionFieldWord σ ee p.id account 1 + shares))
  have hm1 := hm.narrow (by decide : 64 ≤ 416)
  have had := (hm.narrowAdvance.trans (heapAdvance_hash _ _ p.id (UInt256.ofNat 2))).trans
    (heapAdvance_hash _ _ account (solcMappingSlot ⟨2⟩ p.id))
  exact .ok (ab1.step hass) (by simpa only [hs.env, ← hs.accounts] using hs') hperm
    ((hm1.hash p.id (UInt256.ofNat 2)).hash account (solcMappingSlot ⟨2⟩ p.id))
    (by simpa only [Nat.add_zero] using had) rd5

end Benchmarks.Morpho.MorphoBlue
