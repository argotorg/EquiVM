import Benchmarks.Morpho.MorphoBlue.BorrowMarketReach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

inductive BorrowMarketRefines (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (p : MarketParamsWords) (assets shares account receiver : UInt256)
    (locals imms : Store) (evm : EVM.State) (mem : ByteArray) (fp : UInt256) (R : List UInt256) : Prop where
  | reverted : ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (borrowTransition.body.drop 16) .reverted → RDrev (deployedRuntime v) g s0 →
      BorrowMarketRefines v ee g s0 p assets shares account receiver locals imms evm mem fp R
  | ok {locals' evm' σ' mem' fp' aw' out' k' C'} :
      StateBlock config { contract := contract, locals := locals, immutables := imms }
        evm (borrowTransition.body.drop 16) { contract := contract, locals := locals', immutables := imms }
        evm' (borrowTransition.body.drop 20) → MarketTransferLocals p assets shares account receiver locals' →
      locals'.get? "__memory" = locals.get? "__memory" →
      SourceState s0 ee σ' evm' → MorphoHeap mem' fp' 224 → HeapAdvance mem fp mem' fp' 128 →
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13948)
        ([UInt256.ofNat 128, p.id, account, UInt256.ofNat 8794] ++ borrowHealthTail p.id assets shares account receiver R)
        mem' aw' out' σ' k' C' →
      BorrowMarketRefines v ee g s0 p assets shares account receiver locals imms evm mem fp R

theorem morphoBorrowMarketRefine {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {aw fp assets shares account receiver : UInt256} {out mem : ByteArray}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (p : MarketParamsWords)
    (locals imms : Store) (hstack : R.length + 40 ≤ 1024) (hperm : ee.perm = true)
    (hl : MarketTransferLocals p assets shares account receiver locals) (hs : SourceState s0 ee σ evm)
    (hm : MorphoHeap mem fp 352)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15480)
      ([shares, UInt256.ofNat 8645] ++ borrowMarketTail p.id assets shares account receiver R)
      mem aw out σ k C) :
    BorrowMarketRefines v ee g s0 p assets shares account receiver locals imms evm mem fp R := by
  by_cases hc : shares.toNat < 2 ^ 128
  swap
  · exact .reverted (ExecBlock.consRevert (morphoToUint128CallReverts shares evm locals imms
      (.var "shares") "__c7" (hl.evalShares imms evm) (Nat.le_of_not_gt hc)))
      (morphoToUint128Reverts (v := v) (by simp only [borrowMarketTail, borrowSharesStoreTail, borrowStoreTail, borrowHealthTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
        (hm.alloc64Guard (by decide)) hm.size (by rw [hm.free]; exact hm.lower)
        hm.errorGap hm.errorHi (Nat.le_of_not_gt hc) h)
  have he1 := morphoToUint128CallOk shares evm locals imms (.var "shares") "__c7" (hl.evalShares imms evm) hc
  let l1 := locals.insert "__c7" (.int (Int.ofNat shares.toNat))
  have hl1 : MarketTransferLocals p assets shares account receiver l1 := hl.insert _ _ (by decide) (by decide)
  have hs1 : evalExpr? config { contract := contract, locals := l1, immutables := imms } evm (.var "__c7") =
      .ok (.int (Int.ofNat shares.toNat)) := by simp only [evalExpr?, l1, store_get_self, EvalResult.ofOption]
  have ab1 : StateBlock config { contract := contract, locals := locals, immutables := imms }
      evm (borrowTransition.body.drop 16) { contract := contract, locals := l1, immutables := imms }
      evm (borrowTransition.body.drop 17) := StateBlock.start.step he1
  obtain ⟨a1, k1, C1, rd1⟩ := morphoToUint128Ok (v := v) (by simp only [borrowMarketTail, borrowSharesStoreTail, borrowStoreTail, borrowHealthTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (hm.alloc64Guard (by decide)) hc h
  have hm1 := hm.narrow (by decide : 64 ≤ 352)
  obtain ⟨a2, k2, C2, rd2⟩ := morphoBorrowMarketSharesReachAdd (v := v) (by omega) rd1
  have hm2 := hm1.hash p.id (UInt256.ofNat 3)
  by_cases hf : (marketFieldWord σ ee p.id 3).toNat + shares.toNat < 2 ^ 128
  swap
  · exact .reverted (ab1.reverts (morphoAccrueAssetsAssignReverts p l1 imms evm ⟨3, by decide⟩
      "__c7" shares hl1.toMarketLocals hs1 (by simpa only [hs.env, ← hs.accounts] using Nat.le_of_not_gt hf)))
      (morphoCheckedAdd128Reverts (v := v) (by simp only [borrowMarketTail, borrowSharesStoreTail, borrowStoreTail, borrowHealthTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
        (halfWord_bound _ _) hc (Nat.le_of_not_gt hf) rd2)
  have hass := morphoAccrueAssetsAssign p l1 imms evm ⟨3, by decide⟩ "__c7" shares hl1.toMarketLocals hs1
    (by simpa only [hs.env, ← hs.accounts] using hf)
  obtain ⟨k3, C3, rd3⟩ := morphoCheckedAdd128Ok (v := v) (by simp only [borrowMarketTail, borrowSharesStoreTail, borrowStoreTail, borrowHealthTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (halfWord_bound _ _) hc hf rd2
  obtain ⟨a4, k4, C4, rd4⟩ := morphoBorrowMarketSharesStore (v := v) (by omega) hperm (accrueAssetSumClean hf) rd3
  let e1 := storeMarketField evm p.id ⟨3, by decide⟩ (marketFieldWord evm.accountMap evm.executionEnv p.id 3 + shares)
  let σ1 := storeMarketFieldAccounts σ ee p.id ⟨3, by decide⟩ (marketFieldWord σ ee p.id 3 + shares)
  have heq : SourceState s0 ee σ1 e1 := by
    simpa only [e1, σ1, hs.env, ← hs.accounts] using storeMarketField_bridge hs p.id ⟨3, by decide⟩
      (marketFieldWord σ ee p.id 3 + shares)
  have ab2 : StateBlock config { contract := contract, locals := locals, immutables := imms }
      evm (borrowTransition.body.drop 16) { contract := contract, locals := l1, immutables := imms }
      e1 (borrowTransition.body.drop 18) := ab1.step hass
  let rd5 := rd4
  by_cases hca : assets.toNat < 2 ^ 128
  swap
  · exact .reverted (ab2.reverts (morphoToUint128CallReverts assets e1 l1 imms (.var "assets") "__c8"
        (hl1.evalAssets imms e1) (Nat.le_of_not_gt hca)))
      (morphoToUint128Reverts (v := v) (by simp only [borrowMarketTail, borrowSharesStoreTail, borrowStoreTail, borrowHealthTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
        (hm2.alloc64Guard (by decide)) hm2.size (by rw [hm2.free]; exact hm2.lower)
        hm2.errorGap hm2.errorHi (Nat.le_of_not_gt hca) rd5)
  have he2 := morphoToUint128CallOk assets e1 l1 imms (.var "assets") "__c8" (hl1.evalAssets imms e1) hca
  let l2 := l1.insert "__c8" (.int (Int.ofNat assets.toNat))
  have hl2 : MarketTransferLocals p assets shares account receiver l2 := hl1.insert _ _ (by decide) (by decide)
  have ha2 : evalExpr? config { contract := contract, locals := l2, immutables := imms } e1 (.var "__c8") =
      .ok (.int (Int.ofNat assets.toNat)) := by simp only [evalExpr?, l2, store_get_self, EvalResult.ofOption]
  have ab3 : StateBlock config { contract := contract, locals := locals, immutables := imms }
      evm (borrowTransition.body.drop 16) { contract := contract, locals := l2, immutables := imms }
      e1 (borrowTransition.body.drop 19) := ab2.step he2
  obtain ⟨a6, k6, C6, rd6⟩ := morphoToUint128Ok (v := v) (by simp only [borrowMarketTail, borrowSharesStoreTail, borrowStoreTail, borrowHealthTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (hm2.alloc64Guard (by decide)) hca rd5
  have hm6 := hm2.narrow (by decide : 64 ≤ 352 - 64)
  obtain ⟨a7, k7, C7, rd7⟩ := morphoBorrowMarketAssetsReachAdd (v := v) (by omega) rd6
  by_cases hfa : (marketFieldWord σ1 ee p.id 2).toNat + assets.toNat < 2 ^ 128
  swap
  · exact .reverted (ab3.reverts (morphoAccrueAssetsAssignReverts p l2 imms e1 ⟨2, by decide⟩
      "__c8" assets hl2.toMarketLocals ha2 (by simpa only [heq.env, ← heq.accounts] using Nat.le_of_not_gt hfa)))
      (morphoCheckedAdd128Reverts (v := v) (by simp only [borrowMarketTail, borrowSharesStoreTail, borrowStoreTail, borrowHealthTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
        (halfWord_bound _ _) hca (Nat.le_of_not_gt hfa) rd7)
  obtain ⟨k8, C8, rd8⟩ := morphoCheckedAdd128Ok (v := v) (by simp only [borrowMarketTail, borrowSharesStoreTail, borrowStoreTail, borrowHealthTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (halfWord_bound _ _) hca hfa rd7
  have hass2 := morphoAccrueAssetsAssign p l2 imms e1 ⟨2, by decide⟩ "__c8" assets hl2.toMarketLocals ha2
    (by simpa only [heq.env, ← heq.accounts] using hfa)
  let e2 := storeMarketField e1 p.id ⟨2, by decide⟩ (marketFieldWord e1.accountMap e1.executionEnv p.id 2 + assets)
  let σ2 := storeMarketFieldAccounts σ1 ee p.id ⟨2, by decide⟩ (marketFieldWord σ1 ee p.id 2 + assets)
  have heq2 : SourceState s0 ee σ2 e2 := by
    simpa only [e2, σ2, heq.env, ← heq.accounts] using storeMarketField_bridge heq p.id ⟨2, by decide⟩
      (marketFieldWord σ1 ee p.id 2 + assets)
  obtain ⟨a9, k9, C9, rd9⟩ := morphoBorrowStoreHealth (v := v) (by omega) hperm (accrueAssetSumClean hfa) rd8
  have had := ((hm.narrowAdvance.trans (heapAdvance_hash _ _ p.id (UInt256.ofNat 3))).trans
    hm2.narrowAdvance).trans (heapAdvance_hash _ _ p.id (UInt256.ofNat 3))
  refine .ok (ab3.step hass2) hl2 ?_ heq2 (hm6.hash p.id (UInt256.ofNat 3)) ?_ rd9
  · simp only [l2, l1, store_get_ne (k := "__c8") (a := "__memory") _ _ (by decide),
      store_get_ne (k := "__c7") (a := "__memory") _ _ (by decide)]
  · simpa only [Nat.add_zero, Nat.reduceAdd] using had

end Benchmarks.Morpho.MorphoBlue
