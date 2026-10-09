import Benchmarks.Morpho.MorphoBlue.SupplyMarketReach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

inductive SupplyMarketRefines (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (p : MarketParamsWords) (assets shares account srcOff len : UInt256) (data : ByteArray)
    (locals imms : Store) (evm : EVM.State) (mem : ByteArray) (fp : UInt256) (R : List UInt256) : Prop where
  | reverted : ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (supplyTransition.body.drop 13) .reverted → RDrev (deployedRuntime v) g s0 →
      SupplyMarketRefines v ee g s0 p assets shares account srcOff len data locals imms evm mem fp R
  | ok {locals' evm' σ' mem' fp' aw' out' k' C'} :
      StateBlock config { contract := contract, locals := locals, immutables := imms }
        evm (supplyTransition.body.drop 13) { contract := contract, locals := locals', immutables := imms }
        evm' (supplyTransition.body.drop 16) → SupplyLocals p assets shares account data locals' →
      locals'.get? "__memory" = locals.get? "__memory" →
      locals'.get? "__c6" = some (.int (Int.ofNat assets.toNat)) →
      SourceState s0 ee σ' evm' → MorphoHeap mem' fp' 160 → HeapAdvance mem fp mem' fp' 128 →
      (marketFieldWord σ' ee p.id 0).toNat + assets.toNat < 2 ^ 128 →
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 4124)
        ((marketFieldWord σ' ee p.id 0 + assets) :: supplyStoreTail σ' ee p.id assets shares account srcOff len R)
        mem' aw' out' σ' k' C' →
      SupplyMarketRefines v ee g s0 p assets shares account srcOff len data locals imms evm mem fp R

theorem morphoSupplyMarketRefine {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {aw fp assets shares account srcOff len : UInt256} {out mem : ByteArray}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (p : MarketParamsWords) (data : ByteArray)
    (locals imms : Store) (hstack : R.length + 32 ≤ 1024) (hperm : ee.perm = true)
    (hl : SupplyLocals p assets shares account data locals) (hs : SourceState s0 ee σ evm)
    (hm : MorphoHeap mem fp 288)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15480)
      ([shares, UInt256.ofNat 4031, UInt256.ofNat 4056] ++ supplyUpdateTail p.id assets shares account srcOff len R)
      mem aw out σ k C) :
    SupplyMarketRefines v ee g s0 p assets shares account srcOff len data locals imms evm mem fp R := by
  by_cases hc : shares.toNat < 2 ^ 128
  swap
  · exact .reverted (ExecBlock.consRevert (morphoToUint128CallReverts shares evm locals imms
      (.var "shares") "__c5" (hl.evalShares imms evm) (Nat.le_of_not_gt hc)))
      (morphoToUint128Reverts (v := v) (by change R.length + 12 + 16 ≤ 1024; omega)
        (hm.alloc64Guard (by decide)) hm.size (by rw [hm.free]; exact hm.lower)
        hm.errorGap hm.errorHi (Nat.le_of_not_gt hc) h)
  have he1 := morphoToUint128CallOk shares evm locals imms (.var "shares") "__c5" (hl.evalShares imms evm) hc
  let l1 := locals.insert "__c5" (.int (Int.ofNat shares.toNat))
  have hl1 : SupplyLocals p assets shares account data l1 := hl.insert _ _ (by decide) (by decide)
  have hs1 : evalExpr? config { contract := contract, locals := l1, immutables := imms } evm (.var "__c5") =
      .ok (.int (Int.ofNat shares.toNat)) := by simp only [evalExpr?, l1, store_get_self, EvalResult.ofOption]
  have ab1 : StateBlock config { contract := contract, locals := locals, immutables := imms }
      evm (supplyTransition.body.drop 13) { contract := contract, locals := l1, immutables := imms }
      evm (supplyTransition.body.drop 14) := StateBlock.start.step he1
  obtain ⟨a1, k1, C1, rd1⟩ := morphoToUint128Ok (v := v) (by change R.length + 12 + 16 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (hm.alloc64Guard (by decide)) hc h
  have hm1 := hm.narrow (by decide : 64 ≤ 288)
  obtain ⟨a2, k2, C2, rd2⟩ := morphoSupplyMarketSharesReachAdd (v := v) (by omega) rd1
  have hm2 := hm1.hash p.id (UInt256.ofNat 3)
  by_cases hf : (marketFieldWord σ ee p.id 1).toNat + shares.toNat < 2 ^ 128
  swap
  · exact .reverted (ab1.reverts (morphoAccrueAssetsAssignReverts p l1 imms evm ⟨1, by decide⟩
      "__c5" shares hl1.toMarketLocals hs1 (by simpa only [hs.env, ← hs.accounts] using Nat.le_of_not_gt hf)))
      (morphoCheckedAdd128Reverts (v := v) (by change R.length + 13 + 6 ≤ 1024; omega)
        (halfWord_bound _ _) hc (Nat.le_of_not_gt hf) rd2)
  have hass := morphoAccrueAssetsAssign p l1 imms evm ⟨1, by decide⟩ "__c5" shares hl1.toMarketLocals hs1
    (by simpa only [hs.env, ← hs.accounts] using hf)
  obtain ⟨k3, C3, rd3⟩ := morphoCheckedAdd128Ok (v := v) (by change R.length + 13 + 6 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (halfWord_bound _ _) hc hf rd2
  obtain ⟨k4, C4, rd4⟩ := morphoStoreUint128High (v := v) (by change R.length + 11 + 7 ≤ 1024; omega)
    hperm (by rw [morphoPatchedValidJumps v]; jump_dest) (accrueAssetSumClean hf) rd3
  let e1 := storeMarketField evm p.id ⟨1, by decide⟩ (marketFieldWord evm.accountMap evm.executionEnv p.id 1 + shares)
  let σ1 := storeMarketFieldAccounts σ ee p.id ⟨1, by decide⟩ (marketFieldWord σ ee p.id 1 + shares)
  have heq : SourceState s0 ee σ1 e1 := by
    simpa only [e1, σ1, hs.env, ← hs.accounts] using storeMarketField_bridge hs p.id ⟨1, by decide⟩
      (marketFieldWord σ ee p.id 1 + shares)
  have ab2 : StateBlock config { contract := contract, locals := locals, immutables := imms }
      evm (supplyTransition.body.drop 13) { contract := contract, locals := l1, immutables := imms }
      e1 (supplyTransition.body.drop 15) := ab1.step hass
  have rd5 := morphoBlocks.morpho_block_4056 (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 13 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd4
  by_cases hca : assets.toNat < 2 ^ 128
  swap
  · exact .reverted (ab2.reverts (morphoToUint128CallReverts assets e1 l1 imms (.var "assets") "__c6"
        (hl1.evalAssets imms e1) (Nat.le_of_not_gt hca)))
      (morphoToUint128Reverts (v := v) (by change R.length + 11 + 16 ≤ 1024; omega)
        (hm2.alloc64Guard (by decide)) hm2.size (by rw [hm2.free]; exact hm2.lower)
        hm2.errorGap hm2.errorHi (Nat.le_of_not_gt hca) rd5)
  have he2 := morphoToUint128CallOk assets e1 l1 imms (.var "assets") "__c6" (hl1.evalAssets imms e1) hca
  let l2 := l1.insert "__c6" (.int (Int.ofNat assets.toNat))
  have hl2 : SupplyLocals p assets shares account data l2 := hl1.insert _ _ (by decide) (by decide)
  have ha2 : evalExpr? config { contract := contract, locals := l2, immutables := imms } e1 (.var "__c6") =
      .ok (.int (Int.ofNat assets.toNat)) := by simp only [evalExpr?, l2, store_get_self, EvalResult.ofOption]
  have ab3 : StateBlock config { contract := contract, locals := locals, immutables := imms }
      evm (supplyTransition.body.drop 13) { contract := contract, locals := l2, immutables := imms }
      e1 (supplyTransition.body.drop 16) := ab2.step he2
  obtain ⟨a6, k6, C6, rd6⟩ := morphoToUint128Ok (v := v) (by change R.length + 11 + 16 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (hm2.alloc64Guard (by decide)) hca rd5
  have hm6 := hm2.narrow (by decide : 64 ≤ 288 - 64)
  obtain ⟨a7, k7, C7, rd7⟩ := morphoSupplyMarketAssetsReachAdd (v := v) (by omega) rd6
  by_cases hfa : (marketFieldWord σ1 ee p.id 0).toNat + assets.toNat < 2 ^ 128
  swap
  · exact .reverted (ab3.reverts (morphoAccrueAssetsAssignReverts p l2 imms e1 ⟨0, by decide⟩
      "__c6" assets hl2.toMarketLocals ha2 (by simpa only [heq.env, ← heq.accounts] using Nat.le_of_not_gt hfa)))
      (morphoCheckedAdd128Reverts (v := v) (by change R.length + 14 + 6 ≤ 1024; omega)
        (halfWord_bound _ _) hca (Nat.le_of_not_gt hfa) rd7)
  obtain ⟨k8, C8, rd8⟩ := morphoCheckedAdd128Ok (v := v) (by change R.length + 14 + 6 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (halfWord_bound _ _) hca hfa rd7
  have had := ((hm.narrowAdvance.trans (heapAdvance_hash _ _ p.id (UInt256.ofNat 3))).trans
    hm2.narrowAdvance).trans (heapAdvance_hash _ _ p.id (UInt256.ofNat 3))
  refine .ok ab3 hl2 ?_ (store_get_self _ _ _) heq (hm6.hash p.id (UInt256.ofNat 3)) ?_ hfa rd8
  · simp only [l2, l1, store_get_ne (k := "__c6") (a := "__memory") _ _ (by decide),
      store_get_ne (k := "__c5") (a := "__memory") _ _ (by decide)]
  · simpa only [Nat.add_zero, Nat.reduceAdd] using had

end Benchmarks.Morpho.MorphoBlue
