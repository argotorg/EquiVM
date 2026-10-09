import Benchmarks.Morpho.MorphoBlue.LiquidateMarketReach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

inductive LiquidateMarketRefines (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (p : MarketParamsWords) (assets seized shares account srcOff len : UInt256) (data : ByteArray)
    (locals imms : Store) (evm : EVM.State) (mem : ByteArray) (fp : UInt256) (R : List UInt256) : Prop where
  | reverted : ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (liquidateTransition.body.drop 21) .reverted → RDrev (deployedRuntime v) g s0 →
      LiquidateMarketRefines v ee g s0 p assets seized shares account srcOff len data locals imms evm mem fp R
  | ok {locals' evm' σ' mem' fp' aw' out' k' C'} :
      StateBlock config { contract := contract, locals := locals, immutables := imms }
        evm (liquidateTransition.body.drop 21) { contract := contract, locals := locals', immutables := imms }
        evm' (liquidateTransition.body.drop 25) → LiquidateLocals p account seized shares data locals' →
      locals'.get? "__memory" = locals.get? "__memory" →
      locals'.get? "__c14" = some (.int (Int.ofNat (zeroFloorSubWord (marketFieldWord σ' ee p.id 2) assets).toNat)) →
      locals'.get? "repaidAssets" = some (.int (Int.ofNat assets.toNat)) →
      SourceState s0 ee σ' evm' → MorphoHeap mem' fp' 640 → HeapAdvance mem fp mem' fp' 128 →
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 2391)
        (zeroFloorSubWord (marketFieldWord σ' ee p.id 2) assets :: liquidateMarketTail p.id assets seized shares srcOff len R)
        mem' aw' out' σ' k' C' →
      LiquidateMarketRefines v ee g s0 p assets seized shares account srcOff len data locals imms evm mem fp R

theorem morphoLiquidateMarketRefine {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {aw fp assets seized shares account srcOff len : UInt256} {out mem : ByteArray}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (p : MarketParamsWords) (data : ByteArray)
    (locals imms : Store) (hstack : R.length + 40 ≤ 1024) (hperm : ee.perm = true)
    (hl : LiquidateLocals p account seized shares data locals) (hs : SourceState s0 ee σ evm)
    (hassets : locals.get? "repaidAssets" = some (.int (Int.ofNat assets.toNat)))
    (hm : MorphoHeap mem fp 768)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15480)
      ([shares, UInt256.ofNat 2249, UInt256.ofNat 2342] ++ liquidateMarketTail p.id assets seized shares srcOff len R)
      mem aw out σ k C) :
    LiquidateMarketRefines v ee g s0 p assets seized shares account srcOff len data locals imms evm mem fp R := by
  by_cases hc : shares.toNat < 2 ^ 128
  swap
  · exact .reverted (ExecBlock.consRevert (morphoToUint128CallReverts shares evm locals imms
      (.var "repaidShares") "__c13" (hl.evalShares imms evm) (Nat.le_of_not_gt hc)))
      (morphoToUint128Reverts (v := v) (by change R.length + 10 + 16 ≤ 1024; omega)
        (hm.alloc64Guard (by decide)) hm.size (by rw [hm.free]; exact hm.lower)
        hm.errorGap hm.errorHi (Nat.le_of_not_gt hc) h)
  have he1 := morphoToUint128CallOk shares evm locals imms (.var "repaidShares") "__c13" (hl.evalShares imms evm) hc
  let l1 := locals.insert "__c13" (.int (Int.ofNat shares.toNat))
  have hl1 : LiquidateLocals p account seized shares data l1 := hl.insert _ _ (by decide) (by decide)
  have he6 : evalExpr? config { contract := contract, locals := l1, immutables := imms } evm (.var "__c13") =
      .ok (.int (Int.ofNat shares.toNat)) := by simp only [evalExpr?, l1, store_get_self, EvalResult.ofOption]
  have ab1 : StateBlock config { contract := contract, locals := locals, immutables := imms }
      evm (liquidateTransition.body.drop 21) { contract := contract, locals := l1, immutables := imms }
      evm (liquidateTransition.body.drop 22) := StateBlock.start.step he1
  obtain ⟨a1, k1, C1, rd1⟩ := morphoToUint128Ok (v := v) (by change R.length + 10 + 16 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (hm.alloc64Guard (by decide)) hc h
  have hm1 := hm.narrow (by decide : 64 ≤ 768)
  obtain ⟨a2, k2, C2, rd2⟩ := morphoLiquidateMarketSharesReachSub (v := v) (by omega) rd1
  have hm2 := hm1.hash p.id (UInt256.ofNat 3)
  have hb : (marketFieldWord σ ee p.id 3).toNat < 2 ^ 128 := halfWord_bound _ _
  by_cases hf : shares.toNat ≤ (marketFieldWord σ ee p.id 3).toNat
  swap
  · exact .reverted (ab1.reverts (morphoMarketSubtractAssignReverts p l1 imms evm ⟨3, by decide⟩
      "__c13" shares hl1.toMarketLocals he6 (by simpa only [hs.env, ← hs.accounts] using Nat.lt_of_not_ge hf)))
      (morphoCheckedSub128Reverts (v := v) (by change R.length + 11 + 6 ≤ 1024; omega) hb hc (Nat.lt_of_not_ge hf) rd2)
  have hass := morphoMarketSubtractAssign p l1 imms evm ⟨3, by decide⟩ "__c13" shares hl1.toMarketLocals he6
    (by simpa only [hs.env, ← hs.accounts] using hf)
  obtain ⟨k3, C3, rd3⟩ := morphoCheckedSub128Ok (v := v) (by change R.length + 11 + 6 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hb hc hf rd2
  obtain ⟨k4, C4, rd4⟩ := morphoStoreUint128High (v := v) (by change R.length + 9 + 7 ≤ 1024; omega)
    hperm (by rw [morphoPatchedValidJumps v]; jump_dest) (by rw [usub_toNat hf]; omega) rd3
  let e1 := storeMarketField evm p.id ⟨3, by decide⟩ (UInt256.sub (marketFieldWord evm.accountMap evm.executionEnv p.id 3) shares)
  let σ1 := storeMarketFieldAccounts σ ee p.id ⟨3, by decide⟩ (UInt256.sub (marketFieldWord σ ee p.id 3) shares)
  have hs1 : SourceState s0 ee σ1 e1 := by
    simpa only [e1, σ1, hs.env, ← hs.accounts] using storeMarketField_bridge hs p.id ⟨3, by decide⟩
      (UInt256.sub (marketFieldWord σ ee p.id 3) shares)
  have ab2 : StateBlock config { contract := contract, locals := locals, immutables := imms }
      evm (liquidateTransition.body.drop 21) { contract := contract, locals := l1, immutables := imms }
      e1 (liquidateTransition.body.drop 23) := ab1.step hass
  let debt := zeroFloorSubWord (marketFieldWord σ1 ee p.id 2) assets
  have hd : debt.toNat < 2 ^ 128 := by
    dsimp only [debt]
    rw [zeroFloorSubWord_toNat]
    have hh : (marketFieldWord σ1 ee p.id 2).toNat < 2 ^ 128 := halfWord_bound _ _
    omega
  have hes : evalExpr? config { contract := contract, locals := l1, immutables := imms } e1
      (.storage ⟨"market", [.mindex (.var "id"), .field "totalBorrowAssets"]⟩) =
      .ok (.int (Int.ofNat (marketFieldWord σ1 ee p.id 2).toNat)) := by
    simpa only [hs1.env, ← hs1.accounts] using hl1.evalField imms e1 ⟨2, by decide⟩
  have hea : evalExpr? config { contract := contract, locals := l1, immutables := imms } e1
      (.var "repaidAssets") = .ok (.int (Int.ofNat assets.toNat)) := by
    simp only [evalExpr?, l1, store_get_ne _ _ (show ("__c13" == "repaidAssets") = false by decide),
      hassets, EvalResult.ofOption]
  have he2 := morphoZeroFloorSubCall (marketFieldWord σ1 ee p.id 2) assets e1 l1 imms
    [.storage ⟨"market", [.mindex (.var "id"), .field "totalBorrowAssets"]⟩, .var "repaidAssets"] "debtRemaining"
    (by simp only [evalExprs?, hes, hea, pure, bind, EvalResult.bind])
  let l2 := l1.insert "debtRemaining" (.int (Int.ofNat debt.toNat))
  have hl2 : LiquidateLocals p account seized shares data l2 := hl1.insert _ _ (by decide) (by decide)
  have hed : evalExpr? config { contract := contract, locals := l2, immutables := imms } e1 (.var "debtRemaining") =
      .ok (.int (Int.ofNat debt.toNat)) := by simp only [evalExpr?, l2, store_get_self, EvalResult.ofOption]
  have he3 := morphoToUint128CallOk debt e1 l2 imms (.var "debtRemaining") "__c14" hed hd
  obtain ⟨a5, k5, C5, rd5⟩ := morphoLiquidateDebtReachCast (v := v) (by omega) rd4
  have hm5 := hm2.hash p.id (UInt256.ofNat 3)
  obtain ⟨a6, k6, C6, rd6⟩ := morphoToUint128Ok (v := v) (by change R.length + 9 + 16 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (hm5.alloc64Guard (by decide)) hd rd5
  have had := ((hm.narrowAdvance.trans (heapAdvance_hash _ _ p.id (UInt256.ofNat 3))).trans
    (heapAdvance_hash _ _ p.id (UInt256.ofNat 3))).trans hm5.narrowAdvance
  refine .ok ((ab2.step he2).step he3) (hl2.insert "__c14" _ (by decide) (by decide)) ?_
    (store_get_self _ _ _) ?_ hs1 (hm5.narrow (by decide : 64 ≤ 768 - 64)) ?_ rd6
  · simp only [l2, l1, store_get_ne (k := "__c14") (a := "__memory") _ _ (by decide),
      store_get_ne (k := "debtRemaining") (a := "__memory") _ _ (by decide),
      store_get_ne (k := "__c13") (a := "__memory") _ _ (by decide)]
  · simp only [l2, l1, store_get_ne _ _ (show ("__c14" == "repaidAssets") = false by decide),
      store_get_ne _ _ (show ("debtRemaining" == "repaidAssets") = false by decide),
      store_get_ne _ _ (show ("__c13" == "repaidAssets") = false by decide), hassets]
  · simpa only [Nat.add_zero, Nat.reduceAdd] using had

end Benchmarks.Morpho.MorphoBlue
