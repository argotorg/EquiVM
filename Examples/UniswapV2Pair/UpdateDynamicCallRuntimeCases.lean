import Examples.UniswapV2Pair.UpdateCallSource
import Examples.UniswapV2Pair.SyncDynamicRuntime
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem uniswapUpdateCallRuntimeCases_dynamic
    {g : Sat256} {s0 : State} {I : ExecutionEnv} {k C : ℕ}
    {reserve1 reserve0 balance1 balance0 ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw ptr : UInt256} {args : List Expr} {retVar : Ident} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {locals : Store} (evm : EVM.State)
    (rd6959 : RD uniswapV2PairBytecode I g s0 ⟨6959⟩
      (reserve1 :: reserve0 :: balance1 :: balance0 :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hAccounts : accountMapEquiv σ evm.accountMap)
    (henv : evm.executionEnv = I)
    (hargs : evalExprs? config { contract := contract, locals := locals } evm args =
      .ok (syncUpdateCallArgValsWith balance0 balance1 reserve0 reserve1))
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hperm : I.perm = true)
    (hin : 96 ≤ mem.size) (hlo : 96 ≤ ptr.toNat) (hgap : ptr.toNat - mem.size < USize.size)
    (hfit : ptr.toNat + 131 < UInt256.size) (haw : aw.toNat * 32 < UInt256.size)
    (hawLo : 96 ≤ aw.toNat * 32) (hmem64 : mem.readWithPadding 64 32 = ptr.toByteArray)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 21 ≤ 1024) :
    (ExecStmt config { contract := contract, locals := locals } evm
      (.internalCall "_update"
        args
        retVar) .reverted ∧ RDrev uniswapV2PairBytecode g s0) ∨
    (∃ evm' σ' packed k' C',
      ExecStmt config { contract := contract, locals := locals } evm
        (.internalCall "_update"
          args
          retVar)
        (.ok (resumeAfterInternalCall { contract := contract, locals := locals }
          retVar none) evm') ∧
      accountMapEquiv σ' evm'.accountMap ∧ evm'.executionEnv = I ∧
      evm'.createdAccounts = evm.createdAccounts ∧
      RD uniswapV2PairBytecode I g s0 ret R (pairDynamicMem mem ptr (uniswapSyncReserve0Word packed) (uniswapSyncReserve1Word packed))
        (pairDynamicWords aw ptr) rdata (cA, σ') k' C' ∧
      (pairDynamicMem mem ptr (uniswapSyncReserve0Word packed) (uniswapSyncReserve1Word packed)).size = max mem.size (ptr.toNat + 64) ∧
      (pairDynamicMem mem ptr (uniswapSyncReserve0Word packed) (uniswapSyncReserve1Word packed)).readWithPadding 64 32 = ptr.toByteArray) := by
  have hmask : Int.ofNat reserve112Mask.toNat = maxUint112 := by native_decide
  by_cases hb0 : balance0.toNat ≤ reserve112Mask.toNat
  · have hb0S : Int.ofNat balance0.toNat ≤ maxUint112 := by
      rw [← hmask]
      exact Int.ofNat_le.mpr hb0
    by_cases hb1 : balance1.toNat ≤ reserve112Mask.toNat
    · have hb1S : Int.ofNat balance1.toNat ≤ maxUint112 := by
        rw [← hmask]
        exact Int.ofNat_le.mpr hb1
      obtain ⟨_, _, rd7060⟩ := RD.uniswapUpdateOverflowGuardOk rd6959 hb0 hb1
        (by simp only [List.length_cons]; omega)
      have hslot8 : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ =
          uniswapSlotWord ⟨8⟩ σ I := by
        have h := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨8⟩ ⟨0⟩
        simpa only [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
          uniswapSlotWord, henv] using h.symm
      have htime : syncTimeElapsedInt evm = Int.ofNat
          (UInt256.land (uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σ I) I)
            reserve32Mask).toNat := by
        rw [syncTimeElapsedInt_eq_updateElapsedWord_toNat, hslot8, henv]
      by_cases hskip : UInt256.land
          (uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σ I) I) reserve32Mask = ⟨0⟩ ∨
          UInt256.land reserve0 reserve112Mask = ⟨0⟩ ∨
          UInt256.land reserve1 reserve112Mask = ⟨0⟩
      · have hskipS : syncTimeElapsedInt evm = 0 ∨ reserve0 = ⟨0⟩ ∨ reserve1 = ⟨0⟩ := by
          rcases hskip with ht | hr0 | hr1
          · exact Or.inl (by rw [htime, ht]; rfl)
          · exact Or.inr (Or.inl (by rwa [hclean0] at hr0))
          · exact Or.inr (Or.inr (by rwa [hclean1] at hr1))
        obtain ⟨_, _, rd7241⟩ := RD.uniswapUpdateConditionFalseSkipsCumulatives rd7060 hskip
          (by simp only [List.length_cons]; omega)
        obtain ⟨_, _, rd7339⟩ := RD.uniswapUpdateStorePackedReserves rd7241 hperm
          (by simp only [List.length_cons]; omega)
        obtain ⟨kRet, CRet, rdRet⟩ := RD.uniswapUpdateEmitSyncAndJump_dynamic rd7339 hin hlo hgap (by omega) haw hawLo hmem64 hperm
          hret (by omega)
        refine Or.inr ⟨syncUpdatePackedReserveState evm balance0 balance1, _, _, _, _,
          uniswapUpdateCallReturnsConditionFalse evm balance0 balance1
            reserve0 reserve1 hargs hb0S hb1S hskipS,
          accountMapEquiv_syncUpdatePackedReserveState hAccounts henv hslot8 rfl,
          ?_, ?_, rdRet, ?_, ?_⟩
        · simp only [syncUpdatePackedReserveState, storageStore_executionEnv, henv]
        · simp only [syncUpdatePackedReserveState, storageStore_createdAccounts]
        · exact (pairDynamicMem_sizes ptr _ _ hgap (by omega)).2
        · exact (pairDynamicMem_read_below ptr _ _ 64 hin hlo hgap (by omega)).trans hmem64
      · have ht : UInt256.land
            (uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σ I) I) reserve32Mask ≠ ⟨0⟩ :=
          fun h ↦ hskip (Or.inl h)
        have hr0 : UInt256.land reserve0 reserve112Mask ≠ ⟨0⟩ :=
          fun h ↦ hskip (Or.inr (Or.inl h))
        have hr1 : UInt256.land reserve1 reserve112Mask ≠ ⟨0⟩ :=
          fun h ↦ hskip (Or.inr (Or.inr h))
        have htS : 0 < syncTimeElapsedInt evm := by
          rw [htime]
          exact Int.ofNat_lt.mpr (Nat.pos_of_ne_zero (fun hz ↦ ht (uint256_toNat_eq_zero hz)))
        have hr0S : Int.ofNat reserve0.toNat ≠ 0 :=
          intOfNat_toNat_ne_zero_of_u256_ne_zero reserve0 (by rwa [hclean0] at hr0)
        have hr1S : Int.ofNat reserve1.toNat ≠ 0 :=
          intOfNat_toNat_ne_zero_of_u256_ne_zero reserve1 (by rwa [hclean1] at hr1)
        obtain ⟨_, _, rd7241⟩ := RD.uniswapUpdateCumulativesAndJump
          (reserve0 := reserve0) (reserve1 := reserve1) rd7060 ht hr0 hr1 hperm
          (by simp only [List.length_cons]; omega)
        obtain ⟨_, _, rd7339⟩ := RD.uniswapUpdateStorePackedReserves rd7241 hperm
          (by simp only [List.length_cons]; omega)
        obtain ⟨kRet, CRet, rdRet⟩ := RD.uniswapUpdateEmitSyncAndJump_dynamic rd7339 hin hlo hgap (by omega) haw hawLo hmem64 hperm
          hret (by omega)
        refine Or.inr ⟨syncUpdateCumulativePackedReserveStateWith evm balance0 balance1
            reserve0 reserve1,
          uniswapUpdateCumulativePackedMapWith σ I balance0 balance1 reserve0 reserve1,
          uniswapUpdateCumulativePackedWordWith σ I balance0 balance1 reserve0 reserve1, kRet, CRet,
          uniswapUpdateCallReturnsConditionTrue evm balance0 balance1
            reserve0 reserve1 hargs hb0S hb1S htS hr0S hr1S,
          accountMapEquiv_syncUpdateCumulativePackedMapWith hAccounts henv hslot8
            (by rw [← hclean0]; exact reserve112Word_lt _)
            (by rw [← hclean1]; exact reserve112Word_lt _), ?_, ?_, ?_, ?_, ?_⟩
        · simp only [syncUpdateCumulativePackedReserveStateWith,
            storageStore_executionEnv, henv]
        · simp only [syncUpdateCumulativePackedReserveStateWith,
            storageStore_createdAccounts]
        · simpa only [uniswapUpdateCumulativePackedMapWith, uniswapUpdateCumulativePackedWordWith,
            uniswapUpdatePrice1CumulativeMapWith, uniswapUpdatePrice0CumulativeMapWith,
            uniswapUpdateElapsedFromStorage, uniswapUpdateElapsedWord, uniswapUpdateTimestampWord,
            uniswapSlotWord] using rdRet
        · exact (pairDynamicMem_sizes ptr _ _ hgap (by omega)).2
        · exact (pairDynamicMem_read_below ptr _ _ 64 hin hlo hgap (by omega)).trans hmem64
    · exact Or.inl ⟨uniswapUpdateCallRevertsSecondBound evm balance0 balance1
        reserve0 reserve1 hargs hb0S
        (by rw [← hmask]; exact Int.ofNat_lt.mpr (Nat.lt_of_not_ge hb1)),
        RD.uniswapUpdateOverflowReverts_dynamic rd6959 (Or.inr (Nat.lt_of_not_ge hb1))
          hin hlo hgap hfit haw hawLo hmem64 (by simp only [List.length_cons]; omega)⟩
  · exact Or.inl ⟨uniswapUpdateCallRevertsFirstBound evm balance0 balance1
      reserve0 reserve1 hargs
      (by rw [← hmask]; exact Int.ofNat_lt.mpr (Nat.lt_of_not_ge hb0)),
      RD.uniswapUpdateOverflowReverts_dynamic rd6959 (Or.inl (Nat.lt_of_not_ge hb0))
        hin hlo hgap hfit haw hawLo hmem64 (by simp only [List.length_cons]; omega)⟩

end UniswapV2Pair
