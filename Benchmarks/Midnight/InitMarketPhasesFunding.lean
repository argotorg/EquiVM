import Benchmarks.Midnight.InitMarketStorageTrace
import Benchmarks.Midnight.InitMarketStorageFundingBlocks
import Benchmarks.Midnight.AllocationFunding

variable {fork : Ethereum.Fork}

/-! Funded summaries for the fresh-market initialization phases. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight
set_option maxRecDepth 10000

-- GENERALIZES midnightInitMarketTick with retained funding.
theorem midnightInitMarketTick_funded {credit : Nat} {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr arrayPtr limit root id ret previous count : UInt256}
    {k C : Nat} {R : List UInt256} (m : MarketData)
    (hstack : R.length + 9 ≤ 1024) (hm : MarketStored mem ptr arrayPtr limit m)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hperm : evm.executionEnv.perm = true)
    (hfund : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode evm.executionEnv g s0 ⟨21130⟩
      (arrayPtr :: previous :: ret :: ptr :: (ptr + UInt256.ofNat 96) :: id :: count :: R)
      mem aw rdata evm.accountMap k C) :
    ∃ aw' k' C', MemoryFunding credit (writeWord (initMarketScratch mem id m.loanToken) root.toNat
        (settlementFeeWord (initMarketDefaultWord evm id m.loanToken) 0)) aw' C' ∧ RD fork midnightBytecode evm.executionEnv g s0 ⟨21213⟩
      (initMarketDefaultWord evm id m.loanToken :: (root + UInt256.ofNat 32) :: root ::
        initMarketDefaultWord evm id m.loanToken :: (ptr + UInt256.ofNat 64) ::
        (solcMappingSlot ⟨1⟩ id + ⟨2⟩) :: ptr :: id :: ret :: R)
      (writeWord (initMarketScratch mem id m.loanToken) root.toNat
        (settlementFeeWord (initMarketDefaultWord evm id m.loanToken) 0))
      aw' rdata (initMarketTick evm id).accountMap k' C' := by
  have hlo := hm.lower
  have hsz := hm.words.size
  have hb := hm.words.bound
  change ptr.toNat + 32 * 8 ≤ mem.size at hsz
  change ptr.toNat + 32 * 8 < UInt256.size at hb
  have hmem : 96 ≤ mem.size := by omega
  have hp64 : (ptr + UInt256.ofNat 64).toNat = ptr.toNat + 64 :=
    uadd_word_ofNat_toNat _ _ (by omega)
  have hh1 : keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 1) mem) =
      solcMappingSlot ⟨1⟩ id := twoWordHashMem_mapSlot_of_ge64 _ _ (by omega)
  have hloan : memLoad (ptr + UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 1) mem) =
      UInt256.ofNat m.loanToken.val := by
    rw [memLoad_twoWordHashMem _ _ _ (by rw [hp64]; omega) (by rw [hp64]; omega)]
    exact hm.loanToken
  have hclean : UInt256.land solcAddrMask (UInt256.ofNat m.loanToken.val) =
      UInt256.ofNat m.loanToken.val := by
    rw [u256_land_comm]
    exact solcAddrMask_clean (addressWord_val_canonical m.loanToken)
  have hsize1 : (twoWordHashMem id (UInt256.ofNat 1) mem).size = mem.size :=
    twoWordHashMem_size_of_ge_64 _ _ (by omega)
  have hh4 : keccakWord ⟨0⟩ (UInt256.ofNat 64)
      (twoWordHashMem (UInt256.ofNat m.loanToken.val) (UInt256.ofNat 4)
        (twoWordHashMem id (UInt256.ofNat 1) mem)) =
      solcMappingSlot ⟨4⟩ (UInt256.ofNat m.loanToken.val) :=
    twoWordHashMem_mapSlot_of_ge64 _ _ (by rw [hsize1]; omega)
  have hf : memLoad (UInt256.ofNat 64)
      (twoWordHashMem (UInt256.ofNat m.loanToken.val) (UInt256.ofNat 4)
        (twoWordHashMem id (UInt256.ofNat 1) mem)) = root := by
    rw [memLoad_twoWordHashMem _ _ _ (by decide) (by rw [hsize1]; exact hmem),
      memLoad_twoWordHashMem id (UInt256.ofNat 1) (UInt256.ofNat 64) (by decide) hmem, hfree]
  obtain ⟨aw1, k1, C1, hfund1, rd1⟩ := midnight_block_21130_funded hstack hperm hfund rd
  simp only [midnightBlocks.midnight_block_21130_stack,
    midnightBlocks.midnight_block_21130_memory, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold,
    hh1, hloan, addressMask_computed, hclean, hh4, hf, initMarketTickWord,
    u256_add_comm (UInt256.ofNat 2)] at rd1 hfund1
  have hac : sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap
      (solcMappingSlot ⟨1⟩ id + ⟨2⟩) (setUint8Offset18Word (marketFeeWord evm id) ⟨4⟩) =
      (initMarketTick evm id).accountMap := by
    rw [initMarketTick, storageStore_accountMap]
  refine ⟨aw1, k1, C1, ?_, ?_⟩
  · simpa only [initMarketDefaultWord, initMarketScratch, settlementFeeWord_zero,
      initMarketTick, storageStore_accountMap, marketFeeWord,
      Stele.EVM.storageLoad, State.lookupAccount, storageStore_executionEnv,
      solcSlotWordAt, solcSlotWord, Reasoning.Theory.writeWord] using hfund1
  · simpa only [initMarketDefaultWord, initMarketScratch, settlementFeeWord_zero,
      initMarketTick, storageStore_accountMap, marketFeeWord,
      Stele.EVM.storageLoad, State.lookupAccount, storageStore_executionEnv,
      solcSlotWordAt, solcSlotWord, Reasoning.Theory.writeWord] using rd1

-- GENERALIZES midnightInitMarketFeeCopy with retained funding.
theorem midnightInitMarketFeeCopy_funded {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw root word : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 13 ≤ 1024)
    (hb : root.toNat + 224 < 2^64)
    (hfund : MemoryFunding credit
      (writeWord mem root.toNat (settlementFeeWord word 0)) aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨21213⟩
      (word :: (root + UInt256.ofNat 32) :: root :: word :: R)
      (writeWord mem root.toNat (settlementFeeWord word 0)) aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit (initMarketFeeMemory mem root word) aw' C' ∧ RD fork midnightBytecode I g s0 ⟨21305⟩
      (root :: (root + UInt256.ofNat 32) :: (root + UInt256.ofNat 64) ::
        (root + UInt256.ofNat 96) :: (root + UInt256.ofNat 128) ::
        (root + UInt256.ofNat 160) :: (root + UInt256.ofNat 192) :: R)
      (initMarketFeeMemory mem root word) aw' rdata σ k' C' := by
  have hp (n : Nat) (hn : n ≤ 224) : (root + UInt256.ofNat n).toNat = root.toNat + n :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  have rd1 := midnightBlocks.midnight_block_21213 (by omega) (by jump_dest) rd
  have hfund1 := memoryFundingAt (credit := credit) rd1 (by
    unfold midnightBlocks.midnight_block_21213_memory
    memory_fund hfund)
  simp only [midnightBlocks.midnight_block_21213_stack] at rd1
  have hmemory : midnightBlocks.midnight_block_21213_memory
      (mem := writeWord mem root.toNat (settlementFeeWord word 0))
      (x0 := word) (x1 := root + UInt256.ofNat 32) (x2 := root) (x3 := word) =
      writeWordArray mem root.toNat (initMarketSettlementFeeWords word) := by
    simp only [midnightBlocks.midnight_block_21213_memory, initMarketSettlementFeeWords, writeWordArray,
      settlementFeeWord, u256_land_comm (UInt256.ofNat 65535), hp 32 (by omega),
      hp 64 (by omega), hp 96 (by omega), hp 128 (by omega), hp 160 (by omega), hp 192 (by omega),
      Nat.add_assoc, Nat.reduceAdd]
    rfl
  rw [hmemory] at rd1 hfund1
  have he : allocationEnd root (UInt256.ofNat 224) = root + UInt256.ofNat 224 := by
    unfold allocationEnd
    rfl
  have hc : allocationCheck root (allocationEnd root (UInt256.ofNat 224)) = ⟨0⟩ := by
    rw [he]
    exact allocationCheck_ok (by rw [hp 224 le_rfl]; exact hb) (by rw [hp 224 le_rfl]; omega)
  obtain ⟨aw2, k2, C2, hfund2, rd2⟩ := midnightAllocate_funded (by simp only [List.length_cons]; omega)
    hc (by jump_dest) hfund1 rd1
  rw [he] at rd2 hfund2
  exact ⟨aw2, k2, C2, hfund2, rd2⟩

-- GENERALIZES the settlement-fee writes with retained funding.
theorem midnightInitMarketFirstFees_funded {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw root word id tokenPtr : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 11 ≤ 1024) (hperm : I.perm = true)
    (hw : MemoryWords mem root.toNat (initMarketSettlementFeeWords word))
    (hfund : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨21305⟩
      (root :: (root + UInt256.ofNat 32) :: (root + UInt256.ofNat 64) ::
        (root + UInt256.ofNat 96) :: (root + UInt256.ofNat 128) ::
        (root + UInt256.ofNat 160) :: (root + UInt256.ofNat 192) :: tokenPtr ::
        (solcMappingSlot ⟨1⟩ id + ⟨2⟩) :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit mem aw' C' ∧ RD fork midnightBytecode I g s0 ⟨21420⟩
      (UInt256.land (UInt256.lnot (UInt256.ofNat 1208907372870555465154560))
        (solcSlotWordAt (solcMappingSlot ⟨1⟩ id + ⟨2⟩)
          (initSettlementAccounts σ I id word 4) I) :: settlementFeeWord word 4 ::
        (root + UInt256.ofNat 160) :: (root + UInt256.ofNat 192) :: tokenPtr ::
        (solcMappingSlot ⟨1⟩ id + ⟨2⟩) :: R)
      mem aw' rdata (initSettlementAccounts σ I id word 4) k' C' := by
  have h0 : memLoad root mem = settlementFeeWord word 0 :=
    hw.load_word ⟨0, by simp [initMarketSettlementFeeWords]⟩ (by simp)
  have hload (i : Fin 7) : memLoad (root + UInt256.ofNat (32 * i.val)) mem =
      settlementFeeWord word i.val :=
    (hw.load_offset ⟨i.val, i.isLt⟩ rfl).trans (initMarketSettlementFeeWords_get word i)
  have hl1 : memLoad (root + UInt256.ofNat 32) mem = settlementFeeWord word 1 := hload 1
  have hl2 : memLoad (root + UInt256.ofNat 64) mem = settlementFeeWord word 2 := hload 2
  have hl3 : memLoad (root + UInt256.ofNat 96) mem = settlementFeeWord word 3 := hload 3
  have hl4 : memLoad (root + UInt256.ofNat 128) mem = settlementFeeWord word 4 := hload 4
  have hpair (τ : AccountMap) :
      sstoreAccountMap I.codeOwner τ (solcMappingSlot ⟨1⟩ id + ⟨2⟩)
        (UInt256.lor (UInt256.land (UInt256.ofNat 4294901760)
          (UInt256.shiftLeft (settlementFeeWord word 1) (UInt256.ofNat 16)))
          (UInt256.lor (UInt256.land (settlementFeeWord word 0) (UInt256.ofNat 65535))
            (UInt256.land (solcSlotWordAt (solcMappingSlot ⟨1⟩ id + ⟨2⟩) τ I)
              (UInt256.lnot (UInt256.ofNat 4294967295))))) =
        initSettlementAccounts τ I id word 2 :=
    storeSettlementFee_pair τ I id _ _ (settlementFeeWord_lt word 1)
  have h2 (τ : AccountMap) := storeSettlementFee_solc τ I id (settlementFeeWord word 2) 2
    (settlementFeeWord_lt word 2)
  have h3 (τ : AccountMap) := storeSettlementFee_solc τ I id (settlementFeeWord word 3) 3
    (settlementFeeWord_lt word 3)
  norm_num only [show (2 : Fin 7).val = 2 from rfl,
    show (3 : Fin 7).val = 3 from rfl, Nat.reduceMul, Nat.reducePow] at h2 h3
  obtain ⟨aw1, k1, C1, hfund1, rd1⟩ := midnight_block_21305_funded hstack hperm hfund rd
  simp only [midnightBlocks.midnight_block_21305_stack, h0, hl1, hl2, hl3, hl4,
    accountStorageWord_fold, hpair, h2, h3] at rd1 hfund1
  exact ⟨aw1, k1, C1, hfund1, rd1⟩

-- GENERALIZES the settlement-fee writes with retained funding.
theorem midnightInitMarketLastFees_funded {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw root word id tokenPtr : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (token : AccountAddress)
    (hstack : R.length + 7 ≤ 1024) (hperm : I.perm = true)
    (hw : MemoryWords mem root.toNat (initMarketSettlementFeeWords word))
    (htoken : memLoad tokenPtr mem = UInt256.ofNat token.val)
    (hfund : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨21420⟩
      (UInt256.land (UInt256.lnot (UInt256.ofNat 1208907372870555465154560))
        (solcSlotWordAt (solcMappingSlot ⟨1⟩ id + ⟨2⟩)
          (initSettlementAccounts σ I id word 4) I) :: settlementFeeWord word 4 ::
        (root + UInt256.ofNat 160) :: (root + UInt256.ofNat 192) :: tokenPtr ::
        (solcMappingSlot ⟨1⟩ id + ⟨2⟩) :: R)
      mem aw rdata (initSettlementAccounts σ I id word 4) k C) :
    ∃ aw' k' C', MemoryFunding credit
      (twoWordHashMem (UInt256.ofNat token.val) (UInt256.ofNat 5) mem) aw' C' ∧ RD fork midnightBytecode I g s0 ⟨21514⟩
      (⟨0⟩ :: (solcMappingSlot ⟨1⟩ id + ⟨2⟩) :: R)
      (twoWordHashMem (UInt256.ofNat token.val) (UInt256.ofNat 5) mem)
      aw' rdata (initSettlementAccounts σ I id word 7) k' C' := by
  have hl5 : memLoad (root + UInt256.ofNat 160) mem = settlementFeeWord word 5 :=
    (hw.load_offset ⟨5, by simp [initMarketSettlementFeeWords]⟩ rfl).trans (initMarketSettlementFeeWords_get word 5)
  have hl6 : memLoad (root + UInt256.ofNat 192) mem = settlementFeeWord word 6 :=
    (hw.load_offset ⟨6, by simp [initMarketSettlementFeeWords]⟩ rfl).trans (initMarketSettlementFeeWords_get word 6)
  have h4 (τ : AccountMap) := storeSettlementFee_solc τ I id (settlementFeeWord word 4) 4
    (settlementFeeWord_lt word 4)
  have h5 (τ : AccountMap) := storeSettlementFee_solc τ I id (settlementFeeWord word 5) 5
    (settlementFeeWord_lt word 5)
  have h6 (τ : AccountMap) := storeSettlementFee_solc τ I id (settlementFeeWord word 6) 6
    (settlementFeeWord_lt word 6)
  norm_num only [show (4 : Fin 7).val = 4 from rfl, show (5 : Fin 7).val = 5 from rfl,
    show (6 : Fin 7).val = 6 from rfl, Nat.reduceMul, Nat.reducePow] at h4 h5 h6
  have hmask5 : UInt256.shiftLeft (UInt256.ofNat 65535) (UInt256.ofNat 80) =
      UInt256.ofNat 79226953588444722964369244160 := by decide
  have hmask6 : UInt256.shiftLeft (UInt256.ofNat 65535) (UInt256.ofNat 96) =
      UInt256.ofNat 5192217630372313364192902785269760 := by decide
  have hclean : UInt256.land solcAddrMask (UInt256.ofNat token.val) = UInt256.ofNat token.val := by
    rw [u256_land_comm]
    exact solcAddrMask_clean (addressWord_val_canonical token)
  obtain ⟨aw1, k1, C1, hfund1, rd1⟩ := midnight_block_21420_funded hstack hperm hfund rd
  simp only [midnightBlocks.midnight_block_21420_stack, midnightBlocks.midnight_block_21420_memory,
    hl5, hl6, htoken, hmask5, hmask6, accountStorageWord_fold, h4, h5, h6,
    addressMask_computed, hclean, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold] at rd1 hfund1
  exact ⟨aw1, k1, C1, hfund1, rd1⟩

-- GENERALIZES midnightInitMarketContinuous with retained funding.
theorem midnightInitMarketContinuous_funded {credit : Nat} {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw id : UInt256} {k C : Nat} {R : List UInt256}
    (token : AccountAddress) (hstack : R.length + 5 ≤ 1024)
    (hmem : 64 ≤ mem.size) (hperm : evm.executionEnv.perm = true)
    (hfund : MemoryFunding credit
      (twoWordHashMem (UInt256.ofNat token.val) (UInt256.ofNat 5) mem) aw C)
    (rd : RD fork midnightBytecode evm.executionEnv g s0 ⟨21514⟩
      (⟨0⟩ :: (solcMappingSlot ⟨1⟩ id + ⟨2⟩) :: R)
      (twoWordHashMem (UInt256.ofNat token.val) (UInt256.ofNat 5) mem)
      aw rdata evm.accountMap k C) :
    ∃ aw' k' C', MemoryFunding credit
      (twoWordHashMem (UInt256.ofNat token.val) (UInt256.ofNat 5) mem) aw' C' ∧ RD fork midnightBytecode evm.executionEnv g s0 ⟨24347⟩
      (UInt256.ofNat 21556 :: R)
      (twoWordHashMem (UInt256.ofNat token.val) (UInt256.ofNat 5) mem)
      aw' rdata (initMarketContinuous evm id token).accountMap k' C' := by
  have hh : keccakWord ⟨0⟩ (UInt256.ofNat 64)
      (twoWordHashMem (UInt256.ofNat token.val) (UInt256.ofNat 5) mem) =
      solcMappingSlot ⟨5⟩ (UInt256.ofNat token.val) := twoWordHashMem_mapSlot_of_ge64 _ _ hmem
  obtain ⟨aw1, k1, C1, hfund1, rd1⟩ := midnight_block_21514_funded hstack hperm (by jump_dest) hfund rd
  simp only [midnightBlocks.midnight_block_21514_stack, hh, initMarketContinuousWord,
    accountStorageWord_fold] at rd1
  refine ⟨aw1, k1, C1, hfund1, ?_⟩
  simpa only [initMarketContinuous, marketFeeWord, storageStore_accountMap,
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv _ rfl] using rd1


end Benchmarks.Midnight
