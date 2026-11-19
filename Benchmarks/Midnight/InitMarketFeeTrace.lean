import Benchmarks.Midnight.InitMarketFeeMemory

/-! The packed settlement-fee writes during market initialization. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightInitMarketFirstFees {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw root word id tokenPtr : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 11 ≤ 1024) (hperm : I.perm = true)
    (hw : MemoryWords mem root.toNat (initMarketSettlementFeeWords word))
    (rd : RD midnightBytecode I g s0 ⟨21305⟩
      (root :: (root + UInt256.ofNat 32) :: (root + UInt256.ofNat 64) ::
        (root + UInt256.ofNat 96) :: (root + UInt256.ofNat 128) ::
        (root + UInt256.ofNat 160) :: (root + UInt256.ofNat 192) :: tokenPtr ::
        (solcMappingSlot ⟨1⟩ id + ⟨2⟩) :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD midnightBytecode I g s0 ⟨21420⟩
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
  obtain ⟨aw1, k1, C1, rd1⟩ := midnightBlocks.midnight_block_21305_packed hstack hperm rd
  simp only [midnightBlocks.midnight_block_21305_stack, h0, hl1, hl2, hl3, hl4,
    accountStorageWord_fold, hpair, h2, h3] at rd1
  exact ⟨aw1, k1, C1, rd1⟩

theorem midnightInitMarketLastFees {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw root word id tokenPtr : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (token : AccountAddress)
    (hstack : R.length + 7 ≤ 1024) (hperm : I.perm = true)
    (hw : MemoryWords mem root.toNat (initMarketSettlementFeeWords word))
    (htoken : memLoad tokenPtr mem = UInt256.ofNat token.val)
    (rd : RD midnightBytecode I g s0 ⟨21420⟩
      (UInt256.land (UInt256.lnot (UInt256.ofNat 1208907372870555465154560))
        (solcSlotWordAt (solcMappingSlot ⟨1⟩ id + ⟨2⟩)
          (initSettlementAccounts σ I id word 4) I) :: settlementFeeWord word 4 ::
        (root + UInt256.ofNat 160) :: (root + UInt256.ofNat 192) :: tokenPtr ::
        (solcMappingSlot ⟨1⟩ id + ⟨2⟩) :: R)
      mem aw rdata (initSettlementAccounts σ I id word 4) k C) :
    ∃ aw' k' C', RD midnightBytecode I g s0 ⟨21514⟩
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
  obtain ⟨aw1, k1, C1, rd1⟩ := midnightBlocks.midnight_block_21420_packed hstack hperm rd
  simp only [midnightBlocks.midnight_block_21420_stack, midnightBlocks.midnight_block_21420_memory,
    hl5, hl6, htoken, hmask5, hmask6, accountStorageWord_fold, h4, h5, h6,
    addressMask_computed, hclean, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold] at rd1
  exact ⟨aw1, k1, C1, rd1⟩

end Benchmarks.Midnight
