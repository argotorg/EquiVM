import Benchmarks.Midnight.ToMarketCopy
import Benchmarks.Midnight.MarketDecode
import Benchmarks.Midnight.MemoryDecodeBounds

/-! Matching the stored-market decoder's root-offset and fixed-header checks. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightToMarketDecodeHeader {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {aw id : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hsmall : (extCodeSizeWord σ id).toNat < 2^64)
    (rd : RD midnightBytecode I g s0 ⟨900⟩ (⟨1088⟩ :: ⟨1120⟩ :: R)
      (toMarketCodeMemory σ id) aw rdata σ k C) :
    (config.externalABI.decodeValue? Model.marketABI (externalCodePrefix σ id) = none ∧
      RDrev midnightBytecode g s0) ∨
    (32 ≤ (extCodeSizeWord σ id).toNat ∧
      (calldataWord (externalCodePrefix σ id) 0).toNat < 2^64 ∧
      (calldataWord (externalCodePrefix σ id) 0).toNat + 256 ≤ (extCodeSizeWord σ id).toNat ∧
      ∃ aw' k' C', RD midnightBytecode I g s0 ⟨949⟩
        (((⟨1088⟩ + extCodeSizeWord σ id) + ⟨32⟩) ::
          (⟨1088⟩ + extCodeSizeWord σ id) ::
          (⟨1088⟩ + calldataWord (externalCodePrefix σ id) 0) :: R)
        (toMarketCodeMemory σ id) aw' rdata σ k' C') := by
  have hlen : memLoad ⟨1088⟩ (toMarketCodeMemory σ id) = extCodeSizeWord σ id :=
    (toMarketCodeMemory_properties σ id).1
  have hbytes := externalCodePrefix_size σ id
  have hsize : (externalCodePrefix σ id).size < 2^255 := by rw [hbytes]; omega
  by_cases hshort : (extCodeSizeWord σ id).toNat < 32
  · left
    refine ⟨decodeMarketRoot_short (by rw [hbytes]; exact hshort), ?_⟩
    have hc : UInt256.slt (UInt256.sub (⟨1088⟩ + extCodeSizeWord σ id) ⟨1088⟩)
        (UInt256.ofNat 32) = ⟨1⟩ := by
      simpa only [u256_ofNat_toNat] using solcReturnStaticLenCheckShort
        (base := 1088) (len := (extCodeSizeWord σ id).toNat) (words := 1)
        hshort (by decide) (by change _ < 2^256; omega) (by decide)
    have rd1 := midnightBlocks.midnight_block_900_taken
      (by omega) (by rw [hlen, hc]; decide) (by jump_dest) rd
    exact midnightBlocks.midnight_block_712 (by
      simp only [midnightBlocks.midnight_block_900_taken_stack, List.length_cons]; omega) rd1
  have h32 : 32 ≤ (extCodeSizeWord σ id).toNat := by omega
  have hc : UInt256.slt (UInt256.sub (⟨1088⟩ + extCodeSizeWord σ id) ⟨1088⟩)
      (UInt256.ofNat 32) = ⟨0⟩ := by
    simpa only [u256_ofNat_toNat] using solcReturnStaticLenCheckOk
      (base := 1088) (len := (extCodeSizeWord σ id).toNat) (words := 1)
      h32 (by omega) (by decide) (by change _ < 2^256; omega)
  have rd1 := midnightBlocks.midnight_block_900_fallthrough
    (by omega) (by rw [hlen]; exact hc) rd
  simp only [midnightBlocks.midnight_block_900_fallthrough_stack, hlen] at rd1
  have hroot : memLoad ⟨1120⟩ (toMarketCodeMemory σ id) =
      calldataWord (externalCodePrefix σ id) 0 := by
    exact (toMarketCodeMemory_bytes σ id hsmall).load (by rw [hbytes]; exact h32)
  by_cases hoff : (calldataWord (externalCodePrefix σ id) 0).toNat < 2^64
  · have hg : UInt256.gt (memLoad ⟨1120⟩ (toMarketCodeMemory σ id))
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1)) =
        ⟨0⟩ := by
      rw [hroot]; apply ugt_zero
      change _ ≤ 18446744073709551615
      omega
    have rd2 := midnightBlocks.midnight_block_920_fallthrough
      (by simp only [List.length_cons]; omega) hg rd1
    simp only [midnightBlocks.midnight_block_920_fallthrough_stack, hroot] at rd2
    have he : (⟨1088⟩ + extCodeSizeWord σ id).toNat =
        1088 + (extCodeSizeWord σ id).toNat := by
      rw [uadd_toNat]
      exact Nat.mod_eq_of_lt (by change 1088 + _ < 2^256; omega)
    have ho : (⟨1088⟩ + calldataWord (externalCodePrefix σ id) 0).toNat =
        1088 + (calldataWord (externalCodePrefix σ id) 0).toNat := by
      rw [uadd_toNat]
      exact Nat.mod_eq_of_lt (by change 1088 + _ < 2^256; omega)
    have hcheck := memoryDecodeCheck (finish := ⟨1088⟩ + extCodeSizeWord σ id)
      (start := ⟨1088⟩ + calldataWord (externalCodePrefix σ id) 0) (need := 256)
      (by rw [he]; omega) (by rw [ho]; omega) (by decide)
    rw [he, ho] at hcheck
    by_cases hhead : (calldataWord (externalCodePrefix σ id) 0).toNat + 256 ≤
        (extCodeSizeWord σ id).toNat
    · right
      refine ⟨h32, hoff, hhead, ?_⟩
      rw [decide_eq_false (by omega)] at hcheck
      have rd3 := midnightBlocks.midnight_block_936_fallthrough
        (by omega) hcheck rd2
      exact ⟨_, _, _, rd3⟩
    · left
      refine ⟨decodeMarketRoot_shortHead hsize (by rw [hbytes]; exact h32) hoff
        (by rw [hbytes]; omega), ?_⟩
      rw [decide_eq_true (by omega)] at hcheck
      have rd3 := midnightBlocks.midnight_block_936_taken
        (by omega) (by rw [hcheck]; decide) (by jump_dest) rd2
      exact midnightBlocks.midnight_block_712 (by
        simp only [midnightBlocks.midnight_block_936_taken_stack, List.length_cons]; omega) rd3
  · left
    refine ⟨decodeMarketRoot_largeOffset hsize (by rw [hbytes]; exact h32) (by omega), ?_⟩
    have hg : UInt256.gt (memLoad ⟨1120⟩ (toMarketCodeMemory σ id))
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1)) =
        ⟨1⟩ := by
      rw [hroot]; apply ugt_one
      change 18446744073709551615 < _
      omega
    have rd2 := midnightBlocks.midnight_block_920_taken
      (by simp only [List.length_cons]; omega) (by rw [hg]; decide) (by jump_dest) rd1
    exact midnightBlocks.midnight_block_712 (by
      simp only [midnightBlocks.midnight_block_920_taken_stack, List.length_cons]; omega) rd2

end Benchmarks.Midnight
