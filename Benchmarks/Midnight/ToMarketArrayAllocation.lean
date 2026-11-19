import Benchmarks.Midnight.ArrayAllocation

/-! Pointer-array allocation and bounds of its encoded collateral elements. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem collateralStrideWord {n : UInt256} (hn : n.toNat < 2^64) :
    (UInt256.shiftLeft n (UInt256.ofNat 7)).toNat = 128 * n.toNat := by
  unfold UInt256.shiftLeft
  rw [if_neg (by decide : ¬ (UInt256.ofNat 7).val ≥ 256)]
  change (n.toNat <<< 7) % UInt256.size = _
  rw [Nat.shiftLeft_eq]
  norm_num only [Nat.reducePow]
  rw [Nat.mod_eq_of_lt (by change _ < 2^256; omega)]
  omega

theorem collateralEnd_toNat {header n : UInt256}
    (hheader : header.toNat < 2^128) (hn : n.toNat < 2^64) :
    ((header + UInt256.shiftLeft n (UInt256.ofNat 7)) + UInt256.ofNat 32).toNat =
      header.toNat + 32 + 128 * n.toNat := by
  have hadd : (header + UInt256.shiftLeft n (UInt256.ofNat 7)).toNat =
      header.toNat + 128 * n.toNat := by
    rw [uadd_toNat, collateralStrideWord hn, Nat.mod_eq_of_lt (by change _ < 2^256; omega)]
  rw [uadd_word_ofNat_toNat _ _ (by rw [hadd]; change _ < 2^256; omega), hadd]
  omega

theorem collateralEnd_eq {header n : UInt256}
    (hheader : header.toNat < 2^128) (hn : n.toNat < 2^64) :
    (header + UInt256.shiftLeft n (UInt256.ofNat 7)) + UInt256.ofNat 32 =
      UInt256.ofNat (header.toNat + 32 + 128 * n.toNat) := by
  apply u256_inj
  rw [collateralEnd_toNat hheader hn,
    UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)]

def marketArrayMemory (mem : ByteArray) (ptr n : UInt256) : ByteArray :=
  writeWord (writeWord mem 64 (ptr + UInt256.ofNat (pointerArrayAllocation n.toNat))) ptr.toNat n

theorem midnightToMarketArrayAllocation {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr n header x finish : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hfree : memLoad (UInt256.ofNat 64) mem = ptr)
    (hptr : ptr.toNat < 2^64) (hn : n.toNat < 2^64) (hheader : header.toNat < 2^128)
    (rd : RD midnightBytecode I g s0 ⟨1051⟩
      (UInt256.ofNat (pointerArrayAllocation n.toNat) :: x :: finish :: n :: header :: R)
      mem aw rdata σ k C) :
    (¬ ptr.toNat + pointerArrayAllocation n.toNat < 2^64 ∧ RDrev midnightBytecode g s0) ∨
    (finish.toNat < header.toNat + 32 + 128 * n.toNat ∧ RDrev midnightBytecode g s0) ∨
    (ptr.toNat + pointerArrayAllocation n.toNat < 2^64 ∧
      header.toNat + 32 + 128 * n.toNat ≤ finish.toNat ∧
      ∃ aw' k' C', RD midnightBytecode I g s0 ⟨1092⟩
        ((ptr + UInt256.ofNat 32) :: x ::
          UInt256.ofNat (header.toNat + 32 + 128 * n.toNat) ::
          (UInt256.ofNat 32 + header) :: ptr :: R)
        (marketArrayMemory mem ptr n) aw' rdata σ k' C') := by
  have hend := pointerArrayAllocation_end hn hptr
  have hnext : (ptr + UInt256.ofNat (pointerArrayAllocation n.toNat)).toNat =
      ptr.toNat + pointerArrayAllocation n.toNat :=
    uadd_word_ofNat_toNat _ _ (by change _ + (32 + 32 * n.toNat) < 2^256; omega)
  have rd1 := midnightBlocks.midnight_block_1051 (by omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_1051_stack, hfree] at rd1
  by_cases hfit : ptr.toNat + pointerArrayAllocation n.toNat < 2^64
  · have hc : allocationCheck ptr (allocationEnd ptr (UInt256.ofNat (pointerArrayAllocation n.toNat))) =
        ⟨0⟩ := by
      rw [hend]
      exact allocationCheck_ok (by rw [hnext]; exact hfit) (by rw [hnext]; omega)
    obtain ⟨aw2, k2, C2, rd2⟩ := midnightAllocate (by simp only [List.length_cons]; omega)
      hc (by jump_dest) rd1
    rw [hend] at rd2
    have hext := collateralEnd_toNat hheader hn
    have hextWord := collateralEnd_eq hheader hn
    by_cases hbound : header.toNat + 32 + 128 * n.toNat ≤ finish.toNat
    · right; right
      refine ⟨hfit, hbound, ?_⟩
      have hg : UInt256.gt ((header + UInt256.shiftLeft n (UInt256.ofNat 7)) + UInt256.ofNat 32)
          finish = ⟨0⟩ := ugt_zero (by rw [hext]; exact hbound)
      have rd3 := midnightBlocks.midnight_block_1065_fallthrough (by omega) hg rd2
      simp only [midnightBlocks.midnight_block_1065_fallthrough_stack,
        midnightBlocks.midnight_block_1065_fallthrough_memory, hextWord] at rd3
      have rd4 := midnightBlocks.midnight_block_1088 (by simp only [List.length_cons]; omega) rd3
      exact ⟨_, _, _, rd4⟩
    · right; left
      refine ⟨by omega, ?_⟩
      have hg : UInt256.gt ((header + UInt256.shiftLeft n (UInt256.ofNat 7)) + UInt256.ofNat 32)
          finish = ⟨1⟩ := ugt_one (by rw [hext]; omega)
      have rd3 := midnightBlocks.midnight_block_1065_taken (by omega)
        (by rw [hg]; decide) (by jump_dest) rd2
      exact midnightBlocks.midnight_block_712 (by
        simp only [midnightBlocks.midnight_block_1065_taken_stack, List.length_cons]; omega) rd3
  · left
    refine ⟨hfit, ?_⟩
    apply midnightAllocateRevert (by simp only [List.length_cons]; omega) _ rd1
    rw [hend]
    exact allocationCheck_large (by rw [hnext]; omega) (by rw [hnext]; omega)

end Benchmarks.Midnight
