import Benchmarks.Midnight.ToMarketFirstFields
import Benchmarks.Midnight.ArrayAllocation

variable {fork : Ethereum.Fork}

/-! The stored-market collateral-array header bounds and uint64 length check. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightToMarketArrayHeader {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem bytes rdata : ByteArray} {aw ptr anchor x finish : UInt256} {σ : AccountMap}
    {base start k C : Nat} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hbytes : MemoryBytes mem base bytes) (hhead : start + 256 ≤ bytes.size)
    (hanchor : anchor.toNat + 32 = base + start)
    (hfinish : finish.toNat = base + bytes.size) (hsmall : base + bytes.size < 2^128)
    (hoff : (calldataWord bytes (start + 96)).toNat < 2^64)
    (rd : RD fork midnightBytecode I g s0 ⟨1022⟩
      (calldataWord bytes (start + 96) :: x :: finish :: ptr :: anchor :: R)
      mem aw rdata σ k C) :
    (decodeMarketData bytes start = none ∧ RDrev fork midnightBytecode g s0) ∨
    (start + (calldataWord bytes (start + 96)).toNat + 32 ≤ bytes.size ∧
      (calldataWord bytes (start + (calldataWord bytes (start + 96)).toNat)).toNat < 2^64 ∧
      ∃ k' C', RD fork midnightBytecode I g s0 ⟨1051⟩
        (UInt256.ofNat (pointerArrayAllocation
          (calldataWord bytes (start + (calldataWord bytes (start + 96)).toNat)).toNat) ::
          x :: finish :: calldataWord bytes (start + (calldataWord bytes (start + 96)).toNat) ::
          ((anchor + calldataWord bytes (start + 96)) + UInt256.ofNat 32) :: ptr :: anchor :: R)
        mem (M aw ((anchor + calldataWord bytes (start + 96)) + UInt256.ofNat 32) ⟨32⟩)
        rdata σ k' C') := by
  let relative := calldataWord bytes (start + 96)
  let target := (anchor + relative) + UInt256.ofNat 32
  have har : (anchor + relative).toNat = anchor.toNat + relative.toNat := by
    rw [uadd_toNat]
    apply Nat.mod_eq_of_lt
    change _ < 2^256
    change relative.toNat < 2^64 at hoff
    omega
  have ht : target.toNat = base + start + relative.toNat := by
    rw [show target = (anchor + relative) + UInt256.ofNat 32 from rfl,
      uadd_word_ofNat_toNat _ _ (by rw [har]; change _ < 2^256; change relative.toNat < 2^64 at hoff; omega), har]
    omega
  have ht31 : (target + UInt256.ofNat 31).toNat = base + start + relative.toNat + 31 := by
    rw [uadd_word_ofNat_toNat _ _ (by rw [ht]; change _ < 2^256; change relative.toNat < 2^64 at hoff; omega), ht]
  by_cases hh : start + relative.toNat + 32 ≤ bytes.size
  · have hs : UInt256.slt (target + UInt256.ofNat 31) finish = ⟨1⟩ := by
      have he := slt_lit_one_low (a := target + UInt256.ofNat 31) (m := finish.toNat)
        (by rw [hfinish]; omega) (by rw [hfinish, ht31]; omega)
      simpa only [u256_ofNat_toNat] using he
    have rd1 := midnightBlocks.midnight_block_1022_fallthrough (by omega)
      (by change UInt256.isZero (UInt256.slt (target + UInt256.ofNat 31) finish) = _; rw [hs]; rfl) rd
    simp only [midnightBlocks.midnight_block_1022_fallthrough_stack] at rd1
    have hn : memLoad target mem = calldataWord bytes (start + relative.toNat) :=
      hbytes.load_word hh (by rw [ht]; omega)
    have rd2 := midnightBlocks.midnight_block_1040
      (by simp only [List.length_cons]; omega) (by jump_dest) rd1
    change RD fork midnightBytecode I g s0 ⟨18477⟩
      (memLoad target mem :: ⟨1051⟩ :: x :: finish :: memLoad target mem :: target :: ptr :: anchor :: R)
      mem (M aw target ⟨32⟩) rdata σ _ _ at rd2
    rw [hn] at rd2
    by_cases hnsmall : (calldataWord bytes (start + relative.toNat)).toNat < 2^64
    · right
      refine ⟨hh, hnsmall, ?_⟩
      exact midnightPointerArraySize hnsmall (by simp only [List.length_cons]; omega)
        (by jump_dest) rd2
    · left
      refine ⟨?_, ?_⟩
      · have hread := readNat_bytes hh
        have hncap : solcMaxU64 < (calldataWord bytes (start + relative.toNat)).toNat := by
          change 18446744073709551615 < _; omega
        simpa only [relative] using (show decodeMarketData bytes start = none from by
          simp only [decodeMarketData]
          split
          · rfl
          · split
            · rfl
            · rw [hread]
              dsimp only [bind, Option.bind]
              exact if_pos hncap)
      · exact midnightPointerArrayLengthTooLarge (by omega)
          (by simp only [List.length_cons]; omega) rd2
  · left
    refine ⟨?_, ?_⟩
    · have hread := readNat_bytes_short (bytes := bytes) (off := start + relative.toNat) (by omega)
      simp [decodeMarketData, show readNat? bytes.toList
        (start + (calldataWord bytes (start + 96)).toNat) = none from hread]
    · have hs : UInt256.slt (target + UInt256.ofNat 31) finish = ⟨0⟩ := by
        have he := slt_lit_zero (a := target + UInt256.ofNat 31) (m := finish.toNat)
          (by rw [hfinish]; omega) (by rw [hfinish, ht31]; omega)
          (by rw [ht31]; change relative.toNat < 2^64 at hoff; omega)
        simpa only [u256_ofNat_toNat] using he
      have rd1 := midnightBlocks.midnight_block_1022_taken (by omega)
        (by change UInt256.isZero (UInt256.slt (target + UInt256.ofNat 31) finish) ≠ _; rw [hs]; decide)
        (by jump_dest) rd
      exact midnightBlocks.midnight_block_712 (by
        simp only [midnightBlocks.midnight_block_1022_taken_stack, List.length_cons]; omega) rd1

end Benchmarks.Midnight
