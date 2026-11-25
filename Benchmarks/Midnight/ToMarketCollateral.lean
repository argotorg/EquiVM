import Benchmarks.Midnight.CollateralData
import Benchmarks.Midnight.MemoryBytes
import Benchmarks.Midnight.MemoryAddressDecode

variable {fork : Ethereum.Fork}

/-! One collateral tuple copied by the stored-market decoder. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def collateralCopyMemory (mem : ByteArray) (ptr writePtr : UInt256) (c : CollateralData) : ByteArray :=
  writeWord (writeWordArray mem ptr.toNat c.words) writePtr.toNat ptr

theorem midnightToMarketCollateral {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem bytes rdata : ByteArray} {aw ptr readPtr writePtr x finish : UInt256} {σ : AccountMap}
    {base start k C : Nat} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hbytes : MemoryBytes mem base bytes) (hhead : start + 128 ≤ bytes.size)
    (hread : readPtr.toNat = base + start)
    (hregion : base + bytes.size ≤ ptr.toNat) (hptr : ptr.toNat + 128 < 2^64)
    (rd : RD fork midnightBytecode I g s0 ⟨1218⟩
      (ptr :: writePtr :: UInt256.ofNat 32 :: UInt256.ofNat 128 :: x :: finish :: readPtr :: R)
      mem aw rdata σ k C) :
    (¬ CollateralData.canonicalAt bytes start ∧ RDrev fork midnightBytecode g s0) ∨
    (CollateralData.canonicalAt bytes start ∧
      ∃ aw' k' C', RD fork midnightBytecode I g s0 ⟨1092⟩
        ((writePtr + UInt256.ofNat 32) :: x :: finish :: (readPtr + UInt256.ofNat 128) :: R)
        (collateralCopyMemory mem ptr writePtr (CollateralData.at bytes start)) aw' rdata σ k' C') := by
  have load {m : ByteArray} (hb : MemoryBytes m base bytes) (off : Nat) (ho : off + 32 ≤ 128) :
      memLoad (readPtr + UInt256.ofNat off) m = calldataWord bytes (start + off) := by
    apply hb.load_word (by omega)
    rw [uadd_word_ofNat_toNat _ _ (by have h := hb.bound; omega), hread]
    omega
  have h0 : memLoad readPtr mem = calldataWord bytes start := hbytes.load_word (by omega) hread
  have hp32 : (ptr + UInt256.ofNat 32).toNat = ptr.toNat + 32 :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  have hp64 : (ptr + UInt256.ofNat 64).toNat = ptr.toNat + 64 :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  have hp96 : (ptr + UInt256.ofNat 96).toNat = ptr.toNat + 96 :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  have rd1 := midnightBlocks.midnight_block_1218 (by omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_1218_stack] at rd1
  by_cases ht : (calldataWord bytes start).toNat < EVM.addressModulus
  · obtain ⟨aw2, k2, C2, rd2⟩ := midnightMemoryAddress_ok
      (by simp only [List.length_cons]; omega) (by rw [h0]; exact ht) (by jump_dest) rd1
    rw [h0] at rd2
    let m1 := writeWord mem ptr.toNat (calldataWord bytes start)
    have hb1 : MemoryBytes m1 base bytes := hbytes.writeWord _ (Or.inl hregion)
    have h32 : memLoad (readPtr + UInt256.ofNat 32) m1 = calldataWord bytes (start + 32) :=
      load hb1 32 (by decide)
    let m2 := writeWord m1 (ptr + UInt256.ofNat 32).toNat (calldataWord bytes (start + 32))
    have hb2 : MemoryBytes m2 base bytes := hb1.writeWord _ (Or.inl (by rw [hp32]; omega))
    have h64 : memLoad (readPtr + UInt256.ofNat 64) m2 = calldataWord bytes (start + 64) :=
      load hb2 64 (by decide)
    let m3 := writeWord m2 (ptr + UInt256.ofNat 64).toNat (calldataWord bytes (start + 64))
    have hb3 : MemoryBytes m3 base bytes := hb2.writeWord _ (Or.inl (by rw [hp64]; omega))
    have h96 : memLoad (readPtr + UInt256.ofNat 96) m3 = calldataWord bytes (start + 96) :=
      load hb3 96 (by decide)
    have hmem : midnightBlocks.midnight_block_1227_memory (mem := mem)
        (x0 := calldataWord bytes start) (x1 := ptr) (x3 := UInt256.ofNat 32) (x7 := readPtr) = m3 := by
      change writeWord (writeWord m1 (ptr + UInt256.ofNat 32).toNat
        (memLoad (readPtr + UInt256.ofNat 32) m1)) (ptr + UInt256.ofNat 64).toNat
        (memLoad (readPtr + UInt256.ofNat 64)
          (writeWord m1 (ptr + UInt256.ofNat 32).toNat (memLoad (readPtr + UInt256.ofNat 32) m1))) = m3
      rw [h32]
      change writeWord m2 (ptr + UInt256.ofNat 64).toNat
        (memLoad (readPtr + UInt256.ofNat 64) m2) = m3
      rw [h64]
    have rd3 := midnightBlocks.midnight_block_1227 (by omega) (by jump_dest) rd2
    simp only [midnightBlocks.midnight_block_1227_stack, hmem] at rd3
    by_cases ho : (calldataWord bytes (start + 96)).toNat < EVM.addressModulus
    · right
      have hc : CollateralData.canonicalAt bytes start := ⟨ht, ho⟩
      refine ⟨hc, ?_⟩
      obtain ⟨aw4, k4, C4, rd4⟩ := midnightMemoryAddress_ok
        (by simp only [List.length_cons]; omega) (by rw [h96]; exact ho) (by jump_dest) rd3
      rw [h96] at rd4
      have rd5 := midnightBlocks.midnight_block_1259 (by omega) (by jump_dest) rd4
      have hf : midnightBlocks.midnight_block_1259_memory (mem := m3)
          (x0 := calldataWord bytes (start + 96)) (x1 := ptr) (x2 := writePtr) =
          collateralCopyMemory mem ptr writePtr (CollateralData.at bytes start) := by
        simp only [midnightBlocks.midnight_block_1259_memory, collateralCopyMemory,
          CollateralData.at_words hc, writeWordArray]
        change writeWord (writeWord m3 (ptr + UInt256.ofNat 96).toNat
          (calldataWord bytes (start + 96))) writePtr.toNat ptr = _
        simp only [m3, m2, m1, hp32, hp64, hp96, Nat.add_assoc, Nat.reduceAdd]
      simp only [midnightBlocks.midnight_block_1259_stack, hf] at rd5
      exact ⟨_, _, _, rd5⟩
    · left
      refine ⟨by simp [CollateralData.canonicalAt, ho], ?_⟩
      exact midnightMemoryAddress_bad (by simp only [List.length_cons]; omega)
        (by rw [h96]; exact ho) rd3
  · left
    refine ⟨by simp [CollateralData.canonicalAt, ht], ?_⟩
    exact midnightMemoryAddress_bad (by simp only [List.length_cons]; omega)
      (by rw [h0]; exact ht) rd1

end Benchmarks.Midnight
