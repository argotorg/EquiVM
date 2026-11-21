import Benchmarks.Midnight.CollateralLoopMemory
import Benchmarks.Midnight.CollateralDecode

/-! Inductive correctness of the stored-market collateral-decoding loop. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightToMarketCollateralLoop {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem bytes rdata : ByteArray} {aw ptr readPtr writePtr x finish : UInt256} {σ : AccountMap}
    {base start n k C : Nat} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hbytes : MemoryBytes mem base bytes) (hbase : 96 ≤ base)
    (hbound : start + 128 * n ≤ bytes.size) (hread : readPtr.toNat = base + start)
    (hend : x.toNat + 32 = base + bytes.size) (hsmall : base + bytes.size < 2^128)
    (hfinish : finish.toNat = readPtr.toNat + 128 * n)
    (hptr : ptr.toNat < 2^64) (hfree : memLoad (UInt256.ofNat 64) mem = ptr)
    (hwrite : base + bytes.size ≤ writePtr.toNat) (harray : writePtr.toNat + 32 * n ≤ ptr.toNat)
    (rd : RD midnightBytecode I g s0 ⟨1092⟩ (writePtr :: x :: finish :: readPtr :: R)
      mem aw rdata σ k C) :
    (decodeCollateralElements n bytes start = none ∧ RDrev midnightBytecode g s0) ∨
    (¬ ptr.toNat + 128 * n < 2^64 ∧ RDrev midnightBytecode g s0) ∨
    (∃ values : List CollateralData, decodeCollateralElements n bytes start = some values ∧
      ptr.toNat + 128 * n < 2^64 ∧
      MemoryBytes (collateralLoopMemory mem ptr writePtr values) base bytes ∧
      memLoad (UInt256.ofNat 64) (collateralLoopMemory mem ptr writePtr values) =
        ptr + UInt256.ofNat (128 * n) ∧
      ∃ aw' k' C', RD midnightBytecode I g s0 ⟨1100⟩
        ((writePtr + UInt256.ofNat (32 * n)) :: x :: finish :: (readPtr + UInt256.ofNat (128 * n)) :: R)
        (collateralLoopMemory mem ptr writePtr values) aw' rdata σ k' C') := by
  induction n generalizing mem ptr writePtr readPtr start aw k C with
  | zero =>
    right; right
    refine ⟨[], rfl, by simpa using hptr, hbytes, ?_, ?_⟩
    · simpa only [collateralLoopMemory, Nat.mul_zero, wordAddNat_zero] using hfree
    · have hc : UInt256.lt readPtr finish = ⟨0⟩ := ult_zero (by omega)
      have rd1 := midnightBlocks.midnight_block_1092_fallthrough (by omega) hc rd
      exact ⟨_, _, _, by simpa only [collateralLoopMemory, Nat.mul_zero, wordAddNat_zero] using rd1⟩
  | succ n ih =>
    have hhead : start + 128 ≤ bytes.size := by omega
    rcases midnightToMarketLoopStep hstack hbytes hbase hhead hread hend hsmall
        (by omega) (by omega) hptr hfree rd with
      ⟨hbad, hrev⟩ | ⟨hnc, hrev⟩ | ⟨hfit, hcanon, aw1, k1, C1, rd1⟩
    · exact Or.inr (Or.inl ⟨by omega, hrev⟩)
    · left
      refine ⟨?_, hrev⟩
      rw [decodeCollateralElements, if_neg (by tauto)]
    · let c := CollateralData.at bytes start
      let nextMem := collateralStepMemory mem ptr writePtr c
      have hb : MemoryBytes nextMem base bytes :=
        collateralStepMemory_bytes c hbytes hbase (by omega) hwrite
      have hf : memLoad (UInt256.ofNat 64) nextMem = ptr + UInt256.ofNat 128 :=
        collateralStepMemory_free c (by omega) (by omega)
      have hp : (ptr + UInt256.ofNat 128).toNat = ptr.toNat + 128 :=
        uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
      have hw : (writePtr + UInt256.ofNat 32).toNat = writePtr.toNat + 32 :=
        uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
      have hr : (readPtr + UInt256.ofNat 128).toNat = readPtr.toNat + 128 :=
        uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
      rcases ih (mem := nextMem) (ptr := ptr + UInt256.ofNat 128)
          (writePtr := writePtr + UInt256.ofNat 32) (readPtr := readPtr + UInt256.ofNat 128)
          (start := start + 128) hb (by omega) (by rw [hr]; omega)
          (by rw [hr]; omega) (by rw [hp]; exact hfit) hf
          (by rw [hw]; omega) (by rw [hw, hp]; omega) rd1 with
        ⟨hnone, hrev⟩ | ⟨hbad, hrev⟩ | ⟨values, hd, hfit', hb', hf', aw2, k2, C2, rd2⟩
      · left
        refine ⟨?_, hrev⟩
        rw [decodeCollateralElements, if_pos ⟨hhead, hcanon⟩, hnone]
        rfl
      · right; left
        rw [hp] at hbad
        exact ⟨by omega, hrev⟩
      · right; right
        refine ⟨c :: values, ?_, ?_, hb', ?_, ?_⟩
        · rw [decodeCollateralElements, if_pos ⟨hhead, hcanon⟩, hd]
          rfl
        · rw [hp] at hfit'
          omega
        · simpa only [wordAddNat_add, show 128 + 128 * n = 128 * (n + 1) by omega] using hf'
        · refine ⟨aw2, k2, C2, ?_⟩
          simpa only [wordAddNat_add, show 32 + 32 * n = 32 * (n + 1) by omega,
            show 128 + 128 * n = 128 * (n + 1) by omega] using rd2

end Benchmarks.Midnight
