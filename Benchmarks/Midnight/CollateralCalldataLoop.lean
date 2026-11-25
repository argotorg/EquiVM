import Benchmarks.Midnight.CollateralCalldataLoopStep
import Benchmarks.Midnight.CollateralDecode

variable {fork : Ethereum.Fork}

/-! Inductive correctness of the market calldata collateral loop. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightCollateralCalldataLoop {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr head writePtr finish : UInt256} {σ : AccountMap}
    {n k C : Nat} {R : List UInt256} (hstack : R.length + 18 ≤ 1024)
    (hbound : head.toNat + 128 * n ≤ I.calldata.size) (hsize : I.calldata.size < 2^255)
    (hfinish : finish.toNat = head.toNat + 128 * n)
    (hptr : ptr.toNat < 2^64) (hfree : memLoad (UInt256.ofNat 64) mem = ptr)
    (hwrite : 96 ≤ writePtr.toNat) (harray : writePtr.toNat + 32 * n ≤ ptr.toNat)
    (rd : RD fork midnightBytecode I g s0 ⟨18726⟩
      (writePtr :: UInt256.ofNat I.calldata.size :: head :: finish :: R) mem aw rdata σ k C) :
    (decodeCollateralElements n I.calldata head.toNat = none ∧ RDrev fork midnightBytecode g s0) ∨
    (¬ ptr.toNat + 128 * n < 2^64 ∧ RDrev fork midnightBytecode g s0) ∨
    (∃ values : List CollateralData,
      decodeCollateralElements n I.calldata head.toNat = some values ∧
      ptr.toNat + 128 * n < 2^64 ∧
      memLoad (UInt256.ofNat 64) (collateralLoopMemory mem ptr writePtr values) =
        ptr + UInt256.ofNat (128 * n) ∧
      ∃ aw' k' C', RD fork midnightBytecode I g s0 ⟨18734⟩
        ((writePtr + UInt256.ofNat (32 * n)) :: UInt256.ofNat I.calldata.size ::
          (head + UInt256.ofNat (128 * n)) :: finish :: R)
        (collateralLoopMemory mem ptr writePtr values) aw' rdata σ k' C') := by
  induction n generalizing mem ptr writePtr head aw k C with
  | zero =>
    right; right
    refine ⟨[], rfl, by simpa using hptr, ?_, ?_⟩
    · simpa only [collateralLoopMemory, Nat.mul_zero, wordAddNat_zero] using hfree
    · have hc : UInt256.lt head finish = ⟨0⟩ := ult_zero (by omega)
      have rd1 := midnightBlocks.midnight_block_18726_fallthrough (by omega) hc rd
      exact ⟨_, _, _, by simpa only [collateralLoopMemory, Nat.mul_zero, wordAddNat_zero] using rd1⟩
  | succ n ih =>
    have hhead : head.toNat + 128 ≤ I.calldata.size := by omega
    rcases midnightCollateralCalldataLoopStep hstack hhead hsize (by omega) hfree hptr rd with
      ⟨hbad, hrev⟩ | ⟨hnc, hrev⟩ | ⟨hfit, hcanon, aw1, k1, C1, rd1⟩
    · exact Or.inr (Or.inl ⟨by omega, hrev⟩)
    · left
      refine ⟨?_, hrev⟩
      rw [decodeCollateralElements, if_neg (by tauto)]
    · let c := CollateralData.at I.calldata head.toNat
      let nextMem := collateralStepMemory mem ptr writePtr c
      have hf : memLoad (UInt256.ofNat 64) nextMem = ptr + UInt256.ofNat 128 :=
        collateralStepMemory_free c (by omega) hwrite
      have hp : (ptr + UInt256.ofNat 128).toNat = ptr.toNat + 128 :=
        uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
      have hw : (writePtr + UInt256.ofNat 32).toNat = writePtr.toNat + 32 :=
        uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
      have hr : (head + UInt256.ofNat 128).toNat = head.toNat + 128 :=
        uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
      rcases ih (mem := nextMem) (ptr := ptr + UInt256.ofNat 128)
          (writePtr := writePtr + UInt256.ofNat 32) (head := head + UInt256.ofNat 128)
          (by rw [hr]; omega) (by rw [hr]; omega) (by rw [hp]; exact hfit) hf
          (by rw [hw]; omega) (by rw [hw, hp]; omega) rd1 with
        ⟨hnone, hrev⟩ | ⟨hbad, hrev⟩ | ⟨values, hd, hfit', hf', aw2, k2, C2, rd2⟩
      · left
        refine ⟨?_, hrev⟩
        rw [hr] at hnone
        rw [decodeCollateralElements, if_pos ⟨hhead, hcanon⟩, hnone]
        rfl
      · right; left
        rw [hp] at hbad
        exact ⟨by omega, hrev⟩
      · right; right
        refine ⟨c :: values, ?_, ?_, ?_, ?_⟩
        · rw [hr] at hd
          rw [decodeCollateralElements, if_pos ⟨hhead, hcanon⟩, hd]
          rfl
        · rw [hp] at hfit'
          omega
        · simpa only [wordAddNat_add, show 128 + 128 * n = 128 * (n + 1) by omega] using hf'
        · refine ⟨aw2, k2, C2, ?_⟩
          simpa only [wordAddNat_add, show 32 + 32 * n = 32 * (n + 1) by omega,
            show 128 + 128 * n = 128 * (n + 1) by omega] using rd2

end Benchmarks.Midnight
