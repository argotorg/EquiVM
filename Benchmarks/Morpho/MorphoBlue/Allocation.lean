import Benchmarks.Morpho.MorphoBlue.ErrorRoutines
import Reasoning.HeapMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: the compiler's mask order agrees with the shared allocator size.
theorem returnReserveSize_solc (size : Nat) :
    UInt256.land (UInt256.ofNat size + UInt256.ofNat 31)
      (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904) =
      returnReserveSize size := by
  exact u256_land_comm _ _

theorem morphoAllocDynamicExact {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap} {k C : Nat} {ptr ret : UInt256} {R : List UInt256} (size : Nat)
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (hsmall : ptr.toNat + size + 31 ≤ 2 ^ 200)
    (hfit : ptr.toNat + (size + 31) / 32 * 32 < 2 ^ 64)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 11535)
      (ptr :: UInt256.ofNat size :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret R
      (returnReserveMem mem ptr size) aw' rdata σ k' C' := by
  have hp := returnReservePtr_toNat hsmall
  have hcond : UInt256.lor (UInt256.gt (returnReservePtr ptr size)
      (UInt256.ofNat 18446744073709551615))
      (UInt256.lt (returnReservePtr ptr size) ptr) = UInt256.ofNat 0 := by
    rw [ugt_zero (by rw [hp]; change _ ≤ 18446744073709551615; omega),
      ult_zero (by rw [hp]; omega)]
    rfl
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_11535_fallthrough_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [returnReserveSize_solc]; exact hcond) h
  obtain ⟨aw2, k2, C2, rd2⟩ := morphoBlocks.morpho_block_11596_packed
    (immWords := wordsOf (immStore v)) (by omega) hvalid rd1
  dsimp only [morphoBlocks.morpho_block_11596_memory] at rd2
  rw [returnReserveSize_solc] at rd2
  exact ⟨aw2, k2, C2, rd2⟩

theorem morphoAllocDynamicOverflow {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap} {k C : Nat} {ptr ret : UInt256} {R : List UInt256} (size : Nat)
    (hstack : R.length + 5 ≤ 1024)
    (hsmall : ptr.toNat + size + 31 ≤ 2 ^ 200)
    (hbad : 2 ^ 64 ≤ ptr.toNat + (size + 31) / 32 * 32)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 11535)
      (ptr :: UInt256.ofNat size :: ret :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have hp := returnReservePtr_toNat hsmall
  have hcond : UInt256.lor (UInt256.gt (returnReservePtr ptr size)
      (UInt256.ofNat 18446744073709551615))
      (UInt256.lt (returnReservePtr ptr size) ptr) ≠ UInt256.ofNat 0 := by
    rw [ugt_one (by rw [hp]; change 18446744073709551615 < _; omega)]
    exact u256_lor_one_left_ne_zero _
  have rd1 := morphoBlocks.morpho_block_11535_taken
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [returnReserveSize_solc]; exact hcond)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  exact morphoBlocks.morpho_block_6709 (immWords := wordsOf (immStore v))
    (by change R.length + 2 + 2 ≤ 1024; omega) rd1

theorem morphoAllocDynamic {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap} {k C : Nat} {ptr ret : UInt256} {R : List UInt256} (size : Nat)
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (hfit : ptr.toNat + size + 31 ≤ 2 ^ 64 - 1)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 11535)
      (ptr :: UInt256.ofNat size :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret R
      (returnReserveMem mem ptr size) aw' rdata σ k' C' := by
  exact morphoAllocDynamicExact size hstack hvalid (by omega) (by omega) h

end Benchmarks.Morpho.MorphoBlue
