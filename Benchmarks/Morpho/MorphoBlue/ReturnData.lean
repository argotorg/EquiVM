import Benchmarks.Morpho.MorphoBlue.Allocation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: rounding the payload and adding its header is bytes allocation.
theorem returnDataAllocWord {n : Nat} (hb : n + 94 < UInt256.size) :
    returnReserveSize n + UInt256.ofNat 32 = UInt256.ofNat ((n + 63) / 32 * 32) := by
  apply u256_inj
  have hs := returnReserveSize_toNat (size := n) (by omega)
  rw [uadd_word_ofNat_toNat _ 32 (by rw [hs]; omega), hs,
    UInt256.toNat_ofNat_of_lt (by omega)]
  omega

-- LIBRARY CANDIDATE: allocating an already rounded bytes size preserves the size.
theorem returnReserveSize_bytesRounded {n : Nat} (hb : n + 94 < UInt256.size) :
    returnReserveSize ((n + 63) / 32 * 32) = bytesAllocSize n := by
  apply u256_inj
  rw [returnReserveSize_toNat (by omega), bytesAllocSize_toNat (by omega)]
  omega

theorem morphoReturnDataEmpty {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hout : out.size = 0)
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14548)
      (ret :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret
      (UInt256.ofNat 96 :: R) mem aw' out σ k' C' := by
  have rd1 := morphoBlocks.morpho_block_14548_taken
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 2 ≤ 1024; omega)
    (by rw [hout]; decide) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  exact morphoBlocks.morpho_block_14637_packed
    (immWords := wordsOf (immStore v)) (by omega) hvalid rd1

theorem morphoReturnDataOversize {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hb : out.size < UInt256.size)
    (hout : 2 ^ 64 ≤ out.size) (hstack : R.length + 4 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14548)
      (ret :: R) mem aw out σ k C) : RDrev (deployedRuntime v) g s0 := by
  have hn : UInt256.ofNat out.size ≠ UInt256.ofNat 0 := by
    intro he
    have he := congrArg UInt256.toNat he
    rw [UInt256.toNat_ofNat_of_lt hb] at he
    change out.size = 0 at he
    omega
  have rd1 := morphoBlocks.morpho_block_14548_fallthrough
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 2 ≤ 1024; omega)
    (isZero_eq_zero_of_ne hn) h
  have rd2 := morphoBlocks.morpho_block_14555_taken
    (immWords := wordsOf (immStore v)) hstack
    (by rw [ugt_one (by rw [UInt256.toNat_ofNat_of_lt hb]; change 18446744073709551615 < out.size; omega)]; decide)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
  exact morphoBlocks.morpho_block_6709 (immWords := wordsOf (immStore v))
    (by change R.length + 2 + 2 ≤ 1024; omega) rd2

theorem morphoReturnDataPrepare {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hb : out.size < 2 ^ 64) (hn : out.size ≠ 0)
    (hfree : memLoad (UInt256.ofNat 64) mem = ptr) (hstack : R.length + 8 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14548)
      (ret :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 11535)
      (ptr :: UInt256.ofNat ((out.size + 63) / 32 * 32) :: UInt256.ofNat 14625 ::
        UInt256.ofNat out.size :: ret :: ptr :: R) mem aw' out σ k' C' := by
  have hsize : out.size < UInt256.size := by change _ < 2 ^ 256; omega
  have hnw : UInt256.ofNat out.size ≠ UInt256.ofNat 0 := by
    intro he
    have he := congrArg UInt256.toNat he
    rw [UInt256.toNat_ofNat_of_lt hsize] at he
    exact hn he
  have rd1 := morphoBlocks.morpho_block_14548_fallthrough
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 2 ≤ 1024; omega)
    (isZero_eq_zero_of_ne hnw) h
  have rd2 := morphoBlocks.morpho_block_14555_fallthrough
    (immWords := wordsOf (immStore v)) (by omega)
    (ugt_zero (by rw [UInt256.toNat_ofNat_of_lt hsize]; change out.size ≤ 18446744073709551615; omega)) rd1
  obtain ⟨aw3, k3, C3, rd3⟩ := morphoBlocks.morpho_block_14572_packed
    (immWords := wordsOf (immStore v)) hstack
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  dsimp only [morphoBlocks.morpho_block_14572_stack,
    morphoBlocks.morpho_block_14555_fallthrough_stack] at rd3
  rw [hfree, returnReserveSize_solc,
    returnDataAllocWord (by change out.size + 94 < 2 ^ 256; omega)] at rd3
  exact ⟨aw3, k3, C3, rd3⟩

theorem morphoReturnDataOverflow {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hb : out.size < 2 ^ 64) (hn : out.size ≠ 0)
    (hp : ptr.toNat < 2 ^ 64)
    (hfree : memLoad (UInt256.ofNat 64) mem = ptr) (hstack : R.length + 8 ≤ 1024)
    (hbad : 2 ^ 64 ≤ ptr.toNat + (out.size + 63) / 32 * 32)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14548)
      (ret :: R) mem aw out σ k C) : RDrev (deployedRuntime v) g s0 := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoReturnDataPrepare hb hn hfree hstack h
  exact morphoAllocDynamicOverflow _ (by change R.length + 3 + 5 ≤ 1024; omega)
    (by omega) (by omega) rd1

theorem morphoReturnDataCopy {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hb : out.size < 2 ^ 64) (hn : out.size ≠ 0)
    (hfree : memLoad (UInt256.ofNat 64) mem = ptr) (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (hfit : ptr.toNat + (out.size + 63) / 32 * 32 < 2 ^ 64)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14548)
      (ret :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret (ptr :: R)
      (bytesAllocMem mem out ptr) aw' out σ k' C' := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoReturnDataPrepare hb hn hfree hstack h
  obtain ⟨aw2, k2, C2, rd2⟩ := morphoAllocDynamicExact _
    (by change R.length + 3 + 5 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by omega) (by omega) rd1
  obtain ⟨aw3, k3, C3, rd3⟩ := morphoBlocks.morpho_block_14625_packed
    (immWords := wordsOf (immStore v)) (by omega)
    (by change 0 + out.size % UInt256.size ≤ out.size; simpa only [Nat.zero_add] using Nat.mod_le out.size UInt256.size)
    hvalid rd2
  have hs : out.size + 94 < UInt256.size := by change _ < 2 ^ 256; omega
  have hptr : returnReservePtr ptr ((out.size + 63) / 32 * 32) = bytesAllocPtr ptr out.size := by
    rw [returnReservePtr, returnReserveSize_bytesRounded hs]
    rfl
  have hadd : (ptr + UInt256.ofNat 32).toNat = ptr.toNat + 32 :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2 ^ 256; omega)
  dsimp only [morphoBlocks.morpho_block_14625_memory, morphoBlocks.morpho_block_14625_stack,
    returnReserveMem] at rd3
  rw [hptr, UInt256.toNat_ofNat_of_lt (n := out.size) (by omega), hadd] at rd3
  exact ⟨aw3, k3, C3, rd3⟩

end Benchmarks.Morpho.MorphoBlue
