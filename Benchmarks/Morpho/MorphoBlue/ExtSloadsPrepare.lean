import Benchmarks.Morpho.MorphoBlue.ExtSloadsReadLoop
import Benchmarks.Morpho.MorphoBlue.ExtSloadsMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoArrayByteSize {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C n : Nat} {ret : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024) (hn : n ≤ solcMaxU64)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14371)
      (UInt256.ofNat n :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret
      (UInt256.ofNat (32 * (n + 1)) :: R) mem aw' rdata σ k' C' := by
  have hf : 32 * (n + 1) < UInt256.size := by
    norm_num [solcMaxU64, UInt256.size] at hn ⊢; omega
  have rd := morphoBlocks.morpho_block_14371_fallthrough (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (ugt_zero (by rw [UInt256.toNat_ofNat_of_lt (by omega : n < UInt256.size)]; exact hn)) h
  have rd' := morphoBlocks.morpho_block_14387 (immWords := wordsOf (immStore v))
    (by omega) hvalid rd
  have he : UInt256.ofNat 32 + UInt256.shiftLeft (UInt256.ofNat n) (UInt256.ofNat 5) =
      UInt256.ofNat (32 * (n + 1)) := by
    have hs : UInt256.shiftLeft (UInt256.ofNat n) (UInt256.ofNat 5) =
        UInt256.ofNat (32 * n) := shiftLeft5_ofNat_eq (by omega)
    rw [hs, ofNat_add_words]
    congr 1; omega
  refine ⟨aw, k + 6 + 6, C + 23 + 23, ?_⟩
  simpa only [morphoBlocks.morpho_block_14387_stack, he] using rd'

theorem extSloadsReservePtr {n : Nat} (hn : n ≤ solcMaxU64) :
    returnReservePtr (UInt256.ofNat 128) (32 * (n + 1)) = UInt256.ofNat (160 + 32 * n) := by
  have hf : 128 + 32 * (n + 1) + 31 ≤ 2 ^ 200 := by
    norm_num [solcMaxU64] at hn ⊢; omega
  apply u256_inj
  have hp := returnReservePtr_toNat (ptr := UInt256.ofNat 128) (size := 32 * (n + 1)) hf
  change (returnReservePtr (UInt256.ofNat 128) (32 * (n + 1))).toNat = _
  rw [hp, UInt256.toNat_ofNat_of_lt (n := 160 + 32 * n)
    (by change 160 + 32 * n < 2 ^ 256; omega)]
  change 128 + (32 * (n + 1) + 31) / 32 * 32 = _
  omega

theorem morphoExtSloadsPrepare {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C n : Nat} {off : UInt256}
    (hn : n ≤ solcMaxU64) (hsize : ee.calldata.size < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6873)
      [UInt256.ofNat n, UInt256.ofNat 5, UInt256.ofNat 32, UInt256.ofNat 36, off, UInt256.ofNat 0]
      solcFreePtrMem aw rdata σ k C) :
    (¬ 128 + 32 * (n + 1) ≤ solcMaxU64 ∧ RDrev (deployedRuntime v) g s0) ∨
    (128 + 32 * (n + 1) ≤ solcMaxU64 ∧ ∃ aw' k' C',
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6955)
        (extSloadsReadStack off n 0 [off, UInt256.ofNat 0]) (extSloadsHeaderMem n)
        aw' rdata σ k' C') := by
  have hf : 160 + 32 * n + 64 < UInt256.size := by
    norm_num [solcMaxU64, UInt256.size] at hn ⊢; omega
  have rd0 := morphoBlocks.morpho_block_6873 (immWords := wordsOf (immStore v)) (by simp)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoArrayByteSize (v := v) (by simp) hn
    (by rw [morphoPatchedValidJumps v]; jump_dest) rd0
  have rd2 := morphoBlocks.morpho_block_6885 (immWords := wordsOf (immStore v)) (by simp)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
  change RD _ _ _ _ _
    [memLoad (UInt256.ofNat 64) solcFreePtrMem, UInt256.ofNat (32 * (n + 1)), UInt256.ofNat 6899,
     UInt256.ofNat 36, UInt256.ofNat n, UInt256.ofNat 5, UInt256.ofNat 0, off, UInt256.ofNat 32,
     memLoad (UInt256.ofNat 64) solcFreePtrMem, off, UInt256.ofNat 0] _ _ _ _ _ _ at rd2
  have hfp : memLoad (UInt256.ofNat 64) solcFreePtrMem = UInt256.ofNat 128 :=
    solcFreePtrMem_mload64
  rw [hfp] at rd2
  have hround : UInt256.ofNat 128 + UInt256.land
      (UInt256.ofNat (32 * (n + 1)) + UInt256.ofNat 31)
      (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904) =
      UInt256.ofNat (160 + 32 * n) := by
    change UInt256.ofNat 128 + UInt256.land
      (UInt256.ofNat (32 * (n + 1)) + ⟨31⟩) (UInt256.lnot ⟨31⟩) = _
    rw [u256_land_comm]
    exact extSloadsReservePtr hn
  have hpn : (UInt256.ofNat (160 + 32 * n)).toNat = 160 + 32 * n :=
    UInt256.toNat_ofNat_of_lt (by omega)
  by_cases ha : 128 + 32 * (n + 1) ≤ solcMaxU64
  swap
  · have rd3 := morphoBlocks.morpho_block_11535_taken (immWords := wordsOf (immStore v))
      (by simp) (by
        rw [hround, ult_zero (by rw [hpn]; change 128 ≤ _; omega),
          u256_lor_zero, ugt_one (by
            rw [hpn]
            change 18446744073709551615 < _
            change ¬ 128 + 32 * (n + 1) ≤ 18446744073709551615 at ha
            omega)]
        decide) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
    exact .inl ⟨ha, morphoBlocks.morpho_block_6709 (immWords := wordsOf (immStore v))
      (by simp [morphoBlocks.morpho_block_11535_taken_stack]) rd3⟩
  obtain ⟨aw3, k3, C3, rd3⟩ := morphoAllocDynamic (v := v) (32 * (n + 1)) (by simp)
    (by rw [morphoPatchedValidJumps v]; jump_dest)
    (by change 128 + 32 * (n + 1) + 31 ≤ 18446744073709551615
        change 128 + 32 * (n + 1) ≤ 18446744073709551615 at ha; omega) rd2
  have hmem : returnReserveMem solcFreePtrMem (UInt256.ofNat 128) (32 * (n + 1)) =
      writeWord solcFreePtrMem 64 (UInt256.ofNat (160 + 32 * n)) := by
    unfold returnReserveMem
    rw [extSloadsReservePtr hn]
  rw [hmem] at rd3
  have rd4 := morphoBlocks.morpho_block_6899 (immWords := wordsOf (immStore v)) (by simp)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd3
  obtain ⟨aw5, k5, C5, rd5⟩ := morphoArrayByteSize (v := v) (by simp) hn
    (by rw [morphoPatchedValidJumps v]; jump_dest) rd4
  obtain ⟨aw6, k6, C6, rd6⟩ := morphoBlocks.morpho_block_6911_packed
    (immWords := wordsOf (immStore v)) (by simp) rd5
  have hlen : (UInt256.ofNat (32 * (n + 1)) +
      UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904).toNat =
      32 * n := by
    rw [show UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 =
      UInt256.sub ⟨0⟩ (UInt256.ofNat 32) by native_decide, word_add_sub_zero,
      usub_ofNat_lit_toNat (by omega) (by omega)]
    omega
  change RD _ _ _ _ _ (extSloadsReadStack off n 0 [off, UInt256.ofNat 0])
    (ee.calldata.write (UInt256.ofNat ee.calldata.size).toNat (extSloadsHeaderMem n) 160 _)
    aw6 rdata σ k6 C6 at rd6
  rw [UInt256.toNat_ofNat_of_lt hsize, hlen, ← extSloadsHeader_size n,
    byteArray_write_zero_at_end] at rd6
  exact .inr ⟨ha, aw6, k6, C6, rd6⟩

end Benchmarks.Morpho.MorphoBlue
