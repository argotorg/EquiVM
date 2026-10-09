import Benchmarks.Morpho.MorphoBlue.MarketParamsCommon
import Benchmarks.Morpho.MorphoBlue.ErrorRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def marketParamsAllocatedMem (mem : ByteArray) : ByteArray :=
  ((memLoad (UInt256.ofNat 64) mem + UInt256.ofNat 160).toByteArray.write 0 mem 64 32)

theorem morphoDecodeMarketParamsPrefix {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap} {k C : Nat} {ret : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hsize : ee.calldata.size < UInt256.size) (hlen : 164 ≤ ee.calldata.size)
    (hbound : ee.calldata.size < 2 ^ 255 + 4)
    (hfit : UInt256.lor (UInt256.gt (memLoad (UInt256.ofNat 64) mem + UInt256.ofNat 160)
        (UInt256.ofNat 18446744073709551615))
      (UInt256.lt (memLoad (UInt256.ofNat 64) mem + UInt256.ofNat 160)
        (memLoad (UInt256.ofNat 64) mem)) = UInt256.ofNat 0)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 11600)
      (UInt256.ofNat ee.calldata.size :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 11655)
      (ret :: memLoad (UInt256.ofNat 64) mem :: R) (marketParamsAllocatedMem mem) aw' rdata σ k' C' := by
  have hcond := solcCalldataStaticLenCheckOk (words := 5) hlen hbound hsize
  have rdGuard := morphoBlocks.morpho_block_11600_fallthrough
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by simpa only [wordAddNegFour] using hcond) h
  have rdAlloc := morphoBlocks.morpho_block_11643
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rdGuard
  have rdFit := morphoBlocks.morpho_block_11479_fallthrough
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hfit rdAlloc
  have rdDecode := morphoBlocks.morpho_block_11503
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rdFit
  exact ⟨_, _, _, rdDecode⟩

theorem morphoDecodeMarketParamsOk {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap} {k C : Nat} {ret ptr : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (hc : (marketParamsFromCalldata ee.calldata).Canonical)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 11655)
      (ret :: ptr :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret (ptr :: R)
      (marketParamsMem (marketParamsFromCalldata ee.calldata) ptr mem) aw' rdata σ k' C' := by
  dsimp only [MarketParamsWords.Canonical, marketParamsFromCalldata] at hc
  have rd0 := morphoBlocks.morpho_block_11655_fallthrough
    (immWords := wordsOf (immStore v)) hstack
    (by change UInt256.sub (calldataWord ee.calldata 4) (UInt256.land (calldataWord ee.calldata 4) solcAddrMask) = _
        rw [solcAddrMask_clean hc.1, u256_sub_self]; rfl) h
  have rd1 := morphoBlocks.morpho_block_11690_fallthrough
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by change UInt256.sub (calldataWord ee.calldata 36) (UInt256.land (calldataWord ee.calldata 36) solcAddrMask) = _
        rw [solcAddrMask_clean hc.2.1, u256_sub_self]; rfl) rd0
  have rd2 := morphoBlocks.morpho_block_11704_fallthrough
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by change UInt256.sub (calldataWord ee.calldata 68) (UInt256.land (calldataWord ee.calldata 68) solcAddrMask) = _
        rw [solcAddrMask_clean hc.2.2.1, u256_sub_self]; rfl) rd1
  have rd3 := morphoBlocks.morpho_block_11721_fallthrough
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by change UInt256.sub (calldataWord ee.calldata 100) (UInt256.land (calldataWord ee.calldata 100) solcAddrMask) = _
        rw [solcAddrMask_clean hc.2.2.2, u256_sub_self]; rfl) rd2
  have rdReturn := morphoBlocks.morpho_block_11738
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hvalid rd3
  exact ⟨_, _, _, rdReturn⟩

theorem morphoDecodeMarketParamsNoncanonical {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap} {k C : Nat} {ret ptr : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hnc : ¬ (marketParamsFromCalldata ee.calldata).Canonical)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 11655)
      (ret :: ptr :: R) mem aw rdata σ k C) : RDrev (deployedRuntime v) g s0 := by
  dsimp only [MarketParamsWords.Canonical, marketParamsFromCalldata] at hnc
  have hvalid : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 712) = true := by
    rw [morphoPatchedValidJumps v]; jump_dest
  by_cases h0 : (calldataWord ee.calldata 4).toNat < EVM.addressModulus
  · have rd0 := morphoBlocks.morpho_block_11655_fallthrough
      (immWords := wordsOf (immStore v)) hstack
      (by change UInt256.sub (calldataWord ee.calldata 4) (UInt256.land (calldataWord ee.calldata 4) solcAddrMask) = _
          rw [solcAddrMask_clean h0, u256_sub_self]; rfl) h
    by_cases h1 : (calldataWord ee.calldata 36).toNat < EVM.addressModulus
    · have rd1 := morphoBlocks.morpho_block_11690_fallthrough
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (by change UInt256.sub (calldataWord ee.calldata 36) (UInt256.land (calldataWord ee.calldata 36) solcAddrMask) = _
            rw [solcAddrMask_clean h1, u256_sub_self]; rfl) rd0
      by_cases h2 : (calldataWord ee.calldata 68).toNat < EVM.addressModulus
      · have rd2 := morphoBlocks.morpho_block_11704_fallthrough
          (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
          (by change UInt256.sub (calldataWord ee.calldata 68) (UInt256.land (calldataWord ee.calldata 68) solcAddrMask) = _
              rw [solcAddrMask_clean h2, u256_sub_self]; rfl) rd1
        have h3 : ¬ (calldataWord ee.calldata 100).toNat < EVM.addressModulus := fun hc => hnc ⟨h0, h1, h2, hc⟩
        have rdRev := morphoBlocks.morpho_block_11721_taken
          (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
          (addressMaskSub_nonzero h3) hvalid rd2
        exact morphoBlocks.morpho_block_712 (immWords := wordsOf (immStore v))
          (by simp only [morphoBlocks.morpho_block_11721_taken_stack, List.length_cons]; omega) rdRev
      · have rdRev := morphoBlocks.morpho_block_11704_taken
          (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
          (addressMaskSub_nonzero h2) hvalid rd1
        exact morphoBlocks.morpho_block_712 (immWords := wordsOf (immStore v))
          (by simp only [morphoBlocks.morpho_block_11704_taken_stack, List.length_cons]; omega) rdRev
    · have rdRev := morphoBlocks.morpho_block_11690_taken
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (addressMaskSub_nonzero h1) hvalid rd0
      exact morphoBlocks.morpho_block_712 (immWords := wordsOf (immStore v))
        (by simp only [morphoBlocks.morpho_block_11690_taken_stack, List.length_cons]; omega) rdRev
  · have rdRev := morphoBlocks.morpho_block_11655_taken
      (immWords := wordsOf (immStore v)) hstack (addressMaskSub_nonzero h0) hvalid h
    exact morphoBlocks.morpho_block_712 (immWords := wordsOf (immStore v))
      (by simp only [morphoBlocks.morpho_block_11655_taken_stack, List.length_cons]; omega) rdRev

end Benchmarks.Morpho.MorphoBlue
