import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsReturnMemory

/-! The address checks and five field stores in the market-parameter decoder. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem marketParamsAddressCases {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {ptr value ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hload : memLoad ptr mem = value)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨16096⟩ (ptr :: ret :: R)
      mem aw out σ k C) :
    (¬ value.toNat < EVM.addressModulus ∧ RDrev (deployedRuntime v) g s0) ∨
    (value.toNat < EVM.addressModulus ∧ ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ret (value :: R) mem aw' out σ k' C') := by
  by_cases hc : value.toNat < EVM.addressModulus
  · have hguard : UInt256.sub (memLoad ptr mem)
        (UInt256.land (memLoad ptr mem) solcAddrMask) = ⟨0⟩ := by
      rw [hload, solcAddrMask_clean hc]
      exact u256_sub_self _
    have h1 := metaMorphoV1_1_block_16096_fallthrough
      (immWords := wordsOf (immStore v)) hstack hguard rd
    obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_16115_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hret h1
    exact .inr ⟨hc, aw2, k2, C2, by simpa only [metaMorphoV1_1_block_16115_stack,
      metaMorphoV1_1_block_16096_fallthrough_stack, hload] using h2⟩
  · have hguard : UInt256.sub (memLoad ptr mem)
        (UInt256.land (memLoad ptr mem) solcAddrMask) ≠ ⟨0⟩ := by
      rw [hload]
      intro hz
      have he := u256_sub_eq_zero_iff_eq.mp hz
      apply hc
      calc value.toNat = (UInt256.land value solcAddrMask).toNat := congrArg UInt256.toNat he
           _ < EVM.addressModulus := solcAddrMask_result_canonical value
    have h1 := metaMorphoV1_1_block_16096_taken
      (immWords := wordsOf (immStore v)) hstack hguard
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    exact .inl ⟨hc, metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
      (by simp only [metaMorphoV1_1_block_16096_taken_stack, List.length_cons]; omega) h1⟩

set_option maxRecDepth 2000 in
theorem marketParamsDecodeFields {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {ptr dst ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024)
    (hlong : 160 ≤ out.size) (hmem : ptr.toNat + 160 ≤ mem.size)
    (hsep : ptr.toNat + 160 ≤ dst.toNat) (hdst : dst.toNat + 160 < UInt256.size)
    (hread : ∀ off, off + 32 ≤ 160 →
      memLoad (ptr + UInt256.ofNat off) mem = calldataWord out off)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨16288⟩
      (ptr :: ⟨128⟩ :: dst :: ret :: R) mem aw out σ k C) :
    (¬ MarketParamsChecks out ∧ RDrev (deployedRuntime v) g s0) ∨
    (MarketParamsChecks out ∧ ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ret (dst :: R)
        (marketParamsCopyMem mem dst.toNat out) aw' out σ k' C') := by
  have hp : ptr.toNat + 160 < UInt256.size := by omega
  have hadd (n : Nat) (hn : n ≤ 160) :
      (dst + UInt256.ofNat n).toNat = dst.toNat + n :=
    uadd_word_ofNat_toNat dst n (by omega)
  have h0 := metaMorphoV1_1_block_16288 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  rcases marketParamsAddressCases v (by simp only [List.length_cons]; omega)
      (by simpa only [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_add_zero]
        using hread 0 (by decide))
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h0 with
    hbad | ⟨hc0, aw0, k0, C0, hr0⟩
  · exact .inl ⟨fun hc ↦ hbad.1 hc.2.1, hbad.2⟩
  let m1 := writeWord mem dst.toNat (calldataWord out 0)
  have hm1 : ptr.toNat + 160 ≤ m1.size := by dsimp [m1]; rw [writeWord_sparse_size]; omega
  have hread1 := wordWindowRead_write dst.toNat (calldataWord out 0) hmem hsep hp hread
  obtain ⟨aw1, k1, C1, hr1⟩ := metaMorphoV1_1_block_16297_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) hr0
  rcases marketParamsAddressCases v (by simp only [List.length_cons]; omega)
      (hread1 32 (by decide))
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) hr1 with
    hbad | ⟨hc32, aw2, k2, C2, hr2⟩
  · exact .inl ⟨fun hc ↦ hbad.1 hc.2.2.1, hbad.2⟩
  let m2 := writeWord m1 (dst.toNat + 32) (calldataWord out 32)
  have hm2 : ptr.toNat + 160 ≤ m2.size := by dsimp [m2]; rw [writeWord_sparse_size]; omega
  have hread2 := wordWindowRead_write (dst.toNat + 32) (calldataWord out 32)
    hm1 (by omega) hp hread1
  obtain ⟨aw3, k3, C3, hr3⟩ := metaMorphoV1_1_block_16311_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) hr2
  simp only [metaMorphoV1_1_block_16311_stack, metaMorphoV1_1_block_16311_memory,
    hadd 32 (by decide)] at hr3
  rcases marketParamsAddressCases v (by simp only [List.length_cons]; omega)
      (hread2 64 (by decide))
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) hr3 with
    hbad | ⟨hc64, aw4, k4, C4, hr4⟩
  · exact .inl ⟨fun hc ↦ hbad.1 hc.2.2.2.1, hbad.2⟩
  let m3 := writeWord m2 (dst.toNat + 64) (calldataWord out 64)
  have hm3 : ptr.toNat + 160 ≤ m3.size := by dsimp [m3]; rw [writeWord_sparse_size]; omega
  have hread3 := wordWindowRead_write (dst.toNat + 64) (calldataWord out 64)
    hm2 (by omega) hp hread2
  obtain ⟨aw5, k5, C5, hr5⟩ := metaMorphoV1_1_block_16328_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) hr4
  simp only [metaMorphoV1_1_block_16328_stack, metaMorphoV1_1_block_16328_memory,
    hadd 64 (by decide)] at hr5
  rcases marketParamsAddressCases v (by simp only [List.length_cons]; omega)
      (hread3 96 (by decide))
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) hr5 with
    hbad | ⟨hc96, aw6, k6, C6, hr6⟩
  · exact .inl ⟨fun hc ↦ hbad.1 hc.2.2.2.2, hbad.2⟩
  have hread4 := wordWindowRead_write (dst.toNat + 96) (calldataWord out 96)
    hm3 (by omega) hp hread3
  obtain ⟨aw7, k7, C7, hr7⟩ := metaMorphoV1_1_block_16345_packed
    (immWords := wordsOf (immStore v)) (by omega) hret hr6
  have hm : metaMorphoV1_1_block_16345_memory (mem := m3) (x0 := calldataWord out 96)
      (x1 := ptr) (x2 := ⟨128⟩) (x3 := dst) = marketParamsCopyMem mem dst.toNat out := by
    simp only [metaMorphoV1_1_block_16345_memory, hadd 96 (by decide), hadd 128 (by decide)]
    rw [show memLoad (ptr + (⟨128⟩ : UInt256))
      ((calldataWord out 96).toByteArray.write 0 m3 (dst.toNat + 96) 32) =
        calldataWord out 128 from hread4 128 (by decide)]
    simp only [marketParamsCopyMem, structReturnMemory, wordArrayWords, wordSequenceMemory,
      Nat.reduceAdd, Nat.reduceMul, Nat.add_assoc, m3, m2, m1]
    rfl
  change RD (deployedRuntime v) I g s0 ret (dst :: R)
    (metaMorphoV1_1_block_16345_memory (mem := m3) (x0 := calldataWord out 96)
      (x1 := ptr) (x2 := ⟨128⟩) (x3 := dst)) aw7 out σ k7 C7 at hr7
  rw [hm] at hr7
  exact .inr ⟨⟨hlong, hc0, hc32, hc64, hc96⟩, aw7, k7, C7, hr7⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
