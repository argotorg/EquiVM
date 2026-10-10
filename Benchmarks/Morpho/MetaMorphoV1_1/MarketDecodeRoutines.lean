import Benchmarks.Morpho.MetaMorphoV1_1.MarketReturnMemory
import Benchmarks.Morpho.MetaMorphoV1_1.MarketABI

/-! The uint128 validators and six field stores in the market decoder. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

def uint128Mask : UInt256 :=
  UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)

set_option maxRecDepth 2000 in
theorem marketUint128Cases {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {ptr value ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hload : memLoad ptr mem = value)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨14809⟩ (ptr :: ret :: R)
      mem aw out σ k C) :
    (¬ value.toNat < 2 ^ 128 ∧ RDrev (deployedRuntime v) g s0) ∨
    (value.toNat < 2 ^ 128 ∧ ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ret (value :: R) mem aw' out σ k' C') := by
  have hmask : uint128Mask.toNat = 2 ^ 128 - 1 := by decide +kernel
  by_cases hc : value.toNat < 2 ^ 128
  · have hguard : UInt256.sub (memLoad ptr mem)
        (UInt256.land (memLoad ptr mem) uint128Mask) = ⟨0⟩ := by
      rw [hload, u256LandMaskCleanOfToNat value uint128Mask hmask hc]
      exact u256_sub_self _
    have h1 := metaMorphoV1_1_block_14809_fallthrough
      (immWords := wordsOf (immStore v)) hstack hguard rd
    obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_14828_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hret h1
    exact .inr ⟨hc, aw2, k2, C2, by simpa only [metaMorphoV1_1_block_14828_stack,
      metaMorphoV1_1_block_14809_fallthrough_stack, hload] using h2⟩
  · have hguard : UInt256.sub (memLoad ptr mem)
        (UInt256.land (memLoad ptr mem) uint128Mask) ≠ ⟨0⟩ := by
      rw [hload]
      intro hz
      have he := u256_sub_eq_zero_iff_eq.mp hz
      apply hc
      calc value.toNat = (UInt256.land value uint128Mask).toNat := congrArg UInt256.toNat he
           _ < 2 ^ 128 := u256LandMaskToNatLtOfToNat value uint128Mask hmask
    have h1 := metaMorphoV1_1_block_14809_taken
      (immWords := wordsOf (immStore v)) hstack hguard
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    exact .inl ⟨hc, metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
      (by simp only [metaMorphoV1_1_block_14809_taken_stack, List.length_cons]; omega) h1⟩

set_option maxRecDepth 2000 in
theorem marketDecodeFields {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {ptr dst ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 11 ≤ 1024)
    (hlong : 192 ≤ out.size) (hmem : ptr.toNat + 192 ≤ mem.size)
    (hsep : ptr.toNat + 192 ≤ dst.toNat) (hdst : dst.toNat + 192 < UInt256.size)
    (hread : ∀ off, off + 32 ≤ 192 →
      memLoad (ptr + UInt256.ofNat off) mem = calldataWord out off)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨14858⟩
      (ptr :: ⟨160⟩ :: ⟨14943⟩ :: dst :: ret :: R) mem aw out σ k C) :
    (¬ MarketChecks out ∧ RDrev (deployedRuntime v) g s0) ∨
    (MarketChecks out ∧ ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ret (dst :: R)
        (marketCopyMem mem dst.toNat out) aw' out σ k' C') := by
  have hp : ptr.toNat + 192 < UInt256.size := by omega
  have hadd (n : Nat) (hn : n ≤ 192) :
      (dst + UInt256.ofNat n).toNat = dst.toNat + n :=
    uadd_word_ofNat_toNat dst n (by omega)
  have h0 := metaMorphoV1_1_block_14858 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  rcases marketUint128Cases v (by simp only [List.length_cons]; omega)
      (by simpa only [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_add_zero]
        using hread 0 (by decide))
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h0 with
    hbad | ⟨hc0, aw0, k0, C0, hr0⟩
  · exact .inl ⟨fun hc ↦ hbad.1 hc.2.1, hbad.2⟩
  let m1 := writeWord mem dst.toNat (calldataWord out 0)
  have hm1 : ptr.toNat + 192 ≤ m1.size := by dsimp [m1]; rw [writeWord_sparse_size]; omega
  have hread1 := wordWindowRead_write dst.toNat (calldataWord out 0) hmem hsep hp hread
  obtain ⟨aw1, k1, C1, hr1⟩ := metaMorphoV1_1_block_14867_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) hr0
  rcases marketUint128Cases v (by simp only [List.length_cons]; omega)
      (hread1 32 (by decide))
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) hr1 with
    hbad | ⟨hc32, aw2, k2, C2, hr2⟩
  · exact .inl ⟨fun hc ↦ hbad.1 hc.2.2.1, hbad.2⟩
  let m2 := writeWord m1 (dst.toNat + 32) (calldataWord out 32)
  have hm2 : ptr.toNat + 192 ≤ m2.size := by dsimp [m2]; rw [writeWord_sparse_size]; omega
  have hread2 := wordWindowRead_write (dst.toNat + 32) (calldataWord out 32)
    hm1 (by omega) hp hread1
  obtain ⟨aw3, k3, C3, hr3⟩ := metaMorphoV1_1_block_14881_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) hr2
  simp only [metaMorphoV1_1_block_14881_stack, metaMorphoV1_1_block_14881_memory,
    hadd 32 (by decide)] at hr3
  rcases marketUint128Cases v (by simp only [List.length_cons]; omega)
      (hread2 64 (by decide))
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) hr3 with
    hbad | ⟨hc64, aw4, k4, C4, hr4⟩
  · exact .inl ⟨fun hc ↦ hbad.1 hc.2.2.2.1, hbad.2⟩
  let m3 := writeWord m2 (dst.toNat + 64) (calldataWord out 64)
  have hm3 : ptr.toNat + 192 ≤ m3.size := by dsimp [m3]; rw [writeWord_sparse_size]; omega
  have hread3 := wordWindowRead_write (dst.toNat + 64) (calldataWord out 64)
    hm2 (by omega) hp hread2
  obtain ⟨aw5, k5, C5, hr5⟩ := metaMorphoV1_1_block_14898_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) hr4
  simp only [metaMorphoV1_1_block_14898_stack, metaMorphoV1_1_block_14898_memory,
    hadd 64 (by decide)] at hr5
  rcases marketUint128Cases v (by simp only [List.length_cons]; omega)
      (hread3 96 (by decide))
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) hr5 with
    hbad | ⟨hc96, aw6, k6, C6, hr6⟩
  · exact .inl ⟨fun hc ↦ hbad.1 hc.2.2.2.2.1, hbad.2⟩
  let m4 := writeWord m3 (dst.toNat + 96) (calldataWord out 96)
  have hm4 : ptr.toNat + 192 ≤ m4.size := by dsimp [m4]; rw [writeWord_sparse_size]; omega
  have hread4 := wordWindowRead_write (dst.toNat + 96) (calldataWord out 96)
    hm3 (by omega) hp hread3
  obtain ⟨aw7, k7, C7, hr7⟩ := metaMorphoV1_1_block_14915_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) hr6
  simp only [metaMorphoV1_1_block_14915_stack, metaMorphoV1_1_block_14915_memory,
    hadd 96 (by decide)] at hr7
  rcases marketUint128Cases v (by simp only [List.length_cons]; omega)
      (hread4 128 (by decide))
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) hr7 with
    hbad | ⟨hc128, aw8, k8, C8, hr8⟩
  · exact .inl ⟨fun hc ↦ hbad.1 hc.2.2.2.2.2.1, hbad.2⟩
  let m5 := writeWord m4 (dst.toNat + 128) (calldataWord out 128)
  have hread5 := wordWindowRead_write (dst.toNat + 128) (calldataWord out 128)
    hm4 (by omega) hp hread4
  obtain ⟨aw9, k9, C9, hr9⟩ := metaMorphoV1_1_block_14932_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) hr8
  simp only [metaMorphoV1_1_block_14932_stack, metaMorphoV1_1_block_14932_memory,
    hadd 128 (by decide)] at hr9
  rcases marketUint128Cases v (by simp only [List.length_cons]; omega)
      (hread5 160 (by decide))
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) hr9 with
    hbad | ⟨hc160, aw10, k10, C10, hr10⟩
  · exact .inl ⟨fun hc ↦ hbad.1 hc.2.2.2.2.2.2, hbad.2⟩
  obtain ⟨aw11, k11, C11, hr11⟩ := metaMorphoV1_1_block_14943_packed
    (immWords := wordsOf (immStore v)) (by omega) hret hr10
  have hm : metaMorphoV1_1_block_14943_memory (mem := m5) (x0 := calldataWord out 160)
      (x1 := dst) = marketCopyMem mem dst.toNat out := by
    simp only [metaMorphoV1_1_block_14943_memory, hadd 160 (by decide), marketCopyMem,
      structReturnMemory, wordArrayWords, wordSequenceMemory, Nat.reduceAdd,
      Nat.reduceMul, Nat.add_assoc, m5, m4, m3, m2, m1]
    rfl
  change RD (deployedRuntime v) I g s0 ret (dst :: R)
    (metaMorphoV1_1_block_14943_memory (mem := m5) (x0 := calldataWord out 160)
      (x1 := dst)) aw11 out σ k11 C11 at hr11
  rw [hm] at hr11
  exact .inr ⟨⟨hlong, hc0, hc32, hc64, hc96, hc128, hc160⟩, aw11, k11, C11, hr11⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
