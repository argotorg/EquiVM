import Benchmarks.Morpho.MetaMorphoV1_1.WordArraySizeRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.WordArrayInitMemory
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_041

/-! The two checked memory allocations before the withdrawal-queue loops. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem updateWithdrawQueueSeenAllocation {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {data len : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 11 ≤ 1024)
    (hcd : I.calldata.size < UInt256.size) (hmem : mem.size ≤ 128)
    (hfree : memLoad ⟨64⟩ mem = ⟨128⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨8067⟩ (data :: len :: R) mem aw out σ k C) :
    let curr := codeOwnerStorageWord I σ ⟨21⟩
    (solcMaxU64 < curr.toNat ∧ RDrev (deployedRuntime v) g s0) ∨
    (curr.toNat ≤ solcMaxU64 ∧ ¬ 160 + 32 * curr.toNat < 2 ^ 64 ∧
      RDrev (deployedRuntime v) g s0) ∨
    (curr.toNat ≤ solcMaxU64 ∧ 160 + 32 * curr.toNat < 2 ^ 64 ∧ ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ⟨12021⟩ (len :: ⟨8122⟩ :: ⟨128⟩ :: curr ::
        data :: len :: R) (wordArrayInitMemory mem ⟨128⟩ curr.toNat) aw' out σ k' C') := by
  dsimp only
  let curr := codeOwnerStorageWord I σ ⟨21⟩
  obtain ⟨k1, C1, r1⟩ := metaMorphoV1_1_block_8067 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  change RD (deployedRuntime v) I g s0 ⟨12021⟩
    (curr :: ⟨8078⟩ :: curr :: data :: len :: R) mem aw out σ k1 C1 at r1
  by_cases hc : curr.toNat ≤ solcMaxU64
  case neg =>
    exact .inl ⟨Nat.lt_of_not_ge hc, wordArraySizeRevert v
      (by simp only [List.length_cons]; omega) (Nat.lt_of_not_ge hc) r1⟩
  obtain ⟨k2, C2, r2⟩ := wordArraySizeReturn v
    (by simp only [List.length_cons]; omega) hc
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r1
  have r3 := metaMorphoV1_1_block_8078 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r2
  change RD (deployedRuntime v) I g s0 ⟨11329⟩
    (memLoad ⟨64⟩ mem :: UInt256.ofNat (32 + 32 * curr.toNat) :: ⟨8091⟩ ::
      memLoad ⟨64⟩ mem :: curr :: data :: len :: R) mem _ out σ _ _ at r3
  rw [hfree] at r3
  by_cases hfit : 160 + 32 * curr.toNat < 2 ^ 64
  case neg =>
    exact .inr (.inl ⟨hc, hfit, allocateRoundedRevert v
      (by simp only [List.length_cons]; omega)
      (by rw [wordArrayAllocationFits _ hc]; exact hfit) r3⟩)
  obtain ⟨aw4, k4, C4, r4⟩ := allocateRoundedReturn v
    (by simp only [List.length_cons]; omega)
    ((wordArrayAllocationFits ⟨128⟩ hc).mpr hfit)
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r3
  rw [wordArrayNextCursor _ hc] at r4
  obtain ⟨aw5, k5, C5, r5⟩ := metaMorphoV1_1_block_8091_packed
    (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r4
  have r5' : RD (deployedRuntime v) I g s0 ⟨12021⟩
    (curr :: ⟨8106⟩ :: UInt256.lnot ⟨31⟩ :: ⟨128⟩ :: curr :: data :: len :: R)
    (wordArrayInitMemory mem ⟨128⟩ curr.toNat) aw5 out σ k5 C5 := by
    simpa only [metaMorphoV1_1_block_8091_stack, metaMorphoV1_1_block_8091_memory,
      wordArrayInitMemory, u256_ofNat_toNat] using r5
  obtain ⟨k6, C6, r6⟩ := wordArraySizeReturn v
    (by simp only [List.length_cons]; omega) hc
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r5'
  obtain ⟨aw7, k7, C7, r7⟩ := metaMorphoV1_1_block_8106_packed
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r6
  have hsub : (UInt256.ofNat (32 + 32 * curr.toNat) + UInt256.lnot ⟨31⟩).toNat =
      32 * curr.toNat := wordArrayDataSize hc
  simp only [metaMorphoV1_1_block_8106_stack, metaMorphoV1_1_block_8106_memory,
    UInt256.toNat_ofNat_of_lt hcd, hsub] at r7
  have hz := wordArrayInitMemory_zeroCopy mem I.calldata ⟨128⟩ curr.toNat hmem
    (by decide) (by decide)
  change I.calldata.write I.calldata.size (wordArrayInitMemory mem ⟨128⟩ curr.toNat)
    (⟨128⟩ + UInt256.ofNat 32).toNat (32 * curr.toNat) = _ at hz
  rw [hz] at r7
  exact .inr (.inr ⟨hc, hfit, aw7, k7, C7, r7⟩)

theorem updateWithdrawQueueArrayAllocation {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr seen curr data len : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 11 ≤ 1024)
    (hcd : I.calldata.size < UInt256.size) (hmem : mem.size ≤ ptr.toNat)
    (hptr : 96 ≤ ptr.toNat) (hfree : memLoad ⟨64⟩ mem = ptr)
    (rd : RD (deployedRuntime v) I g s0 ⟨12021⟩
      (len :: ⟨8122⟩ :: seen :: curr :: data :: len :: R) mem aw out σ k C) :
    (solcMaxU64 < len.toNat ∧ RDrev (deployedRuntime v) g s0) ∨
    (len.toNat ≤ solcMaxU64 ∧ ¬ ptr.toNat + 32 + 32 * len.toNat < 2 ^ 64 ∧
      RDrev (deployedRuntime v) g s0) ∨
    (len.toNat ≤ solcMaxU64 ∧ ptr.toNat + 32 + 32 * len.toNat < 2 ^ 64 ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨8163⟩
        (⟨0⟩ :: len :: data :: seen :: curr :: ptr :: (ptr + ⟨32⟩) :: R)
        (wordArrayInitMemory mem ptr len.toNat) aw' out σ k' C') := by
  by_cases hn : len.toNat ≤ solcMaxU64
  case neg =>
    exact .inl ⟨Nat.lt_of_not_ge hn, wordArraySizeRevert v
      (by simp only [List.length_cons]; omega) (Nat.lt_of_not_ge hn) rd⟩
  obtain ⟨k1, C1, r1⟩ := wordArraySizeReturn v
    (by simp only [List.length_cons]; omega) hn
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd
  have r2 := metaMorphoV1_1_block_8122 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r1
  change RD (deployedRuntime v) I g s0 ⟨11329⟩
    (memLoad ⟨64⟩ mem :: UInt256.ofNat (32 + 32 * len.toNat) :: ⟨8136⟩ :: data ::
      seen :: curr :: memLoad ⟨64⟩ mem :: len :: R) mem _ out σ _ _ at r2
  rw [hfree] at r2
  by_cases hfit : ptr.toNat + 32 + 32 * len.toNat < 2 ^ 64
  case neg =>
    exact .inr (.inl ⟨hn, hfit, allocateRoundedRevert v
      (by simp only [List.length_cons]; omega)
      (by rw [wordArrayAllocationFits _ hn]; exact hfit) r2⟩)
  obtain ⟨aw3, k3, C3, r3⟩ := allocateRoundedReturn v
    (by simp only [List.length_cons]; omega) ((wordArrayAllocationFits ptr hn).mpr hfit)
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r2
  rw [wordArrayNextCursor _ hn] at r3
  obtain ⟨aw4, k4, C4, r4⟩ := metaMorphoV1_1_block_8136_packed
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r3
  have r4' : RD (deployedRuntime v) I g s0 ⟨12021⟩
      (len :: ⟨8148⟩ :: data :: seen :: curr :: ptr :: len :: R)
      (wordArrayInitMemory mem ptr len.toNat) aw4 out σ k4 C4 := by
    simpa only [metaMorphoV1_1_block_8136_stack, metaMorphoV1_1_block_8136_memory,
      wordArrayInitMemory, u256_ofNat_toNat] using r4
  obtain ⟨k5, C5, r5⟩ := wordArraySizeReturn v
    (by simp only [List.length_cons]; omega) hn
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r4'
  obtain ⟨aw6, k6, C6, r6⟩ := metaMorphoV1_1_block_8148_packed
    (immWords := wordsOf (immStore v)) (by omega) r5
  have hsub : (UInt256.lnot (UInt256.ofNat 31) + UInt256.ofNat (32 + 32 * len.toNat)).toNat =
      32 * len.toNat := by
    rw [u256_add_comm]
    exact wordArrayDataSize hn
  simp only [metaMorphoV1_1_block_8148_stack, metaMorphoV1_1_block_8148_memory,
    UInt256.toNat_ofNat_of_lt hcd, hsub] at r6
  have hz := wordArrayInitMemory_zeroCopy mem I.calldata ptr len.toNat hmem hptr
    (lt_trans (by omega : ptr.toNat + 32 < 2 ^ 64) (by decide))
  change I.calldata.write I.calldata.size (wordArrayInitMemory mem ptr len.toNat)
    (ptr + UInt256.ofNat 32).toNat (32 * len.toNat) = _ at hz
  rw [hz] at r6
  exact .inr (.inr ⟨hn, hfit, aw6, k6, C6, r6⟩)

end Benchmarks.Morpho.MetaMorphoV1_1
