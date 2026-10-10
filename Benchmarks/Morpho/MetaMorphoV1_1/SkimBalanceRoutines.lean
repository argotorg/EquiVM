import Benchmarks.Morpho.MetaMorphoV1_1.TokenBalanceMemory
import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawableRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_017
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_018

/-! Skim's balance call and its fixed-size return reservation. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem skimBalanceCall {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr recipient : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (token : AccountAddress)
    (hstack : R.length + 9 ≤ 1024) (hs : SourceState s0 I σ evm)
    (hptr : ptr.toNat < 2 ^ 64) (hfree : memLoad ⟨64⟩ mem = ptr)
    (rd : RD (deployedRuntime v) I g s0 ⟨2755⟩
      (UInt256.ofNat token.toNat :: recipient :: R) mem aw rdata σ k C) :
    ∃ (evm' : State) (ok : Bool) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      typedCallViaEVM config evm token "balanceOf" 0 [.address I.codeOwner]
        (ok, evm', out) false ∧
      SourceState s0 I evm'.accountMap evm' ∧ out.size < UInt256.size ∧
      RD (deployedRuntime v) I g s0 ⟨2796⟩
        ((if ok then ⟨1⟩ else ⟨0⟩) :: recipient :: ptr :: UInt256.ofNat token.toNat :: R)
        (fixedReturnBuffer (tokenBalanceCallMem mem ptr.toNat I.codeOwner) ptr out 32)
        aw' out evm'.accountMap k' C' := by
  change memLoad (UInt256.ofNat 64) mem = ptr at hfree
  have h4 := uadd_word_ofNat_toNat ptr 4 (by change _ < 2 ^ 256; omega)
  have hm : metaMorphoV1_1_block_2755_memory (ee := I) (mem := mem) =
      tokenBalanceCallMem mem ptr.toNat I.codeOwner := by
    simp only [metaMorphoV1_1_block_2755_memory, hfree, h4]
    rfl
  have hmask : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) (UInt256.ofNat token.toNat) = UInt256.ofNat token.toNat :=
    easWord_mask token
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_2755_packed
    (immWords := wordsOf (immStore v)) hstack rd
  simp only [metaMorphoV1_1_block_2755_stack, hfree, hmask, hm] at h1
  have hdec : decode (deployedRuntime v) ⟨2795⟩ = some (.STATICCALL, none) := by
    change decode (immutableLayout.runtime metaMorphoV1_1Bytecode
      (wordsOf (immStore v))) _ = _
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨2795⟩ : UInt256), UInt8.ofNat 250, .STATICCALL, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  exact typedStaticcallSimulation (by simp only [List.length_cons]; omega) hdec hs
    (by symm; rw [accountAddress_ofUInt256_eq_ofNat_toNat]
        exact accountAddress_of_word_val token)
    (by change _ = some ((tokenBalanceCallMem mem ptr.toNat I.codeOwner).readWithPadding
      ptr.toNat 36); rw [tokenBalanceEncode I.codeOwner, tokenBalanceCallMem_read]) h1

theorem skimBalanceCallFailure {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {recipient ptr : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (hout : out.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨2796⟩ (⟨0⟩ :: recipient :: ptr :: R)
      mem aw out σ k C) : RDrev (deployedRuntime v) g s0 := by
  have hfail := metaMorphoV1_1_block_2796_taken (immWords := wordsOf (immStore v))
    (by omega) (by decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_2921 (immWords := wordsOf (immStore v))
    (by simp only [metaMorphoV1_1_block_2796_taken_stack, List.length_cons]; omega)
    (by change 0 + (UInt256.ofNat out.size).toNat ≤ out.size
        rw [UInt256.toNat_ofNat_of_lt hout, Nat.zero_add]) hfail

theorem skimBalanceReturnAllocation {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {recipient ptr : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 11 ≤ 1024)
    (hout : out.size < UInt256.size) (hfit : allocationFits ptr ⟨32⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨2796⟩ (⟨1⟩ :: recipient :: ptr :: R)
      mem aw out σ k C) :
    (out.size < 32 ∧ RDrev (deployedRuntime v) g s0) ∨
      (32 ≤ out.size ∧ ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨2904⟩
        (ptr :: recipient :: R) (writeWord mem 64 (nextCursor ptr ⟨32⟩)) aw' out σ k' C') := by
  have h1 := metaMorphoV1_1_block_2796_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) (by decide) rd
  have h2 := metaMorphoV1_1_block_2803_taken (immWords := wordsOf (immStore v))
    (by omega) (by decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  by_cases hl : 32 ≤ out.size
  · have h3 := metaMorphoV1_1_block_2867_fallthrough (immWords := wordsOf (immStore v))
      (by omega) (ugt_zero (by simpa only [UInt256.toNat_ofNat_of_lt hout] using hl)) h2
    have h4 := metaMorphoV1_1_block_2882 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
    obtain ⟨aw5, k5, C5, h5⟩ := allocateRoundedReturn v
      (by simp only [List.length_cons]; omega) hfit
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h4
    obtain ⟨aw6, k6, C6, h6⟩ := metaMorphoV1_1_block_2895_fallthrough_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
      (by rw [word_add_sub_left]; decide +kernel) h5
    exact .inr ⟨hl, aw6, k6, C6, h6⟩
  · have h3 := metaMorphoV1_1_block_2867_taken (immWords := wordsOf (immStore v))
      (by omega)
      (by rw [ugt_one (by simpa only [UInt256.toNat_ofNat_of_lt hout] using
            Nat.lt_of_not_ge hl)]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
    have h4 := metaMorphoV1_1_block_2913 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
    have h5 := metaMorphoV1_1_block_2882 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h4
    refine .inl ⟨by omega, ?_⟩
    by_cases hf : allocationFits ptr (UInt256.ofNat out.size)
    · obtain ⟨aw6, k6, C6, h6⟩ := allocateRoundedReturn v
        (by simp only [List.length_cons]; omega) hf
        (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h5
      have h7 := metaMorphoV1_1_block_2895_taken (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega)
        (by rw [word_add_sub_left, slt_ofNat_lit_one_low (by decide) (by omega)]; decide)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h6
      exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
        (by simp only [metaMorphoV1_1_block_2895_taken_stack, List.length_cons]; omega) h7
    · exact allocateRoundedRevert v (by simp only [List.length_cons]; omega) hf h5

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
