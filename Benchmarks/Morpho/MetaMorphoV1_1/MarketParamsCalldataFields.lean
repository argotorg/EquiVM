import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsCalldata
import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsReturnMemory
import Benchmarks.Morpho.MetaMorphoV1_1.Decode
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_056
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_057

/-! The four canonical-address checks and five stores in the calldata struct decoder. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem marketParamsCalldataFields {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 9 ≤ 1024)
    (hlong : 164 ≤ I.calldata.size) (hfit : ptr.toNat + 160 < UInt256.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨11387⟩ (ret :: ptr :: R)
      mem aw rdata σ k C) :
    (¬ MarketParamsChecks (marketParamsArgs I.calldata) ∧ RDrev (deployedRuntime v) g s0) ∨
    (MarketParamsChecks (marketParamsArgs I.calldata) ∧ ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ret (ptr :: R)
        (marketParamsCopyMem mem ptr.toNat (marketParamsArgs I.calldata)) aw' rdata σ k' C') := by
  have hword (off : Nat) (hoff : off ≤ 128) :
      uInt256OfByteArray (I.calldata.readBytes (4 + off) 32) =
        calldataWord (marketParamsArgs I.calldata) off :=
    (marketParamsArgs_word (by omega)).symm
  have hadd (off : Nat) (hoff : off ≤ 160) :
      (ptr + UInt256.ofNat off).toNat = ptr.toNat + off :=
    uadd_word_ofNat_toNat ptr off (by omega)
  by_cases hc0 : (calldataWord (marketParamsArgs I.calldata) 0).toNat <
      EVM.addressModulus
  case neg =>
    have hg : UInt256.sub (uInt256OfByteArray (I.calldata.readBytes 4 32))
        (UInt256.land (uInt256OfByteArray (I.calldata.readBytes 4 32)) solcAddrMask) ≠
          ⟨0⟩ := by
      rw [hword 0 (by decide)]
      exact addressSubMask_nonzero _ hc0
    obtain ⟨_, _, _, hbad⟩ := metaMorphoV1_1_block_11387_taken_packed
      (immWords := wordsOf (immStore v)) (by omega) hg
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    exact .inl ⟨fun hc ↦ hc0 hc.2.1,
      metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
        (by simp only [metaMorphoV1_1_block_11387_taken_stack, List.length_cons]; omega) hbad⟩
  have hg0 : UInt256.sub (uInt256OfByteArray (I.calldata.readBytes 4 32))
      (UInt256.land (uInt256OfByteArray (I.calldata.readBytes 4 32)) solcAddrMask) =
        ⟨0⟩ := by
    rw [hword 0 (by decide)]
    exact addressSubMask_zero _ hc0
  obtain ⟨aw0, k0, C0, r0⟩ := metaMorphoV1_1_block_11387_fallthrough_packed
    (immWords := wordsOf (immStore v)) (by omega) hg0 rd
  simp only [metaMorphoV1_1_block_11387_fallthrough_stack] at r0
  by_cases hc32 : (calldataWord (marketParamsArgs I.calldata) 32).toNat <
      EVM.addressModulus
  case neg =>
    have hg : UInt256.sub (uInt256OfByteArray (I.calldata.readBytes 36 32))
        (UInt256.land (uInt256OfByteArray (I.calldata.readBytes 36 32)) solcAddrMask) ≠
          ⟨0⟩ := by
      rw [hword 32 (by decide)]
      exact addressSubMask_nonzero _ hc32
    obtain ⟨_, _, _, hbad⟩ := metaMorphoV1_1_block_11408_taken_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hg
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r0
    exact .inl ⟨fun hc ↦ hc32 hc.2.2.1,
      metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
        (by simp only [metaMorphoV1_1_block_11408_taken_stack, List.length_cons]; omega) hbad⟩
  have hg1 : UInt256.sub (uInt256OfByteArray (I.calldata.readBytes 36 32))
      (UInt256.land (uInt256OfByteArray (I.calldata.readBytes 36 32)) solcAddrMask) =
        ⟨0⟩ := by
    rw [hword 32 (by decide)]
    exact addressSubMask_zero _ hc32
  obtain ⟨aw1, k1, C1, r1⟩ := metaMorphoV1_1_block_11408_fallthrough_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hg1 r0
  simp only [metaMorphoV1_1_block_11408_fallthrough_stack] at r1
  by_cases hc64 : (calldataWord (marketParamsArgs I.calldata) 64).toNat <
      EVM.addressModulus
  case neg =>
    have hg : UInt256.sub (uInt256OfByteArray (I.calldata.readBytes 68 32))
        (UInt256.land (uInt256OfByteArray (I.calldata.readBytes 68 32)) solcAddrMask) ≠
          ⟨0⟩ := by
      rw [hword 64 (by decide)]
      exact addressSubMask_nonzero _ hc64
    obtain ⟨_, _, _, hbad⟩ := metaMorphoV1_1_block_11429_taken_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hg
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r1
    exact .inl ⟨fun hc ↦ hc64 hc.2.2.2.1,
      metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
        (by simp only [metaMorphoV1_1_block_11429_taken_stack, List.length_cons]; omega) hbad⟩
  have hg2 : UInt256.sub (uInt256OfByteArray (I.calldata.readBytes 68 32))
      (UInt256.land (uInt256OfByteArray (I.calldata.readBytes 68 32)) solcAddrMask) =
        ⟨0⟩ := by
    rw [hword 64 (by decide)]
    exact addressSubMask_zero _ hc64
  obtain ⟨aw2, k2, C2, r2⟩ := metaMorphoV1_1_block_11429_fallthrough_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hg2 r1
  simp only [metaMorphoV1_1_block_11429_fallthrough_stack] at r2
  by_cases hc96 : (calldataWord (marketParamsArgs I.calldata) 96).toNat <
      EVM.addressModulus
  case neg =>
    have hg : UInt256.sub (uInt256OfByteArray (I.calldata.readBytes 100 32))
        (UInt256.land (uInt256OfByteArray (I.calldata.readBytes 100 32)) solcAddrMask) ≠
          ⟨0⟩ := by
      rw [hword 96 (by decide)]
      exact addressSubMask_nonzero _ hc96
    obtain ⟨_, _, _, hbad⟩ := metaMorphoV1_1_block_11453_taken_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hg
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r2
    exact .inl ⟨fun hc ↦ hc96 hc.2.2.2.2,
      metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
        (by simp only [metaMorphoV1_1_block_11453_taken_stack, List.length_cons]; omega) hbad⟩
  have hg3 : UInt256.sub (uInt256OfByteArray (I.calldata.readBytes 100 32))
      (UInt256.land (uInt256OfByteArray (I.calldata.readBytes 100 32)) solcAddrMask) =
        ⟨0⟩ := by
    rw [hword 96 (by decide)]
    exact addressSubMask_zero _ hc96
  obtain ⟨aw3, k3, C3, r3⟩ := metaMorphoV1_1_block_11453_fallthrough_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hg3 r2
  simp only [metaMorphoV1_1_block_11453_fallthrough_stack] at r3
  obtain ⟨aw4, k4, C4, r4⟩ := metaMorphoV1_1_block_11477_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hret r3
  refine .inr ⟨⟨by rw [marketParamsArgs_size]; omega, hc0, hc32, hc64, hc96⟩,
    aw4, k4, C4, ?_⟩
  change RD (deployedRuntime v) I g s0 ret (ptr :: R)
    (writeWord (writeWord (writeWord (writeWord (writeWord mem ptr.toNat
      (calldataWord I.calldata 4)) (ptr + UInt256.ofNat 32).toNat
        (calldataWord I.calldata 36)) (ptr + UInt256.ofNat 64).toNat
          (calldataWord I.calldata 68)) (ptr + UInt256.ofNat 96).toNat
            (calldataWord I.calldata 100)) (ptr + UInt256.ofNat 128).toNat
              (calldataWord I.calldata 132)) aw4 rdata σ k4 C4 at r4
  have hw (off : Nat) (hoff : off ≤ 128) :
      calldataWord I.calldata (4 + off) = calldataWord (marketParamsArgs I.calldata) off :=
    hword off hoff
  rw [hadd 32 (by decide), hadd 64 (by decide), hadd 96 (by decide), hadd 128 (by decide),
    hw 0 (by decide), hw 32 (by decide), hw 64 (by decide), hw 96 (by decide),
    hw 128 (by decide)] at r4
  simpa only [marketParamsCopyMem, structReturnMemory, wordArrayWords, wordSequenceMemory,
    Nat.reduceAdd, Nat.reduceMul, Nat.add_assoc, Nat.add_zero] using r4

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
