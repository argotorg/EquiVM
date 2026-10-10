import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsCallMemory
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_073

/-! The market-parameter reader's initial allocation and fixed-size STATICCALL setup. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

theorem marketParamsZeroWrites (mem : ByteArray) (ptr : UInt256)
    (hfit : allocationFits ptr ⟨160⟩) :
    (⟨0⟩ : UInt256).toByteArray.write 0
      ((⟨0⟩ : UInt256).toByteArray.write 0
        ((⟨0⟩ : UInt256).toByteArray.write 0
          ((⟨0⟩ : UInt256).toByteArray.write 0
            ((⟨0⟩ : UInt256).toByteArray.write 0
              (writeWord mem 64 (nextCursor ptr ⟨160⟩)) ptr.toNat 32)
            (ptr + UInt256.ofNat 32).toNat 32)
          (ptr + UInt256.ofNat 64).toNat 32)
        (ptr + UInt256.ofNat 96).toNat 32)
      (ptr + UInt256.ofNat 128).toNat 32 = marketParamsInitialMem mem ptr := by
  have hb := (allocationFits_aligned ptr ⟨160⟩ (by decide +kernel)).mp hfit
  have hadd (n : Nat) (hn : n ≤ 160) : (ptr + UInt256.ofNat n).toNat = ptr.toNat + n :=
    uadd_word_ofNat_toNat ptr n (lt_trans (by change ptr.toNat + 160 < 2 ^ 64 at hb; omega)
      (by decide : 2 ^ 64 < UInt256.size))
  rw [hadd 32 (by decide), hadd 64 (by decide), hadd 96 (by decide), hadd 128 (by decide)]
  rfl

set_option maxRecDepth 2000 in
theorem marketParamsPrefixRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 9 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hfit : ¬ allocationFits ptr ⟨160⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨16116⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have h1 := metaMorphoV1_1_block_16116 (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  have hf : memLoad (UInt256.ofNat 64) mem = ptr := hfree
  simp only [metaMorphoV1_1_block_16116_stack, hf] at h1
  exact allocateStruct160Revert v (by simp only [List.length_cons]; omega) hfit h1

set_option maxRecDepth 2000 in
theorem marketParamsReachStaticcall {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr id : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hfit : allocationFits ptr ⟨160⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨16116⟩ (id :: R) mem aw rdata σ k C) :
    ∃ gasArg aw' k' C', RD (deployedRuntime v) I g s0 ⟨16221⟩
      (gasArg :: UInt256.land (wordsOf (immStore v) "MORPHO") solcAddrMask ::
        nextCursor ptr ⟨160⟩ :: ⟨36⟩ :: nextCursor ptr ⟨160⟩ :: ⟨160⟩ ::
        nextCursor ptr ⟨160⟩ :: R)
      (marketParamsCallMem (marketParamsInitialMem mem ptr) (nextCursor ptr ⟨160⟩).toNat id)
      aw' rdata σ k' C' := by
  have h1 := metaMorphoV1_1_block_16116 (immWords := wordsOf (immStore v)) (by
    simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  have hf : memLoad (UInt256.ofNat 64) mem = ptr := hfree
  simp only [metaMorphoV1_1_block_16116_stack, hf] at h1
  obtain ⟨aw1, k1, C1, h2⟩ := allocateStruct160Return v
    (by simp only [List.length_cons]; omega) hfit
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
  obtain ⟨aw2, k2, C2, h3⟩ := metaMorphoV1_1_block_16131_packed
    (immWords := wordsOf (immStore v)) (by omega) h2
  have hcursor : memLoad (UInt256.ofNat 64) (marketParamsInitialMem mem ptr) =
      nextCursor ptr ⟨160⟩ := marketParamsInitialMem_free mem ptr hlo
  have h4 : (nextCursor ptr ⟨160⟩ + UInt256.ofNat 4).toNat =
      (nextCursor ptr ⟨160⟩).toNat + 4 :=
    uadd_word_ofNat_toNat _ 4 (by have hp := hfit.1; change _ < 2 ^ 256; omega)
  simp only [metaMorphoV1_1_block_16131_stack, metaMorphoV1_1_block_16131_memory,
    marketParamsZeroWrites mem ptr hfit, hcursor, h4] at h3
  exact ⟨_, aw2, k2, C2, h3⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
