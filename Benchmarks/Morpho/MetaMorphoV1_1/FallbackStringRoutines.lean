import Benchmarks.Morpho.MetaMorphoV1_1.FallbackStringCopy
import Benchmarks.Morpho.MetaMorphoV1_1.FallbackStringAllocation
import Benchmarks.Morpho.MetaMorphoV1_1.Eip712StringSource
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_058
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_083

/-! The storage fallback branches of the two EIP-712 string getters. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

def fallbackStringPC (version : Bool) : UInt256 := if version then ⟨18548⟩ else ⟨18486⟩

theorem fallbackStringReachCopy {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {word ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (version : Bool) (free : Nat)
    (hstack : R.length + 8 ≤ 1024) (hptr : memLoad ⟨64⟩ mem = UInt256.ofNat free)
    (rd : RD (deployedRuntime v) I g s0 (fallbackStringPC version)
      (word :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨11857⟩
      (domainStringFallbackSlot version :: UInt256.ofNat free :: ⟨18505⟩ ::
        UInt256.ofNat free :: ⟨11757⟩ :: UInt256.ofNat free :: ret :: R)
      mem aw' rdata σ k' C' := by
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free at hptr
  cases version
  · obtain ⟨aw', k', C', h⟩ := metaMorphoV1_1_block_18486_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨aw', k', C', by
      simpa only [metaMorphoV1_1_block_18486_stack, hptr, domainStringFallbackSlot,
        Bool.false_eq_true, if_false] using h⟩
  · obtain ⟨aw', k', C', h⟩ := metaMorphoV1_1_block_18548_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨aw', k', C', by
      simpa only [metaMorphoV1_1_block_18548_stack, hptr, domainStringFallbackSlot,
        if_true] using h⟩

theorem fallbackStringReachAllocation {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {word ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (version : Bool) (free : Nat)
    (hstack : R.length + 15 ≤ 1024) (hfree : free < 2 ^ 64)
    (hptr : memLoad ⟨64⟩ mem = UInt256.ofNat free)
    (hvalid : storageStringValid (codeOwnerStorageWord I σ (domainStringFallbackSlot version)))
    (rd : RD (deployedRuntime v) I g s0 (fallbackStringPC version)
      (word :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨11329⟩
      (UInt256.ofNat free :: stringCopySize
        (storageStringLength (codeOwnerStorageWord I σ (domainStringFallbackSlot version))) ::
        ⟨11757⟩ :: UInt256.ofNat free :: ret :: R)
      (fallbackStringMemory I σ mem (domainStringFallbackSlot version)
        (codeOwnerStorageWord I σ (domainStringFallbackSlot version)) free)
      aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := fallbackStringReachCopy v version free (by omega) hptr rd
  obtain ⟨aw2, k2, C2, h2⟩ := fallbackStringCopyReturn v free
    (by simp only [List.length_cons]; omega) hfree hvalid
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
  obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_18505_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
  have hsub := stringCopySize_subAt free _ hfree
    (storageStringLength_lt (codeOwnerStorageWord I σ (domainStringFallbackSlot version)))
  simp only [stringCopyEndAt] at hsub
  exact ⟨aw3, k3, C3, by
    simpa only [metaMorphoV1_1_block_18505_stack, hsub] using h3⟩

theorem fallbackStringReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {word ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (version : Bool) (free : Nat)
    (hstack : R.length + 15 ≤ 1024) (hfree : free < 2 ^ 64)
    (hptr : memLoad ⟨64⟩ mem = UInt256.ofNat free)
    (hvalid : storageStringValid (codeOwnerStorageWord I σ (domainStringFallbackSlot version)))
    (hfit : allocationFits (UInt256.ofNat free) (stringCopySize
      (storageStringLength (codeOwnerStorageWord I σ (domainStringFallbackSlot version)))))
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 (fallbackStringPC version)
      (word :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret (UInt256.ofNat free :: R)
      (writeWord (fallbackStringMemory I σ mem (domainStringFallbackSlot version)
        (codeOwnerStorageWord I σ (domainStringFallbackSlot version)) free) 64
        (stringCopyEndAt free (storageStringLength
          (codeOwnerStorageWord I σ (domainStringFallbackSlot version))))) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := fallbackStringReachAllocation v version free hstack
    hfree hptr hvalid rd
  obtain ⟨aw2, k2, C2, h2⟩ := allocateRoundedReturn v
    (by simp only [List.length_cons]; omega) hfit
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
  rw [stringCopyNextCursorAt free _ (storageStringLength_lt _)] at h2
  exact metaMorphoV1_1_block_11757_packed (immWords := wordsOf (immStore v))
    (by omega) hret h2

theorem fallbackStringRevertsAllocation {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {word ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (version : Bool) (free : Nat)
    (hstack : R.length + 15 ≤ 1024) (hfree : free < 2 ^ 64)
    (hptr : memLoad ⟨64⟩ mem = UInt256.ofNat free)
    (hvalid : storageStringValid (codeOwnerStorageWord I σ (domainStringFallbackSlot version)))
    (hbad : ¬ allocationFits (UInt256.ofNat free) (stringCopySize
      (storageStringLength (codeOwnerStorageWord I σ (domainStringFallbackSlot version)))))
    (rd : RD (deployedRuntime v) I g s0 (fallbackStringPC version)
      (word :: ret :: R) mem aw rdata σ k C) : RDrev (deployedRuntime v) g s0 := by
  obtain ⟨aw1, k1, C1, h1⟩ := fallbackStringReachAllocation v version free hstack
    hfree hptr hvalid rd
  exact allocateRoundedRevert v (by simp only [List.length_cons]; omega) hbad h1

theorem fallbackStringRevertsHeader {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {word ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (version : Bool) (free : Nat)
    (hstack : R.length + 14 ≤ 1024) (hptr : memLoad ⟨64⟩ mem = UInt256.ofNat free)
    (hbad : ¬ storageStringValid
      (codeOwnerStorageWord I σ (domainStringFallbackSlot version)))
    (rd : RD (deployedRuntime v) I g s0 (fallbackStringPC version)
      (word :: ret :: R) mem aw rdata σ k C) : RDrev (deployedRuntime v) g s0 := by
  obtain ⟨aw1, k1, C1, h1⟩ := fallbackStringReachCopy v version free (by omega) hptr rd
  exact fallbackStringCopyRevertsHeader v (by simp only [List.length_cons]; omega) hbad h1

end Benchmarks.Morpho.MetaMorphoV1_1
