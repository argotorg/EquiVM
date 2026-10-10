import Benchmarks.Morpho.MetaMorphoV1_1.FallbackStringRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.ShortStringRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.Eip712StringMemory

/-! A common bytecode interface for the EIP-712 name and version getters. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000
set_option autoImplicit false

def domainStringPC (version : Bool) : UInt256 := if version then ⟨18512⟩ else ⟨18416⟩

theorem domainStringReachFallback {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {word : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (version : Bool) (hstack : R.length + 3 ≤ 1024)
    (heq : word = ⟨255⟩)
    (rd : RD (deployedRuntime v) I g s0 (domainStringPC version)
      (word :: R) mem aw rdata σ k C) :
    RD (deployedRuntime v) I g s0 (fallbackStringPC version)
      (word :: R) mem aw rdata σ (k + 6) (C + 23) := by
  have hc : UInt256.eq word (UInt256.ofNat 255) ≠ UInt256.ofNat 0 := by
    subst word
    decide
  cases version
  · exact metaMorphoV1_1_block_18416_taken (immWords := wordsOf (immStore v)) hstack hc
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  · exact metaMorphoV1_1_block_18512_taken (immWords := wordsOf (immStore v)) hstack hc
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd

theorem domainStringReachShort {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {word : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (version : Bool) (hstack : R.length + 3 ≤ 1024)
    (hne : word ≠ ⟨255⟩)
    (rd : RD (deployedRuntime v) I g s0 (domainStringPC version)
      (word :: R) mem aw rdata σ k C) :
    RD (deployedRuntime v) I g s0 (shortStringDecodePC version)
      (word :: R) mem aw rdata σ (k + 6) (C + 23) := by
  have hc : UInt256.eq word (UInt256.ofNat 255) = UInt256.ofNat 0 := u256_eq_of_ne hne
  cases version
  · exact metaMorphoV1_1_block_18416_fallthrough (immWords := wordsOf (immStore v))
      hstack hc rd
  · exact metaMorphoV1_1_block_18512_fallthrough (immWords := wordsOf (immStore v))
      hstack hc rd

theorem domainStringFallbackAllocationFits (evm : State) (v : MetaMorphoV1_1Immutables)
    (version : Bool) (free : Nat) (hfree : free < 2 ^ 64)
    (heq : domainStringImmutable v version = ⟨255⟩) :
    allocationFits (UInt256.ofNat free) (stringCopySize
      (storageStringLength (storageStringHeader evm (domainStringFallbackSlot version)))) ↔
      domainStringEnd evm v version free < 2 ^ 64 := by
  rw [stringAllocationFitsAt free _ (storageStringLength_lt _)]
  simpa only [domainStringSize, domainStringBytes, if_pos heq, storageStringBytes_size] using
    domainStringAllocationFits evm v version free hfree

theorem domainStringReturn {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {k C : Nat} {ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (version : Bool) (free : Nat)
    (hstack : R.length + 15 ≤ 1024) (hlo : 96 ≤ free) (hfree : free < 2 ^ 64)
    (hsize : evm.executionEnv.calldata.size < UInt256.size)
    (hptr : memLoad ⟨64⟩ mem = UInt256.ofNat free)
    (hvalid : domainStringValid v version evm)
    (hfit : domainStringEnd evm v version free < 2 ^ 64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 (domainStringPC version)
      (domainStringImmutable v version :: ret :: R) mem aw rdata evm.accountMap k C) :
    ∃ mem' aw' k' C',
      RD (deployedRuntime v) evm.executionEnv g s0 ret (UInt256.ofNat free :: R)
        mem' aw' rdata evm.accountMap k' C' ∧
      StringBuffer mem' free (domainStringBytes v version evm) ∧
      MemoryPrefix mem mem' free ∧
      memLoad ⟨64⟩ mem' = UInt256.ofNat (domainStringEnd evm v version free) ∧
      domainStringEnd evm v version free ≤ mem'.size := by
  have hf : free < UInt256.size := lt_trans hfree (by decide)
  by_cases heq : domainStringImmutable v version = ⟨255⟩
  · have hv : storageStringValid
        (storageStringHeader evm (domainStringFallbackSlot version)) := by
      simpa only [domainStringValid, if_pos heq] using hvalid
    have h1 := domainStringReachFallback v version
      (by simp only [List.length_cons]; omega) heq rd
    obtain ⟨aw2, k2, C2, h2⟩ := fallbackStringReturn v version free hstack hfree hptr hv
      ((domainStringFallbackAllocationFits evm v version free hfree heq).mpr hfit) hret h1
    refine ⟨_, aw2, k2, C2, h2, ?_, ?_, ?_, ?_⟩
    · simpa only [domainStringBytes, if_pos heq] using
        (fallbackStringMemory_buffer evm mem (domainStringFallbackSlot version)
          free hlo hf hv).writeFree _ hlo hf
    · exact (fallbackStringMemory_prefix _ _ _ _ _ _).trans
        (memoryPrefix_sparse_writeWord _ 64 free _ (.inr (by decide)))
    · have hl : memLoad ⟨64⟩ (writeWord
          (fallbackStringMemory evm.executionEnv evm.accountMap mem
            (domainStringFallbackSlot version)
            (storageStringHeader evm (domainStringFallbackSlot version)) free) 64
          (stringCopyEndAt free (storageStringLength
            (storageStringHeader evm (domainStringFallbackSlot version))))) =
          stringCopyEndAt free (storageStringLength
            (storageStringHeader evm (domainStringFallbackSlot version))) :=
        memLoad_write_same _ _ _ _ rfl
      refine hl.trans ?_
      simp only [domainStringEnd, domainStringBytes, if_pos heq, storageStringBytes_size]
      rfl
    · have hm := fallbackStringMemory_size evm.executionEnv evm.accountMap mem
        (domainStringFallbackSlot version)
        (storageStringHeader evm (domainStringFallbackSlot version)) free hv
      simpa only [domainStringEnd, domainStringBytes, if_pos heq, storageStringBytes_size,
        paddedSize, stringWordCount, writeWord_sparse_size] using
        le_trans hm (Nat.le_max_left _ 96)
  · have hv : shortStringValid (domainStringImmutable v version) := by
      simpa only [domainStringValid, if_neg heq] using hvalid
    have h1 := domainStringReachShort v version
      (by simp only [List.length_cons]; omega) heq rd
    obtain ⟨aw2, k2, C2, h2⟩ := shortStringReachAllocation v version
      (by simp only [List.length_cons]; omega) hv h1
    rw [hptr] at h2
    have hfit' : free + 64 < 2 ^ 64 := by
      simpa only [domainStringEnd, if_neg heq] using hfit
    obtain ⟨aw3, k3, C3, h3⟩ := shortStringAllocatedReturn v free (by omega) hsize hfit' hret h2
    refine ⟨_, aw3, k3, C3, h3, ?_, shortStringMemory_prefix _ _ _ _, ?_, ?_⟩
    · simpa only [domainStringBytes, if_neg heq] using
        shortStringMemory_buffer mem evm.executionEnv.calldata free _ hf hv
    · simpa only [domainStringEnd, if_neg heq] using
        shortStringMemory_free mem evm.executionEnv.calldata free _ hlo
    · simp only [domainStringEnd, if_neg heq, shortStringMemory_size]
      exact Nat.le_max_right _ _

theorem domainStringRevertsInvalid {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {k C : Nat} {ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (version : Bool) (free : Nat)
    (hstack : R.length + 14 ≤ 1024) (hptr : memLoad ⟨64⟩ mem = UInt256.ofNat free)
    (hbad : ¬ domainStringValid v version evm)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 (domainStringPC version)
      (domainStringImmutable v version :: ret :: R) mem aw rdata evm.accountMap k C) :
    RDrev (deployedRuntime v) g s0 := by
  by_cases heq : domainStringImmutable v version = ⟨255⟩
  · have h1 := domainStringReachFallback v version
      (by simp only [List.length_cons]; omega) heq rd
    exact fallbackStringRevertsHeader v version free hstack hptr
      (by simpa only [domainStringValid, if_pos heq] using hbad) h1
  · have h1 := domainStringReachShort v version
      (by simp only [List.length_cons]; omega) heq rd
    exact shortStringDecodeReverts v version (by simp only [List.length_cons]; omega)
      (by simpa only [domainStringValid, if_neg heq] using hbad) h1

theorem domainStringRevertsAllocation {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {k C : Nat} {ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (version : Bool) (free : Nat)
    (hstack : R.length + 15 ≤ 1024) (hfree : free < 2 ^ 64)
    (hptr : memLoad ⟨64⟩ mem = UInt256.ofNat free)
    (hvalid : domainStringValid v version evm)
    (hbad : ¬ domainStringEnd evm v version free < 2 ^ 64)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 (domainStringPC version)
      (domainStringImmutable v version :: ret :: R) mem aw rdata evm.accountMap k C) :
    RDrev (deployedRuntime v) g s0 := by
  by_cases heq : domainStringImmutable v version = ⟨255⟩
  · have h1 := domainStringReachFallback v version
      (by simp only [List.length_cons]; omega) heq rd
    exact fallbackStringRevertsAllocation v version free hstack hfree hptr
      (by simpa only [domainStringValid, if_pos heq] using hvalid)
      (fun hfit ↦ hbad
        ((domainStringFallbackAllocationFits evm v version free hfree heq).mp hfit)) h1
  · have h1 := domainStringReachShort v version
      (by simp only [List.length_cons]; omega) heq rd
    obtain ⟨aw2, k2, C2, h2⟩ := shortStringReachAllocation v version
      (by simp only [List.length_cons]; omega)
      (by simpa only [domainStringValid, if_neg heq] using hvalid) h1
    rw [hptr] at h2
    apply allocateRoundedRevert v (by simp only [List.length_cons]; omega) _ h2
    intro hfit
    apply hbad
    apply (domainStringAllocationFits evm v version free hfree).mp
    simpa only [domainStringSize, if_neg heq] using hfit

end Benchmarks.Morpho.MetaMorphoV1_1
