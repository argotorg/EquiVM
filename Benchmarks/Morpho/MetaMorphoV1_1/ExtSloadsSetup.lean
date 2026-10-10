import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsEncode
import Benchmarks.Morpho.MetaMorphoV1_1.MorphoSlotRoutines

/-! Construction of the exact input stack and calldata at the `extSloads` STATICCALL. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

theorem singletonEncodeMem_call (mem : ByteArray) (ptr slot : UInt256)
    (hfit : ptr.toNat + 100 < UInt256.size) :
    singletonEncodeMem (writeWord mem ptr.toNat extSloadsSelectorWord) (ptr + ⟨4⟩) slot =
      extSloadsCallMem mem ptr.toNat slot := by
  have h4 : (ptr + ⟨4⟩).toNat = ptr.toNat + 4 := uadd_word_ofNat_toNat ptr 4 (by omega)
  have h36 : ((ptr + ⟨4⟩) + ⟨32⟩).toNat = ptr.toNat + 36 := by
    rw [show ((ptr + ⟨4⟩) + ⟨32⟩).toNat = (ptr + ⟨4⟩).toNat + 32 from
      uadd_word_ofNat_toNat (ptr + ⟨4⟩) 32 (by rw [h4]; omega), h4]
  have h68 : ((ptr + ⟨4⟩) + ⟨64⟩).toNat = ptr.toNat + 68 := by
    rw [show ((ptr + ⟨4⟩) + ⟨64⟩).toNat = (ptr + ⟨4⟩).toNat + 64 from
      uadd_word_ofNat_toNat (ptr + ⟨4⟩) 64 (by rw [h4]; omega), h4]
  simp only [singletonEncodeMem, h4, h36, h68, extSloadsCallMem,
    writeCascade_cons, writeCascade_nil]

set_option maxRecDepth 2000 in
theorem extSloadsEncodeReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr array slot ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024)
    (hin : array.toNat + 64 ≤ mem.size) (hbelow : array.toNat + 64 ≤ ptr.toNat)
    (hfit : ptr.toNat + 100 < UInt256.size)
    (hlen : memLoad array mem = ⟨1⟩) (hslot : memLoad (array + ⟨32⟩) mem = slot)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨13342⟩ ((ptr + ⟨4⟩) :: array :: ret :: R)
      (writeWord mem ptr.toNat extSloadsSelectorWord) aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret ((ptr + ⟨100⟩) :: R)
      (extSloadsCallMem mem ptr.toNat slot) aw' rdata σ k' C' := by
  have h4 : (ptr + ⟨4⟩).toNat = ptr.toNat + 4 := uadd_word_ofNat_toNat ptr 4 (by omega)
  have harray32 : (array + ⟨32⟩).toNat = array.toNat + 32 :=
    uadd_word_ofNat_toNat array 32 (by omega)
  obtain ⟨aw1, k1, C1, r1⟩ := singletonArrayEncodeReturn v hstack
    (by rw [writeWord_sparse_size]; omega) (by rw [h4]; omega) (by rw [h4]; omega)
    (by rw [memLoad_write_above _ _ _ _ (by omega) (by omega), hlen])
    (by rw [memLoad_write_above _ _ _ _ (by rw [harray32]; omega)
      (by rw [harray32]; omega), hslot]) hret rd
  have hcursor : (ptr + ⟨4⟩) + ⟨96⟩ = ptr + ⟨100⟩ := by rw [u256_add_assoc]; rfl
  rw [hcursor, singletonEncodeMem_call mem ptr slot hfit] at r1
  exact ⟨aw1, k1, C1, r1⟩

set_option maxRecDepth 2000 in
theorem extSloadsReachStaticcall {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr array slot morpho : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 14 ≤ 1024)
    (hin : array.toNat + 64 ≤ mem.size) (hbelow : array.toNat + 64 ≤ ptr.toNat)
    (hfit : ptr.toNat + 100 < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr)
    (hlen : memLoad array mem = ⟨1⟩) (hslot : memLoad (array + ⟨32⟩) mem = slot)
    (rd : RD (deployedRuntime v) I g s0 ⟨14169⟩
      (array :: morpho :: ⟨0⟩ :: ⟨14197⟩ :: R) mem aw rdata σ k C) :
    ∃ callGas aw' k' C', RD (deployedRuntime v) I g s0 ⟨14210⟩
      (callGas :: UInt256.land solcAddrMask morpho :: ptr :: ⟨100⟩ :: ptr :: ⟨0⟩ :: ptr :: R)
      (extSloadsCallMem mem ptr.toNat slot) aw' rdata σ k' C' := by
  have hfree' : memLoad (UInt256.ofNat 64) mem = ptr := hfree
  have hm : metaMorphoV1_1Blocks.metaMorphoV1_1_block_14169_memory (mem := mem) =
      writeWord mem ptr.toNat extSloadsSelectorWord := by
    unfold metaMorphoV1_1Blocks.metaMorphoV1_1_block_14169_memory
    rw [hfree']
    rfl
  obtain ⟨_, _, _, hencode⟩ := metaMorphoV1_1Blocks.metaMorphoV1_1_block_14169_packed
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [metaMorphoV1_1Blocks.metaMorphoV1_1_block_14169_stack, hfree', hm] at hencode
  change RD _ _ _ _ _
    ((ptr + ⟨4⟩) :: array :: ⟨14197⟩ :: ptr :: ptr :: morpho :: ptr :: ⟨0⟩ :: ptr :: R)
    _ _ _ _ _ _ at hencode
  obtain ⟨_, _, _, hcall⟩ := extSloadsEncodeReturn v
    (by simp only [List.length_cons]; omega) hin hbelow hfit hlen hslot
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) hencode
  have hready := metaMorphoV1_1Blocks.metaMorphoV1_1_block_14197
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hcall
  change RD _ _ _ _ _
    (_ :: UInt256.land solcAddrMask morpho :: ptr :: UInt256.sub (ptr + ⟨100⟩) ptr ::
      ptr :: ⟨0⟩ :: ptr :: R) _ _ _ _ _ _ at hready
  rw [word_add_sub_left] at hready
  exact ⟨_, _, _, _, hready⟩

end Benchmarks.Morpho.MetaMorphoV1_1
