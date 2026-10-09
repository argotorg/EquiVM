import Benchmarks.Morpho.MetaMorphoV1_1.MorphoSlots
import Benchmarks.Morpho.MetaMorphoV1_1.PackedHashMemory
import Benchmarks.Morpho.MetaMorphoV1_1.MemoryArrayRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_067

/-! The two nested storage-slot hashes and singleton argument array in `supplyShares`. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem positionSlotReachFirstHash {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr morpho id user : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 13 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hfit : ptr.toNat + 96 < 2 ^ 64)
    (rd : RD (deployedRuntime v) I g s0 ⟨14078⟩ (morpho :: id :: user :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨14119⟩
      (ptr :: (ptr + ⟨32⟩) :: user :: ⟨14169⟩ :: morpho :: ⟨0⟩ :: ⟨14197⟩ :: R)
      (packedPairAllocMem mem ptr id ⟨2⟩) aw' rdata σ k' C' := by
  have hfree' : memLoad (UInt256.ofNat 64) mem = ptr := hfree
  have hm : metaMorphoV1_1Blocks.metaMorphoV1_1_block_14078_memory
      (mem := mem) (x1 := id) = packedPairMem mem ptr id ⟨2⟩ := by
    unfold metaMorphoV1_1Blocks.metaMorphoV1_1_block_14078_memory
    rw [hfree']
    rfl
  obtain ⟨_, _, _, halloc⟩ := metaMorphoV1_1Blocks.metaMorphoV1_1_block_14078_packed
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [metaMorphoV1_1Blocks.metaMorphoV1_1_block_14078_stack, hfree', hm] at halloc
  obtain ⟨aw', k', C', hdone⟩ := allocateReturn v
    (by simp only [List.length_cons]; omega) (by decide) hfit
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) halloc
  exact ⟨aw', k', C', hdone⟩

def positionSlotHashMem (mem : ByteArray) (ptr id user : UInt256) : ByteArray :=
  packedPairAllocMem (packedPairAllocMem mem ptr id ⟨2⟩) (ptr + ⟨96⟩)
    (UInt256.land solcAddrMask user) (solcMappingSlot ⟨2⟩ id)

set_option maxRecDepth 2000 in
theorem positionSlotReachSecondHash {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr id user : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024)
    (hlower : 96 ≤ ptr.toNat) (hfit : ptr.toNat + 192 < 2 ^ 64)
    (rd : RD (deployedRuntime v) I g s0 ⟨14119⟩ (ptr :: (ptr + ⟨32⟩) :: user :: R)
      (packedPairAllocMem mem ptr id ⟨2⟩) aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨14161⟩
      ((ptr + ⟨96⟩) :: ((ptr + ⟨96⟩) + ⟨32⟩) :: R)
      (positionSlotHashMem mem ptr id user) aw' rdata σ k' C' := by
  have hword : ptr.toNat + 64 < UInt256.size :=
    lt_trans (by omega : ptr.toNat + 64 < 2 ^ 64) (by decide)
  have h96 : (ptr + ⟨96⟩).toNat = ptr.toNat + 96 :=
    uadd_word_ofNat_toNat ptr 96 (lt_trans (by omega : ptr.toNat + 96 < 2 ^ 64) (by decide))
  have hfree : memLoad (UInt256.ofNat 64) (packedPairAllocMem mem ptr id ⟨2⟩) =
      ptr + ⟨96⟩ := packedPairAllocMem_free mem ptr id ⟨2⟩
  have hlen := packedPairAllocMem_length mem ptr id ⟨2⟩ hlower hword
  have hhash := packedPairAllocMem_hash mem ptr id ⟨2⟩ hlower hword
  have hm : metaMorphoV1_1Blocks.metaMorphoV1_1_block_14119_memory
      (mem := packedPairAllocMem mem ptr id ⟨2⟩) (x0 := ptr) (x1 := ptr + ⟨32⟩)
      (x2 := user) = packedPairMem (packedPairAllocMem mem ptr id ⟨2⟩) (ptr + ⟨96⟩)
        (UInt256.land solcAddrMask user) (solcMappingSlot ⟨2⟩ id) := by
    unfold metaMorphoV1_1Blocks.metaMorphoV1_1_block_14119_memory
    rw [hfree, hlen, hhash]
    rfl
  obtain ⟨_, _, _, halloc⟩ := metaMorphoV1_1Blocks.metaMorphoV1_1_block_14119_packed
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [metaMorphoV1_1Blocks.metaMorphoV1_1_block_14119_stack, hfree, hm] at halloc
  obtain ⟨aw', k', C', hdone⟩ := allocateReturn v
    (by simp only [List.length_cons]; omega) (by decide)
    (by change (ptr + ⟨96⟩).toNat + 96 < 2 ^ 64; rw [h96]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) halloc
  exact ⟨aw', k', C', hdone⟩

set_option maxRecDepth 2000 in
theorem positionSlotReachArray {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr morpho id user : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 13 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlower : 96 ≤ ptr.toNat)
    (hfit : ptr.toNat + 192 < 2 ^ 64)
    (rd : RD (deployedRuntime v) I g s0 ⟨14078⟩ (morpho :: id :: user :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨16791⟩
      (positionSupplySharesSlot id (AccountAddress.ofNat user.toNat) ::
        ⟨14169⟩ :: morpho :: ⟨0⟩ :: ⟨14197⟩ :: R)
      (positionSlotHashMem mem ptr id user) aw' rdata σ k' C' := by
  obtain ⟨_, _, _, hfirst⟩ := positionSlotReachFirstHash v hstack hfree (by omega) rd
  obtain ⟨_, _, _, hsecond⟩ := positionSlotReachSecondHash v
    (by simp only [List.length_cons]; omega) hlower hfit hfirst
  have h96 : (ptr + ⟨96⟩).toNat = ptr.toNat + 96 :=
    uadd_word_ofNat_toNat ptr 96 (lt_trans (by omega : ptr.toNat + 96 < 2 ^ 64) (by decide))
  have hlo : 96 ≤ (ptr + ⟨96⟩).toNat := by rw [h96]; omega
  have hword : (ptr + ⟨96⟩).toNat + 64 < UInt256.size := by
    rw [h96]
    exact lt_trans (by omega : ptr.toNat + 96 + 64 < 2 ^ 64) (by decide)
  have hlen := packedPairAllocMem_length (packedPairAllocMem mem ptr id ⟨2⟩)
    (ptr + ⟨96⟩) (UInt256.land solcAddrMask user) (solcMappingSlot ⟨2⟩ id) hlo hword
  have hhash := packedPairAllocMem_hash (packedPairAllocMem mem ptr id ⟨2⟩)
    (ptr + ⟨96⟩) (UInt256.land solcAddrMask user) (solcMappingSlot ⟨2⟩ id) hlo hword
  obtain ⟨aw', k', C', hdone⟩ := metaMorphoV1_1Blocks.metaMorphoV1_1_block_14161_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) hsecond
  simp only [metaMorphoV1_1Blocks.metaMorphoV1_1_block_14161_stack, positionSlotHashMem,
    hlen, hhash] at hdone
  rw [positionSupplySharesSlot_of_word]
  exact ⟨aw', k', C', hdone⟩

def positionSlotArrayMem (mem calldata : ByteArray) (ptr id user : UInt256) : ByteArray :=
  morphoArrayMem (positionSlotHashMem mem ptr id user) calldata (ptr + ⟨192⟩)
    (positionSupplySharesSlot id (AccountAddress.ofNat user.toNat))

set_option maxRecDepth 2000 in
theorem supplySharesReachEncoding {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr morpho id user : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 13 ≤ 1024)
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlower : 96 ≤ ptr.toNat)
    (hfit : ptr.toNat + 256 < 2 ^ 64)
    (rd : RD (deployedRuntime v) I g s0 ⟨14078⟩ (morpho :: id :: user :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨14169⟩
      ((ptr + ⟨192⟩) :: morpho :: ⟨0⟩ :: ⟨14197⟩ :: R)
      (positionSlotArrayMem mem I.calldata ptr id user) aw' rdata σ k' C' := by
  obtain ⟨_, _, _, harray⟩ := positionSlotReachArray v hstack hfree hlower (by omega) rd
  have h192 : (ptr + ⟨192⟩).toNat = ptr.toNat + 192 :=
    uadd_word_ofNat_toNat ptr 192
      (lt_trans (by omega : ptr.toNat + 192 < 2 ^ 64) (by decide))
  have hcursor : memLoad ⟨64⟩ (positionSlotHashMem mem ptr id user) = ptr + ⟨192⟩ := by
    rw [positionSlotHashMem, packedPairAllocMem_free, u256_add_assoc]
    rfl
  obtain ⟨aw', k', C', hdone⟩ := morphoArrayReturn v
    (by simp only [List.length_cons]; omega) hcalldata hcursor
    (by rw [h192]; omega) (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) harray
  exact ⟨aw', k', C', hdone⟩

end Benchmarks.Morpho.MetaMorphoV1_1
