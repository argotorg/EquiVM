import Benchmarks.CompoundIII.Comet.WordStructMemory
import Benchmarks.CompoundIII.Comet.AssetMemory
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_016

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: mapping-key hashing preserves every complete word above scratch space.
theorem twoWordHashMem_load_ge {mem : ByteArray} {ptr : UInt256} (key slot : UInt256)
    (hlo : 64 ≤ ptr.toNat) (hsize : ptr.toNat + 32 ≤ mem.size) :
    memLoad ptr (twoWordHashMem key slot mem) = memLoad ptr mem := by
  change memLoad ptr (writeWord (writeWord mem 0 key) 32 slot) = memLoad ptr mem
  have h0 := writeWord_sparse_size mem 0 key
  have h1 := writeWord_sparse_size (writeWord mem 0 key) 32 slot
  have hread : (writeWord (writeWord mem 0 key) 32 slot).readWithPadding ptr.toNat 32 =
      mem.readWithPadding ptr.toNat 32 := by
    rw [writeWord_sparse_read_preserved _ _ _ _ (Or.inr ⟨by omega, by omega⟩),
      writeWord_sparse_read_preserved _ _ _ _ (Or.inr ⟨by omega, by omega⟩)]
  unfold memLoad
  rw [if_neg (by omega), if_neg (by omega), hread]

theorem AssetMemory.scratch {mem : ByteArray} {ptr free : UInt256} {out : ByteArray}
    (hm : AssetMemory mem ptr free out) (key slot : UInt256) :
    AssetMemory (twoWordHashMem key slot mem) ptr free out := by
  have hmem : 96 ≤ mem.size := by have ha := hm.lower; have hb := hm.present; omega
  have hw : WordStructMemory mem ptr 8 (fun i ↦ calldataWord out (32 * i)) :=
    ⟨by have ha := hm.separate; have hb := hm.bounded; omega, hm.present, hm.words⟩
  have hw' := hw.scratch hm.lower key slot
  refine ⟨hm.lower, hw'.size, hm.separate, hm.bounded, ?_, hw'.word⟩
  rw [twoWordHashMem_load_ge (ptr := ⟨64⟩) key slot (by decide) hmem, hm.freeWord]

theorem AssetMemory.scratchOrSame {mem mem' : ByteArray} {ptr free : UInt256} {out : ByteArray}
    (hm : AssetMemory mem ptr free out) (key slot : UInt256)
    (he : mem' = mem ∨ mem' = twoWordHashMem key slot mem) :
    AssetMemory mem' ptr free out ∧ mem'.size = mem.size := by
  rcases he with rfl | rfl
  · exact ⟨hm, rfl⟩
  · exact ⟨hm.scratch key slot, twoWordHashMem_size_of_ge_64 _ _
      (by have hl := hm.lower; have hp := hm.present; omega)⟩

theorem cometMappingHash {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {slot key ret : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024) (hkey : key.toNat < EVM.addressModulus)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨2428⟩ (slot :: key :: ret :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret (solcMappingSlot slot key :: R)
      (twoWordHashMem key slot mem) aw' rdata σ k' C' := by
  have r1 := cometWithExtendedAssetList_block_2428 (immWords := wordsOf (immStore v))
    hstack hret h
  dsimp only [cometWithExtendedAssetList_block_2428_stack,
    cometWithExtendedAssetList_block_2428_memory] at r1
  have hmask : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) key = key := solcAddrMask_clean_left hkey
  rw [hmask] at r1
  change RD _ _ _ _ _
    (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (twoWordHashMem key slot mem) :: R)
    (twoWordHashMem key slot mem) _ _ _ _ _ at r1
  have hhash : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem key slot mem) = solcMappingSlot slot key :=
    twoWordHashMem_solcMappingSlot_any slot key mem
  rw [hhash] at r1
  exact ⟨_, _, _, r1⟩

end Benchmarks.CompoundIII.Comet
