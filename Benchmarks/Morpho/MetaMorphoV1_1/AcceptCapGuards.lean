import Benchmarks.Morpho.MetaMorphoV1_1.AcceptCapSource
import Benchmarks.Morpho.MetaMorphoV1_1.MappingScratchMemory
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_024
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_036
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_037

/-! Pending-cap guards and the jump into the internal cap setter. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

def acceptCapGuardMemory (mem : ByteArray) (id : UInt256) : ByteArray :=
  twoWordHashMem id ⟨16⟩ (twoWordHashMem id ⟨16⟩ mem)

theorem acceptCapGuardMemory_prefix (mem : ByteArray) (id : UInt256) (limit : Nat) :
    MemoryPrefix mem (acceptCapGuardMemory mem id) limit :=
  (twoWordHashMem_prefix mem id ⟨16⟩ limit).trans
    (twoWordHashMem_prefix (twoWordHashMem id ⟨16⟩ mem) id ⟨16⟩ limit)

theorem acceptCapGuardMemory_free {mem : ByteArray} (id : UInt256) (hmem : 96 ≤ mem.size) :
    memLoad ⟨64⟩ (acceptCapGuardMemory mem id) = memLoad ⟨64⟩ mem := by
  rw [acceptCapGuardMemory, twoWordHashMem_free _ _ (by
    rw [twoWordHashMem_size_of_ge_64' _ _ (by omega)]; exact hmem),
    twoWordHashMem_free _ _ hmem]

theorem acceptCapGuardsReach {evm : State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {k C : Nat} {R : List UInt256} {params id : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (hlo : 96 ≤ params.toNat) (hmem : params.toNat + 160 ≤ mem.size)
    (hid : keccakWord params ⟨160⟩ mem = id)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨7285⟩ (params :: R)
      mem aw rdata evm.accountMap k C) :
    (¬ acceptCapAllowed evm id ∧ RDrev (deployedRuntime v) g s0) ∨
    (acceptCapAllowed evm id ∧ ∃ aw' k' C',
      RD (deployedRuntime v) evm.executionEnv g s0 ⟨13448⟩
        ([params, id, acceptCapValue evm id, ⟨1867⟩] ++ R)
        (acceptCapGuardMemory mem id) aw' rdata evm.accountMap k' C') := by
  have hid' : keccakWord params (UInt256.ofNat 160) mem = id := hid
  have hh (m : ByteArray) :
      keccakWord ⟨0⟩ (UInt256.ofNat 64)
        ((UInt256.ofNat 16).toByteArray.write 0 (id.toByteArray.write 0 m
          (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) =
          solcMappingSlot ⟨16⟩ id := twoWordHashMem_solcMappingSlot_any _ _ _
  by_cases hn : marketRemovalPendingAt evm id ≠ ⟨0⟩
  case neg =>
    obtain ⟨_, _, _, hbad⟩ := metaMorphoV1_1_block_7285_taken_packed
      (immWords := wordsOf (immStore v)) (by omega)
      (by
        rw [hid', hh]
        change UInt256.isZero (marketRemovalPendingAt evm id) ≠ ⟨0⟩
        rw [not_ne_iff.mp hn]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    exact .inl ⟨fun h ↦ hn h.1,
      metaMorphoV1_1_block_4249 (immWords := wordsOf (immStore v))
        (by simp only [metaMorphoV1_1_block_7285_taken_stack, List.length_cons]; omega) hbad⟩
  obtain ⟨aw1, k1, C1, r1⟩ := metaMorphoV1_1_block_7285_fallthrough_packed
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [hid', hh]; exact isZero_eq_zero_of_ne hn) rd
  simp only [metaMorphoV1_1_block_7285_fallthrough_stack,
    metaMorphoV1_1_block_7285_fallthrough_memory, hid', hh] at r1
  by_cases ht : (marketRemovalPendingAt evm id).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat
  case neg =>
    have hbad := metaMorphoV1_1_block_7311_taken (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by
        change UInt256.lt (UInt256.ofNat evm.executionEnv.header.timestamp)
          (marketRemovalPendingAt evm id) ≠ ⟨0⟩
        rw [ult_one (by omega)]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r1
    exact .inl ⟨fun h ↦ ht h.2,
      metaMorphoV1_1_block_4234 (immWords := wordsOf (immStore v))
        (by simp only [metaMorphoV1_1_block_7311_taken_stack, List.length_cons]; omega) hbad⟩
  have r2 := metaMorphoV1_1_block_7311_fallthrough (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (ult_zero ht) r1
  change RD (deployedRuntime v) evm.executionEnv g s0 ⟨7317⟩ (params :: R)
    (twoWordHashMem id ⟨16⟩ mem) aw1 rdata evm.accountMap (k1 + 4) (C1 + 18) at r2
  have hp := twoWordHashMem_prefix mem id ⟨16⟩ (params.toNat + 160)
  have hid2 : keccakWord params (UInt256.ofNat 160) (twoWordHashMem id ⟨16⟩ mem) = id := by
    unfold keccakWord
    change UInt256.ofNat (fromByteArrayBigEndian
      (KEC ((twoWordHashMem id ⟨16⟩ mem).readWithPadding params.toNat 160))) = _
    rw [memoryPrefix_read_words hp 5 params.toNat hlo (by omega) hmem]
    exact hid
  obtain ⟨aw3, k3, C3, r3⟩ := metaMorphoV1_1_block_7317_packed
    (immWords := wordsOf (immStore v)) hstack
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r2
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 184))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 184 - 1) := by decide +kernel
  refine .inr ⟨⟨hn, ht⟩, aw3, k3, C3, ?_⟩
  simp only [metaMorphoV1_1_block_7317_stack, metaMorphoV1_1_block_7317_memory,
    hid2, hh, hmask] at r3
  exact r3

end Benchmarks.Morpho.MetaMorphoV1_1
