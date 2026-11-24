import Benchmarks.EAS.EAS.CopySignatureArrayLoop
import Benchmarks.EAS.EAS.ArrayAllocationHead

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easCopySignatureArrayHead {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {header heap a b c d e : UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+16 ≤ 1024)
    (hfree : memLoad (UInt256.ofNat 64) mem = heap)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨1439⟩ (a::b::c::d::e::header::R) mem aw rdata σ k C) :
    let len := calldataWord ee.calldata header.toNat
    if signatureArrayHeaderValid ee.calldata header ∧
        allocateNext heap.toNat (32+32*len.toNat) ≤ 2^64-1 ∧
        heap.toNat ≤ allocateNext heap.toNat (32+32*len.toNat) then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨1492⟩
        ((heap+UInt256.ofNat 32)::(header+UInt256.ofNat 32)::
          ((header+UInt256.ofNat 32)+UInt256.mul len (UInt256.ofNat 96))::a::b::c::d::e::heap::R)
        (arrayAllocationHeaderMemory mem heap len.toNat) aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  dsimp only
  let len := calldataWord ee.calldata header.toNat
  obtain ⟨a1,j1,D1,r1⟩ := easBlocks.eas_block_1439_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  change RD fork (deployedRuntime v) ee g s0 ⟨5069⟩ (len::⟨1450⟩::header::a::b::c::d::e::len::R) mem a1 rdata σ j1 D1 at r1
  have hsize := easArrayAllocationSize v (by simp only [List.length_cons]; omega)
    (by rw [easPatchedValidJumps v]; jump_dest) r1
  by_cases hl : len.toNat ≤ 2^64-1
  · rw [if_pos hl] at hsize
    obtain ⟨a2,j2,D2,r2⟩ := hsize
    obtain ⟨a3,j3,D3,r3⟩ := easBlocks.eas_block_1450_packed (immWords := wordsOf (immStore v))
      (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r2
    simp only [easBlocks.eas_block_1450_stack,hfree] at r3
    have hn : (UInt256.ofNat (32+32*len.toNat)).toNat = 32+32*len.toNat := ulit_toNat' _ (by change _ < 2^256; omega)
    by_cases hg : allocateNext heap.toNat (32+32*len.toNat) ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat (32+32*len.toNat)
    · obtain ⟨a4,j4,D4,r4⟩ := easAllocate_ok v (by simp only [List.length_cons]; omega)
        (by simpa only [hn] using hg) (by rw [easPatchedValidJumps v]; jump_dest) r3
      rw [hn] at r4
      have heq : (header+UInt256.mul len (UInt256.ofNat 96))+UInt256.ofNat 32 =
          (header+UInt256.ofNat 32)+UInt256.mul len (UInt256.ofNat 96) := by
        apply u256_inj
        change ((header.val+(UInt256.mul len (UInt256.ofNat 96)).val)+(UInt256.ofNat 32).val).val =
          ((header.val+(UInt256.ofNat 32).val)+(UInt256.mul len (UInt256.ofNat 96)).val).val
        rw [add_right_comm]
      by_cases he : signatureArrayHeaderValid ee.calldata header
      · rw [if_pos ⟨he,hg⟩]
        obtain ⟨a5,j5,D5,r5⟩ := easBlocks.eas_block_1464_fallthrough_packed (immWords := wordsOf (immStore v))
          (by omega) (by rw [heq]; exact he.2) r4
        obtain ⟨a6,j6,D6,r6⟩ := easBlocks.eas_block_1488_packed (immWords := wordsOf (immStore v))
          (by simp only [easBlocks.eas_block_1464_fallthrough_stack,List.length_cons]; omega) r5
        refine ⟨a6,j6,D6,?_⟩
        simpa only [easBlocks.eas_block_1488_stack,easBlocks.eas_block_1464_fallthrough_stack,
          easBlocks.eas_block_1464_fallthrough_memory,arrayAllocationHeaderMemory,Reasoning.Theory.writeWord,
          u256_ofNat_toNat,heq,u256_add_comm (UInt256.ofNat 32) header] using r6
      · rw [if_neg (fun h => he h.1)]
        obtain ⟨a5,j5,D5,r5⟩ := easBlocks.eas_block_1464_taken_packed (immWords := wordsOf (immStore v))
          (by omega) (by rw [heq]; intro h; exact he ⟨hl,h⟩)
          (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r4
        exact easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
          (by simp only [easBlocks.eas_block_1464_taken_stack,List.length_cons]; omega) r5
    · rw [if_neg (fun h => hg h.2)]
      exact easAllocate_revert v (by simp only [List.length_cons]; omega) (by simpa only [hn] using hg) r3
  · rw [if_neg hl] at hsize
    rw [if_neg (fun h => hl h.1.1)]
    exact hsize

end Benchmarks.EAS.EAS
