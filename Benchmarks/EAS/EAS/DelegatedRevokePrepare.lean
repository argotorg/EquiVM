import Benchmarks.EAS.EAS.DelegatedRevokePrepareMemory
import Benchmarks.EAS.EAS.DelegatedRevokeDecode
import Benchmarks.EAS.EAS.RevokeCalldataCopy
import Benchmarks.EAS.EAS.RuntimeBlocks_005
import Benchmarks.EAS.EAS.RuntimeBlocks_006

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easDelegatedRevokeAllocated {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+14 ≤ 1024)
    (hsize : ee.calldata.size < UInt256.size) (h228 : 228 ≤ ee.calldata.size) (hbig : ee.calldata.size < 2^255+4)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨965⟩ R attestPublicInitialMemory aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨1050⟩
      (UInt256.ofNat 416::calldataWord ee.calldata 4::UInt256.ofNat 224::R)
      (delegatedRevokeAllocatedMemory ee.calldata) aw' rdata σ k' C' := by
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_965_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [easBlocks.eas_block_965_stack,show memLoad (UInt256.ofNat 64) attestPublicInitialMemory = UInt256.ofNat 224 by native_decide] at r1
  change RD fork (deployedRuntime v) ee g s0 ⟨4695⟩ (UInt256.ofNat 224::UInt256.ofNat 976::UInt256.ofNat 224::R)
    attestPublicInitialMemory a1 rdata σ k1 C1 at r1
  obtain ⟨a2,k2,C2,r2⟩ := easFixedAllocate_ok v .bytes128 (by simp only [List.length_cons]; omega)
    (by native_decide) (by rw [easPatchedValidJumps v]; jump_dest) r1
  simp only [FixedAllocationSite.size,show (UInt256.ofNat 224).toNat = 224 from rfl,show allocateNext 224 128 = 352 by native_decide] at r2
  obtain ⟨a3,k3,C3,r3⟩ := easBlocks.eas_block_976_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r2
  change RD fork (deployedRuntime v) ee g s0 ⟨5854⟩
    (UInt256.ofNat ee.calldata.size::UInt256.ofNat 991::calldataWord ee.calldata 4::UInt256.ofNat 224::R)
    (delegatedRevokeSchemaMemory ee.calldata) a3 rdata σ k3 C3 at r3
  have hc := easRevokeCalldataCopy (heap := UInt256.ofNat 352) v (by simp only [List.length_cons]; omega)
    hsize (by omega) hbig (by decide) (delegatedRevokeSchemaMemory_free ee.calldata)
    (by rw [easPatchedValidJumps v]; jump_dest) r3
  rw [if_pos (by decide)] at hc
  obtain ⟨a4,k4,C4,r4⟩ := hc
  change RD fork (deployedRuntime v) ee g s0 ⟨991⟩
    (UInt256.ofNat 352::calldataWord ee.calldata 4::UInt256.ofNat 224::R)
    (delegatedRevokeDataMemory ee.calldata) a4 rdata σ k4 C4 at r4
  have hsub : UInt256.ofNat ee.calldata.size+UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639836 =
      UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨100⟩ := by
    change _ = UInt256.ofNat ee.calldata.size-⟨100⟩
    rw [word_sub_eq_add_neg (UInt256.ofNat ee.calldata.size) ⟨100⟩]; rfl
  obtain ⟨a5,k5,C5,r5⟩ := easBlocks.eas_block_991_fallthrough_packed (immWords := wordsOf (immStore v))
    (by omega) (by
      rw [hsub]
      exact solcDecodeLenCheckOk (head := ⟨100⟩) (need := ⟨96⟩) (by change 196 ≤ _; omega)
        (by change ee.calldata.size < 2^255+100; omega) hsize (by decide)) r4
  obtain ⟨a6,k6,C6,r6⟩ := easBlocks.eas_block_1039_packed (immWords := wordsOf (immStore v))
    (by simp only [easBlocks.eas_block_991_fallthrough_stack,List.length_cons]; omega)
    (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r5
  have hf : memLoad (UInt256.ofNat 64) (Reasoning.Theory.writeWord (delegatedRevokeDataMemory ee.calldata) 256 (UInt256.ofNat 352)) = UInt256.ofNat 416 := by
    rw [memLoad_write_below _ _ _ _ (by decide) (by
      unfold delegatedRevokeDataMemory
      rw [writeWord_sparse_size]
      change 96 ≤ _; omega)]
    exact delegatedRevokeDataMemory_free ee.calldata
  change RD fork (deployedRuntime v) ee g s0 ⟨4826⟩
    (memLoad (UInt256.ofNat 64) (Reasoning.Theory.writeWord (delegatedRevokeDataMemory ee.calldata) 256 (UInt256.ofNat 352))::
      UInt256.ofNat 1050::memLoad (UInt256.ofNat 64) (Reasoning.Theory.writeWord (delegatedRevokeDataMemory ee.calldata) 256 (UInt256.ofNat 352))::
      calldataWord ee.calldata 4::UInt256.ofNat 224::R)
    (Reasoning.Theory.writeWord (delegatedRevokeDataMemory ee.calldata) 256 (UInt256.ofNat 352)) a6 rdata σ k6 C6 at r6
  rw [hf] at r6
  obtain ⟨a7,k7,C7,r7⟩ := easFixedAllocate_ok v .bytes96 (by simp only [List.length_cons]; omega)
    (by native_decide) (by rw [easPatchedValidJumps v]; jump_dest) r6
  simp only [FixedAllocationSite.size,show (UInt256.ofNat 416).toNat = 416 from rfl,show allocateNext 416 96 = 512 by native_decide] at r7
  exact ⟨a7,k7,C7,r7⟩

theorem easDelegatedRevokePrepare {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+14 ≤ 1024)
    (hsize : ee.calldata.size < UInt256.size) (h228 : 228 ≤ ee.calldata.size) (hbig : ee.calldata.size < 2^255+4)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨965⟩ R attestPublicInitialMemory aw rdata σ k C) :
    (delegatedRevokeClean ee.calldata 4 →
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨13806⟩
        (UInt256.ofNat 224::UInt256.ofNat 1136::calldataWord ee.calldata 196::calldataWord ee.calldata 4::UInt256.ofNat 1180::R)
        (delegatedRevokeInputMemory ee.calldata) aw' rdata σ k' C') ∧
    (¬ delegatedRevokeClean ee.calldata 4 → RDrev fork (deployedRuntime v) g s0) := by
  constructor
  · intro hclean
    obtain ⟨a1,k1,C1,r1⟩ := easDelegatedRevokeAllocated v hstack hsize h228 hbig rd
    have hc : UInt256.sub (calldataWord ee.calldata 100) (UInt256.land (calldataWord ee.calldata 100) (UInt256.ofNat 255)) = ⟨0⟩ := by
      have hv : calldataWord ee.calldata 100 = UInt256.land (calldataWord ee.calldata 100) (UInt256.ofNat 255) := hclean.1
      rw [← hv,u256_sub_self]
    obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_1050_fallthrough_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hc r1
    obtain ⟨a3,k3,C3,r3⟩ := easBlocks.eas_block_1064_fallthrough_packed (immWords := wordsOf (immStore v))
      (by omega) (by
        change UInt256.sub (calldataWord ee.calldata 196) (UInt256.land (calldataWord ee.calldata 196) solcAddrMask) = ⟨0⟩
        rw [solcAddrMask_clean hclean.2,u256_sub_self]) r2
    exact easBlocks.eas_block_1119_packed (immWords := wordsOf (immStore v))
      (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r3
  · intro hclean
    obtain ⟨a1,k1,C1,r1⟩ := easDelegatedRevokeAllocated v hstack hsize h228 hbig rd
    by_cases hv : signatureClean (signatureRecord ee.calldata 100)
    · have hc : UInt256.sub (calldataWord ee.calldata 100) (UInt256.land (calldataWord ee.calldata 100) (UInt256.ofNat 255)) = ⟨0⟩ := by
        change calldataWord ee.calldata 100 = UInt256.land (calldataWord ee.calldata 100) (UInt256.ofNat 255) at hv
        rw [← hv,u256_sub_self]
      obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_1050_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hc r1
      have ha : ¬ (calldataWord ee.calldata 196).toNat < EVM.addressModulus := fun ha => hclean ⟨hv,ha⟩
      have hn : calldataWord ee.calldata 196 ≠ UInt256.land (calldataWord ee.calldata 196) solcAddrMask := by
        intro he
        exact ha (he ▸ solcAddrMask_result_canonical _)
      obtain ⟨a3,k3,C3,r3⟩ := easBlocks.eas_block_1064_taken_packed (immWords := wordsOf (immStore v))
        (by omega) (u256_sub_ne_zero_of_ne hn) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r2
      exact easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
        (by simp only [easBlocks.eas_block_1064_taken_stack,List.length_cons]; omega) r3
    · obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_1050_taken_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (u256_sub_ne_zero_of_ne hv)
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
      exact easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
        (by simp only [easBlocks.eas_block_1050_taken_stack,List.length_cons]; omega) r2

end Benchmarks.EAS.EAS
