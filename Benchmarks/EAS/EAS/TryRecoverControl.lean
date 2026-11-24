import Benchmarks.EAS.EAS.TryRecoverMemory
import Benchmarks.EAS.EAS.TryRecoverSource
import Benchmarks.EAS.EAS.RuntimeBlocks_033
import Benchmarks.EAS.EAS.RuntimeBlocks_054

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem tryRecoverHighEVM {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {hash sigV r s ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+11 ≤ 1024) (hi : ecdsaHalfOrder < s.toNat)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨16645⟩ (hash::sigV::r::s::ret::R) mem aw rdata σ k C) :
    ∃ k' C', RD fork (deployedRuntime v) ee g s0 ret (⟨3⟩::⟨0⟩::R) mem aw rdata σ k' C' := by
  have hc : UInt256.gt s (UInt256.ofNat ecdsaHalfOrder) = ⟨1⟩ := ugt_one hi
  dsimp only [ecdsaHalfOrder] at hc
  have r1 := easBlocks.eas_block_16645_taken (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [hc]; decide)
    (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  exact RD.pack (easBlocks.eas_block_16774 (immWords := wordsOf (immStore v)) (by omega) hret r1)

theorem tryRecoverStart {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {heap hash sigV r s ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+11 ≤ 1024) (hi : ¬ ecdsaHalfOrder < s.toNat)
    (hh : memLoad (UInt256.ofNat 64) mem = heap) (hv : sigV.toNat < 2^8) (hb : heap.toNat+128 < UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨16645⟩ (hash::sigV::r::s::ret::R) mem aw rdata σ k C) :
    ∃ gasArg aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨16723⟩
      (gasArg::⟨1⟩::heap::⟨128⟩::⟨0⟩::⟨32⟩::ret::R)
      (tryRecoverInputMemory mem heap hash sigV r s) aw' rdata σ k' C' := by
  have hc : UInt256.gt s (UInt256.ofNat ecdsaHalfOrder) = ⟨0⟩ := ugt_zero (Nat.le_of_not_gt hi)
  have r1 := easBlocks.eas_block_16645_fallthrough (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) hc rd
  obtain ⟨aw1,k1,C1,r2⟩ := easBlocks.eas_block_16685_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) r1
  rw [tryRecoverInputMemory_eq hh hv hb] at r2
  simp only [easBlocks.eas_block_16685_stack,hh] at r2
  exact ⟨_,aw1,k1,C1,r2⟩

theorem tryRecoverCall_decode (v : EASImmutables) :
    decode (deployedRuntime v) ⟨16723⟩ = some (.STATICCALL,none) := by
  change decode (immutableLayout.runtime easBytecode (wordsOf (immStore v))) (UInt256.ofNat 16723) = _
  immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨16723⟩ : UInt256), UInt8.ofNat 250,
    .STATICCALL, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)

theorem tryRecoverFinish {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap} {k C : Nat}
    {a : AccountAddress} {ret : UInt256} {R : List UInt256} (v : EASImmutables) (success : Bool)
    (hstack : R.length+5 ≤ 1024) (ha : memLoad (UInt256.ofNat 0) mem = UInt256.ofNat a.val)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨16724⟩ ((if success then ⟨1⟩ else ⟨0⟩)::ret::R) mem aw out σ k C) :
    if success then ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret
      (UInt256.ofNat (recoveryError a)::UInt256.ofNat a.val::R) mem aw' out σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  have haddr : (UInt256.ofNat a.val).toNat = a.val := addressWord_toNat_val a
  cases success with
  | false =>
    have r1 := easBlocks.eas_block_16724_taken (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by decide)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact easBlocks.eas_block_9844 (immWords := wordsOf (immStore v))
      (by simp only [easBlocks.eas_block_16724_taken_stack,List.length_cons]; omega)
      (by change 0 + out.size % UInt256.size ≤ out.size; exact (Nat.zero_add _).symm ▸ Nat.mod_le _ _) r1
  | true =>
    have r1 := easBlocks.eas_block_16724_fallthrough (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) rfl rd
    have hm : UInt256.land (memLoad (UInt256.ofNat 0) mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = UInt256.ofNat a.val := by
      rw [ha]
      exact u256LandMaskCleanOfToNat _ _ (bits := 160) rfl (by rw [haddr]; exact a.isLt)
    by_cases hz : a = 0
    · have r2 := easBlocks.eas_block_16729_taken (immWords := wordsOf (immStore v))
        (by simp only [easBlocks.eas_block_16724_fallthrough_stack,List.length_cons]; omega)
        (by rw [hm,hz]; decide) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
      have r3 := easBlocks.eas_block_16765 (immWords := wordsOf (immStore v)) (by omega) hret r2
      simp only [recoveryError,hz,if_pos rfl]
      exact ⟨_,_,_,r3⟩
    · have hn : UInt256.ofNat a.val ≠ ⟨0⟩ := by
        intro he
        apply hz
        apply Fin.ext
        have he' := congrArg UInt256.toNat he
        rw [haddr] at he'
        exact he'
      have r2 := easBlocks.eas_block_16729_fallthrough (immWords := wordsOf (immStore v))
        (by simp only [easBlocks.eas_block_16724_fallthrough_stack,List.length_cons]; omega)
        (by rw [hm]; exact isZero_eq_zero_of_ne hn) r1
      have r3 := easBlocks.eas_block_16760 (immWords := wordsOf (immStore v)) (by omega) hret r2
      simp only [easBlocks.eas_block_16760_stack,ha] at r3
      simp only [recoveryError,if_neg hz]
      exact ⟨_,_,_,r3⟩

end Benchmarks.EAS.EAS
