import Benchmarks.EAS.EAS.CopyRequestArrayHead
import Benchmarks.EAS.EAS.CopyRequestCall

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easCopyRequestArrayDone {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {dst src base stop ret array : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+9 ≤ 1024) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5594⟩ (dst::src::base::src::stop::ret::array::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (array::R) mem aw' rdata σ k' C' := by
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_5594_fallthrough_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (ult_zero (le_refl _)) rd
  exact easBlocks.eas_block_5602_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) hret r1

theorem easCopyRequestArrayRead {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {dst src base limit stop ret array : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+14 ≤ 1024) (hi : src.toNat < limit.toNat)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5594⟩ (dst::src::base::limit::stop::ret::array::R) mem aw rdata σ k C) :
    ((calldataWord ee.calldata src.toNat).toNat ≤ 2^64-1 →
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨5344⟩
        ((base+calldataWord ee.calldata src.toNat)::stop::⟨5641⟩::dst::⟨32⟩::⟨32⟩::src::base::limit::stop::ret::array::R)
        mem aw' rdata σ k' C') ∧
    (¬ (calldataWord ee.calldata src.toNat).toNat ≤ 2^64-1 → RDrev fork (deployedRuntime v) g s0) := by
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_5594_taken_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [ult_one hi]; decide)
    (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  constructor
  · intro ho
    have hg : UInt256.gt (calldataWord ee.calldata src.toNat) (UInt256.ofNat (2^64-1)) = ⟨0⟩ := by
      exact ugt_zero ho
    obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_5608_fallthrough_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hg r1
    obtain ⟨a3,k3,C3,r3⟩ := easBlocks.eas_block_5626_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r2
    exact ⟨a3,k3,C3,r3⟩
  · intro ho
    have hg : UInt256.gt (calldataWord ee.calldata src.toNat) (UInt256.ofNat (2^64-1)) ≠ ⟨0⟩ := by
      rw [ugt_one (by change 18446744073709551615 < _; omega)]; decide
    obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_5608_taken_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hg (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
    exact easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
      (by simp only [easBlocks.eas_block_5608_taken_stack,List.length_cons]; omega) r2

theorem easCopyRequestArraySet {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ptr dst src : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+6 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5641⟩ (ptr::dst::⟨32⟩::⟨32⟩::src::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨5594⟩ ((dst+⟨32⟩)::(src+⟨32⟩)::R)
      (Reasoning.Theory.writeWord mem dst.toNat ptr) aw' rdata σ k' C' :=
  easBlocks.eas_block_5641_packed (immWords := wordsOf (immStore v)) hstack
    (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd

end Benchmarks.EAS.EAS
