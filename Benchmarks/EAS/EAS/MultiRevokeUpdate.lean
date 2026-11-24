import Benchmarks.EAS.EAS.MultiRevokeControl
import Benchmarks.EAS.EAS.MultiAttestUpdate
import Benchmarks.EAS.EAS.RuntimeBlocks_008

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easMultiRevokeCall {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C n i : Nat}
    {base available data : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+14 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨3530⟩
      (data::multiRevokeCopySaved ee n i base available R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨12743⟩
      (calldataWord ee.calldata (multiRequestRoot ee.calldata base i).toNat::data::UInt256.ofNat ee.source.val::available::
        multiAttestLastWord n i::multiRevokeSaved n i base available R) mem aw' rdata σ k' C' := by
  obtain ⟨a,j,D,h⟩ := easBlocks.eas_block_3530_packed (immWords := wordsOf (immStore v))
    (by simp only [multiRevokeSaved,List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  exact ⟨a,j,D,h⟩

theorem easMultiRevokeUpdate {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C n i : Nat}
    {base available used : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+12 ≤ 1024)
    (hu : used.toNat ≤ available.toNat)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨1710⟩
      (used::available::⟨3537⟩::⟨1⟩::UInt256.ofNat n::UInt256.ofNat i::base::(UInt256.ofNat n-⟨1⟩)::R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨3396⟩
      (multiRevokeLoopStack n (i+1) base (UInt256.sub available used) R) mem aw' rdata σ k' C' := by
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_1710_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨a2,k2,C2,r2⟩ := easCheckedSub v (by simp only [List.length_cons]; omega) hu
    (by rw [easPatchedValidJumps v]; jump_dest) r1
  obtain ⟨a3,k3,C3,r3⟩ := easBlocks.eas_block_3537_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r2
  have hinc : UInt256.ofNat i+⟨1⟩ = UInt256.ofNat (i+1) := (u256_add_comm _ _).trans (u256_one_add_ofNat i)
  exact ⟨a3,k3,C3,by simpa only [easBlocks.eas_block_3537_stack,hinc] using r3⟩

end Benchmarks.EAS.EAS
