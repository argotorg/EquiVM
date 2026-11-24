import Benchmarks.EAS.EAS.DelegatedBatchIndex
import Benchmarks.EAS.EAS.MultiDelegatedRevokeVerifyPrepare
import Benchmarks.EAS.EAS.MultiRevokeUpdate

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def multiDelegatedRevokeLoopStack (n i : Nat) (base available : UInt256) (R : List UInt256) : List UInt256 :=
  [UInt256.ofNat n,base,UInt256.ofNat n-⟨1⟩,available,UInt256.ofNat i]++R

theorem easMultiDelegatedRevokeAccess {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C n i : Nat}
    {base available : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+12 ≤ 1024)
    (hi : i<n) (hn : n<UInt256.size) (hb : base.toNat+32*i < UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨1298⟩ (multiDelegatedRevokeLoopStack n i base available R) mem aw rdata σ k C) :
    if delegatedBatchReferenceValid ee.calldata base i then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨1318⟩
        (multiRequestRoot ee.calldata base i::multiDelegatedRevokeLoopStack n i base available R) mem aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  simp only [multiDelegatedRevokeLoopStack,List.cons_append,List.nil_append] at rd ⊢
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_1298_taken_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [ult_one (by rw [ulit_toNat' i (by omega),ulit_toNat' n hn]; exact hi)]; decide)
    (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_1307_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
  exact easDelegatedBatchIndex v (by simp only [List.length_cons]; omega) hi hn hb
    (by rw [easPatchedValidJumps v]; jump_dest) r2

theorem easMultiDelegatedRevokeDone {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C n : Nat}
    {base available : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+7 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨1298⟩ (multiDelegatedRevokeLoopStack n n base available R) mem aw rdata σ k C) :
    RDret fork (deployedRuntime v) g s0 σ ByteArray.empty := by
  simp only [multiDelegatedRevokeLoopStack,List.cons_append,List.nil_append] at rd
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_1298_fallthrough_packed (immWords := wordsOf (immStore v))
    (by omega) (ult_zero (le_refl _)) rd
  exact easBlocks.eas_block_1306 (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) r1

theorem easMultiDelegatedRevokeVerifyDone {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C n i heap : Nat}
    {base available row data sig : UInt256} {r : DelegatedRevocationBatch} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+18 ≤ 1024)
    (hv : DelegatedRevocationBatchMemoryView mem row data sig r heap)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨1552⟩
      (multiDelegatedRevokeVerifyStack r.data.length base (UInt256.ofNat n) available (UInt256.ofNat n-⟨1⟩) row data
        (UInt256.ofNat i::R)) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨12743⟩
      ([r.schema,data,UInt256.ofNat r.revoker.val,available,multiAttestLastWord n i,⟨1710⟩,
        available,⟨1716⟩,⟨1⟩,UInt256.ofNat n,UInt256.ofNat n-⟨1⟩,base,UInt256.ofNat i]++R)
      mem aw' rdata σ k' C' := by
  simp only [multiDelegatedRevokeVerifyStack,List.cons_append,List.nil_append] at rd
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_1552_taken_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [hv.data.length,ult_zero (le_refl _)]; decide)
    (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_1658_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
  have hac : UInt256.land (UInt256.ofNat r.revoker.val) (UInt256.ofNat 1461501637330902918203684832716283019655932542975) =
      UInt256.ofNat r.revoker.val := addressWord_val_clean r.revoker
  exact ⟨a2,k2,C2,by simpa only [easBlocks.eas_block_1658_stack,hv.schema,hv.revoker,hac,multiAttestLastWord] using r2⟩

theorem easMultiDelegatedRevokeUpdate {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C n i : Nat}
    {base available used : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+12 ≤ 1024)
    (hu : used.toNat ≤ available.toNat)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨1710⟩
      ([used,available,⟨1716⟩,⟨1⟩,UInt256.ofNat n,UInt256.ofNat n-⟨1⟩,base,UInt256.ofNat i]++R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨1298⟩
      (multiDelegatedRevokeLoopStack n (i+1) base (UInt256.sub available used) R) mem aw' rdata σ k' C' := by
  simp only [List.cons_append,List.nil_append] at rd
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_1710_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨a2,k2,C2,r2⟩ := easCheckedSub v (by simp only [List.length_cons]; omega) hu
    (by rw [easPatchedValidJumps v]; jump_dest) r1
  obtain ⟨a3,k3,C3,r3⟩ := easBlocks.eas_block_1716_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r2
  have hinc : UInt256.ofNat i+⟨1⟩=UInt256.ofNat (i+1) := (u256_add_comm _ _).trans (u256_one_add_ofNat i)
  exact ⟨a3,k3,C3,by simpa only [easBlocks.eas_block_1716_stack,hinc,multiDelegatedRevokeLoopStack] using r3⟩

end Benchmarks.EAS.EAS
