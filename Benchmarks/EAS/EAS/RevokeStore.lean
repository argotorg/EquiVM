import Benchmarks.EAS.EAS.RevokeLayout
import Benchmarks.EAS.EAS.AttestationAlias
import Benchmarks.EAS.EAS.RevokeStatic

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: packed stores depend only on the low bits of their data word.
theorem packedSliceWord_data_congr (old a b : UInt256) (start width : Nat)
    (hs : start < 256) (hw : start+width ≤ 256) (he : a.toNat % 2^width = b.toNat % 2^width) :
    packedSliceWord old a start width = packedSliceWord old b start width := by
  apply u256_inj
  rw [packedSliceWord_toNat _ _ _ _ hs hw,packedSliceWord_toNat _ _ _ _ hs hw,he]

theorem revokeTimePacked (ee : ExecutionEnv) (old : UInt256) :
    packedSliceWord old (UInt256.ofNat ee.header.timestamp) 128 64 = packedSliceWord old (easTimeWord ee) 128 64 := by
  apply packedSliceWord_data_congr _ _ _ _ _ (by decide) (by decide)
  rw [easTimeWord,uland_toNat]
  change _ = (Nat.land (UInt256.ofNat ee.header.timestamp).toNat (2^64-1)) % 2^64
  rw [nat_land_mask_eq_mod,Nat.mod_mod]

theorem easRevokeStore_ok {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {request idx word : UInt256} {R : List UInt256} (v : EASImmutables) (site : RevokeSite)
    (hstack : R.length+31 ≤ 1024) (hperm : ee.perm = true)
    (rd : RD fork (deployedRuntime v) ee g s0 site.kind.writePC
      (revokeWriteStack site.kind request idx (dbSlot word) site.schema (UInt256.ofNat site.revoker.val)
        (revokeGuardRest site ee R)) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨6501⟩
      (dbSlot word::site.kind.copyReturnPC::revokeCopySaved site ee request idx word R) mem aw' rdata
      ((revokeTimeField word (easTimeWord ee)).accounts σ ee) k' C' := by
  cases hk : site.kind with
  | single =>
    simp only [revokeWriteStack,revokeGuardRest,hk,List.cons_append,List.nil_append,
      show UInt256.land (UInt256.ofNat site.revoker.val) solcAddrMask = UInt256.ofNat site.revoker.val from addressWord_val_clean _] at rd
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_12429_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hperm (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    obtain ⟨aw2,k2,C2,rd2⟩ := easBlocks.eas_block_12576_packed (immWords := wordsOf (immStore v))
      (by simp only [easBlocks.eas_block_12429_stack,List.length_cons]; omega)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact ⟨aw2,k2,C2,by simpa only [hk,revokeCopySaved,RevokeKind.copyReturnPC,easBlocks.eas_block_12576_stack,
      easBlocks.eas_block_12429_stack,revokeTimeField,attestationTimeWrite,ScalarFieldWrite.accounts,attestationU64Loc,packedSliceWord] using rd2⟩
  | many =>
    simp only [revokeWriteStack,revokeGuardRest,hk,List.cons_append,List.nil_append] at rd
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_13063_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hperm (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    have hm (old : UInt256) :
        UInt256.lor (UInt256.land (UInt256.ofNat 6277101735386680763495507056286727952638980837032266301440)
          (UInt256.shiftLeft (UInt256.ofNat ee.header.timestamp) (UInt256.ofNat 128)))
          (UInt256.land (UInt256.ofNat 115792089237316195417293883273301227089774477609353836086818603170880863338495) old) =
        packedSliceWord old (easTimeWord ee) 128 64 := by
      rw [u256_lor_comm,u256_land_comm (UInt256.ofNat 6277101735386680763495507056286727952638980837032266301440),
        u256_land_comm (UInt256.ofNat 115792089237316195417293883273301227089774477609353836086818603170880863338495)]
      exact revokeTimePacked ee old
    simp only [hm] at rd1
    exact ⟨aw1,k1,C1,by simpa only [hk,revokeCopySaved,RevokeKind.copyReturnPC] using rd1⟩

theorem easRevokeStore_static {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {request idx word : UInt256} {R : List UInt256} (v : EASImmutables) (site : RevokeSite)
    (hstack : R.length+31 ≤ 1024) (hperm : ee.perm = false)
    (rd : RD fork (deployedRuntime v) ee g s0 site.kind.writePC
      (revokeWriteStack site.kind request idx (dbSlot word) site.schema (UInt256.ofNat site.revoker.val)
        (revokeGuardRest site ee R)) mem aw rdata σ k C) : RDstatic fork (deployedRuntime v) g s0 := by
  cases hk : site.kind with
  | single =>
    simp only [revokeWriteStack,revokeGuardRest,hk,List.cons_append,List.nil_append] at rd
    exact easRevokeSingle_static v (by simp only [List.length_cons]; omega) hperm rd
  | many =>
    simp only [revokeWriteStack,revokeGuardRest,hk,List.cons_append,List.nil_append] at rd
    exact easRevokeMany_static v (by simp only [List.length_cons]; omega) hperm rd

end Benchmarks.EAS.EAS
