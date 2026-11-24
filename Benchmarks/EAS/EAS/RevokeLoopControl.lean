import Benchmarks.EAS.EAS.RevokeLayout
import Benchmarks.EAS.EAS.MemoryArrayIndex

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def RevokeKind.readPC : RevokeKind → UInt256 | .single => ⟨12286⟩ | .many => ⟨12925⟩
def RevokeKind.exitPC : RevokeKind → UInt256 | .single => ⟨12265⟩ | .many => ⟨12911⟩

theorem easRevokeLoopTest {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C i : Nat} {R : List UInt256}
    (v : EASImmutables) (site : RevokeSite) (hstack : R.length+13 ≤ 1024)
    (hi : i < UInt256.size) (hlen : site.length < UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 site.kind.loopPC
      (revokeLoopStack site ee (UInt256.ofNat i) R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0
      (if i < site.length then site.kind.readPC else site.kind.exitPC)
      (revokeLoopStack site ee (UInt256.ofNat i) R) mem aw' rdata σ k' C' := by
  by_cases hb : i < site.length
  · rw [if_pos hb]
    have hc : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat site.length) ≠ UInt256.ofNat 0 := by
      rw [ult_one (by rw [ulit_toNat' _ hi,ulit_toNat' _ hlen]; exact hb)]; decide
    cases hk : site.kind with
    | single =>
      simp only [revokeLoopStack,revokeGuardTail,revokeGuardRest,hk,RevokeKind.loopPC,RevokeKind.readPC,
        List.cons_append,List.nil_append] at rd ⊢
      exact easBlocks.eas_block_12257_taken_packed (immWords := wordsOf (immStore v))
        (by first | omega | (simp only [List.length_cons]; omega)) hc (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    | many =>
      simp only [revokeLoopStack,revokeGuardTail,revokeGuardRest,hk,RevokeKind.loopPC,RevokeKind.readPC,
        List.cons_append,List.nil_append] at rd ⊢
      exact easBlocks.eas_block_12903_taken_packed (immWords := wordsOf (immStore v))
        (by first | omega | (simp only [List.length_cons]; omega)) hc (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  · rw [if_neg hb]
    have hc : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat site.length) = UInt256.ofNat 0 :=
      ult_zero (by rw [ulit_toNat' _ hi,ulit_toNat' _ hlen]; omega)
    cases hk : site.kind with
    | single =>
      simp only [revokeLoopStack,revokeGuardTail,revokeGuardRest,hk,RevokeKind.loopPC,RevokeKind.exitPC,
        List.cons_append,List.nil_append] at rd ⊢
      exact easBlocks.eas_block_12257_fallthrough_packed (immWords := wordsOf (immStore v))
        (by first | omega | (simp only [List.length_cons]; omega)) hc rd
    | many =>
      simp only [revokeLoopStack,revokeGuardTail,revokeGuardRest,hk,RevokeKind.loopPC,RevokeKind.exitPC,
        List.cons_append,List.nil_append] at rd ⊢
      exact easBlocks.eas_block_12903_fallthrough_packed (immWords := wordsOf (immStore v))
        (by first | omega | (simp only [List.length_cons]; omega)) hc rd

theorem easRevokeRequestRead {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C i : Nat} {R : List UInt256}
    (v : EASImmutables) (site : RevokeSite) (hstack : R.length+17 ≤ 1024) (hi : i < site.length)
    (hb : site.data.toNat+32+32*site.length < UInt256.size)
    (hl : memLoad site.data mem = UInt256.ofNat site.length)
    (rd : RD fork (deployedRuntime v) ee g s0 site.kind.readPC
      (revokeLoopStack site ee (UInt256.ofNat i) R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 site.kind.uidPC
      (UInt256.ofNat (site.data.toNat+32+32*i)::revokeLoopStack site ee (UInt256.ofNat i) R)
      mem aw' rdata σ k' C' := by
  cases hk : site.kind with
  | single =>
    simp only [revokeLoopStack,revokeGuardTail,revokeGuardRest,hk,RevokeKind.readPC,RevokeKind.uidPC,
      List.cons_append,List.nil_append] at rd ⊢
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_12286_packed (immWords := wordsOf (immStore v))
      (by first | omega | (simp only [List.length_cons]; omega)) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact easMemoryArrayIndex v (by first | omega | (simp only [List.length_cons]; omega)) hi (by omega) (by omega) hl
      (by rw [easPatchedValidJumps v]; jump_dest) rd1
  | many =>
    simp only [revokeLoopStack,revokeGuardTail,revokeGuardRest,hk,RevokeKind.readPC,RevokeKind.uidPC,
      List.cons_append,List.nil_append] at rd ⊢
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_12925_packed (immWords := wordsOf (immStore v))
      (by first | omega | (simp only [List.length_cons]; omega)) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact easMemoryArrayIndex v (by first | omega | (simp only [List.length_cons]; omega)) hi (by omega) (by omega) hl
      (by rw [easPatchedValidJumps v]; jump_dest) rd1

theorem easRevokeLoopExit {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} {idx : UInt256} {R : List UInt256}
    (v : EASImmutables) (site : RevokeSite) (hstack : R.length+11 ≤ 1024)
    (hlast : site.kind = .single → site.last = true)
    (rd : RD fork (deployedRuntime v) ee g s0 site.kind.exitPC
      (revokeLoopStack site ee idx R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨15058⟩
      (site.schemaPtr::site.records::site.values::site.available::site.last.toUInt256::⟨4692⟩::site.ret::R)
      mem aw' rdata σ k' C' := by
  cases hk : site.kind with
  | single =>
    simp only [revokeLoopStack,revokeGuardTail,revokeGuardRest,hk,RevokeKind.exitPC,
      List.cons_append,List.nil_append] at rd
    rw [hlast hk]
    exact easBlocks.eas_block_12265_packed (immWords := wordsOf (immStore v))
      (by first | omega | (simp only [List.length_cons]; omega)) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  | many =>
    simp only [revokeLoopStack,revokeGuardTail,revokeGuardRest,hk,RevokeKind.exitPC,
      List.cons_append,List.nil_append] at rd
    exact easBlocks.eas_block_12911_packed (immWords := wordsOf (immStore v))
      (by first | omega | (simp only [List.length_cons]; omega)) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd

end Benchmarks.EAS.EAS
