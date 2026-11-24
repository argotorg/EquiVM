import Benchmarks.EAS.EAS.RevokeControl

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easRevokeRevocableCheck {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {packed : UInt256} {R : List UInt256} (v : EASImmutables) (kind : RevokeKind)
    (hstack : R.length+2 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 kind.revocablePC (packed::R) mem aw rdata σ k C) :
    if UInt256.land (UInt256.shiftRight packed ⟨160⟩) ⟨255⟩ ≠ ⟨0⟩ then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 kind.timePC R mem aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  by_cases hv : UInt256.land (UInt256.shiftRight packed ⟨160⟩) ⟨255⟩ ≠ ⟨0⟩
  · rw [if_pos hv]
    have hc : UInt256.isZero (UInt256.land (UInt256.ofNat 255) (UInt256.shiftRight packed (UInt256.ofNat 160))) = UInt256.ofNat 0 := by
      rw [u256_land_comm]; exact isZero_eq_zero_of_ne hv
    cases kind with
    | single => exact easBlocks.eas_block_12394_fallthrough_packed (immWords := wordsOf (immStore v)) hstack hc rd
    | many => exact easBlocks.eas_block_13028_fallthrough_packed (immWords := wordsOf (immStore v)) hstack hc rd
  · rw [if_neg hv]
    have hc : UInt256.isZero (UInt256.land (UInt256.ofNat 255) (UInt256.shiftRight packed (UInt256.ofNat 160))) ≠ UInt256.ofNat 0 := by
      have hz : UInt256.land (UInt256.shiftRight packed (UInt256.ofNat 160)) (UInt256.ofNat 255) = UInt256.ofNat 0 := not_ne_iff.mp hv
      rw [u256_land_comm,hz]; decide
    have hd : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 9647) = true := by rw [easPatchedValidJumps v]; jump_dest
    have hr : ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨9647⟩ R mem aw' rdata σ k' C' := by
      cases kind with
      | single => exact easBlocks.eas_block_12394_taken_packed (immWords := wordsOf (immStore v)) hstack hc hd rd
      | many => exact easBlocks.eas_block_13028_taken_packed (immWords := wordsOf (immStore v)) hstack hc hd rd
    obtain ⟨aw',k',C',hr⟩ := hr
    exact easBlocks.eas_block_9647 (immWords := wordsOf (immStore v)) hstack hr

theorem easRevokeTimeCheck {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {request idx slot schema revoker : UInt256} {R : List UInt256} (v : EASImmutables) (kind : RevokeKind)
    (hstack : R.length+11 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 kind.timePC
      (revokePermissionStack kind request idx slot schema revoker R) mem aw rdata σ k C) :
    if UInt256.land (UInt256.shiftRight (solcSlotWord σ ee (slot+⟨2⟩)) ⟨128⟩) ⟨18446744073709551615⟩ = ⟨0⟩ then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 kind.writePC
        (revokeWriteStack kind request idx slot schema revoker R) mem aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  by_cases hv : UInt256.land (UInt256.shiftRight (solcSlotWord σ ee (slot+⟨2⟩)) ⟨128⟩) ⟨18446744073709551615⟩ = ⟨0⟩
  · rw [if_pos hv]
    cases kind with
    | single =>
      exact easBlocks.eas_block_12405_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hv rd
    | many =>
      exact easBlocks.eas_block_13039_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hv rd
  · rw [if_neg hv]
    have hd : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 12632) = true := by rw [easPatchedValidJumps v]; jump_dest
    cases kind with
    | single =>
      obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_12405_taken_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hv hd rd
      exact easBlocks.eas_block_12632 (immWords := wordsOf (immStore v))
        (by simp only [easBlocks.eas_block_12405_taken_stack,List.length_cons]; omega) hr
    | many =>
      obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_13039_taken_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hv hd rd
      exact easBlocks.eas_block_12632 (immWords := wordsOf (immStore v))
        (by simp only [easBlocks.eas_block_13039_taken_stack,List.length_cons]; omega) hr

end Benchmarks.EAS.EAS
