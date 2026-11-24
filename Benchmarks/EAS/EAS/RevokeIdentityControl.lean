import Benchmarks.EAS.EAS.RevokeControl

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easRevokeSchemaCheck {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {request idx slot schema revoker : UInt256} {R : List UInt256} (v : EASImmutables) (kind : RevokeKind)
    (hstack : R.length+8 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 kind.schemaPC
      (revokeSchemaStack kind request idx slot schema revoker R) mem aw rdata σ k C) :
    if solcSlotWord σ ee (slot+⟨1⟩) = schema then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 kind.attesterPC
        (revokeAttesterStack kind request idx slot schema revoker R) mem aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  by_cases hv : solcSlotWord σ ee (slot+⟨1⟩) = schema
  · rw [if_pos hv]
    have hc : UInt256.sub (solcSlotWord σ ee (slot+⟨1⟩)) schema = UInt256.ofNat 0 := u256_sub_eq_zero_iff_eq.mpr hv
    cases kind with
    | single => exact easBlocks.eas_block_12322_fallthrough_packed (immWords := wordsOf (immStore v)) hstack hc rd
    | many => exact easBlocks.eas_block_12961_fallthrough_packed (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hc rd
  · rw [if_neg hv]
    have hc := u256_sub_ne_zero_of_ne hv
    have hd : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 9765) = true := by rw [easPatchedValidJumps v]; jump_dest
    cases kind with
    | single =>
      obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_12322_taken_packed (immWords := wordsOf (immStore v)) hstack hc hd rd
      exact easBlocks.eas_block_9765 (immWords := wordsOf (immStore v))
        (by simp only [easBlocks.eas_block_12322_taken_stack,List.length_cons]; omega) hr
    | many =>
      obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_12961_taken_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hc hd rd
      exact easBlocks.eas_block_9765 (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hr

theorem easRevokeAttesterCheck {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {request idx slot schema revoker : UInt256} {R : List UInt256} (v : EASImmutables) (kind : RevokeKind)
    (hstack : R.length+11 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 kind.attesterPC
      (revokeAttesterStack kind request idx slot schema revoker R) mem aw rdata σ k C) :
    if UInt256.land (solcSlotWord σ ee (slot+⟨5⟩)) solcAddrMask = UInt256.land revoker solcAddrMask then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 kind.revocablePC
        (solcSlotWord σ ee (slot+⟨5⟩)::revokePermissionStack kind request idx slot schema revoker R) mem aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  by_cases hv : UInt256.land (solcSlotWord σ ee (slot+⟨5⟩)) solcAddrMask = UInt256.land revoker solcAddrMask
  · rw [if_pos hv]
    have hc := u256_sub_eq_zero_iff_eq.mpr hv
    cases kind with
    | single =>
      exact easBlocks.eas_block_12335_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hc rd
    | many => exact easBlocks.eas_block_12972_fallthrough_packed (immWords := wordsOf (immStore v)) (by omega) hc rd
  · rw [if_neg hv]
    have hc := u256_sub_ne_zero_of_ne hv
    have hd : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 12674) = true := by rw [easPatchedValidJumps v]; jump_dest
    cases kind with
    | single =>
      obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_12335_taken_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hc hd rd
      exact easBlocks.eas_block_12674 (immWords := wordsOf (immStore v))
        (by simp only [easBlocks.eas_block_12335_taken_stack,List.length_cons]; omega) hr
    | many =>
      obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_12972_taken_packed (immWords := wordsOf (immStore v)) (by omega) hc hd rd
      exact easBlocks.eas_block_12674 (immWords := wordsOf (immStore v))
        (by simp only [easBlocks.eas_block_12972_taken_stack,List.length_cons]; omega) hr

end Benchmarks.EAS.EAS
