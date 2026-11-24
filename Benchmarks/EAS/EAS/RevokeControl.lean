import Benchmarks.EAS.EAS.RuntimeBlocks_039
import Benchmarks.EAS.EAS.RuntimeBlocks_040
import Benchmarks.EAS.EAS.RuntimeBlocks_041
import Benchmarks.EAS.EAS.GetAttestationEVM

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

inductive RevokeKind where
  | single | many
def RevokeKind.uidPC : RevokeKind → UInt256 | .single => ⟨12296⟩ | .many => ⟨12935⟩
def RevokeKind.schemaPC : RevokeKind → UInt256 | .single => ⟨12322⟩ | .many => ⟨12961⟩
def RevokeKind.attesterPC : RevokeKind → UInt256 | .single => ⟨12335⟩ | .many => ⟨12972⟩
def RevokeKind.revocablePC : RevokeKind → UInt256 | .single => ⟨12394⟩ | .many => ⟨13028⟩
def RevokeKind.timePC : RevokeKind → UInt256 | .single => ⟨12405⟩ | .many => ⟨13039⟩
def RevokeKind.writePC : RevokeKind → UInt256 | .single => ⟨12429⟩ | .many => ⟨13063⟩

def revokeGuardTail (kind : RevokeKind) (schema revoker : UInt256) (R : List UInt256) : List UInt256 :=
  match kind with | .single => revoker::schema::R | .many => schema::revoker::R
def revokeSchemaStack (kind : RevokeKind) (request idx slot schema revoker : UInt256) (R : List UInt256) : List UInt256 :=
  request::idx::slot::revokeGuardTail kind schema revoker R
def revokeAttesterStack (kind : RevokeKind) (request idx slot schema revoker : UInt256) (R : List UInt256) : List UInt256 :=
  match kind with
  | .single => request::(slot+⟨1⟩)::idx::slot::revoker::schema::R
  | .many => request::idx::slot::schema::revoker::R
def revokePermissionStack (kind : RevokeKind) (request idx slot schema revoker : UInt256) (R : List UInt256) : List UInt256 :=
  match kind with
  | .single => request::UInt256.land revoker solcAddrMask::(slot+⟨1⟩)::idx::slot::revoker::schema::R
  | .many => request::idx::slot::schema::revoker::R
def revokeWriteStack (kind : RevokeKind) (request idx slot schema revoker : UInt256) (R : List UInt256) : List UInt256 :=
  match kind with
  | .single => slot::request::UInt256.land revoker solcAddrMask::(slot+⟨1⟩)::idx::(slot+⟨2⟩)::revoker::schema::R
  | .many => slot::request::idx::(slot+⟨2⟩)::schema::revoker::R

theorem easRevokeUIDCheck {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {cell request idx word : UInt256} {R : List UInt256} (v : EASImmutables) (kind : RevokeKind)
    (hstack : R.length+5 ≤ 1024) (hp : memLoad cell mem = request) (hu : memLoad request mem = word)
    (rd : RD fork (deployedRuntime v) ee g s0 kind.uidPC (cell::idx::R) mem aw rdata σ k C) :
    if solcSlotWord σ ee (dbSlot word) ≠ ⟨0⟩ then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 kind.schemaPC (request::idx::dbSlot word::R)
        (twoWordHashMem word ⟨1⟩ mem) aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  have hk : keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem word ⟨1⟩ mem) = dbSlot word :=
    twoWordHashMem_solcMappingSlot_any ⟨1⟩ word mem
  by_cases hv : solcSlotWord σ ee (dbSlot word) ≠ ⟨0⟩
  · rw [if_pos hv]
    have hc : UInt256.isZero (solcSlotWord σ ee (dbSlot word)) = UInt256.ofNat 0 := isZero_eq_zero_of_ne hv
    cases kind with
    | single =>
      obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_12296_fallthrough_packed (immWords := wordsOf (immStore v)) (x0 := cell) (x1 := idx) (R := R) hstack
        (by
          change UInt256.isZero (solcSlotWord σ ee (keccakWord ⟨0⟩ ⟨64⟩
            (twoWordHashMem (memLoad (memLoad cell mem) mem) ⟨1⟩ mem))) = UInt256.ofNat 0
          rw [hp,hu,hk]
          exact hc) rd
      simp only [easBlocks.eas_block_12296_fallthrough_stack,easBlocks.eas_block_12296_fallthrough_memory,hp,hu] at hr
      change RD fork (deployedRuntime v) ee g s0 _
        (request::idx::keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem word ⟨1⟩ mem)::R)
        (twoWordHashMem word ⟨1⟩ mem) aw' rdata σ k' C' at hr
      rw [hk] at hr
      exact ⟨aw',k',C',hr⟩
    | many =>
      obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_12935_fallthrough_packed (immWords := wordsOf (immStore v)) (x0 := cell) (x1 := idx) (R := R) hstack
        (by
          change UInt256.isZero (solcSlotWord σ ee (keccakWord ⟨0⟩ ⟨64⟩
            (twoWordHashMem (memLoad (memLoad cell mem) mem) ⟨1⟩ mem))) = UInt256.ofNat 0
          rw [hp,hu,hk]
          exact hc) rd
      simp only [easBlocks.eas_block_12935_fallthrough_stack,easBlocks.eas_block_12935_fallthrough_memory,hp,hu] at hr
      change RD fork (deployedRuntime v) ee g s0 _
        (request::idx::keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem word ⟨1⟩ mem)::R)
        (twoWordHashMem word ⟨1⟩ mem) aw' rdata σ k' C' at hr
      rw [hk] at hr
      exact ⟨aw',k',C',hr⟩
  · rw [if_neg hv]
    have hc : UInt256.isZero (solcSlotWord σ ee (dbSlot word)) ≠ UInt256.ofNat 0 := by rw [not_ne_iff.mp hv]; decide
    have hd : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 9302) = true := by rw [easPatchedValidJumps v]; jump_dest
    cases kind with
    | single =>
      obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_12296_taken_packed (immWords := wordsOf (immStore v)) (x0 := cell) (x1 := idx) (R := R) hstack
        (by
          change UInt256.isZero (solcSlotWord σ ee (keccakWord ⟨0⟩ ⟨64⟩
            (twoWordHashMem (memLoad (memLoad cell mem) mem) ⟨1⟩ mem))) ≠ UInt256.ofNat 0
          rw [hp,hu,hk]
          exact hc) hd rd
      exact easBlocks.eas_block_9302 (immWords := wordsOf (immStore v)) (by simp only [easBlocks.eas_block_12296_taken_stack,List.length_cons]; omega) hr
    | many =>
      obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_12935_taken_packed (immWords := wordsOf (immStore v)) (x0 := cell) (x1 := idx) (R := R) hstack
        (by
          change UInt256.isZero (solcSlotWord σ ee (keccakWord ⟨0⟩ ⟨64⟩
            (twoWordHashMem (memLoad (memLoad cell mem) mem) ⟨1⟩ mem))) ≠ UInt256.ofNat 0
          rw [hp,hu,hk]
          exact hc) hd rd
      exact easBlocks.eas_block_9302 (immWords := wordsOf (immStore v)) (by simp only [easBlocks.eas_block_12935_taken_stack,List.length_cons]; omega) hr

end Benchmarks.EAS.EAS
