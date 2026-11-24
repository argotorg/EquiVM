import Benchmarks.EAS.EAS.WordArrayBridge
import Benchmarks.EAS.EAS.RuntimeBlocks_006
import Benchmarks.EAS.EAS.RuntimeBlocks_011
import Benchmarks.EAS.EAS.DelegatedBatchDecode

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def DelegatedBatchSite.pc : DelegatedBatchSite → UInt256
  | .attest => ⟨2691⟩ | .revoke => ⟨1225⟩
def DelegatedBatchSite.callPC : DelegatedBatchSite → UInt256
  | .attest => ⟨2709⟩ | .revoke => ⟨1243⟩
def DelegatedBatchSite.retPC : DelegatedBatchSite → UInt256
  | .attest => ⟨2722⟩ | .revoke => ⟨1256⟩

set_option maxHeartbeats 1000000 in
theorem easDelegatedBatchArrayDecode {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : EASImmutables) (site : DelegatedBatchSite) (hstack : R.length+8 ≤ 1024) (hsize : ee.calldata.size < UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 site.pc R mem aw rdata σ k C) :
    if wordArrayValid ee.calldata then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 site.retPC
        (UInt256.ofNat (wordArrayLength ee.calldata)::UInt256.ofNat (wordArrayOffset ee.calldata+36)::R) mem aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  by_cases ho : wordArrayOffset ee.calldata ≤ solcMaxU64
  · have hread : ∃ a j D, RD fork (deployedRuntime v) ee g s0 site.callPC
        (calldataWord ee.calldata 4::R) mem a rdata σ j D := by
      cases site with
      | attest => exact easBlocks.eas_block_2691_fallthrough_packed (immWords := wordsOf (immStore v)) (by omega) (ugt_zero ho) rd
      | revoke => exact easBlocks.eas_block_1225_fallthrough_packed (immWords := wordsOf (immStore v)) (by omega) (ugt_zero ho) rd
    obtain ⟨a1,k1,C1,r1⟩ := hread
    have hcall : ∃ a j D, RD fork (deployedRuntime v) ee g s0 ⟨4225⟩
        ((UInt256.ofNat 4+calldataWord ee.calldata 4)::UInt256.ofNat ee.calldata.size::site.retPC::R) mem a rdata σ j D := by
      have hd : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 4225) = true := by rw [easPatchedValidJumps v]; jump_dest
      cases site with
      | attest =>
        exact easBlocks.eas_block_2709_packed (immWords := wordsOf (immStore v)) (R := R) (x0 := calldataWord ee.calldata 4)
          (ee := ee) (g := g) (s0 := s0) (mem := mem) (aw := a1) (k := k1) (C := C1) (by omega) hd r1
      | revoke =>
        exact easBlocks.eas_block_1243_packed (immWords := wordsOf (immStore v)) (R := R) (x0 := calldataWord ee.calldata 4)
          (ee := ee) (g := g) (s0 := s0) (mem := mem) (aw := a1) (k := k1) (C := C1) (by omega) hd r1
    obtain ⟨a2,k2,C2,r2⟩ := hcall
    have hd := easWordArrayDecode v hstack hsize ho
      (by cases site <;> simp only [DelegatedBatchSite.retPC] <;> rw [easPatchedValidJumps v] <;> jump_dest) r2
    by_cases hv : wordArrayValid ee.calldata
    · rw [if_pos hv] at hd ⊢
      obtain ⟨j,D,h⟩ := hd
      exact ⟨a2,j,D,h⟩
    · simpa only [if_neg hv] using hd
  · rw [if_neg (fun h => ho h.1)]
    have hg : UInt256.gt (calldataWord ee.calldata 4) (UInt256.ofNat 18446744073709551615) ≠ ⟨0⟩ := by
      have hg1 : UInt256.gt (calldataWord ee.calldata 4) (UInt256.ofNat 18446744073709551615) = ⟨1⟩ :=
        ugt_one (Nat.lt_of_not_ge ho)
      rw [hg1]
      decide
    have hbad : ∃ a j D, RD fork (deployedRuntime v) ee g s0 ⟨402⟩ (calldataWord ee.calldata 4::R) mem a rdata σ j D := by
      have hd : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 402) = true := by rw [easPatchedValidJumps v]; jump_dest
      cases site with
      | attest => exact easBlocks.eas_block_2691_taken_packed (immWords := wordsOf (immStore v)) (by omega) hg hd rd
      | revoke => exact easBlocks.eas_block_1225_taken_packed (immWords := wordsOf (immStore v)) (by omega) hg hd rd
    obtain ⟨a1,k1,C1,r1⟩ := hbad
    exact easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) r1

end Benchmarks.EAS.EAS
