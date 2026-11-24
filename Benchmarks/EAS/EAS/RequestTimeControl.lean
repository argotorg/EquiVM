import Benchmarks.EAS.EAS.RecordPrepare
import Benchmarks.EAS.EAS.RuntimeBlocks_032
import Benchmarks.EAS.EAS.RuntimeBlocks_037

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

def requestTimeComparePC : UIDSite → UInt256
  | .single .. => UInt256.ofNat 9744
  | .many .. => UInt256.ofNat 11925
def requestTimeRequirePC : UIDSite → UInt256
  | .single .. => UInt256.ofNat 7926
  | .many .. => UInt256.ofNat 10143
def requestRevocablePC : UIDSite → UInt256
  | .single .. => UInt256.ofNat 7932
  | .many .. => UInt256.ofNat 10149

set_option maxRecDepth 10000 in
theorem easRequestTimeCompare {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {expire dummy : UInt256} {R : List UInt256} (v : EASImmutables) (site : UIDSite)
    (hstack : R.length+3 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 (requestTimeComparePC site) (expire::dummy::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (requestTimeRequirePC site)
      (UInt256.ofNat (deployedRuntime v).size::UInt256.isZero (UInt256.lt (easTimeWord ee) expire)::R) mem aw' rdata σ k' C' := by
  cases site with
  | single _ _ _ _ _ _ _ _ =>
    exact easBlocks.eas_block_9744_packed (immWords := wordsOf (immStore v)) hstack
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  | many _ _ _ _ _ _ =>
    exact easBlocks.eas_block_11925_packed (immWords := wordsOf (immStore v)) hstack
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd

set_option maxRecDepth 10000 in
theorem easRequestTimeRequire {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {dummy bad : UInt256} {R : List UInt256} (v : EASImmutables) (site : UIDSite)
    (hstack : R.length+2 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 (requestTimeRequirePC site) (dummy::bad::R) mem aw rdata σ k C) :
    if bad = ⟨0⟩ then ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (requestRevocablePC site) R mem aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  cases site with
  | single _ _ _ _ _ _ _ _ =>
    by_cases hz : bad = ⟨0⟩
    · rw [if_pos hz]
      exact easBlocks.eas_block_7926_fallthrough_packed (immWords := wordsOf (immStore v)) hstack hz rd
    · rw [if_neg hz]
      obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_7926_taken_packed (immWords := wordsOf (immStore v)) hstack hz
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      exact easBlocks.eas_block_9702 (immWords := wordsOf (immStore v)) hstack hr
  | many _ _ _ _ _ _ =>
    by_cases hz : bad = ⟨0⟩
    · rw [if_pos hz]
      exact easBlocks.eas_block_10143_fallthrough_packed (immWords := wordsOf (immStore v)) hstack hz rd
    · rw [if_neg hz]
      obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_10143_taken_packed (immWords := wordsOf (immStore v)) hstack hz
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      exact easBlocks.eas_block_9702 (immWords := wordsOf (immStore v)) hstack hr

end Benchmarks.EAS.EAS
