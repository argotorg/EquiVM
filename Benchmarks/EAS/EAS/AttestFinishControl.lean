import Benchmarks.EAS.EAS.AttestLoopControl
import Benchmarks.EAS.EAS.RecordTailPreserve
import Benchmarks.EAS.EAS.RequestRevocableControl

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def attestAvailableWord : UIDSite → UInt256
  | .single _ _ a _ _ _ _ _ => a
  | .many a _ _ _ _ _ => a
def attestLastWord : UIDSite → UInt256
  | .single _ _ _ _ _ _ _ _ => ⟨1⟩
  | .many _ last _ _ _ _ => last
def attestReturnPC : UIDSite → UInt256
  | .single _ _ _ ret _ _ _ _ => ret
  | .many _ _ ret _ _ _ => ret
def attestFinishPC : UIDSite → UInt256
  | .single _ _ _ _ _ _ _ _ => ⟨7871⟩
  | .many _ _ _ _ _ _ => ⟨10084⟩
def attestFinishSaved (site : UIDSite) (R : List UInt256) : List UInt256 :=
  match site with
  | .single _ _ _ ret _ _ result _ => result::ret::R
  | .many _ _ ret _ _ _ => ret::R

theorem easAttestResolveStart {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {schema idx t3 t4 : UInt256} {R : List UInt256} (v : EASImmutables) (site : UIDSite)
    (hstack : R.length+11 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 (attestLoopExitPC site)
      (recordNextStack site schema idx t3 t4 R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨14435⟩
      (requestSchemaPtr site::recordArrayPtr site t3 t4::recordValuesPtr site t4::attestAvailableWord site::
        attestLastWord site::attestFinishPC site::attestFinishSaved site R) mem aw' rdata σ k' C' := by
  cases site with
  | single s1 s2 s3 s4 s5 s6 s7 s8 =>
    obtain ⟨a,j,D,hr⟩ := easBlocks.eas_block_7853_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨a,j,D,hr⟩
  | many s1 s2 s3 s4 s5 s6 =>
    obtain ⟨a,j,D,hr⟩ := easBlocks.eas_block_10072_packed (immWords := wordsOf (immStore v))
      (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨a,j,D,hr⟩

theorem easAttestReturn {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {used : UInt256} {R : List UInt256} (v : EASImmutables) (site : UIDSite)
    (hstack : R.length+4 ≤ 1024) (hlo : 160 ≤ (recordResultPtr site mem).toNat)
    (hcovered : (recordResultPtr site mem).toNat+32 ≤ mem.size)
    (hret : (D_J (deployedRuntime v) 0).contains (attestReturnPC site) = true)
    (rd : RD fork (deployedRuntime v) ee g s0 (attestFinishPC site)
      (used::attestFinishSaved site R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (attestReturnPC site)
      (recordResultPtr site mem::R) (Reasoning.Theory.writeWord mem (recordResultPtr site mem).toNat used)
      aw' rdata σ k' C' := by
  cases site with
  | single s1 s2 s3 s4 s5 s6 s7 s8 =>
    exact easBlocks.eas_block_7871_packed (immWords := wordsOf (immStore v)) hstack hret rd
  | many s1 s2 s3 s4 s5 s6 =>
    obtain ⟨a,j,D,hr⟩ := easBlocks.eas_block_10084_packed (immWords := wordsOf (immStore v)) (by omega) hret rd
    have hp := memLoad_write_below mem (memLoad (UInt256.ofNat 128) mem).toNat (UInt256.ofNat 128) used hlo
      (by change 160 ≤ mem.size; have hl : 160 ≤ (memLoad (UInt256.ofNat 128) mem).toNat := hlo
          have hc : (memLoad (UInt256.ofNat 128) mem).toNat+32 ≤ mem.size := hcovered
          omega)
    simp only [Reasoning.Theory.writeWord] at hp
    simpa only [easBlocks.eas_block_10084_stack,easBlocks.eas_block_10084_memory,
      Reasoning.Theory.writeWord,recordResultPtr,attestReturnPC,hp] using (show ∃ a j D, RD fork (deployedRuntime v) ee g s0 s3
        (easBlocks.eas_block_10084_stack (mem := mem) (x0 := used) (R := R))
        (easBlocks.eas_block_10084_memory (mem := mem) (x0 := used)) a rdata σ j D from ⟨a,j,D,hr⟩)

end Benchmarks.EAS.EAS
