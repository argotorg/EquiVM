import Benchmarks.EAS.EAS.RequestTimeControl

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

def requestSchemaPtr : UIDSite → UInt256
  | .single _ s2 .. => s2
  | .many _ _ _ s4 .. => s4

def requestRevocableRequirePC : UIDSite → UInt256
  | .single .. => UInt256.ofNat 7943
  | .many .. => UInt256.ofNat 10160

set_option maxRecDepth 10000 in
theorem easRequestRevocableRequire {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {bad : UInt256} {R : List UInt256} (v : EASImmutables) (site : UIDSite)
    (hstack : R.length+2 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 (requestRevocableRequirePC site) (bad::R) mem aw rdata σ k C) :
    if bad = ⟨0⟩ then ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (recordPreparePC site) R mem aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  cases site with
  | single _ _ _ _ _ _ _ _ =>
    by_cases hz : bad = ⟨0⟩
    · rw [if_pos hz]
      exact easBlocks.eas_block_7943_fallthrough_packed (immWords := wordsOf (immStore v)) hstack hz rd
    · rw [if_neg hz]
      obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_7943_taken_packed (immWords := wordsOf (immStore v)) hstack hz
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      exact easBlocks.eas_block_9647 (immWords := wordsOf (immStore v)) hstack hr
  | many _ _ _ _ _ _ =>
    by_cases hz : bad = ⟨0⟩
    · rw [if_pos hz]
      exact easBlocks.eas_block_10160_fallthrough_packed (immWords := wordsOf (immStore v)) hstack hz rd
    · rw [if_neg hz]
      obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_10160_taken_packed (immWords := wordsOf (immStore v)) hstack hz
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      exact easBlocks.eas_block_9647 (immWords := wordsOf (immStore v)) hstack hr

set_option maxRecDepth 10000 in
theorem easRequestRevocableCheck {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {schema idx t3 t4 : UInt256} {R : List UInt256} {schemaRev requestRev : Bool}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+16 ≤ 1024)
    (hs : memLoad (requestSchemaPtr site+UInt256.ofNat 64) mem = UInt256.fromBool schemaRev)
    (hr : UInt256.isZero (UInt256.isZero (memLoad (refUIDPtr site t3+UInt256.ofNat 64) mem)) = requestRev.toUInt256)
    (rd : RD fork (deployedRuntime v) ee g s0 (requestRevocablePC site)
      (uidSaved site (refUIDPtr site t3+UInt256.ofNat 32) (schema::idx::t3::t4::R)) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (requestRevocableRequirePC site)
      ((!schemaRev && requestRev).toUInt256::uidSaved site (refUIDPtr site t3+UInt256.ofNat 32) (schema::idx::t3::t4::R))
      mem aw' rdata σ k' C' := by
  cases schemaRev with
  | false =>
    have hc : UInt256.isZero (memLoad (requestSchemaPtr site+UInt256.ofNat 64) mem) ≠ UInt256.ofNat 0 := by rw [hs]; decide
    cases site with
    | single s1 s2 s3 s4 s5 s6 s7 s8 =>
      obtain ⟨aw1,k1,C1,h1⟩ := easBlocks.eas_block_7932_taken_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hc (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      obtain ⟨aw2,k2,C2,h2⟩ := easBlocks.eas_block_9689_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) h1
      simp only [refUIDPtr] at hr
      exact ⟨aw2,k2,C2,by simpa only [easBlocks.eas_block_9689_stack,hr,Bool.not_false,Bool.true_and] using h2⟩
    | many s1 s2 s3 s4 s5 s6 =>
      obtain ⟨aw1,k1,C1,h1⟩ := easBlocks.eas_block_10149_taken_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hc (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      obtain ⟨aw2,k2,C2,h2⟩ := easBlocks.eas_block_11912_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) h1
      simp only [refUIDPtr] at hr
      exact ⟨aw2,k2,C2,by simpa only [easBlocks.eas_block_11912_stack,hr,Bool.not_false,Bool.true_and] using h2⟩
  | true =>
    have hc : UInt256.isZero (memLoad (requestSchemaPtr site+UInt256.ofNat 64) mem) = UInt256.ofNat 0 := by rw [hs]; decide
    cases site with
    | single s1 s2 s3 s4 s5 s6 s7 s8 =>
      obtain ⟨aw1,k1,C1,h1⟩ := easBlocks.eas_block_7932_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hc rd
      exact ⟨aw1,k1,C1,by simpa only [easBlocks.eas_block_7932_fallthrough_stack,hc,Bool.not_true,Bool.false_and] using h1⟩
    | many s1 s2 s3 s4 s5 s6 =>
      obtain ⟨aw1,k1,C1,h1⟩ := easBlocks.eas_block_10149_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hc rd
      exact ⟨aw1,k1,C1,by simpa only [easBlocks.eas_block_10149_fallthrough_stack,hc,Bool.not_true,Bool.false_and] using h1⟩

end Benchmarks.EAS.EAS
