import Benchmarks.EAS.EAS.SchemaSites
import Benchmarks.EAS.EAS.RuntimeBlocks_029
import Benchmarks.EAS.EAS.RuntimeBlocks_033
import Benchmarks.EAS.EAS.RuntimeBlocks_037
import Benchmarks.EAS.EAS.RuntimeBlocks_038
import Benchmarks.EAS.EAS.RuntimeBlocks_039
import Benchmarks.EAS.EAS.RuntimeBlocks_040
import Benchmarks.EAS.EAS.RuntimeBlocks_041

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def schemaDecodeReturnPC : SchemaCallSite → UInt256
  | .at7795 .. => ⟨9837⟩
  | .at10016 .. => ⟨11968⟩
  | .at12196 => ⟨12737⟩
  | .at12855 => ⟨13309⟩
def schemaDecodeSaved (site : SchemaCallSite) (R : List UInt256) : List UInt256 :=
  match site with
  | .at7795 a b => b::a::R
  | .at10016 a b c d e => b::c::d::e::a::R
  | .at12196 | .at12855 => R
def schemaDonePC : SchemaCallSite → UInt256
  | .at7795 .. => ⟨7810⟩
  | .at10016 .. => ⟨10031⟩
  | .at12196 => ⟨12211⟩
  | .at12855 => ⟨12870⟩
def schemaDoneStack (v : EASImmutables) (site : SchemaCallSite) (record : UInt256) (R : List UInt256) : List UInt256 :=
  UInt256.ofNat (deployedRuntime v).size :: match site with
  | .at7795 a b => a::b::record::R
  | .at10016 a b c d e => a::b::c::d::e::record::R
  | .at12196 | .at12855 => record::R

theorem schemaDecodeReturn_valid (v : EASImmutables) (site : SchemaCallSite) :
    (D_J (deployedRuntime v) 0).contains (schemaDecodeReturnPC site) = true := by
  cases site <;> rw [easPatchedValidJumps v] <;> unfold schemaDecodeReturnPC <;> jump_dest

theorem schemaCallResultPrepare {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw ptr : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : EASImmutables) (site : SchemaCallSite) (success : Bool)
    (hstack : R.length+15 ≤ 1024) (hout : out.size < 2^138)
    (rd : RD fork (deployedRuntime v) ee g s0 (schemaAfterCallPC site)
      ((if success then ⟨1⟩ else ⟨0⟩)::schemaCallSaved site ptr R) mem aw out σ k C) :
    if success then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨4883⟩
        (ptr::UInt256.ofNat out.size::⟨9829⟩::UInt256.ofNat out.size::ptr::schemaDecodeReturnPC site::schemaDecodeSaved site R)
        (out.write 0 mem ptr.toNat out.size) aw' out σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  have ho : (UInt256.ofNat out.size).toNat = out.size := ulit_toNat' _ (by change out.size < 2^256; omega)
  have hcopy : (UInt256.ofNat 0).toNat+(UInt256.ofNat out.size).toNat ≤ out.size := by rw [ho]; change 0+out.size ≤ out.size; omega
  cases site with
  | at7795 a b =>
    cases success with
    | false =>
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_7796_taken_packed (immWords := wordsOf (immStore v))
        (by first | omega | (simp only [schemaDecodeSaved,List.length_cons]; omega)) (by decide) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      exact easBlocks.eas_block_9844 (immWords := wordsOf (immStore v))
        (by simp only [easBlocks.eas_block_7796_taken_stack,List.length_cons]; omega) hcopy rd1
    | true =>
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_7796_fallthrough_packed (immWords := wordsOf (immStore v))
        (by first | omega | (simp only [schemaDecodeSaved,List.length_cons]; omega)) (by decide) rd
      obtain ⟨aw2,k2,C2,rd2⟩ := easBlocks.eas_block_7803_taken_packed (immWords := wordsOf (immStore v))
        (by first | omega | (simp only [schemaDecodeSaved,List.length_cons]; omega)) (by decide) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
      obtain ⟨aw3,k3,C3,rd3⟩ := easBlocks.eas_block_9807_packed (immWords := wordsOf (immStore v))
        (by first | omega | (simp only [schemaDecodeSaved,List.length_cons]; omega)) hcopy (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd2
      refine ⟨aw3,k3,C3,?_⟩
      simpa only [easBlocks.eas_block_9807_stack,easBlocks.eas_block_9807_memory,ho,
        show (UInt256.ofNat 0).toNat = 0 from rfl] using rd3
  | at10016 a b c d e =>
    cases success with
    | false =>
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_10017_taken_packed (immWords := wordsOf (immStore v))
        (by first | omega | (simp only [schemaDecodeSaved,List.length_cons]; omega)) (by decide) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      exact easBlocks.eas_block_9844 (immWords := wordsOf (immStore v))
        (by simp only [easBlocks.eas_block_10017_taken_stack,List.length_cons]; omega) hcopy rd1
    | true =>
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_10017_fallthrough_packed (immWords := wordsOf (immStore v))
        (by first | omega | (simp only [schemaDecodeSaved,List.length_cons]; omega)) (by decide) rd
      obtain ⟨aw2,k2,C2,rd2⟩ := easBlocks.eas_block_10024_taken_packed (immWords := wordsOf (immStore v))
        (by first | omega | (simp only [schemaDecodeSaved,List.length_cons]; omega)) (by decide) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
      obtain ⟨aw3,k3,C3,rd3⟩ := easBlocks.eas_block_11946_packed (immWords := wordsOf (immStore v))
        (by first | omega | (simp only [schemaDecodeSaved,List.length_cons]; omega)) hcopy (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd2
      refine ⟨aw3,k3,C3,?_⟩
      simpa only [easBlocks.eas_block_11946_stack,easBlocks.eas_block_11946_memory,ho,
        show (UInt256.ofNat 0).toNat = 0 from rfl] using rd3
  | at12196 =>
    cases success with
    | false =>
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_12197_taken_packed (immWords := wordsOf (immStore v))
        (by first | omega | (simp only [schemaDecodeSaved,List.length_cons]; omega)) (by decide) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      exact easBlocks.eas_block_9844 (immWords := wordsOf (immStore v))
        (by simp only [easBlocks.eas_block_12197_taken_stack,List.length_cons]; omega) hcopy rd1
    | true =>
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_12197_fallthrough_packed (immWords := wordsOf (immStore v))
        (by first | omega | (simp only [schemaDecodeSaved,List.length_cons]; omega)) (by decide) rd
      obtain ⟨aw2,k2,C2,rd2⟩ := easBlocks.eas_block_12204_taken_packed (immWords := wordsOf (immStore v))
        (by first | omega | (simp only [schemaDecodeSaved,List.length_cons]; omega)) (by decide) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
      obtain ⟨aw3,k3,C3,rd3⟩ := easBlocks.eas_block_12716_packed (immWords := wordsOf (immStore v))
        (by first | omega | (simp only [schemaDecodeSaved,List.length_cons]; omega)) hcopy (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd2
      refine ⟨aw3,k3,C3,?_⟩
      simpa only [easBlocks.eas_block_12716_stack,easBlocks.eas_block_12716_memory,ho,
        show (UInt256.ofNat 0).toNat = 0 from rfl] using rd3
  | at12855 =>
    cases success with
    | false =>
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_12856_taken_packed (immWords := wordsOf (immStore v))
        (by first | omega | (simp only [schemaDecodeSaved,List.length_cons]; omega)) (by decide) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      exact easBlocks.eas_block_9844 (immWords := wordsOf (immStore v))
        (by simp only [easBlocks.eas_block_12856_taken_stack,List.length_cons]; omega) hcopy rd1
    | true =>
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_12856_fallthrough_packed (immWords := wordsOf (immStore v))
        (by first | omega | (simp only [schemaDecodeSaved,List.length_cons]; omega)) (by decide) rd
      obtain ⟨aw2,k2,C2,rd2⟩ := easBlocks.eas_block_12863_taken_packed (immWords := wordsOf (immStore v))
        (by first | omega | (simp only [schemaDecodeSaved,List.length_cons]; omega)) (by decide) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
      obtain ⟨aw3,k3,C3,rd3⟩ := easBlocks.eas_block_13288_packed (immWords := wordsOf (immStore v))
        (by first | omega | (simp only [schemaDecodeSaved,List.length_cons]; omega)) hcopy (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd2
      refine ⟨aw3,k3,C3,?_⟩
      simpa only [easBlocks.eas_block_13288_stack,easBlocks.eas_block_13288_memory,ho,
        show (UInt256.ofNat 0).toNat = 0 from rfl] using rd3

theorem schemaCallResultFinish {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw record : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : EASImmutables) (site : SchemaCallSite) (hstack : R.length+10 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 (schemaDecodeReturnPC site)
      (record::schemaDecodeSaved site R) mem aw out σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (schemaDonePC site)
      (schemaDoneStack v site record R) mem aw' out σ k' C' := by
  cases site with
  | at7795 a b =>
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_9837_packed (immWords := wordsOf (immStore v))
      (by first | omega | (simp only [schemaDecodeSaved,List.length_cons]; omega)) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨aw1,k1,C1,rd1⟩
  | at10016 a b c d e =>
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_11968_packed (immWords := wordsOf (immStore v))
      (by first | omega | (simp only [schemaDecodeSaved,List.length_cons]; omega)) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨aw1,k1,C1,rd1⟩
  | at12196 =>
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_12737_packed (immWords := wordsOf (immStore v))
      (by first | omega | (simp only [schemaDecodeSaved,List.length_cons]; omega)) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨aw1,k1,C1,rd1⟩
  | at12855 =>
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_13309_packed (immWords := wordsOf (immStore v))
      (by first | omega | (simp only [schemaDecodeSaved,List.length_cons]; omega)) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨aw1,k1,C1,rd1⟩

end Benchmarks.EAS.EAS
