import Benchmarks.EAS.EAS.MemoryArrayIndex

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def resolveManyEntryPC (rev : Bool) : UInt256 := if rev then ⟨15058⟩ else ⟨14435⟩
def resolveManySinglePC (rev : Bool) : UInt256 := if rev then ⟨15622⟩ else ⟨15021⟩
def resolveManyLoadPC (rev : Bool) : UInt256 := if rev then ⟨15073⟩ else ⟨14452⟩
def resolveManyHeadStack (rev : Bool) (schema array values available last len : UInt256) (R : List UInt256) : List UInt256 :=
  if rev then schema::array::values::last::available::len::R else schema::array::⟨0⟩::values::last::available::len::R

theorem resolveManyStart {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C len : Nat}
    {schema array values available last : UInt256} {R : List UInt256} (v : EASImmutables) (rev : Bool)
    (hstack : R.length+9 ≤ 1024) (hlen : len < UInt256.size) (hl : memLoad array mem = UInt256.ofNat len)
    (rd : RD fork (deployedRuntime v) ee g s0 (resolveManyEntryPC rev)
      (schema::array::values::available::last::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (if len=1 then resolveManySinglePC rev else resolveManyLoadPC rev)
      (resolveManyHeadStack rev schema array values available last (UInt256.ofNat len) R) mem aw' rdata σ k' C' := by
  by_cases ho : len=1
  · subst len
    simp only [if_pos rfl]
    have hg : UInt256.eq (memLoad array mem) (UInt256.ofNat 1) ≠ ⟨0⟩ := by rw [hl,uInt256_eq_self]; decide
    cases rev with
    | false =>
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_14435_taken_packed (immWords := wordsOf (immStore v)) hstack hg
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      exact ⟨aw1,k1,C1,by simpa only [easBlocks.eas_block_14435_taken_stack,hl] using rd1⟩
    | true =>
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_15058_taken_packed (immWords := wordsOf (immStore v)) (by omega) hg
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      exact ⟨aw1,k1,C1,by simpa only [easBlocks.eas_block_15058_taken_stack,hl] using rd1⟩
  · rw [if_neg ho]
    have hg : UInt256.eq (memLoad array mem) (UInt256.ofNat 1) = ⟨0⟩ := by
      apply uInt256_eq_zero_of_ne
      intro he
      have ht := congrArg UInt256.toNat (uInt256_eq_one_eq he)
      rw [hl,ulit_toNat' _ hlen] at ht
      exact ho ht
    cases rev with
    | false =>
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_14435_fallthrough_packed (immWords := wordsOf (immStore v)) hstack hg rd
      exact ⟨aw1,k1,C1,by simpa only [easBlocks.eas_block_14435_fallthrough_stack,hl] using rd1⟩
    | true =>
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_15058_fallthrough_packed (immWords := wordsOf (immStore v)) (by omega) hg rd
      exact ⟨aw1,k1,C1,by simpa only [easBlocks.eas_block_15058_fallthrough_stack,hl] using rd1⟩

theorem resolveManySingleEntry {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {schema array values available last src word : UInt256} {R : List UInt256} (v : EASImmutables) (rev : Bool)
    (hstack : R.length+11 ≤ 1024) (hl : memLoad array mem = UInt256.ofNat 1)
    (hv : memLoad values mem = UInt256.ofNat 1)
    (hs : memLoad (UInt256.ofNat (array.toNat+32)) mem = src)
    (hw : memLoad (UInt256.ofNat (values.toNat+32)) mem = word)
    (rd : RD fork (deployedRuntime v) ee g s0 (resolveManySinglePC rev)
      (resolveManyHeadStack rev schema array values available last (UInt256.ofNat 1) R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨15724⟩
      (schema::src::word::rev.toUInt256::available::last::⟨4692⟩::R) mem aw' rdata σ k' C' := by
  have hfirst : ∃ aw1 k1 C1, RD fork (deployedRuntime v) ee g s0 ⟨5712⟩
      (array::⟨15044⟩::⟨15051⟩::values::schema::rev.toUInt256::available::last::⟨4692⟩::R) mem aw1 rdata σ k1 C1 := by
    cases rev with
    | false =>
      exact easBlocks.eas_block_15021_packed (immWords := wordsOf (immStore v)) (by omega)
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    | true =>
      exact easBlocks.eas_block_15622_packed (immWords := wordsOf (immStore v)) (by omega)
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨aw1,k1,C1,rd1⟩ := hfirst
  obtain ⟨aw2,k2,C2,rd2⟩ := easMemoryArrayFirst v
    (by simp only [List.length_cons]; omega) (by rw [hl]; decide)
    (by rw [easPatchedValidJumps]; jump_dest) rd1
  obtain ⟨aw3,k3,C3,rd3⟩ := easBlocks.eas_block_15044_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd2
  simp only [easBlocks.eas_block_15044_stack,hs] at rd3
  obtain ⟨aw4,k4,C4,rd4⟩ := easMemoryArrayFirst v
    (by simp only [List.length_cons]; omega) (by rw [hv]; decide)
    (by rw [easPatchedValidJumps]; jump_dest) rd3
  obtain ⟨aw5,k5,C5,rd5⟩ := easBlocks.eas_block_15051_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd4
  exact ⟨aw5,k5,C5,by simpa only [easBlocks.eas_block_15051_stack,hw] using rd5⟩

end Benchmarks.EAS.EAS
