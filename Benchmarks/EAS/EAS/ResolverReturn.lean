import Benchmarks.EAS.EAS.BoolReturnAllocation

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def resolverAfterCallPC (many rev : Bool) : UInt256 := if many then (if rev then ⟨15188⟩ else ⟨14567⟩) else (if rev then ⟨15862⟩ else ⟨16073⟩)
def resolverCopyPC (many rev : Bool) : UInt256 := if many then (if rev then ⟨15258⟩ else ⟨14646⟩) else (if rev then ⟨15946⟩ else ⟨16142⟩)
def resolverLengthPC (many rev : Bool) : UInt256 := if many then (if rev then ⟨15285⟩ else ⟨14673⟩) else (if rev then ⟨15973⟩ else ⟨16169⟩)
def resolverBoolPC (many rev : Bool) : UInt256 := if many then (if rev then ⟨15294⟩ else ⟨14682⟩) else (if rev then ⟨15982⟩ else ⟨16178⟩)
def resolverDecodedPC (many rev : Bool) : UInt256 := if many then (if rev then ⟨15302⟩ else ⟨14690⟩) else (if rev then ⟨15990⟩ else ⟨16186⟩)
def resolverDonePC (many rev : Bool) : UInt256 := if many then (if rev then ⟨15202⟩ else ⟨14581⟩) else (if rev then ⟨15876⟩ else ⟨16087⟩)

theorem resolverReturn_success {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr : UInt256} {R : List UInt256} (v : EASImmutables) (many rev : Bool)
    (hstack : R.length+6 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 (resolverAfterCallPC many rev) (⟨1⟩::ptr::R) mem aw out σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (resolverCopyPC many rev) (ptr::⟨0⟩::R) mem aw' out σ k' C' := by
  cases many with
  | false =>
    cases rev with
    | false =>
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_16073_fallthrough_packed (immWords := wordsOf (immStore v)) (by omega) (by decide) rd
      exact easBlocks.eas_block_16080_taken_packed (immWords := wordsOf (immStore v)) (by omega) (by decide)
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
    | true =>
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_15862_fallthrough_packed (immWords := wordsOf (immStore v)) (by omega) (by decide) rd
      exact easBlocks.eas_block_15869_taken_packed (immWords := wordsOf (immStore v)) (by omega) (by decide)
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
  | true =>
    cases rev with
    | false =>
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_14567_fallthrough_packed (immWords := wordsOf (immStore v)) (by omega) (by decide) rd
      exact easBlocks.eas_block_14574_taken_packed (immWords := wordsOf (immStore v)) (by omega) (by decide)
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
    | true =>
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_15188_fallthrough_packed (immWords := wordsOf (immStore v)) (by omega) (by decide) rd
      exact easBlocks.eas_block_15195_taken_packed (immWords := wordsOf (immStore v)) (by omega) (by decide)
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
theorem resolverReturn_failure {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr : UInt256} {R : List UInt256} (v : EASImmutables) (many rev : Bool)
    (hstack : R.length+6 ≤ 1024) (hb : out.size < UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 (resolverAfterCallPC many rev) (⟨0⟩::ptr::R) mem aw out σ k C) :
    RDrev fork (deployedRuntime v) g s0 := by
  have hr : ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨9844⟩ (ptr::⟨0⟩::R) mem aw' out σ k' C' := by
    cases many with
    | false =>
      cases rev with
      | false =>
        exact easBlocks.eas_block_16073_taken_packed (immWords := wordsOf (immStore v)) (by omega) (by decide)
          (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      | true =>
        exact easBlocks.eas_block_15862_taken_packed (immWords := wordsOf (immStore v)) (by omega) (by decide)
          (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    | true =>
      cases rev with
      | false =>
        exact easBlocks.eas_block_14567_taken_packed (immWords := wordsOf (immStore v)) (by omega) (by decide)
          (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      | true =>
        exact easBlocks.eas_block_15188_taken_packed (immWords := wordsOf (immStore v)) (by omega) (by decide)
          (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨aw1,k1,C1,rd1⟩ := hr
  exact easBlocks.eas_block_9844 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [ulit_toNat' _ hb]; change 0+out.size ≤ out.size; omega) rd1

theorem resolverReturn_allocateEntry {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr : UInt256} {R : List UInt256} (v : EASImmutables) (many rev : Bool)
    (hstack : R.length+9 ≤ 1024) (hb : out.size < UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 (resolverCopyPC many rev) (ptr::⟨0⟩::R) mem aw out σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨4883⟩
      (ptr::UInt256.ofNat (min out.size 32)::resolverLengthPC many rev::
        UInt256.ofNat (min out.size 32)::ptr::⟨32⟩::ptr::R) mem aw' out σ k' C' := by
  have hn : (UInt256.ofNat out.size).toNat = out.size := ulit_toNat' _ hb
  by_cases hl : 32 ≤ out.size
  · have hc : UInt256.gt (UInt256.ofNat 32) (UInt256.ofNat out.size) = ⟨0⟩ := ugt_zero (by rw [hn]; exact hl)
    rw [Nat.min_eq_right hl]
    cases many with
    | false =>
      cases rev with
      | false =>
        obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_16142_fallthrough_packed (immWords := wordsOf (immStore v)) (by omega) hc rd
        exact easBlocks.eas_block_16156_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
      | true =>
        obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_15946_fallthrough_packed (immWords := wordsOf (immStore v)) (by omega) hc rd
        exact easBlocks.eas_block_15960_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
    | true =>
      cases rev with
      | false =>
        obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_14646_fallthrough_packed (immWords := wordsOf (immStore v)) (by omega) hc rd
        exact easBlocks.eas_block_14660_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
      | true =>
        obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_15258_fallthrough_packed (immWords := wordsOf (immStore v)) (by omega) hc rd
        exact easBlocks.eas_block_15272_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
  · have hc : UInt256.gt (UInt256.ofNat 32) (UInt256.ofNat out.size) ≠ ⟨0⟩ := by
      rw [ugt_one (show (UInt256.ofNat out.size).toNat < (UInt256.ofNat 32).toNat by rw [hn]; change out.size < 32; omega)]
      decide
    rw [Nat.min_eq_left (by omega)]
    cases many with
    | false =>
      cases rev with
      | false =>
        obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_16142_taken_packed (immWords := wordsOf (immStore v)) (by omega) hc
          (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
        obtain ⟨aw2,k2,C2,rd2⟩ := easBlocks.eas_block_16192_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
        exact easBlocks.eas_block_16156_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd2
      | true =>
        obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_15946_taken_packed (immWords := wordsOf (immStore v)) (by omega) hc
          (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
        obtain ⟨aw2,k2,C2,rd2⟩ := easBlocks.eas_block_15996_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
        exact easBlocks.eas_block_15960_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd2
    | true =>
      cases rev with
      | false =>
        obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_14646_taken_packed (immWords := wordsOf (immStore v)) (by omega) hc
          (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
        obtain ⟨aw2,k2,C2,rd2⟩ := easBlocks.eas_block_14696_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
        exact easBlocks.eas_block_14660_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd2
      | true =>
        obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_15258_taken_packed (immWords := wordsOf (immStore v)) (by omega) hc
          (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
        obtain ⟨aw2,k2,C2,rd2⟩ := easBlocks.eas_block_15308_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
        exact easBlocks.eas_block_15272_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd2
theorem resolverReturn_decodeEntry {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap}
    {k C len : Nat} {ptr : UInt256} {R : List UInt256} (v : EASImmutables) (many rev : Bool)
    (hstack : R.length+8 ≤ 1024) (hlen : len ≤ 32) (hbound : ptr.toNat+32 < UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 (resolverLengthPC many rev)
      (UInt256.ofNat len::ptr::⟨32⟩::ptr::R) mem aw out σ k C) :
    if 32 ≤ len then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨7319⟩
        (ptr::resolverDecodedPC many rev::R) mem aw' out σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  have hp : UInt256.ofNat ptr.toNat = ptr := u256_ofNat_toNat ptr
  by_cases hl : 32 ≤ len
  · rw [if_pos hl]
    have hc : UInt256.slt (UInt256.sub (ptr+UInt256.ofNat len) ptr) (UInt256.ofNat 32) = ⟨0⟩ := by
      simpa only [hp] using solcReturnStaticLenCheckOk (words := 1) (base := ptr.toNat) (len := len)
        hl (by omega) (by omega) (by omega)
    cases many with
    | false =>
      cases rev with
      | false =>
        obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_16169_fallthrough_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) hc rd
        exact easBlocks.eas_block_16178_packed (immWords := wordsOf (immStore v))
          (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
      | true =>
        obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_15973_fallthrough_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) hc rd
        exact easBlocks.eas_block_15982_packed (immWords := wordsOf (immStore v))
          (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
    | true =>
      cases rev with
      | false =>
        obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_14673_fallthrough_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) hc rd
        exact easBlocks.eas_block_14682_packed (immWords := wordsOf (immStore v))
          (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
      | true =>
        obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_15285_fallthrough_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) hc rd
        exact easBlocks.eas_block_15294_packed (immWords := wordsOf (immStore v))
          (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
  · rw [if_neg hl]
    have hc : UInt256.slt (UInt256.sub (ptr+UInt256.ofNat len) ptr) (UInt256.ofNat 32) ≠ ⟨0⟩ := by
      have he : UInt256.slt (UInt256.sub (ptr+UInt256.ofNat len) ptr) (UInt256.ofNat 32) = ⟨1⟩ := by
        simpa only [hp] using solcReturnStaticLenCheckShort (words := 1) (base := ptr.toNat) (len := len)
          (by omega) (by omega) (by omega) (by decide)
      rw [he]
      decide
    have hr : ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨402⟩ (ptr::R) mem aw' out σ k' C' := by
      cases many with
      | false =>
        cases rev with
        | false =>
          exact easBlocks.eas_block_16169_taken_packed (immWords := wordsOf (immStore v))
            (by simp only [List.length_cons]; omega) hc (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
        | true =>
          exact easBlocks.eas_block_15973_taken_packed (immWords := wordsOf (immStore v))
            (by simp only [List.length_cons]; omega) hc (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      | true =>
        cases rev with
        | false =>
          exact easBlocks.eas_block_14673_taken_packed (immWords := wordsOf (immStore v))
            (by simp only [List.length_cons]; omega) hc (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
        | true =>
          exact easBlocks.eas_block_15285_taken_packed (immWords := wordsOf (immStore v))
            (by simp only [List.length_cons]; omega) hc (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    obtain ⟨aw1,k1,C1,rd1⟩ := hr
    exact easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) rd1

theorem resolverReturn_done {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap}
    {k C : Nat} {word : UInt256} {R : List UInt256} (v : EASImmutables) (many rev : Bool)
    (hstack : R.length+3 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 (resolverDecodedPC many rev) (word::R) mem aw out σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (resolverDonePC many rev)
      (UInt256.ofNat (deployedRuntime v).size::word::R) mem aw' out σ k' C' := by
  cases many with
  | false =>
    cases rev with
    | false =>
      exact easBlocks.eas_block_16186_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    | true =>
      exact easBlocks.eas_block_15990_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  | true =>
    cases rev with
    | false =>
      exact easBlocks.eas_block_14690_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    | true =>
      exact easBlocks.eas_block_15302_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
theorem resolverReturn {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr : UInt256} {R : List UInt256} (v : EASImmutables) (many rev success : Bool)
    (hstack : R.length+9 ≤ 1024) (hb : out.size < UInt256.size)
    (hlo : 96 ≤ ptr.toNat) (hin : ptr.toNat+32 ≤ mem.size) (hbound : ptr.toNat+32 < UInt256.size)
    (hword : 32 ≤ out.size → memLoad ptr mem = calldataWord out 0)
    (rd : RD fork (deployedRuntime v) ee g s0 (resolverAfterCallPC many rev)
      ((if success then ⟨1⟩ else ⟨0⟩)::ptr::R) mem aw out σ k C) :
    if resolverCallValid ptr.toNat success out then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (resolverDonePC many rev)
        (UInt256.ofNat (deployedRuntime v).size::calldataWord out 0::R)
        (resolverReturnMemory mem ptr out) aw' out σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  cases success with
  | false =>
    have hf : ¬ resolverCallValid ptr.toNat false out := by intro h; cases h.1
    rw [if_neg hf]
    exact resolverReturn_failure v many rev (by omega) hb rd
  | true =>
    obtain ⟨aw1,k1,C1,rd1⟩ := resolverReturn_success v many rev (by omega) rd
    obtain ⟨aw2,k2,C2,rd2⟩ := resolverReturn_allocateEntry v many rev hstack hb rd1
    have hd := boolReturnAtAllocation (R := R) v (by simp only [List.length_cons]; omega) (by omega) hlo hin hword
      (by cases many <;> cases rev <;> rw [easPatchedValidJumps v] <;> unfold resolverLengthPC <;> jump_dest)
      (decodedPC := resolverDecodedPC many rev)
      (by cases many <;> cases rev <;> rw [easPatchedValidJumps v] <;> unfold resolverDecodedPC <;> jump_dest)
      (fun hr => by
        have h := resolverReturn_decodeEntry v many rev (by omega) (Nat.min_le_right _ _) hbound hr
        have he : (32 ≤ min out.size 32) = (32 ≤ out.size) := by apply propext; omega
        simpa only [he] using h) rd2
    by_cases hv : resolverCallValid ptr.toNat true out
    · rw [if_pos hv] at hd ⊢
      obtain ⟨aw3,k3,C3,rd3⟩ := hd
      exact resolverReturn_done v many rev (by omega) rd3
    · rw [if_neg hv] at hd ⊢
      exact hd


abbrev resolverOneAfterCallPC (rev : Bool) : UInt256 := resolverAfterCallPC false rev
abbrev resolverOneCopyPC (rev : Bool) : UInt256 := resolverCopyPC false rev
abbrev resolverOneLengthPC (rev : Bool) : UInt256 := resolverLengthPC false rev
abbrev resolverOneBoolPC (rev : Bool) : UInt256 := resolverBoolPC false rev
abbrev resolverOneDecodedPC (rev : Bool) : UInt256 := resolverDecodedPC false rev
abbrev resolverOneDonePC (rev : Bool) : UInt256 := resolverDonePC false rev

theorem resolverOneReturn {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr : UInt256} {R : List UInt256} (v : EASImmutables) (rev success : Bool)
    (hstack : R.length+9 ≤ 1024) (hb : out.size < UInt256.size)
    (hlo : 96 ≤ ptr.toNat) (hin : ptr.toNat+32 ≤ mem.size) (hbound : ptr.toNat+32 < UInt256.size)
    (hword : 32 ≤ out.size → memLoad ptr mem = calldataWord out 0)
    (rd : RD fork (deployedRuntime v) ee g s0 (resolverOneAfterCallPC rev)
      ((if success then ⟨1⟩ else ⟨0⟩)::ptr::R) mem aw out σ k C) :
    if resolverCallValid ptr.toNat success out then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (resolverOneDonePC rev)
        (UInt256.ofNat (deployedRuntime v).size::calldataWord out 0::R)
        (resolverReturnMemory mem ptr out) aw' out σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  exact resolverReturn v false rev success hstack hb hlo hin hbound hword rd

end Benchmarks.EAS.EAS
