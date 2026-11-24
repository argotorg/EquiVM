import Benchmarks.EAS.EAS.BoolReturnAllocation
import Benchmarks.EAS.EAS.RuntimeBlocks_045
import Benchmarks.EAS.EAS.RuntimeBlocks_048
import Benchmarks.EAS.EAS.RuntimeBlocks_052

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

inductive PayableSite where
  | single | multiAttest | multiRevoke
  deriving DecidableEq

def payableCopyPC : PayableSite → UInt256
  | .single => ⟨16270⟩ | .multiAttest => ⟨14904⟩ | .multiRevoke => ⟨15519⟩
def payableLengthPC : PayableSite → UInt256
  | .single => ⟨16297⟩ | .multiAttest => ⟨14930⟩ | .multiRevoke => ⟨15544⟩
def payableDecodedPC : PayableSite → UInt256
  | .single => ⟨16314⟩ | .multiAttest => ⟨14947⟩ | .multiRevoke => ⟨15562⟩
def payableDonePC : PayableSite → UInt256
  | .single => ⟨16263⟩ | .multiAttest => ⟨14897⟩ | .multiRevoke => ⟨15512⟩

-- The revoke loop keeps one unused word until its bool decoder entry.
def payableCopyTail (site : PayableSite) (ptr junk : UInt256) (R : List UInt256) : List UInt256 :=
  match site with
  | .multiRevoke => junk::ptr::R
  | _ => ptr::R

theorem payableCopyTail_length (site : PayableSite) (ptr junk : UInt256) (R : List UInt256) :
    (payableCopyTail site ptr junk R).length ≤ R.length+2 := by
  cases site <;> simp only [payableCopyTail, List.length_cons] <;> omega

theorem payableAllocateEntry {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr junk : UInt256} {R : List UInt256} (v : EASImmutables) (site : PayableSite)
    (hstack : R.length+10 ≤ 1024) (hb : out.size < UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 (payableCopyPC site) (ptr::junk::R) mem aw out σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨4883⟩
      (ptr::UInt256.ofNat (min out.size 32)::payableLengthPC site::
        UInt256.ofNat (min out.size 32)::ptr::⟨32⟩::payableCopyTail site ptr junk R) mem aw' out σ k' C' := by
  have hn : (UInt256.ofNat out.size).toNat = out.size := ulit_toNat' _ hb
  by_cases hl : 32 ≤ out.size
  · have hc : UInt256.gt (UInt256.ofNat 32) (UInt256.ofNat out.size) = ⟨0⟩ := ugt_zero (by rw [hn]; exact hl)
    rw [Nat.min_eq_right hl]
    cases site with
    | single =>
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_16270_fallthrough_packed (immWords := wordsOf (immStore v)) (by omega) hc rd
      exact easBlocks.eas_block_16284_packed (immWords := wordsOf (immStore v))
        (by simp only [payableCopyTail, List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
    | multiAttest =>
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_14904_fallthrough_packed (immWords := wordsOf (immStore v)) (by omega) hc rd
      exact easBlocks.eas_block_14917_packed (immWords := wordsOf (immStore v))
        (by simp only [payableCopyTail, List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
    | multiRevoke =>
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_15519_fallthrough_packed (immWords := wordsOf (immStore v)) (by omega) hc rd
      exact easBlocks.eas_block_15531_packed (immWords := wordsOf (immStore v))
        (by simp only [payableCopyTail, List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
  · have hc : UInt256.gt (UInt256.ofNat 32) (UInt256.ofNat out.size) ≠ ⟨0⟩ := by
      rw [ugt_one (show (UInt256.ofNat out.size).toNat < (UInt256.ofNat 32).toNat by rw [hn]; change out.size < 32; omega)]
      decide
    rw [Nat.min_eq_left (by omega)]
    cases site with
    | single =>
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_16270_taken_packed (immWords := wordsOf (immStore v)) (by omega) hc
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      obtain ⟨aw2,k2,C2,rd2⟩ := easBlocks.eas_block_16320_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
      exact easBlocks.eas_block_16284_packed (immWords := wordsOf (immStore v))
        (by simp only [payableCopyTail, List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd2
    | multiAttest =>
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_14904_taken_packed (immWords := wordsOf (immStore v)) (by omega) hc
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      obtain ⟨aw2,k2,C2,rd2⟩ := easBlocks.eas_block_14957_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
      exact easBlocks.eas_block_14917_packed (immWords := wordsOf (immStore v))
        (by simp only [payableCopyTail, List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd2
    | multiRevoke =>
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_15519_taken_packed (immWords := wordsOf (immStore v)) (by omega) hc
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      obtain ⟨aw2,k2,C2,rd2⟩ := easBlocks.eas_block_15568_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
      exact easBlocks.eas_block_15531_packed (immWords := wordsOf (immStore v))
        (by simp only [payableCopyTail, List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd2

theorem payableDecodeEntry {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap}
    {k C len : Nat} {ptr junk : UInt256} {R : List UInt256} (v : EASImmutables) (site : PayableSite)
    (hstack : R.length+8 ≤ 1024) (hdepth : site = .multiAttest → 4 ≤ R.length) (hlen : len ≤ 32) (hbound : ptr.toNat+32 < UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 (payableLengthPC site)
      (UInt256.ofNat len::ptr::⟨32⟩::payableCopyTail site ptr junk R) mem aw out σ k C) :
    if 32 ≤ len then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨7319⟩ (ptr::payableDecodedPC site::R) mem aw' out σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  have hp : UInt256.ofNat ptr.toNat = ptr := u256_ofNat_toNat ptr
  by_cases hl : 32 ≤ len
  · rw [if_pos hl]
    have hc : UInt256.slt (UInt256.sub (ptr+UInt256.ofNat len) ptr) (UInt256.ofNat 32) = ⟨0⟩ := by
      simpa only [hp] using solcReturnStaticLenCheckOk (words := 1) (base := ptr.toNat) (len := len)
        hl (by omega) (by omega) (by omega)
    cases site with
    | single =>
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_16297_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [payableCopyTail, List.length_cons]; omega) hc rd
      exact easBlocks.eas_block_16306_packed (immWords := wordsOf (immStore v))
        (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
    | multiAttest =>
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_14930_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [payableCopyTail, List.length_cons]; omega) hc rd
      exact easBlocks.eas_block_14939_packed (immWords := wordsOf (immStore v))
        (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
    | multiRevoke =>
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_15544_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [payableCopyTail, List.length_cons]; omega) hc rd
      exact easBlocks.eas_block_15553_packed (immWords := wordsOf (immStore v))
        (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
  · rw [if_neg hl]
    have hc : UInt256.slt (UInt256.sub (ptr+UInt256.ofNat len) ptr) (UInt256.ofNat 32) ≠ ⟨0⟩ := by
      have he : UInt256.slt (UInt256.sub (ptr+UInt256.ofNat len) ptr) (UInt256.ofNat 32) = ⟨1⟩ := by
        simpa only [hp] using solcReturnStaticLenCheckShort (words := 1) (base := ptr.toNat) (len := len)
          (by omega) (by omega) (by omega) (by decide)
      rw [he]
      decide
    cases site with
    | single =>
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_16297_taken_packed (immWords := wordsOf (immStore v))
        (by simp only [payableCopyTail, List.length_cons]; omega) hc (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      exact easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
        (by simp only [easBlocks.eas_block_16297_taken_stack, payableCopyTail, List.length_cons]; omega) rd1
    | multiAttest =>
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_14930_taken_packed (immWords := wordsOf (immStore v))
        (by simp only [payableCopyTail, List.length_cons]; omega) hc (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      have hlower := hdepth rfl
      rcases R with _|⟨a,_|⟨b,_|⟨c,_|⟨d,S⟩⟩⟩⟩
      all_goals simp only [List.length_cons, List.length_nil] at hlower hstack
      all_goals try omega
      exact easBlocks.eas_block_14953 (immWords := wordsOf (immStore v)) (R := S)
        (by omega) rd1
    | multiRevoke =>
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_15544_taken_packed (immWords := wordsOf (immStore v))
        (by simp only [payableCopyTail, List.length_cons]; omega) hc (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      exact easBlocks.eas_block_6038 (immWords := wordsOf (immStore v))
        (by simp only [easBlocks.eas_block_15544_taken_stack, payableCopyTail, List.length_cons]; omega) rd1

theorem payableReturn_done {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap}
    {k C : Nat} {word : UInt256} {R : List UInt256} (v : EASImmutables) (site : PayableSite)
    (hstack : R.length+3 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 (payableDecodedPC site) (word::R) mem aw out σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (payableDonePC site)
      (UInt256.ofNat (deployedRuntime v).size::word::R) mem aw' out σ k' C' := by
  cases site with
  | single =>
    exact easBlocks.eas_block_16314_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  | multiAttest =>
    exact easBlocks.eas_block_14947_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  | multiRevoke =>
    exact easBlocks.eas_block_15562_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd

theorem payableCopyReturn {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr junk : UInt256} {R : List UInt256} (v : EASImmutables) (site : PayableSite)
    (hstack : R.length+10 ≤ 1024) (hb : out.size < UInt256.size)
    (hdepth : site = .multiAttest → 4 ≤ R.length)
    (hlo : 96 ≤ ptr.toNat) (hin : ptr.toNat+32 ≤ mem.size) (hbound : ptr.toNat+32 < UInt256.size)
    (hword : 32 ≤ out.size → memLoad ptr mem = calldataWord out 0)
    (rd : RD fork (deployedRuntime v) ee g s0 (payableCopyPC site) (ptr::junk::R) mem aw out σ k C) :
    if resolverCallValid ptr.toNat true out then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (payableDonePC site)
        (UInt256.ofNat (deployedRuntime v).size::calldataWord out 0::R)
        (resolverReturnMemory mem ptr out) aw' out σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  obtain ⟨aw1,k1,C1,rd1⟩ := payableAllocateEntry v site hstack hb rd
  have hd := boolReturnAtAllocation (R := R) v
    (by simp only [List.length_cons]; have := payableCopyTail_length site ptr junk R; omega) (by omega) hlo hin hword
    (by cases site <;> rw [easPatchedValidJumps v] <;> unfold payableLengthPC <;> jump_dest)
    (decodedPC := payableDecodedPC site)
    (by cases site <;> rw [easPatchedValidJumps v] <;> unfold payableDecodedPC <;> jump_dest)
    (fun hr => by
      have h := payableDecodeEntry v site (by omega) hdepth (Nat.min_le_right _ _) hbound hr
      have he : (32 ≤ min out.size 32) = (32 ≤ out.size) := by apply propext; omega
      simpa only [he] using h) rd1
  by_cases hv : resolverCallValid ptr.toNat true out
  · rw [if_pos hv] at hd ⊢
    obtain ⟨aw2,k2,C2,rd2⟩ := hd
    exact payableReturn_done v site (by omega) rd2
  · rw [if_neg hv] at hd ⊢
    exact hd

end Benchmarks.EAS.EAS
