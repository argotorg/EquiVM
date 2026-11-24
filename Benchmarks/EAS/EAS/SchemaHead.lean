import Benchmarks.EAS.EAS.SchemaABI
import Benchmarks.EAS.EAS.RuntimeBlocks_028

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: the EVM form of the bounded signed extent check.
theorem sltSubSmall_ofNat {size start need : Nat}
    (hs : size < 2^255) (hp : start < 2^255) (hn : need < 2^255) :
    UInt256.slt (UInt256.sub (UInt256.ofNat size) (UInt256.ofNat start)) (UInt256.ofNat need) =
      UInt256.fromBool (decide (size < start+need)) := by
  change UInt256.fromBool (UInt256.sltBool _ _) = _
  rw [sltBool_signed]
  apply congrArg UInt256.fromBool
  have h := solcSLT_sub_small hs hp hn
  change decide (EVM.signed (UInt256.ofNat (UInt256.sub (UInt256.ofNat size) (UInt256.ofNat start)).toNat) <
    EVM.signed (UInt256.ofNat need)) = _ at h
  simpa only [u256_ofNat_toNat] using h

theorem easSchemaHead {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {ptr ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+8 ≤ 1024) (hptr : ptr.toNat ≤ 2^64-1) (hout : out.size < 2^138)
    (hword : 32 ≤ out.size → memLoad ptr mem = calldataWord out 0)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨7332⟩
      (ptr::(ptr+UInt256.ofNat out.size)::ret::R) mem aw out σ k C) :
    if 32 ≤ out.size ∧ schemaReturnOffset out ≤ solcMaxU64 ∧ schemaReturnOffset out+128 ≤ out.size then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨7373⟩
        ((ptr+UInt256.ofNat out.size)::(ptr+UInt256.ofNat (schemaReturnOffset out))::ret::R) mem aw' out σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  have hb : ptr.toNat+out.size < UInt256.size := by change ptr.toNat+out.size < 2^256; omega
  have hp : UInt256.ofNat ptr.toNat = ptr := u256_ofNat_toNat ptr
  have hlen : UInt256.sub (ptr+UInt256.ofNat out.size) ptr = UInt256.ofNat out.size := word_add_sub_left _ _
  by_cases hh : 32 ≤ out.size
  · have hc : UInt256.slt (UInt256.sub (ptr+UInt256.ofNat out.size) ptr) (UInt256.ofNat 32) = ⟨0⟩ := by
      simpa only [hp] using solcReturnStaticLenCheckOk (base := ptr.toNat) (len := out.size) (words := 1)
        hh (by omega) (by omega) hb
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_7332_fallthrough_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hc rd
    have hw := hword hh
    by_cases ho : schemaReturnOffset out ≤ solcMaxU64
    · have hc0 : UInt256.gt (memLoad ptr mem) (UInt256.ofNat 18446744073709551615) = ⟨0⟩ := by
        rw [hw]
        exact ugt_zero ho
      obtain ⟨aw2,k2,C2,rd2⟩ := easBlocks.eas_block_7343_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hc0 rd1
      simp only [easBlocks.eas_block_7343_fallthrough_stack, hw] at rd2
      have ha : ptr+UInt256.ofNat out.size = UInt256.ofNat (ptr.toNat+out.size) := by
        apply u256_inj
        rw [uadd_word_ofNat_toNat ptr out.size hb, ulit_toNat' _ hb]
      have hoff : UInt256.ofNat (schemaReturnOffset out) = calldataWord out 0 := u256_ofNat_toNat _
      have hd : ptr+calldataWord out 0 = UInt256.ofNat (ptr.toNat+schemaReturnOffset out) := by
        rw [← hoff]
        have hbound : ptr.toNat+schemaReturnOffset out < UInt256.size := by
          change ptr.toNat+schemaReturnOffset out < 2^256
          change schemaReturnOffset out ≤ 18446744073709551615 at ho
          omega
        apply u256_inj
        rw [uadd_word_ofNat_toNat ptr (schemaReturnOffset out) hbound, ulit_toNat' _ hbound]
      have hc1 := sltSubSmall_ofNat (size := ptr.toNat+out.size) (start := ptr.toNat+schemaReturnOffset out)
        (need := 128) (by omega) (by change schemaReturnOffset out ≤ 18446744073709551615 at ho; omega) (by decide)
      rw [← ha, ← hd] at hc1
      by_cases hf : schemaReturnOffset out+128 ≤ out.size
      · rw [decide_eq_false (by omega : ¬ ptr.toNat+out.size < ptr.toNat+schemaReturnOffset out+128)] at hc1
        obtain ⟨aw3,k3,C3,rd3⟩ := easBlocks.eas_block_7361_fallthrough_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) hc1 rd2
        rw [if_pos ⟨hh,ho,hf⟩]
        exact ⟨aw3,k3,C3,by simpa only [easBlocks.eas_block_7361_fallthrough_stack,hoff] using rd3⟩
      · rw [decide_eq_true (by omega : ptr.toNat+out.size < ptr.toNat+schemaReturnOffset out+128)] at hc1
        obtain ⟨aw3,k3,C3,rd3⟩ := easBlocks.eas_block_7361_taken_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) (by rw [hc1]; decide)
          (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd2
        rw [if_neg (by intro h; exact hf h.2.2)]
        exact easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
          (by simp only [easBlocks.eas_block_7361_taken_stack,List.length_cons]; omega) rd3
    · have hc0 : UInt256.gt (memLoad ptr mem) (UInt256.ofNat 18446744073709551615) ≠ ⟨0⟩ := by
        rw [hw, ugt_one (by change 18446744073709551615 < (calldataWord out 0).toNat; change ¬ schemaReturnOffset out ≤ 18446744073709551615 at ho; unfold schemaReturnOffset at ho; omega)]
        decide
      obtain ⟨aw2,k2,C2,rd2⟩ := easBlocks.eas_block_7343_taken_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hc0 (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
      rw [if_neg (by intro h; exact ho h.2.1)]
      exact easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
        (by simp only [easBlocks.eas_block_7343_taken_stack,List.length_cons]; omega) rd2
  · have hc : UInt256.slt (UInt256.sub (ptr+UInt256.ofNat out.size) ptr) (UInt256.ofNat 32) = ⟨1⟩ := by
      simpa only [hp] using solcReturnStaticLenCheckShort (base := ptr.toNat) (len := out.size) (words := 1)
        (by omega) (by omega) hb (by decide)
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_7332_taken_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [hc]; decide)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    rw [if_neg (by intro h; exact hh h.1)]
    exact easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) rd1

end Benchmarks.EAS.EAS
