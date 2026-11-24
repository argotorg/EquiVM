import Benchmarks.EAS.EAS.UIDHead
import Benchmarks.EAS.EAS.UIDMemory

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem uidLengthWord (len : Nat) (hl : len+153 < UInt256.size) :
    (UInt256.ofNat 153+UInt256.ofNat len)+
      UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639908 =
      UInt256.ofNat (125+len) := by
  apply u256_inj
  have hi : (UInt256.ofNat 153+UInt256.ofNat len).toNat = 153+len := by
    rw [uadd_toNat,ulit_toNat' 153 (by change 153 < 2^256; decide),ulit_toNat' len (by omega),Nat.mod_eq_of_lt (by omega)]
  rw [uadd_toNat,hi,
    ulit_toNat' _ (by change 115792089237316195423570985008687907853269984665640564039457584007913129639908 < 2^256; decide),
    ulit_toNat' _ (by omega)]
  have he : 153+len+115792089237316195423570985008687907853269984665640564039457584007913129639908 = UInt256.size+(125+len) := by
    change 153+len+115792089237316195423570985008687907853269984665640564039457584007913129639908 = 2^256+(125+len)
    omega
  rw [he,Nat.add_mod_left,Nat.mod_eq_of_lt (by omega)]

theorem uidAllocateWord (len : Nat) :
    UInt256.ofNat 4+(UInt256.ofNat 153+UInt256.ofNat len) = UInt256.ofNat (157+len) := by
  rw [← u256_add_assoc]
  change UInt256.ofNat 157+UInt256.ofNat len = UInt256.ofNat (157+len)
  apply u256_inj
  change (157%UInt256.size+len%UInt256.size)%UInt256.size = (157+len)%UInt256.size
  exact (Nat.add_mod 157 len UInt256.size).symm

theorem easUIDCopy {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {heap dataPtr : UInt256} {a : AttestationRecord} {R : List UInt256} (v : EASImmutables) (site : UIDSite)
    (hstack : R.length+10 ≤ 1024) (hh : heap.toNat ≤ 2^64-1) (hlen : a.data.size < 2^64)
    (rd : RD fork (deployedRuntime v) ee g s0 (UInt256.ofNat 4400)
      ((dataPtr+UInt256.ofNat 32)::(heap+UInt256.ofNat 153)::UInt256.ofNat a.data.size::uidCopyReturnPC site::
        UInt256.ofNat a.data.size::heap::R)
      (uidHeadMemory mem (heap.toNat+32) a) aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (uidCopyReturnPC site) (UInt256.ofNat a.data.size::heap::R)
      (uidCopyMemory mem heap dataPtr a) aw' rdata σ k' C' := by
  have hl : (UInt256.ofNat a.data.size).toNat = a.data.size := ulit_toNat' _ (by change a.data.size < 2^256; omega)
  have hd : (heap+UInt256.ofNat 153).toNat = heap.toNat+153 := uadd_word_ofNat_toNat heap 153 (by change heap.toNat+153 < 2^256; omega)
  obtain ⟨aw',k',C',rd'⟩ := easCopy v (by simp only [List.length_cons]; omega)
    (by rw [hl]; change a.data.size+31 < 2^256; omega)
    (by cases site <;> rw [easPatchedValidJumps v] <;> simp only [uidCopyReturnPC] <;> jump_dest) rd
  have he : (UInt256.ofNat a.data.size+(heap+UInt256.ofNat 153)).toNat = heap.toNat+153+a.data.size := by
    rw [u256_add_comm,uadd_word_ofNat_toNat _ _ (by rw [hd]; change heap.toNat+153+a.data.size < 2^256; omega),hd]
  refine ⟨aw',k',C',?_⟩
  simpa only [hl,he,uidCopyMemory] using rd'

theorem easUIDTail {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {heap dataPtr bump : UInt256} {a : AttestationRecord} {R : List UInt256} (v : EASImmutables) (site : UIDSite)
    (hstack : R.length+8 ≤ 1024) (hh : heap.toNat ≤ 2^64-1) (hlen : a.data.size < 2^64)
    (rd : RD fork (deployedRuntime v) ee g s0 (uidCopyReturnPC site)
      (UInt256.ofNat a.data.size::heap::heap::(heap+UInt256.ofNat 32)::bump::R)
      (uidCopyMemory mem heap dataPtr a) aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (UInt256.ofNat 4883)
      (heap::UInt256.ofNat (157+a.data.size)::uidHashPC site::heap::(heap+UInt256.ofNat 32)::bump::R)
      (uidMemory mem heap dataPtr a bump) aw' rdata σ k' C' := by
  have hl : a.data.size+153 < UInt256.size := by change a.data.size+153 < 2^256; omega
  have he : ((heap+UInt256.ofNat a.data.size)+UInt256.ofNat 153).toNat = heap.toNat+153+a.data.size := by
    rw [uadd_word_ofNat_toNat _ 153 (by rw [uadd_word_ofNat_toNat _ _ (by change heap.toNat+a.data.size < 2^256; omega)]; change heap.toNat+a.data.size+153 < 2^256; omega),
      uadd_word_ofNat_toNat _ _ (by change heap.toNat+a.data.size < 2^256; omega)]
    omega
  cases site with
  | single s1 s2 s3 s4 s5 s6 s7 s8 =>
    obtain ⟨aw',k',C',rd'⟩ := easBlocks.eas_block_8374_packed (immWords := wordsOf (immStore v)) hstack
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    refine ⟨aw',k',C',?_⟩
    simpa only [easBlocks.eas_block_8374_stack,easBlocks.eas_block_8374_memory,word_add_sub_left,
      uidLengthWord _ hl,uidAllocateWord,uidMask224,he,← writeWord_as_write,uidHashPC,uidMemory] using rd'
  | many s1 s2 s3 s4 s5 s6 =>
    obtain ⟨aw',k',C',rd'⟩ := easBlocks.eas_block_10590_packed (immWords := wordsOf (immStore v)) hstack
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    refine ⟨aw',k',C',?_⟩
    simpa only [easBlocks.eas_block_10590_stack,easBlocks.eas_block_10590_memory,word_add_sub_left,
      uidLengthWord _ hl,uidAllocateWord,uidMask224,he,← writeWord_as_write,uidHashPC,uidMemory] using rd'

end Benchmarks.EAS.EAS
