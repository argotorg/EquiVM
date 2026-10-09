import Benchmarks.Auction.ErrorDecodeTail

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def ErrorDataValid (out : ByteArray) : Prop :=
  68 ≤ out.size ∧ ErrorOffsetValid out ∧ (errorLength out).toNat ≤ 2 ^ 64 - 1 ∧
    (errorOffset out).toNat + (errorLength out).toNat + 36 ≤ out.size

theorem errorAllocSize_eq {out : ByteArray}
    (ho : (errorOffset out).toNat ≤ 2 ^ 64 - 1)
    (hn : (errorLength out).toNat ≤ 2 ^ 64 - 1) :
    errorAllocSize out = UInt256.ofNat ((errorOffset out).toNat + (errorLength out).toNat + 32)
      := by
  have h1 : (errorOffset out + errorLength out).toNat =
      (errorOffset out).toNat + (errorLength out).toNat :=
    addWord_toNat _ _ (by change _ < 2 ^ 256; omega)
  apply u256_inj
  change (UInt256.add _ ⟨32⟩).toNat = _
  rw [addWord_toNat _ ⟨32⟩ (by rw [h1]; change _ + 32 < 2 ^ 256; omega), h1,
    ulit_toNat' _ (by change _ < 2 ^ 256; omega)]
  rfl

theorem errorAllocPtr_toNat {ptr : UInt256} {out : ByteArray} (hv : ErrorDataValid out)
    (hb : ptr.toNat + out.size + 64 ≤ 2 ^ 200) :
    (errorAllocPtr ptr (errorAllocSize out)).toNat =
      ptr.toNat + ((errorOffset out).toNat + (errorLength out).toNat + 63) / 32 * 32 := by
  rw [errorAllocPtr, errorAllocSize_eq hv.2.1.1 hv.2.2.1]
  change (returnReservePtr ptr ((errorOffset out).toNat + (errorLength out).toNat + 32)).toNat = _
  rw [returnReservePtr_toNat (by have he := hv.2.2.2; omega)]

theorem errorDecodeHeap {mem aw ptr out} (hm : HeapMemory mem aw ptr)
    (hin : ptr.toNat ≤ mem.size) (hv : ErrorDataValid out)
    (hb : ptr.toNat + out.size + 64 ≤ 2 ^ 200) :
    HeapMemory (writeWord (errorPayloadMem mem out ptr) 64 (errorAllocPtr ptr (errorAllocSize out)))
      (errorPayloadWords aw ptr out) (errorAllocPtr ptr (errorAllocSize out)) := by
  have hh := errorPayloadHeap hm hin hv.1 (by omega)
  have hs := errorPayload_size hm hin hv.1
  have hp := errorAllocPtr_toNat hv hb
  have he := hv.2.2.2
  refine ⟨?_, ?_, by have hl := hm.lower; omega, ?_, hh.active⟩
  · rw [writeWord_size _ _ _ (by have hsz := hh.size; have hu := lt_usize 0 (by decide); omega)]
    have hsz := hh.size
    omega
  · exact writeWord_read_back _ _ _
      (by have hsz := hh.size; have hu := lt_usize 0 (by decide); omega)
  · rw [writeWord_size _ _ _ (by have hsz := hh.size; have hu := lt_usize 0 (by decide); omega)]
    omega

theorem errorDecodedPtr_ne_zero {mem aw ptr out} (hm : HeapMemory mem aw ptr)
    (hv : ErrorDataValid out) (hb : ptr.toNat + out.size ≤ 2 ^ 200) :
    ptr + errorOffset out ≠ ⟨0⟩ := by
  have hoff := hv.2.1.2
  have hp : (ptr + errorOffset out).toNat = ptr.toNat + (errorOffset out).toNat :=
    addWord_toNat _ _ (by change _ < 2 ^ 256; omega)
  intro he
  have hz := congrArg UInt256.toNat he
  rw [hp] at hz
  have hlo := hm.lower
  change ptr.toNat + (errorOffset out).toNat = 0 at hz
  omega

end Auction
