import Benchmarks.Midnight.BytesCalldataDecoder
import Benchmarks.Midnight.MemoryByteString

/-! The heap facts produced by materialized calldata bytes decoding. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem returnDataAllocation_eq (len : Nat) : returnDataAllocation len = 32 + paddedSize len := by
  unfold returnDataAllocation paddedSize
  omega

theorem bytesCalldataMemory_prefix {mem bytes data : ByteArray} {ptr : UInt256} {head : Nat}
    (hd : decodeBytesAt bytes head = some data) :
    MemoryPrefix mem (bytesCalldataMemory mem bytes ptr head) ptr.toNat := by
  have hs := (decodeBytesAt_success hd).2.2.2.1
  exact (memoryPrefix_writeWord mem 64 ptr.toNat _ (Or.inr (by decide))).trans
    (calldataBytesEncodeMemory_prefix _ _ _ _ _ _ hs le_rfl)

theorem bytesCalldataMemory_free {mem bytes data : ByteArray} {ptr : UInt256} {head : Nat}
    (hd : decodeBytesAt bytes head = some data) (hlo : 96 ≤ ptr.toNat) :
    memLoad (UInt256.ofNat 64) (bytesCalldataMemory mem bytes ptr head) =
      returnDataPtr ptr data.size := by
  have hv := decodeBytesAt_success hd
  rw [bytesCalldataMemory, calldataBytesEncodeMemory_load_before _ _ _ _ _ _ hv.2.2.2.1
      (by rw [writeWord_sparse_size]; change 64 + 32 ≤ _; omega) hlo, hv.2.2.2.2.2]
  exact memLoad_writeWord mem (UInt256.ofNat 64) _

theorem bytesCalldataMemory_size {mem bytes data : ByteArray} {ptr : UInt256} {head : Nat}
    (hd : decodeBytesAt bytes head = some data) :
    ptr.toNat + returnDataAllocation data.size ≤ (bytesCalldataMemory mem bytes ptr head).size := by
  have hv := decodeBytesAt_success hd
  rw [bytesCalldataMemory, calldataBytesEncodeMemory_size _ _ _ _ _ hv.2.2.2.1,
    hv.2.2.2.2.2]
  unfold returnDataAllocation
  omega

theorem bytesCalldataMemory_stored {mem bytes data : ByteArray} {ptr : UInt256} {head : Nat}
    (hd : decodeBytesAt bytes head = some data) (hlo : 96 ≤ ptr.toNat)
    (hfit : ptr.toNat + returnDataAllocation data.size < 2^64) :
    MemoryByteString (bytesCalldataMemory mem bytes ptr head) ptr data := by
  have hv := decodeBytesAt_success hd
  rw [hv.2.2.2.2.1]
  apply calldataBytesEncodeMemory_stored _ _ hlo hv.2.2.1 _ hv.2.2.2.1
  rw [hv.2.2.2.2.2, returnDataAllocation_eq] at hfit
  change _ < 2^256
  omega

theorem bytesCalldataMemory_low {mem bytes data : ByteArray} {ptr : UInt256}
    {head base : Nat} {words : List UInt256}
    (hd : decodeBytesAt bytes head = some data)
    (hw : MemoryWords mem base words) (hlo : 96 ≤ base)
    (hbelow : base + 32 * words.length ≤ ptr.toNat) :
    MemoryWords (bytesCalldataMemory mem bytes ptr head) base words := by
  have hp := bytesCalldataMemory_prefix (mem := mem) (ptr := ptr) hd
  apply hw.preserve hp.size
  intro read hrlo hrhi
  exact hp.load read (by omega) (by omega) (hrhi.trans hw.size)

theorem returnDataPtr_toNat {ptr : UInt256} {size : Nat}
    (hfit : ptr.toNat + returnDataAllocation size < 2^64) :
    (returnDataPtr ptr size).toNat = ptr.toNat + returnDataAllocation size :=
  uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)

theorem returnDataPtr_aligned {ptr : UInt256} {size : Nat}
    (halign : ptr.toNat % 32 = 0) (hfit : ptr.toNat + returnDataAllocation size < 2^64) :
    (returnDataPtr ptr size).toNat % 32 = 0 := by
  rw [returnDataPtr_toNat hfit]
  unfold returnDataAllocation
  omega

end Benchmarks.Midnight
