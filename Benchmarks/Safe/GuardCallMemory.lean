import Benchmarks.Safe.Memory
import Benchmarks.Safe.GuardSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def guardCallMemory (kind : GuardKind) : ByteArray :=
  writeWord (writeWord solcFreePtrMem 128 (UInt256.shiftLeft ⟨33540519⟩ ⟨224⟩)) 132
    (guardInterfaceWord kind)

variable {kind : GuardKind}

theorem guardCallMemory_size : (guardCallMemory kind).size = 164 := by
  cases kind <;> native_decide

theorem guardCallMemory_freePtr : (guardCallMemory kind).readWithPadding 64 32 =
    (⟨128⟩ : UInt256).toByteArray := by
  cases kind <;> native_decide

theorem guardCallMemory_mload : memLoad ⟨64⟩ (guardCallMemory kind) = ⟨128⟩ :=
  memLoad_of_wordRead _ _ _ guardCallMemory_freePtr

theorem guardInterfaceEncoding : config.externalABI.encode? "supportsInterface"
    [guardInterfaceValue kind] = some ((guardCallMemory kind).readWithPadding 128 36) := by
  cases kind <;> native_decide

theorem guardCallInputSize : ((guardCallMemory kind).readWithPadding 128 36).size ≤
    Ethereum.EVM.maxReturnDataSizeByGas := by
  cases kind <;> native_decide

-- LIBRARY CANDIDATE: the length copied to a fixed one-word call-output buffer.
theorem callOutputLength {out : ByteArray} (hb : out.size < UInt256.size) :
    (min (UInt256.ofNat 32) (UInt256.ofNat out.size)).toNat = min 32 out.size := by
  change (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = _
  by_cases h : 32 ≤ out.size
  · rw [u256_min32_ofNat_toNat_of_ge32 out.size h hb, Nat.min_eq_left h]
  · rw [u256_min32_ofNat_toNat_of_lt32 out.size (by omega), Nat.min_eq_right (by omega)]

-- LIBRARY CANDIDATE: a bounded return copy above the free pointer preserves that pointer.
theorem callOutputFreePtrAt (mem out : ByteArray) (ptr : Nat)
    (hm : ptr ≤ mem.size) (hp : 96 ≤ ptr) :
    (out.write 0 mem ptr (min 32 out.size)).readWithPadding 64 32 =
      mem.readWithPadding 64 32 := by
  by_cases hz : min 32 out.size = 0
  · rw [hz, byteArray_write_zero_length]
  · exact write_read_below_gen_extend out mem ptr (min 32 out.size) 64 hz
      (Nat.min_le_right _ _) hm hp

theorem callOutputFreePtr (mem out : ByteArray) (hm : 128 ≤ mem.size) :
    (out.write 0 mem 128 (min 32 out.size)).readWithPadding 64 32 =
      mem.readWithPadding 64 32 :=
  callOutputFreePtrAt mem out 128 hm (by decide)

-- LIBRARY CANDIDATE: the first ABI word after a one-word call return copy.
theorem callOutputWordAt (mem out : ByteArray) (ptr : Nat)
    (hm : ptr ≤ mem.size) (hl : 32 ≤ out.size) :
    (out.write 0 mem ptr (min 32 out.size)).readWithPadding ptr 32 =
      (calldataWord out 0).toByteArray := by
  rw [Nat.min_eq_left hl, write32_read_back out mem ptr hl hm]
  exact (calldataWord_bytes hl).symm

theorem callOutputWord (mem out : ByteArray) (hm : 128 ≤ mem.size) (hl : 32 ≤ out.size) :
    (out.write 0 mem 128 (min 32 out.size)).readWithPadding 128 32 =
      (calldataWord out 0).toByteArray :=
  callOutputWordAt mem out 128 hm hl

def guardOutputMemory (kind : GuardKind) (out : ByteArray) : ByteArray :=
  out.write 0 (guardCallMemory kind) 128 (min 32 out.size)

theorem guardOutputMemory_lower (out : ByteArray) : 164 ≤ (guardOutputMemory kind out).size := by
  rw [← guardCallMemory_size]
  exact byteArray_write_size_ge_base _ _ _ _ _

theorem guardOutputMemory_freePtr (out : ByteArray) :
    memLoad ⟨64⟩ (guardOutputMemory kind out) = ⟨128⟩ := by
  apply memLoad_of_wordRead
  exact (callOutputFreePtr (guardCallMemory kind) out (by rw [guardCallMemory_size]; decide)).trans
    guardCallMemory_freePtr

theorem guardOutputMemory_word (out : ByteArray) (hl : 32 ≤ out.size) :
    (guardOutputMemory kind out).readWithPadding 128 32 = (calldataWord out 0).toByteArray :=
  callOutputWord (guardCallMemory kind) out (by rw [guardCallMemory_size]; decide) hl

def guardDecodedMemory (kind : GuardKind) (out : ByteArray) : ByteArray :=
  writeWord (guardOutputMemory kind out) 64
    (⟨128⟩ + UInt256.land (UInt256.ofNat out.size + UInt256.ofNat 31)
      (UInt256.lnot (UInt256.ofNat 31)))

theorem guardDecodedMemory_word (out : ByteArray) (hl : 32 ≤ out.size) :
    memLoad ⟨128⟩ (guardDecodedMemory kind out) = calldataWord out 0 := by
  apply memLoad_of_wordRead
  change (writeWord _ 64 _).readWithPadding 128 32 = _
  rw [writeWord_sparse_read_preserved _ 64 128 _
    (.inr ⟨by decide, by have := guardOutputMemory_lower (kind := kind) out; omega⟩)]
  exact guardOutputMemory_word out hl

end Benchmarks.Safe
