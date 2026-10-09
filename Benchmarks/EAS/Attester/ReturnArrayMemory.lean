import Benchmarks.EAS.Attester.Common
import Benchmarks.EAS.Attester.UnboundedMemory
import Reasoning.HeapMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

def returnArrayFree (base : Nat) (out : ByteArray) : Nat :=
  base + (out.size + 31) / 32 * 32

def returnArrayInputMemory (mem : ByteArray) (base : Nat) (out : ByteArray) : ByteArray :=
  writeWord (out.write 0 mem base out.size) 64 (UInt256.ofNat (returnArrayFree base out))

theorem returnCopy_size {mem out : ByteArray} {base : Nat} (hb : base ≤ mem.size) :
    (out.write 0 mem base out.size).size = max mem.size (base + out.size) := by
  by_cases hz : out.size = 0
  · rw [hz, byteArray_write_len_zero]; omega
  exact copyWindow_size out mem 0 base out.size hz (by omega) hb

theorem returnArrayInputMemory_size {mem out : ByteArray} {base : Nat}
    (hlo : 96 ≤ base) (hb : base ≤ mem.size) :
    (returnArrayInputMemory mem base out).size = max mem.size (base + out.size) := by
  rw [returnArrayInputMemory, writeWord_sparse_size, returnCopy_size hb]
  omega

theorem returnArrayInputMemory_freePtr (mem out : ByteArray) (base : Nat) :
    memLoad (UInt256.ofNat 64) (returnArrayInputMemory mem base out) =
      UInt256.ofNat (returnArrayFree base out) := memLoad_write_same _ _ _ _ rfl

theorem returnArrayFree_bounds (base : Nat) (out : ByteArray) :
    base + out.size ≤ returnArrayFree base out ∧ returnArrayFree base out ≤ base + out.size + 31 :=
        by
  unfold returnArrayFree
  omega

theorem returnArrayInputMemory_load {mem out : ByteArray} {base off : Nat}
    (hlo : 96 ≤ base) (hb : base ≤ mem.size) (hin : off + 32 ≤ out.size)
    (hfit : base + off < UInt256.size) :
    memLoad (UInt256.ofNat (base + off)) (returnArrayInputMemory mem base out) =
      calldataWord out off := by
  rw [returnArrayInputMemory, Reasoning.Theory.writeWord, memLoad_write_disjoint _ _ _ _
    (by rw [returnCopy_size hb, ulit_toNat' _ hfit]; omega)
    (.inr (by rw [ulit_toNat' _ hfit]; omega))]
  apply mloadWordValue_of_readWithPadding
  · rw [ulit_toNat' _ hfit, returnCopy_size hb]; omega
  · rw [ulit_toNat' _ hfit, copyWindow_read_word out mem 0 base out.size off
      (by omega) (by omega) hb hin, Nat.zero_add,
      readWithPadding_eq_extract out off hin, calldataWord_bytes_at hin]

theorem returnArrayInputMemory_summary {mem out : ByteArray} {base : Nat}
    (hfp : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat base)
    (hbound : base + out.size + 31 ≤ 2 ^ 200) :
    attesterRuntime_block_1803_memory (mem := mem) (rdata := out) =
      returnArrayInputMemory mem base out := by
  have hf : base < UInt256.size := by change base < 2 ^ 256; omega
  have ho : out.size < UInt256.size := by change out.size < 2 ^ 256; omega
  have hb : (UInt256.ofNat base).toNat + out.size + 31 ≤ 2 ^ 200 := by
    rw [ulit_toNat' _ hf]; exact hbound
  have hptr : returnReservePtr (UInt256.ofNat base) out.size =
      UInt256.ofNat (returnArrayFree base out) := by
    apply u256_inj
    rw [returnReservePtr_toNat hb, ulit_toNat' _ hf,
      ulit_toNat' _ (by
        have hh := (returnArrayFree_bounds base out).2
        change returnArrayFree base out < 2 ^ 256
        omega)]
    rfl
  simp only [attesterRuntime_block_1803_memory, hfp, ulit_toNat' _ hf, ulit_toNat' _ ho]
  change (returnReservePtr (UInt256.ofNat base) out.size).toByteArray.write 0
    (out.write 0 mem base out.size) 64 32 = _
  rw [hptr]
  rfl

end Benchmarks.EAS.Attester
