import Benchmarks.Safe.GuardCallMemory
import Reasoning.HeapMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def preModuleOutputMemory (mem out : ByteArray) (ptr : UInt256) : ByteArray :=
  out.write 0 mem ptr.toNat (min 32 out.size)

def preModuleNextPtr (ptr : UInt256) (out : ByteArray) : UInt256 :=
  ptr + UInt256.land (UInt256.ofNat out.size + UInt256.ofNat 31)
    (UInt256.lnot (UInt256.ofNat 31))

def preModuleReturnMemory (mem out : ByteArray) (ptr : UInt256) : ByteArray :=
  writeWord (preModuleOutputMemory mem out ptr) 64 (preModuleNextPtr ptr out)

theorem preModuleOutputFree {mem out : ByteArray} {ptr : UInt256}
    (hf : memLoad ⟨64⟩ mem = ptr) (hm : ptr.toNat ≤ mem.size) (hp : 96 ≤ ptr.toNat) :
    memLoad ⟨64⟩ (preModuleOutputMemory mem out ptr) = ptr := by
  have hs : mem.size ≤ (preModuleOutputMemory mem out ptr).size :=
    byteArray_write_size_ge_base _ _ _ _ _
  calc
    _ = memLoad ⟨64⟩ mem := by
      simp only [memLoad, show (⟨64⟩ : UInt256).toNat = 64 from rfl,
        if_neg (show ¬ 64 ≥ (preModuleOutputMemory mem out ptr).size by omega),
        if_neg (show ¬ 64 ≥ mem.size by omega)]
      congr 2
      exact callOutputFreePtrAt mem out ptr.toNat hm hp
    _ = ptr := hf

theorem preModuleReturnWord {mem out : ByteArray} {ptr : UInt256}
    (hm : ptr.toNat + 32 ≤ mem.size) (hp : 96 ≤ ptr.toNat) (hl : 32 ≤ out.size) :
    memLoad ptr (preModuleReturnMemory mem out ptr) = calldataWord out 0 := by
  apply memLoad_of_wordRead
  have hs : mem.size ≤ (preModuleOutputMemory mem out ptr).size :=
    byteArray_write_size_ge_base _ _ _ _ _
  rw [preModuleReturnMemory, writeWord_sparse_read_preserved _ _ _ _
    (.inr ⟨hp, by omega⟩)]
  exact callOutputWordAt mem out ptr.toNat (by omega) hl

theorem preModuleReturnFree (mem out : ByteArray) (ptr : UInt256) :
    memLoad ⟨64⟩ (preModuleReturnMemory mem out ptr) = preModuleNextPtr ptr out := by
  apply memLoad_of_wordRead
  exact writeWord_sparse_read_back _ _ _

theorem preModuleReturnSize {mem out : ByteArray} {ptr : UInt256} (hm : 96 ≤ mem.size) :
    96 ≤ (preModuleReturnMemory mem out ptr).size := by
  rw [preModuleReturnMemory, writeWord_sparse_size]
  omega

theorem preModuleNextPtr_toNat {ptr : UInt256} {out : ByteArray}
    (hb : ptr.toNat + out.size + 31 ≤ 2 ^ 200) :
    (preModuleNextPtr ptr out).toNat = ptr.toNat + (out.size + 31) / 32 * 32 := by
  have he : preModuleNextPtr ptr out = returnReservePtr ptr out.size := by
    unfold preModuleNextPtr returnReservePtr returnReserveSize
    rw [u256_land_comm]
    rfl
  rw [he, returnReservePtr_toNat hb]

end Benchmarks.Safe
