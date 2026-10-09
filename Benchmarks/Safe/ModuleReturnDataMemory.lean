import Benchmarks.Safe.ModuleMemory
import Benchmarks.Safe.PostModuleMemory
import Benchmarks.Safe.ByteCopy
import Benchmarks.Safe.Blocks.Runtime_018

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

def moduleReturnDataMemory (mem : ByteArray) (ptr : Nat) (out : ByteArray) : ByteArray :=
  out.write 0
    (writeWord (writeWord mem 64 (UInt256.ofNat (ptr + 32 + out.size))) ptr
      (UInt256.ofNat out.size)) (ptr + 32) out.size

theorem safeModuleReturnDataMemory {mem out : ByteArray} {ptr : UInt256}
    (hf : memLoad ⟨64⟩ mem = ptr) (hb : ptr.toNat + 32 + out.size < UInt256.size) :
    safeRuntime_block_3005_memory (mem := mem) (rdata := out) =
      moduleReturnDataMemory mem ptr.toNat out := by
  have h32 : (ptr + UInt256.ofNat 32).toNat = ptr.toNat + 32 :=
    addWord_toNat ptr ⟨32⟩ (by change ptr.toNat + 32 < UInt256.size; omega)
  have hnext : ptr + (UInt256.ofNat out.size + UInt256.ofNat 32) =
      UInt256.ofNat (ptr.toNat + 32 + out.size) := by
    apply u256_inj
    rw [u256_add_comm (UInt256.ofNat out.size)]
    change (ptr + (⟨32⟩ + UInt256.ofNat out.size)).toNat = _
    rw [u256_32_add_ofNat, uadd_word_ofNat_toNat ptr (out.size + 32) (by omega),
      ulit_toNat' _ hb]
    omega
  change memLoad (UInt256.ofNat 64) mem = ptr at hf
  simp only [safeRuntime_block_3005_memory, hf, h32, hnext,
    ulit_toNat' out.size (by omega), moduleReturnDataMemory, Reasoning.Theory.writeWord]
  rfl

theorem moduleReturnDataMemory_size (mem out : ByteArray) (ptr : Nat) (hp : 96 ≤ ptr) :
    (moduleReturnDataMemory mem ptr out).size = max mem.size (ptr + 32 + out.size) := by
  rw [moduleReturnDataMemory, byteArray_write_all_size _ _ _ (by
    simp only [writeWord_sparse_size]; omega)]
  simp only [writeWord_sparse_size]
  omega

theorem moduleReturnDataMemory_free (mem out : ByteArray) (ptr : Nat) (hp : 96 ≤ ptr) :
    memLoad ⟨64⟩ (moduleReturnDataMemory mem ptr out) = UInt256.ofNat (ptr + 32 + out.size) := by
  apply memLoad_of_wordRead
  change (moduleReturnDataMemory mem ptr out).readWithPadding 64 32 = _
  rw [moduleReturnDataMemory, copyWindowReadBelow _ _ _ _ _ _ _ (by omega)
    (by simp only [writeWord_sparse_size]; omega) (by omega),
    writeWordReadBelow _ _ _ _ _ (by rw [writeWord_sparse_size]; omega) hp,
    writeWord_sparse_read_back]

theorem moduleReturnDataMemory_length (mem out : ByteArray) (ptr : Nat) :
    (moduleReturnDataMemory mem ptr out).readWithPadding ptr 32 =
      (UInt256.ofNat out.size).toByteArray := by
  rw [moduleReturnDataMemory, copyWindowReadBelow _ _ _ _ _ _ _ (by omega)
    (by simp only [writeWord_sparse_size]; omega) (by omega), writeWord_sparse_read_back]

theorem moduleReturnDataMemory_payload (mem out : ByteArray) (ptr : Nat) :
    (moduleReturnDataMemory mem ptr out).readWithPadding (ptr + 32) out.size = out := by
  exact copyWhole_read _ _ _ (by simp only [writeWord_sparse_size]; omega)

theorem postModuleMemory_readBelow (mem : ByteArray) (ptr hash : UInt256) (z : Bool)
    (off count : Nat) (hin : off + count ≤ mem.size) (hb : off + count ≤ ptr.toNat) :
    (postModuleMemory mem ptr hash z).readWithPadding off count =
      mem.readWithPadding off count := by
  rw [postModuleMemory, selectorWordPairMemory,
    writeWordReadBelow _ _ _ _ _ (by simp only [writeWord_sparse_size]; omega) (by omega),
    writeWordReadBelow _ _ _ _ _ (by rw [writeWord_sparse_size]; omega) (by omega),
    writeWordReadBelow _ _ _ _ _ hin hb]

end Benchmarks.Safe
