import Benchmarks.Safe.BytesMemoryPreserved
import Benchmarks.Safe.Hashes

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def ethSignPrefixBytes : ByteArray :=
  ⟨#[25, 69, 116, 104, 101, 114, 101, 117, 109, 32, 83, 105, 103, 110,
    101, 100, 32, 77, 101, 115, 115, 97, 103, 101, 58, 10, 51, 50]⟩

def ethSignPrefixWord : UInt256 :=
  ⟨11430537079145650693387304458692941425836787954612963690241153482819318579200⟩

def ethSignBytes (hash : UInt256) : ByteArray := ethSignPrefixBytes ++ hash.toByteArray

def ethSignWord (hash : UInt256) : UInt256 := uInt256OfByteArray (KEC (ethSignBytes hash))

def ethSignPayloadMemory (mem : ByteArray) (ptr : Nat) (hash : UInt256) : ByteArray :=
  writeWord (writeWord mem (ptr + 32) ethSignPrefixWord) (ptr + 60) hash

def ethSignMemory (mem : ByteArray) (ptr : Nat) (hash : UInt256) : ByteArray :=
  writeWord (writeWord (ethSignPayloadMemory mem ptr hash) ptr ⟨60⟩) 64
    (UInt256.ofNat (ptr + 92))

theorem ethSignPayloadMemory_size (mem : ByteArray) (ptr : Nat) (hash : UInt256) :
    (ethSignPayloadMemory mem ptr hash).size = max mem.size (ptr + 92) := by
  simp only [ethSignPayloadMemory, writeWord_sparse_size]
  omega

theorem ethSignMemory_size (mem : ByteArray) (ptr : Nat) (hash : UInt256) (hp : 96 ≤ ptr) :
    (ethSignMemory mem ptr hash).size = max mem.size (ptr + 92) := by
  simp only [ethSignMemory, writeWord_sparse_size, ethSignPayloadMemory_size]
  omega

theorem ethSignPayloadMemory_read (mem : ByteArray) (ptr : Nat) (hash : UInt256) :
    (ethSignPayloadMemory mem ptr hash).readWithPadding (ptr + 32) 60 = ethSignBytes hash := by
  have hs : (ethSignPrefixWord.toByteArray).extract 0 28 = ethSignPrefixBytes := by native_decide
  rw [show 60 = 28 + 32 from rfl, byteArray_readWithPadding_split_unbounded _ _ _ _
    (by decide) (by decide) (by rw [ethSignPayloadMemory_size]; omega)]
  have hl : (ethSignPayloadMemory mem ptr hash).readWithPadding (ptr + 32) 28 =
      ethSignPrefixBytes := by
    rw [ethSignPayloadMemory, writeWordReadBelow _ _ _ _ _ (by
      rw [writeWord_sparse_size]; omega) (by omega),
      ← paddedReadPrefix _ (ptr + 32) 28 32 (by rw [writeWord_sparse_size]; omega) (by decide),
      writeWord_sparse_read_back, hs]
  rw [hl]
  change ethSignPrefixBytes ++ (Reasoning.Theory.writeWord _ (ptr + 60) hash).readWithPadding
    (ptr + 32 + 28) 32 = _
  rw [show ptr + 32 + 28 = ptr + 60 by omega, writeWord_sparse_read_back]
  rfl

theorem ethSignMemory_read (mem : ByteArray) (ptr : Nat) (hash : UInt256) (hp : 96 ≤ ptr) :
    (ethSignMemory mem ptr hash).readWithPadding (ptr + 32) 60 = ethSignBytes hash := by
  rw [ethSignMemory, writeWordReadAbove _ _ _ _ _ (by
    rw [writeWord_sparse_size, ethSignPayloadMemory_size]; omega) (by omega),
    writeWordReadAbove _ _ _ _ _ (by rw [ethSignPayloadMemory_size]; omega) (by omega),
    ethSignPayloadMemory_read]

theorem ethSignPayloadMemory_free {mem : ByteArray} {ptr : Nat} {hash : UInt256}
    (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr) (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) :
    memLoad ⟨64⟩ (ethSignPayloadMemory mem ptr hash) = UInt256.ofNat ptr := by
  rw [memLoadReadWord, show (⟨64⟩ : UInt256).toNat = 64 from rfl, ethSignPayloadMemory,
    writeWordReadBelow _ _ _ _ _ (by rw [writeWord_sparse_size]; omega) (by omega),
    writeWordReadBelow _ _ _ _ _ hm (by omega),
    ← show (⟨64⟩ : UInt256).toNat = 64 from rfl, ← memLoadReadWord, hf]

theorem ethSignMemory_free (mem : ByteArray) (ptr : Nat) (hash : UInt256) :
    memLoad ⟨64⟩ (ethSignMemory mem ptr hash) = UInt256.ofNat (ptr + 92) := by
  apply memLoad_of_wordRead
  exact writeWord_sparse_read_back _ _ _

theorem ethSignMemory_length (mem : ByteArray) (ptr : Nat) (hash : UInt256)
    (hp : 96 ≤ ptr) (hb : ptr < UInt256.size) :
    memLoad (UInt256.ofNat ptr) (ethSignMemory mem ptr hash) = ⟨60⟩ := by
  apply memLoad_of_wordRead
  rw [ulit_toNat' ptr hb, ethSignMemory, writeWordReadAbove _ _ _ _ _ (by
    rw [writeWord_sparse_size]; omega) hp, writeWord_sparse_read_back]

theorem ethSignMemory_preserved (mem : ByteArray) (ptr off count : Nat) (hash : UInt256)
    (hin : off + count ≤ mem.size) (hl : 96 ≤ off) (hh : off + count ≤ ptr) :
    (ethSignMemory mem ptr hash).readWithPadding off count =
      mem.readWithPadding off count := by
  rw [ethSignMemory, writeWordReadAbove _ _ _ _ _ (by
    rw [writeWord_sparse_size, ethSignPayloadMemory_size]; omega) hl,
    writeWordReadBelow _ _ _ _ _ (by rw [ethSignPayloadMemory_size]; omega) hh,
    ethSignPayloadMemory, writeWordReadBelow _ _ _ _ _ (by
      rw [writeWord_sparse_size]; omega) (by omega), writeWordReadBelow _ _ _ _ _ hin (by omega)]

theorem ethSignMemory_bytes {mem bytes : ByteArray} {ptr src : Nat} {hash : UInt256}
    (hm : BytesMemory mem src bytes) (hs : 96 ≤ src)
    (ha : src + 32 + bytes.size ≤ ptr) (hb : src < UInt256.size) :
    BytesMemory (ethSignMemory mem ptr hash) src bytes := by
  apply hm.preserved hb (by rw [ethSignMemory_size _ _ _ (by omega)]; omega)
  intro off count hlo hin
  exact ethSignMemory_preserved _ _ _ _ _ (by have := hm.available; omega) (by omega) (by omega)

end Benchmarks.Safe
