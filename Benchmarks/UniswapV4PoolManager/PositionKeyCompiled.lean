import Benchmarks.UniswapV4PoolManager.PositionKeyMemory
import Benchmarks.UniswapV4PoolManager.WordStoreMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem positionKeyMemory_compiled (mem : ByteArray) (ptr : UInt256) (owner : AccountAddress)
    (lower upper salt : UInt256) (hf : ptr.toNat+38 < UInt256.size) :
    ((accountWord owner).toByteArray.write 0 (lower.toByteArray.write 0
      (upper.toByteArray.write 0 (salt.toByteArray.write 0 mem (ptr+UInt256.ofNat 38).toNat 32)
        (ptr+UInt256.ofNat 6).toNat 32) (ptr+UInt256.ofNat 3).toNat 32) ptr.toNat 32) =
      positionKeyMemory mem ptr.toNat owner lower upper salt := by
  have h38 := uadd_word_ofNat_toNat ptr 38 hf
  have h6 := uadd_word_ofNat_toNat ptr 6 (by omega)
  have h3 := uadd_word_ofNat_toNat ptr 3 (by omega)
  change writeWord (writeWord (writeWord (writeWord mem (ptr+UInt256.ofNat 38).toNat salt)
    (ptr+UInt256.ofNat 6).toNat upper) (ptr+UInt256.ofNat 3).toNat lower) ptr.toNat (accountWord owner) = _
  rw [h38, h6, h3]
  rfl

theorem positionKeyMemory_hash (mem : ByteArray) (ptr : UInt256) (owner : AccountAddress)
    (lower upper salt : UInt256) (hf : ptr.toNat+12 < UInt256.size) :
    keccakWord (ptr+UInt256.ofNat 12) (UInt256.ofNat 58)
      (positionKeyMemory mem ptr.toNat owner lower upper salt) = positionKey owner lower upper salt := by
  have h12 := uadd_word_ofNat_toNat ptr 12 hf
  change UInt256.ofNat (fromByteArrayBigEndian (KEC
    ((positionKeyMemory mem ptr.toNat owner lower upper salt).readWithPadding (ptr+UInt256.ofNat 12).toNat 58))) = _
  rw [h12, positionKeyMemory_read]
  exact keccakSlot_eq _

def positionKeyCleanMemory (mem : ByteArray) (off : Nat) (owner : AccountAddress) (lower upper salt : UInt256) : ByteArray :=
  writeWord (writeWord (writeWord (positionKeyMemory mem off owner lower upper salt) (off+64) ⟨0⟩)
    (off+32) ⟨0⟩) off ⟨0⟩

theorem positionKeyCleanMemory_size (mem : ByteArray) (off : Nat) (owner : AccountAddress) (lower upper salt : UInt256) :
    (positionKeyCleanMemory mem off owner lower upper salt).size = max mem.size (off+96) := by
  simp only [positionKeyCleanMemory, writeWord_sparse_size, positionKeyMemory_size]
  omega

theorem positionKeyCleanMemory_load_before {mem : ByteArray} {off : Nat} (owner : AccountAddress)
    (lower upper salt read : UInt256) (hin : read.toNat+32 ≤ mem.size) (hb : read.toNat+32 ≤ off) :
    memLoad read (positionKeyCleanMemory mem off owner lower upper salt) = memLoad read mem := by
  rw [positionKeyCleanMemory, writeWord_sparse_load_before _ _ _ _
      (by simp only [writeWord_sparse_size, positionKeyMemory_size]; omega) hb,
    writeWord_sparse_load_before _ _ _ _ (by rw [writeWord_sparse_size, positionKeyMemory_size]; omega) (by omega),
    writeWord_sparse_load_before _ _ _ _ (by rw [positionKeyMemory_size]; omega) (by omega),
    positionKeyMemory_load_before owner lower upper salt read hin hb]

theorem positionKeyCleanMemory_compiled (mem : ByteArray) (ptr : UInt256) (owner : AccountAddress)
    (lower upper salt : UInt256) (hf : ptr.toNat+64 < UInt256.size) :
    ((⟨0⟩ : UInt256).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0
      ((⟨0⟩ : UInt256).toByteArray.write 0 (positionKeyMemory mem ptr.toNat owner lower upper salt)
        (ptr+UInt256.ofNat 64).toNat 32) (ptr+UInt256.ofNat 32).toNat 32) ptr.toNat 32) =
      positionKeyCleanMemory mem ptr.toNat owner lower upper salt := by
  have h64 := uadd_word_ofNat_toNat ptr 64 hf
  have h32 := uadd_word_ofNat_toNat ptr 32 (by omega)
  change writeWord (writeWord (writeWord (positionKeyMemory mem ptr.toNat owner lower upper salt)
    (ptr+UInt256.ofNat 64).toNat ⟨0⟩) (ptr+UInt256.ofNat 32).toNat ⟨0⟩) ptr.toNat ⟨0⟩ = _
  rw [h64, h32]
  rfl

end Benchmarks.UniswapV4PoolManager
