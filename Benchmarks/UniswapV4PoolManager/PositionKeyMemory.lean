import Benchmarks.UniswapV4PoolManager.PositionKeySource
import Benchmarks.UniswapV4PoolManager.SparseBytesMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def positionKeyMemory (mem : ByteArray) (off : Nat) (owner : AccountAddress) (lower upper salt : UInt256) : ByteArray :=
  writeWord (writeWord (writeWord (writeWord mem (off+38) salt) (off+6) upper) (off+3) lower)
    off (accountWord owner)

theorem positionKeyMemory_size (mem : ByteArray) (off : Nat) (owner : AccountAddress) (lower upper salt : UInt256) :
    (positionKeyMemory mem off owner lower upper salt).size = max mem.size (off+70) := by
  simp only [positionKeyMemory, writeWord_sparse_size]
  omega

theorem positionKeyMemory_read_owner (mem : ByteArray) (off : Nat) (owner : AccountAddress)
    (lower upper salt : UInt256) :
    (positionKeyMemory mem off owner lower upper salt).readWithPadding (off+12) 20 =
      (accountWord owner).toByteArray.extract 12 32 :=
  writeWord_sparse_read_window _ off 12 20 (accountWord owner) (by decide) (by decide) (by decide)

theorem positionKeyMemory_read_lower (mem : ByteArray) (off : Nat) (owner : AccountAddress)
    (lower upper salt : UInt256) :
    (positionKeyMemory mem off owner lower upper salt).readWithPadding (off+32) 3 =
      lower.toByteArray.extract 29 32 := by
  rw [positionKeyMemory, writeWord_sparse_read_preserved_unbounded _ _ _ _ _
    (by simp only [writeWord_sparse_size]; omega) (.inr (by omega))]
  simpa only [Nat.add_assoc] using writeWord_sparse_read_window
    (writeWord (writeWord mem (off+38) salt) (off+6) upper) (off+3) 29 3 lower (by decide) (by decide) (by decide)

theorem positionKeyMemory_read_upper (mem : ByteArray) (off : Nat) (owner : AccountAddress)
    (lower upper salt : UInt256) :
    (positionKeyMemory mem off owner lower upper salt).readWithPadding (off+35) 3 =
      upper.toByteArray.extract 29 32 := by
  rw [positionKeyMemory, writeWord_sparse_read_preserved_unbounded _ _ _ _ _
      (by simp only [writeWord_sparse_size]; omega) (.inr (by omega)),
    writeWord_sparse_read_preserved_unbounded _ _ _ _ _
      (by simp only [writeWord_sparse_size]; omega) (.inr (by omega))]
  simpa only [Nat.add_assoc] using writeWord_sparse_read_window
    (writeWord mem (off+38) salt) (off+6) 29 3 upper (by decide) (by decide) (by decide)

theorem positionKeyMemory_read_salt (mem : ByteArray) (off : Nat) (owner : AccountAddress)
    (lower upper salt : UInt256) :
    (positionKeyMemory mem off owner lower upper salt).readWithPadding (off+38) 32 = salt.toByteArray := by
  rw [positionKeyMemory, writeWord_sparse_read_preserved_unbounded _ _ _ _ _
      (by simp only [writeWord_sparse_size]; omega) (.inr (by omega)),
    writeWord_sparse_read_preserved_unbounded _ _ _ _ _
      (by simp only [writeWord_sparse_size]; omega) (.inr (by omega)),
    writeWord_sparse_read_preserved_unbounded _ _ _ _ _
      (by simp only [writeWord_sparse_size]; omega) (.inr (by omega)), writeWord_sparse_read_back]

theorem positionKeyMemory_read (mem : ByteArray) (off : Nat) (owner : AccountAddress) (lower upper salt : UInt256) :
    (positionKeyMemory mem off owner lower upper salt).readWithPadding (off+12) 58 =
      positionKeyBytes owner lower upper salt := by
  have hs := positionKeyMemory_size mem off owner lower upper salt
  rw [show 58 = 20+38 from rfl, readWithPadding_split _ _ 20 38 (by omega), positionKeyMemory_read_owner,
    show off+12+20 = off+32 by omega, show 38 = 3+35 from rfl,
    readWithPadding_split _ _ 3 35 (by omega), positionKeyMemory_read_lower,
    show off+32+3 = off+35 by omega, show 35 = 3+32 from rfl,
    readWithPadding_split _ _ 3 32 (by omega), positionKeyMemory_read_upper,
    show off+35+3 = off+38 by omega, positionKeyMemory_read_salt]
  simp only [positionKeyBytes, ByteArray.append_assoc]

theorem positionKeyMemory_load_before {mem : ByteArray} {off : Nat} (owner : AccountAddress)
    (lower upper salt read : UInt256) (hin : read.toNat+32 ≤ mem.size) (hb : read.toNat+32 ≤ off) :
    memLoad read (positionKeyMemory mem off owner lower upper salt) = memLoad read mem := by
  rw [positionKeyMemory, writeWord_sparse_load_before _ _ _ _
      (by simp only [writeWord_sparse_size]; omega) hb,
    writeWord_sparse_load_before _ _ _ _ (by simp only [writeWord_sparse_size]; omega) (by omega),
    writeWord_sparse_load_before _ _ _ _ (by rw [writeWord_sparse_size]; omega) (by omega),
    writeWord_sparse_load_before _ _ _ _ hin (by omega)]

end Benchmarks.UniswapV4PoolManager
