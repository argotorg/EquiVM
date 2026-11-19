import Benchmarks.Midnight.PositionUpdateSourceFrames
import Benchmarks.Midnight.SlashCreditTrace
import Benchmarks.Midnight.MemoryPrefix
import Benchmarks.Midnight.MemoryWords

/-! Scratch and event memory in a position update preserve the previously allocated market. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem twoWordHashMem_prefix (mem : ByteArray) (key slot : UInt256) (limit : Nat) :
    MemoryPrefix mem (twoWordHashMem key slot mem) limit :=
  (memoryPrefix_writeWord mem 0 limit key (Or.inr (by decide))).trans
    (memoryPrefix_writeWord _ 32 limit slot (Or.inr (by decide)))

theorem positionReadMemory_prefix (mem : ByteArray) (id user : UInt256) (limit : Nat) :
    MemoryPrefix mem (positionReadMemory mem id user) limit :=
  (twoWordHashMem_prefix mem id ⟨0⟩ limit).trans (twoWordHashMem_prefix _ user (solcMappingSlot ⟨0⟩ id) limit)

theorem positionSlashMemory_prefix (mem : ByteArray) (id user lastLoss : UInt256) (limit : Nat) :
    MemoryPrefix mem (positionSlashMemory mem id user lastLoss) limit := by
  unfold positionSlashMemory
  split
  · exact (positionReadMemory_prefix mem id user limit).trans (twoWordHashMem_prefix _ id _ limit)
  · exact positionReadMemory_prefix mem id user limit

def positionUpdateScratch (mem : ByteArray) (evm : EVM.State) (id user : UInt256) : ByteArray :=
  positionSlashMemory (positionReadMemory mem id user) id user (positionFieldWord evm id user 2)

theorem positionUpdateScratch_size (mem : ByteArray) (evm : EVM.State) (id user : UInt256)
    (hsize : 64 ≤ mem.size) : (positionUpdateScratch mem evm id user).size = mem.size := by
  rw [positionUpdateScratch, positionSlashMemory_size _ _ _ _ (by
    rw [positionReadMemory_size _ _ _ hsize]; exact hsize), positionReadMemory_size _ _ _ hsize]

theorem positionUpdateScratch_load (mem : ByteArray) (evm : EVM.State) (id user off : UInt256)
    (hlo : 64 ≤ off.toNat) (hin : off.toNat + 32 ≤ mem.size) :
    memLoad off (positionUpdateScratch mem evm id user) = memLoad off mem := by
  have hs : 64 ≤ mem.size := by omega
  rw [positionUpdateScratch, positionSlashMemory_load _ _ _ _ _ hlo (by
    rw [positionReadMemory_size _ _ _ hs]; exact hin), positionReadMemory,
    memLoad_twoWordHashMem _ _ _ hlo (by rw [twoWordHashMem_size_of_ge_64 _ _ hs]; exact hin),
    memLoad_twoWordHashMem _ _ _ hlo hin]

def positionUpdateLogMemory (mem : ByteArray) (root : UInt256) (evm : EVM.State)
    (m : MarketData) (id user : UInt256) : ByteArray :=
  writeWordArray (twoWordHashMem id (UInt256.ofNat 1)
    (twoWordHashMem id (UInt256.ofNat 1) (positionUpdateScratch mem evm id user))) root.toNat
    [positionCreditDecrease evm m id user, positionPendingDecrease evm m id user, positionViewFee evm m id user]

theorem positionUpdateLogMemory_prefix (mem : ByteArray) (root : UInt256) (evm : EVM.State)
    (m : MarketData) (id user : UInt256) :
    MemoryPrefix mem (positionUpdateLogMemory mem root evm m id user) root.toNat :=
  (positionReadMemory_prefix mem id user root.toNat).trans
    ((positionSlashMemory_prefix _ id user _ root.toNat).trans
      ((twoWordHashMem_prefix _ id _ root.toNat).trans
        ((twoWordHashMem_prefix _ id _ root.toNat).trans (memoryPrefix_writeWordArray _ _ _ _ le_rfl))))

theorem positionUpdateLogMemory_free (mem : ByteArray) (root : UInt256) (evm : EVM.State)
    (m : MarketData) (id user : UInt256) (hmem : 96 ≤ mem.size) (hroot : 96 ≤ root.toNat)
    (hfree : memLoad (UInt256.ofNat 64) mem = root) :
    memLoad (UInt256.ofNat 64) (positionUpdateLogMemory mem root evm m id user) = root := by
  have hs : 96 ≤ (positionUpdateScratch mem evm id user).size := by
    rw [positionUpdateScratch_size _ _ _ _ (by omega)]; exact hmem
  have hs1 : 96 ≤ (twoWordHashMem id (UInt256.ofNat 1) (positionUpdateScratch mem evm id user)).size := by
    rw [twoWordHashMem_size_of_ge_64 _ _ (by omega)]; exact hs
  have hs2 : 96 ≤ (twoWordHashMem id (UInt256.ofNat 1)
      (twoWordHashMem id (UInt256.ofNat 1) (positionUpdateScratch mem evm id user))).size := by
    rw [twoWordHashMem_size_of_ge_64 _ _ (by omega)]; exact hs1
  rw [positionUpdateLogMemory, memLoad_writeWordArray_preserved _ _ (UInt256.ofNat 64) _ hs2
    (Or.inl hroot), memLoad_twoWordHashMem id (UInt256.ofNat 1) (UInt256.ofNat 64) (by decide) hs1,
    memLoad_twoWordHashMem id (UInt256.ofNat 1) (UInt256.ofNat 64) (by decide) hs,
    positionUpdateScratch_load mem evm id user (UInt256.ofNat 64) (by decide) hmem, hfree]

end Benchmarks.Midnight
