import Benchmarks.Midnight.TakeParticipantsRuntime
import Benchmarks.Midnight.MappingKeyUpdate

/-! Scratch memory for both position slots and the buyer's initial credit read. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def takePositionsMemory (mem : ByteArray) (id buyer seller : UInt256) : ByteArray :=
  writeWord (writeWord (positionReadMemory mem id buyer) 0 seller) 0 buyer

def takeHasCreditWord (σ : AccountMap) (I : ExecutionEnv) (id user : UInt256) : UInt256 :=
  UInt256.isZero (UInt256.isZero (low128 (solcSlotWordAt (positionSlot id user) σ I)))

theorem takePositionsMemory_size (mem : ByteArray) (id buyer seller : UInt256)
    (hm : 64 ≤ mem.size) : (takePositionsMemory mem id buyer seller).size = mem.size := by
  simp only [takePositionsMemory, writeWord_sparse_size, positionReadMemory_size _ _ _ hm]
  omega

theorem takePositionsMemory_load {mem : ByteArray} (id buyer seller read : UInt256)
    (hlo : 64 ≤ read.toNat) (hin : read.toNat + 32 ≤ mem.size) :
    memLoad read (takePositionsMemory mem id buyer seller) = memLoad read mem := by
  have hm : 64 ≤ mem.size := by omega
  rw [takePositionsMemory, memLoad_writeWord_preserved _ _ _ _
    (by rw [writeWord_sparse_size, positionReadMemory_size _ _ _ hm]; omega)
      (Or.inr (by omega)),
    memLoad_writeWord_preserved _ _ _ _ (by rw [positionReadMemory_size _ _ _ hm]; exact hin)
      (Or.inr (by omega)), positionReadMemory,
    memLoad_twoWordHashMem _ _ _ hlo (by rw [twoWordHashMem_size_of_ge_64 _ _ hm]; exact hin),
    memLoad_twoWordHashMem _ _ _ hlo hin]

theorem takePositionsMemory_prefix (mem : ByteArray) (id buyer seller : UInt256) (limit : Nat) :
    MemoryPrefix mem (takePositionsMemory mem id buyer seller) limit :=
  ((positionReadMemory_prefix mem id buyer limit).trans
    (memoryPrefix_writeWord _ 0 limit seller (Or.inr (by decide)))).trans
    (memoryPrefix_writeWord _ 0 limit buyer (Or.inr (by decide)))

end Benchmarks.Midnight
