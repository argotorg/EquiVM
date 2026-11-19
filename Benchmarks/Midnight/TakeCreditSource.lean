import Benchmarks.Midnight.HasCreditSource
import Benchmarks.Midnight.PositionUpdateCallFunding
import Benchmarks.Midnight.TakePositionsMemory

/-! Correspondence between source credit predicates and their runtime boolean words. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem hasCreditValue_eq (evm : State) (id user : UInt256) :
    hasCreditValue evm id user = !decide (positionFieldWord evm id user 0 = ⟨0⟩) := by
  have hp : 0 < (positionFieldWord evm id user 0).toNat ↔
      positionFieldWord evm id user 0 ≠ ⟨0⟩ := by
    constructor
    · intro h he; rw [he] at h; contradiction
    · intro h
      exact Nat.pos_of_ne_zero (fun he ↦ h (uint256_toNat_eq_zero he))
  simp only [hasCreditValue, hp, decide_not]

theorem positionCreditSourceWord {s0 evm : State} {I : ExecutionEnv} {σ : AccountMap}
    (hs : SourceState s0 I σ evm) (id user : UInt256) :
    positionFieldWord evm id user 0 = low128 (solcSlotWordAt (positionSlot id user) σ I) := by
  change UInt256.land (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
    (positionSlot id user)) uint128Mask = _
  rw [hs.storageRead]
  rfl

theorem positionDebtSourceWord {s0 evm : State} {I : ExecutionEnv} {σ : AccountMap}
    (hs : SourceState s0 I σ evm) (id user : UInt256) :
    low128 (healthPositionWord evm id user) =
      low128 (solcSlotWordAt (positionSlot id user + ⟨2⟩) σ I) := by
  unfold healthPositionWord
  rw [hs.storageRead]
  rfl

theorem takeHasCreditWord_source {s0 evm : State} {I : ExecutionEnv} {σ : AccountMap}
    (hs : SourceState s0 I σ evm) (id user : UInt256) :
    takeHasCreditWord σ I id user =
      if positionFieldWord evm id user 0 = ⟨0⟩ then ⟨0⟩ else ⟨1⟩ := by
  rw [takeHasCreditWord, ← positionCreditSourceWord hs]
  by_cases hz : positionFieldWord evm id user 0 = ⟨0⟩
  · simp only [hz, if_true]
    rfl
  · rw [if_neg hz, isZero_eq_zero_of_ne hz]
    rfl

theorem positionReadMemory_load {mem : ByteArray} (id user read : UInt256)
    (hlo : 64 ≤ read.toNat) (hin : read.toNat + 32 ≤ mem.size) :
    memLoad read (positionReadMemory mem id user) = memLoad read mem := by
  rw [positionReadMemory, memLoad_twoWordHashMem _ _ _ hlo (by
    rw [twoWordHashMem_size_of_ge_64 _ _ (by omega)]; exact hin),
    memLoad_twoWordHashMem _ _ _ hlo hin]

end Benchmarks.Midnight
