import Benchmarks.CompoundIII.Comet.PermissionEvm
import Benchmarks.CompoundIII.Comet.PermissionSource
import Benchmarks.CompoundIII.Comet.MappingScratch
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- GENERALIZES permissionMemory_size to any memory containing the Solidity scratch area.
theorem permissionMemory_size_ge (owner manager : UInt256) {mem : ByteArray}
    (hm : 64 ≤ mem.size) : (permissionMemory owner manager mem).size = mem.size := by
  unfold permissionMemory
  split
  · rfl
  · rw [twoWordHashMem_size_of_ge_64 _ _ (by rw [twoWordHashMem_size_of_ge_64 _ _ hm]; exact hm),
      twoWordHashMem_size_of_ge_64 _ _ hm]

theorem permissionMemory_free (owner manager : UInt256) {mem : ByteArray}
    (hm : 96 ≤ mem.size) : memLoad ⟨64⟩ (permissionMemory owner manager mem) = memLoad ⟨64⟩ mem := by
  unfold permissionMemory
  split
  · rfl
  · rw [twoWordHashMem_load_ge (ptr := ⟨64⟩) _ _ (by decide)
      (by rw [twoWordHashMem_size_of_ge_64 _ _ (by omega)]; exact hm),
      twoWordHashMem_load_ge (ptr := ⟨64⟩) _ _ (by decide) hm]

-- GENERALIZES permissionBool_init to a source state reached after storage writes or calls.
theorem permissionBool_state {s0 I σ evm} (hs : SourceState s0 I σ evm)
    (owner manager : AccountAddress) :
    permissionBool evm owner manager =
      decide ((permissionRuntimeWord σ I (EVM.word owner.val) (EVM.word manager.val)).toNat ≠ 0) := by
  have heq : EVM.word owner.val = EVM.word manager.val ↔ owner = manager := by
    constructor
    · intro he
      have ha := congrArg AccountAddress.ofUInt256 he
      change AccountAddress.ofUInt256 (UInt256.ofNat owner.val) =
        AccountAddress.ofUInt256 (UInt256.ofNat manager.val) at ha
      simpa only [accountAddress_roundtrip] using ha
    · intro he; rw [he]
  have hr := hs.storageRead (isAllowedSlot owner manager)
  simp only [permissionBool, permissionRuntimeWord, heq]
  by_cases he : owner = manager
  · simp only [he, decide_true, Bool.true_or, if_true]
    decide
  · simp only [he, decide_false, Bool.false_or, if_false]
    rw [hr]
    rfl

theorem permissionRuntime_nonzero {s0 I σ evm owner manager}
    (hs : SourceState s0 I σ evm) (hp : permissionBool evm owner manager = true) :
    permissionRuntimeWord σ I (EVM.word owner.val) (EVM.word manager.val) ≠ ⟨0⟩ := by
  rw [permissionBool_state hs] at hp
  intro he
  simp only [he, show (⟨0⟩ : UInt256).toNat = 0 from rfl, ne_eq,
    not_true_eq_false, decide_false, Bool.false_eq_true] at hp

theorem permissionRuntime_zero {s0 I σ evm owner manager}
    (hs : SourceState s0 I σ evm) (hp : ¬ permissionBool evm owner manager = true) :
    permissionRuntimeWord σ I (EVM.word owner.val) (EVM.word manager.val) = ⟨0⟩ := by
  apply uint256_toNat_eq_zero
  rw [permissionBool_state hs] at hp
  simpa only [decide_eq_true_eq, not_not] using hp

end Benchmarks.CompoundIII.Comet
