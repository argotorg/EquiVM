import Benchmarks.Morpho.MetaMorphoV1_1.PendingCapStorage
import Benchmarks.Morpho.MetaMorphoV1_1.SubmitCapScheduleStatic
import Benchmarks.Morpho.MetaMorphoV1_1.Uint184Cast
import Benchmarks.Morpho.MetaMorphoV1_1.MarketRemovalStore

/-! Checked cap scheduling and its two packed storage writes in the runtime. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem pendingCapValueWord_bytecode (old cap : UInt256) (hcap : cap.toNat < 2 ^ 184) :
    UInt256.lor (UInt256.land old
      (UInt256.shiftLeft (UInt256.ofNat (2 ^ 64 - 1)) (UInt256.ofNat 192)))
      (UInt256.land
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 184)) (UInt256.ofNat 1))
        cap) = setPendingUint192Word old cap := by
  have hm : UInt256.shiftLeft (UInt256.ofNat (2 ^ 64 - 1)) (UInt256.ofNat 192) =
      UInt256.lnot (UInt256.ofNat (2 ^ 192 - 1)) := by decide +kernel
  have h184 : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 184))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 184 - 1) := by decide +kernel
  have hc184 := u256LandMaskCleanOfToNat cap (UInt256.ofNat (2 ^ 184 - 1))
    (UInt256.toNat_ofNat_of_lt (by decide)) hcap
  have hc192 := u256LandMaskCleanOfToNat cap (UInt256.ofNat (2 ^ 192 - 1))
    (UInt256.toNat_ofNat_of_lt (by decide)) (lt_trans hcap (by decide))
  rw [hm, h184, u256_land_comm _ cap, hc184, u256_land_comm old, u256_lor_comm]
  simpa only [hc192] using setPendingUint192Word_bytecode old cap

theorem submitCapScheduleValueWrite {evm : State} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw cap id : UInt256} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 11 ≤ 1024)
    (hperm : evm.executionEnv.perm = true) (hcap : cap.toNat < 2 ^ 184)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨9284⟩
      ([cap, ⟨9312⟩, UInt256.ofNat (2 ^ 64 - 1), solcMappingSlot ⟨16⟩ id,
        ⟨9343⟩, cap, id] ++ R) mem aw out evm.accountMap k C) :
    ∃ k' C', RD (deployedRuntime v) evm.executionEnv g s0 ⟨12077⟩
      ([UInt256.ofNat evm.executionEnv.header.timestamp, pendingTimelockDelay evm,
        ⟨9312⟩, UInt256.ofNat (2 ^ 64 - 1), solcMappingSlot ⟨16⟩ id, ⟨9343⟩, cap, id] ++ R)
      mem aw out (pendingCapValueState evm id cap).accountMap k' C' := by
  obtain ⟨k1, C1, r1⟩ := metaMorphoV1_1_block_9284 (immWords := wordsOf (immStore v))
    (by change R.length + 3 + 8 ≤ 1024; omega) hperm
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  rw [pendingCapValueWord_bytecode _ cap hcap] at r1
  refine ⟨k1, C1, ?_⟩
  simpa only [pendingCapValueState, storageStore_accountMap,
    metaMorphoV1_1_block_9284_stack] using r1

theorem submitCapScheduleTimeWrite {evm : State} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw cap id time : UInt256} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024)
    (hperm : evm.executionEnv.perm = true)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨9312⟩
      ([time, UInt256.ofNat (2 ^ 64 - 1), solcMappingSlot ⟨16⟩ id, ⟨9343⟩, cap, id] ++ R)
      mem aw out evm.accountMap k C) :
    RDret (deployedRuntime v) g s0 (pendingCapTimeState evm id time).accountMap
      ByteArray.empty := by
  obtain ⟨k1, C1, r1⟩ := metaMorphoV1_1_block_9312 (immWords := wordsOf (immStore v))
    (by change R.length + 2 + 8 ≤ 1024; omega) hperm
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  have hm : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 192))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 192 - 1) := by decide +kernel
  rw [hm, u256_land_comm (UInt256.ofNat (2 ^ 64 - 1)), pendingTimeCastWord_mask,
    show UInt256.ofNat 192 = (⟨192⟩ : UInt256) by rfl,
    setPendingTimeHighWord_bytecode, pendingTimeCastWord_storeHigh] at r1
  have hret := metaMorphoV1_1_block_9343 (R := R) (immWords := wordsOf (immStore v))
    (by omega) hperm r1
  simpa only [pendingCapTimeState, storageStore_accountMap] using hret

theorem submitCapScheduleRuntime {evm : State} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw cap params id : UInt256} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 14 ≤ 1024)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨9247⟩ (cap :: params :: id :: R)
      mem aw out evm.accountMap k C) :
    (2 ^ 184 ≤ cap.toNat ∧ RDrev (deployedRuntime v) g s0) ∨
    (cap.toNat < 2 ^ 184 ∧ evm.executionEnv.perm = false ∧
      RDstatic (deployedRuntime v) g s0) ∨
    (cap.toNat < 2 ^ 184 ∧ evm.executionEnv.perm = true ∧
      ¬ pendingTimelockScheduleFits evm ∧ RDrev (deployedRuntime v) g s0) ∨
    (cap.toNat < 2 ^ 184 ∧ evm.executionEnv.perm = true ∧
      pendingTimelockScheduleFits evm ∧ RDret (deployedRuntime v) g s0
        (pendingCapScheduledState evm id cap).accountMap ByteArray.empty) := by
  obtain ⟨aw1, k1, C1, r1⟩ := metaMorphoV1_1_block_9247_packed
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  have hh : keccakWord ⟨0⟩ (UInt256.ofNat 64)
      ((UInt256.ofNat 16).toByteArray.write 0 (id.toByteArray.write 0 mem
        (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) =
        solcMappingSlot ⟨16⟩ id := twoWordHashMem_solcMappingSlot_any _ _ _
  have hm64 : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  simp only [metaMorphoV1_1_block_9247_stack, hh, hm64] at r1
  rcases toUint184Runtime v (by change R.length + 6 + 5 ≤ 1024; omega)
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r1 with
    ⟨hover, hrev⟩ | ⟨hcap, k2, C2, r2⟩
  · exact .inl ⟨hover, hrev⟩
  cases hp : evm.executionEnv.perm with
  | false =>
      exact .inr (.inl ⟨hcap, rfl, submitCapScheduleStatic v
        (by change R.length + 3 + 8 ≤ 1024; omega) hp r2⟩)
  | true =>
      obtain ⟨k3, C3, r3⟩ := submitCapScheduleValueWrite v (by omega) hp hcap r2
      by_cases hfit : pendingTimelockScheduleFits evm
      · obtain ⟨k4, C4, r4⟩ := checkedAddReturn v
          (by change R.length + 5 + 4 ≤ 1024; omega) hfit
          (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r3
        exact .inr (.inr (.inr ⟨hcap, rfl, hfit,
          submitCapScheduleTimeWrite (evm := pendingCapValueState evm id cap)
            (R := R) (cap := cap) (id := id) (time := pendingTimelockTime evm) v (by omega)
            (by simp only [pendingCapValueState_env]; exact hp)
            (by simpa only [pendingCapValueState_env] using r4)⟩))
      · exact .inr (.inr (.inl ⟨hcap, rfl, hfit,
          checkedAddRevert v (by change R.length + 5 + 4 ≤ 1024; omega) (by omega) r3⟩))

end Benchmarks.Morpho.MetaMorphoV1_1
