import Benchmarks.Morpho.MetaMorphoV1_1.MarketRemovalStorage
import Benchmarks.Morpho.MetaMorphoV1_1.MarketRemovalStatic
import Benchmarks.Morpho.MetaMorphoV1_1.CheckedArithmetic

/-! Checked scheduling arithmetic and the packed timestamp update in the runtime. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem pendingTimeCastWord_mask (time : UInt256) :
    UInt256.land time (UInt256.ofNat (2 ^ 64 - 1)) = pendingTimeCastWord time := by
  apply u256_inj
  rw [uland_toNat, pendingTimeCastWord_toNat]
  change Nat.land time.toNat (2 ^ 64 - 1) = time.toNat % 2 ^ 64
  exact nat_land_mask_eq_mod _ _

theorem marketRemovalStoreReturn {evm : State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {R : List UInt256} {id time : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 9 ≤ 1024)
    (hperm : evm.executionEnv.perm = true)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨5365⟩
      (time :: UInt256.ofNat (2 ^ 64 - 1) :: ⟨5414⟩ :: id :: R)
      mem aw rdata evm.accountMap k C) :
    RDret (deployedRuntime v) g s0 (marketRemovalTimeState evm id time).accountMap
      ByteArray.empty := by
  obtain ⟨aw1, k1, C1, r1⟩ := metaMorphoV1_1_block_5365_packed
    (immWords := wordsOf (immStore v)) hstack hperm
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  have hh : keccakWord ⟨0⟩ (UInt256.ofNat 64)
      ((UInt256.ofNat 13).toByteArray.write 0
        (id.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) =
        solcMappingSlot ⟨13⟩ id := twoWordHashMem_solcMappingSlot_any _ _ _
  have hm192 : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 192))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 192 - 1) := by decide +kernel
  rw [hh, hm192, pendingTimeCastWord_mask,
    show UInt256.ofNat 192 = (⟨192⟩ : UInt256) by rfl,
    setPendingTimeHighWord_bytecode, pendingTimeCastWord_storeHigh] at r1
  have h := metaMorphoV1_1_block_5414 (immWords := wordsOf (immStore v))
    (by omega) hperm r1
  simpa only [marketRemovalTimeState, marketRemovalConfigWord, storageStore_accountMap] using h

theorem marketRemovalReachAdd {evm : State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨5343⟩ R
      mem aw rdata evm.accountMap k C) :
    ∃ k' C', RD (deployedRuntime v) evm.executionEnv g s0 ⟨12077⟩
      (UInt256.ofNat evm.executionEnv.header.timestamp :: pendingTimelockDelay evm ::
        ⟨5365⟩ :: UInt256.ofNat (2 ^ 64 - 1) :: ⟨5414⟩ :: R)
      mem aw rdata evm.accountMap k' C' := by
  obtain ⟨k', C', r1⟩ := metaMorphoV1_1_block_5343 (immWords := wordsOf (immStore v))
    hstack (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact ⟨k', C', r1⟩

theorem marketRemovalSchedule {evm : State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {R : List UInt256} {id : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨5343⟩ (id :: R)
      mem aw rdata evm.accountMap k C) :
    (¬ pendingTimelockScheduleFits evm ∧ RDrev (deployedRuntime v) g s0) ∨
    (pendingTimelockScheduleFits evm ∧ evm.executionEnv.perm = false ∧
      RDstatic (deployedRuntime v) g s0) ∨
    (pendingTimelockScheduleFits evm ∧ evm.executionEnv.perm = true ∧
      RDret (deployedRuntime v) g s0
        (marketRemovalTimeState evm id (pendingTimelockTime evm)).accountMap ByteArray.empty) := by
  obtain ⟨_, _, r1⟩ := marketRemovalReachAdd v (by simp only [List.length_cons]; omega) rd
  by_cases hfit : pendingTimelockScheduleFits evm
  · obtain ⟨_, _, r2⟩ := checkedAddReturn v (by simp only [List.length_cons]; omega) hfit
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r1
    cases hp : evm.executionEnv.perm
    · exact .inr (.inl ⟨hfit, rfl, marketRemovalStoreStatic v (by omega) hp r2⟩)
    · exact .inr (.inr ⟨hfit, rfl, marketRemovalStoreReturn v (by omega) hp r2⟩)
  · exact .inl ⟨hfit, checkedAddRevert v (by simp only [List.length_cons]; omega)
      (Nat.le_of_not_gt hfit) r1⟩

end Benchmarks.Morpho.MetaMorphoV1_1
