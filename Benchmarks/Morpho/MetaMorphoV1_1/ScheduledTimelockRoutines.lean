import Benchmarks.Morpho.MetaMorphoV1_1.PendingTimelockMutation
import Benchmarks.Morpho.MetaMorphoV1_1.TimelockBoundsSource
import Benchmarks.Morpho.MetaMorphoV1_1.CheckedArithmetic
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_035

/-! Runtime scheduling of a timelock with checked addition between the two stores. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

def submitTimelockTopic : UInt256 :=
  UInt256.ofNat 81264438903807308125143185332747105003289375680382869976726107697328478286720

theorem timelockValueMasks (value : UInt256) (hbound : timelockInBounds value) :
    UInt256.land value (UInt256.ofNat (2 ^ 184 - 1)) =
      UInt256.land value (UInt256.ofNat (2 ^ 192 - 1)) := by
  apply u256_inj
  rw [uland_toNat, uland_toNat]
  change Nat.land value.toNat (2 ^ 184 - 1) = Nat.land value.toNat (2 ^ 192 - 1)
  rw [nat_land_mask_eq_mod, nat_land_mask_eq_mod,
    Nat.mod_eq_of_lt (show value.toNat < 2 ^ 184 by have := hbound.1; omega),
    Nat.mod_eq_of_lt (show value.toNat < 2 ^ 192 by have := hbound.1; omega)]

set_option maxRecDepth 2000 in
theorem scheduledTimelockReachAdd {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {R : List UInt256} {value : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (hperm : evm.executionEnv.perm = true) (hbound : timelockInBounds value)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨6955⟩
      (pendingTimelockDelay evm :: value :: R) mem aw rdata evm.accountMap k C) :
    ∃ k' C', RD (deployedRuntime v) evm.executionEnv g s0 ⟨12077⟩
      (UInt256.ofNat evm.executionEnv.header.timestamp :: pendingTimelockDelay evm ::
        ⟨7029⟩ :: value :: ⟨32⟩ :: submitTimelockTopic :: R)
      mem aw rdata (pendingTimelockValueState evm value).accountMap k' C' := by
  obtain ⟨k', C', r1⟩ := metaMorphoV1_1_block_6955
    (immWords := wordsOf (immStore v)) hstack hperm
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  have hm184 : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 184))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 184 - 1) := by decide
  have hm192 : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 192))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 192 - 1) := by decide
  rw [hm184, hm192, timelockValueMasks value hbound, setPendingUint192Word_bytecode] at r1
  refine ⟨k', C', ?_⟩
  simpa only [pendingTimelockValueState, storageStore_accountMap] using r1

set_option maxRecDepth 2000 in
theorem scheduledTimelockTimeReturn {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {R : List UInt256} {time value : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 9 ≤ 1024)
    (hperm : evm.executionEnv.perm = true)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨7029⟩
      (time :: value :: ⟨32⟩ :: submitTimelockTopic :: R) mem aw rdata evm.accountMap k C) :
    RDret (deployedRuntime v) g s0 (pendingTimelockTimeState evm time).accountMap
      ByteArray.empty := by
  have hret := metaMorphoV1_1_block_7029 (immWords := wordsOf (immStore v)) hstack hperm rd
  have hm192 : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 192))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 192 - 1) := by decide
  rw [hm192, show UInt256.ofNat 192 = (⟨192⟩ : UInt256) by decide,
    setPendingTimeHighWord_bytecode] at hret
  simpa only [pendingTimelockTimeState, storageStore_accountMap] using hret

set_option maxRecDepth 2000 in
theorem scheduledTimelockReturn {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {R : List UInt256} {value : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 9 ≤ 1024)
    (hperm : evm.executionEnv.perm = true) (hbound : timelockInBounds value)
    (hfit : pendingTimelockScheduleFits evm)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨6955⟩
      (pendingTimelockDelay evm :: value :: R) mem aw rdata evm.accountMap k C) :
    RDret (deployedRuntime v) g s0 (pendingTimelockScheduledState evm value).accountMap
      ByteArray.empty := by
  obtain ⟨_, _, r1⟩ := scheduledTimelockReachAdd v (by omega) hperm hbound rd
  obtain ⟨_, _, r2⟩ := checkedAddReturn v (by simp only [List.length]; omega) hfit
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r1
  apply scheduledTimelockTimeReturn (evm := pendingTimelockValueState evm value)
    (R := R) (value := value) v hstack
    (by simpa only [pendingTimelockValueState_executionEnv] using hperm)
  simpa only [pendingTimelockValueState_executionEnv, pendingTimelockTime] using r2

theorem scheduledTimelockRevert {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {R : List UInt256} {value : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 9 ≤ 1024)
    (hperm : evm.executionEnv.perm = true) (hbound : timelockInBounds value)
    (hover : ¬ pendingTimelockScheduleFits evm)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨6955⟩
      (pendingTimelockDelay evm :: value :: R) mem aw rdata evm.accountMap k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨_, _, r1⟩ := scheduledTimelockReachAdd v (by omega) hperm hbound rd
  exact checkedAddRevert v (by simp only [List.length]; omega) (Nat.le_of_not_gt hover) r1

end Benchmarks.Morpho.MetaMorphoV1_1
