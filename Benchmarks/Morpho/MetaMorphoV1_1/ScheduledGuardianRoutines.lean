import Benchmarks.Morpho.MetaMorphoV1_1.PendingGuardianMutation
import Benchmarks.Morpho.MetaMorphoV1_1.CheckedArithmetic
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_025

/-! Runtime scheduling of a guardian, with checked timestamp addition between the two stores. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

set_option maxRecDepth 2000 in
theorem scheduledGuardianReachAdd {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {R : List UInt256} {value : AccountAddress} {unused : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (hperm : evm.executionEnv.perm = true)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨4458⟩
      (unused :: UInt256.ofNat value.val :: R) mem aw rdata evm.accountMap k C) :
    ∃ k' C', RD (deployedRuntime v) evm.executionEnv g s0 ⟨12077⟩
      (UInt256.ofNat evm.executionEnv.header.timestamp :: pendingGuardianDelay evm ::
        ⟨4491⟩ :: UInt256.ofNat value.val :: R)
      mem aw rdata (pendingGuardianValueState evm value).accountMap k' C' := by
  obtain ⟨k', C', r1⟩ := metaMorphoV1_1_block_4458
    (immWords := wordsOf (immStore v)) hstack hperm
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  have hm : UInt256.shiftLeft (UInt256.sub
      (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 96)) (UInt256.ofNat 1))
      (UInt256.ofNat 160) = UInt256.lnot solcAddrMask := by decide
  have hw : UInt256.lor
      (UInt256.land (codeOwnerStorageWord evm.executionEnv evm.accountMap (UInt256.ofNat 15))
        (UInt256.lnot solcAddrMask)) (UInt256.ofNat value.val) =
      setAddressOffset0Word
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨15⟩) (UInt256.ofNat value.val) := by
    rw [setAddressOffset0Word, solcAddrMask_clean (w := UInt256.ofNat value.val)
      (addressWord_val_canonical value)]
    rfl
  rw [hm, hw] at r1
  refine ⟨k', C', ?_⟩
  simpa only [pendingGuardianValueState, storageStore_accountMap] using r1

set_option maxRecDepth 2000 in
theorem scheduledGuardianTimeReturn {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {R : List UInt256} {time value : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (hperm : evm.executionEnv.perm = true)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨4491⟩ (time :: value :: R)
      mem aw rdata evm.accountMap k C) :
    RDret (deployedRuntime v) g s0 (pendingGuardianTimeState evm time).accountMap
      ByteArray.empty := by
  have hret := metaMorphoV1_1_block_4491 (immWords := wordsOf (immStore v)) hstack hperm rd
  have hm : UInt256.lor
      (UInt256.land (UInt256.shiftLeft (UInt256.ofNat 18446744073709551615) (UInt256.ofNat 160))
        (UInt256.shiftLeft time (UInt256.ofNat 160)))
      (UInt256.land (UInt256.lnot
        (UInt256.shiftLeft (UInt256.ofNat 18446744073709551615) (UInt256.ofNat 160)))
        (codeOwnerStorageWord evm.executionEnv evm.accountMap (UInt256.ofNat 15))) =
      setPendingTimeWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨15⟩) time :=
    setPendingTimeWord_bytecode _ _
  rw [hm] at hret
  simpa only [pendingGuardianTimeState, storageStore_accountMap] using hret

set_option maxRecDepth 2000 in
theorem scheduledGuardianReturn {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {R : List UInt256} {value : AccountAddress} {unused : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (hperm : evm.executionEnv.perm = true) (hfit : pendingGuardianScheduleFits evm)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨4458⟩
      (unused :: UInt256.ofNat value.val :: R) mem aw rdata evm.accountMap k C) :
    RDret (deployedRuntime v) g s0 (pendingGuardianScheduledState evm value).accountMap
      ByteArray.empty := by
  obtain ⟨_, _, r1⟩ := scheduledGuardianReachAdd v hstack hperm rd
  obtain ⟨_, _, r2⟩ := checkedAddReturn v (by simp only [List.length]; omega) hfit
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r1
  apply scheduledGuardianTimeReturn (evm := pendingGuardianValueState evm value)
    (R := R) (value := UInt256.ofNat value.val) v (by omega)
    (by simpa only [pendingGuardianValueState_executionEnv] using hperm)
  simpa only [pendingGuardianValueState_executionEnv, pendingGuardianTime] using r2

theorem scheduledGuardianRevert {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {R : List UInt256} {value : AccountAddress} {unused : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (hperm : evm.executionEnv.perm = true) (hover : ¬ pendingGuardianScheduleFits evm)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨4458⟩
      (unused :: UInt256.ofNat value.val :: R) mem aw rdata evm.accountMap k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨_, _, r1⟩ := scheduledGuardianReachAdd v hstack hperm rd
  exact checkedAddRevert v (by simp only [List.length]; omega) (Nat.le_of_not_gt hover) r1

end Benchmarks.Morpho.MetaMorphoV1_1
