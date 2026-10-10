import Benchmarks.Morpho.MetaMorphoV1_1.AcceptPendingGuards
import Benchmarks.Morpho.MetaMorphoV1_1.SetPendingRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_013

/-! Complete the accepted update through its setter and the shared return point. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

def acceptPendingSetterPC (guardian : Bool) : UInt256 := if guardian then ⟨15404⟩ else ⟨14755⟩

theorem pendingGuardianValueWord (word : UInt256) :
    UInt256.ofNat (AccountAddress.ofNat (pendingUpdateValue true word).toNat).val =
      pendingUpdateValue true word := (maskedAddress_eq_iff_word word _).mp rfl

set_option maxRecDepth 2000 in
theorem acceptPendingValueJump {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {word : UInt256}
    (v : MetaMorphoV1_1Immutables) (guardian : Bool) (hstack : R.length + 5 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 (acceptPendingValuePC guardian) (word :: R)
      mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 (acceptPendingSetterPC guardian)
      (pendingUpdateValue guardian word :: ⟨1867⟩ :: R) mem aw rdata σ k' C' := by
  cases guardian
  · have r1 := metaMorphoV1_1_block_4931 (immWords := wordsOf (immStore v)) hstack
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    have hm : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 192))
        (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 192 - 1) := by decide
    refine ⟨k + 10, C + 35, ?_⟩
    simpa only [metaMorphoV1_1_block_4931_stack, hm, u256_land_comm] using r1
  · have r1 := metaMorphoV1_1_block_4217 (immWords := wordsOf (immStore v)) hstack
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    change RD _ _ _ _ _ (UInt256.land solcAddrMask word :: ⟨1867⟩ :: R) _ _ _ _ _ _ at r1
    rw [u256_land_comm solcAddrMask] at r1
    exact ⟨_, _, r1⟩

set_option maxRecDepth 2000 in
theorem acceptPendingStoreReturn {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (guardian : Bool) (hstack : R.length + 7 ≤ 1024)
    (hperm : evm.executionEnv.perm = true)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 (acceptPendingValuePC guardian)
      (pendingUpdateWord guardian evm :: R) mem aw rdata evm.accountMap k C) :
    RDret (deployedRuntime v) g s0 (acceptPendingState guardian evm).accountMap
      ByteArray.empty := by
  obtain ⟨_, _, r1⟩ := acceptPendingValueJump v guardian (by omega) rd
  cases guardian
  · obtain ⟨_, _, _, r2⟩ := setTimelockReturn (evm := evm) v (by omega) hperm
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r1
    exact metaMorphoV1_1_block_1867 (immWords := wordsOf (immStore v)) (by omega) r2
  · rw [← pendingGuardianValueWord] at r1
    obtain ⟨_, _, _, r2⟩ := setGuardianReturn (evm := evm) v hstack hperm
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r1
    exact metaMorphoV1_1_block_1867 (immWords := wordsOf (immStore v)) (by omega) r2

set_option maxRecDepth 2000 in
theorem acceptPendingStoreStatic {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (guardian : Bool) (hstack : R.length + 7 ≤ 1024)
    (hperm : evm.executionEnv.perm = false)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 (acceptPendingValuePC guardian)
      (pendingUpdateWord guardian evm :: R) mem aw rdata evm.accountMap k C) :
    RDstatic (deployedRuntime v) g s0 := by
  obtain ⟨_, _, r1⟩ := acceptPendingValueJump v guardian (by omega) rd
  cases guardian
  · exact setTimelockStatic v (by omega) hperm r1
  · rw [← pendingGuardianValueWord] at r1
    exact setGuardianStatic v hstack hperm r1

end Benchmarks.Morpho.MetaMorphoV1_1
