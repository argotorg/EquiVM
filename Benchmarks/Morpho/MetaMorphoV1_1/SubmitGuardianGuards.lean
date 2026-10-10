import Benchmarks.Morpho.MetaMorphoV1_1.SubmitGuardianEntry
import Benchmarks.Morpho.MetaMorphoV1_1.SubmitGuardianSyntax
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_010

/-! Reject unchanged guardians and existing pending updates before selecting the update path. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

def guardianWord (evm : EVM.State) : UInt256 :=
  UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩) solcAddrMask

theorem guardianWord_eq_iff (evm : EVM.State) (value : AccountAddress) :
    guardianWord evm = UInt256.ofNat value.val ↔ guardianAddress evm = value := by
  exact eq_comm.trans (maskedAddress_eq_iff_word _ value).symm

theorem guardianWord_zero_iff (evm : EVM.State) :
    guardianWord evm = ⟨0⟩ ↔ guardianAddress evm = AccountAddress.ofNat 0 :=
  guardianWord_eq_iff evm (AccountAddress.ofNat 0)

set_option maxRecDepth 2000 in
theorem submitGuardianReadDifferent {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {R : List UInt256} {value : AccountAddress}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hne : value ≠ guardianAddress evm)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨4401⟩ (UInt256.ofNat value.val :: R)
      mem aw rdata evm.accountMap k C) :
    ∃ k' C', RD (deployedRuntime v) evm.executionEnv g s0 ⟨4426⟩
      (guardianWord evm :: UInt256.ofNat value.val :: UInt256.ofNat value.val :: R)
      mem aw rdata evm.accountMap k' C' := by
  have hc : UInt256.eq (guardianWord evm) (UInt256.land solcAddrMask
      (UInt256.ofNat value.val)) = ⟨0⟩ := by
    rw [solcAddrMask_clean_left (w := UInt256.ofNat value.val) (addressWord_val_canonical value)]
    exact u256_eq_of_ne (fun h ↦ hne ((guardianWord_eq_iff evm value).mp h).symm)
  obtain ⟨k', C', r1⟩ := metaMorphoV1_1_block_4401_fallthrough
    (immWords := wordsOf (immStore v)) hstack hc rd
  change RD _ _ _ _ _ (guardianWord evm :: UInt256.ofNat value.val ::
    UInt256.land solcAddrMask (UInt256.ofNat value.val) :: R) _ _ _ _ _ _ at r1
  rw [solcAddrMask_clean_left (w := UInt256.ofNat value.val)
    (addressWord_val_canonical value)] at r1
  exact ⟨k', C', r1⟩

set_option maxRecDepth 2000 in
theorem submitGuardianReachBranch {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {R : List UInt256} {value : AccountAddress}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (hgood : submitGuardianAllowed evm value)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨4401⟩ (UInt256.ofNat value.val :: R)
      mem aw rdata evm.accountMap k C) :
    ∃ k' C', RD (deployedRuntime v) evm.executionEnv g s0 ⟨4445⟩
      (guardianWord evm :: UInt256.ofNat value.val :: UInt256.ofNat value.val :: R)
      mem aw rdata evm.accountMap k' C' := by
  obtain ⟨_, _, r1⟩ := submitGuardianReadDifferent v (by omega) hgood.1 rd
  exact metaMorphoV1_1_block_4426_fallthrough (immWords := wordsOf (immStore v))
    (by simp only [List.length]; omega) hgood.2 r1

set_option maxRecDepth 2000 in
theorem submitGuardianRevertGuard {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {R : List UInt256} {value : AccountAddress}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (hbad : ¬ submitGuardianAllowed evm value)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨4401⟩ (UInt256.ofNat value.val :: R)
      mem aw rdata evm.accountMap k C) : RDrev (deployedRuntime v) g s0 := by
  by_cases heq : value = guardianAddress evm
  · have hc : UInt256.eq (guardianWord evm)
        (UInt256.land solcAddrMask (UInt256.ofNat value.val)) ≠ ⟨0⟩ := by
      rw [solcAddrMask_clean_left (w := UInt256.ofNat value.val) (addressWord_val_canonical value),
        (guardianWord_eq_iff evm value).mpr heq.symm]
      simp only [UInt256.eq]
      decide
    obtain ⟨_, _, r1⟩ := metaMorphoV1_1_block_4401_taken
      (immWords := wordsOf (immStore v)) (by omega) hc
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    exact metaMorphoV1_1_block_1143 (immWords := wordsOf (immStore v))
      (by simp only [metaMorphoV1_1_block_4401_taken_stack, List.length]; omega) r1
  · obtain ⟨_, _, r1⟩ := submitGuardianReadDifferent v (by omega) heq rd
    have ht : pendingUpdateTime true (pendingUpdateWord true evm) ≠ ⟨0⟩ :=
      fun hz ↦ hbad ⟨heq, hz⟩
    obtain ⟨_, _, r2⟩ := metaMorphoV1_1_block_4426_taken
      (immWords := wordsOf (immStore v)) (by simp only [List.length]; omega) ht
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r1
    exact metaMorphoV1_1_block_4572 (immWords := wordsOf (immStore v))
      (by simp only [List.length]; omega) r2

end Benchmarks.Morpho.MetaMorphoV1_1
