import Benchmarks.Morpho.MetaMorphoV1_1.SetCapStorage
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_065

/-! The cap setter's final packed write, event, deletion, and internal return. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

def setCapTailAccounts (I : ExecutionEnv) (σ : AccountMap) (id cap : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner
    (sstoreAccountMap I.codeOwner σ (solcMappingSlot ⟨13⟩ id)
      (setLowBytesWord (codeOwnerStorageWord I σ (solcMappingSlot ⟨13⟩ id)) cap 23))
    (solcMappingSlot ⟨16⟩ id) ⟨0⟩

theorem setCapFinalState_accounts (evm : State) (id cap : UInt256) :
    (setCapFinalState evm id cap).accountMap =
      setCapTailAccounts evm.executionEnv evm.accountMap id cap := by
  simp only [setCapFinalState, setCapValueState, storageStore_accountMap]
  rfl

theorem setCapValueWord_bytecode (old cap : UInt256) (hcap : cap.toNat < 2 ^ 184) :
    UInt256.lor (UInt256.land old
      (UInt256.shiftLeft (UInt256.ofNat 4722366482869645213695) (UInt256.ofNat 184))) cap =
      setLowBytesWord old cap 23 := by
  have hm : UInt256.shiftLeft (UInt256.ofNat 4722366482869645213695) (UInt256.ofNat 184) =
      UInt256.lnot (UInt256.ofNat (2 ^ (8 * 23) - 1)) := by decide
  rw [hm, u256_land_comm old]
  simpa only [show 8 * 23 = 184 by decide, wordLowMask_eq_self cap 184 (by decide) hcap]
    using setLowBytesWord_bytecode old cap 23 (by decide)

theorem setCapTailRuntime {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {junk cap id ret : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024)
    (hcap : cap.toNat < 2 ^ 184) (hperm : I.perm = true)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨13479⟩
      ([junk, cap, id, ret, solcMappingSlot ⟨13⟩ id] ++ R) mem aw rdata σ k C) :
    ∃ mem' aw' k' C', RD (deployedRuntime v) I g s0 ret R mem' aw' rdata
      (setCapTailAccounts I σ id cap) k' C' := by
  obtain ⟨k', C', h⟩ := metaMorphoV1_1_block_13479
    (immWords := wordsOf (immStore v)) hstack hperm hret rd
  have hh : keccakWord ⟨0⟩ (UInt256.ofNat 64)
      ((UInt256.ofNat 16).toByteArray.write 0
        (id.toByteArray.write 0 (cap.toByteArray.write 0 mem
          (memLoad (UInt256.ofNat 64) mem).toNat 32) (⟨0⟩ : UInt256).toNat 32)
        (UInt256.ofNat 32).toNat 32) =
      solcMappingSlot ⟨16⟩ id := twoWordHashMem_solcMappingSlot_any _ _ _
  change ∃ mem' aw' k' C', RD (deployedRuntime v) I g s0 ret R mem' aw' rdata
    (sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σ (solcMappingSlot ⟨13⟩ id)
        (setLowBytesWord (codeOwnerStorageWord I σ (solcMappingSlot ⟨13⟩ id)) cap 23))
      (solcMappingSlot ⟨16⟩ id) ⟨0⟩) k' C'
  rw [hh] at h
  have hw := setCapValueWord_bytecode
    (codeOwnerStorageWord I σ (solcMappingSlot ⟨13⟩ id)) cap hcap
  dsimp only [codeOwnerStorageWord] at hw
  rw [hw] at h
  exact ⟨_, _, k', C', h⟩

theorem setCapClearTimeRuntime {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {junk cap id ret : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024) (hperm : I.perm = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨13576⟩
      ([junk, cap, id, ret, solcMappingSlot ⟨13⟩ id] ++ R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨13479⟩
      ([id, cap, id, ret, solcMappingSlot ⟨13⟩ id] ++ R) mem aw rdata
      (sstoreAccountMap I.codeOwner σ (solcMappingSlot ⟨13⟩ id)
        (UInt256.land (UInt256.ofNat (2 ^ 192 - 1))
          (codeOwnerStorageWord I σ (solcMappingSlot ⟨13⟩ id)))) k' C' := by
  obtain ⟨k', C', h⟩ := metaMorphoV1_1_block_13576
    (immWords := wordsOf (immStore v)) hstack hperm
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  have hm : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 192))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 192 - 1) := by decide
  rw [hm] at h
  exact ⟨k', C', h⟩

end Benchmarks.Morpho.MetaMorphoV1_1
