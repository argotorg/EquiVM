import Benchmarks.Morpho.MetaMorphoV1_1.TransferGuards
import Benchmarks.Morpho.MetaMorphoV1_1.BalanceMutation

/-! The transfer balance check and ordered balance stores. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

def balanceMoveAccounts (I : ExecutionEnv) (σ : AccountMap)
    (sender recipient : AccountAddress) (value : UInt256) : AccountMap :=
  let debited := sstoreAccountMap I.codeOwner σ (balanceSlot sender)
    (UInt256.sub (codeOwnerStorageWord I σ (balanceSlot sender)) value)
  sstoreAccountMap I.codeOwner debited (balanceSlot recipient)
    (codeOwnerStorageWord I debited (balanceSlot recipient) + value)

theorem balanceMoveState_accounts (evm : State)
    (sender recipient : AccountAddress) (value : UInt256) :
    (balanceMoveState evm sender recipient value).accountMap =
      balanceMoveAccounts evm.executionEnv evm.accountMap sender recipient value := by
  simp only [balanceMoveState, balanceDebitState, balanceStore, balanceWord, balanceMoveAccounts,
    storageStore_accountMap, storageStore_executionEnv, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage, codeOwnerStorageWord]

theorem transferReadBalance {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {sender : AccountAddress} {value : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hbal : value.toNat ≤ (codeOwnerStorageWord I σ (balanceSlot sender)).toNat)
    (rd : RD (deployedRuntime v) I g s0 ⟨12761⟩
      (value :: UInt256.ofNat sender.toNat :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨12780⟩
      (codeOwnerStorageWord I σ (balanceSlot sender) :: value :: UInt256.ofNat sender.toNat :: R)
      (twoWordHashMem (UInt256.ofNat sender.toNat) ⟨0⟩ mem) aw' rdata σ k' C' := by
  have hh : keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (UInt256.ofNat sender.toNat) ⟨0⟩ mem) =
      balanceSlot sender := twoWordHashMem_solcMappingSlot_any _ _ _
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_12761_fallthrough_packed
    (immWords := wordsOf (immStore v)) hstack (by
      change UInt256.lt (codeOwnerStorageWord I σ
        (keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (UInt256.ofNat sender.toNat) ⟨0⟩ mem))) value = ⟨0⟩
      rw [hh]
      exact ult_zero hbal) rd
  change RD (deployedRuntime v) I g s0 ⟨12780⟩
    (codeOwnerStorageWord I σ
      (keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (UInt256.ofNat sender.toNat) ⟨0⟩ mem)) ::
      value :: UInt256.ofNat sender.toNat :: R)
    (twoWordHashMem (UInt256.ofNat sender.toNat) ⟨0⟩ mem) aw1 rdata σ k1 C1 at h1
  rw [hh] at h1
  exact ⟨aw1, k1, C1, h1⟩

theorem transferRevertBalance {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {sender : AccountAddress} {value : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (hbal : ¬ value.toNat ≤ (codeOwnerStorageWord I σ (balanceSlot sender)).toNat)
    (rd : RD (deployedRuntime v) I g s0 ⟨12761⟩
      (value :: UInt256.ofNat sender.toNat :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have hh : keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (UInt256.ofNat sender.toNat) ⟨0⟩ mem) =
      balanceSlot sender := twoWordHashMem_solcMappingSlot_any _ _ _
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_12761_taken_packed
    (immWords := wordsOf (immStore v)) (by omega) (by
      change UInt256.lt (codeOwnerStorageWord I σ
        (keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (UInt256.ofNat sender.toNat) ⟨0⟩ mem))) value ≠ ⟨0⟩
      rw [hh, ult_one (Nat.lt_of_not_ge hbal)]
      decide) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_12854 (immWords := wordsOf (immStore v)) hstack h1

def transferScratchMem (mem : ByteArray) (sender recipient : AccountAddress) : ByteArray :=
  twoWordHashMem (UInt256.ofNat recipient.toNat) ⟨0⟩
    (twoWordHashMem (UInt256.ofNat sender.toNat) ⟨0⟩ mem)

def transferReturnMem (mem : ByteArray) (sender recipient : AccountAddress) (value : UInt256) :
    ByteArray :=
  writeWord (transferScratchMem mem sender recipient)
    (memLoad ⟨64⟩ (transferScratchMem mem sender recipient)).toNat value

theorem transferStoreReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {sender recipient : AccountAddress} {value ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024) (hperm : I.perm = true)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨12780⟩
      (codeOwnerStorageWord I σ (balanceSlot sender) :: value :: UInt256.ofNat sender.toNat ::
        UInt256.ofNat recipient.toNat :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret R
      (transferReturnMem mem sender recipient value) aw' rdata
      (balanceMoveAccounts I σ sender recipient value) k' C' := by
  let inner := twoWordHashMem (UInt256.ofNat sender.toNat) ⟨0⟩ mem
  let outer := twoWordHashMem (UInt256.ofNat recipient.toNat) ⟨0⟩ inner
  have hi : keccakWord ⟨0⟩ ⟨64⟩ inner = balanceSlot sender :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  have ho : keccakWord ⟨0⟩ ⟨64⟩ outer = balanceSlot recipient :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_12780_packed
    (immWords := wordsOf (immStore v)) hstack hperm hret rd
  change RD (deployedRuntime v) I g s0 ret R
    (writeWord outer (memLoad ⟨64⟩ outer).toNat value) aw1 rdata
    (sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σ (keccakWord ⟨0⟩ ⟨64⟩ inner)
        (UInt256.sub (codeOwnerStorageWord I σ (balanceSlot sender)) value))
      (keccakWord ⟨0⟩ ⟨64⟩ outer)
      (codeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σ (keccakWord ⟨0⟩ ⟨64⟩ inner)
          (UInt256.sub (codeOwnerStorageWord I σ (balanceSlot sender)) value))
        (keccakWord ⟨0⟩ ⟨64⟩ outer) + value)) k1 C1 at h1
  rw [hi, ho] at h1
  exact ⟨aw1, k1, C1, h1⟩

end Benchmarks.Morpho.MetaMorphoV1_1
