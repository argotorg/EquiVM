import Benchmarks.Safe.Runs1e6.AddOwnerSource
import Benchmarks.Safe.Runs1e6.CheckedIncrement
import Benchmarks.Safe.Runs1e6.Blocks.Runtime_006
import Benchmarks.Safe.Runs1e6.Blocks.Runtime_013
import Benchmarks.Safe.Runs1e6.Blocks.Runtime_014

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.Runs1e6.RuntimeBlocks

namespace Benchmarks.Safe.Runs1e6

set_option maxRecDepth 100000

def addOwnerLinkAccounts (σ : AccountMap) (I : ExecutionEnv) (key : UInt256) : AccountMap :=
  let σ₁ := sstoreAccountMap I.codeOwner σ (mapSlot key ⟨2⟩)
    (setAddressOffset0Word (solcSlotWordAt (mapSlot key ⟨2⟩) σ I) (ownerLinkAt σ I ⟨1⟩))
  sstoreAccountMap I.codeOwner σ₁ (mapSlot ⟨1⟩ ⟨2⟩)
    (setAddressOffset0Word (solcSlotWordAt (mapSlot ⟨1⟩ ⟨2⟩) σ₁ I) key)

def addOwnerCountAccounts (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨3⟩ ((solcSlotWordAt ⟨3⟩ σ I) + ⟨1⟩)

theorem safeAddOwnerLinkAccounts (evm : EVM.State) (key : UInt256) :
    (addOwnerLinks evm key).accountMap = addOwnerLinkAccounts evm.accountMap evm.executionEnv key
      := by
  simp only [addOwnerLinks, writeOwnerLink, ownerLink, storageStore_executionEnv,
    storageLoad_eq_solcSlotWord, storageStore_accountMap]
  rfl

theorem safeAddOwnerLinksEnv (evm : EVM.State) (key : UInt256) :
    (addOwnerLinks evm key).executionEnv = evm.executionEnv := by
  simp only [addOwnerLinks, writeOwnerLink, storageStore_executionEnv]

theorem safeAddOwnerCountAccounts (evm : EVM.State) :
    (addOwnerCountState evm).accountMap = addOwnerCountAccounts evm.accountMap evm.executionEnv :=
      by
  simp only [addOwnerCountState, ownerCount, storageStore_accountMap, storageLoad_eq_solcSlotWord]
  rfl

theorem safeAddOwnerCountEnv (evm : EVM.State) :
    (addOwnerCountState evm).executionEnv = evm.executionEnv := by
  simp only [addOwnerCountState, storageStore_executionEnv]

theorem safeAddOwnerLinksTrace {I g s0 σ k C aw mem rdata} {key threshold : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1777⟩ (threshold :: key :: R) mem aw rdata σ k C)
    (hov : R.length + 11 ≤ 1024) (hm : mem.size = 96)
    (hc : key.toNat < EVM.addressModulus) (hperm : I.perm = true) :
    ∃ mem' aw' k' C', RD fork safeBytecode I g s0 ⟨13831⟩
      (solcSlotWordAt ⟨3⟩ (addOwnerLinkAccounts σ I key) I :: ⟨1924⟩ :: ⟨0⟩ :: ⟨3⟩ ::
        threshold :: key :: R) mem' aw' rdata (addOwnerLinkAccounts σ I key) k' C' := by
  obtain ⟨aw', k', C', h'⟩ := safeRuntime_block_1777_packed (by omega) hperm (by jump_dest) h
  simp only [safeRuntime_block_1777_stack, safeAddressMaskLiteral, safeAddressComplementLiteral,
    solcAddrMask_clean_left hc] at h'
  have hh := keyAfterSlotHash key (UInt256.ofNat 2) hm
  change keccakWord ⟨0⟩ (UInt256.ofNat 64)
    (key.toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem
      (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) = mapSlot key ⟨2⟩ at hh
  rw [hh, ← safeOwnerSentinelSlot] at h'
  have hfirst (word next : UInt256) :
      UInt256.lor (UInt256.land (UInt256.lnot solcAddrMask) word)
        (UInt256.land next solcAddrMask) =
      setAddressOffset0Word word (UInt256.land next solcAddrMask) := by
    rw [setAddressOffset0Word, maskTwice, u256_land_comm (UInt256.lnot solcAddrMask) word]
  have hsecond (word : UInt256) :
      UInt256.lor (UInt256.land (UInt256.lnot solcAddrMask) word) key =
      setAddressOffset0Word word key := by
    rw [setAddressOffset0Word, solcAddrMask_clean hc,
      u256_land_comm (UInt256.lnot solcAddrMask) word]
  simp only [hfirst, hsecond] at h'
  exact ⟨_, aw', k', C', h'⟩

theorem safeAddOwnerTraceStatic {I g s0 σ k C aw mem rdata} {key threshold : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1777⟩ (threshold :: key :: R) mem aw rdata σ k C)
    (hov : R.length + 11 ≤ 1024) (hperm : I.perm = false) :
    RDstatic fork safeBytecode g s0 := by
  have hslot := evm_run h with [jumpdest, push1 ⟨2⟩, push1 ⟨32⟩, genMstore]
  have hsent := hslot.pushConst
    (UInt256.ofNat 105409183525425523237923285454331214386340807945685310246717412709691342439136)
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by simp; omega)
  have hdup := evm_run hsent with [dup1]
  obtain ⟨_, _, hnext⟩ := RD.sload hdup (by native_decide) (by simp; omega)
  have hhash := evm_run hnext with [push20 solcAddrMask,
    dup5, dup2, and, push0, dup2, dup2, genMstore, push1 ⟨64⟩, dup2, genKeccak256, dup1]
  obtain ⟨_, _, hload⟩ := RD.sload hhash (by native_decide) (by simp; omega)
  have hmask := evm_run hload with [swap4, swap1, swap5, and]
  have hmask := hmask.pushConst (UInt256.lnot solcAddrMask)
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by simp; omega)
  have hstore := evm_run hmask with [swap4, dup5, and, or, swap1, swap4]
  exact hstore.sstoreStatic hperm (by native_decide) (by simp; omega)

theorem safeAddOwnerCountUnchanged {I g s0 σ k C aw mem rdata} {key threshold : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1924⟩
      ((solcSlotWordAt ⟨3⟩ σ I + ⟨1⟩) :: ⟨0⟩ :: ⟨3⟩ :: threshold :: key :: ⟨664⟩ :: R)
      mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) (hperm : I.perm = true)
    (ht : solcSlotWordAt ⟨4⟩ (addOwnerCountAccounts σ I) I = threshold) :
    RDret fork safeBytecode g s0 (addOwnerCountAccounts σ I) ByteArray.empty := by
  obtain ⟨_, _, h₁⟩ := safeRuntime_block_1924_taken (by simp; omega) hperm
    (by change UInt256.eq (solcSlotWordAt ⟨4⟩ (addOwnerCountAccounts σ I) I) threshold ≠ ⟨0⟩
        rw [ht, uInt256_eq_self]; decide) (by jump_dest) h
  have h₂ := safeRuntime_block_2010 (by omega) (by jump_dest) h₁
  exact safeRuntime_block_664 (by simp [safeRuntime_block_2010_stack]; omega) h₂

theorem safeAddOwnerCountChanged {I g s0 σ k C aw mem rdata} {key threshold ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1924⟩
      ((solcSlotWordAt ⟨3⟩ σ I + ⟨1⟩) :: ⟨0⟩ :: ⟨3⟩ :: threshold :: key :: ret :: R)
      mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) (hperm : I.perm = true)
    (ht : solcSlotWordAt ⟨4⟩ (addOwnerCountAccounts σ I) I ≠ threshold) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨4000⟩
      (threshold :: ⟨2010⟩ :: threshold :: key :: ret :: R) mem aw' rdata
      (addOwnerCountAccounts σ I) k' C' := by
  obtain ⟨aw', k', C', h₁⟩ := safeRuntime_block_1924_fallthrough_packed (by simp; omega) hperm
    (by
      change UInt256.eq (solcSlotWordAt ⟨4⟩ (addOwnerCountAccounts σ I) I) threshold = ⟨0⟩
      exact uInt256_eq_zero_of_ne (fun he ↦ ht (uInt256_eq_one_eq he))) h
  exact ⟨aw', _, _, safeRuntime_block_2002 (by simp; omega) (by jump_dest) h₁⟩

end Benchmarks.Safe.Runs1e6
