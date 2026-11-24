import Benchmarks.Safe.ViaIR.AddOwnerSource
import Benchmarks.Safe.ViaIR.CheckedIncrement
import Benchmarks.Safe.ViaIR.Blocks.Runtime_032
import Benchmarks.Safe.ViaIR.Blocks.Runtime_033
import Benchmarks.Safe.ViaIR.Blocks.Runtime_006

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

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
    (h : RD fork safeBytecode I g s0 ⟨6724⟩ (key :: threshold :: R) mem aw rdata σ k C)
    (hov : R.length + 11 ≤ 1024) (hm : mem.size = 96)
    (hc : key.toNat < EVM.addressModulus) (hperm : I.perm = true) :
    ∃ mem' aw' k' C', RD fork safeBytecode I g s0 ⟨7497⟩
      (solcSlotWordAt ⟨3⟩ (addOwnerLinkAccounts σ I key) I :: ⟨6831⟩ :: key ::
        threshold :: R) mem' aw' rdata (addOwnerLinkAccounts σ I key) k' C' := by
  obtain ⟨aw', k', C', h'⟩ := safeRuntime_block_6724_packed (by simp; omega) hperm (by jump_dest) h
  simp only [safeRuntime_block_6724_stack, safeAddressMask, solcAddrMask_clean_left hc] at h'
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
      UInt256.lor key (UInt256.land (UInt256.lnot solcAddrMask) word) =
      setAddressOffset0Word word key := by
    rw [u256_lor_comm key, setAddressOffset0Word, solcAddrMask_clean hc,
      u256_land_comm (UInt256.lnot solcAddrMask) word]
  simp only [hfirst, hsecond] at h'
  exact ⟨_, aw', k', C', h'⟩

theorem safeAddOwnerTraceStatic {I g s0 σ k C aw mem rdata} {key threshold : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6724⟩ (key :: threshold :: R) mem aw rdata σ k C)
    (hov : R.length + 11 ≤ 1024) (hperm : I.perm = false) :
    RDstatic fork safeBytecode g s0 := by
  have hslot := evm_run h with [jumpdest, push1 ⟨2⟩, push1 ⟨32⟩, genMstore]
  have hsent := hslot.pushConst
    (UInt256.ofNat 105409183525425523237923285454331214386340807945685310246717412709691342439136)
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by simp; omega)
  have hdup := evm_run hsent with [dup1]
  obtain ⟨_, _, hnext⟩ := RD.sload hdup (by native_decide) (by simp; omega)
  have hhash := evm_run hnext with [push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    swap3, dup4, and, push0, dup2, dup2, genMstore, push1 ⟨64⟩, dup2, genKeccak256, dup1]
  obtain ⟨_, _, hload⟩ := RD.sload hhash (by native_decide) (by simp; omega)
  have hstore := evm_run hload with [swap6, swap1, swap4, and, push1 ⟨1⟩, push1 ⟨1⟩,
    push1 ⟨160⟩, shl, sub, not, swap6, dup7, and, or, swap1, swap3]
  exact hstore.sstoreStatic hperm (by native_decide) (by simp; omega)

theorem safeAddOwnerCountUnchanged {I g s0 σ k C aw mem rdata} {key threshold : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6831⟩
      ((solcSlotWordAt ⟨3⟩ σ I + ⟨1⟩) :: key :: threshold :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) (hperm : I.perm = true)
    (ht : solcSlotWordAt ⟨4⟩ (addOwnerCountAccounts σ I) I = threshold) :
    RDret fork safeBytecode g s0 (addOwnerCountAccounts σ I) ByteArray.empty := by
  obtain ⟨_, _, h₁⟩ := safeRuntime_block_6831_fallthrough (by omega) hperm
    (u256_sub_eq_zero_iff_eq.mpr ht) h
  exact safeRuntime_block_6882 (by simp [safeRuntime_block_6831_fallthrough_stack]; omega) h₁

theorem safeAddOwnerCountChanged {I g s0 σ k C aw mem rdata} {key threshold : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6831⟩
      ((solcSlotWordAt ⟨3⟩ σ I + ⟨1⟩) :: key :: threshold :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) (hperm : I.perm = true)
    (ht : solcSlotWordAt ⟨4⟩ (addOwnerCountAccounts σ I) I ≠ threshold) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨6883⟩
      ((solcSlotWordAt ⟨3⟩ σ I + ⟨1⟩) :: threshold :: R) mem aw' rdata
      (addOwnerCountAccounts σ I) k' C' := by
  exact safeRuntime_block_6831_taken_packed (by omega) hperm
    (u256_sub_ne_zero_of_ne ht) (by jump_dest) h

theorem safeAddOwnerLinkAccountPresent (σ : AccountMap) (I : ExecutionEnv) (key : UInt256)
    (hacc : σ.get? I.codeOwner ≠ none) :
    (addOwnerLinkAccounts σ I key).get? I.codeOwner ≠ none := by
  obtain ⟨acc, hacc⟩ := Option.ne_none_iff_exists'.mp hacc
  simp only [Std.ExtTreeMap.get?_eq_getElem?] at hacc
  simp [addOwnerLinkAccounts, sstoreAccountMap, hacc, Option.option]

theorem safeAddOwnerCountValue (evm : EVM.State)
    (hacc : evm.accountMap.get? evm.executionEnv.codeOwner ≠ none) :
    ownerCount (addOwnerCountState evm) = ownerCount evm + ⟨1⟩ := by
  obtain ⟨acc, hacc⟩ := Option.ne_none_iff_exists'.mp hacc
  simpa only [ownerCount, addOwnerCountState, storageStore_executionEnv] using
    storageLoad_storageStore_same_present evm evm.executionEnv.codeOwner hacc ⟨3⟩
      (ownerCount evm + ⟨1⟩)

theorem safeAddOwnerThresholdTrace {I g s0 σ k C aw mem rdata} {count value : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6891⟩ (count :: value :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) (hperm : I.perm = true)
    (hle : value.toNat ≤ count.toNat) (hnz : value ≠ ⟨0⟩) :
    RDret fork safeBytecode g s0 (sstoreAccountMap I.codeOwner σ ⟨4⟩ value) ByteArray.empty := by
  have h₁ := safeRuntime_block_6891_fallthrough (by omega) (ugt_zero hle) h
  have h₂ := safeRuntime_block_6898_fallthrough (by omega) (isZero_eq_zero_of_ne hnz) h₁
  exact safeRuntime_block_6904 (by omega) hperm h₂

theorem safeAddOwnerThresholdTooLarge {I g s0 σ k C aw mem rdata} {count value : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6891⟩ (count :: value :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) (hle : ¬value.toNat ≤ count.toNat) :
    RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_6891_taken (by omega)
    (by rw [ugt_one (by omega)]; decide) (by jump_dest) h
  have h₂ := safeRuntime_block_874 (by simp [safeRuntime_block_6891_taken_stack]; omega)
    (by jump_dest) h₁
  exact safeRuntime_block_9502 (by simp [safeRuntime_block_6891_taken_stack]; omega) h₂

theorem safeAddOwnerThresholdZero {I g s0 σ k C aw mem rdata} {count : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6891⟩ (count :: ⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_6891_fallthrough (by omega)
    (ugt_zero (show (⟨0⟩ : UInt256).toNat ≤ count.toNat from Nat.zero_le _)) h
  have h₂ := safeRuntime_block_6898_taken (by omega) (by decide) (by jump_dest) h₁
  have h₃ := safeRuntime_block_869 (by simp; omega) (by jump_dest) h₂
  exact safeRuntime_block_9547 (by simp; omega) h₃

end Benchmarks.Safe.ViaIR
