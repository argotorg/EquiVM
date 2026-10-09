import Benchmarks.Safe.RemoveOwnerSource
import Benchmarks.Safe.CheckedDecrement
import Benchmarks.Safe.Blocks.Runtime_028
import Benchmarks.Safe.Blocks.Runtime_029
import Benchmarks.Safe.Blocks.Runtime_006

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

def removeOwnerCountAccounts (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨3⟩ (UInt256.sub (solcSlotWordAt ⟨3⟩ σ I) ⟨1⟩)

def removeOwnerLinkAccounts (σ : AccountMap) (I : ExecutionEnv) (prev key : UInt256) : AccountMap :=
  let σ₁ := sstoreAccountMap I.codeOwner σ (mapSlot prev ⟨2⟩)
    (setAddressOffset0Word (solcSlotWordAt (mapSlot prev ⟨2⟩) σ I) (ownerLinkAt σ I key))
  sstoreAccountMap I.codeOwner σ₁ (mapSlot key ⟨2⟩)
    (setAddressOffset0Word (solcSlotWordAt (mapSlot key ⟨2⟩) σ₁ I) ⟨0⟩)

theorem safeRemoveOwnerCountAccounts (evm : EVM.State) :
    (removeOwnerCountState evm).accountMap =
      removeOwnerCountAccounts evm.accountMap evm.executionEnv := by
  simp only [removeOwnerCountState, ownerCount, storageStore_accountMap,
    storageLoad_eq_solcSlotWord]
  rfl

theorem safeRemoveOwnerCountEnv (evm : EVM.State) :
    (removeOwnerCountState evm).executionEnv = evm.executionEnv :=
  storageStore_executionEnv _ _ _ _

theorem safeRemoveOwnerCountValue (evm : EVM.State) (hnz : ownerCount evm ≠ ⟨0⟩) :
    ownerCount (removeOwnerCountState evm) = UInt256.sub (ownerCount evm) ⟨1⟩ := by
  cases hacc : evm.accountMap.get? evm.executionEnv.codeOwner with
  | none =>
      simp only [Std.ExtTreeMap.get?_eq_getElem?] at hacc
      have hz : ownerCount evm = ⟨0⟩ := by
        simp [ownerCount, Solm.EVM.storageLoad, State.lookupAccount, hacc, Option.option]
      exact False.elim (hnz hz)
  | some acc =>
      simpa only [ownerCount, removeOwnerCountState, storageStore_executionEnv] using
        storageLoad_storageStore_same_present evm evm.executionEnv.codeOwner hacc ⟨3⟩
          (UInt256.sub (ownerCount evm) ⟨1⟩)

theorem safeRemoveOwnerLinkAccounts (evm : EVM.State) (prev key : UInt256) :
    (removeOwnerLinks evm prev key).accountMap =
      removeOwnerLinkAccounts evm.accountMap evm.executionEnv prev key := by
  simp only [removeOwnerLinks, writeOwnerLink, ownerLink, storageStore_executionEnv,
    storageLoad_eq_solcSlotWord, storageStore_accountMap]
  rfl

theorem safeRemoveOwnerLinksEnv (evm : EVM.State) (prev key : UInt256) :
    (removeOwnerLinks evm prev key).executionEnv = evm.executionEnv := by
  simp only [removeOwnerLinks, writeOwnerLink, storageStore_executionEnv]

theorem safeRemoveOwnerCountReach {I g s0 σ k C aw mem rdata} {threshold : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨6589⟩
      (UInt256.sub (solcSlotWordAt ⟨3⟩ σ I) ⟨1⟩ :: ⟨0⟩ :: ⟨3⟩ :: threshold :: R)
      mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024) (hperm : I.perm = true)
    (hle : threshold.toNat ≤ (UInt256.sub (solcSlotWordAt ⟨3⟩ σ I) ⟨1⟩).toNat) :
    ∃ k' C', RD safeBytecode I g s0 ⟨6617⟩ R mem aw rdata
      (removeOwnerCountAccounts σ I) k' C' := by
  exact safeRuntime_block_6589_taken hov hperm
    (by rw [ult_zero hle]; decide) (by jump_dest) h

theorem safeRemoveOwnerCountRevert {I g s0 σ k C aw mem rdata} {threshold : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨6589⟩
      (UInt256.sub (solcSlotWordAt ⟨3⟩ σ I) ⟨1⟩ :: ⟨0⟩ :: ⟨3⟩ :: threshold :: R)
      mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) (hperm : I.perm = true)
    (hle : ¬threshold.toNat ≤ (UInt256.sub (solcSlotWordAt ⟨3⟩ σ I) ⟨1⟩).toNat) :
    RDrev safeBytecode g s0 := by
  obtain ⟨_, _, h6601⟩ := safeRuntime_block_6589_fallthrough (by omega) hperm
    (by rw [ult_one (by omega)]; decide) h
  have h6898 := safeRuntime_block_6601
    (by simp only [safeRuntime_block_6589_fallthrough_stack]; omega) (by jump_dest) h6601
  exact safeRuntime_block_6898
    (by simp only [safeRuntime_block_6601_stack, safeRuntime_block_6589_fallthrough_stack,
      List.length_cons]; omega) h6898

theorem safeRemoveOwnerCountStatic {I g s0 σ k C aw mem rdata} {value : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨6589⟩ (value :: ⟨0⟩ :: ⟨3⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) (hperm : I.perm = false) :
    RDstatic safeBytecode g s0 := by
  have hstore := evm_run h with [jumpdest, swap2, dup3, swap1]
  exact hstore.sstoreStatic hperm (by native_decide) (by simp; omega)

theorem safeRemoveOwnerLinksTrace {I g s0 σ k C aw mem rdata} {prev key threshold : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨6627⟩ (threshold :: key :: prev :: R) mem aw rdata σ k C)
    (hov : R.length + 13 ≤ 1024) (hm : mem.size = 96)
    (hp : prev.toNat < EVM.addressModulus) (hc : key.toNat < EVM.addressModulus)
    (hperm : I.perm = true) :
    ∃ mem' ptr aw' k' C', RD safeBytecode I g s0 ⟨6700⟩
      (⟨0⟩ :: ptr :: key :: threshold :: key :: prev :: R) mem' aw' rdata
      (removeOwnerLinkAccounts σ I prev key) k' C' := by
  obtain ⟨aw', k', C', h'⟩ := safeRuntime_block_6627_packed hov hperm h
  simp only [safeRuntime_block_6627_stack, safeRuntime_block_6627_memory,
    safeAddressMask, solcAddrMask_clean_left hp, solcAddrMask_clean_left hc] at h'
  have hKey := twoWordHashMemMapSlot key (UInt256.ofNat 2) hm
  change keccakWord ⟨0⟩ (UInt256.ofNat 64)
    ((UInt256.ofNat 2).toByteArray.write 0
      (key.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) =
      mapSlot key ⟨2⟩ at hKey
  have hPrev := keyAfterSlotHash prev (UInt256.ofNat 2) (wordAt0Mem_size_96 key hm)
  change keccakWord ⟨0⟩ (UInt256.ofNat 64)
    (prev.toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0
      (key.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)
      (⟨0⟩ : UInt256).toNat 32) = mapSlot prev ⟨2⟩ at hPrev
  rw [hKey, hPrev] at h'
  have hfirst (word next : UInt256) :
      UInt256.lor (UInt256.land (UInt256.lnot solcAddrMask) word)
        (UInt256.land solcAddrMask next) =
      setAddressOffset0Word word (UInt256.land next solcAddrMask) := by
    rw [setAddressOffset0Word, maskTwice, u256_land_comm (UInt256.lnot solcAddrMask) word,
      u256_land_comm solcAddrMask next]
  have hsecond (word : UInt256) : UInt256.land (UInt256.lnot solcAddrMask) word =
      setAddressOffset0Word word ⟨0⟩ := by
    rw [setAddressOffset0Word, u256_land_zero_left, u256_lor_zero, u256_land_comm]
  simp only [hfirst] at h'
  rw [hsecond] at h'
  exact ⟨_, _, _, _, _, h'⟩

theorem safeRemoveOwnerThresholdUnchanged {I g s0 σ k C aw mem rdata}
    {ptr prev key threshold : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨6700⟩
      (⟨0⟩ :: ptr :: key :: threshold :: key :: prev :: ⟨664⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 8 ≤ 1024) (hperm : I.perm = true)
    (ht : solcSlotWordAt ⟨4⟩ σ I = threshold) :
    RDret safeBytecode g s0 σ ByteArray.empty := by
  obtain ⟨_, _, h6752⟩ := safeRuntime_block_6700_taken (by simp; omega) hperm
    (by change UInt256.eq (solcSlotWordAt ⟨4⟩ σ I) threshold ≠ ⟨0⟩
        rw [ht, uInt256_eq_self]; decide) (by jump_dest) h
  have h664 := safeRuntime_block_6752 (by omega) (by jump_dest) h6752
  exact safeRuntime_block_664 (by simp [safeRuntime_block_6752_stack]; omega) h664

theorem safeRemoveOwnerThresholdChanged {I g s0 σ k C aw mem rdata}
    {ptr prev key threshold ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨6700⟩
      (⟨0⟩ :: ptr :: key :: threshold :: key :: prev :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 8 ≤ 1024) (hperm : I.perm = true)
    (ht : solcSlotWordAt ⟨4⟩ σ I ≠ threshold) :
    ∃ aw' k' C', RD safeBytecode I g s0 ⟨3415⟩
      (threshold :: ⟨6752⟩ :: threshold :: key :: prev :: ret :: R) mem aw' rdata σ k' C' := by
  obtain ⟨aw', k', C', h6744⟩ := safeRuntime_block_6700_fallthrough_packed (by simp; omega) hperm
    (by
      change UInt256.eq (solcSlotWordAt ⟨4⟩ σ I) threshold = ⟨0⟩
      exact uInt256_eq_zero_of_ne (fun he ↦ ht (uInt256_eq_one_eq he))) h
  exact ⟨aw', _, _, safeRuntime_block_6744 (by simp; omega) (by jump_dest) h6744⟩

end Benchmarks.Safe
