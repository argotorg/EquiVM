import Benchmarks.Safe.ViaIR.RemoveOwnerSource
import Benchmarks.Safe.ViaIR.CheckedDecrement
import Benchmarks.Safe.ViaIR.Blocks.Runtime_005
import Benchmarks.Safe.ViaIR.Blocks.Runtime_006

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

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
        simp [ownerCount, Stele.EVM.storageLoad, State.lookupAccount, hacc, Option.option]
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

theorem safeRemoveOwnerCountReach {I g s0 σ k C aw mem rdata} {key prev threshold : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨649⟩
      (solcSlotWordAt ⟨3⟩ σ I :: key :: prev :: threshold :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) (hperm : I.perm = true)
    (hle : threshold.toNat ≤ (UInt256.sub (solcSlotWordAt ⟨3⟩ σ I) ⟨1⟩).toNat) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨663⟩ (key :: prev :: threshold :: R)
      mem aw rdata (removeOwnerCountAccounts σ I) k' C' := by
  obtain ⟨_, _, h663⟩ := safeRuntime_block_649_fallthrough hov hperm
    (by rw [lnot_zero_add]; exact ult_zero hle) h
  simpa only [safeRuntime_block_649_fallthrough_stack, lnot_zero_add] using ⟨_, _, h663⟩

theorem safeRemoveOwnerCountRevert {I g s0 σ k C aw mem rdata} {key prev threshold : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨649⟩
      (solcSlotWordAt ⟨3⟩ σ I :: key :: prev :: threshold :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) (hperm : I.perm = true)
    (hle : ¬threshold.toNat ≤ (UInt256.sub (solcSlotWordAt ⟨3⟩ σ I) ⟨1⟩).toNat) :
    RDrev fork safeBytecode g s0 := by
  obtain ⟨_, _, h874⟩ := safeRuntime_block_649_taken hov hperm
    (by rw [lnot_zero_add, ult_one (by omega)]; decide) (by jump_dest) h
  have h9502 := safeRuntime_block_874
    (by simp [safeRuntime_block_649_taken_stack]; omega) (by jump_dest) h874
  exact safeRuntime_block_9502 (by simp [safeRuntime_block_649_taken_stack]; omega) h9502

theorem safeRemoveOwnerCountStatic {I g s0 σ k C aw mem rdata}
    {count key prev threshold : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨649⟩ (count :: key :: prev :: threshold :: R)
      mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) (hperm : I.perm = false) :
    RDstatic fork safeBytecode g s0 := by
  have hstore := evm_run h with [dup4, swap1, push0, not, add, dup1, push1 ⟨3⟩]
  exact hstore.sstoreStatic hperm (by native_decide) (by simp; omega)

theorem safeRemoveOwnerLinksTrace {I g s0 σ k C aw mem rdata} {prev key threshold : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨672⟩ (key :: prev :: threshold :: ⟨0⟩ :: R)
      mem aw rdata σ k C)
    (hov : R.length + 13 ≤ 1024) (hm : mem.size = 96)
    (hp : prev.toNat < EVM.addressModulus) (hc : key.toNat < EVM.addressModulus)
    (hperm : I.perm = true) :
    ∃ mem' aw' k' C', RD fork safeBytecode I g s0 ⟨748⟩
      (key :: threshold :: ⟨0⟩ :: R) mem' aw' rdata
      (removeOwnerLinkAccounts σ I prev key) k' C' := by
  obtain ⟨aw', k', C', h'⟩ := safeRuntime_block_672_packed (by omega) hperm h
  simp only [safeRuntime_block_672_stack, safeRuntime_block_672_memory,
    safeAddressMask, solcAddrMask_clean_left hp, solcAddrMask_clean_left hc] at h'
  have hKey := twoWordHashMemMapSlot key (UInt256.ofNat 2) hm
  have hPrev := twoWordHashMemMapSlot prev (UInt256.ofNat 2)
    (twoWordHashMem_size_96 key (UInt256.ofNat 2) hm)
  have hKey' := twoWordHashMemMapSlot key (UInt256.ofNat 2)
    (twoWordHashMem_size_96 prev (UInt256.ofNat 2)
      (twoWordHashMem_size_96 key (UInt256.ofNat 2) hm))
  dsimp only [twoWordHashMem, wordAt32Mem, wordAt0Mem] at hKey hPrev hKey'
  simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl] at h'
  rw [hKey, hPrev, hKey'] at h'
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
  have hstore := evm_run h' with [swap1, swap2]
  obtain ⟨_, _, h748⟩ := RD.sstore hstore hperm (by native_decide) (by simp; omega)
  exact ⟨_, _, _, _, h748⟩

-- Split the generated block after the second store so the source and EVM states align.
theorem safeRemoveOwnerThresholdCheck {I g s0 σ k C aw mem rdata}
    {key threshold : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨748⟩ (key :: threshold :: ⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) (hperm : I.perm = true) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨792⟩
      (⟨796⟩ :: UInt256.sub (solcSlotWordAt ⟨4⟩ σ I) threshold :: threshold :: ⟨0⟩ :: R)
      mem aw' rdata σ k' C' := by
  have r4 := h.pushConst
    ⟨112549260719532661292031762456511781745355494859329508612328448226810028203695⟩
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r6 := evm_run r4 with [dup4, dup1]
  have r7 := RD.genLog2 r6 (by native_decide) hperm (by evm_ov)
  have r9 := evm_run r7 with [dup1, push1 ⟨4⟩]
  obtain ⟨_, _, r10⟩ := RD.sload r9 (by native_decide) (by evm_ov)
  have r12 := evm_run r10 with [sub, push2 ⟨796⟩]
  exact ⟨_, _, _, r12⟩

theorem safeRemoveOwnerThresholdUnchanged {I g s0 σ k C aw mem rdata}
    {key threshold : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨748⟩ (key :: threshold :: ⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) (hperm : I.perm = true)
    (ht : solcSlotWordAt ⟨4⟩ σ I = threshold) :
    RDret fork safeBytecode g s0 σ ByteArray.empty := by
  obtain ⟨_, _, _, h792⟩ := safeRemoveOwnerThresholdCheck h hov hperm
  have h793 := h792.jumpiNT (by native_decide) (u256_sub_eq_zero_iff_eq.mpr ht) (by evm_ov)
  simpa only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, byteArray_readWithPadding_zero] using
    safeRuntime_block_793 (by simp; omega) h793

theorem safeRemoveOwnerThresholdChanged {I g s0 σ k C aw mem rdata}
    {key threshold : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨748⟩ (key :: threshold :: ⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) (hperm : I.perm = true)
    (ht : solcSlotWordAt ⟨4⟩ σ I ≠ threshold) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨796⟩ (threshold :: ⟨0⟩ :: R)
      mem aw' rdata σ k' C' := by
  obtain ⟨_, _, _, h792⟩ := safeRemoveOwnerThresholdCheck h hov hperm
  exact ⟨_, _, _, h792.jumpiT (by native_decide) (u256_sub_ne_zero_of_ne ht)
    (by jump_dest) (by evm_ov)⟩

theorem safeRemoveOwnerThresholdTrace {I g s0 σ k C aw mem rdata} {value : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨804⟩ (value :: ⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) (hperm : I.perm = true)
    (hle : value.toNat ≤ (solcSlotWordAt ⟨3⟩ σ I).toNat) (hnz : value ≠ ⟨0⟩) :
    RDret fork safeBytecode g s0 (sstoreAccountMap I.codeOwner σ ⟨4⟩ value) ByteArray.empty := by
  obtain ⟨_, _, h814⟩ := safeRuntime_block_804_fallthrough (by simp; omega) (ugt_zero hle) h
  have h820 := safeRuntime_block_814_fallthrough (by simp; omega)
    (isZero_eq_zero_of_ne hnz) h814
  simpa only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, byteArray_readWithPadding_zero] using
    safeRuntime_block_820 hov hperm h820

theorem safeRemoveOwnerThresholdTooLarge {I g s0 σ k C aw mem rdata} {value : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨804⟩ (value :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024)
    (hle : ¬ value.toNat ≤ (solcSlotWordAt ⟨3⟩ σ I).toNat) : RDrev fork safeBytecode g s0 := by
  obtain ⟨_, _, h874⟩ := safeRuntime_block_804_taken (by omega)
    (by
      change UInt256.gt value (solcSlotWordAt ⟨3⟩ σ I) ≠ ⟨0⟩
      rw [ugt_one (by omega)]; decide) (by jump_dest) h
  have h9502 := safeRuntime_block_874 (by simp; omega) (by jump_dest) h874
  exact safeRuntime_block_9502 (by simp; omega) h9502

theorem safeRemoveOwnerThresholdZero {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨804⟩ (⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  obtain ⟨_, _, h814⟩ := safeRuntime_block_804_fallthrough (by omega)
    (ugt_zero (show (⟨0⟩ : UInt256).toNat ≤ (solcSlotWordAt ⟨3⟩ σ I).toNat
      from Nat.zero_le _)) h
  have h869 := safeRuntime_block_814_taken (by omega) (by decide) (by jump_dest) h814
  have h9547 := safeRuntime_block_869 (by simp; omega) (by jump_dest) h869
  exact safeRuntime_block_9547 (by simp; omega) h9547

end Benchmarks.Safe.ViaIR
