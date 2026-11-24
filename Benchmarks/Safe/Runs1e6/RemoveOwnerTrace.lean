import Benchmarks.Safe.Runs1e6.RemoveOwnerSource
import Benchmarks.Safe.Runs1e6.CheckedDecrement
import Benchmarks.Safe.Runs1e6.Blocks.Runtime_006
import Benchmarks.Safe.Runs1e6.Blocks.Runtime_028
import Benchmarks.Safe.Runs1e6.Blocks.Runtime_029
import Benchmarks.Safe.Runs1e6.Blocks.Runtime_030

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.Runs1e6.RuntimeBlocks

namespace Benchmarks.Safe.Runs1e6

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

theorem safeRemoveOwnerCountReach {I g s0 σ k C aw mem rdata} {threshold : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7990⟩
      (UInt256.sub (solcSlotWordAt ⟨3⟩ σ I) ⟨1⟩ :: ⟨0⟩ :: ⟨3⟩ :: threshold :: R)
      mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024) (hperm : I.perm = true)
    (hle : threshold.toNat ≤ (UInt256.sub (solcSlotWordAt ⟨3⟩ σ I) ⟨1⟩).toNat) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨8042⟩ R mem aw rdata
      (removeOwnerCountAccounts σ I) k' C' := by
  exact safeRuntime_block_7990_taken hov hperm
    (by rw [ult_zero hle]; decide) (by jump_dest) h

theorem safeRemoveOwnerCountRevert {I g s0 σ k C aw mem rdata} {threshold : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7990⟩
      (UInt256.sub (solcSlotWordAt ⟨3⟩ σ I) ⟨1⟩ :: ⟨0⟩ :: ⟨3⟩ :: threshold :: R)
      mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) (hperm : I.perm = true)
    (hle : ¬threshold.toNat ≤ (UInt256.sub (solcSlotWordAt ⟨3⟩ σ I) ⟨1⟩).toNat) :
    RDrev fork safeBytecode g s0 := by
  obtain ⟨_, _, h6601⟩ := safeRuntime_block_7990_fallthrough (by omega) hperm
    (by rw [ult_one (by omega)]; decide) h
  have h6898 := safeRuntime_block_8002
    (by simp only [safeRuntime_block_7990_fallthrough_stack]; omega) (by jump_dest) h6601
  exact safeRuntime_block_8421
    (by simp only [safeRuntime_block_8002_stack, safeRuntime_block_7990_fallthrough_stack,
      List.length_cons]; omega) h6898

theorem safeRemoveOwnerCountStatic {I g s0 σ k C aw mem rdata} {value : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7990⟩ (value :: ⟨0⟩ :: ⟨3⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) (hperm : I.perm = false) :
    RDstatic fork safeBytecode g s0 := by
  have hstore := evm_run h with [jumpdest, swap2, dup3, swap1]
  exact hstore.sstoreStatic hperm (by native_decide) (by simp; omega)

theorem safeRemoveOwnerLinksTrace {I g s0 σ k C aw mem rdata} {prev key threshold : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8052⟩ (threshold :: key :: prev :: R) mem aw rdata σ k C)
    (hov : R.length + 13 ≤ 1024) (hm : mem.size = 96)
    (hp : prev.toNat < EVM.addressModulus) (hc : key.toNat < EVM.addressModulus)
    (hperm : I.perm = true) :
    ∃ mem' ptr aw' k' C', RD fork safeBytecode I g s0 ⟨8162⟩
      (⟨0⟩ :: ptr :: key :: threshold :: key :: prev :: R) mem' aw' rdata
      (removeOwnerLinkAccounts σ I prev key) k' C' := by
  -- The generated summary now includes the event and threshold branch. Stop at the
  -- existing link-update checkpoint so its callers retain their decomposition.
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push20 solcAddrMask (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.and (by native_decide) (by evm_ov)
  have r6 := r5.push0 (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := RD.genMstore r8 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r12 := RD.genMstore r11 (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r14 := r13.dup1 (by native_decide) (by evm_ov)
  have r15 := r14.dup3 (by native_decide) (by evm_ov)
  have r16 := RD.genKeccak256 r15 (by native_decide) (by evm_ov)
  have r17 := r16.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r18⟩ := RD.sload r17 (by native_decide) (by evm_ov)
  have r19 := r18.dup9 (by native_decide) (by evm_ov)
  have r20 := r19.dup7 (by native_decide) (by evm_ov)
  have r21 := r20.and (by native_decide) (by evm_ov)
  have r22 := r21.dup5 (by native_decide) (by evm_ov)
  have r23 := RD.genMstore r22 (by native_decide) (by evm_ov)
  have r24 := r23.dup3 (by native_decide) (by evm_ov)
  have r25 := r24.dup5 (by native_decide) (by evm_ov)
  have r26 := RD.genKeccak256 r25 (by native_decide) (by evm_ov)
  have r27 := r26.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r28⟩ := RD.sload r27 (by native_decide) (by evm_ov)
  have r29 := r28.swap2 (by native_decide) (by evm_ov)
  have r30 := r29.swap1 (by native_decide) (by evm_ov)
  have r31 := r30.swap7 (by native_decide) (by evm_ov)
  have r32 := r31.and (by native_decide) (by evm_ov)
  have r33 := r32.pushConst (UInt256.lnot solcAddrMask)
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r34 := r33.swap2 (by native_decide) (by evm_ov)
  have r35 := r34.dup3 (by native_decide) (by evm_ov)
  have r36 := r35.and (by native_decide) (by evm_ov)
  have r37 := r36.or (by native_decide) (by evm_ov)
  have r38 := r37.swap1 (by native_decide) (by evm_ov)
  have r39 := r38.swap6 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r40⟩ := RD.sstore r39 hperm (by native_decide) (by evm_ov)
  have r41 := r40.dup4 (by native_decide) (by evm_ov)
  have r42 := r41.dup4 (by native_decide) (by evm_ov)
  have r43 := RD.genMstore r42 (by native_decide) (by evm_ov)
  have r44 := r43.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r45⟩ := RD.sload r44 (by native_decide) (by evm_ov)
  have r46 := r45.swap1 (by native_decide) (by evm_ov)
  have r47 := r46.swap5 (by native_decide) (by evm_ov)
  have r48 := r47.and (by native_decide) (by evm_ov)
  have r49 := r48.swap1 (by native_decide) (by evm_ov)
  have r50 := r49.swap4 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r51⟩ := RD.sstore r50 hperm (by native_decide) (by evm_ov)
  have r52 := r51.swap2 (by native_decide) (by evm_ov)
  have r53 := RD.genMload r52 (by native_decide) (by evm_ov)
  have r54 := r53.swap1 (by native_decide) (by evm_ov)
  have r55 := r54.swap2 (by native_decide) (by evm_ov)
  have h' := RD.normalizePC (pc' := (⟨8162⟩ : UInt256)) r55 (by native_decide)
  simp only [solcAddrMask_clean_left hp, solcAddrMask_clean_left hc] at h'
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
    (h : RD fork safeBytecode I g s0 ⟨8162⟩
      (⟨0⟩ :: ptr :: key :: threshold :: key :: prev :: ⟨664⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 8 ≤ 1024) (hperm : I.perm = true)
    (ht : solcSlotWordAt ⟨4⟩ σ I = threshold) :
    RDret fork safeBytecode g s0 σ ByteArray.empty := by
  have htopic := h.pushConst
    ⟨112549260719532661292031762456511781745355494859329508612328448226810028203695⟩
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by simp; omega)
  have hlog := evm_run htopic with [swap2]
  have hlog := RD.genLog2 hlog (by native_decide) hperm (by simp; omega)
  have hload := evm_run hlog with [dup1, push1 ⟨4⟩]
  obtain ⟨_, _, hload⟩ := RD.sload hload (by native_decide) (by simp; omega)
  have hcond := evm_run hload with [eq, push2 ⟨8214⟩]
  have h6752 := hcond.jumpiT (by native_decide)
    (by change UInt256.eq (solcSlotWordAt ⟨4⟩ σ I) threshold ≠ ⟨0⟩
        rw [ht, uInt256_eq_self]; decide) (by jump_dest) (by simp; omega)
  have h664 := safeRuntime_block_8214 (by omega) (by jump_dest) h6752
  exact safeRuntime_block_664 (by simp [safeRuntime_block_8214_stack]; omega) h664

theorem safeRemoveOwnerThresholdChanged {I g s0 σ k C aw mem rdata}
    {ptr prev key threshold ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8162⟩
      (⟨0⟩ :: ptr :: key :: threshold :: key :: prev :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 8 ≤ 1024) (hperm : I.perm = true)
    (ht : solcSlotWordAt ⟨4⟩ σ I ≠ threshold) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨4000⟩
      (threshold :: ⟨8214⟩ :: threshold :: key :: prev :: ret :: R) mem aw' rdata σ k' C' := by
  have htopic := h.pushConst
    ⟨112549260719532661292031762456511781745355494859329508612328448226810028203695⟩
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by simp; omega)
  have hlog := evm_run htopic with [swap2]
  have hlog := RD.genLog2 hlog (by native_decide) hperm (by simp; omega)
  have hload := evm_run hlog with [dup1, push1 ⟨4⟩]
  obtain ⟨_, _, hload⟩ := RD.sload hload (by native_decide) (by simp; omega)
  have hcond := evm_run hload with [eq, push2 ⟨8214⟩]
  have h6744 := hcond.jumpiNT (by native_decide)
    (by change UInt256.eq (solcSlotWordAt ⟨4⟩ σ I) threshold = ⟨0⟩
        exact uInt256_eq_zero_of_ne (fun he ↦ ht (uInt256_eq_one_eq he))) (by simp; omega)
  exact ⟨_, _, _, safeRuntime_block_8206 (by simp; omega) (by jump_dest) h6744⟩

end Benchmarks.Safe.Runs1e6
