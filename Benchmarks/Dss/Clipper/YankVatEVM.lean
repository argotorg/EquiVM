import Benchmarks.Dss.Clipper.YankEVM
import Benchmarks.Dss.Clipper.Invalid
import Reasoning.MemCascade

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

abbrev clipperYankVatTarget (v : ClipperImmutables) : UInt256 :=
  UInt256.land solcAddrMask (EVM.Word.ofNat (↑v.vat : Nat))

noncomputable abbrev clipperYankVatFluxBaseMem (v : ClipperImmutables)
    (I : ExecutionEnv) (tab : UInt256) : ByteArray :=
  twoWordHashMem (clipperYankArgWord I) ⟨12⟩
    (clipperDogDigsCalldataMem v tab (clipperYankSalesHashMemRefresh I))

theorem clipperYankPatchesWindowDisjoint32PostVat (v : ClipperImmutables)
    (lo hi : Nat) (hlo : 2527 ≤ lo) (hhi : hi ≤ 2540) :
    PatchesWindowDisjoint32 lo hi (patches v) := by
  unfold PatchesWindowDisjoint32 PatchWindowDisjoint32 patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      try omega
  | some bs =>
      simp [hIlk]
      try omega

theorem clipperYankDecodePostVat (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {pc : UInt256} {res : Operation × Option (UInt256 × Nat)}
    (hlo : 2527 ≤ pc.toNat)
    (hhi : pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2) ≤ 2540)
    (hdec : decode clipperBytecode pc = some res) :
    decode code pc = some res :=
  patchRuntime_decode_disjoint_of_decode_res hpatch
    (clipperYankPatchesWindowDisjoint32PostVat v pc.toNat (pc.toNat + 1) hlo
      (by omega))
    (clipperYankPatchesWindowDisjoint32PostVat v (pc.toNat + 1)
      (pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2)) (by omega)
      hhi)
    hdec
    (by
      have hle :
          pc.toNat + 1 ≤
            pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2) := by
        omega
      exact Nat.lt_of_le_of_lt (Nat.le_trans hle hhi) (by norm_num))
    (by exact Nat.lt_of_le_of_lt hhi (by norm_num))

theorem clipperYankJumpDest8274 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨8274⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperYankJumpDest8296 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨8296⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperYankJumpDest8348 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨8348⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperYankJumpDest8379 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨8379⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperYankJumpDest8390 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨8390⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperYankJumpDest2540 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨2540⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 3000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperYankJumpDest8460 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨8460⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

macro "clipper_yank_post_decode" : tactic =>
  `(tactic| exact clipperYankDecodePostVat _ (by assumption)
      (by native_decide) (by native_decide) (by native_decide))

theorem clipperYankPatchesWindowDisjoint32PostRemoveReturn (v : ClipperImmutables)
    (lo hi : Nat) (hlo : 2540 ≤ lo) (hhi : hi ≤ 2599) :
    PatchesWindowDisjoint32 lo hi (patches v) := by
  unfold PatchesWindowDisjoint32 PatchWindowDisjoint32 patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      try omega
  | some bs =>
      simp [hIlk]
      try omega

theorem clipperYankDecodePostRemoveReturn (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {pc : UInt256} {res : Operation × Option (UInt256 × Nat)}
    (hlo : 2540 ≤ pc.toNat)
    (hhi : pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2) ≤ 2599)
    (hdec : decode clipperBytecode pc = some res) :
    decode code pc = some res :=
  patchRuntime_decode_disjoint_of_decode_res hpatch
    (clipperYankPatchesWindowDisjoint32PostRemoveReturn v pc.toNat (pc.toNat + 1) hlo
      (by omega))
    (clipperYankPatchesWindowDisjoint32PostRemoveReturn v (pc.toNat + 1)
      (pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2)) (by omega)
      hhi)
    hdec
    (by
      have hle :
          pc.toNat + 1 ≤
            pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2) := by
        omega
      exact Nat.lt_of_le_of_lt (Nat.le_trans hle hhi) (by norm_num))
    (by exact Nat.lt_of_le_of_lt hhi (by norm_num))

macro "clipper_yank_post_remove_decode" : tactic =>
  `(tactic| exact clipperYankDecodePostRemoveReturn _ (by assumption)
      (by native_decide) (by native_decide) (by native_decide))

theorem clipperYankPatchesWindowDisjoint32Remove (v : ClipperImmutables)
    (lo hi : Nat) (hlo : 8274 ≤ lo) (hhi : hi ≤ 8461) :
    PatchesWindowDisjoint32 lo hi (patches v) := by
  unfold PatchesWindowDisjoint32 PatchWindowDisjoint32 patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      try omega
  | some bs =>
      simp [hIlk]
      try omega

theorem clipperYankDecodeRemove (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {pc : UInt256} {res : Operation × Option (UInt256 × Nat)}
    (hlo : 8274 ≤ pc.toNat)
    (hhi : pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2) ≤ 8461)
    (hdec : decode clipperBytecode pc = some res) :
    decode code pc = some res :=
  patchRuntime_decode_disjoint_of_decode_res hpatch
    (clipperYankPatchesWindowDisjoint32Remove v pc.toNat (pc.toNat + 1) hlo
      (by omega))
    (clipperYankPatchesWindowDisjoint32Remove v (pc.toNat + 1)
      (pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2)) (by omega)
      hhi)
    hdec
    (by
      have hle :
          pc.toNat + 1 ≤
            pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2) := by
        omega
      exact Nat.lt_of_le_of_lt (Nat.le_trans hle hhi) (by norm_num))
    (by exact Nat.lt_of_le_of_lt hhi (by norm_num))

macro "clipper_yank_remove_decode" : tactic =>
  `(tactic| exact clipperYankDecodeRemove _ (by assumption)
      (by native_decide) (by native_decide) (by native_decide))

theorem clipperYankLenAddLnotZero_eq_subOne (Z : UInt256) :
    Z + UInt256.lnot ⟨0⟩ = UInt256.sub Z ⟨1⟩ := by
  apply u256_inj
  have hlnot : (UInt256.lnot ⟨0⟩).toNat = 2 ^ 256 - 1 := by
    unfold UInt256.lnot
    decide
  have h1 : (⟨1⟩ : UInt256).toNat = 1 := by decide
  have hZ : Z.toNat < UInt256.size := Z.val.isLt
  rw [show UInt256.size = 2 ^ 256 from by decide] at hZ
  rcases Nat.eq_zero_or_pos Z.toNat with hz | hz
  · rw [uadd_toNat, hlnot, usub_toNat_underflow (by rw [hz, h1]; omega), hz, h1,
      show UInt256.size = 2 ^ 256 from by decide]
    omega
  · rw [uadd_toNat, hlnot, usub_toNat (by rw [h1]; omega), h1,
      show UInt256.size = 2 ^ 256 from by decide]
    omega

theorem clipperYankNonzeroLenPredLt (len : UInt256) (hlen : len ≠ ⟨0⟩) :
    UInt256.lt (len + UInt256.lnot ⟨0⟩) len = ⟨1⟩ := by
  rw [clipperYankLenAddLnotZero_eq_subOne]
  apply ult_one
  have hpos : 0 < len.toNat := by
    by_contra hnot
    have hzeroNat : len.toNat = 0 := by omega
    exact hlen (uint256_toNat_eq_zero hzeroNat)
  rw [usub_toNat]
  · rw [show (⟨1⟩ : UInt256).toNat = 1 from by native_decide]
    omega
  · rw [show (⟨1⟩ : UInt256).toNat = 1 from by native_decide]
    exact Nat.succ_le_of_lt hpos

theorem clipperYankVatFluxBaseMem_size (v : ClipperImmutables) (I : ExecutionEnv)
    (tab : UInt256) :
    (clipperYankVatFluxBaseMem v I tab).size = 196 := by
  unfold clipperYankVatFluxBaseMem twoWordHashMem wordAt32Mem wordAt0Mem
  change
    (writeCascade (clipperDogDigsCalldataMem v tab (clipperYankSalesHashMemRefresh I))
      [(0, clipperYankArgWord I), (32, (⟨12⟩ : UInt256))]).size = 196
  rw [writeCascade_size_of_base
    (clipperDogDigsCalldataMem v tab (clipperYankSalesHashMemRefresh I))
    [(0, clipperYankArgWord I), (32, (⟨12⟩ : UInt256))] rfl
    (by simp [WriteGapsOk])
    (by
      simp [writeCascadeSize]
      rw [clipperDogDigsCalldataMem_size v tab (clipperYankSalesHashMemRefresh_size I)])]
  norm_num

theorem clipperYankVatFluxBaseMem_read64 (v : ClipperImmutables) (I : ExecutionEnv)
    (tab : UInt256) :
    (clipperYankVatFluxBaseMem v I tab).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperYankVatFluxBaseMem twoWordHashMem wordAt32Mem wordAt0Mem
  change
    (writeCascade (clipperDogDigsCalldataMem v tab (clipperYankSalesHashMemRefresh I))
      [(0, clipperYankArgWord I), (32, (⟨12⟩ : UInt256))]).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩
  rw [writeCascade_read_preserved_of_base
    (clipperDogDigsCalldataMem v tab (clipperYankSalesHashMemRefresh I))
    [(0, clipperYankArgWord I), (32, (⟨12⟩ : UInt256))] rfl]
  · exact clipperDogDigsCalldataMem_read64 v tab
      (clipperYankSalesHashMemRefresh_size I) (clipperYankSalesHashMemRefresh_read64 I)
  · simp [WindowDisjointFromWrites]
    rw [clipperDogDigsCalldataMem_size v tab (clipperYankSalesHashMemRefresh_size I)]
    omega

theorem clipperYankTwoWordHashMem_read0_of_ge {mem : ByteArray} (key slot : UInt256)
    (_hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 0 32 = UInt256.toByteArray key := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by
        have hword0 : 32 ≤ (wordAt0Mem key mem).size := by
          simpa [wordAt0Mem] using
            toByteArray_write_size_ge_off_add32 key mem 0 (by simp)
        omega)
      (by omega)]
  unfold wordAt0Mem
  rw [write32_read_back _ _ 0 (by rw [toByteArray_size]) (by omega)]
  rw [toByteArray_extract_all]

theorem clipperYankTwoWordHashMem_read32_of_ge {mem : ByteArray} (key slot : UInt256)
    (_hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 32 32 = UInt256.toByteArray slot := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_back _ _ 32 (by rw [toByteArray_size])
      (by
        have hword0 : 32 ≤ (wordAt0Mem key mem).size := by
          simpa [wordAt0Mem] using
            toByteArray_write_size_ge_off_add32 key mem 0 (by simp)
        omega)]
  rw [toByteArray_extract_all]

set_option maxHeartbeats 800000 in
theorem clipperYankTwoWordHashMem_read0_64_of_ge {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [byteArray_readWithPadding_split _ 0 32 32 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by
        have hge : 64 ≤ (twoWordHashMem key slot mem).size := by
          unfold twoWordHashMem wordAt32Mem
          have hword0 : 32 ≤ (wordAt0Mem key mem).size := by
            simpa [wordAt0Mem] using
              toByteArray_write_size_ge_off_add32 key mem 0 (by simp)
          simpa using
            toByteArray_write_size_ge_off_add32 slot (wordAt0Mem key mem) 32
              (lt_usize (32 - (wordAt0Mem key mem).size) (by omega))
        exact hge)]
  rw [clipperYankTwoWordHashMem_read0_of_ge key slot hmem,
    clipperYankTwoWordHashMem_read32_of_ge key slot hmem]

theorem clipperYankVatFluxBaseMem_solcMappingSlot (v : ClipperImmutables)
    (I : ExecutionEnv) (tab : UInt256) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((clipperYankVatFluxBaseMem v I tab).readWithPadding 0 64))) =
      clipperYankSalesBaseSlot I := by
  rw [clipperYankVatFluxBaseMem, clipperYankSalesBaseSlot_eq I]
  rw [clipperYankTwoWordHashMem_read0_64_of_ge]
  · unfold solcMappingSlot
    exact mappingSlot_single (clipperYankArgWord I) ⟨12⟩
  · have hsize :=
      clipperDogDigsCalldataMem_size v tab (clipperYankSalesHashMemRefresh_size I)
    omega

theorem clipperYankVatTargetAddress (v : ClipperImmutables) :
    AccountAddress.ofUInt256 (clipperYankVatTarget v) = v.vat := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  have hvatWordToNat : (EVM.Word.ofNat (↑v.vat : Nat)).toNat = ↑v.vat := by
    simp [EVM.Word.ofNat, UInt256.ofNat, UInt256.toNat, Fin.ofNat]
    exact Nat.mod_eq_of_lt (lt_of_lt_of_le v.vat.isLt (by decide))
  have hclean :
      UInt256.land solcAddrMask (EVM.Word.ofNat (↑v.vat : Nat)) =
        EVM.Word.ofNat (↑v.vat : Nat) := by
    exact solcAddrMask_clean_left (w := EVM.Word.ofNat (↑v.vat : Nat)) (by
      rw [hvatWordToNat]
      simp [EVM.addressModulus, EVM.twoPow, AccountAddress.size])
  simpa [clipperYankVatTarget, hclean] using clipperAddressOfWordOfNat v.vat

theorem clipperYankEVMAddressAccountAddress (a : AccountAddress) :
    EVM.address a = a := by
  apply Fin.ext
  simp [EVM.address, EVM.uintN]
  exact Nat.mod_eq_of_lt (by simp [EVM.twoPow, AccountAddress.size])

set_option maxHeartbeats 2000000 in
theorem RD.clipperYankVatFluxExtcodesizeGuard {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {k C : ℕ} {sel dogTarget tab : UInt256} {rdata : ByteArray}
    (h : RD code ee g s0 ⟨2335⟩
      (⟨196⟩ :: clipperDogDigsSelectorWord :: dogTarget ::
        clipperYankArgWord ee :: ⟨502⟩ :: [sel])
      (clipperDogDigsCalldataMem v tab (clipperYankSalesHashMemRefresh ee))
      (UInt256.ofNat 7) rdata (cA, σ) k C) :
    ∃ k' C', RD code ee g s0 ⟨2495⟩
      (clipperYankVatTarget v :: clipperYankVatTarget v :: ⟨0⟩ :: ⟨128⟩ ::
        ⟨132⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨260⟩ :: clipperVatFluxSelectorWord ::
        clipperYankVatTarget v :: clipperYankArgWord ee :: ⟨502⟩ :: [sel])
      (clipperVatFluxCalldataMem v ee (clipperYankSalesLotWord σ ee)
        (clipperYankVatFluxBaseMem v ee tab))
      (UInt256.ofNat 9) rdata (cA, σ) k' C' := by
  rcases v.ilk_wf with ⟨ilkBs, hilk, hlen⟩
  let ilkWord : UInt256 := EVM.Word.ofNat (fromBytesBigEndian ilkBs)
  let vatWord : UInt256 := EVM.Word.ofNat (↑v.vat : Nat)
  have hslot := clipperYankVatFluxBaseMem_solcMappingSlot v ee tab
  have hbaseMload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (clipperYankVatFluxBaseMem v ee tab).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((clipperYankVatFluxBaseMem v ee tab).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue
      (mem := clipperYankVatFluxBaseMem v ee tab) (aw := UInt256.ofNat 7)
      (by rw [clipperYankVatFluxBaseMem_size v ee tab]; decide)
      (by decide) (clipperYankVatFluxBaseMem_read64 v ee tab)
  have hcallMload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (clipperVatFluxCalldataMem v ee (clipperYankSalesLotWord σ ee)
              (clipperYankVatFluxBaseMem v ee tab)).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((clipperVatFluxCalldataMem v ee (clipperYankSalesLotWord σ ee)
              (clipperYankVatFluxBaseMem v ee tab)).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    clipperVatFluxCalldataMem_mload64 v ee (clipperYankSalesLotWord σ ee)
      (clipperYankVatFluxBaseMem_size v ee tab)
      (clipperYankVatFluxBaseMem_read64 v ee tab)
  have rd2340pre := evm_run h with [
    raw pop (by clipper_yank_decode) (by evm_ov),
    raw pop (by clipper_yank_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_yank_decode) (by evm_ov),
    raw dup3 (by clipper_yank_decode) (by evm_ov),
    raw dup2 (by clipper_yank_decode) (by evm_ov)]
  have rd2341 := rd2340pre.mstore 0
    (wordAt0Mem (clipperYankArgWord ee)
      (clipperDogDigsCalldataMem v tab (clipperYankSalesHashMemRefresh ee)))
    (UInt256.ofNat 7) (by clipper_yank_decode) mem_cost (by rfl)
    (by native_decide) (by evm_ov)
  have rd2346pre := evm_run rd2341 with [
    raw push1 ⟨12⟩ (by clipper_yank_decode) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_yank_decode) (by evm_ov)]
  have rd2347 := rd2346pre.mstore 0 (clipperYankVatFluxBaseMem v ee tab)
    (UInt256.ofNat 7) (by clipper_yank_decode) mem_cost (by rfl)
    (by native_decide) (by evm_ov)
  have rd2351pre := evm_run rd2347 with [
    raw push1 ⟨64⟩ (by clipper_yank_decode) (by evm_ov),
    raw dup1 (by clipper_yank_decode) (by evm_ov),
    raw dup3 (by clipper_yank_decode) (by evm_ov)]
  have rd2352 := rd2351pre.keccak256 0 (clipperYankSalesBaseSlot ee)
    (UInt256.ofNat 7) (by clipper_yank_decode) mem_cost hslot
    (by native_decide) (by evm_ov)
  have rd2355pre := evm_run rd2352 with [
    raw push1 ⟨2⟩ (by clipper_yank_decode) (by evm_ov),
    raw add (by clipper_yank_decode) (by evm_ov)]
  rw [u256_add_comm ⟨2⟩ (clipperYankSalesBaseSlot ee)] at rd2355pre
  obtain ⟨k2356, C2356, rd2356raw⟩ :=
    rd2355pre.sload (by clipper_yank_decode) (by evm_ov)
  have rd2356 : RD code ee g s0 ⟨2356⟩
      (clipperYankSalesLotWord σ ee :: ⟨64⟩ :: ⟨0⟩ :: dogTarget ::
        clipperYankArgWord ee :: ⟨502⟩ :: [sel])
      (clipperYankVatFluxBaseMem v ee tab) (UInt256.ofNat 7) rdata
      (cA, σ) k2356 C2356 := by
    simpa [clipperYankSalesLotWord, clipperYankSalesLotSlot, solcSlotWord] using
      rd2356raw
  have rd2357pre := evm_run rd2356 with [
    raw dup2 (by clipper_yank_decode) (by evm_ov)]
  have rd2358 := rd2357pre.mload 0 ⟨128⟩ (UInt256.ofNat 7)
    (by clipper_yank_decode) mem_cost hbaseMload64 (by native_decide) (by evm_ov)
  have rd2367pre := evm_run rd2358 with [
    raw push4 clipperVatFluxSelectorSeed (by clipper_yank_decode) (by evm_ov),
    raw push1 ⟨225⟩ (by clipper_yank_decode) (by evm_ov),
    raw shl (by clipper_yank_decode) (by evm_ov),
    raw dup2 (by clipper_yank_decode) (by evm_ov)]
  rw [show UInt256.shiftLeft clipperVatFluxSelectorSeed ⟨225⟩ =
    clipperVatFluxSelectorShifted from by native_decide] at rd2367pre
  have rd2368 := rd2367pre.mstore 0
    (clipperVatFluxSelectorMem (clipperYankVatFluxBaseMem v ee tab))
    (UInt256.ofNat 7) (by clipper_yank_decode) mem_cost (by rfl)
    (by native_decide) (by evm_ov)
  have rd2401 := rd2368.pushConst ilkWord (width := 32) (op := .PUSH32)
    (by decide)
    (by simpa [ilkWord] using clipperYankIlkPush32Decode2368 v hpatch hilk hlen)
    (by evm_ov)
  have rd2405pre := evm_run rd2401 with [
    raw push1 ⟨4⟩ (by clipper_yank_decode) (by evm_ov),
    raw dup3 (by clipper_yank_decode) (by evm_ov),
    raw add (by clipper_yank_decode) (by evm_ov)]
  rw [show (⟨128⟩ : UInt256) + ⟨4⟩ = ⟨132⟩ from by native_decide] at rd2405pre
  have rd2406 := rd2405pre.mstore 0
    (clipperVatFluxIlkMem v (clipperYankVatFluxBaseMem v ee tab))
    (UInt256.ofNat 7) (by clipper_yank_decode) mem_cost
    (by
      rw [show (⟨132⟩ : UInt256).toNat = 132 from by decide]
      simp [clipperVatFluxIlkMem, clipperYankIlkWord, hilk, ilkWord])
    (by native_decide) (by evm_ov)
  have rd2411pre := evm_run rd2406 with [
    raw uniswapAddress (by clipper_yank_decode) (by evm_ov),
    raw push1 ⟨36⟩ (by clipper_yank_decode) (by evm_ov),
    raw dup3 (by clipper_yank_decode) (by evm_ov),
    raw add (by clipper_yank_decode) (by evm_ov)]
  rw [show (⟨128⟩ : UInt256) + ⟨36⟩ = ⟨164⟩ from by native_decide] at rd2411pre
  have rd2412 := rd2411pre.mstore 0
    (clipperVatFluxThisMem ee
      (clipperVatFluxIlkMem v (clipperYankVatFluxBaseMem v ee tab)))
    (UInt256.ofNat 7) (by clipper_yank_decode) mem_cost (by rfl)
    (by native_decide) (by evm_ov)
  have rd2417pre := evm_run rd2412 with [
    raw caller (by clipper_yank_decode) (by evm_ov),
    raw push1 ⟨68⟩ (by clipper_yank_decode) (by evm_ov),
    raw dup3 (by clipper_yank_decode) (by evm_ov),
    raw add (by clipper_yank_decode) (by evm_ov)]
  rw [show (⟨128⟩ : UInt256) + ⟨68⟩ = ⟨196⟩ from by native_decide] at rd2417pre
  have rd2418 := rd2417pre.mstore 3
    (clipperVatFluxCallerMem ee
      (clipperVatFluxThisMem ee
        (clipperVatFluxIlkMem v (clipperYankVatFluxBaseMem v ee tab))))
    (UInt256.ofNat 8) (by clipper_yank_decode) mem_cost (by rfl)
    (by native_decide) (by evm_ov)
  have rd2425pre := evm_run rd2418 with [
    raw push1 ⟨100⟩ (by clipper_yank_decode) (by evm_ov),
    raw dup2 (by clipper_yank_decode) (by evm_ov),
    raw add (by clipper_yank_decode) (by evm_ov),
    raw swap2 (by clipper_yank_decode) (by evm_ov),
    raw swap1 (by clipper_yank_decode) (by evm_ov),
    raw swap2 (by clipper_yank_decode) (by evm_ov)]
  rw [show (⟨128⟩ : UInt256) + ⟨100⟩ = ⟨228⟩ from by native_decide] at rd2425pre
  have rd2426 := rd2425pre.mstore 3
    (clipperVatFluxCalldataMem v ee (clipperYankSalesLotWord σ ee)
      (clipperYankVatFluxBaseMem v ee tab))
    (UInt256.ofNat 9) (by clipper_yank_decode) mem_cost (by rfl)
    (by native_decide) (by evm_ov)
  have rd2427pre := evm_run rd2426 with [
    raw swap1 (by clipper_yank_decode) (by evm_ov)]
  have rd2428 := rd2427pre.mload 0 ⟨128⟩ (UInt256.ofNat 9)
    (by clipper_yank_decode) mem_cost hcallMload64 (by native_decide) (by evm_ov)
  have rd2469pre := evm_run rd2428 with [
    raw push1 ⟨1⟩ (by clipper_yank_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_yank_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_yank_decode) (by evm_ov),
    raw shl (by clipper_yank_decode) (by evm_ov),
    raw sub (by clipper_yank_decode) (by evm_ov)]
  have rd2470pre := rd2469pre.pushConst vatWord (width := 32) (op := .PUSH32)
    (by decide)
    (by simpa [vatWord] using clipperYankVatPush32Decode2436 v hpatch)
    (by evm_ov)
  have rd2471pre := evm_run rd2470pre with [
    raw and (by clipper_yank_decode) (by evm_ov)]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
    solcAddrMask from by native_decide] at rd2471pre
  have rd2495 := evm_run rd2471pre with [
    raw swap4 (by clipper_yank_decode) (by evm_ov),
    raw pop (by clipper_yank_decode) (by evm_ov),
    raw push4 clipperVatFluxSelectorWord (by clipper_yank_decode) (by evm_ov),
    raw swap3 (by clipper_yank_decode) (by evm_ov),
    raw push1 ⟨132⟩ (by clipper_yank_decode) (by evm_ov),
    raw dup1 (by clipper_yank_decode) (by evm_ov),
    raw dup5 (by clipper_yank_decode) (by evm_ov),
    raw add (by clipper_yank_decode) (by evm_ov),
    raw swap4 (by clipper_yank_decode) (by evm_ov),
    raw swap2 (by clipper_yank_decode) (by evm_ov),
    raw swap3 (by clipper_yank_decode) (by evm_ov),
    raw swap2 (by clipper_yank_decode) (by evm_ov),
    raw dup3 (by clipper_yank_decode) (by evm_ov),
    raw swap1 (by clipper_yank_decode) (by evm_ov),
    raw sub (by clipper_yank_decode) (by evm_ov),
    raw add (by clipper_yank_decode) (by evm_ov),
    raw dup2 (by clipper_yank_decode) (by evm_ov),
    raw dup4 (by clipper_yank_decode) (by evm_ov),
    raw dup8 (by clipper_yank_decode) (by evm_ov),
    raw dup1 (by clipper_yank_decode) (by evm_ov)]
  rw [show (⟨128⟩ : UInt256) + ⟨132⟩ = ⟨260⟩ from by native_decide] at rd2495
  rw [show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ = ⟨0⟩ from by native_decide] at rd2495
  rw [show (⟨0⟩ : UInt256) + ⟨132⟩ = ⟨132⟩ from by native_decide] at rd2495
  exact ⟨_, _, by simpa [clipperYankVatTarget, vatWord, u256_land_comm] using rd2495⟩

theorem clipperYankX_vatFluxNoCode {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel tab : UInt256} {rdata : ByteArray}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (rd2495 : RD code I g s0 ⟨2495⟩
      (clipperYankVatTarget v :: clipperYankVatTarget v :: ⟨0⟩ :: ⟨128⟩ ::
        ⟨132⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨260⟩ :: clipperVatFluxSelectorWord ::
        clipperYankVatTarget v :: clipperYankArgWord I :: ⟨502⟩ :: [sel])
      (clipperVatFluxCalldataMem v I (clipperYankSalesLotWord σ I)
        (clipperYankVatFluxBaseMem v I tab))
      (UInt256.ofNat 9) rdata (cA, σ) k C)
    (hcodeSizeVat :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (clipperYankVatTarget v) = ⟨0⟩) :
    RDrev code g s0 := by
  exact RD.uniswapExtcodesizeGuardMissing (pc := ⟨2495⟩) (okPc := ⟨2507⟩)
    rd2495 hcodeSizeVat
    (by clipper_yank_decode) (by clipper_yank_decode) (by clipper_yank_decode)
    (by clipper_yank_decode) (by clipper_yank_decode) (by clipper_yank_decode)
    (by clipper_yank_decode) (by clipper_yank_decode) (by clipper_yank_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.clipperYankVatFluxPostCall {cA0 cA gh bl σ₀ σStart σ I}
    {g : Sat256} {A : Substate} {k C : ℕ} {sel tab : UInt256}
    {rdata : ByteArray} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (rd2495 : RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨2495⟩
      (clipperYankVatTarget v :: clipperYankVatTarget v :: ⟨0⟩ :: ⟨128⟩ ::
        ⟨132⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨260⟩ :: clipperVatFluxSelectorWord ::
        clipperYankVatTarget v :: clipperYankArgWord I :: ⟨502⟩ :: [sel])
      (clipperVatFluxCalldataMem v I (clipperYankSalesLotWord σ I)
        (clipperYankVatFluxBaseMem v I tab))
      (UInt256.ofNat 9) rdata (cA, σ) k C)
    (hcodeSizeVat :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (clipperYankVatTarget v) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true) :
    ∃ (cA_vat : Batteries.RBSet AccountAddress compare) (σ_vat : AccountMap)
      (zVat : Bool) (outVat : ByteArray) (A_vat : Substate) (k' C' : ℕ),
      RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨2511⟩
        ((if zVat then ⟨1⟩ else ⟨0⟩) :: ⟨260⟩ :: clipperVatFluxSelectorWord ::
          clipperYankVatTarget v :: clipperYankArgWord I :: ⟨502⟩ :: [sel])
        (outVat.write 0
          (clipperVatFluxCalldataMem v I (clipperYankSalesLotWord σ I)
            (clipperYankVatFluxBaseMem v I tab))
          128 (min (⟨0⟩ : UInt256) (UInt256.ofNat outVat.size)).toNat)
        (UInt256.ofNat
          (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
            (⟨128⟩ : UInt256).toNat (⟨132⟩ : UInt256).toNat)
            (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat))
        outVat (cA_vat, σ_vat) k' C' ∧
      typedCallViaEVM (config v)
        { initState cA0 gh bl σStart σ₀ g A I with
          accountMap := σ, createdAccounts := cA }
        (EVM.address v.vat) "flux" 0
        [v.ilk, .address I.codeOwner, .address I.source,
          .int (Int.ofNat (clipperYankSalesLotWord σ I).toNat)]
        (zVat,
          { initState cA0 gh bl σStart σ₀ g A I with
            accountMap := σ_vat
            substate := A_vat
            createdAccounts := cA_vat },
          outVat) true ∧
      outVat.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd2510⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨2495⟩) (okPc := ⟨2507⟩)
      rd2495 hcodeSizeVat
      (by clipper_yank_decode) (by clipper_yank_decode)
      (by clipper_yank_decode) (by clipper_yank_decode)
      (by clipper_yank_decode) (by clipper_yank_decode)
      (clipperYankJumpDest2507 v hpatch)
      (by clipper_yank_decode) (by clipper_yank_decode)
      (by clipper_yank_decode)
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨cA_vat, σ_vat, zVat, outVat, A_in, callGas, k2511, C2511, hΘpack,
      rd2511raw, houtVatSize⟩ :=
    RD.call rd2510 (by clipper_yank_decode) hdepth (by evm_ov)
  obtain ⟨g'', A_vat, hΘ⟩ := hΘpack
  refine ⟨cA_vat, σ_vat, zVat, outVat, A_vat, k2511, C2511, ?_, ?_,
    houtVatSize⟩
  · exact rd2511raw
  · let evmVat : EVM.State :=
      { initState cA0 gh bl σStart σ₀ g A I with
        accountMap := σ, createdAccounts := cA }
    refine callCoincides (cfg := config v)
      (evm := evmVat)
      (name := "flux")
      (args := [v.ilk, .address I.codeOwner, .address I.source,
        .int (Int.ofNat (clipperYankSalesLotWord σ I).toNat)])
      (tgt := EVM.address v.vat) (targetWord := clipperYankVatTarget v)
      (cA' := cA_vat) (σ' := σ_vat) (A' := A_vat) (A_in := A_in)
      (z := zVat) (o := outVat) (g'' := g'') (callGas := callGas)
      (mem := clipperVatFluxCalldataMem v I (clipperYankSalesLotWord σ I)
        (clipperYankVatFluxBaseMem v I tab))
      (inOff := ⟨128⟩) (inSize := ⟨132⟩) (callPerm := true)
      (fun h => absurd hdepth (by
        have hI : I.depth = (1024 : Fin 1025) := by
          simpa [evmVat, initState] using h
        rw [hI]
        decide))
      ?_ ?_ ?_
    · rw [clipperYankVatTargetAddress v]
      exact clipperYankEVMAddressAccountAddress v.vat
    · simpa [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
        show (⟨132⟩ : UInt256).toNat = 132 from by decide] using
        clipperVatFluxEncode_eq v I (clipperYankSalesLotWord σ I)
          (clipperYankVatFluxBaseMem_size v I tab)
    · simpa [evmVat, initState, hperm] using hΘ

theorem RD.clipperYankVatFluxCallFailure
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    (rd : RD code ee g s0 ⟨2511⟩ (⟨0⟩ :: R) mem aw o acc k C)
    (hosz : o.size < UInt256.size)
    (hov : R.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.uniswapCallSuccessGuardMissing (pc := ⟨2511⟩) (okPc := ⟨2527⟩)
    rd (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by clipper_yank_decode) (by clipper_yank_decode)
    (by clipper_yank_decode) (by clipper_yank_decode)
    (by clipper_yank_decode) (by clipper_yank_decode)
    (by clipper_yank_decode) (by clipper_yank_decode)
    (by clipper_yank_decode) (by clipper_yank_decode)
    (by clipper_yank_decode) (by clipper_yank_decode)
    hosz hov

theorem RD.clipperYankVatFluxCallSuccessToRemove
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {sel : UInt256}
    (rd : RD code ee g s0 ⟨2511⟩
      (⟨1⟩ :: ⟨260⟩ :: clipperVatFluxSelectorWord :: clipperYankVatTarget v ::
        clipperYankArgWord ee :: ⟨502⟩ :: [sel])
      mem aw o acc k C) :
    ∃ k' C', RD code ee g s0 ⟨8274⟩
      (clipperYankArgWord ee :: ⟨2540⟩ :: clipperYankArgWord ee :: ⟨502⟩ :: [sel])
      mem aw o acc k' C' := by
  obtain ⟨_, _, rd2529⟩ :=
    RD.uniswapCallSuccessGuardOk (pc := ⟨2511⟩) (okPc := ⟨2527⟩) rd
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by clipper_yank_decode) (by clipper_yank_decode)
      (by clipper_yank_decode) (by clipper_yank_decode)
      (by clipper_yank_decode) (clipperYankJumpDest2527 v hpatch)
      (by clipper_yank_post_decode) (by clipper_yank_post_decode)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2536 := evm_run rd2529 with [
    raw pop (by clipper_yank_post_decode) (by evm_ov),
    raw pop (by clipper_yank_post_decode) (by evm_ov),
    raw pop (by clipper_yank_post_decode) (by evm_ov),
    raw push2 ⟨2540⟩ (by clipper_yank_post_decode) (by evm_ov),
    raw dup2 (by clipper_yank_post_decode) (by evm_ov),
    raw push2 ⟨8274⟩ (by clipper_yank_post_decode) (by evm_ov)]
  have rd8274 := rd2536.jump (by clipper_yank_post_decode)
    (clipperYankJumpDest8274 v hpatch) (by evm_ov)
  exact ⟨_, _, rd8274⟩

theorem RD.clipperYankRemoveEmptyInvalid
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {sel : UInt256}
    {cA σ}
    (rd : RD code ee g s0 ⟨8274⟩
      (clipperYankArgWord ee :: ⟨2540⟩ :: clipperYankArgWord ee :: ⟨502⟩ :: [sel])
      mem aw o (cA, σ) k C)
    (hlen : solcSlotWord σ ee ⟨11⟩ = ⟨0⟩) :
    RDinvalid code g s0 := by
  have rd8277 := evm_run rd with [
    raw jumpdest (by clipper_yank_remove_decode) (by evm_ov),
    raw push1 ⟨11⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw dup1 (by clipper_yank_remove_decode) (by evm_ov)]
  obtain ⟨_, _, rd8279⟩ := rd8277.sload (by clipper_yank_remove_decode) (by evm_ov)
  have rd8294 := evm_run rd8279 with [
    raw push1 ⟨0⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw swap2 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw not (by clipper_yank_remove_decode) (by evm_ov),
    raw dup2 (by clipper_yank_remove_decode) (by evm_ov),
    raw add (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw dup2 (by clipper_yank_remove_decode) (by evm_ov),
    raw lt (by clipper_yank_remove_decode) (by evm_ov),
    raw push2 ⟨8296⟩ (by clipper_yank_remove_decode) (by evm_ov)]
  have hcond :
      UInt256.lt (solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩)
        (solcSlotWord σ ee ⟨11⟩) = ⟨0⟩ := by
    rw [hlen]
    native_decide
  exact RD.invalidHalt
    (rd8294.jumpiNT (by clipper_yank_remove_decode)
      (by simpa [solcSlotWord] using hcond) (by evm_ov))
    (by clipper_yank_remove_decode)

theorem RD.clipperYankRemoveIdEqMoveToJoin
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {sel : UInt256}
    {cA σ}
    (rd : RD code ee g s0 ⟨8274⟩
      (clipperYankArgWord ee :: ⟨2540⟩ :: clipperYankArgWord ee :: ⟨502⟩ :: [sel])
      mem aw o (cA, σ) k C)
    (hlen : solcSlotWord σ ee ⟨11⟩ ≠ ⟨0⟩)
    (heq :
      let lastIndex := solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩
      clipperYankArgWord ee = solcSlotWord σ ee (clipperYankActiveSlot lastIndex)) :
    let lastIndex := solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩
    let move := solcSlotWord σ ee (clipperYankActiveSlot lastIndex)
    let activeMem := wordAt0Mem (⟨11⟩ : UInt256) mem
    let aw1 := UInt256.ofNat (MachineState.M aw.toNat 0 32)
    let aw2 := UInt256.ofNat (MachineState.M aw1.toNat 0 32)
    ∃ k' C', RD code ee g s0 ⟨8379⟩
      (move :: clipperYankArgWord ee :: ⟨2540⟩ :: clipperYankArgWord ee :: ⟨502⟩ :: [sel])
      activeMem aw2 o (cA, σ) k' C' := by
  intro lastIndex move activeMem aw1 aw2
  have rd8277 := evm_run rd with [
    raw jumpdest (by clipper_yank_remove_decode) (by evm_ov),
    raw push1 ⟨11⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw dup1 (by clipper_yank_remove_decode) (by evm_ov)]
  obtain ⟨_, _, rd8279⟩ := rd8277.sload (by clipper_yank_remove_decode) (by evm_ov)
  have rd8294 := evm_run rd8279 with [
    raw push1 ⟨0⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw swap2 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw not (by clipper_yank_remove_decode) (by evm_ov),
    raw dup2 (by clipper_yank_remove_decode) (by evm_ov),
    raw add (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw dup2 (by clipper_yank_remove_decode) (by evm_ov),
    raw lt (by clipper_yank_remove_decode) (by evm_ov),
    raw push2 ⟨8296⟩ (by clipper_yank_remove_decode) (by evm_ov)]
  have hcond :
      UInt256.lt (solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩)
        (solcSlotWord σ ee ⟨11⟩) = ⟨1⟩ :=
    clipperYankNonzeroLenPredLt (solcSlotWord σ ee ⟨11⟩) hlen
  have hcondNe :
      UInt256.lt (solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩)
        (solcSlotWord σ ee ⟨11⟩) ≠ ⟨0⟩ := by
    rw [hcond]
    native_decide
  have rd8296 := rd8294.jumpiT (by clipper_yank_remove_decode)
    (by simpa [solcSlotWord] using hcondNe)
    (clipperYankJumpDest8296 v hpatch) (by evm_ov)
  have rd8300 := evm_run rd8296 with [
    raw jumpdest (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8301 := rd8300.mstore (Cₘ aw1 - Cₘ aw) activeMem aw1
    (by clipper_yank_remove_decode)
    (by
      intro s hawEq hstk
      exact mstoreCost_of_stack hawEq hstk (by simp [aw1]))
    (by simpa [activeMem, wordAt0Mem]) (by rfl) (by evm_ov)
  have hslot :
      UInt256.ofNat
          (fromByteArrayBigEndian (ffi.KEC (activeMem.readWithPadding 0 32))) =
        activeDataSlot := by
    simpa [activeMem, activeDataSlot,
      show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨32⟩ : UInt256).toNat = 32 from by decide] using
      (wordAt0Mem_keccak_word (⟨11⟩ : UInt256) mem).trans
        (keccakSlot_eq (UInt256.toByteArray (⟨11⟩ : UInt256)))
  have rd8305 := evm_run rd8301 with [
    raw push1 ⟨32⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8306 := rd8305.keccak256 (Cₘ aw2 - Cₘ aw1) activeDataSlot aw2
    (by clipper_yank_remove_decode)
    (by
      intro s hawEq hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hawEq, hstk, aw2,
        show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨32⟩ : UInt256).toNat = 32 from by decide])
    hslot (by rfl) (by evm_ov)
  have rd8307pre := evm_run rd8306 with [
    raw add (by clipper_yank_remove_decode) (by evm_ov)]
  have hslotActive :
      activeDataSlot + (solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩) =
        clipperYankActiveSlot lastIndex := by
    simpa [lastIndex, clipperYankActiveSlot_eq]
  have hslotActive' :
      UInt256.lnot ⟨0⟩ + (solcSlotWord σ ee ⟨11⟩ + activeDataSlot) =
        clipperYankActiveSlot lastIndex := by
    rw [← u256_add_assoc]
    rw [u256_add_comm (UInt256.lnot ⟨0⟩) (solcSlotWord σ ee ⟨11⟩)]
    rw [u256_add_assoc]
    rw [u256_add_comm (UInt256.lnot ⟨0⟩) activeDataSlot]
    rw [← u256_add_assoc]
    rw [u256_add_comm (solcSlotWord σ ee ⟨11⟩) activeDataSlot]
    rw [u256_add_assoc]
    exact hslotActive
  obtain ⟨k8307, C8307, rd8307slot⟩ :
      ∃ k C, RD code ee g s0 ⟨8307⟩
        (clipperYankActiveSlot lastIndex :: ⟨0⟩ :: clipperYankArgWord ee :: ⟨2540⟩ ::
          clipperYankArgWord ee :: ⟨502⟩ :: [sel])
        activeMem aw2 o (cA, σ) k C := by
    exact ⟨_, _, by simpa [solcSlotWord, hslotActive] using rd8307pre⟩
  obtain ⟨_, _, rd8308raw⟩ := rd8307slot.sload (by clipper_yank_remove_decode) (by evm_ov)
  obtain ⟨k8308, C8308, rd8308⟩ :
      ∃ k C, RD code ee g s0 ⟨8308⟩
        (move :: ⟨0⟩ :: clipperYankArgWord ee :: ⟨2540⟩ ::
          clipperYankArgWord ee :: ⟨502⟩ :: [sel])
        activeMem aw2 o (cA, σ) k C := by
    exact ⟨_, _, by simpa [move, solcSlotWord] using rd8308raw⟩
  have rd8312 := evm_run rd8308 with [
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw pop (by clipper_yank_remove_decode) (by evm_ov),
    raw dup1 (by clipper_yank_remove_decode) (by evm_ov),
    raw dup3 (by clipper_yank_remove_decode) (by evm_ov),
    raw eq (by clipper_yank_remove_decode) (by evm_ov)]
  have hidMove : clipperYankArgWord ee = move := by
    simpa [lastIndex, move] using heq
  have heqCond : UInt256.eq (clipperYankArgWord ee) move ≠ ⟨0⟩ := by
    rw [← hidMove, uInt256_eq_self]
    native_decide
  have rd8316 := evm_run rd8312 with [
    raw push2 ⟨8379⟩ (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8379 := rd8316.jumpiT (by clipper_yank_remove_decode)
    heqCond (clipperYankJumpDest8379 v hpatch) (by evm_ov)
  exact ⟨_, _, rd8379⟩

abbrev clipperYankMoveAccountMap (σ : AccountMap) (I : ExecutionEnv)
    (idx move : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner
    (sstoreAccountMap I.codeOwner σ (clipperYankActiveSlot idx) move)
    (clipperYankSalesMovePosSlot move) idx

theorem clipperYankMoveAccountMap_state_accountMapEquiv
    {σ τ : AccountMap} (evm : EVM.State) (I : ExecutionEnv)
    (idx move : UInt256)
    (hAccounts : accountMapEquiv σ τ)
    (hevm : evm.accountMap = τ)
    (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    accountMapEquiv (clipperYankMoveAccountMap σ I idx move)
      (let evmIndex := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (clipperYankActiveSlot idx) move
       let evmMovePos := Solm.EVM.storageStore evmIndex evmIndex.executionEnv.codeOwner
        (clipperYankSalesMovePosSlot move) idx
       evmMovePos.accountMap) := by
  let evmIndex := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (clipperYankActiveSlot idx) move
  have hindex :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ (clipperYankActiveSlot idx) move)
        evmIndex.accountMap := by
    simpa [evmIndex, storageStore_accountMap, howner] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (clipperYankActiveSlot idx) move
        (by simpa [hevm] using hAccounts)
  have hownerIndex : evmIndex.executionEnv.codeOwner = I.codeOwner := by
    simp [evmIndex, storageStore_executionEnv, howner]
  simpa [clipperYankMoveAccountMap, evmIndex, storageStore_accountMap,
    storageStore_executionEnv, howner, hownerIndex] using
    accountMapEquiv_sstoreAccountMap I.codeOwner (clipperYankSalesMovePosSlot move) idx
      hindex

set_option maxHeartbeats 4000000 in
theorem RD.clipperYankRemoveIdNeMoveToJoin
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {sel : UInt256}
    {cA σ}
    (rd : RD code ee g s0 ⟨8274⟩
      (clipperYankArgWord ee :: ⟨2540⟩ :: clipperYankArgWord ee :: ⟨502⟩ :: [sel])
      mem aw o (cA, σ) k C)
    (hlen : solcSlotWord σ ee ⟨11⟩ ≠ ⟨0⟩)
    (hne :
      let lastIndex := solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩
      clipperYankArgWord ee ≠ solcSlotWord σ ee (clipperYankActiveSlot lastIndex))
    (hactiveMemSize : 64 ≤ (wordAt0Mem (⟨11⟩ : UInt256) mem).size)
    (hidxBound :
      (solcSlotWord σ ee (clipperYankSalesPosSlot ee)).toNat <
        (solcSlotWord σ ee ⟨11⟩).toNat)
    (hperm : ee.perm = true) :
    let lastIndex := solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩
    let move := solcSlotWord σ ee (clipperYankActiveSlot lastIndex)
    let idx := solcSlotWord σ ee (clipperYankSalesPosSlot ee)
    ∃ mem' aw' k' C',
      RD code ee g s0 ⟨8379⟩
        (move :: clipperYankArgWord ee :: ⟨2540⟩ :: clipperYankArgWord ee :: ⟨502⟩ ::
          [sel])
        mem' aw' o (cA, clipperYankMoveAccountMap σ ee idx move) k' C' ∧
      64 ≤ (wordAt0Mem (⟨11⟩ : UInt256) mem').size := by
  intro lastIndex move idx
  let activeMem := wordAt0Mem (⟨11⟩ : UInt256) mem
  let aw1 := UInt256.ofNat (MachineState.M aw.toNat 0 32)
  let aw2 := UInt256.ofNat (MachineState.M aw1.toNat 0 32)
  let saleKeyMem := wordAt0Mem (clipperYankArgWord ee) activeMem
  let aw3 := UInt256.ofNat (MachineState.M aw2.toNat 0 32)
  let saleHashMem := twoWordHashMem (clipperYankArgWord ee) ⟨12⟩ activeMem
  let aw4 := UInt256.ofNat (MachineState.M aw3.toNat 32 32)
  let aw5 := UInt256.ofNat (MachineState.M aw4.toNat 0 64)
  let activeIndexMem := wordAt0Mem (⟨11⟩ : UInt256) saleHashMem
  let aw6 := UInt256.ofNat (MachineState.M aw5.toNat 0 32)
  let aw7 := UInt256.ofNat (MachineState.M aw6.toNat 0 32)
  let σIndex := sstoreAccountMap ee.codeOwner σ (clipperYankActiveSlot idx) move
  let moveKeyMem := wordAt0Mem move activeIndexMem
  let aw8 := UInt256.ofNat (MachineState.M aw7.toNat 0 32)
  let moveHashMem := twoWordHashMem move ⟨12⟩ activeIndexMem
  let aw9 := UInt256.ofNat (MachineState.M aw8.toNat 32 32)
  let aw10 := UInt256.ofNat (MachineState.M aw9.toNat 0 64)
  have rd8277 := evm_run rd with [
    raw jumpdest (by clipper_yank_remove_decode) (by evm_ov),
    raw push1 ⟨11⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw dup1 (by clipper_yank_remove_decode) (by evm_ov)]
  obtain ⟨_, _, rd8279⟩ := rd8277.sload (by clipper_yank_remove_decode) (by evm_ov)
  have rd8294 := evm_run rd8279 with [
    raw push1 ⟨0⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw swap2 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw not (by clipper_yank_remove_decode) (by evm_ov),
    raw dup2 (by clipper_yank_remove_decode) (by evm_ov),
    raw add (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw dup2 (by clipper_yank_remove_decode) (by evm_ov),
    raw lt (by clipper_yank_remove_decode) (by evm_ov),
    raw push2 ⟨8296⟩ (by clipper_yank_remove_decode) (by evm_ov)]
  have hcond :
      UInt256.lt (solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩)
        (solcSlotWord σ ee ⟨11⟩) = ⟨1⟩ :=
    clipperYankNonzeroLenPredLt (solcSlotWord σ ee ⟨11⟩) hlen
  have hcondNe :
      UInt256.lt (solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩)
        (solcSlotWord σ ee ⟨11⟩) ≠ ⟨0⟩ := by
    rw [hcond]
    native_decide
  have rd8296 := rd8294.jumpiT (by clipper_yank_remove_decode)
    (by simpa [solcSlotWord] using hcondNe)
    (clipperYankJumpDest8296 v hpatch) (by evm_ov)
  have rd8300 := evm_run rd8296 with [
    raw jumpdest (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8301 := rd8300.mstore (Cₘ aw1 - Cₘ aw) activeMem aw1
    (by clipper_yank_remove_decode)
    (by
      intro s hawEq hstk
      exact mstoreCost_of_stack hawEq hstk (by simp [aw1]))
    (by simpa [activeMem, wordAt0Mem]) (by rfl) (by evm_ov)
  have hslot :
      UInt256.ofNat
          (fromByteArrayBigEndian (ffi.KEC (activeMem.readWithPadding 0 32))) =
        activeDataSlot := by
    simpa [activeMem, activeDataSlot,
      show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨32⟩ : UInt256).toNat = 32 from by decide] using
      (wordAt0Mem_keccak_word (⟨11⟩ : UInt256) mem).trans
        (keccakSlot_eq (UInt256.toByteArray (⟨11⟩ : UInt256)))
  have rd8305 := evm_run rd8301 with [
    raw push1 ⟨32⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8306 := rd8305.keccak256 (Cₘ aw2 - Cₘ aw1) activeDataSlot aw2
    (by clipper_yank_remove_decode)
    (by
      intro s hawEq hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hawEq, hstk, aw2,
        show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨32⟩ : UInt256).toNat = 32 from by decide])
    hslot (by rfl) (by evm_ov)
  have rd8307pre := evm_run rd8306 with [
    raw add (by clipper_yank_remove_decode) (by evm_ov)]
  have hslotActive :
      activeDataSlot + (solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩) =
        clipperYankActiveSlot lastIndex := by
    simpa [lastIndex, clipperYankActiveSlot_eq]
  have hslotActive' :
      UInt256.lnot ⟨0⟩ + (solcSlotWord σ ee ⟨11⟩ + activeDataSlot) =
        clipperYankActiveSlot lastIndex := by
    rw [← u256_add_assoc]
    rw [u256_add_comm (UInt256.lnot ⟨0⟩) (solcSlotWord σ ee ⟨11⟩)]
    rw [u256_add_assoc]
    rw [u256_add_comm (UInt256.lnot ⟨0⟩) activeDataSlot]
    rw [← u256_add_assoc]
    rw [u256_add_comm (solcSlotWord σ ee ⟨11⟩) activeDataSlot]
    rw [u256_add_assoc]
    exact hslotActive
  obtain ⟨k8307, C8307, rd8307slot⟩ :
      ∃ k C, RD code ee g s0 ⟨8307⟩
        (clipperYankActiveSlot lastIndex :: ⟨0⟩ :: clipperYankArgWord ee :: ⟨2540⟩ ::
          clipperYankArgWord ee :: ⟨502⟩ :: [sel])
        activeMem aw2 o (cA, σ) k C := by
    exact ⟨_, _, by simpa [solcSlotWord, hslotActive] using rd8307pre⟩
  obtain ⟨_, _, rd8308raw⟩ := rd8307slot.sload (by clipper_yank_remove_decode) (by evm_ov)
  obtain ⟨k8308, C8308, rd8308⟩ :
      ∃ k C, RD code ee g s0 ⟨8308⟩
        (move :: ⟨0⟩ :: clipperYankArgWord ee :: ⟨2540⟩ ::
          clipperYankArgWord ee :: ⟨502⟩ :: [sel])
        activeMem aw2 o (cA, σ) k C := by
    exact ⟨_, _, by simpa [move, solcSlotWord] using rd8308raw⟩
  have rd8312 := evm_run rd8308 with [
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw pop (by clipper_yank_remove_decode) (by evm_ov),
    raw dup1 (by clipper_yank_remove_decode) (by evm_ov),
    raw dup3 (by clipper_yank_remove_decode) (by evm_ov),
    raw eq (by clipper_yank_remove_decode) (by evm_ov)]
  have hneMove : clipperYankArgWord ee ≠ move := by
    simpa [lastIndex, move] using hne
  have hneCond : UInt256.eq (clipperYankArgWord ee) move = ⟨0⟩ :=
    uInt256_eq_zero_of_ne (by
      intro hEqOne
      exact hneMove (uInt256_eq_one_eq hEqOne))
  have rd8316 := evm_run rd8312 with [
    raw push2 ⟨8379⟩ (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8317 := rd8316.jumpiNT (by clipper_yank_remove_decode)
    (by simpa using hneCond) (by evm_ov)
  have rd8321pre := evm_run rd8317 with [
    raw push1 ⟨0⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw dup3 (by clipper_yank_remove_decode) (by evm_ov),
    raw dup2 (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8322 := rd8321pre.mstore (Cₘ aw3 - Cₘ aw2) saleKeyMem aw3
    (by clipper_yank_remove_decode)
    (by
      intro s hawEq hstk
      exact mstoreCost_of_stack hawEq hstk (by simp [aw3]))
    (by simpa [saleKeyMem, wordAt0Mem]) (by rfl) (by evm_ov)
  have rd8326pre := evm_run rd8322 with [
    raw push1 ⟨12⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8327 := rd8326pre.mstore (Cₘ aw4 - Cₘ aw3) saleHashMem aw4
    (by clipper_yank_remove_decode)
    (by
      intro s hawEq hstk
      exact mstoreCost_of_stack hawEq hstk (by
        simp [aw4, show (⟨32⟩ : UInt256).toNat = 32 from by decide]))
    (by rfl) (by rfl) (by evm_ov)
  have hsalesBase :
      UInt256.ofNat
          (fromByteArrayBigEndian (ffi.KEC (saleHashMem.readWithPadding 0 64))) =
        clipperYankSalesBaseSlot ee := by
    change
      UInt256.ofNat
          (fromByteArrayBigEndian
            (ffi.KEC
              ((twoWordHashMem (clipperYankArgWord ee) (⟨12⟩ : UInt256) activeMem).readWithPadding
                0 64))) =
        clipperYankSalesBaseSlot ee
    rw [clipperYankTwoWordHashMem_read0_64_of_ge
      (clipperYankArgWord ee) (⟨12⟩ : UInt256) (by
        simpa [activeMem] using hactiveMemSize)]
    rw [clipperYankSalesBaseSlot_eq ee]
    exact mappingSlot_single (clipperYankArgWord ee) ⟨12⟩
  have rd8330pre := evm_run rd8327 with [
    raw push1 ⟨64⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8331pre := rd8330pre.keccak256 (Cₘ aw5 - Cₘ aw4) (clipperYankSalesBaseSlot ee) aw5
    (by clipper_yank_remove_decode)
    (by
      intro s hawEq hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hawEq, hstk, aw5,
        show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide])
    hsalesBase (by rfl) (by evm_ov)
  obtain ⟨_, _, rd8332raw⟩ := rd8331pre.sload (by clipper_yank_remove_decode) (by evm_ov)
  obtain ⟨k8332, C8332, rd8332⟩ :
      ∃ k C, RD code ee g s0 ⟨8332⟩
        (idx :: move :: clipperYankArgWord ee :: ⟨2540⟩ :: clipperYankArgWord ee :: ⟨502⟩ ::
          [sel])
        saleHashMem aw5 o (cA, σ) k C := by
    exact ⟨_, _, by simpa [idx, clipperYankSalesPosSlot, solcSlotWord] using rd8332raw⟩
  have rd8346 := evm_run rd8332 with [
    raw push1 ⟨11⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw dup1 (by clipper_yank_remove_decode) (by evm_ov)]
  obtain ⟨_, _, rd8336raw⟩ := rd8346.sload (by clipper_yank_remove_decode) (by evm_ov)
  have rd8347pre := evm_run rd8336raw with [
    raw dup4 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap2 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw dup4 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw dup2 (by clipper_yank_remove_decode) (by evm_ov),
    raw lt (by clipper_yank_remove_decode) (by evm_ov),
    raw push2 ⟨8348⟩ (by clipper_yank_remove_decode) (by evm_ov)]
  have hidxCond : UInt256.lt idx (solcSlotWord σ ee ⟨11⟩) ≠ ⟨0⟩ := by
    rw [ult_one hidxBound]
    native_decide
  have rd8348 := rd8347pre.jumpiT (by clipper_yank_remove_decode)
    (by simpa [idx, solcSlotWord] using hidxCond)
    (clipperYankJumpDest8348 v hpatch) (by evm_ov)
  have rd8352pre := evm_run rd8348 with [
    raw jumpdest (by clipper_yank_remove_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw swap2 (by clipper_yank_remove_decode) (by evm_ov),
    raw dup3 (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8353 := rd8352pre.mstore (Cₘ aw6 - Cₘ aw5) activeIndexMem aw6
    (by clipper_yank_remove_decode)
    (by
      intro s hawEq hstk
      exact mstoreCost_of_stack hawEq hstk (by simp [aw6]))
    (by simpa [activeIndexMem, wordAt0Mem]) (by rfl) (by evm_ov)
  have hactiveBase :
      UInt256.ofNat
          (fromByteArrayBigEndian (ffi.KEC (activeIndexMem.readWithPadding 0 32))) =
        activeDataSlot := by
    simpa [activeIndexMem, activeDataSlot,
      show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨32⟩ : UInt256).toNat = 32 from by decide] using
      (wordAt0Mem_keccak_word (⟨11⟩ : UInt256) saleHashMem).trans
        (keccakSlot_eq (UInt256.toByteArray (⟨11⟩ : UInt256)))
  have rd8358pre := evm_run rd8353 with [
    raw push1 ⟨32⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw dup1 (by clipper_yank_remove_decode) (by evm_ov),
    raw dup4 (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8359pre := rd8358pre.keccak256 (Cₘ aw7 - Cₘ aw6) activeDataSlot aw7
    (by clipper_yank_remove_decode)
    (by
      intro s hawEq hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hawEq, hstk, aw7,
        show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨32⟩ : UInt256).toNat = 32 from by decide])
    hactiveBase (by rfl) (by evm_ov)
  have rd8365pre := evm_run rd8359pre with [
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap2 (by clipper_yank_remove_decode) (by evm_ov),
    raw add (by clipper_yank_remove_decode) (by evm_ov),
    raw swap3 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap3 (by clipper_yank_remove_decode) (by evm_ov)]
  obtain ⟨k8366, C8366, rd8366⟩ :
      ∃ k C, RD code ee g s0 ⟨8366⟩
        (⟨0⟩ :: ⟨32⟩ :: idx :: move :: clipperYankArgWord ee :: ⟨2540⟩ ::
          clipperYankArgWord ee :: ⟨502⟩ :: [sel])
        activeIndexMem aw7 o (cA, σIndex) k C := by
    obtain ⟨k', C', rd'⟩ := rd8365pre.sstore hperm (by clipper_yank_remove_decode)
      (by simp only [List.length_cons, List.length_nil]; omega)
    exact ⟨k', C', by
      simpa [σIndex, clipperYankActiveSlot_eq, u256_add_comm activeDataSlot idx] using rd'⟩
  have rd8368pre := evm_run rd8366 with [
    raw dup4 (by clipper_yank_remove_decode) (by evm_ov),
    raw dup2 (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8369 := rd8368pre.mstore (Cₘ aw8 - Cₘ aw7) moveKeyMem aw8
    (by clipper_yank_remove_decode)
    (by
      intro s hawEq hstk
      exact mstoreCost_of_stack hawEq hstk (by simp [aw8]))
    (by simpa [moveKeyMem, wordAt0Mem]) (by rfl) (by evm_ov)
  have rd8373pre := evm_run rd8369 with [
    raw push1 ⟨12⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap2 (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8374 := rd8373pre.mstore (Cₘ aw9 - Cₘ aw8) moveHashMem aw9
    (by clipper_yank_remove_decode)
    (by
      intro s hawEq hstk
      exact mstoreCost_of_stack hawEq hstk (by
        simp [aw9, show (⟨32⟩ : UInt256).toNat = 32 from by decide]))
    (by rfl) (by rfl) (by evm_ov)
  have hsaleHashMemSize : 64 ≤ saleHashMem.size := by
    unfold saleHashMem twoWordHashMem wordAt32Mem
    exact toByteArray_write_size_ge_off_add32 (⟨12⟩ : UInt256)
      (wordAt0Mem (clipperYankArgWord ee) activeMem) 32 (by
        have hkeySize : 64 ≤ (wordAt0Mem (clipperYankArgWord ee) activeMem).size := by
          have hactiveMemSize' : 64 ≤ activeMem.size := by
            simpa [activeMem] using hactiveMemSize
          have hsizeEq :
              (wordAt0Mem (clipperYankArgWord ee) activeMem).size =
                max activeMem.size (0 + 32) := by
            simpa [wordAt0Mem, Reasoning.Theory.writeWord] using
              (Reasoning.Theory.writeWord_size activeMem 0 (clipperYankArgWord ee) (by
                simpa using lt_usize 0 (by norm_num)))
          rw [hsizeEq]
          exact le_trans hactiveMemSize' (Nat.le_max_left _ _)
        have hzero :
            32 - (wordAt0Mem (clipperYankArgWord ee) activeMem).size = 0 := by
          omega
        rw [hzero]
        exact lt_usize 0 (by norm_num))
  have hactiveIndexMemSize : 64 ≤ activeIndexMem.size := by
    have hsizeEq : activeIndexMem.size = max saleHashMem.size (0 + 32) := by
      simpa [activeIndexMem, wordAt0Mem, Reasoning.Theory.writeWord] using
        (Reasoning.Theory.writeWord_size saleHashMem 0 (⟨11⟩ : UInt256) (by
          simpa using lt_usize 0 (by norm_num)))
    rw [hsizeEq]
    exact le_trans hsaleHashMemSize (Nat.le_max_left _ _)
  have hmoveKeyMemSize : 64 ≤ moveKeyMem.size := by
    have hsizeEq : moveKeyMem.size = max activeIndexMem.size (0 + 32) := by
      simpa [moveKeyMem, wordAt0Mem, Reasoning.Theory.writeWord] using
        (Reasoning.Theory.writeWord_size activeIndexMem 0 move (by
          simpa using lt_usize 0 (by norm_num)))
    rw [hsizeEq]
    exact le_trans hactiveIndexMemSize (Nat.le_max_left _ _)
  have hmoveBase :
      UInt256.ofNat
          (fromByteArrayBigEndian (ffi.KEC (moveHashMem.readWithPadding 0 64))) =
        clipperYankSalesMovePosSlot move := by
    change
      UInt256.ofNat
          (fromByteArrayBigEndian
            (ffi.KEC
              ((twoWordHashMem move (⟨12⟩ : UInt256) activeIndexMem).readWithPadding 0 64))) =
        clipperYankSalesMovePosSlot move
    rw [clipperYankTwoWordHashMem_read0_64_of_ge move (⟨12⟩ : UInt256)
      hactiveIndexMemSize]
    rw [mappingSlot_single move ⟨12⟩]
    unfold clipperYankSalesMovePosSlot clipperYankSalesBaseSlotOfWord salesBase mapSlot
    rw [keyValueToWord_uint256]
  have rd8377pre := evm_run rd8374 with [
    raw push1 ⟨64⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8378pre := rd8377pre.keccak256 (Cₘ aw10 - Cₘ aw9)
    (clipperYankSalesMovePosSlot move) aw10
    (by clipper_yank_remove_decode)
    (by
      intro s hawEq hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hawEq, hstk, aw10,
        show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide])
    hmoveBase (by rfl) (by evm_ov)
  obtain ⟨k8379, C8379, rd8379raw⟩ :
      ∃ k C, RD code ee g s0 ⟨8379⟩
        (move :: clipperYankArgWord ee :: ⟨2540⟩ :: clipperYankArgWord ee :: ⟨502⟩ ::
          [sel])
        moveHashMem aw10 o (cA, clipperYankMoveAccountMap σ ee idx move) k C := by
    obtain ⟨k', C', rd'⟩ := rd8378pre.sstore hperm (by clipper_yank_remove_decode)
      (by simp only [List.length_cons, List.length_nil]; omega)
    exact ⟨k', C', by
      simpa [clipperYankMoveAccountMap, σIndex] using rd'⟩
  have hmoveHashSize : 64 ≤ moveHashMem.size := by
    unfold moveHashMem twoWordHashMem wordAt32Mem
    exact toByteArray_write_size_ge_off_add32 (⟨12⟩ : UInt256)
      (wordAt0Mem move activeIndexMem) 32 (by
        have hzero : 32 - (wordAt0Mem move activeIndexMem).size = 0 := by
          have hkeySize : 64 ≤ (wordAt0Mem move activeIndexMem).size := by
            simpa [moveKeyMem] using hmoveKeyMemSize
          omega
        rw [hzero]
        exact lt_usize 0 (by norm_num))
  have hjoinMemSize : 64 ≤ (wordAt0Mem (⟨11⟩ : UInt256) moveHashMem).size := by
    have hsizeEq :
        (wordAt0Mem (⟨11⟩ : UInt256) moveHashMem).size =
          max moveHashMem.size (0 + 32) := by
      simpa [wordAt0Mem, Reasoning.Theory.writeWord] using
        (Reasoning.Theory.writeWord_size moveHashMem 0 (⟨11⟩ : UInt256) (by
          simpa using lt_usize 0 (by norm_num)))
    rw [hsizeEq]
    exact le_trans hmoveHashSize (Nat.le_max_left _ _)
  exact ⟨moveHashMem, aw10, k8379, C8379, rd8379raw, hjoinMemSize⟩

set_option maxHeartbeats 4000000 in
theorem RD.clipperYankRemoveIdNeMoveIndexOobInvalid
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {sel : UInt256}
    {cA σ}
    (rd : RD code ee g s0 ⟨8274⟩
      (clipperYankArgWord ee :: ⟨2540⟩ :: clipperYankArgWord ee :: ⟨502⟩ :: [sel])
      mem aw o (cA, σ) k C)
    (hlen : solcSlotWord σ ee ⟨11⟩ ≠ ⟨0⟩)
    (hne :
      let lastIndex := solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩
      clipperYankArgWord ee ≠ solcSlotWord σ ee (clipperYankActiveSlot lastIndex))
    (hactiveMemSize : 64 ≤ (wordAt0Mem (⟨11⟩ : UInt256) mem).size)
    (hidxBound :
      (solcSlotWord σ ee ⟨11⟩).toNat ≤
        (solcSlotWord σ ee (clipperYankSalesPosSlot ee)).toNat) :
    RDinvalid code g s0 := by
  let lastIndex := solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩
  let move := solcSlotWord σ ee (clipperYankActiveSlot lastIndex)
  let idx := solcSlotWord σ ee (clipperYankSalesPosSlot ee)
  let activeMem := wordAt0Mem (⟨11⟩ : UInt256) mem
  let aw1 := UInt256.ofNat (MachineState.M aw.toNat 0 32)
  let aw2 := UInt256.ofNat (MachineState.M aw1.toNat 0 32)
  let saleKeyMem := wordAt0Mem (clipperYankArgWord ee) activeMem
  let aw3 := UInt256.ofNat (MachineState.M aw2.toNat 0 32)
  let saleHashMem := twoWordHashMem (clipperYankArgWord ee) ⟨12⟩ activeMem
  let aw4 := UInt256.ofNat (MachineState.M aw3.toNat 32 32)
  let aw5 := UInt256.ofNat (MachineState.M aw4.toNat 0 64)
  have rd8277 := evm_run rd with [
    raw jumpdest (by clipper_yank_remove_decode) (by evm_ov),
    raw push1 ⟨11⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw dup1 (by clipper_yank_remove_decode) (by evm_ov)]
  obtain ⟨_, _, rd8279⟩ := rd8277.sload (by clipper_yank_remove_decode) (by evm_ov)
  have rd8294 := evm_run rd8279 with [
    raw push1 ⟨0⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw swap2 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw not (by clipper_yank_remove_decode) (by evm_ov),
    raw dup2 (by clipper_yank_remove_decode) (by evm_ov),
    raw add (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw dup2 (by clipper_yank_remove_decode) (by evm_ov),
    raw lt (by clipper_yank_remove_decode) (by evm_ov),
    raw push2 ⟨8296⟩ (by clipper_yank_remove_decode) (by evm_ov)]
  have hcond :
      UInt256.lt (solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩)
        (solcSlotWord σ ee ⟨11⟩) = ⟨1⟩ :=
    clipperYankNonzeroLenPredLt (solcSlotWord σ ee ⟨11⟩) hlen
  have hcondNe :
      UInt256.lt (solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩)
        (solcSlotWord σ ee ⟨11⟩) ≠ ⟨0⟩ := by
    rw [hcond]
    native_decide
  have rd8296 := rd8294.jumpiT (by clipper_yank_remove_decode)
    (by simpa [solcSlotWord] using hcondNe)
    (clipperYankJumpDest8296 v hpatch) (by evm_ov)
  have rd8300 := evm_run rd8296 with [
    raw jumpdest (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8301 := rd8300.mstore (Cₘ aw1 - Cₘ aw) activeMem aw1
    (by clipper_yank_remove_decode)
    (by
      intro s hawEq hstk
      exact mstoreCost_of_stack hawEq hstk (by simp [aw1]))
    (by simpa [activeMem, wordAt0Mem]) (by rfl) (by evm_ov)
  have hslot :
      UInt256.ofNat
          (fromByteArrayBigEndian (ffi.KEC (activeMem.readWithPadding 0 32))) =
        activeDataSlot := by
    simpa [activeMem, activeDataSlot,
      show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨32⟩ : UInt256).toNat = 32 from by decide] using
      (wordAt0Mem_keccak_word (⟨11⟩ : UInt256) mem).trans
        (keccakSlot_eq (UInt256.toByteArray (⟨11⟩ : UInt256)))
  have rd8305 := evm_run rd8301 with [
    raw push1 ⟨32⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8306 := rd8305.keccak256 (Cₘ aw2 - Cₘ aw1) activeDataSlot aw2
    (by clipper_yank_remove_decode)
    (by
      intro s hawEq hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hawEq, hstk, aw2,
        show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨32⟩ : UInt256).toNat = 32 from by decide])
    hslot (by rfl) (by evm_ov)
  have rd8307pre := evm_run rd8306 with [
    raw add (by clipper_yank_remove_decode) (by evm_ov)]
  have hslotActive :
      activeDataSlot + (solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩) =
        clipperYankActiveSlot lastIndex := by
    simpa [lastIndex, clipperYankActiveSlot_eq]
  obtain ⟨k8307, C8307, rd8307slot⟩ :
      ∃ k C, RD code ee g s0 ⟨8307⟩
        (clipperYankActiveSlot lastIndex :: ⟨0⟩ :: clipperYankArgWord ee :: ⟨2540⟩ ::
          clipperYankArgWord ee :: ⟨502⟩ :: [sel])
        activeMem aw2 o (cA, σ) k C := by
    exact ⟨_, _, by simpa [solcSlotWord, hslotActive] using rd8307pre⟩
  obtain ⟨_, _, rd8308raw⟩ := rd8307slot.sload (by clipper_yank_remove_decode) (by evm_ov)
  obtain ⟨k8308, C8308, rd8308⟩ :
      ∃ k C, RD code ee g s0 ⟨8308⟩
        (move :: ⟨0⟩ :: clipperYankArgWord ee :: ⟨2540⟩ ::
          clipperYankArgWord ee :: ⟨502⟩ :: [sel])
        activeMem aw2 o (cA, σ) k C := by
    exact ⟨_, _, by simpa [move, solcSlotWord] using rd8308raw⟩
  have rd8312 := evm_run rd8308 with [
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw pop (by clipper_yank_remove_decode) (by evm_ov),
    raw dup1 (by clipper_yank_remove_decode) (by evm_ov),
    raw dup3 (by clipper_yank_remove_decode) (by evm_ov),
    raw eq (by clipper_yank_remove_decode) (by evm_ov)]
  have hneMove : clipperYankArgWord ee ≠ move := by
    simpa [lastIndex, move] using hne
  have hneCond : UInt256.eq (clipperYankArgWord ee) move = ⟨0⟩ :=
    uInt256_eq_zero_of_ne (by
      intro hEqOne
      exact hneMove (uInt256_eq_one_eq hEqOne))
  have rd8316 := evm_run rd8312 with [
    raw push2 ⟨8379⟩ (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8317 := rd8316.jumpiNT (by clipper_yank_remove_decode)
    (by simpa using hneCond) (by evm_ov)
  have rd8321pre := evm_run rd8317 with [
    raw push1 ⟨0⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw dup3 (by clipper_yank_remove_decode) (by evm_ov),
    raw dup2 (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8322 := rd8321pre.mstore (Cₘ aw3 - Cₘ aw2) saleKeyMem aw3
    (by clipper_yank_remove_decode)
    (by
      intro s hawEq hstk
      exact mstoreCost_of_stack hawEq hstk (by simp [aw3]))
    (by simpa [saleKeyMem, wordAt0Mem]) (by rfl) (by evm_ov)
  have rd8326pre := evm_run rd8322 with [
    raw push1 ⟨12⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8327 := rd8326pre.mstore (Cₘ aw4 - Cₘ aw3) saleHashMem aw4
    (by clipper_yank_remove_decode)
    (by
      intro s hawEq hstk
      exact mstoreCost_of_stack hawEq hstk (by
        simp [aw4, show (⟨32⟩ : UInt256).toNat = 32 from by decide]))
    (by rfl) (by rfl) (by evm_ov)
  have hsalesBase :
      UInt256.ofNat
          (fromByteArrayBigEndian (ffi.KEC (saleHashMem.readWithPadding 0 64))) =
        clipperYankSalesBaseSlot ee := by
    change
      UInt256.ofNat
          (fromByteArrayBigEndian
            (ffi.KEC
              ((twoWordHashMem (clipperYankArgWord ee) (⟨12⟩ : UInt256) activeMem).readWithPadding
                0 64))) =
        clipperYankSalesBaseSlot ee
    rw [clipperYankTwoWordHashMem_read0_64_of_ge
      (clipperYankArgWord ee) (⟨12⟩ : UInt256) (by
        simpa [activeMem] using hactiveMemSize)]
    rw [clipperYankSalesBaseSlot_eq ee]
    exact mappingSlot_single (clipperYankArgWord ee) ⟨12⟩
  have rd8330pre := evm_run rd8327 with [
    raw push1 ⟨64⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8331pre := rd8330pre.keccak256 (Cₘ aw5 - Cₘ aw4) (clipperYankSalesBaseSlot ee) aw5
    (by clipper_yank_remove_decode)
    (by
      intro s hawEq hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hawEq, hstk, aw5,
        show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide])
    hsalesBase (by rfl) (by evm_ov)
  obtain ⟨_, _, rd8332raw⟩ := rd8331pre.sload (by clipper_yank_remove_decode) (by evm_ov)
  obtain ⟨k8332, C8332, rd8332⟩ :
      ∃ k C, RD code ee g s0 ⟨8332⟩
        (idx :: move :: clipperYankArgWord ee :: ⟨2540⟩ :: clipperYankArgWord ee :: ⟨502⟩ ::
          [sel])
        saleHashMem aw5 o (cA, σ) k C := by
    exact ⟨_, _, by simpa [idx, clipperYankSalesPosSlot, solcSlotWord] using rd8332raw⟩
  have rd8346 := evm_run rd8332 with [
    raw push1 ⟨11⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw dup1 (by clipper_yank_remove_decode) (by evm_ov)]
  obtain ⟨_, _, rd8336raw⟩ := rd8346.sload (by clipper_yank_remove_decode) (by evm_ov)
  have rd8347pre := evm_run rd8336raw with [
    raw dup4 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap2 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw dup4 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw dup2 (by clipper_yank_remove_decode) (by evm_ov),
    raw lt (by clipper_yank_remove_decode) (by evm_ov),
    raw push2 ⟨8348⟩ (by clipper_yank_remove_decode) (by evm_ov)]
  have hidxCond : UInt256.lt idx (solcSlotWord σ ee ⟨11⟩) = ⟨0⟩ :=
    ult_zero hidxBound
  exact RD.invalidHalt
    (rd8347pre.jumpiNT (by clipper_yank_remove_decode)
      (by simpa [idx, solcSlotWord] using hidxCond) (by evm_ov))
    (by clipper_yank_remove_decode)

abbrev clipperYankPopAccountMap (σ : AccountMap) (I : ExecutionEnv)
    (lastIndex : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner
    (sstoreAccountMap I.codeOwner σ (clipperYankActiveSlot lastIndex) ⟨0⟩)
    ⟨11⟩ lastIndex

abbrev clipperYankDeleteSaleAccountMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  let base := clipperYankSalesBaseSlot I
  let σ0 := sstoreAccountMap I.codeOwner σ base ⟨0⟩
  let σ1 := sstoreAccountMap I.codeOwner σ0 (base + ⟨1⟩) ⟨0⟩
  let σ2 := sstoreAccountMap I.codeOwner σ1 (base + ⟨2⟩) ⟨0⟩
  let σ3 := sstoreAccountMap I.codeOwner σ2 (base + ⟨3⟩) ⟨0⟩
  sstoreAccountMap I.codeOwner σ3 (base + ⟨4⟩) ⟨0⟩

abbrev clipperYankRemoveAccountMap (σ : AccountMap) (I : ExecutionEnv)
    (lastIndex : UInt256) : AccountMap :=
  clipperYankDeleteSaleAccountMap (clipperYankPopAccountMap σ I lastIndex) I

abbrev clipperYankSuccessAccountMap (σ : AccountMap) (I : ExecutionEnv)
    (lastIndex : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner (clipperYankRemoveAccountMap σ I lastIndex) ⟨13⟩ ⟨0⟩

theorem clipperAccountEquiv_trans {a b c : Account}
    (hab : accountEquiv a b) (hbc : accountEquiv b c) :
    accountEquiv a c := by
  rcases hab with ⟨hn1, hb1, hc1, hs1, ht1⟩
  rcases hbc with ⟨hn2, hb2, hc2, hs2, ht2⟩
  exact ⟨hn1.trans hn2, hb1.trans hb2, hc1.trans hc2,
    fun slot => (hs1 slot).trans (hs2 slot),
    fun slot => (ht1 slot).trans (ht2 slot)⟩

theorem clipperAccountMapEquiv_trans {σ τ υ : AccountMap}
    (hστ : accountMapEquiv σ τ) (hτυ : accountMapEquiv τ υ) :
    accountMapEquiv σ υ := by
  intro addr
  specialize hστ addr
  specialize hτυ addr
  cases hσ : σ.find? addr <;> cases hτ : τ.find? addr <;>
    cases hυ : υ.find? addr <;> simp [hσ, hτ, hυ] at hστ hτυ ⊢
  exact clipperAccountEquiv_trans hστ hτυ

theorem clipperYankRemovePopState_accountMap (evm : EVM.State)
    (I : ExecutionEnv) (lastIndex : UInt256)
    (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    (clipperYankRemovePopState evm lastIndex).accountMap =
      clipperYankPopAccountMap evm.accountMap I lastIndex := by
  simp [clipperYankRemovePopState, clipperYankPopAccountMap, storageStore_accountMap,
    howner]

theorem clipperYankPopAccountMap_accountMapEquiv {σ τ : AccountMap}
    (I : ExecutionEnv) (lastIndex : UInt256)
    (hAccounts : accountMapEquiv σ τ) :
    accountMapEquiv (clipperYankPopAccountMap σ I lastIndex)
      (clipperYankPopAccountMap τ I lastIndex) := by
  unfold clipperYankPopAccountMap
  exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨11⟩ lastIndex
    (accountMapEquiv_sstoreAccountMap I.codeOwner
      (clipperYankActiveSlot lastIndex) ⟨0⟩ hAccounts)

set_option maxHeartbeats 2000000 in
theorem clipperYankDeleteSaleState_accountMapEquiv
    {σ : AccountMap} (evm : EVM.State) (I : ExecutionEnv)
    (hAccounts : accountMapEquiv σ evm.accountMap)
    (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    accountMapEquiv (clipperYankDeleteSaleAccountMap σ I)
      (clipperYankDeleteSaleState evm I).accountMap := by
  let base := clipperYankSalesBaseSlot I
  let σ0 := sstoreAccountMap I.codeOwner σ base ⟨0⟩
  let σ1 := sstoreAccountMap I.codeOwner σ0 (base + ⟨1⟩) ⟨0⟩
  let σ2 := sstoreAccountMap I.codeOwner σ1 (base + ⟨2⟩) ⟨0⟩
  let σ3 := sstoreAccountMap I.codeOwner σ2 (base + ⟨3⟩) ⟨0⟩
  let evm0 := Solm.EVM.storageStore evm evm.executionEnv.codeOwner base ⟨0⟩
  let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (base + ⟨1⟩) ⟨0⟩
  let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner (base + ⟨2⟩) ⟨0⟩
  let usrVal :=
    UInt256.land (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner (base + ⟨3⟩))
      (UInt256.lnot solcAddrMask)
  let evmUsr := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner (base + ⟨3⟩) usrVal
  let evm3 := Solm.EVM.storageStore evmUsr evmUsr.executionEnv.codeOwner (base + ⟨3⟩) ⟨0⟩
  have howner0 : evm0.executionEnv.codeOwner = I.codeOwner := by
    simp [evm0, storageStore_executionEnv, howner]
  have howner1 : evm1.executionEnv.codeOwner = I.codeOwner := by
    simp [evm1, storageStore_executionEnv, howner0]
  have howner2 : evm2.executionEnv.codeOwner = I.codeOwner := by
    simp [evm2, storageStore_executionEnv, howner1]
  have hownerUsr : evmUsr.executionEnv.codeOwner = I.codeOwner := by
    simp [evmUsr, storageStore_executionEnv, howner2]
  have howner3 : evm3.executionEnv.codeOwner = I.codeOwner := by
    simp [evm3, storageStore_executionEnv, hownerUsr]
  have h0 : accountMapEquiv σ0 evm0.accountMap := by
    simpa [σ0, evm0, storageStore_accountMap, howner] using
      accountMapEquiv_sstoreAccountMap I.codeOwner base ⟨0⟩ hAccounts
  have h1 : accountMapEquiv σ1 evm1.accountMap := by
    simpa [σ1, evm1, storageStore_accountMap, howner0] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (base + ⟨1⟩) ⟨0⟩ h0
  have h2 : accountMapEquiv σ2 evm2.accountMap := by
    simpa [σ2, evm2, storageStore_accountMap, howner1] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (base + ⟨2⟩) ⟨0⟩ h1
  have h3same : accountMapEquiv σ3
      (Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner (base + ⟨3⟩) ⟨0⟩).accountMap := by
    simpa [σ3, storageStore_accountMap, howner2] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (base + ⟨3⟩) ⟨0⟩ h2
  have h3extra :
      accountMapEquiv
        (Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner (base + ⟨3⟩) ⟨0⟩).accountMap
        evm3.accountMap := by
    let τ := evm2.accountMap
    have hleft :
        (Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner (base + ⟨3⟩) ⟨0⟩).accountMap =
          sstoreAccountMap I.codeOwner τ (base + ⟨3⟩) ⟨0⟩ := by
      simp [τ, storageStore_accountMap, howner2]
    have husrMap :
        evmUsr.accountMap =
          sstoreAccountMap I.codeOwner τ (base + ⟨3⟩) usrVal := by
      simp [τ, evmUsr, storageStore_accountMap, howner2]
    have hright :
        evm3.accountMap =
          sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner τ (base + ⟨3⟩) usrVal)
            (base + ⟨3⟩) ⟨0⟩ := by
      simp [evm3, storageStore_accountMap, hownerUsr, husrMap]
    rw [hleft, hright]
    have hfinalTrue : ((⟨0⟩ : UInt256) == (default : UInt256)) = true := by native_decide
    intro addr
    by_cases haddr : addr = I.codeOwner
    · subst addr
      unfold sstoreAccountMap
      cases hτ : τ.find? I.codeOwner with
      | none =>
          simp [hτ, Option.option]
      | some acc =>
          simp [Option.option, accountMap_find_insert_self]
          by_cases hzero : usrVal = (default : UInt256)
          · simpa [hzero] using accountEquiv_update_erase_self acc (base + ⟨3⟩) usrVal
          · simpa [hzero] using accountEquiv_update_erase_self acc (base + ⟨3⟩) usrVal
    · unfold sstoreAccountMap
      cases hτ : τ.find? I.codeOwner
      · simp only [hτ, Option.option]
        cases τ.find? addr <;> simp [accountEquiv_refl]
      · simp only [Option.option, hfinalTrue]
        rw [accountMap_find_insert_self]
        rw [accountMap_find?_insert_ne τ addr I.codeOwner _ haddr]
        rw [accountMap_find?_insert_ne (τ.insert I.codeOwner _) addr I.codeOwner _ haddr]
        rw [accountMap_find?_insert_ne τ addr I.codeOwner _ haddr]
        cases τ.find? addr <;> simp [accountEquiv_refl]
  have h3 : accountMapEquiv σ3 evm3.accountMap :=
    clipperAccountMapEquiv_trans h3same h3extra
  have h4 :
      accountMapEquiv (sstoreAccountMap I.codeOwner σ3 (base + ⟨4⟩) ⟨0⟩)
        (Solm.EVM.storageStore evm3 evm3.executionEnv.codeOwner (base + ⟨4⟩) ⟨0⟩).accountMap := by
    simpa [storageStore_accountMap, howner3] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (base + ⟨4⟩) ⟨0⟩ h3
  simpa [clipperYankDeleteSaleAccountMap, clipperYankDeleteSaleState, base, σ0, σ1, σ2,
    σ3, evm0, evm1, evm2, usrVal, evmUsr, evm3, storageStore_executionEnv] using h4

set_option maxHeartbeats 1000000 in
theorem clipperYankSuccessAccountMap_state_accountMapEquiv
    {σ τ : AccountMap} (evm : EVM.State) (I : ExecutionEnv) (lastIndex : UInt256)
    (hAccounts : accountMapEquiv σ τ)
    (hevm : evm.accountMap = τ)
    (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    accountMapEquiv (clipperYankSuccessAccountMap σ I lastIndex)
      (let evmPop := clipperYankRemovePopState evm lastIndex
       let evmRemove := clipperYankDeleteSaleState evmPop I
       (Solm.EVM.storageStore evmRemove evmRemove.executionEnv.codeOwner ⟨13⟩ ⟨0⟩).accountMap) := by
  have hpop :
      accountMapEquiv (clipperYankPopAccountMap σ I lastIndex)
        (clipperYankRemovePopState evm lastIndex).accountMap := by
    rw [clipperYankRemovePopState_accountMap evm I lastIndex howner]
    exact clipperYankPopAccountMap_accountMapEquiv I lastIndex (by simpa [hevm] using hAccounts)
  have hpopOwner :
      (clipperYankRemovePopState evm lastIndex).executionEnv.codeOwner = I.codeOwner := by
    simp [clipperYankRemovePopState, storageStore_executionEnv, howner]
  have hdel :=
    clipperYankDeleteSaleState_accountMapEquiv (clipperYankRemovePopState evm lastIndex) I
      hpop hpopOwner
  simpa [clipperYankSuccessAccountMap, clipperYankRemoveAccountMap,
    storageStore_accountMap, storageStore_executionEnv, howner] using
    accountMapEquiv_sstoreAccountMap I.codeOwner ⟨13⟩ ⟨0⟩ hdel

set_option maxHeartbeats 1000000 in
theorem RD.clipperYankRemoveJoinSuccess
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {sel move : UInt256}
    {cA σ}
    (rd : RD code ee g s0 ⟨8379⟩
      (move :: clipperYankArgWord ee :: ⟨2540⟩ :: clipperYankArgWord ee :: ⟨502⟩ :: [sel])
      mem aw o (cA, σ) k C)
    (hlen : solcSlotWord σ ee ⟨11⟩ ≠ ⟨0⟩)
    (hactiveMemSize : 64 ≤ (wordAt0Mem (⟨11⟩ : UInt256) mem).size)
    (hperm : ee.perm = true) :
    let lastIndex := solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩
    RDret code g s0 (cA, clipperYankSuccessAccountMap σ ee lastIndex) ByteArray.empty := by
  intro lastIndex
  let len := solcSlotWord σ ee ⟨11⟩
  let activeMem := wordAt0Mem (⟨11⟩ : UInt256) mem
  let aw1 := UInt256.ofNat (MachineState.M aw.toNat 0 32)
  let aw2 := UInt256.ofNat (MachineState.M aw1.toNat 0 32)
  let saleKeyMem := wordAt0Mem (clipperYankArgWord ee) activeMem
  let saleHashMem := twoWordHashMem (clipperYankArgWord ee) ⟨12⟩ activeMem
  let aw3 := UInt256.ofNat (MachineState.M aw2.toNat 0 32)
  let aw4 := UInt256.ofNat (MachineState.M aw3.toNat 32 32)
  let aw5 := UInt256.ofNat (MachineState.M aw4.toNat 0 64)
  let base := clipperYankSalesBaseSlot ee
  let σSale0 :=
    sstoreAccountMap ee.codeOwner (clipperYankPopAccountMap σ ee lastIndex) base ⟨0⟩
  let σSale1 := sstoreAccountMap ee.codeOwner σSale0 (base + ⟨1⟩) ⟨0⟩
  let σSale2 := sstoreAccountMap ee.codeOwner σSale1 (base + ⟨2⟩) ⟨0⟩
  let σSale3 := sstoreAccountMap ee.codeOwner σSale2 (base + ⟨3⟩) ⟨0⟩
  let σRemoved := clipperYankRemoveAccountMap σ ee lastIndex
  have rd8384 := evm_run rd with [
    raw jumpdest (by clipper_yank_remove_decode) (by evm_ov),
    raw push1 ⟨11⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw dup1 (by clipper_yank_remove_decode) (by evm_ov)]
  obtain ⟨_, _, rd8384raw⟩ := rd8384.sload (by clipper_yank_remove_decode) (by evm_ov)
  have rd8388 := evm_run rd8384raw with [
    raw dup1 (by clipper_yank_remove_decode) (by evm_ov),
    raw push2 ⟨8390⟩ (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8390 := rd8388.jumpiT (by clipper_yank_remove_decode)
    (by simpa [len, solcSlotWord] using hlen)
    (clipperYankJumpDest8390 v hpatch) (by evm_ov)
  have rd8395pre := evm_run rd8390 with [
    raw jumpdest (by clipper_yank_remove_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw dup3 (by clipper_yank_remove_decode) (by evm_ov),
    raw dup2 (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8396 := rd8395pre.mstore (Cₘ aw1 - Cₘ aw) activeMem aw1
    (by clipper_yank_remove_decode)
    (by
      intro s hawEq hstk
      exact mstoreCost_of_stack hawEq hstk (by simp [aw1]))
    (by simpa [activeMem, wordAt0Mem]) (by rfl) (by evm_ov)
  have hslot :
      UInt256.ofNat
          (fromByteArrayBigEndian (ffi.KEC (activeMem.readWithPadding 0 32))) =
        activeDataSlot := by
    simpa [activeMem, activeDataSlot,
      show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨32⟩ : UInt256).toNat = 32 from by decide] using
      (wordAt0Mem_keccak_word (⟨11⟩ : UInt256) mem).trans
        (keccakSlot_eq (UInt256.toByteArray (⟨11⟩ : UInt256)))
  have rd8400pre := evm_run rd8396 with [
    raw push1 ⟨32⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw dup1 (by clipper_yank_remove_decode) (by evm_ov),
    raw dup3 (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8401 := rd8400pre.keccak256 (Cₘ aw2 - Cₘ aw1) activeDataSlot aw2
    (by clipper_yank_remove_decode)
    (by
      intro s hawEq hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hawEq, hstk, aw2,
        show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨32⟩ : UInt256).toNat = 32 from by decide])
    hslot (by rfl) (by evm_ov)
  have rd8411pre := evm_run rd8401 with [
    raw dup4 (by clipper_yank_remove_decode) (by evm_ov),
    raw add (by clipper_yank_remove_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw not (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw dup2 (by clipper_yank_remove_decode) (by evm_ov),
    raw add (by clipper_yank_remove_decode) (by evm_ov),
    raw dup4 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov)]
  have hslotActive :
      activeDataSlot + (solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩) =
        clipperYankActiveSlot lastIndex := by
    simpa [lastIndex, clipperYankActiveSlot_eq]
  have hslotActive' :
      UInt256.lnot ⟨0⟩ + (solcSlotWord σ ee ⟨11⟩ + activeDataSlot) =
        clipperYankActiveSlot lastIndex := by
    rw [← u256_add_assoc]
    rw [u256_add_comm (UInt256.lnot ⟨0⟩) (solcSlotWord σ ee ⟨11⟩)]
    rw [u256_add_assoc]
    rw [u256_add_comm (UInt256.lnot ⟨0⟩) activeDataSlot]
    rw [← u256_add_assoc]
    rw [u256_add_comm (solcSlotWord σ ee ⟨11⟩) activeDataSlot]
    rw [u256_add_assoc]
    exact hslotActive
  obtain ⟨k8412, C8412, rd8412⟩ :
      ∃ k C, RD code ee g s0 ⟨8412⟩
        (UInt256.lnot ⟨0⟩ :: ⟨32⟩ :: ⟨0⟩ :: solcSlotWord σ ee ⟨11⟩ :: ⟨11⟩ ::
          move :: clipperYankArgWord ee :: ⟨2540⟩ :: clipperYankArgWord ee :: ⟨502⟩ ::
            [sel])
        activeMem aw2 o
        (cA, sstoreAccountMap ee.codeOwner σ (clipperYankActiveSlot lastIndex) ⟨0⟩)
        k C := by
    obtain ⟨k', C', rd'⟩ := rd8411pre.sstore hperm (by clipper_yank_remove_decode)
      (by simp only [List.length_cons, List.length_nil]; omega)
    exact ⟨k', C', by simpa [solcSlotWord, hslotActive'] using rd'⟩
  have rd8417pre := evm_run rd8412 with [
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap3 (by clipper_yank_remove_decode) (by evm_ov),
    raw add (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap3 (by clipper_yank_remove_decode) (by evm_ov)]
  obtain ⟨k8418, C8418, rd8418⟩ :
      ∃ k C, RD code ee g s0 ⟨8418⟩
        (⟨32⟩ :: ⟨0⟩ :: move :: clipperYankArgWord ee :: ⟨2540⟩ ::
          clipperYankArgWord ee :: ⟨502⟩ :: [sel])
        activeMem aw2 o (cA, clipperYankPopAccountMap σ ee lastIndex) k C := by
    obtain ⟨k', C', rd'⟩ := rd8417pre.sstore hperm (by clipper_yank_remove_decode)
      (by simp only [List.length_cons, List.length_nil]; omega)
    exact ⟨k', C', by
      simpa [clipperYankPopAccountMap, lastIndex] using rd'⟩
  have rd8420pre := evm_run rd8418 with [
    raw swap3 (by clipper_yank_remove_decode) (by evm_ov),
    raw dup2 (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8421 := rd8420pre.mstore (Cₘ aw3 - Cₘ aw2) saleKeyMem aw3
    (by clipper_yank_remove_decode)
    (by
      intro s hawEq hstk
      exact mstoreCost_of_stack hawEq hstk (by simp [aw3]))
    (by simpa [saleKeyMem, wordAt0Mem]) (by rfl) (by evm_ov)
  have rd8425pre := evm_run rd8421 with [
    raw push1 ⟨12⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap3 (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8426 := rd8425pre.mstore (Cₘ aw4 - Cₘ aw3) saleHashMem aw4
    (by clipper_yank_remove_decode)
    (by
      intro s hawEq hstk
      exact mstoreCost_of_stack hawEq hstk (by
        simp [aw4, show (⟨32⟩ : UInt256).toNat = 32 from by decide]))
    (by rfl) (by rfl) (by evm_ov)
  have hbase :
      UInt256.ofNat
          (fromByteArrayBigEndian (ffi.KEC (saleHashMem.readWithPadding 0 64))) =
        base := by
    change
      UInt256.ofNat
          (fromByteArrayBigEndian
            (ffi.KEC
              ((twoWordHashMem (clipperYankArgWord ee) (⟨12⟩ : UInt256) activeMem).readWithPadding
                0 64))) =
        clipperYankSalesBaseSlot ee
    rw [clipperYankTwoWordHashMem_read0_64_of_ge
      (clipperYankArgWord ee) (⟨12⟩ : UInt256) hactiveMemSize]
    rw [clipperYankSalesBaseSlot_eq ee]
    exact mappingSlot_single (clipperYankArgWord ee) ⟨12⟩
  have rd8431 := evm_run rd8426 with [
    raw pop (by clipper_yank_remove_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw dup2 (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8431hash := rd8431.keccak256 (Cₘ aw5 - Cₘ aw4) base aw5
    (by clipper_yank_remove_decode)
    (by
      intro s hawEq hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hawEq, hstk, aw5,
        show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide])
    hbase (by rfl) (by evm_ov)
  have rd8433pre := evm_run rd8431hash with [
    raw dup2 (by clipper_yank_remove_decode) (by evm_ov),
    raw dup2 (by clipper_yank_remove_decode) (by evm_ov)]
  obtain ⟨k8434, C8434, rd8434⟩ :
      ∃ k C, RD code ee g s0 ⟨8434⟩
        (base :: ⟨0⟩ :: ⟨2540⟩ :: clipperYankArgWord ee :: ⟨502⟩ :: [sel])
        saleHashMem aw5 o (cA, σSale0) k C := by
    obtain ⟨k', C', rd'⟩ := rd8433pre.sstore hperm (by clipper_yank_remove_decode)
      (by simp only [List.length_cons, List.length_nil]; omega)
    exact ⟨k', C', by simpa [base, σSale0] using rd'⟩
  have rd8440pre := evm_run rd8434 with [
    raw push1 ⟨1⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw dup2 (by clipper_yank_remove_decode) (by evm_ov),
    raw add (by clipper_yank_remove_decode) (by evm_ov),
    raw dup3 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov)]
  obtain ⟨k8441, C8441, rd8441⟩ :
      ∃ k C, RD code ee g s0 ⟨8441⟩
        (base :: ⟨0⟩ :: ⟨2540⟩ :: clipperYankArgWord ee :: ⟨502⟩ :: [sel])
        saleHashMem aw5 o (cA, σSale1) k C := by
    obtain ⟨k', C', rd'⟩ := rd8440pre.sstore hperm (by clipper_yank_remove_decode)
      (by simp only [List.length_cons, List.length_nil]; omega)
    exact ⟨k', C', by simpa [σSale1] using rd'⟩
  have rd8447pre := evm_run rd8441 with [
    raw push1 ⟨2⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw dup2 (by clipper_yank_remove_decode) (by evm_ov),
    raw add (by clipper_yank_remove_decode) (by evm_ov),
    raw dup3 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov)]
  obtain ⟨k8448, C8448, rd8448⟩ :
      ∃ k C, RD code ee g s0 ⟨8448⟩
        (base :: ⟨0⟩ :: ⟨2540⟩ :: clipperYankArgWord ee :: ⟨502⟩ :: [sel])
        saleHashMem aw5 o (cA, σSale2) k C := by
    obtain ⟨k', C', rd'⟩ := rd8447pre.sstore hperm (by clipper_yank_remove_decode)
      (by simp only [List.length_cons, List.length_nil]; omega)
    exact ⟨k', C', by simpa [σSale2] using rd'⟩
  have rd8454pre := evm_run rd8448 with [
    raw push1 ⟨3⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw dup2 (by clipper_yank_remove_decode) (by evm_ov),
    raw add (by clipper_yank_remove_decode) (by evm_ov),
    raw dup3 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov)]
  obtain ⟨k8455, C8455, rd8455⟩ :
      ∃ k C, RD code ee g s0 ⟨8455⟩
        (base :: ⟨0⟩ :: ⟨2540⟩ :: clipperYankArgWord ee :: ⟨502⟩ :: [sel])
        saleHashMem aw5 o (cA, σSale3) k C := by
    obtain ⟨k', C', rd'⟩ := rd8454pre.sstore hperm (by clipper_yank_remove_decode)
      (by simp only [List.length_cons, List.length_nil]; omega)
    exact ⟨k', C', by simpa [σSale3] using rd'⟩
  have rd8458pre := evm_run rd8455 with [
    raw push1 ⟨4⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw add (by clipper_yank_remove_decode) (by evm_ov)]
  obtain ⟨k8459, C8459, rd8459⟩ :
      ∃ k C, RD code ee g s0 ⟨8459⟩
        (⟨2540⟩ :: clipperYankArgWord ee :: ⟨502⟩ :: [sel])
        saleHashMem aw5 o (cA, σRemoved) k C := by
    obtain ⟨k', C', rd'⟩ := rd8458pre.sstore hperm (by clipper_yank_remove_decode)
      (by simp only [List.length_cons, List.length_nil]; omega)
    exact ⟨k', C', by
      simpa [σRemoved, clipperYankRemoveAccountMap, clipperYankDeleteSaleAccountMap,
        σSale0, σSale1, σSale2, σSale3, base,
        u256_add_comm (⟨4⟩ : UInt256) base] using rd'⟩
  have rd2540 := rd8459.jump (by clipper_yank_remove_decode)
    (clipperYankJumpDest2540 v hpatch) (by evm_ov)
  let freePtr :=
    if (⟨64⟩ : UInt256).toNat ≥ saleHashMem.size ∨ (⟨64⟩ : UInt256) ≥ aw5 * ⟨32⟩ then
      (⟨0⟩ : UInt256)
    else
      UInt256.ofNat (fromByteArrayBigEndian (saleHashMem.readWithPadding 64 32))
  let aw6 := UInt256.ofNat (MachineState.M aw5.toNat 64 32)
  let eventMem := (clipperYankArgWord ee).toByteArray.write 0 saleHashMem freePtr.toNat 32
  let aw7 := UInt256.ofNat (MachineState.M aw6.toNat freePtr.toNat 32)
  let freePtrBase :=
    if (⟨64⟩ : UInt256).toNat ≥ eventMem.size ∨ (⟨64⟩ : UInt256) ≥ aw7 * ⟨32⟩ then
      (⟨0⟩ : UInt256)
    else
      UInt256.ofNat (fromByteArrayBigEndian (eventMem.readWithPadding 64 32))
  let aw8 := UInt256.ofNat (MachineState.M aw7.toNat 64 32)
  let yankTopic : UInt256 :=
    ⟨20066359233804962805847604945324360652817654806409140269471901996943370884174⟩
  have rd2544pre := evm_run rd2540 with [
    raw jumpdest (by clipper_yank_post_remove_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_yank_post_remove_decode) (by evm_ov),
    raw dup1 (by clipper_yank_post_remove_decode) (by evm_ov)]
  have rd2545 := rd2544pre.mload (Cₘ aw6 - Cₘ aw5) freePtr aw6
    (by clipper_yank_post_remove_decode)
    (by
      intro s hawEq hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hawEq, hstk, aw6,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide])
    (by rfl) (by rfl) (by evm_ov)
  have rd2547pre := evm_run rd2545 with [
    raw dup3 (by clipper_yank_post_remove_decode) (by evm_ov),
    raw dup2 (by clipper_yank_post_remove_decode) (by evm_ov)]
  have rd2548 := rd2547pre.mstore (Cₘ aw7 - Cₘ aw6) eventMem aw7
    (by clipper_yank_post_remove_decode)
    (by
      intro s hawEq hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hawEq, hstk, aw7])
    (by rfl) (by rfl) (by evm_ov)
  have rd2549pre := evm_run rd2548 with [
    raw swap1 (by clipper_yank_post_remove_decode) (by evm_ov)]
  have rd2550 := rd2549pre.mload (Cₘ aw8 - Cₘ aw7) freePtrBase aw8
    (by clipper_yank_post_remove_decode)
    (by
      intro s hawEq hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hawEq, hstk, aw8,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide])
    (by rfl) (by rfl) (by evm_ov)
  have rd2583 := rd2550.pushConst yankTopic (width := 32) (op := .PUSH32)
    (by decide)
    (by simpa [yankTopic] using
      (show decode code ⟨2550⟩ = some (.PUSH32, some (yankTopic, 32)) by
        clipper_yank_post_remove_decode))
    (by evm_ov)
  have rd2591pre := evm_run rd2583 with [
    raw swap2 (by clipper_yank_post_remove_decode) (by evm_ov),
    raw dup2 (by clipper_yank_post_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_post_remove_decode) (by evm_ov),
    raw sub (by clipper_yank_post_remove_decode) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_yank_post_remove_decode) (by evm_ov),
    raw add (by clipper_yank_post_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_post_remove_decode) (by evm_ov)]
  let logSize := (⟨32⟩ : UInt256) + UInt256.sub freePtr freePtrBase
  let aw9 := UInt256.ofNat (MachineState.M aw8.toNat freePtrBase.toNat logSize.toNat)
  have rd2592 : RD code ee g s0 ⟨2592⟩
      (clipperYankArgWord ee :: ⟨502⟩ :: [sel])
      eventMem aw9 o (cA, σRemoved) (k8459 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
      (C8459 + 8 + 1 + 3 + 3 + (Cₘ aw6 - Cₘ aw5 + 3) + 3 + 3 +
        (Cₘ aw7 - Cₘ aw6 + 3) + 3 + (Cₘ aw8 - Cₘ aw7 + 3) + 3 + 3 + 3 +
        3 + 3 + 3 + 3 + 3 +
        (Cₘ aw9 - Cₘ aw8 +
          (GasConstants.Glog + GasConstants.Glogdata * logSize.toNat +
            GasConstants.Glogtopic))) := by
    simpa [logSize, aw9] using
      (RD.log1 (Cₘ aw9 - Cₘ aw8) aw9 rd2591pre
        (by clipper_yank_post_remove_decode) hperm
        (by
          intro s hawEq hstk
          simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hawEq, hstk, aw9, logSize])
        (by simp [aw9, logSize])
        (by evm_ov))
  have rd2597pre := evm_run rd2592 with [
    raw pop (by clipper_yank_post_remove_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_yank_post_remove_decode) (by evm_ov),
    raw push1 ⟨13⟩ (by clipper_yank_post_remove_decode) (by evm_ov)]
  obtain ⟨k2598, C2598, rd2598⟩ :
      ∃ k C, RD code ee g s0 ⟨2598⟩ (⟨502⟩ :: [sel])
        eventMem aw9 o (cA, clipperYankSuccessAccountMap σ ee lastIndex) k C := by
    obtain ⟨k', C', rd'⟩ := rd2597pre.sstore hperm (by clipper_yank_post_remove_decode)
      (by simp only [List.length_cons, List.length_nil]; omega)
    exact ⟨k', C', by simpa [clipperYankSuccessAccountMap, σRemoved] using rd'⟩
  have rd502 := rd2598.jump (by clipper_yank_post_remove_decode)
    (clipperRelyReturnJumpDest v hpatch) (by evm_ov)
  have rd503 := rd502.jumpdest (by clipper_decode) (by evm_ov)
  exact RD.stop rd503 (by clipper_decode) (by evm_ov)

theorem RD.clipperYankRemoveJoinEmptyInvalid
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {sel move : UInt256}
    {cA σ}
    (rd : RD code ee g s0 ⟨8379⟩
      (move :: clipperYankArgWord ee :: ⟨2540⟩ :: clipperYankArgWord ee :: ⟨502⟩ :: [sel])
      mem aw o (cA, σ) k C)
    (hlen : solcSlotWord σ ee ⟨11⟩ = ⟨0⟩) :
    RDinvalid code g s0 := by
  let len := solcSlotWord σ ee ⟨11⟩
  have rd8384 := evm_run rd with [
    raw jumpdest (by clipper_yank_remove_decode) (by evm_ov),
    raw push1 ⟨11⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw dup1 (by clipper_yank_remove_decode) (by evm_ov)]
  obtain ⟨_, _, rd8384raw⟩ := rd8384.sload (by clipper_yank_remove_decode) (by evm_ov)
  have rd8388 := evm_run rd8384raw with [
    raw dup1 (by clipper_yank_remove_decode) (by evm_ov),
    raw push2 ⟨8390⟩ (by clipper_yank_remove_decode) (by evm_ov)]
  exact RD.invalidHalt
    (rd8388.jumpiNT (by clipper_yank_remove_decode)
      (by simpa [len, solcSlotWord] using hlen) (by evm_ov))
    (by clipper_yank_remove_decode)

end Benchmarks.Dss.Clipper
