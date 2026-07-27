import Benchmarks.Dss.Clipper.StatusPriceCall
import Benchmarks.Dss.Clipper.TakeStatus
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

theorem clipperTakeJumpDest3527 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨3527⟩ : UInt256) = true := by
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

theorem clipperTakeJumpDest3604 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨3604⟩ : UInt256) = true := by
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

theorem clipperTakeJumpDest3694 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨3694⟩ : UInt256) = true := by
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

theorem clipperTakeJumpDest3821 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨3821⟩ : UInt256) = true := by
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

theorem clipperTakeJumpDest3852 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨3852⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 5000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperTakeJumpDest3929 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨3929⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 5000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperTakeJumpDest4007 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨4007⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 5000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperTakeJumpDest4045 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨4045⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 5000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperTakeJumpDest4057 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨4057⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 5000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperTakeJumpDest4079 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨4079⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 5000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperTakeJumpDest4087 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨4087⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 5000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperTakeJumpDest4101 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨4101⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 5000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperTakeJumpDest4223 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨4223⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 5000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperTakeJumpDest4392 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨4392⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 5000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperTakeJumpDest4412 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨4412⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 5000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperTakeJumpDest4494 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨4494⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 5000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperTakeJumpDest4524 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨4524⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 5000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperTakeJumpDest4701 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨4701⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 5000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

abbrev clipperTakeIlkWord (v : ClipperImmutables) : UInt256 :=
  match v.ilk with
  | .fixedBytes _ bs => EVM.Word.ofNat (fromBytesBigEndian bs)
  | _ => ⟨0⟩

abbrev clipperTakeVatTarget (v : ClipperImmutables) : UInt256 :=
  UInt256.land solcAddrMask (EVM.Word.ofNat (↑v.vat : Nat))

abbrev clipperTakeVatFluxSelectorSeed : UInt256 :=
  ⟨814276375⟩

abbrev clipperTakeVatFluxSelectorShifted : UInt256 :=
  UInt256.shiftLeft clipperTakeVatFluxSelectorSeed ⟨225⟩

abbrev clipperTakeVatFluxSelectorWord : UInt256 :=
  ⟨1628552750⟩

abbrev clipperTakeThisWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.codeOwner.val

noncomputable def clipperTakeVatFluxSelectorMem (mem : ByteArray) : ByteArray :=
  clipperTakeVatFluxSelectorShifted.toByteArray.write 0 mem 128 32

noncomputable def clipperTakeVatFluxIlkMem (v : ClipperImmutables)
    (mem : ByteArray) : ByteArray :=
  (clipperTakeIlkWord v).toByteArray.write 0 (clipperTakeVatFluxSelectorMem mem) 132 32

noncomputable def clipperTakeVatFluxThisMem (I : ExecutionEnv)
    (mem : ByteArray) : ByteArray :=
  (clipperTakeThisWord I).toByteArray.write 0 mem 164 32

noncomputable def clipperTakeVatFluxWhoMem (who : UInt256) (mem : ByteArray) :
    ByteArray :=
  (UInt256.land solcAddrMask who).toByteArray.write 0 mem 196 32

noncomputable def clipperTakeVatFluxCalldataMem (v : ClipperImmutables)
    (I : ExecutionEnv) (who slice : UInt256) (mem : ByteArray) : ByteArray :=
  slice.toByteArray.write 0
    (clipperTakeVatFluxWhoMem who
      (clipperTakeVatFluxThisMem I (clipperTakeVatFluxIlkMem v mem)))
    228 32

theorem clipperTakeVatFluxSelectorMem_size {mem : ByteArray} (hmem : mem.size = 196) :
    (clipperTakeVatFluxSelectorMem mem).size = 196 := by
  unfold clipperTakeVatFluxSelectorMem
  exact toByteArray_write32_size_of_le mem clipperTakeVatFluxSelectorShifted 128 196 196
    hmem (by rw [hmem]; omega) (by omega)

theorem clipperTakeVatFluxIlkMem_size (v : ClipperImmutables) {mem : ByteArray}
    (hmem : mem.size = 196) :
    (clipperTakeVatFluxIlkMem v mem).size = 196 := by
  unfold clipperTakeVatFluxIlkMem
  exact toByteArray_write32_size_of_le (clipperTakeVatFluxSelectorMem mem)
    (clipperTakeIlkWord v) 132 196 196 (clipperTakeVatFluxSelectorMem_size hmem)
    (by rw [clipperTakeVatFluxSelectorMem_size hmem]; omega) (by omega)

theorem clipperTakeVatFluxThisMem_size (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 196) :
    (clipperTakeVatFluxThisMem I mem).size = 196 := by
  unfold clipperTakeVatFluxThisMem
  exact toByteArray_write32_size_of_le mem (clipperTakeThisWord I) 164 196 196 hmem
    (by rw [hmem]; omega) (by omega)

theorem clipperTakeVatFluxWhoMem_size (who : UInt256) {mem : ByteArray}
    (hmem : mem.size = 196) :
    (clipperTakeVatFluxWhoMem who mem).size = 228 := by
  unfold clipperTakeVatFluxWhoMem
  exact toByteArray_write32_size_of_le mem (UInt256.land solcAddrMask who) 196 196 228
    hmem (by rw [hmem]) (by native_decide)

theorem clipperTakeVatFluxCalldataMem_size (v : ClipperImmutables)
    (I : ExecutionEnv) (who slice : UInt256) {mem : ByteArray}
    (hmem : mem.size = 196) :
    (clipperTakeVatFluxCalldataMem v I who slice mem).size = 260 := by
  have hIlk : (clipperTakeVatFluxIlkMem v mem).size = 196 :=
    clipperTakeVatFluxIlkMem_size v hmem
  have hThis : (clipperTakeVatFluxThisMem I (clipperTakeVatFluxIlkMem v mem)).size =
      196 :=
    clipperTakeVatFluxThisMem_size I hIlk
  have hWho :
      (clipperTakeVatFluxWhoMem who
        (clipperTakeVatFluxThisMem I (clipperTakeVatFluxIlkMem v mem))).size = 228 :=
    clipperTakeVatFluxWhoMem_size who hThis
  unfold clipperTakeVatFluxCalldataMem
  exact toByteArray_write32_size_of_le
    (clipperTakeVatFluxWhoMem who
      (clipperTakeVatFluxThisMem I (clipperTakeVatFluxIlkMem v mem))) slice 228 228 260
    hWho (by rw [hWho]) (by native_decide)

theorem clipperTakeVatFluxSelectorMem_read64 {mem : ByteArray}
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperTakeVatFluxSelectorMem mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperTakeVatFluxSelectorMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
    (by rw [hmem]; native_decide) (by omega), hread64]

theorem clipperTakeVatFluxIlkMem_read64 (v : ClipperImmutables) {mem : ByteArray}
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperTakeVatFluxIlkMem v mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperTakeVatFluxIlkMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [clipperTakeVatFluxSelectorMem_size hmem]; native_decide) (by omega),
    clipperTakeVatFluxSelectorMem_read64 hmem hread64]

theorem clipperTakeVatFluxThisMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperTakeVatFluxThisMem I mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperTakeVatFluxThisMem
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
    (by rw [hmem]; native_decide) (by omega), hread64]

theorem clipperTakeVatFluxWhoMem_read64 (who : UInt256) {mem : ByteArray}
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperTakeVatFluxWhoMem who mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperTakeVatFluxWhoMem
  rw [write32_read_below _ _ 196 64 (by rw [toByteArray_size])
    (by rw [hmem]) (by omega), hread64]

theorem clipperTakeVatFluxCalldataMem_read64 (v : ClipperImmutables)
    (I : ExecutionEnv) (who slice : UInt256) {mem : ByteArray}
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperTakeVatFluxCalldataMem v I who slice mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  have hIlk : (clipperTakeVatFluxIlkMem v mem).size = 196 :=
    clipperTakeVatFluxIlkMem_size v hmem
  have hThis : (clipperTakeVatFluxThisMem I (clipperTakeVatFluxIlkMem v mem)).size =
      196 :=
    clipperTakeVatFluxThisMem_size I hIlk
  have hWho :
      (clipperTakeVatFluxWhoMem who
        (clipperTakeVatFluxThisMem I (clipperTakeVatFluxIlkMem v mem))).size = 228 :=
    clipperTakeVatFluxWhoMem_size who hThis
  unfold clipperTakeVatFluxCalldataMem
  rw [write32_read_below _ _ 228 64 (by rw [toByteArray_size])
    (by rw [hWho]) (by omega)]
  exact clipperTakeVatFluxWhoMem_read64 who hThis
    (clipperTakeVatFluxThisMem_read64 I hIlk
      (clipperTakeVatFluxIlkMem_read64 v hmem hread64))

theorem clipperTakeVatFluxCalldataMem_mload64 (v : ClipperImmutables)
    (I : ExecutionEnv) (who slice : UInt256) {mem : ByteArray}
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (clipperTakeVatFluxCalldataMem v I who slice mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((clipperTakeVatFluxCalldataMem v I who slice mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ := by
  exact mloadFreePtrValue
    (mem := clipperTakeVatFluxCalldataMem v I who slice mem) (aw := UInt256.ofNat 9)
    (by rw [clipperTakeVatFluxCalldataMem_size v I who slice hmem]; norm_num)
    (by decide)
    (clipperTakeVatFluxCalldataMem_read64 v I who slice hmem hread64)

theorem clipperTakeVatFluxSelectorMem_read128_4 {mem : ByteArray}
    (hmem : mem.size = 196) :
    (clipperTakeVatFluxSelectorMem mem).readWithPadding 128 4 = vatFluxSelector := by
  unfold clipperTakeVatFluxSelectorMem
  rw [toByteArray_write_read_window_of_gap clipperTakeVatFluxSelectorShifted mem 128 0 4
    (by norm_num) (by norm_num) (by norm_num) (by rw [hmem]; native_decide)]
  rw [toByteArray_eq_toBytesBE]
  native_decide

theorem clipperTakeVatFluxCalldataMem_read128_4 (v : ClipperImmutables)
    (I : ExecutionEnv) (who slice : UInt256) {mem : ByteArray}
    (hmem : mem.size = 196) :
    (clipperTakeVatFluxCalldataMem v I who slice mem).readWithPadding 128 4 =
      vatFluxSelector := by
  have hIlk : (clipperTakeVatFluxIlkMem v mem).size = 196 :=
    clipperTakeVatFluxIlkMem_size v hmem
  have hThis : (clipperTakeVatFluxThisMem I (clipperTakeVatFluxIlkMem v mem)).size =
      196 :=
    clipperTakeVatFluxThisMem_size I hIlk
  have hWho :
      (clipperTakeVatFluxWhoMem who
        (clipperTakeVatFluxThisMem I (clipperTakeVatFluxIlkMem v mem))).size = 228 :=
    clipperTakeVatFluxWhoMem_size who hThis
  unfold clipperTakeVatFluxCalldataMem
  rw [write32_read_below_len _ _ 228 128 4 (by rw [toByteArray_size])
    (by rw [hWho]) (by omega) (by rw [hWho]; omega) (by norm_num) (by norm_num)]
  unfold clipperTakeVatFluxWhoMem
  rw [write32_read_below_len _ _ 196 128 4 (by rw [toByteArray_size])
    (by rw [hThis]) (by omega) (by rw [hThis]; omega) (by norm_num) (by norm_num)]
  unfold clipperTakeVatFluxThisMem
  rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
    (by rw [hIlk]; omega) (by omega) (by rw [hIlk]; omega) (by norm_num)
    (by norm_num)]
  unfold clipperTakeVatFluxIlkMem
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by rw [clipperTakeVatFluxSelectorMem_size hmem]; omega) (by omega)
    (by rw [clipperTakeVatFluxSelectorMem_size hmem]; omega) (by norm_num)
    (by norm_num)]
  exact clipperTakeVatFluxSelectorMem_read128_4 hmem

theorem clipperTakeVatFluxCalldataMem_read132_32 (v : ClipperImmutables)
    (I : ExecutionEnv) (who slice : UInt256) {mem : ByteArray}
    (hmem : mem.size = 196) :
    (clipperTakeVatFluxCalldataMem v I who slice mem).readWithPadding 132 32 =
      UInt256.toByteArray (clipperTakeIlkWord v) := by
  have hIlk : (clipperTakeVatFluxIlkMem v mem).size = 196 :=
    clipperTakeVatFluxIlkMem_size v hmem
  have hThis : (clipperTakeVatFluxThisMem I (clipperTakeVatFluxIlkMem v mem)).size =
      196 :=
    clipperTakeVatFluxThisMem_size I hIlk
  have hWho :
      (clipperTakeVatFluxWhoMem who
        (clipperTakeVatFluxThisMem I (clipperTakeVatFluxIlkMem v mem))).size = 228 :=
    clipperTakeVatFluxWhoMem_size who hThis
  unfold clipperTakeVatFluxCalldataMem
  rw [write32_read_below _ _ 228 132 (by rw [toByteArray_size])
    (by rw [hWho]) (by omega)]
  unfold clipperTakeVatFluxWhoMem
  rw [write32_read_below _ _ 196 132 (by rw [toByteArray_size])
    (by rw [hThis]) (by omega)]
  unfold clipperTakeVatFluxThisMem
  rw [write32_read_below _ _ 164 132 (by rw [toByteArray_size])
    (by rw [hIlk]; omega) (by omega)]
  unfold clipperTakeVatFluxIlkMem
  rw [write32_read_back _ _ 132 (by rw [toByteArray_size])
    (by rw [clipperTakeVatFluxSelectorMem_size hmem]; omega)]
  rw [show (UInt256.toByteArray (clipperTakeIlkWord v)).extract 0 32 =
      UInt256.toByteArray (clipperTakeIlkWord v) by
    rw [show 32 = (UInt256.toByteArray (clipperTakeIlkWord v)).size by
      rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem clipperTakeVatFluxCalldataMem_read164_32 (v : ClipperImmutables)
    (I : ExecutionEnv) (who slice : UInt256) {mem : ByteArray}
    (hmem : mem.size = 196) :
    (clipperTakeVatFluxCalldataMem v I who slice mem).readWithPadding 164 32 =
      UInt256.toByteArray (clipperTakeThisWord I) := by
  have hIlk : (clipperTakeVatFluxIlkMem v mem).size = 196 :=
    clipperTakeVatFluxIlkMem_size v hmem
  have hThis : (clipperTakeVatFluxThisMem I (clipperTakeVatFluxIlkMem v mem)).size =
      196 :=
    clipperTakeVatFluxThisMem_size I hIlk
  have hWho :
      (clipperTakeVatFluxWhoMem who
        (clipperTakeVatFluxThisMem I (clipperTakeVatFluxIlkMem v mem))).size = 228 :=
    clipperTakeVatFluxWhoMem_size who hThis
  unfold clipperTakeVatFluxCalldataMem
  rw [write32_read_below _ _ 228 164 (by rw [toByteArray_size])
    (by rw [hWho]) (by omega)]
  unfold clipperTakeVatFluxWhoMem
  rw [write32_read_below _ _ 196 164 (by rw [toByteArray_size])
    (by rw [hThis]) (by omega)]
  unfold clipperTakeVatFluxThisMem
  rw [write32_read_back _ _ 164 (by rw [toByteArray_size])
    (by rw [hIlk]; omega)]
  rw [show (UInt256.toByteArray (clipperTakeThisWord I)).extract 0 32 =
      UInt256.toByteArray (clipperTakeThisWord I) by
    rw [show 32 = (UInt256.toByteArray (clipperTakeThisWord I)).size by
      rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem clipperTakeVatFluxCalldataMem_read196_32 (v : ClipperImmutables)
    (I : ExecutionEnv) (who slice : UInt256) {mem : ByteArray}
    (hmem : mem.size = 196) :
    (clipperTakeVatFluxCalldataMem v I who slice mem).readWithPadding 196 32 =
      UInt256.toByteArray (UInt256.land solcAddrMask who) := by
  have hIlk : (clipperTakeVatFluxIlkMem v mem).size = 196 :=
    clipperTakeVatFluxIlkMem_size v hmem
  have hThis : (clipperTakeVatFluxThisMem I (clipperTakeVatFluxIlkMem v mem)).size =
      196 :=
    clipperTakeVatFluxThisMem_size I hIlk
  have hWho :
      (clipperTakeVatFluxWhoMem who
        (clipperTakeVatFluxThisMem I (clipperTakeVatFluxIlkMem v mem))).size = 228 :=
    clipperTakeVatFluxWhoMem_size who hThis
  unfold clipperTakeVatFluxCalldataMem
  rw [write32_read_below _ _ 228 196 (by rw [toByteArray_size])
    (by rw [hWho]) (by omega)]
  unfold clipperTakeVatFluxWhoMem
  rw [write32_read_back _ _ 196 (by rw [toByteArray_size]) (by rw [hThis])]
  rw [show (UInt256.toByteArray (UInt256.land solcAddrMask who)).extract 0 32 =
      UInt256.toByteArray (UInt256.land solcAddrMask who) by
    rw [show 32 = (UInt256.toByteArray (UInt256.land solcAddrMask who)).size by
      rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem clipperTakeVatFluxCalldataMem_read228_32 (v : ClipperImmutables)
    (I : ExecutionEnv) (who slice : UInt256) {mem : ByteArray}
    (hmem : mem.size = 196) :
    (clipperTakeVatFluxCalldataMem v I who slice mem).readWithPadding 228 32 =
      UInt256.toByteArray slice := by
  have hIlk : (clipperTakeVatFluxIlkMem v mem).size = 196 :=
    clipperTakeVatFluxIlkMem_size v hmem
  have hThis : (clipperTakeVatFluxThisMem I (clipperTakeVatFluxIlkMem v mem)).size =
      196 :=
    clipperTakeVatFluxThisMem_size I hIlk
  have hWho :
      (clipperTakeVatFluxWhoMem who
        (clipperTakeVatFluxThisMem I (clipperTakeVatFluxIlkMem v mem))).size = 228 :=
    clipperTakeVatFluxWhoMem_size who hThis
  unfold clipperTakeVatFluxCalldataMem
  rw [write32_read_back _ _ 228 (by rw [toByteArray_size]) (by rw [hWho])]
  rw [show (UInt256.toByteArray slice).extract 0 32 = UInt256.toByteArray slice by
    rw [show 32 = (UInt256.toByteArray slice).size by rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem clipperTakeVatFluxCalldataMem_read128_132 (v : ClipperImmutables)
    (I : ExecutionEnv) (who slice : UInt256) {mem : ByteArray}
    (hmem : mem.size = 196) :
    (clipperTakeVatFluxCalldataMem v I who slice mem).readWithPadding 128 132 =
      vatFluxSelector ++ UInt256.toByteArray (clipperTakeIlkWord v) ++
        UInt256.toByteArray (clipperTakeThisWord I) ++
        UInt256.toByteArray (UInt256.land solcAddrMask who) ++
        UInt256.toByteArray slice := by
  rw [byteArray_readWithPadding_split _ 128 4 128 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [clipperTakeVatFluxCalldataMem_size v I who slice hmem])]
  rw [byteArray_readWithPadding_split _ 132 32 96 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [clipperTakeVatFluxCalldataMem_size v I who slice hmem])]
  rw [byteArray_readWithPadding_split _ 164 32 64 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [clipperTakeVatFluxCalldataMem_size v I who slice hmem])]
  rw [byteArray_readWithPadding_split _ 196 32 32 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [clipperTakeVatFluxCalldataMem_size v I who slice hmem])]
  rw [clipperTakeVatFluxCalldataMem_read128_4 v I who slice hmem,
    clipperTakeVatFluxCalldataMem_read132_32 v I who slice hmem,
    clipperTakeVatFluxCalldataMem_read164_32 v I who slice hmem,
    clipperTakeVatFluxCalldataMem_read196_32 v I who slice hmem,
    clipperTakeVatFluxCalldataMem_read228_32 v I who slice hmem]
  simp [ByteArray.append_assoc]

theorem clipperTakeWhoAddressWord (who : UInt256) :
    EVM.word (AccountAddress.ofNat who.toNat).val =
      UInt256.land who solcAddrMask := by
  apply u256_inj
  rw [u256_land_toNat]
  unfold EVM.word EVM.uintN AccountAddress.ofNat
  simp only [UInt256.toNat, Fin.ofNat]
  rw [show (↑solcAddrMask.val : Nat) = 2 ^ 160 - 1 from by decide]
  rw [nat_land_mask_eq_mod]
  rw [show AccountAddress.size = 2 ^ 160 from by native_decide,
    show EVM.twoPow 256 = UInt256.size from by native_decide]

theorem clipperTakeVatFluxEncode_eq (v : ClipperImmutables) (I : ExecutionEnv)
    (who slice : UInt256) {mem : ByteArray} (hmem : mem.size = 196) :
    (config v).externalABI.encode? "flux"
      [v.ilk, .address I.codeOwner, .address (AccountAddress.ofNat who.toNat),
        .int (Int.ofNat slice.toNat)] =
      some ((clipperTakeVatFluxCalldataMem v I who slice mem).readWithPadding 128 132) := by
  rcases v.ilk_wf with ⟨bs, hilk, hlen⟩
  rw [hilk]
  have hilkWord :
      clipperTakeIlkWord v = EVM.Word.ofNat (fromBytesBigEndian bs) := by
    simp [clipperTakeIlkWord, hilk]
  rw [clipperTakeVatFluxCalldataMem_read128_132 v I who slice hmem, hilkWord]
  have hbytes :
      bs = EVM.Word.toBytesBE (EVM.Word.ofNat (fromBytesBigEndian bs)) := by
    have hword : ABI.bytesToWord bs = EVM.Word.ofNat (fromBytesBigEndian bs) := by
      unfold ABI.bytesToWord fromByteArrayBigEndian
      simp [byteArray_toList_eq, EVM.Word.ofNat]
    rw [← hword]
    exact (toBytesBE_bytesToWord_of_length hlen).symm
  have hwordBytes :
      (EVM.Word.ofNat (fromBytesBigEndian bs)).toByteArray =
        { data := bs.toArray } := by
    rw [← word_toBytesBE_toByteArray_eq_toByteArray
      (EVM.Word.ofNat (fromBytesBigEndian bs)), ← hbytes]
    apply ByteArray.ext
    simp
  have hbsByteArray : bs.toByteArray = { data := bs.toArray } := by
    apply ByteArray.ext
    apply Array.toList_inj.mp
    rw [List.toList_data_toByteArray]
  have hthis : EVM.word I.codeOwner = clipperTakeThisWord I := by
    unfold clipperTakeThisWord EVM.word EVM.uintN UInt256.ofNat
    rfl
  have hwho : EVM.word (AccountAddress.ofNat who.toNat).val =
      UInt256.land who solcAddrMask :=
    clipperTakeWhoAddressWord who
  have hsliceWord : EVM.word slice.toNat = slice := u256_ofNat_toNat slice
  have hsliceLt : slice.toNat < EVM.twoPow 256 := by
    change slice.val.val < UInt256.size
    exact slice.val.isLt
  change externalABI.encode? "flux"
      [.fixedBytes ⟨31, by decide⟩ bs, .address I.codeOwner,
        .address (AccountAddress.ofNat who.toNat), .int (Int.ofNat slice.toNat)] =
    some (vatFluxSelector ++ UInt256.toByteArray (EVM.Word.ofNat (fromBytesBigEndian bs)) ++
      UInt256.toByteArray (clipperTakeThisWord I) ++
      UInt256.toByteArray (UInt256.land solcAddrMask who) ++ UInt256.toByteArray slice)
  unfold externalABI ABI.encodeCallWithSelector? ABI.encodeABIValues?
  simp [ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType, bytes32,
    bytes32Width, addr, uint256, uint256Int, selectorBytes, vatFluxSelector, hlen,
    ABI.zeroBytes, hwordBytes, hbsByteArray, hsliceLt, hsliceWord, hthis, hwho,
    u256_land_comm, word_toBytesBE_toByteArray_eq_toByteArray, ByteArray.append_assoc]

theorem clipperTakeVatTargetAddress (v : ClipperImmutables) :
    AccountAddress.ofUInt256 (clipperTakeVatTarget v) = v.vat := by
  have hvatWordToNat : (EVM.Word.ofNat (↑v.vat : Nat)).toNat = ↑v.vat := by
    simp [EVM.Word.ofNat, UInt256.ofNat, UInt256.toNat, Fin.ofNat]
    exact Nat.mod_eq_of_lt (lt_of_lt_of_le v.vat.isLt (by decide))
  have hclean :
      UInt256.land solcAddrMask (EVM.Word.ofNat (↑v.vat : Nat)) =
        EVM.Word.ofNat (↑v.vat : Nat) := by
    exact solcAddrMask_clean_left (w := EVM.Word.ofNat (↑v.vat : Nat)) (by
      rw [hvatWordToNat]
      simp [EVM.addressModulus, EVM.twoPow, AccountAddress.size])
  rw [clipperTakeVatTarget, hclean]
  simpa [EVM.Word.ofNat] using accountAddress_roundtrip v.vat

theorem clipperTakeEVMAddressAccountAddress (a : AccountAddress) :
    EVM.address a = a := by
  apply Fin.ext
  simp [EVM.address, EVM.uintN]
  exact Nat.mod_eq_of_lt (by simp [EVM.twoPow, AccountAddress.size])

theorem clipperTakeIlkPatchPayload4239 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {bs : List UInt8} (hilk : v.ilk = .fixedBytes ⟨31, by decide⟩ bs)
    (hlen : bs.length = 32) :
    code.extract' 4239 4271 =
      ({ data := (EVM.Word.ofNat (fromBytesBigEndian bs)).toBytesBE.toArray } :
        ByteArray) := by
  let ilkBytes : ByteArray :=
    { data := (EVM.Word.ofNat (fromBytesBigEndian bs)).toBytesBE.toArray }
  let vatBytes : ByteArray :=
    { data := (EVM.Word.ofNat (↑v.vat : Nat)).toBytesBE.toArray }
  have hsize : ilkBytes.size = 32 := by
    simpa [ilkBytes] using
      word_toBytesBE_toByteArray_size (EVM.Word.ofNat (fromBytesBigEndian bs))
  have hpost :
      PatchesWindowDisjoint32 4239 4271
        [(4866, ilkBytes), (5046, ilkBytes), (6800, ilkBytes), (8747, ilkBytes),
          (1463, vatBytes), (2437, vatBytes), (3145, vatBytes), (4318, vatBytes),
          (4441, vatBytes), (4751, vatBytes), (5115, vatBytes), (6295, vatBytes),
          (7936, vatBytes)] := by
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | hfalse
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · cases hfalse
  exact patchRuntime_extract'_exact_split (template := clipperBytecode)
    (pre := [(1510, ilkBytes), (1661, ilkBytes), (2221, ilkBytes), (2369, ilkBytes)])
    (post :=
      [(4866, ilkBytes), (5046, ilkBytes), (6800, ilkBytes), (8747, ilkBytes),
        (1463, vatBytes), (2437, vatBytes), (3145, vatBytes), (4318, vatBytes),
        (4441, vatBytes), (4751, vatBytes), (5115, vatBytes), (6295, vatBytes),
        (7936, vatBytes)])
    (off := 4239) (value := ilkBytes)
    (by
      simpa [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, hilk, hlen,
        List.lookup_cons, ilkBytes, vatBytes] using hpatch)
    hsize hpost (by norm_num) (by norm_num)

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem clipperTakeIlkPush32Decode4238 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {bs : List UInt8} (hilk : v.ilk = .fixedBytes ⟨31, by decide⟩ bs)
    (hlen : bs.length = 32) :
    decode code (⟨4238⟩ : UInt256) =
      some (.Push .PUSH32, some (EVM.Word.ofNat (fromBytesBigEndian bs), 32)) := by
  unfold decode
  rw [patchRuntime_get?_disjoint hpatch
    (clipperRuntimePatchesWindowDisjoint32Bool v (⟨4238⟩ : UInt256).toNat
      ((⟨4238⟩ : UInt256).toNat + 1) (by native_decide))]
  norm_num
  change some (Operation.Push Operation.POp.PUSH32,
      some (uInt256OfByteArray (code.extract' 4239 4271), 32)) =
    some (Operation.Push Operation.POp.PUSH32,
      some (EVM.Word.ofNat (fromBytesBigEndian bs), 32))
  rw [clipperTakeIlkPatchPayload4239 v hpatch hilk hlen]
  rw [uInt256OfByteArray_word_toBytesBE]

theorem clipperTakeVatPatchPayload4318 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    code.extract' 4318 4350 =
      ({ data := (EVM.Word.ofNat (↑v.vat : Nat)).toBytesBE.toArray } : ByteArray) := by
  rcases v.ilk_wf with ⟨bs, hilk, hlen⟩
  let ilkBytes : ByteArray :=
    { data := (EVM.Word.ofNat (fromBytesBigEndian bs)).toBytesBE.toArray }
  let vatBytes : ByteArray :=
    { data := (EVM.Word.ofNat (↑v.vat : Nat)).toBytesBE.toArray }
  have hsize : vatBytes.size = 32 := by
    simpa [vatBytes] using word_toBytesBE_toByteArray_size (EVM.Word.ofNat (↑v.vat : Nat))
  have hpost :
      PatchesWindowDisjoint32 4318 4350
        [(4441, vatBytes), (4751, vatBytes), (5115, vatBytes), (6295, vatBytes),
          (7936, vatBytes)] := by
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | hfalse
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · cases hfalse
  exact patchRuntime_extract'_exact_split (template := clipperBytecode)
    (pre :=
      [(1510, ilkBytes), (1661, ilkBytes), (2221, ilkBytes), (2369, ilkBytes),
        (4239, ilkBytes), (4866, ilkBytes), (5046, ilkBytes), (6800, ilkBytes),
        (8747, ilkBytes), (1463, vatBytes), (2437, vatBytes), (3145, vatBytes)])
    (post :=
      [(4441, vatBytes), (4751, vatBytes), (5115, vatBytes), (6295, vatBytes),
        (7936, vatBytes)])
    (off := 4318) (value := vatBytes)
    (by
      simpa [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, hilk, hlen,
        List.lookup_cons, ilkBytes, vatBytes] using hpatch)
    hsize hpost (by norm_num) (by norm_num)

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem clipperTakeVatPush32Decode4317 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    decode code (⟨4317⟩ : UInt256) =
      some (.Push .PUSH32, some (EVM.Word.ofNat (↑v.vat : Nat), 32)) := by
  unfold decode
  rw [patchRuntime_get?_disjoint hpatch
    (clipperRuntimePatchesWindowDisjoint32Bool v (⟨4317⟩ : UInt256).toNat
      ((⟨4317⟩ : UInt256).toNat + 1) (by native_decide))]
  norm_num
  change some (Operation.Push Operation.POp.PUSH32,
      some (uInt256OfByteArray (code.extract' 4318 4350), 32)) =
    some (Operation.Push Operation.POp.PUSH32, some (EVM.Word.ofNat (↑v.vat : Nat), 32))
  rw [clipperTakeVatPatchPayload4318 v hpatch]
  rw [uInt256OfByteArray_word_toBytesBE]

abbrev clipperTakeNeedsResetRawWord : UInt256 :=
  ⟨0x10db1a5c1c195c8bdb9959591ccb5c995cd95d⟩

abbrev clipperTakeTooExpensiveRawWord : UInt256 :=
  ⟨0x436c69707065722f746f6f2d657870656e73697665⟩

theorem clipperTakeTooExpensiveStringWord :
    UInt256.shiftLeft clipperTakeTooExpensiveRawWord ⟨88⟩ =
      ⟨30496508052792062404443629973729883021709103502700566185445971163008280297472⟩ := by
  native_decide

theorem clipperTakeLockedStringWord :
    UInt256.shiftLeft ⟨24634883019371952566956220926897864252907853633881⟩ ⟨90⟩ =
      ⟨30496508052792062404420069455133111715513420844312188351800969105462834233344⟩ := by
  native_decide

theorem clipperTakeStoppedStringWord :
    UInt256.shiftLeft ⟨105806016908988270734738552397420409440386134862091135834333⟩ ⟨58⟩ =
      ⟨30496508052792062404419589047915533211324476653882280781143920003575554506752⟩ := by
  native_decide

theorem clipperTakePayloadGt_zero {I : ExecutionEnv}
    (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size)
    (hoffMax : ¬ solcMaxLen DecodeMode.legacySolc05 < (clipperTakeDataOffsetWord I).toNat)
    (hlenWord : 4 + (clipperTakeDataOffsetWord I).toNat + 32 ≤ I.calldata.size)
    (hlenMax : ¬ solcMaxLen DecodeMode.legacySolc05 < (clipperTakeDataLenWord I).toNat)
    (hpayloadOk :
      (((I.calldata.toList.drop 4).drop ((clipperTakeDataOffsetWord I).toNat + 32)).take
        (clipperTakeDataLenWord I).toNat).length = (clipperTakeDataLenWord I).toNat) :
    UInt256.gt
      (((⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I) +
        UInt256.mul (clipperTakeDataLenWord I) ⟨1⟩))
      ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) = ⟨0⟩ := by
  apply ugt_zero
  have hoffLe : (clipperTakeDataOffsetWord I).toNat ≤ 4294967296 := by
    exact Nat.le_of_not_gt (by simpa [solcMaxLen, solcMaxLenV1] using hoffMax)
  have hlenLe : (clipperTakeDataLenWord I).toNat ≤ 4294967296 := by
    exact Nat.le_of_not_gt (by simpa [solcMaxLen, solcMaxLenV1] using hlenMax)
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htailGe :
      (clipperTakeDataLenWord I).toNat ≤
        (((I.calldata.toList.drop 4).drop
          ((clipperTakeDataOffsetWord I).toNat + 32))).length := by
    by_contra hnot
    have htailLt :
        (((I.calldata.toList.drop 4).drop
          ((clipperTakeDataOffsetWord I).toNat + 32))).length <
          (clipperTakeDataLenWord I).toNat :=
      Nat.lt_of_not_ge hnot
    have htakeLen :
        (((I.calldata.toList.drop 4).drop
          ((clipperTakeDataOffsetWord I).toNat + 32)).take
          (clipperTakeDataLenWord I).toNat).length =
          (((I.calldata.toList.drop 4).drop
            ((clipperTakeDataOffsetWord I).toNat + 32))).length := by
      rw [List.length_take, Nat.min_eq_right (Nat.le_of_lt htailLt)]
    omega
  have htailLen :
      (((I.calldata.toList.drop 4).drop
        ((clipperTakeDataOffsetWord I).toNat + 32))).length =
        I.calldata.size - 4 - ((clipperTakeDataOffsetWord I).toNat + 32) := by
    rw [List.length_drop, List.length_drop, htlen]
  have hpayloadEnd :
      32 + (4 + (clipperTakeDataOffsetWord I).toNat) +
          (clipperTakeDataLenWord I).toNat ≤ I.calldata.size := by
    rw [htailLen] at htailGe
    omega
  have hoff4 :
      (((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I).toNat) =
        4 + (clipperTakeDataOffsetWord I).toNat := by
    rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      Nat.mod_eq_of_lt (by
        have hbound : 4 + 4294967296 < UInt256.size := by native_decide
        omega)]
  have hmul1 :
      (UInt256.mul (clipperTakeDataLenWord I) (⟨1⟩ : UInt256)).toNat =
        (clipperTakeDataLenWord I).toNat := by
    rw [u256_mul_toNat, show (⟨1⟩ : UInt256).toNat = 1 from by decide, Nat.mul_one]
    exact Nat.mod_eq_of_lt
      (show (clipperTakeDataLenWord I).toNat < UInt256.size from
        (clipperTakeDataLenWord I).val.isLt)
  have hleft :
      ((((⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I) +
        UInt256.mul (clipperTakeDataLenWord I) ⟨1⟩)).toNat) =
        32 + (4 + (clipperTakeDataOffsetWord I).toNat) +
          (clipperTakeDataLenWord I).toNat := by
    rw [uadd_toNat]
    rw [uadd_toNat, hoff4, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
    nth_rewrite 2 [Nat.mod_eq_of_lt (by
      have hbound : 32 + (4 + 4294967296) < UInt256.size := by native_decide
      omega)]
    rw [hmul1]
    rw [Nat.mod_eq_of_lt (by
      have hbound : 32 + (4 + 4294967296) + 4294967296 < UInt256.size := by
        native_decide
      omega)]
  have hright :
      (((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩).toNat) =
        I.calldata.size := by
    rw [show (⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ =
        UInt256.ofNat I.calldata.size from
      uadd_word_usub_ofNat_word (n := I.calldata.size) (c := (⟨4⟩ : UInt256))
        (by simpa using hsz4) hsize]
    exact ulit_toNat' I.calldata.size hsize
  rw [hleft, hright]
  exact hpayloadEnd

theorem clipperTakeLockRevertTailWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcErrorStringRevertTailWf code (⟨3536⟩ : UInt256) ⟨21⟩
      ⟨24634883019371952566956220926897864252907853633881⟩ ⟨90⟩ .PUSH21 21 := by
  unfold solcErrorStringRevertTailWf
  dsimp
  refine
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩ <;> clipper_runtime_decode

theorem clipperTakeStoppedRevertTailWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcErrorStringRevertTailWf code (⟨3622⟩ : UInt256) ⟨25⟩
      ⟨105806016908988270734738552397420409440386134862091135834333⟩ ⟨58⟩ .PUSH25
      25 := by
  unfold solcErrorStringRevertTailWf
  dsimp
  refine
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩ <;> clipper_runtime_decode

theorem clipperTakeTooExpensiveRevertTailWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcErrorStringRevertTailWf code (⟨3939⟩ : UInt256) ⟨21⟩
      clipperTakeTooExpensiveRawWord ⟨88⟩ .PUSH21 21 := by
  unfold solcErrorStringRevertTailWf clipperTakeTooExpensiveRawWord
  dsimp
  refine
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩ <;> clipper_runtime_decode

set_option maxHeartbeats 1000000 in
theorem RD.clipperTakeStatusDoneTrueReverts {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {price : UInt256} {R : List UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD code ee g s0 ⟨3852⟩
      (price :: ⟨1⟩ :: ⟨0⟩ :: ⟨0⟩ :: R)
      mem (UInt256.ofNat 7) rdata (cA, σ) k C)
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 20 ≤ 1024) :
    RDrev code g s0 := by
  have rd3863 := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨3929⟩ (by clipper_runtime_decode) (by evm_ov),
    raw jumpiNT (by clipper_runtime_decode) (by native_decide) (by evm_ov)]
  have rdMload := evm_run rd3863 with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by clipper_runtime_decode)
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by clipper_runtime_decode)
    (by evm_ov)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 (solcErrorStringMem0 mem)
      (UInt256.ofNat 7) (by clipper_runtime_decode) mem_cost (by rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨4⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 (solcErrorStringMem1 mem)
      (UInt256.ofNat 7) (by clipper_runtime_decode) mem_cost (by rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨19⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨36⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 (solcErrorStringMem2 ⟨19⟩ mem)
      (UInt256.ofNat 7) (by clipper_runtime_decode) mem_cost (by rfl)
      (by decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst clipperTakeNeedsResetRawWord
    (width := 19) (op := .PUSH19) (by decide) (by clipper_runtime_decode)
    (by evm_ov)
  have rdWord := evm_run rdRaw with [
    raw push1 ⟨106⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov)]
  exact evm_run rdWord with [
    raw push1 ⟨68⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw mstore 3
      (solcErrorStringMem3 ⟨19⟩
        (UInt256.shiftLeft clipperTakeNeedsResetRawWord ⟨106⟩) mem)
      (UInt256.ofNat 8) (by clipper_runtime_decode) mem_cost (by rfl)
      (by decide) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by clipper_runtime_decode)
      mem_cost
      (solcErrorStringMem3_mload64_of_size196 ⟨19⟩
        (UInt256.shiftLeft clipperTakeNeedsResetRawWord ⟨106⟩) hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨100⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw rev 0 (by clipper_runtime_decode) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem RD.clipperTakeStatusFalseTooExpensiveReverts {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {price tic packed stopped dataLen dataStart who max : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {k C : ℕ}
    (h : RD code ee g s0 ⟨3852⟩
      (price :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: tic :: packed :: stopped ::
        dataLen :: dataStart :: who :: max :: R)
      mem (UInt256.ofNat 7) rdata (cA, σ) k C)
    (hmax : max.toNat < price.toNat)
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 20 ≤ 1024) :
    RDrev code g s0 := by
  have rd3929pre := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨3929⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd3929 := rd3929pre.jumpiT (by clipper_runtime_decode) (by native_decide)
    (clipperTakeJumpDest3929 v hpatch) (by evm_ov)
  have rd3934pre := evm_run rd3929 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw dup9 (by clipper_runtime_decode) (by evm_ov)]
  have rd3933 := rd3934pre.lt (by clipper_runtime_decode)
    (by simp only [List.length_cons]; omega)
  have hltWord : UInt256.lt max price = ⟨1⟩ := by
    exact ult_one hmax
  have hcondZero : UInt256.isZero (UInt256.lt max price) = ⟨0⟩ := by
    rw [hltWord]
    native_decide
  have rd3934 := rd3933.iszero (by clipper_runtime_decode) (by evm_ov)
  have rd3938 := evm_run rd3934 with [
    raw push2 ⟨4007⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd3939 := rd3938.jumpiNT (by clipper_runtime_decode)
    hcondZero (by evm_ov)
  have rdMload := evm_run rd3939 with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by clipper_runtime_decode)
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by clipper_runtime_decode)
    (by evm_ov)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 (solcErrorStringMem0 mem)
      (UInt256.ofNat 7) (by clipper_runtime_decode) mem_cost (by rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨4⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 (solcErrorStringMem1 mem)
      (UInt256.ofNat 7) (by clipper_runtime_decode) mem_cost (by rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨21⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨36⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 (solcErrorStringMem2 ⟨21⟩ mem)
      (UInt256.ofNat 7) (by clipper_runtime_decode) mem_cost (by rfl)
      (by decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst clipperTakeTooExpensiveRawWord
    (width := 21) (op := .PUSH21) (by decide) (by clipper_runtime_decode)
    (by evm_ov)
  have rdWord := evm_run rdRaw with [
    raw push1 ⟨88⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov)]
  exact evm_run rdWord with [
    raw push1 ⟨68⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw mstore 3
      (solcErrorStringMem3 ⟨21⟩
        (UInt256.shiftLeft clipperTakeTooExpensiveRawWord ⟨88⟩) mem)
      (UInt256.ofNat 8) (by clipper_runtime_decode) mem_cost (by rfl)
      (by decide) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by clipper_runtime_decode)
      mem_cost
      (solcErrorStringMem3_mload64_of_size196 ⟨21⟩
        (UInt256.shiftLeft clipperTakeTooExpensiveRawWord ⟨88⟩) hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨100⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw rev 0 (by clipper_runtime_decode) mem_cost (by evm_ov)]

theorem RD.clipperTakeStatusFalseMaxOk {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {price tic packed stopped dataLen dataStart who max : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {k C : ℕ}
    (h : RD code ee g s0 ⟨3852⟩
      (price :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: tic :: packed :: stopped ::
        dataLen :: dataStart :: who :: max :: R)
      mem (UInt256.ofNat 7) rdata (cA, σ) k C)
    (hmax : price.toNat ≤ max.toNat)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨4007⟩
      (price :: tic :: packed :: stopped :: dataLen :: dataStart :: who :: max :: R)
      mem (UInt256.ofNat 7) rdata (cA, σ) k' C' := by
  have rd3929pre := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨3929⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd3929 := rd3929pre.jumpiT (by clipper_runtime_decode) (by native_decide)
    (clipperTakeJumpDest3929 v hpatch) (by evm_ov)
  have rd3934pre := evm_run rd3929 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw dup9 (by clipper_runtime_decode) (by evm_ov)]
  have rd3933 := rd3934pre.lt (by clipper_runtime_decode)
    (by simp only [List.length_cons]; omega)
  have hltWord : UInt256.lt max price = ⟨0⟩ := by
    exact ult_zero hmax
  have hcondNe : UInt256.isZero (UInt256.lt max price) ≠ ⟨0⟩ := by
    rw [hltWord]
    native_decide
  have rd3934 := rd3933.iszero (by clipper_runtime_decode) (by evm_ov)
  have rd3938 := evm_run rd3934 with [
    raw push2 ⟨4007⟩ (by clipper_runtime_decode) (by evm_ov)]
  exact ⟨_, _, rd3938.jumpiT (by clipper_runtime_decode)
    hcondNe (clipperTakeJumpDest4007 v hpatch) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem RD.clipperTakeAfterMaxToMul {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {price tic packed stopped dataLen dataStart who max amt id : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {k C : ℕ}
    (h : RD code ee g s0 ⟨4007⟩
      (price :: tic :: packed :: stopped :: dataLen :: dataStart :: who ::
        max :: amt :: id :: R)
      mem (UInt256.ofNat 7) rdata (cA, σ) k C)
    (hmem : 64 ≤ mem.size)
    (hov : R.length + 40 ≤ 1024) :
    let base : UInt256 := solcMappingSlot ⟨12⟩ id
    let lot : UInt256 := solcSlotWord σ ee (base + ⟨2⟩)
    let tab : UInt256 := solcSlotWord σ ee (base + ⟨1⟩)
    let slice : UInt256 := clipperMinWord amt lot
    ∃ k' C', RD code ee g s0 ⟨8686⟩
      (price :: slice :: ⟨4057⟩ :: slice :: ⟨0⟩ :: tab :: lot ::
        price :: tic :: packed :: stopped :: dataLen :: dataStart :: who ::
        max :: amt :: id :: R)
      (twoWordHashMem id ⟨12⟩ mem) (UInt256.ofNat 7) rdata (cA, σ) k' C' := by
  intro base lot tab slice
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem id (⟨12⟩ : UInt256) mem).readWithPadding 0 64))) =
        base := by
    simpa [base] using twoWordHashMem_solcMappingSlot_of_ge (⟨12⟩ : UInt256) id hmem
  have rdHash := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup11 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 (wordAt0Mem id mem) (UInt256.ofNat 7)
      (by clipper_runtime_decode) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨12⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 (twoWordHashMem id (⟨12⟩ : UInt256) mem) (UInt256.ofNat 7)
      (by clipper_runtime_decode) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw keccak256 0 base (UInt256.ofNat 7) (by clipper_runtime_decode) mem_cost
      hslot (by native_decide) (by evm_ov),
    raw push1 ⟨2⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨kLot, CLot, rdLotRaw⟩ := rdHash.sload (by clipper_runtime_decode) (by evm_ov)
  have rdLot : RD code ee g s0 ⟨4027⟩
      (lot :: base :: ⟨0⟩ :: price :: tic :: packed :: stopped :: dataLen ::
        dataStart :: who :: max :: amt :: id :: R)
      (twoWordHashMem id ⟨12⟩ mem) (UInt256.ofNat 7) rdata (cA, σ) kLot CLot := by
    simpa [lot, solcSlotWord] using rdLotRaw
  have rdTabSlot := evm_run rdLot with [
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨kTab, CTab, rdTabRaw⟩ := rdTabSlot.sload (by clipper_runtime_decode) (by evm_ov)
  have rdTab : RD code ee g s0 ⟨4033⟩
      (tab :: lot :: ⟨0⟩ :: price :: tic :: packed :: stopped :: dataLen ::
        dataStart :: who :: max :: amt :: id :: R)
      (twoWordHashMem id ⟨12⟩ mem) (UInt256.ofNat 7) rdata (cA, σ) kTab CTab := by
    simpa [tab, solcSlotWord] using rdTabRaw
  have rd8661pre := evm_run rdTab with [
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4045⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw dup15 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8661⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd8661 := rd8661pre.jump (by clipper_runtime_decode)
    (clipperJumpDest8661 v hpatch) (by evm_ov)
  obtain ⟨_, _, rd4045⟩ :=
    Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperMin
      (v := v) (hpatch := hpatch) rd8661
      (clipperTakeJumpDest4045 v hpatch)
      (by simp only [List.length_cons]; omega)
  have rd8686pre := evm_run rd4045 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4057⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw dup7 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8686⟩ (by clipper_runtime_decode) (by evm_ov)]
  exact ⟨_, _, by
    simpa [slice] using rd8686pre.jump (by clipper_runtime_decode)
      (clipperJumpDest8686 v hpatch) (by evm_ov)⟩

theorem RD.clipperTakeOwe0MulSuccess {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {price slice tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 ⟨8686⟩
      (price :: slice :: ⟨4057⟩ :: slice :: ⟨0⟩ :: tab :: lot ::
        price :: tic :: packed :: stopped :: dataLen :: dataStart :: who ::
        max :: amt :: id :: R)
      mem aw rdata acc k C)
    (hmul : price.toNat * slice.toNat < UInt256.size)
    (hov : R.length + 24 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨4057⟩
      (UInt256.mul price slice :: slice :: ⟨0⟩ :: tab :: lot ::
        price :: tic :: packed :: stopped :: dataLen :: dataStart :: who ::
        max :: amt :: id :: R)
      mem aw rdata acc k' C' := by
  exact Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperCheckedMul v hpatch h hmul
    (clipperTakeJumpDest4057 v hpatch) (by simp only [List.length_cons]; omega)

theorem RD.clipperTakeOweGtTabToJoin {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {price slice tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 ⟨4057⟩
      (UInt256.mul price slice :: slice :: ⟨0⟩ :: tab :: lot ::
        price :: tic :: packed :: stopped :: dataLen :: dataStart :: who ::
        max :: amt :: id :: R)
      mem aw rdata acc k C)
    (hgt : tab.toNat < (UInt256.mul price slice).toNat)
    (hov : R.length + 30 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨4223⟩
      (UInt256.div tab price :: tab :: tab :: lot ::
        price :: tic :: packed :: stopped :: dataLen :: dataStart :: who ::
        max :: amt :: id :: R)
      mem aw rdata acc k' C' := by
  have hgtWord : UInt256.gt (UInt256.mul price slice) tab = ⟨1⟩ := by
    exact ugt_one hgt
  have hcond : UInt256.isZero (UInt256.gt (UInt256.mul price slice) tab) = ⟨0⟩ := by
    rw [hgtWord]
    native_decide
  have hpriceNe : price ≠ ⟨0⟩ := by
    intro hprice
    subst price
    have hzero : UInt256.mul ⟨0⟩ slice = ⟨0⟩ :=
      Reasoning.Theory.clipperMul_zero_left slice
    simp [hzero] at hgt
  have rd4067pre := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw gt (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4087⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd4068 := rd4067pre.jumpiNT (by clipper_runtime_decode) hcond (by evm_ov)
  have rd4077pre := evm_run rd4068 with [
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4079⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd4079 := rd4077pre.jumpiT (by clipper_runtime_decode) hpriceNe
    (clipperTakeJumpDest4079 v hpatch) (by evm_ov)
  have rd4083 := evm_run rd4079 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw div (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4223⟩ (by clipper_runtime_decode) (by evm_ov)]
  exact ⟨_, _, rd4083.jump (by clipper_runtime_decode)
    (clipperTakeJumpDest4223 v hpatch) (by evm_ov)⟩

theorem RD.clipperTakeOweEqTabToJoin {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {price slice tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 ⟨4057⟩
      (UInt256.mul price slice :: slice :: ⟨0⟩ :: tab :: lot ::
        price :: tic :: packed :: stopped :: dataLen :: dataStart :: who ::
        max :: amt :: id :: R)
      mem aw rdata acc k C)
    (hle : (UInt256.mul price slice).toNat ≤ tab.toNat)
    (hge : tab.toNat ≤ (UInt256.mul price slice).toNat)
    (hov : R.length + 30 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨4223⟩
      (slice :: UInt256.mul price slice :: tab :: lot ::
        price :: tic :: packed :: stopped :: dataLen :: dataStart :: who ::
        max :: amt :: id :: R)
      mem aw rdata acc k' C' := by
  have hgtWord : UInt256.gt (UInt256.mul price slice) tab = ⟨0⟩ :=
    ugt_zero hle
  have hltWord : UInt256.lt (UInt256.mul price slice) tab = ⟨0⟩ :=
    ult_zero hge
  have hcond4067 :
      UInt256.isZero (UInt256.gt (UInt256.mul price slice) tab) ≠ ⟨0⟩ := by
    rw [hgtWord]
    native_decide
  have hcondLt :
      UInt256.isZero (UInt256.lt (UInt256.mul price slice) tab) ≠ ⟨0⟩ := by
    rw [hltWord]
    native_decide
  have rd4067pre := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw gt (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4087⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd4087 := rd4067pre.jumpiT (by clipper_runtime_decode) hcond4067
    (clipperTakeJumpDest4087 v hpatch) (by evm_ov)
  have rd4096pre := evm_run rd4087 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw lt (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4101⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd4101 := rd4096pre.jumpiT (by clipper_runtime_decode) hcondLt
    (clipperTakeJumpDest4101 v hpatch) (by evm_ov)
  have rd4106pre := evm_run rd4101 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4223⟩ (by clipper_runtime_decode) (by evm_ov)]
  exact ⟨_, _, rd4106pre.jumpiT (by clipper_runtime_decode) hcondLt
    (clipperTakeJumpDest4223 v hpatch) (by evm_ov)⟩

theorem RD.clipperTakeOweLtTabSliceGeLotToJoin {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {price slice tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 ⟨4057⟩
      (UInt256.mul price slice :: slice :: ⟨0⟩ :: tab :: lot ::
        price :: tic :: packed :: stopped :: dataLen :: dataStart :: who ::
        max :: amt :: id :: R)
      mem aw rdata acc k C)
    (hle : (UInt256.mul price slice).toNat ≤ tab.toNat)
    (hlt : (UInt256.mul price slice).toNat < tab.toNat)
    (hsliceGe : lot.toNat ≤ slice.toNat)
    (hov : R.length + 30 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨4223⟩
      (slice :: UInt256.mul price slice :: tab :: lot ::
        price :: tic :: packed :: stopped :: dataLen :: dataStart :: who ::
        max :: amt :: id :: R)
      mem aw rdata acc k' C' := by
  have hgtWord : UInt256.gt (UInt256.mul price slice) tab = ⟨0⟩ :=
    ugt_zero hle
  have hltWord : UInt256.lt (UInt256.mul price slice) tab = ⟨1⟩ :=
    ult_one hlt
  have hsliceLtWord : UInt256.lt slice lot = ⟨0⟩ :=
    ult_zero hsliceGe
  have hcond4067 :
      UInt256.isZero (UInt256.gt (UInt256.mul price slice) tab) ≠ ⟨0⟩ := by
    rw [hgtWord]
    native_decide
  have hcond4096 :
      UInt256.isZero (UInt256.lt (UInt256.mul price slice) tab) = ⟨0⟩ := by
    rw [hltWord]
    native_decide
  have hcondSlice :
      UInt256.isZero (UInt256.lt slice lot) ≠ ⟨0⟩ := by
    rw [hsliceLtWord]
    native_decide
  have rd4067pre := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw gt (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4087⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd4087 := rd4067pre.jumpiT (by clipper_runtime_decode) hcond4067
    (clipperTakeJumpDest4087 v hpatch) (by evm_ov)
  have rd4096pre := evm_run rd4087 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw lt (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4101⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd4097 := rd4096pre.jumpiNT (by clipper_runtime_decode) hcond4096 (by evm_ov)
  have rd4101 := evm_run rd4097 with [
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw lt (by clipper_runtime_decode) (by evm_ov)]
  have rd4106pre := evm_run rd4101 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4223⟩ (by clipper_runtime_decode) (by evm_ov)]
  exact ⟨_, _, rd4106pre.jumpiT (by clipper_runtime_decode) hcondSlice
    (clipperTakeJumpDest4223 v hpatch) (by evm_ov)⟩

set_option maxHeartbeats 2000000 in
theorem RD.clipperTakeVatFluxExtcodesizeGuard {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {price slice owe tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD code ee g s0 ⟨4223⟩
      (slice :: owe :: tab :: lot :: price :: tic :: packed :: stopped ::
        dataLen :: dataStart :: who :: max :: amt :: id :: R)
      mem (UInt256.ofNat 7) rdata (cA, σ) k C)
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨4380⟩
      (clipperTakeVatTarget v :: clipperTakeVatTarget v :: ⟨0⟩ :: ⟨128⟩ ::
        ⟨132⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨260⟩ :: clipperTakeVatFluxSelectorWord ::
        clipperTakeVatTarget v :: slice :: owe :: UInt256.sub tab owe ::
        UInt256.sub lot slice :: price :: tic :: packed :: stopped :: dataLen ::
        dataStart :: who :: max :: amt :: id :: R)
      (clipperTakeVatFluxCalldataMem v ee who slice mem)
      (UInt256.ofNat 9) rdata (cA, σ) k' C' := by
  rcases v.ilk_wf with ⟨ilkBs, hilk, hlen⟩
  let ilkWord : UInt256 := EVM.Word.ofNat (fromBytesBigEndian ilkBs)
  let vatWord : UInt256 := EVM.Word.ofNat (↑v.vat : Nat)
  have hbaseMload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (mem := mem) (aw := UInt256.ofNat 7)
      (by rw [hmem]; decide) (by decide) hread64
  have hcallMload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (clipperTakeVatFluxCalldataMem v ee who slice mem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((clipperTakeVatFluxCalldataMem v ee who slice mem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    clipperTakeVatFluxCalldataMem_mload64 v ee who slice hmem hread64
  have rd4237pre := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov)]
  have rd4228 := rd4237pre.mload 0 ⟨128⟩ (UInt256.ofNat 7)
    (by clipper_runtime_decode) mem_cost hbaseMload64 (by native_decide) (by evm_ov)
  have rd4237pre := evm_run rd4228 with [
    raw push4 clipperTakeVatFluxSelectorSeed (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨225⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  rw [show UInt256.shiftLeft clipperTakeVatFluxSelectorSeed ⟨225⟩ =
    clipperTakeVatFluxSelectorShifted from by native_decide] at rd4237pre
  have rd4238 := rd4237pre.mstore 0
    (clipperTakeVatFluxSelectorMem mem)
    (UInt256.ofNat 7) (by clipper_runtime_decode) mem_cost (by rfl)
    (by native_decide) (by evm_ov)
  have rd4271 := rd4238.pushConst ilkWord (width := 32) (op := .PUSH32)
    (by decide)
    (by simpa [ilkWord] using clipperTakeIlkPush32Decode4238 v hpatch hilk hlen)
    (by evm_ov)
  have rd4275pre := evm_run rd4271 with [
    raw push1 ⟨4⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨128⟩ : UInt256) + ⟨4⟩ = ⟨132⟩ from by native_decide] at rd4275pre
  have rd4276 := rd4275pre.mstore 0
    (clipperTakeVatFluxIlkMem v mem)
    (UInt256.ofNat 7) (by clipper_runtime_decode) mem_cost
    (by
      rw [show (⟨132⟩ : UInt256).toNat = 132 from by decide]
      simp [clipperTakeVatFluxIlkMem, clipperTakeIlkWord, hilk, ilkWord])
    (by native_decide) (by evm_ov)
  have rd4281pre := evm_run rd4276 with [
    raw uniswapAddress (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨36⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨128⟩ : UInt256) + ⟨36⟩ = ⟨164⟩ from by native_decide] at rd4281pre
  have rd4282 := rd4281pre.mstore 0
    (clipperTakeVatFluxThisMem ee (clipperTakeVatFluxIlkMem v mem))
    (UInt256.ofNat 7) (by clipper_runtime_decode) mem_cost (by rfl)
    (by native_decide) (by evm_ov)
  have rd4297pre := evm_run rd4282 with [
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw dup14 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨68⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov)]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
    solcAddrMask from by native_decide] at rd4297pre
  rw [show (⟨128⟩ : UInt256) + ⟨68⟩ = ⟨196⟩ from by native_decide] at rd4297pre
  have rd4298 := rd4297pre.mstore 3
    (clipperTakeVatFluxWhoMem who
      (clipperTakeVatFluxThisMem ee (clipperTakeVatFluxIlkMem v mem)))
    (UInt256.ofNat 8) (by clipper_runtime_decode) mem_cost (by rfl)
    (by native_decide) (by evm_ov)
  have rd4304pre := evm_run rd4298 with [
    raw push1 ⟨100⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨128⟩ : UInt256) + ⟨100⟩ = ⟨228⟩ from by native_decide] at rd4304pre
  have rd4305 := rd4304pre.mstore 3
    (clipperTakeVatFluxCalldataMem v ee who slice mem)
    (UInt256.ofNat 9) (by clipper_runtime_decode) mem_cost (by rfl)
    (by native_decide) (by evm_ov)
  have rd4306pre := evm_run rd4305 with [
    raw swap2 (by clipper_runtime_decode) (by evm_ov)]
  have rd4307 := rd4306pre.mload 0 ⟨128⟩ (UInt256.ofNat 9)
    (by clipper_runtime_decode) mem_cost hcallMload64 (by native_decide) (by evm_ov)
  have rd4317pre := evm_run rd4307 with [
    raw swap6 (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw swap6 (by clipper_runtime_decode) (by evm_ov),
    raw swap5 (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw swap5 (by clipper_runtime_decode) (by evm_ov)]
  have rd4350 := rd4317pre.pushConst vatWord (width := 32) (op := .PUSH32)
    (by decide)
    (by simpa [vatWord] using clipperTakeVatPush32Decode4317 v hpatch)
    (by evm_ov)
  have rd4380 := evm_run rd4350 with [
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw push4 clipperTakeVatFluxSelectorWord (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨132⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw dup8 (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨128⟩ : UInt256) + ⟨132⟩ = ⟨260⟩ from by native_decide] at rd4380
  rw [show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ = ⟨0⟩ from by native_decide]
    at rd4380
  rw [show (⟨0⟩ : UInt256) + ⟨132⟩ = ⟨132⟩ from by native_decide] at rd4380
  exact ⟨_, _, by simpa [clipperTakeVatTarget, vatWord, u256_land_comm] using rd4380⟩

set_option maxHeartbeats 1000000 in
theorem RD.clipperTakeVatFluxPostCall {cA0 cA gh bl σ₀ σStart σ I}
    {g : Sat256} {A : Substate} {k C : ℕ}
    {price slice owe tabNew lotNew tic packed stopped dataLen dataStart who max amt id :
      UInt256}
    {R : List UInt256} {baseMem rdata : ByteArray} (v : ClipperImmutables)
    {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (rd4380 : RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨4380⟩
      (clipperTakeVatTarget v :: clipperTakeVatTarget v :: ⟨0⟩ :: ⟨128⟩ ::
        ⟨132⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨260⟩ :: clipperTakeVatFluxSelectorWord ::
        clipperTakeVatTarget v :: slice :: owe :: tabNew :: lotNew :: price :: tic ::
        packed :: stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: R)
      (clipperTakeVatFluxCalldataMem v I who slice baseMem)
      (UInt256.ofNat 9) rdata (cA, σ) k C)
    (hbaseMem : baseMem.size = 196)
    (hcodeSizeVat :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (clipperTakeVatTarget v) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true)
    (hov : R.length + 32 ≤ 1024) :
    ∃ (cA_vat : Batteries.RBSet AccountAddress compare) (σ_vat : AccountMap)
      (zVat : Bool) (outVat : ByteArray) (A_vat : Substate) (k' C' : ℕ),
      RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨4396⟩
        ((if zVat then ⟨1⟩ else ⟨0⟩) :: ⟨260⟩ :: clipperTakeVatFluxSelectorWord ::
          clipperTakeVatTarget v :: slice :: owe :: tabNew :: lotNew :: price :: tic ::
          packed :: stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: R)
        (outVat.write 0 (clipperTakeVatFluxCalldataMem v I who slice baseMem)
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
        [v.ilk, .address I.codeOwner, .address (AccountAddress.ofNat who.toNat),
          .int (Int.ofNat slice.toNat)]
        (zVat,
          { initState cA0 gh bl σStart σ₀ g A I with
            accountMap := σ_vat
            substate := A_vat
            createdAccounts := cA_vat },
          outVat) true ∧
      outVat.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd4395⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨4380⟩) (okPc := ⟨4392⟩)
      rd4380 hcodeSizeVat
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (clipperTakeJumpDest4392 v hpatch)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode)
      (by simp only [List.length_cons]; omega)
  obtain ⟨cA_vat, σ_vat, zVat, outVat, A_in, callGas, k4396, C4396, hΘpack,
      rd4396raw, houtVatSize⟩ :=
    RD.call rd4395 (by clipper_runtime_decode) hdepth (by evm_ov)
  obtain ⟨g'', A_vat, hΘ⟩ := hΘpack
  refine ⟨cA_vat, σ_vat, zVat, outVat, A_vat, k4396, C4396, ?_, ?_,
    houtVatSize⟩
  · exact rd4396raw
  · let evmVat : EVM.State :=
      { initState cA0 gh bl σStart σ₀ g A I with
        accountMap := σ, createdAccounts := cA }
    refine callCoincides (cfg := config v)
      (evm := evmVat)
      (name := "flux")
      (args := [v.ilk, .address I.codeOwner, .address (AccountAddress.ofNat who.toNat),
        .int (Int.ofNat slice.toNat)])
      (tgt := EVM.address v.vat) (targetWord := clipperTakeVatTarget v)
      (cA' := cA_vat) (σ' := σ_vat) (A' := A_vat) (A_in := A_in)
      (z := zVat) (o := outVat) (g'' := g'') (callGas := callGas)
      (mem := clipperTakeVatFluxCalldataMem v I who slice baseMem)
      (inOff := ⟨128⟩) (inSize := ⟨132⟩) (callPerm := true)
      (fun h => absurd hdepth (by
        have hI : I.depth = (1024 : Fin 1025) := by
          simpa [evmVat, initState] using h
        rw [hI]
        decide))
      ?_ ?_ ?_
    · rw [clipperTakeVatTargetAddress v]
      exact clipperTakeEVMAddressAccountAddress v.vat
    · simpa [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
        show (⟨132⟩ : UInt256).toNat = 132 from by decide] using
        clipperTakeVatFluxEncode_eq v I who slice hbaseMem
    · simpa [evmVat, initState, hperm] using hΘ

theorem RD.clipperTakeVatFluxNoCode {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {price slice owe tabNew lotNew tic packed stopped dataLen dataStart who max amt id :
      UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (rd4380 : RD code ee g s0 ⟨4380⟩
      (clipperTakeVatTarget v :: clipperTakeVatTarget v :: ⟨0⟩ :: ⟨128⟩ ::
        ⟨132⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨260⟩ :: clipperTakeVatFluxSelectorWord ::
        clipperTakeVatTarget v :: slice :: owe :: tabNew :: lotNew :: price :: tic ::
        packed :: stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: R)
      mem (UInt256.ofNat 9) rdata (cA, σ) k C)
    (hcodeSizeVat :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (clipperTakeVatTarget v) = ⟨0⟩)
    (hov : R.length + 32 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.uniswapExtcodesizeGuardMissing (pc := ⟨4380⟩) (okPc := ⟨4392⟩)
    rd4380 hcodeSizeVat
    (by clipper_runtime_decode) (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by simp only [List.length_cons]; omega)

theorem RD.clipperTakeVatFluxCallFailure {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    (rd : RD code ee g s0 ⟨4396⟩ (⟨0⟩ :: R) mem aw o acc k C)
    (hosz : o.size < UInt256.size)
    (hov : R.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.uniswapCallSuccessGuardMissing (pc := ⟨4396⟩) (okPc := ⟨4412⟩)
    rd (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    hosz hov

theorem RD.clipperTakeVatFluxCallSuccessToPostGuard {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {price slice owe tabNew lotNew tic packed stopped dataLen dataStart who max amt id :
      UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨4396⟩
      (⟨1⟩ :: ⟨260⟩ :: clipperTakeVatFluxSelectorWord :: clipperTakeVatTarget v ::
        slice :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen ::
        dataStart :: who :: max :: amt :: id :: R)
      mem aw o acc k C)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨4414⟩
      (⟨260⟩ :: clipperTakeVatFluxSelectorWord :: clipperTakeVatTarget v ::
        slice :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen ::
        dataStart :: who :: max :: amt :: id :: R)
      mem aw o acc k' C' := by
  obtain ⟨_, _, rd4414⟩ :=
    RD.uniswapCallSuccessGuardOk (pc := ⟨4396⟩) (okPc := ⟨4412⟩) rd
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (clipperTakeJumpDest4412 v hpatch)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by simp only [List.length_cons]; omega)
  exact ⟨_, _, rd4414⟩

theorem RD.clipperTakeSkipClipperCallDataEmpty {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {price slice owe tabNew lotNew tic packed stopped dataLen dataStart who max amt id :
      UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨4414⟩
      (⟨260⟩ :: clipperTakeVatFluxSelectorWord :: clipperTakeVatTarget v ::
        slice :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped ::
        dataLen :: dataStart :: who :: max :: amt :: id :: R)
      mem aw o (cA, σ) k C)
    (hdataLen : dataLen = ⟨0⟩)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨4701⟩
      (UInt256.land (solcSlotWord σ ee ⟨1⟩) solcAddrMask ::
        slice :: owe :: tabNew :: lotNew :: price :: tic ::
        packed :: stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: R)
      mem aw o (cA, σ) k' C' := by
  have rd4417pre := evm_run rd with [
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rd4418raw⟩ := rd4417pre.sload
    (by clipper_runtime_decode) (by evm_ov)
  have rd4438pre := evm_run rd4418raw with [
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw dup10 (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4494⟩ (by clipper_runtime_decode) (by evm_ov)]
  have hcond4438 : UInt256.isZero dataLen ≠ ⟨0⟩ := by
    rw [hdataLen]
    native_decide
  have rd4494 := rd4438pre.jumpiT (by clipper_runtime_decode) hcond4438
    (clipperTakeJumpDest4494 v hpatch) (by evm_ov)
  have rd4500pre := evm_run rd4494 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4524⟩ (by clipper_runtime_decode) (by evm_ov)]
  have hcond4500 :
      UInt256.isZero (UInt256.isZero (UInt256.isZero dataLen)) ≠ ⟨0⟩ := by
    rw [hdataLen]
    native_decide
  have rd4524 := rd4500pre.jumpiT (by clipper_runtime_decode) hcond4500
    (clipperTakeJumpDest4524 v hpatch) (by evm_ov)
  have rd4529pre := evm_run rd4524 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4701⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd4701 := rd4529pre.jumpiT (by clipper_runtime_decode) hcond4500
    (clipperTakeJumpDest4701 v hpatch) (by evm_ov)
  exact ⟨_, _, by
    simpa [solcSlotWord, u256_land_comm] using rd4701⟩

end Benchmarks.Dss.Clipper
