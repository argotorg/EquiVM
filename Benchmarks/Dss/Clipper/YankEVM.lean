import Benchmarks.Dss.Clipper.YankSource
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

theorem clipperYankPatchesWindowDisjoint32 (v : ClipperImmutables) (lo hi : Nat)
    (hlo : 1912 ≤ lo) (hhi : hi ≤ 2221) :
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

theorem clipperYankDecodeMid (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {pc : UInt256} {res : Operation × Option (UInt256 × Nat)}
    (hlo : 1912 ≤ pc.toNat)
    (hhi : pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2) ≤ 2221)
    (hdec : decode clipperBytecode pc = some res) :
    decode code pc = some res :=
  patchRuntime_decode_disjoint_of_decode_res hpatch
    (clipperYankPatchesWindowDisjoint32 v pc.toNat (pc.toNat + 1) hlo (by omega))
    (clipperYankPatchesWindowDisjoint32 v (pc.toNat + 1)
      (pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2)) (by omega) hhi)
    hdec
    (by
      have hle :
          pc.toNat + 1 ≤
            pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2) := by
        omega
      exact Nat.lt_of_le_of_lt (Nat.le_trans hle hhi) (by norm_num))
    (by exact Nat.lt_of_le_of_lt hhi (by norm_num))

theorem clipperYankPatchesWindowDisjoint32AfterIlk (v : ClipperImmutables)
    (lo hi : Nat) (hlo : 2253 ≤ lo) (hhi : hi ≤ 2369) :
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

theorem clipperYankDecodeAfterIlk (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {pc : UInt256} {res : Operation × Option (UInt256 × Nat)}
    (hlo : 2253 ≤ pc.toNat)
    (hhi : pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2) ≤ 2369)
    (hdec : decode clipperBytecode pc = some res) :
    decode code pc = some res :=
  patchRuntime_decode_disjoint_of_decode_res hpatch
    (clipperYankPatchesWindowDisjoint32AfterIlk v pc.toNat (pc.toNat + 1) hlo
      (by omega))
    (clipperYankPatchesWindowDisjoint32AfterIlk v (pc.toNat + 1)
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

theorem clipperYankPatchesWindowDisjoint32FluxBeforeVat (v : ClipperImmutables)
    (lo hi : Nat) (hlo : 2401 ≤ lo) (hhi : hi ≤ 2437) :
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

theorem clipperYankDecodeFluxBeforeVat (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {pc : UInt256} {res : Operation × Option (UInt256 × Nat)}
    (hlo : 2401 ≤ pc.toNat)
    (hhi : pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2) ≤ 2437)
    (hdec : decode clipperBytecode pc = some res) :
    decode code pc = some res :=
  patchRuntime_decode_disjoint_of_decode_res hpatch
    (clipperYankPatchesWindowDisjoint32FluxBeforeVat v pc.toNat (pc.toNat + 1) hlo
      (by omega))
    (clipperYankPatchesWindowDisjoint32FluxBeforeVat v (pc.toNat + 1)
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

theorem clipperYankPatchesWindowDisjoint32AfterVat (v : ClipperImmutables)
    (lo hi : Nat) (hlo : 2469 ≤ lo) (hhi : hi ≤ 2527) :
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

theorem clipperYankDecodeAfterVat (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {pc : UInt256} {res : Operation × Option (UInt256 × Nat)}
    (hlo : 2469 ≤ pc.toNat)
    (hhi : pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2) ≤ 2527)
    (hdec : decode clipperBytecode pc = some res) :
    decode code pc = some res :=
  patchRuntime_decode_disjoint_of_decode_res hpatch
    (clipperYankPatchesWindowDisjoint32AfterVat v pc.toNat (pc.toNat + 1) hlo
      (by omega))
    (clipperYankPatchesWindowDisjoint32AfterVat v (pc.toNat + 1)
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

macro "clipper_yank_decode" : tactic =>
  `(tactic| first
    | clipper_decode
    | exact clipperYankDecodeMid _ (by assumption)
        (by native_decide) (by native_decide) (by native_decide)
    | exact clipperYankDecodeAfterIlk _ (by assumption)
        (by native_decide) (by native_decide) (by native_decide)
    | exact clipperYankDecodeFluxBeforeVat _ (by assumption)
        (by native_decide) (by native_decide) (by native_decide)
    | exact clipperYankDecodeAfterVat _ (by assumption)
        (by native_decide) (by native_decide) (by native_decide))

noncomputable abbrev clipperYankSalesHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (clipperYankArgWord I) ⟨12⟩ (clipperRelyAuthHashMem I)

theorem clipperYankSalesHashMem_size (I : ExecutionEnv) :
    (clipperYankSalesHashMem I).size = 96 := by
  simpa [clipperYankSalesHashMem] using
    twoWordHashMem_size_96 (clipperYankArgWord I) (⟨12⟩ : UInt256)
      (clipperRelyAuthHashMem_size I)

theorem clipperYankSalesHashMem_read64 (I : ExecutionEnv) :
    (clipperYankSalesHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [clipperYankSalesHashMem, twoWordHashMem_read64 _ _ (clipperRelyAuthHashMem_size I)]
  exact clipperRelyAuthHashMem_read64 I

noncomputable abbrev clipperYankSalesHashMemRefresh (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (clipperYankArgWord I) ⟨12⟩ (clipperYankSalesHashMem I)

theorem clipperYankSalesHashMemRefresh_size (I : ExecutionEnv) :
    (clipperYankSalesHashMemRefresh I).size = 96 := by
  simpa [clipperYankSalesHashMemRefresh] using
    twoWordHashMem_size_96 (clipperYankArgWord I) (⟨12⟩ : UInt256)
      (clipperYankSalesHashMem_size I)

theorem clipperYankSalesHashMemRefresh_read64 (I : ExecutionEnv) :
    (clipperYankSalesHashMemRefresh I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [clipperYankSalesHashMemRefresh,
    twoWordHashMem_read64 _ _ (clipperYankSalesHashMem_size I)]
  exact clipperYankSalesHashMem_read64 I

abbrev clipperYankIlkWord (v : ClipperImmutables) : UInt256 :=
  EVM.Word.ofNat (fromBytesBigEndian (match v.ilk with
    | .fixedBytes _ bs => bs
    | _ => []))

abbrev clipperDogDigsSelectorSeed : UInt256 :=
  ⟨840721661⟩

abbrev clipperDogDigsSelectorShifted : UInt256 :=
  UInt256.shiftLeft clipperDogDigsSelectorSeed ⟨226⟩

abbrev clipperDogDigsSelectorWord : UInt256 :=
  ⟨3362886644⟩

noncomputable def clipperDogDigsSelectorMem (mem : ByteArray) : ByteArray :=
  clipperDogDigsSelectorShifted.toByteArray.write 0 mem 128 32

noncomputable def clipperDogDigsIlkMem (v : ClipperImmutables) (mem : ByteArray) :
    ByteArray :=
  (clipperYankIlkWord v).toByteArray.write 0 (clipperDogDigsSelectorMem mem) 132 32

noncomputable def clipperDogDigsCalldataMem (v : ClipperImmutables) (tab : UInt256)
    (mem : ByteArray) : ByteArray :=
  tab.toByteArray.write 0 (clipperDogDigsIlkMem v mem) 164 32

theorem clipperDogDigsSelectorMem_size {mem : ByteArray} (hmem : mem.size = 96) :
    (clipperDogDigsSelectorMem mem).size = 160 := by
  unfold clipperDogDigsSelectorMem
  exact toByteArray_write32_size_of_ge mem clipperDogDigsSelectorShifted 128 96 160 hmem
    (by omega) (by native_decide) (by omega)

theorem clipperDogDigsSelectorMem_read64 {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperDogDigsSelectorMem mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperDogDigsSelectorMem
  have hpreserve :
      ByteArray.readWithPadding
          ((UInt256.toByteArray clipperDogDigsSelectorShifted).write 0 mem 128 32)
          64 32 =
        mem.readWithPadding 64 32 :=
    toByteArray_write_read_below_of_gap (b := clipperDogDigsSelectorShifted) (mem := mem)
      (off := 128) (read := 64) (hread := by simp [hmem])
      (hbelow := by native_decide) (hgap := by rw [hmem]; native_decide)
  rw [hpreserve, hread64]

theorem clipperDogDigsIlkMem_size (v : ClipperImmutables) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (clipperDogDigsIlkMem v mem).size = 164 := by
  unfold clipperDogDigsIlkMem
  exact toByteArray_write32_size_of_le (clipperDogDigsSelectorMem mem)
    (clipperYankIlkWord v) 132 160 164
    (clipperDogDigsSelectorMem_size hmem)
    (by rw [clipperDogDigsSelectorMem_size hmem]; omega) (by omega)

theorem clipperDogDigsIlkMem_read64 (v : ClipperImmutables) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperDogDigsIlkMem v mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperDogDigsIlkMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [clipperDogDigsSelectorMem_size hmem]; omega) (by omega),
    clipperDogDigsSelectorMem_read64 hmem hread64]

theorem clipperDogDigsCalldataMem_size (v : ClipperImmutables) (tab : UInt256)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (clipperDogDigsCalldataMem v tab mem).size = 196 := by
  unfold clipperDogDigsCalldataMem
  exact toByteArray_write32_size_of_le (clipperDogDigsIlkMem v mem) tab 164 164 196
    (clipperDogDigsIlkMem_size v hmem)
    (by rw [clipperDogDigsIlkMem_size v hmem])
    (by native_decide)

theorem clipperDogDigsCalldataMem_read64 (v : ClipperImmutables) (tab : UInt256)
    {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperDogDigsCalldataMem v tab mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperDogDigsCalldataMem
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
    (by rw [clipperDogDigsIlkMem_size v hmem]) (by native_decide),
    clipperDogDigsIlkMem_read64 v hmem hread64]

theorem clipperDogDigsCalldataMem_mload64 (v : ClipperImmutables) (tab : UInt256)
    {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (clipperDogDigsCalldataMem v tab mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((clipperDogDigsCalldataMem v tab mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ := by
  exact mloadFreePtrValue
    (mem := clipperDogDigsCalldataMem v tab mem) (aw := UInt256.ofNat 7)
    (by rw [clipperDogDigsCalldataMem_size v tab hmem]; norm_num)
    (by decide)
    (clipperDogDigsCalldataMem_read64 v tab hmem hread64)

theorem clipperDogDigsSelectorMem_read128_4 {mem : ByteArray}
    (hmem : mem.size = 96) :
    (clipperDogDigsSelectorMem mem).readWithPadding 128 4 = dogDigsSelector := by
  unfold clipperDogDigsSelectorMem
  rw [toByteArray_write_read_window_of_gap clipperDogDigsSelectorShifted mem 128 0 4
    (by norm_num) (by norm_num) (by norm_num) (by rw [hmem]; native_decide)]
  rw [toByteArray_eq_toBytesBE]
  native_decide

theorem clipperDogDigsCalldataMem_read128_4 (v : ClipperImmutables) (tab : UInt256)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (clipperDogDigsCalldataMem v tab mem).readWithPadding 128 4 = dogDigsSelector := by
  unfold clipperDogDigsCalldataMem
  rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
    (by rw [clipperDogDigsIlkMem_size v hmem])
    (by omega) (by rw [clipperDogDigsIlkMem_size v hmem]; omega)
    (by norm_num) (by norm_num)]
  unfold clipperDogDigsIlkMem
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by rw [clipperDogDigsSelectorMem_size hmem]; omega)
    (by omega) (by rw [clipperDogDigsSelectorMem_size hmem]; omega)
    (by norm_num) (by norm_num)]
  exact clipperDogDigsSelectorMem_read128_4 hmem

theorem clipperDogDigsCalldataMem_read132_32 (v : ClipperImmutables) (tab : UInt256)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (clipperDogDigsCalldataMem v tab mem).readWithPadding 132 32 =
      UInt256.toByteArray (clipperYankIlkWord v) := by
  unfold clipperDogDigsCalldataMem
  rw [write32_read_below _ _ 164 132 (by rw [toByteArray_size])
    (by rw [clipperDogDigsIlkMem_size v hmem]) (by omega)]
  unfold clipperDogDigsIlkMem
  rw [write32_read_back _ _ 132 (by rw [toByteArray_size])
    (by rw [clipperDogDigsSelectorMem_size hmem]; omega)]
  rw [show (UInt256.toByteArray (clipperYankIlkWord v)).extract 0 32 =
      UInt256.toByteArray (clipperYankIlkWord v) by
    rw [show 32 = (UInt256.toByteArray (clipperYankIlkWord v)).size by
      rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem clipperDogDigsCalldataMem_read164_32 (v : ClipperImmutables) (tab : UInt256)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (clipperDogDigsCalldataMem v tab mem).readWithPadding 164 32 =
      UInt256.toByteArray tab := by
  unfold clipperDogDigsCalldataMem
  rw [write32_read_back _ _ 164 (by rw [toByteArray_size])
    (by rw [clipperDogDigsIlkMem_size v hmem])]
  rw [show (UInt256.toByteArray tab).extract 0 32 = UInt256.toByteArray tab by
    rw [show 32 = (UInt256.toByteArray tab).size by rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem clipperDogDigsCalldataMem_read128_68 (v : ClipperImmutables) (tab : UInt256)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (clipperDogDigsCalldataMem v tab mem).readWithPadding 128 68 =
      dogDigsSelector ++ UInt256.toByteArray (clipperYankIlkWord v) ++
        UInt256.toByteArray tab := by
  rw [byteArray_readWithPadding_split _ 128 4 64 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [clipperDogDigsCalldataMem_size v tab hmem])]
  rw [byteArray_readWithPadding_split _ 132 32 32 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [clipperDogDigsCalldataMem_size v tab hmem])]
  rw [clipperDogDigsCalldataMem_read128_4 v tab hmem,
    clipperDogDigsCalldataMem_read132_32 v tab hmem,
    clipperDogDigsCalldataMem_read164_32 v tab hmem, ByteArray.append_assoc]

theorem clipperDogDigsEncode_eq (v : ClipperImmutables) (tab : UInt256)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (config v).externalABI.encode? "digs" [v.ilk, .int (Int.ofNat tab.toNat)] =
      some ((clipperDogDigsCalldataMem v tab mem).readWithPadding 128 68) := by
  rcases v.ilk_wf with ⟨bs, hilk, hlen⟩
  rw [hilk]
  have hilkWord :
      clipperYankIlkWord v = EVM.Word.ofNat (fromBytesBigEndian bs) := by
    simp [clipperYankIlkWord, hilk]
  rw [clipperDogDigsCalldataMem_read128_68 v tab hmem, hilkWord]
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
  have htabWord : EVM.word tab.toNat = tab := u256_ofNat_toNat tab
  have htabLt : tab.toNat < EVM.twoPow 256 := by
    change tab.val.val < UInt256.size
    exact tab.val.isLt
  change externalABI.encode? "digs"
      [.fixedBytes ⟨31, by decide⟩ bs, .int (Int.ofNat tab.toNat)] =
    some (dogDigsSelector ++ UInt256.toByteArray (EVM.Word.ofNat (fromBytesBigEndian bs)) ++
      UInt256.toByteArray tab)
  unfold externalABI ABI.encodeCallWithSelector? ABI.encodeABIValues?
  simp [ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, bytes32, bytes32Width, uint256,
    uint256Int, selectorBytes, dogDigsSelector, hlen, ABI.zeroBytes, hwordBytes,
    hbsByteArray, htabLt, htabWord, word_toBytesBE_toByteArray_eq_toByteArray]
  rw [ByteArray.append_assoc]

abbrev clipperVatFluxSelectorSeed : UInt256 :=
  ⟨814276375⟩

abbrev clipperVatFluxSelectorShifted : UInt256 :=
  UInt256.shiftLeft clipperVatFluxSelectorSeed ⟨225⟩

abbrev clipperVatFluxSelectorWord : UInt256 :=
  ⟨1628552750⟩

abbrev clipperYankThisWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.codeOwner.val

noncomputable def clipperVatFluxSelectorMem (mem : ByteArray) : ByteArray :=
  clipperVatFluxSelectorShifted.toByteArray.write 0 mem 128 32

noncomputable def clipperVatFluxIlkMem (v : ClipperImmutables) (mem : ByteArray) :
    ByteArray :=
  (clipperYankIlkWord v).toByteArray.write 0 (clipperVatFluxSelectorMem mem) 132 32

noncomputable def clipperVatFluxThisMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (clipperYankThisWord I).toByteArray.write 0 mem 164 32

noncomputable def clipperVatFluxCallerMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (solcSourceWord I).toByteArray.write 0 mem 196 32

noncomputable def clipperVatFluxCalldataMem (v : ClipperImmutables) (I : ExecutionEnv)
    (lot : UInt256) (mem : ByteArray) : ByteArray :=
  lot.toByteArray.write 0
    (clipperVatFluxCallerMem I
      (clipperVatFluxThisMem I (clipperVatFluxIlkMem v mem)))
    228 32

theorem clipperVatFluxSelectorMem_size {mem : ByteArray} (hmem : mem.size = 196) :
    (clipperVatFluxSelectorMem mem).size = 196 := by
  unfold clipperVatFluxSelectorMem
  exact toByteArray_write32_size_of_le mem clipperVatFluxSelectorShifted 128 196 196 hmem
    (by rw [hmem]; omega) (by omega)

theorem clipperVatFluxIlkMem_size (v : ClipperImmutables) {mem : ByteArray}
    (hmem : mem.size = 196) :
    (clipperVatFluxIlkMem v mem).size = 196 := by
  unfold clipperVatFluxIlkMem
  exact toByteArray_write32_size_of_le (clipperVatFluxSelectorMem mem)
    (clipperYankIlkWord v) 132 196 196 (clipperVatFluxSelectorMem_size hmem)
    (by rw [clipperVatFluxSelectorMem_size hmem]; omega) (by omega)

theorem clipperVatFluxThisMem_size (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 196) :
    (clipperVatFluxThisMem I mem).size = 196 := by
  unfold clipperVatFluxThisMem
  exact toByteArray_write32_size_of_le mem (clipperYankThisWord I) 164 196 196 hmem
    (by rw [hmem]; omega) (by omega)

theorem clipperVatFluxCallerMem_size (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 196) :
    (clipperVatFluxCallerMem I mem).size = 228 := by
  unfold clipperVatFluxCallerMem
  exact toByteArray_write32_size_of_le mem (solcSourceWord I) 196 196 228 hmem
    (by rw [hmem]) (by native_decide)

theorem clipperVatFluxCalldataMem_size (v : ClipperImmutables) (I : ExecutionEnv)
    (lot : UInt256) {mem : ByteArray} (hmem : mem.size = 196) :
    (clipperVatFluxCalldataMem v I lot mem).size = 260 := by
  have hIlk : (clipperVatFluxIlkMem v mem).size = 196 :=
    clipperVatFluxIlkMem_size v hmem
  have hThis : (clipperVatFluxThisMem I (clipperVatFluxIlkMem v mem)).size = 196 :=
    clipperVatFluxThisMem_size I hIlk
  have hCaller :
      (clipperVatFluxCallerMem I
        (clipperVatFluxThisMem I (clipperVatFluxIlkMem v mem))).size = 228 :=
    clipperVatFluxCallerMem_size I hThis
  unfold clipperVatFluxCalldataMem
  exact toByteArray_write32_size_of_le
    (clipperVatFluxCallerMem I
      (clipperVatFluxThisMem I (clipperVatFluxIlkMem v mem))) lot 228 228 260 hCaller
    (by rw [hCaller]) (by native_decide)

theorem clipperVatFluxSelectorMem_read64 {mem : ByteArray} (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperVatFluxSelectorMem mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperVatFluxSelectorMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
    (by rw [hmem]; native_decide) (by omega), hread64]

theorem clipperVatFluxIlkMem_read64 (v : ClipperImmutables) {mem : ByteArray}
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperVatFluxIlkMem v mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperVatFluxIlkMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [clipperVatFluxSelectorMem_size hmem]; native_decide) (by omega),
    clipperVatFluxSelectorMem_read64 hmem hread64]

theorem clipperVatFluxThisMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperVatFluxThisMem I mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperVatFluxThisMem
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
    (by rw [hmem]; native_decide) (by omega), hread64]

theorem clipperVatFluxCallerMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperVatFluxCallerMem I mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperVatFluxCallerMem
  rw [write32_read_below _ _ 196 64 (by rw [toByteArray_size])
    (by rw [hmem]) (by omega), hread64]

theorem clipperVatFluxCalldataMem_read64 (v : ClipperImmutables) (I : ExecutionEnv)
    (lot : UInt256) {mem : ByteArray} (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperVatFluxCalldataMem v I lot mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  have hIlk : (clipperVatFluxIlkMem v mem).size = 196 :=
    clipperVatFluxIlkMem_size v hmem
  have hThis : (clipperVatFluxThisMem I (clipperVatFluxIlkMem v mem)).size = 196 :=
    clipperVatFluxThisMem_size I hIlk
  have hCaller :
      (clipperVatFluxCallerMem I
        (clipperVatFluxThisMem I (clipperVatFluxIlkMem v mem))).size = 228 :=
    clipperVatFluxCallerMem_size I hThis
  unfold clipperVatFluxCalldataMem
  rw [write32_read_below _ _ 228 64 (by rw [toByteArray_size])
    (by rw [hCaller]) (by omega)]
  exact clipperVatFluxCallerMem_read64 I hThis
    (clipperVatFluxThisMem_read64 I hIlk
      (clipperVatFluxIlkMem_read64 v hmem hread64))

theorem clipperVatFluxCalldataMem_mload64 (v : ClipperImmutables) (I : ExecutionEnv)
    (lot : UInt256) {mem : ByteArray} (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (clipperVatFluxCalldataMem v I lot mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((clipperVatFluxCalldataMem v I lot mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ := by
  exact mloadFreePtrValue
    (mem := clipperVatFluxCalldataMem v I lot mem) (aw := UInt256.ofNat 9)
    (by rw [clipperVatFluxCalldataMem_size v I lot hmem]; norm_num)
    (by decide)
    (clipperVatFluxCalldataMem_read64 v I lot hmem hread64)

theorem clipperVatFluxSelectorMem_read128_4 {mem : ByteArray}
    (hmem : mem.size = 196) :
    (clipperVatFluxSelectorMem mem).readWithPadding 128 4 = vatFluxSelector := by
  unfold clipperVatFluxSelectorMem
  rw [toByteArray_write_read_window_of_gap clipperVatFluxSelectorShifted mem 128 0 4
    (by norm_num) (by norm_num) (by norm_num) (by rw [hmem]; native_decide)]
  rw [toByteArray_eq_toBytesBE]
  native_decide

theorem clipperVatFluxCalldataMem_read128_4 (v : ClipperImmutables) (I : ExecutionEnv)
    (lot : UInt256) {mem : ByteArray} (hmem : mem.size = 196) :
    (clipperVatFluxCalldataMem v I lot mem).readWithPadding 128 4 = vatFluxSelector := by
  have hIlk : (clipperVatFluxIlkMem v mem).size = 196 :=
    clipperVatFluxIlkMem_size v hmem
  have hThis : (clipperVatFluxThisMem I (clipperVatFluxIlkMem v mem)).size = 196 :=
    clipperVatFluxThisMem_size I hIlk
  have hCaller :
      (clipperVatFluxCallerMem I
        (clipperVatFluxThisMem I (clipperVatFluxIlkMem v mem))).size = 228 :=
    clipperVatFluxCallerMem_size I hThis
  unfold clipperVatFluxCalldataMem
  rw [write32_read_below_len _ _ 228 128 4 (by rw [toByteArray_size])
    (by rw [hCaller])
    (by omega)
    (by rw [hCaller]; omega)
    (by norm_num) (by norm_num)]
  unfold clipperVatFluxCallerMem
  rw [write32_read_below_len _ _ 196 128 4 (by rw [toByteArray_size])
    (by rw [hThis])
    (by omega)
    (by rw [hThis]; omega)
    (by norm_num) (by norm_num)]
  unfold clipperVatFluxThisMem
  rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
    (by rw [hIlk]; omega)
    (by omega) (by rw [hIlk]; omega)
    (by norm_num) (by norm_num)]
  unfold clipperVatFluxIlkMem
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by rw [clipperVatFluxSelectorMem_size hmem]; omega)
    (by omega) (by rw [clipperVatFluxSelectorMem_size hmem]; omega)
    (by norm_num) (by norm_num)]
  exact clipperVatFluxSelectorMem_read128_4 hmem

theorem clipperVatFluxCalldataMem_read132_32 (v : ClipperImmutables) (I : ExecutionEnv)
    (lot : UInt256) {mem : ByteArray} (hmem : mem.size = 196) :
    (clipperVatFluxCalldataMem v I lot mem).readWithPadding 132 32 =
      UInt256.toByteArray (clipperYankIlkWord v) := by
  have hIlk : (clipperVatFluxIlkMem v mem).size = 196 :=
    clipperVatFluxIlkMem_size v hmem
  have hThis : (clipperVatFluxThisMem I (clipperVatFluxIlkMem v mem)).size = 196 :=
    clipperVatFluxThisMem_size I hIlk
  have hCaller :
      (clipperVatFluxCallerMem I
        (clipperVatFluxThisMem I (clipperVatFluxIlkMem v mem))).size = 228 :=
    clipperVatFluxCallerMem_size I hThis
  unfold clipperVatFluxCalldataMem
  rw [write32_read_below _ _ 228 132 (by rw [toByteArray_size])
    (by rw [hCaller])
    (by omega)]
  unfold clipperVatFluxCallerMem
  rw [write32_read_below _ _ 196 132 (by rw [toByteArray_size])
    (by rw [hThis])
    (by omega)]
  unfold clipperVatFluxThisMem
  rw [write32_read_below _ _ 164 132 (by rw [toByteArray_size])
    (by rw [hIlk]; omega)
    (by omega)]
  unfold clipperVatFluxIlkMem
  rw [write32_read_back _ _ 132 (by rw [toByteArray_size])
    (by rw [clipperVatFluxSelectorMem_size hmem]; omega)]
  rw [show (UInt256.toByteArray (clipperYankIlkWord v)).extract 0 32 =
      UInt256.toByteArray (clipperYankIlkWord v) by
    rw [show 32 = (UInt256.toByteArray (clipperYankIlkWord v)).size by
      rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem clipperVatFluxCalldataMem_read164_32 (v : ClipperImmutables) (I : ExecutionEnv)
    (lot : UInt256) {mem : ByteArray} (hmem : mem.size = 196) :
    (clipperVatFluxCalldataMem v I lot mem).readWithPadding 164 32 =
      UInt256.toByteArray (clipperYankThisWord I) := by
  have hIlk : (clipperVatFluxIlkMem v mem).size = 196 :=
    clipperVatFluxIlkMem_size v hmem
  have hThis : (clipperVatFluxThisMem I (clipperVatFluxIlkMem v mem)).size = 196 :=
    clipperVatFluxThisMem_size I hIlk
  have hCaller :
      (clipperVatFluxCallerMem I
        (clipperVatFluxThisMem I (clipperVatFluxIlkMem v mem))).size = 228 :=
    clipperVatFluxCallerMem_size I hThis
  unfold clipperVatFluxCalldataMem
  rw [write32_read_below _ _ 228 164 (by rw [toByteArray_size])
    (by rw [hCaller])
    (by omega)]
  unfold clipperVatFluxCallerMem
  rw [write32_read_below _ _ 196 164 (by rw [toByteArray_size])
    (by rw [hThis])
    (by omega)]
  unfold clipperVatFluxThisMem
  rw [write32_read_back _ _ 164 (by rw [toByteArray_size])
    (by rw [hIlk]; omega)]
  rw [show (UInt256.toByteArray (clipperYankThisWord I)).extract 0 32 =
      UInt256.toByteArray (clipperYankThisWord I) by
    rw [show 32 = (UInt256.toByteArray (clipperYankThisWord I)).size by
      rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem clipperVatFluxCalldataMem_read196_32 (v : ClipperImmutables) (I : ExecutionEnv)
    (lot : UInt256) {mem : ByteArray} (hmem : mem.size = 196) :
    (clipperVatFluxCalldataMem v I lot mem).readWithPadding 196 32 =
      UInt256.toByteArray (solcSourceWord I) := by
  have hIlk : (clipperVatFluxIlkMem v mem).size = 196 :=
    clipperVatFluxIlkMem_size v hmem
  have hThis : (clipperVatFluxThisMem I (clipperVatFluxIlkMem v mem)).size = 196 :=
    clipperVatFluxThisMem_size I hIlk
  have hCaller :
      (clipperVatFluxCallerMem I
        (clipperVatFluxThisMem I (clipperVatFluxIlkMem v mem))).size = 228 :=
    clipperVatFluxCallerMem_size I hThis
  unfold clipperVatFluxCalldataMem
  rw [write32_read_below _ _ 228 196 (by rw [toByteArray_size])
    (by rw [hCaller])
    (by omega)]
  unfold clipperVatFluxCallerMem
  rw [write32_read_back _ _ 196 (by rw [toByteArray_size])
    (by rw [hThis])]
  rw [show (UInt256.toByteArray (solcSourceWord I)).extract 0 32 =
      UInt256.toByteArray (solcSourceWord I) by
    rw [show 32 = (UInt256.toByteArray (solcSourceWord I)).size by rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem clipperVatFluxCalldataMem_read228_32 (v : ClipperImmutables) (I : ExecutionEnv)
    (lot : UInt256) {mem : ByteArray} (hmem : mem.size = 196) :
    (clipperVatFluxCalldataMem v I lot mem).readWithPadding 228 32 =
      UInt256.toByteArray lot := by
  have hIlk : (clipperVatFluxIlkMem v mem).size = 196 :=
    clipperVatFluxIlkMem_size v hmem
  have hThis : (clipperVatFluxThisMem I (clipperVatFluxIlkMem v mem)).size = 196 :=
    clipperVatFluxThisMem_size I hIlk
  have hCaller :
      (clipperVatFluxCallerMem I
        (clipperVatFluxThisMem I (clipperVatFluxIlkMem v mem))).size = 228 :=
    clipperVatFluxCallerMem_size I hThis
  unfold clipperVatFluxCalldataMem
  rw [write32_read_back _ _ 228 (by rw [toByteArray_size])
    (by rw [hCaller])]
  rw [show (UInt256.toByteArray lot).extract 0 32 = UInt256.toByteArray lot by
    rw [show 32 = (UInt256.toByteArray lot).size by rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem clipperVatFluxCalldataMem_read128_132 (v : ClipperImmutables) (I : ExecutionEnv)
    (lot : UInt256) {mem : ByteArray} (hmem : mem.size = 196) :
    (clipperVatFluxCalldataMem v I lot mem).readWithPadding 128 132 =
      vatFluxSelector ++ UInt256.toByteArray (clipperYankIlkWord v) ++
        UInt256.toByteArray (clipperYankThisWord I) ++
        UInt256.toByteArray (solcSourceWord I) ++ UInt256.toByteArray lot := by
  rw [byteArray_readWithPadding_split _ 128 4 128 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [clipperVatFluxCalldataMem_size v I lot hmem])]
  rw [byteArray_readWithPadding_split _ 132 32 96 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [clipperVatFluxCalldataMem_size v I lot hmem])]
  rw [byteArray_readWithPadding_split _ 164 32 64 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [clipperVatFluxCalldataMem_size v I lot hmem])]
  rw [byteArray_readWithPadding_split _ 196 32 32 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [clipperVatFluxCalldataMem_size v I lot hmem])]
  rw [clipperVatFluxCalldataMem_read128_4 v I lot hmem,
    clipperVatFluxCalldataMem_read132_32 v I lot hmem,
    clipperVatFluxCalldataMem_read164_32 v I lot hmem,
    clipperVatFluxCalldataMem_read196_32 v I lot hmem,
    clipperVatFluxCalldataMem_read228_32 v I lot hmem]
  simp [ByteArray.append_assoc]

theorem clipperVatFluxEncode_eq (v : ClipperImmutables) (I : ExecutionEnv)
    (lot : UInt256) {mem : ByteArray} (hmem : mem.size = 196) :
    (config v).externalABI.encode? "flux"
      [v.ilk, .address I.codeOwner, .address I.source, .int (Int.ofNat lot.toNat)] =
      some ((clipperVatFluxCalldataMem v I lot mem).readWithPadding 128 132) := by
  rcases v.ilk_wf with ⟨bs, hilk, hlen⟩
  rw [hilk]
  have hilkWord :
      clipperYankIlkWord v = EVM.Word.ofNat (fromBytesBigEndian bs) := by
    simp [clipperYankIlkWord, hilk]
  rw [clipperVatFluxCalldataMem_read128_132 v I lot hmem, hilkWord]
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
  have hthis : EVM.word I.codeOwner = clipperYankThisWord I := by
    unfold clipperYankThisWord EVM.word EVM.uintN UInt256.ofNat
    rfl
  have hsource : EVM.word I.source = solcSourceWord I := by
    unfold solcSourceWord EVM.word EVM.uintN UInt256.ofNat
    rfl
  have hlotWord : EVM.word lot.toNat = lot := u256_ofNat_toNat lot
  have hlotLt : lot.toNat < EVM.twoPow 256 := by
    change lot.val.val < UInt256.size
    exact lot.val.isLt
  change externalABI.encode? "flux"
      [.fixedBytes ⟨31, by decide⟩ bs, .address I.codeOwner, .address I.source,
        .int (Int.ofNat lot.toNat)] =
    some (vatFluxSelector ++ UInt256.toByteArray (EVM.Word.ofNat (fromBytesBigEndian bs)) ++
      UInt256.toByteArray (clipperYankThisWord I) ++
      UInt256.toByteArray (solcSourceWord I) ++ UInt256.toByteArray lot)
  unfold externalABI ABI.encodeCallWithSelector? ABI.encodeABIValues?
  simp [ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType, bytes32,
    bytes32Width, addr, uint256, uint256Int, selectorBytes, vatFluxSelector, hlen,
    ABI.zeroBytes, hwordBytes, hbsByteArray, hlotLt, hlotWord, hthis, hsource,
    word_toBytesBE_toByteArray_eq_toByteArray, ByteArray.append_assoc]

theorem clipperYankIlkPatchPayload2221 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {bs : List UInt8} (hilk : v.ilk = .fixedBytes ⟨31, by decide⟩ bs)
    (hlen : bs.length = 32) :
    code.extract' 2221 2253 =
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
      PatchesWindowDisjoint32 2221 2253
        [(2369, ilkBytes), (4239, ilkBytes), (4866, ilkBytes), (5046, ilkBytes),
          (6800, ilkBytes), (8747, ilkBytes)] := by
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | hfalse
    all_goals first | (unfold PatchWindowDisjoint32; omega) | cases hfalse
  exact patchRuntime_extract'_exact_split (template := clipperBytecode)
    (pre :=
      [(1463, vatBytes), (2437, vatBytes), (3145, vatBytes), (4318, vatBytes),
        (4441, vatBytes), (4751, vatBytes), (5115, vatBytes), (6295, vatBytes),
        (7936, vatBytes), (1510, ilkBytes), (1661, ilkBytes)])
    (post :=
      [(2369, ilkBytes), (4239, ilkBytes), (4866, ilkBytes), (5046, ilkBytes),
        (6800, ilkBytes), (8747, ilkBytes)])
    (off := 2221) (value := ilkBytes)
    (by
      simpa [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, hilk, hlen,
        List.lookup_cons, ilkBytes, vatBytes] using hpatch)
    hsize hpost (by norm_num) (by norm_num)

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem clipperYankIlkPush32Decode2220 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {bs : List UInt8} (hilk : v.ilk = .fixedBytes ⟨31, by decide⟩ bs)
    (hlen : bs.length = 32) :
    decode code (⟨2220⟩ : UInt256) =
      some (.Push .PUSH32, some (EVM.Word.ofNat (fromBytesBigEndian bs), 32)) := by
  unfold decode
  rw [patchRuntime_get?_disjoint hpatch
    (by apply clipperYankPatchesWindowDisjoint32 v <;> native_decide)]
  change some (Operation.Push Operation.POp.PUSH32,
      some (uInt256OfByteArray (code.extract' 2221 2253), 32)) =
    some (Operation.Push Operation.POp.PUSH32,
      some (EVM.Word.ofNat (fromBytesBigEndian bs), 32))
  rw [clipperYankIlkPatchPayload2221 v hpatch hilk hlen]
  rw [uInt256OfByteArray_word_toBytesBE]

theorem clipperYankIlkPatchPayload2369 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {bs : List UInt8} (hilk : v.ilk = .fixedBytes ⟨31, by decide⟩ bs)
    (hlen : bs.length = 32) :
    code.extract' 2369 2401 =
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
      PatchesWindowDisjoint32 2369 2401
        [(4239, ilkBytes), (4866, ilkBytes), (5046, ilkBytes), (6800, ilkBytes),
          (8747, ilkBytes)] := by
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | hfalse
    all_goals first | (unfold PatchWindowDisjoint32; omega) | cases hfalse
  exact patchRuntime_extract'_exact_split (template := clipperBytecode)
    (pre :=
      [(1463, vatBytes), (2437, vatBytes), (3145, vatBytes), (4318, vatBytes),
        (4441, vatBytes), (4751, vatBytes), (5115, vatBytes), (6295, vatBytes),
        (7936, vatBytes), (1510, ilkBytes), (1661, ilkBytes), (2221, ilkBytes)])
    (post :=
      [(4239, ilkBytes), (4866, ilkBytes), (5046, ilkBytes), (6800, ilkBytes),
        (8747, ilkBytes)])
    (off := 2369) (value := ilkBytes)
    (by
      simpa [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, hilk, hlen,
        List.lookup_cons, ilkBytes, vatBytes] using hpatch)
    hsize hpost (by norm_num) (by norm_num)

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem clipperYankIlkPush32Decode2368 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {bs : List UInt8} (hilk : v.ilk = .fixedBytes ⟨31, by decide⟩ bs)
    (hlen : bs.length = 32) :
    decode code (⟨2368⟩ : UInt256) =
      some (.Push .PUSH32, some (EVM.Word.ofNat (fromBytesBigEndian bs), 32)) := by
  unfold decode
  rw [patchRuntime_get?_disjoint hpatch
    (by apply clipperYankPatchesWindowDisjoint32AfterIlk v <;> native_decide)]
  change some (Operation.Push Operation.POp.PUSH32,
      some (uInt256OfByteArray (code.extract' 2369 2401), 32)) =
    some (Operation.Push Operation.POp.PUSH32,
      some (EVM.Word.ofNat (fromBytesBigEndian bs), 32))
  rw [clipperYankIlkPatchPayload2369 v hpatch hilk hlen]
  rw [uInt256OfByteArray_word_toBytesBE]

theorem clipperYankVatPatchPayload2437 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    code.extract' 2437 2469 =
      ({ data := (EVM.Word.ofNat (↑v.vat : Nat)).toBytesBE.toArray } : ByteArray) := by
  rcases v.ilk_wf with ⟨bs, hilk, hlen⟩
  let ilkBytes : ByteArray :=
    { data := (EVM.Word.ofNat (fromBytesBigEndian bs)).toBytesBE.toArray }
  let vatBytes : ByteArray :=
    { data := (EVM.Word.ofNat (↑v.vat : Nat)).toBytesBE.toArray }
  have hsize : vatBytes.size = 32 := by
    simpa [vatBytes] using word_toBytesBE_toByteArray_size (EVM.Word.ofNat (↑v.vat : Nat))
  have hpost :
      PatchesWindowDisjoint32 2437 2469
        [(3145, vatBytes), (4318, vatBytes), (4441, vatBytes), (4751, vatBytes),
          (5115, vatBytes), (6295, vatBytes), (7936, vatBytes),
          (1510, ilkBytes), (1661, ilkBytes), (2221, ilkBytes), (2369, ilkBytes),
          (4239, ilkBytes), (4866, ilkBytes), (5046, ilkBytes), (6800, ilkBytes),
          (8747, ilkBytes)] := by
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | hfalse
    all_goals first | (unfold PatchWindowDisjoint32; omega) | cases hfalse
  exact patchRuntime_extract'_exact_split (template := clipperBytecode)
    (pre := [(1463, vatBytes)])
    (post :=
      [(3145, vatBytes), (4318, vatBytes), (4441, vatBytes), (4751, vatBytes),
        (5115, vatBytes), (6295, vatBytes), (7936, vatBytes),
        (1510, ilkBytes), (1661, ilkBytes), (2221, ilkBytes), (2369, ilkBytes),
        (4239, ilkBytes), (4866, ilkBytes), (5046, ilkBytes), (6800, ilkBytes),
        (8747, ilkBytes)])
    (off := 2437) (value := vatBytes)
    (by
      simpa [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, hilk, hlen,
        List.lookup_cons, ilkBytes, vatBytes] using hpatch)
    hsize hpost (by norm_num) (by norm_num)

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem clipperYankVatPush32Decode2436 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    decode code (⟨2436⟩ : UInt256) =
      some (.Push .PUSH32, some (EVM.Word.ofNat (↑v.vat : Nat), 32)) := by
  unfold decode
  rw [patchRuntime_get?_disjoint hpatch
    (by apply clipperYankPatchesWindowDisjoint32FluxBeforeVat v <;> native_decide)]
  change some (Operation.Push Operation.POp.PUSH32,
      some (uInt256OfByteArray (code.extract' 2437 2469), 32)) =
    some (Operation.Push Operation.POp.PUSH32, some (EVM.Word.ofNat (↑v.vat : Nat), 32))
  rw [clipperYankVatPatchPayload2437 v hpatch]
  rw [uInt256OfByteArray_word_toBytesBE]

theorem clipperYankJumpDest1994 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨1994⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 2500) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperYankJumpDest2071 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨2071⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 2500) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperYankJumpDest2184 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨2184⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 2500) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperYankJumpDest2313 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨2313⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 2500) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperYankJumpDest2333 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨2333⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 2500) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperYankJumpDest2507 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨2507⟩ : UInt256) = true := by
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

theorem clipperYankJumpDest2527 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨2527⟩ : UInt256) = true := by
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

set_option maxHeartbeats 1000000 in
theorem clipperYankX_authorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (h : RD code I g s0 ⟨1912⟩
      [clipperYankArgWord I, ⟨502⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨1994⟩
      [clipperYankArgWord I, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((clipperRelyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (clipperRelySourceWord I) ⟨0⟩ := by
    simpa [clipperRelyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (clipperRelySourceWord I)
        solcFreePtrMem_size
  have rd1918pre := evm_run h with [
    raw jumpdest (by clipper_yank_decode) (by evm_ov),
    raw caller (by clipper_yank_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_yank_decode) (by evm_ov),
    raw swap1 (by clipper_yank_decode) (by evm_ov),
    raw dup2 (by clipper_yank_decode) (by evm_ov)]
  have rd1919 := rd1918pre.mstore 0
    (wordAt0Mem (clipperRelySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by clipper_yank_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd1923pre := evm_run rd1919 with [
    raw push1 ⟨32⟩ (by clipper_yank_decode) (by evm_ov),
    raw dup2 (by clipper_yank_decode) (by evm_ov),
    raw swap1 (by clipper_yank_decode) (by evm_ov)]
  have rd1924 := rd1923pre.mstore 0 (clipperRelyAuthHashMem I)
    (UInt256.ofNat 3) (by clipper_yank_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd1927pre := evm_run rd1924 with [
    raw push1 ⟨64⟩ (by clipper_yank_decode) (by evm_ov),
    raw swap1 (by clipper_yank_decode) (by evm_ov)]
  have rd1928 := rd1927pre.keccak256 0 (mapSlot (clipperRelySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by clipper_yank_decode) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k1929, C1929, rd1929raw⟩ := rd1928.sload
    (by clipper_yank_decode) (by evm_ov)
  have rd1929 : RD code I g s0 ⟨1929⟩
      (clipperRelyAuthWord σ I :: clipperYankArgWord I :: ⟨502⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1929 C1929 := by
    simpa [clipperRelyAuthWord, solcSlotWord,
      clipperRelyAuthStorageSlot_eq_mapSlot_source I] using rd1929raw
  have rd1932pre := evm_run rd1929 with [
    raw push1 ⟨1⟩ (by clipper_yank_decode) (by evm_ov),
    raw eq (by clipper_yank_decode) (by evm_ov)]
  rw [hauth, u256_eq_refl] at rd1932pre
  have rd1935 := rd1932pre.pushConst (⟨1994⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_yank_decode) (by evm_ov)
  exact ⟨_, _, rd1935.jumpiT (by clipper_yank_decode) one_ne_zero_uint
    (clipperYankJumpDest1994 v hpatch) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem clipperYankX_unauthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hauth : clipperRelyAuthWord σ I ≠ ⟨1⟩)
    (h : RD code I g s0 ⟨1912⟩
      [clipperYankArgWord I, ⟨502⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g s0 := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((clipperRelyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (clipperRelySourceWord I) ⟨0⟩ := by
    simpa [clipperRelyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (clipperRelySourceWord I)
        solcFreePtrMem_size
  have rd1918pre := evm_run h with [
    raw jumpdest (by clipper_yank_decode) (by evm_ov),
    raw caller (by clipper_yank_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_yank_decode) (by evm_ov),
    raw swap1 (by clipper_yank_decode) (by evm_ov),
    raw dup2 (by clipper_yank_decode) (by evm_ov)]
  have rd1919 := rd1918pre.mstore 0
    (wordAt0Mem (clipperRelySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by clipper_yank_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd1923pre := evm_run rd1919 with [
    raw push1 ⟨32⟩ (by clipper_yank_decode) (by evm_ov),
    raw dup2 (by clipper_yank_decode) (by evm_ov),
    raw swap1 (by clipper_yank_decode) (by evm_ov)]
  have rd1924 := rd1923pre.mstore 0 (clipperRelyAuthHashMem I)
    (UInt256.ofNat 3) (by clipper_yank_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd1927pre := evm_run rd1924 with [
    raw push1 ⟨64⟩ (by clipper_yank_decode) (by evm_ov),
    raw swap1 (by clipper_yank_decode) (by evm_ov)]
  have rd1928 := rd1927pre.keccak256 0 (mapSlot (clipperRelySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by clipper_yank_decode) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k1929, C1929, rd1929raw⟩ := rd1928.sload
    (by clipper_yank_decode) (by evm_ov)
  have rd1929 : RD code I g s0 ⟨1929⟩
      (clipperRelyAuthWord σ I :: clipperYankArgWord I :: ⟨502⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1929 C1929 := by
    simpa [clipperRelyAuthWord, solcSlotWord,
      clipperRelyAuthStorageSlot_eq_mapSlot_source I] using rd1929raw
  have rd1932pre := evm_run rd1929 with [
    raw push1 ⟨1⟩ (by clipper_yank_decode) (by evm_ov),
    raw eq (by clipper_yank_decode) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (clipperRelyAuthWord σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hauth hbad.symm)
  rw [heq] at rd1932pre
  have rd1935 := rd1932pre.pushConst (⟨1994⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_yank_decode) (by evm_ov)
  have rd1936 := rd1935.jumpiNT (by clipper_yank_decode) rfl (by evm_ov)
  have rd1940 := evm_run rd1936 with [
    raw push1 ⟨64⟩ (by clipper_yank_decode) (by evm_ov),
    raw dup1 (by clipper_yank_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by clipper_yank_decode) mem_cost
      (mloadFreePtrValue (by rw [clipperRelyAuthHashMem_size]; decide)
        (by decide) (clipperRelyAuthHashMem_read64 I))
      (by native_decide) (by evm_ov)]
  have rd1944 := rd1940.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by clipper_yank_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1947 := evm_run rd1944 with [
    raw push1 ⟨229⟩ (by clipper_yank_decode) (by evm_ov),
    raw shl (by clipper_yank_decode) (by evm_ov)]
  rw [clipperRelyNotAuthorizedWord] at rd1947
  have rd1948pre := evm_run rd1947 with [
    raw dup2 (by clipper_yank_decode) (by evm_ov)]
  have rd1949 := rd1948pre.mstore 6
    (solcErrorStringMem0 (clipperRelyAuthHashMem I))
    (UInt256.ofNat 5) (by clipper_yank_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd1955pre := evm_run rd1949 with [
    raw push1 ⟨32⟩ (by clipper_yank_decode) (by evm_ov),
    raw push1 ⟨4⟩ (by clipper_yank_decode) (by evm_ov),
    raw dup3 (by clipper_yank_decode) (by evm_ov),
    raw add (by clipper_yank_decode) (by evm_ov)]
  have rd1956 := rd1955pre.mstore 3
    (solcErrorStringMem1 (clipperRelyAuthHashMem I))
    (UInt256.ofNat 6) (by clipper_yank_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd1967pre := evm_run rd1956 with [
    raw push1 ⟨22⟩ (by clipper_yank_decode) (by evm_ov),
    raw push1 ⟨36⟩ (by clipper_yank_decode) (by evm_ov),
    raw dup3 (by clipper_yank_decode) (by evm_ov),
    raw add (by clipper_yank_decode) (by evm_ov),
    raw mstore 3 (clipperRelyErrorMem2 I)
      (UInt256.ofNat 7) (by clipper_yank_decode) mem_cost (by rfl)
      (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_yank_decode) (by evm_ov),
    raw dup1 (by clipper_yank_decode) (by evm_ov),
    raw mload 0 (clipperRelySourceWord I) (UInt256.ofNat 7)
      (by clipper_yank_decode) mem_cost (clipperRelyErrorMem2_mload0 I)
      (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_yank_decode) (by evm_ov)]
  have rd1972 := rd1967pre.pushConst (⟨9316⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_yank_decode) (by evm_ov)
  have rd1973pre := evm_run rd1972 with [
    raw dup4 (by clipper_yank_decode) (by evm_ov)]
  have rd1974 := rd1973pre.codecopy 0 (clipperRelyErrorCopiedMem code I)
    (UInt256.ofNat 7) (by clipper_yank_decode) mem_cost
    (by
      rw [show (⟨9316⟩ : UInt256).toNat = 9316 from by decide,
        show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      rfl)
    (by native_decide) (by evm_ov)
  have rd1977 := evm_run rd1974 with [
    raw dup2 (by clipper_yank_decode) (by evm_ov),
    raw mload 0 clipperRelyNotAuthorizedStringWord (UInt256.ofNat 7)
      (by clipper_yank_decode) mem_cost
      (by simpa [clipperRelyErrorCopiedMem, clipperRelyErrorMem2]
        using clipperRelyCodecopyMload0 v hpatch I)
      (by native_decide) (by evm_ov),
    raw swap2 (by clipper_yank_decode) (by evm_ov)]
  have rd1978 := rd1977.mstore 0 (clipperRelyErrorRestoredMem code I)
    (UInt256.ofNat 7) (by clipper_yank_decode) mem_cost
    (by simp [clipperRelyErrorRestoredMem, clipperRelyErrorCopiedMem])
    (by native_decide) (by evm_ov)
  have rd1982pre := evm_run rd1978 with [
    raw push1 ⟨68⟩ (by clipper_yank_decode) (by evm_ov),
    raw dup3 (by clipper_yank_decode) (by evm_ov),
    raw add (by clipper_yank_decode) (by evm_ov)]
  have rd1983 := rd1982pre.mstore 3 (clipperRelyErrorStringMem code I)
    (UInt256.ofNat 8) (by clipper_yank_decode) mem_cost
    (by
      rw [show ((⟨128⟩ : UInt256) + ⟨68⟩).toNat = 196 from by decide])
    (by native_decide) (by evm_ov)
  have rd1985 := evm_run rd1983 with [
    raw swap1 (by clipper_yank_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by clipper_yank_decode) mem_cost
      (clipperRelyErrorStringMem_mload64 v hpatch I)
      (by native_decide) (by evm_ov)]
  exact evm_run rd1985 with [
    raw swap1 (by clipper_yank_decode) (by evm_ov),
    raw dup2 (by clipper_yank_decode) (by evm_ov),
    raw swap1 (by clipper_yank_decode) (by evm_ov),
    raw sub (by clipper_yank_decode) (by evm_ov),
    raw push1 ⟨100⟩ (by clipper_yank_decode) (by evm_ov),
    raw add (by clipper_yank_decode) (by evm_ov),
    raw swap1 (by clipper_yank_decode) (by evm_ov),
    raw rev 0 (by clipper_yank_decode) mem_cost (by evm_ov)]

theorem clipperYankX_lockOpen {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (h : RD code I g s0 ⟨1994⟩
      [clipperYankArgWord I, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨2071⟩
      [clipperYankArgWord I, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd1997pre := evm_run h with [
    raw jumpdest (by clipper_yank_decode) (by evm_ov),
    raw push1 ⟨13⟩ (by clipper_yank_decode) (by evm_ov)]
  obtain ⟨k1998, C1998, rd1998raw⟩ := rd1997pre.sload
    (by clipper_yank_decode) (by evm_ov)
  have rd1998 : RD code I g s0 ⟨1998⟩
      (solcSlotWord σ I ⟨13⟩ :: clipperYankArgWord I :: ⟨502⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1998 C1998 := by
    simpa [solcSlotWord] using rd1998raw
  have rd1999 := rd1998.iszero (by clipper_yank_decode) (by evm_ov)
  have hcond : UInt256.isZero (solcSlotWord σ I ⟨13⟩) ≠ ⟨0⟩ := by
    rw [hlocked]
    native_decide
  have rd2002 := rd1999.pushConst (⟨2071⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_yank_decode) (by evm_ov)
  exact ⟨_, _, rd2002.jumpiT (by clipper_yank_decode) hcond
    (clipperYankJumpDest2071 v hpatch) (by evm_ov)⟩

theorem clipperYankX_lockStore {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hperm : I.perm = true)
    (h : RD code I g s0 ⟨2071⟩
      [clipperYankArgWord I, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨2077⟩
      [clipperYankArgWord I, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) k' C' := by
  have rd2076 := evm_run h with [
    raw jumpdest (by clipper_yank_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_yank_decode) (by evm_ov),
    raw push1 ⟨13⟩ (by clipper_yank_decode) (by evm_ov)]
  obtain ⟨_, _, rd2077⟩ := rd2076.sstore hperm (by clipper_yank_decode) (by evm_ov)
  exact ⟨_, _, by simpa using rd2077⟩

set_option maxHeartbeats 1000000 in
theorem clipperYankX_usrNonzero {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (husr :
      clipperYankSalesUsrWord σ I ≠ ⟨0⟩)
    (h : RD code I g s0 ⟨2077⟩
      [clipperYankArgWord I, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨2184⟩
      [clipperYankArgWord I, ⟨502⟩, sel]
      (twoWordHashMem (clipperYankArgWord I) ⟨12⟩ (clipperRelyAuthHashMem I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC
            ((twoWordHashMem (clipperYankArgWord I) ⟨12⟩
              (clipperRelyAuthHashMem I)).readWithPadding 0 64))) =
        clipperYankSalesBaseSlot I := by
    rw [clipperYankSalesBaseSlot_eq I]
    exact twoWordHashMem_solcMappingSlot ⟨12⟩ (clipperYankArgWord I)
      (clipperRelyAuthHashMem_size I)
  have rd2081pre := evm_run h with [
    raw push1 ⟨0⟩ (by clipper_yank_decode) (by evm_ov),
    raw dup2 (by clipper_yank_decode) (by evm_ov),
    raw dup2 (by clipper_yank_decode) (by evm_ov)]
  have rd2082 := rd2081pre.mstore 0
    (wordAt0Mem (clipperYankArgWord I) (clipperRelyAuthHashMem I))
    (UInt256.ofNat 3) (by clipper_yank_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd2086pre := evm_run rd2082 with [
    raw push1 ⟨12⟩ (by clipper_yank_decode) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_yank_decode) (by evm_ov)]
  have rd2087 := rd2086pre.mstore 0
    (twoWordHashMem (clipperYankArgWord I) ⟨12⟩ (clipperRelyAuthHashMem I))
    (UInt256.ofNat 3) (by clipper_yank_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd2090pre := evm_run rd2087 with [
    raw push1 ⟨64⟩ (by clipper_yank_decode) (by evm_ov),
    raw swap1 (by clipper_yank_decode) (by evm_ov)]
  have rd2091 := rd2090pre.keccak256 0 (clipperYankSalesBaseSlot I)
    (UInt256.ofNat 3) (by clipper_yank_decode) mem_cost hslot (by native_decide)
    (by evm_ov)
  have rd2094pre := evm_run rd2091 with [
    raw push1 ⟨3⟩ (by clipper_yank_decode) (by evm_ov),
    raw add (by clipper_yank_decode) (by evm_ov)]
  rw [u256_add_comm ⟨3⟩ (clipperYankSalesBaseSlot I)] at rd2094pre
  obtain ⟨k2095, C2095, rd2095raw⟩ := rd2094pre.sload
    (by clipper_yank_decode) (by evm_ov)
  have rd2095 : RD code I g s0 ⟨2095⟩
      (solcSlotWord σ I (clipperYankSalesUsrSlot I) :: clipperYankArgWord I ::
        ⟨502⟩ :: [sel])
      (twoWordHashMem (clipperYankArgWord I) ⟨12⟩ (clipperRelyAuthHashMem I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2095 C2095 := by
    simpa [clipperYankSalesUsrSlot, solcSlotWord] using rd2095raw
  have rd2104pre := evm_run rd2095 with [
    raw push1 ⟨1⟩ (by clipper_yank_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_yank_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_yank_decode) (by evm_ov),
    raw shl (by clipper_yank_decode) (by evm_ov),
    raw sub (by clipper_yank_decode) (by evm_ov),
    raw and (by clipper_yank_decode) (by evm_ov)]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
    solcAddrMask from by native_decide] at rd2104pre
  have rd2107 := rd2104pre.pushConst (⟨2184⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_yank_decode) (by evm_ov)
  have husrStack :
      UInt256.land solcAddrMask (solcSlotWord σ I (clipperYankSalesUsrSlot I)) ≠ ⟨0⟩ := by
    simpa [clipperYankSalesUsrWord, u256_land_comm] using husr
  exact ⟨_, _, rd2107.jumpiT (by clipper_yank_decode) husrStack
    (clipperYankJumpDest2184 v hpatch) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem clipperYankX_loadDogAndTab {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (h : RD code I g s0 ⟨2184⟩
      [clipperYankArgWord I, ⟨502⟩, sel]
      (clipperYankSalesHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨2208⟩
      (clipperYankSalesTabWord σ I :: ⟨0⟩ :: solcSlotWord σ I ⟨1⟩ ::
        ⟨64⟩ :: clipperYankArgWord I :: ⟨502⟩ :: [sel])
      (clipperYankSalesHashMemRefresh I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k'
      C' := by
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((clipperYankSalesHashMemRefresh I).readWithPadding 0 64))) =
        clipperYankSalesBaseSlot I := by
    rw [clipperYankSalesHashMemRefresh, clipperYankSalesBaseSlot_eq I]
    exact twoWordHashMem_solcMappingSlot ⟨12⟩ (clipperYankArgWord I)
      (clipperYankSalesHashMem_size I)
  have rd2188pre := evm_run h with [
    raw jumpdest (by clipper_yank_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_yank_decode) (by evm_ov),
    raw dup1 (by clipper_yank_decode) (by evm_ov)]
  obtain ⟨k2189, C2189, rd2189raw⟩ := rd2188pre.sload
    (by clipper_yank_decode) (by evm_ov)
  have rd2189 : RD code I g s0 ⟨2189⟩
      (solcSlotWord σ I ⟨1⟩ :: ⟨1⟩ :: clipperYankArgWord I :: ⟨502⟩ :: [sel])
      (clipperYankSalesHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2189
      C2189 := by
    simpa [solcSlotWord] using rd2189raw
  have rd2193pre := evm_run rd2189 with [
    raw push1 ⟨0⟩ (by clipper_yank_decode) (by evm_ov),
    raw dup4 (by clipper_yank_decode) (by evm_ov),
    raw dup2 (by clipper_yank_decode) (by evm_ov)]
  have rd2194 := rd2193pre.mstore 0
    (wordAt0Mem (clipperYankArgWord I) (clipperYankSalesHashMem I))
    (UInt256.ofNat 3) (by clipper_yank_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd2198pre := evm_run rd2194 with [
    raw push1 ⟨12⟩ (by clipper_yank_decode) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_yank_decode) (by evm_ov)]
  have rd2199 := rd2198pre.mstore 0
    (clipperYankSalesHashMemRefresh I) (UInt256.ofNat 3) (by clipper_yank_decode) mem_cost
    (by rfl) (by rfl) (by evm_ov)
  have rd2203pre := evm_run rd2199 with [
    raw push1 ⟨64⟩ (by clipper_yank_decode) (by evm_ov),
    raw dup1 (by clipper_yank_decode) (by evm_ov),
    raw dup3 (by clipper_yank_decode) (by evm_ov)]
  have rd2204 := rd2203pre.keccak256 0 (clipperYankSalesBaseSlot I)
    (UInt256.ofNat 3) (by clipper_yank_decode) mem_cost hslot (by native_decide)
    (by evm_ov)
  have rd2207pre := evm_run rd2204 with [
    raw swap1 (by clipper_yank_decode) (by evm_ov),
    raw swap4 (by clipper_yank_decode) (by evm_ov),
    raw add (by clipper_yank_decode) (by evm_ov)]
  rw [u256_add_comm ⟨1⟩ (clipperYankSalesBaseSlot I)] at rd2207pre
  obtain ⟨k2208, C2208, rd2208raw⟩ := rd2207pre.sload
    (by clipper_yank_decode) (by evm_ov)
  have rd2208 : RD code I g s0 ⟨2208⟩
      (solcSlotWord σ I (clipperYankSalesTabSlot I) :: ⟨0⟩ :: solcSlotWord σ I ⟨1⟩ ::
        ⟨64⟩ :: clipperYankArgWord I :: ⟨502⟩ :: [sel])
      (clipperYankSalesHashMemRefresh I) (UInt256.ofNat 3) ByteArray.empty (cA, σ)
      k2208 C2208 := by
    simpa [clipperYankSalesTabSlot, solcSlotWord] using rd2208raw
  exact ⟨_, _, by simpa [clipperYankSalesTabWord] using rd2208⟩

set_option maxHeartbeats 1000000 in
theorem clipperYankX_dogDigsCallSetup {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (h : RD code I g s0 ⟨2208⟩
      [clipperYankSalesTabWord σ I, ⟨0⟩, solcSlotWord σ I ⟨1⟩, ⟨64⟩,
        clipperYankArgWord I, ⟨502⟩, sel]
      (clipperYankSalesHashMemRefresh I) (UInt256.ofNat 3) ByteArray.empty (cA, σ)
      k C) :
    ∃ k' C', RD code I g s0 ⟨2279⟩
      (UInt256.land solcAddrMask (solcSlotWord σ I ⟨1⟩) :: ⟨0⟩ :: ⟨128⟩ ::
        ⟨128⟩ :: clipperYankArgWord I :: ⟨502⟩ :: [sel])
      (clipperDogDigsCalldataMem v (clipperYankSalesTabWord σ I)
        (clipperYankSalesHashMemRefresh I))
      (UInt256.ofNat 7) ByteArray.empty (cA, σ) k' C' := by
  rcases v.ilk_wf with ⟨ilkBs, hilk, hlen⟩
  let ilkWord : UInt256 := EVM.Word.ofNat (fromBytesBigEndian ilkBs)
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (clipperYankSalesHashMemRefresh I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((clipperYankSalesHashMemRefresh I).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue
      (by rw [clipperYankSalesHashMemRefresh_size I]; decide)
      (by decide)
      (clipperYankSalesHashMemRefresh_read64 I)
  have hcallMload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (clipperDogDigsCalldataMem v (clipperYankSalesTabWord σ I)
              (clipperYankSalesHashMemRefresh I)).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((clipperDogDigsCalldataMem v (clipperYankSalesTabWord σ I)
              (clipperYankSalesHashMemRefresh I)).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    clipperDogDigsCalldataMem_mload64 v (clipperYankSalesTabWord σ I)
      (clipperYankSalesHashMemRefresh_size I)
      (clipperYankSalesHashMemRefresh_read64 I)
  have rd2210pre := evm_run h with [
    raw dup4 (by clipper_yank_decode) (by evm_ov)]
  have rd2210 := rd2210pre.mload 0 ⟨128⟩ (UInt256.ofNat 3)
    (by clipper_yank_decode) mem_cost hmload64 (by native_decide) (by evm_ov)
  have rd2219pre := evm_run rd2210 with [
    raw push4 clipperDogDigsSelectorSeed (by clipper_yank_decode) (by evm_ov),
    raw push1 ⟨226⟩ (by clipper_yank_decode) (by evm_ov),
    raw shl (by clipper_yank_decode) (by evm_ov),
    raw dup2 (by clipper_yank_decode) (by evm_ov)]
  rw [show UInt256.shiftLeft clipperDogDigsSelectorSeed ⟨226⟩ =
    clipperDogDigsSelectorShifted from by native_decide] at rd2219pre
  have rd2220 := rd2219pre.mstore 6
    (clipperDogDigsSelectorMem (clipperYankSalesHashMemRefresh I))
    (UInt256.ofNat 5) (by clipper_yank_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd2253 := rd2220.pushConst ilkWord (width := 32) (op := .PUSH32)
    (by decide)
    (by simpa [ilkWord] using clipperYankIlkPush32Decode2220 v hpatch hilk hlen)
    (by evm_ov)
  have rd2257pre := evm_run rd2253 with [
    raw push1 ⟨4⟩ (by clipper_yank_decode) (by evm_ov),
    raw dup3 (by clipper_yank_decode) (by evm_ov),
    raw add (by clipper_yank_decode) (by evm_ov)]
  rw [show (⟨128⟩ : UInt256) + ⟨4⟩ = ⟨132⟩ from by native_decide] at rd2257pre
  have rd2258 := rd2257pre.mstore 3
    (clipperDogDigsIlkMem v (clipperYankSalesHashMemRefresh I))
    (UInt256.ofNat 6) (by clipper_yank_decode) mem_cost
    (by
      rw [show (⟨132⟩ : UInt256).toNat = 132 from by decide]
      simp [clipperDogDigsIlkMem, clipperYankIlkWord, hilk, ilkWord])
    (by native_decide) (by evm_ov)
  have rd2265pre := evm_run rd2258 with [
    raw push1 ⟨36⟩ (by clipper_yank_decode) (by evm_ov),
    raw dup2 (by clipper_yank_decode) (by evm_ov),
    raw add (by clipper_yank_decode) (by evm_ov),
    raw swap2 (by clipper_yank_decode) (by evm_ov),
    raw swap1 (by clipper_yank_decode) (by evm_ov),
    raw swap2 (by clipper_yank_decode) (by evm_ov)]
  rw [show (⟨128⟩ : UInt256) + ⟨36⟩ = ⟨164⟩ from by native_decide] at rd2265pre
  have rd2266 := rd2265pre.mstore 3
    (clipperDogDigsCalldataMem v (clipperYankSalesTabWord σ I)
      (clipperYankSalesHashMemRefresh I))
    (UInt256.ofNat 7) (by clipper_yank_decode) mem_cost (by rfl)
    (by native_decide) (by evm_ov)
  have rd2267pre := evm_run rd2266 with [
    raw swap3 (by clipper_yank_decode) (by evm_ov)]
  have rd2268 := rd2267pre.mload 0 ⟨128⟩ (UInt256.ofNat 7)
    (by clipper_yank_decode) mem_cost hcallMload64 (by native_decide) (by evm_ov)
  have rd2278pre := evm_run rd2268 with [
    raw push1 ⟨1⟩ (by clipper_yank_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_yank_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_yank_decode) (by evm_ov),
    raw shl (by clipper_yank_decode) (by evm_ov),
    raw sub (by clipper_yank_decode) (by evm_ov),
    raw swap1 (by clipper_yank_decode) (by evm_ov),
    raw swap3 (by clipper_yank_decode) (by evm_ov),
    raw and (by clipper_yank_decode) (by evm_ov)]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
    solcAddrMask from by native_decide] at rd2278pre
  exact ⟨_, _, by
    simpa [u256_land_comm] using rd2278pre⟩

theorem clipperYankX_dogDigsExtcodesizeGuard {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel target : UInt256} {mem : ByteArray}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (h : RD code I g s0 ⟨2279⟩
      [target, ⟨0⟩, ⟨128⟩, ⟨128⟩, clipperYankArgWord I, ⟨502⟩, sel]
      mem (UInt256.ofNat 7) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨2301⟩
      (target :: target :: ⟨0⟩ :: ⟨128⟩ :: ⟨68⟩ :: ⟨128⟩ :: ⟨0⟩ ::
        ⟨196⟩ :: clipperDogDigsSelectorWord :: target :: clipperYankArgWord I ::
        ⟨502⟩ :: [sel])
      mem (UInt256.ofNat 7) ByteArray.empty (cA, σ) k' C' := by
  have rd2301 := evm_run h with [
    raw swap3 (by clipper_yank_decode) (by evm_ov),
    raw push4 clipperDogDigsSelectorWord (by clipper_yank_decode) (by evm_ov),
    raw swap3 (by clipper_yank_decode) (by evm_ov),
    raw push1 ⟨68⟩ (by clipper_yank_decode) (by evm_ov),
    raw dup1 (by clipper_yank_decode) (by evm_ov),
    raw dup4 (by clipper_yank_decode) (by evm_ov),
    raw add (by clipper_yank_decode) (by evm_ov),
    raw swap4 (by clipper_yank_decode) (by evm_ov),
    raw swap3 (by clipper_yank_decode) (by evm_ov),
    raw dup3 (by clipper_yank_decode) (by evm_ov),
    raw swap1 (by clipper_yank_decode) (by evm_ov),
    raw sub (by clipper_yank_decode) (by evm_ov),
    raw add (by clipper_yank_decode) (by evm_ov),
    raw dup2 (by clipper_yank_decode) (by evm_ov),
    raw dup4 (by clipper_yank_decode) (by evm_ov),
    raw dup8 (by clipper_yank_decode) (by evm_ov),
    raw dup1 (by clipper_yank_decode) (by evm_ov)]
  rw [show (⟨128⟩ : UInt256) + ⟨68⟩ = ⟨196⟩ from by native_decide] at rd2301
  rw [show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ = ⟨0⟩ from by native_decide] at rd2301
  rw [show (⟨0⟩ : UInt256) + ⟨68⟩ = ⟨68⟩ from by native_decide] at rd2301
  exact ⟨_, _, by simpa using rd2301⟩

theorem clipperYankX_dogDigsNoCode {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel target tab : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (rd2301 : RD code I g s0 ⟨2301⟩
      (target :: target :: ⟨0⟩ :: ⟨128⟩ :: ⟨68⟩ :: ⟨128⟩ :: ⟨0⟩ ::
        ⟨196⟩ :: clipperDogDigsSelectorWord :: target :: clipperYankArgWord I ::
        ⟨502⟩ :: [sel])
      (clipperDogDigsCalldataMem v tab (clipperYankSalesHashMemRefresh I))
      (UInt256.ofNat 7) ByteArray.empty (cA, σ) k C)
    (hcodeSizeDog : Reasoning.Theory.extCodeSizeWord σ target = ⟨0⟩) :
    RDrev code g s0 := by
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨2301⟩) (okPc := ⟨2313⟩)
    rd2301 hcodeSizeDog
    (by clipper_yank_decode) (by clipper_yank_decode) (by clipper_yank_decode)
    (by clipper_yank_decode) (by clipper_yank_decode) (by clipper_yank_decode)
    (by clipper_yank_decode) (by clipper_yank_decode) (by clipper_yank_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem clipperYankX_dogDigsPostCall {cA gh bl σ₀ σStart σ I}
    {g : Sat256} {A : Substate} {k C : ℕ} {sel target tab : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (rd2301 : RD code I g (initState cA gh bl σStart σ₀ g A I) ⟨2301⟩
      (target :: target :: ⟨0⟩ :: ⟨128⟩ :: ⟨68⟩ :: ⟨128⟩ :: ⟨0⟩ ::
        ⟨196⟩ :: clipperDogDigsSelectorWord :: target :: clipperYankArgWord I ::
        ⟨502⟩ :: [sel])
      (clipperDogDigsCalldataMem v tab (clipperYankSalesHashMemRefresh I))
      (UInt256.ofNat 7) ByteArray.empty (cA, σ) k C)
    (hcodeSizeDog : Reasoning.Theory.extCodeSizeWord σ target ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true) :
    ∃ (cA_dog : Batteries.RBSet AccountAddress compare) (σ_dog : AccountMap)
      (zDog : Bool) (outDog : ByteArray) (A_dog : Substate) (k' C' : ℕ),
      RD code I g (initState cA gh bl σStart σ₀ g A I) ⟨2317⟩
        ((if zDog then ⟨1⟩ else ⟨0⟩) :: ⟨196⟩ :: clipperDogDigsSelectorWord ::
          target :: clipperYankArgWord I :: ⟨502⟩ :: [sel])
        (outDog.write 0
          (clipperDogDigsCalldataMem v tab (clipperYankSalesHashMemRefresh I))
          128 (min (⟨0⟩ : UInt256) (UInt256.ofNat outDog.size)).toNat)
        (UInt256.ofNat
          (MachineState.M (MachineState.M (UInt256.ofNat 7).toNat
            (⟨128⟩ : UInt256).toNat (⟨68⟩ : UInt256).toNat)
            (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat))
        outDog (cA_dog, σ_dog) k' C' ∧
      typedCallViaEVM (config v)
        { initState cA gh bl σStart σ₀ g A I with accountMap := σ }
        (EVM.address (AccountAddress.ofUInt256 target)) "digs" 0
        [v.ilk, .int (Int.ofNat tab.toNat)]
        (zDog,
          { initState cA gh bl σStart σ₀ g A I with
            accountMap := σ_dog
            substate := A_dog
            createdAccounts := cA_dog },
          outDog) true ∧
      outDog.size < UInt256.size := by
  obtain ⟨_, _, _, rd2316⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨2301⟩) (okPc := ⟨2313⟩)
      rd2301 hcodeSizeDog
      (by clipper_yank_decode) (by clipper_yank_decode)
      (by clipper_yank_decode) (by clipper_yank_decode)
      (by clipper_yank_decode) (by clipper_yank_decode)
      (clipperYankJumpDest2313 v hpatch)
      (by clipper_yank_decode) (by clipper_yank_decode)
      (by clipper_yank_decode)
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨cA_dog, σ_dog, zDog, outDog, A_in, callGas, k2317, C2317, hΘpack,
      rd2317raw, houtDogSize⟩ :=
    RD.call rd2316 (by clipper_yank_decode) hdepth (by evm_ov)
  obtain ⟨g'', A_dog, hΘ⟩ := hΘpack
  refine ⟨cA_dog, σ_dog, zDog, outDog, A_dog, k2317, C2317, ?_, ?_,
    houtDogSize⟩
  · exact rd2317raw
  · let evmDog : EVM.State :=
      { initState cA gh bl σStart σ₀ g A I with accountMap := σ }
    refine callCoincides (cfg := config v)
      (evm := evmDog)
      (name := "digs") (args := [v.ilk, .int (Int.ofNat tab.toNat)])
      (tgt := EVM.address (AccountAddress.ofUInt256 target))
      (targetWord := target)
      (cA' := cA_dog) (σ' := σ_dog) (A' := A_dog) (A_in := A_in)
      (z := zDog) (o := outDog) (g'' := g'') (callGas := callGas)
      (mem := clipperDogDigsCalldataMem v tab (clipperYankSalesHashMemRefresh I))
      (inOff := ⟨128⟩) (inSize := ⟨68⟩) (callPerm := true)
      (fun h => absurd hdepth (by
        have hI : I.depth = (1024 : Fin 1025) := by
          simpa [evmDog, initState] using h
        rw [hI]
        decide))
      ?_ (by
        simpa [clipperYankSalesHashMemRefresh_size I] using
          clipperDogDigsEncode_eq v tab (clipperYankSalesHashMemRefresh_size I)) ?_
    · apply Fin.ext
      simp [EVM.address, EVM.uintN]
      exact Nat.mod_eq_of_lt (by simp [EVM.twoPow, AccountAddress.size])
    · simpa [evmDog, initState, hperm] using hΘ

theorem RD.clipperYankDogDigsCallFailure
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {rest : List UInt256}
    (rd : RD code ee g s0 ⟨2317⟩ (⟨0⟩ :: rest) mem aw o acc k C)
    (hosz : o.size < UInt256.size)
    (hov : rest.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨2317⟩) (okPc := ⟨2333⟩)
    rd (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by clipper_yank_decode) (by clipper_yank_decode)
    (by clipper_yank_decode) (by clipper_yank_decode)
    (by clipper_yank_decode) (by clipper_yank_decode)
    (by clipper_yank_decode) (by clipper_yank_decode)
    (by clipper_yank_decode) (by clipper_yank_decode)
    (by clipper_yank_decode) (by clipper_yank_decode)
    hosz hov

set_option maxHeartbeats 1000000 in
theorem RD.clipperYankDogDigsCallDepthLimit
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σStart σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {sel target tab : UInt256}
    (rd2301 : RD code I g (initState cA gh bl σStart σ₀ g A I) ⟨2301⟩
      (target :: target :: ⟨0⟩ :: ⟨128⟩ :: ⟨68⟩ :: ⟨128⟩ :: ⟨0⟩ ::
        ⟨196⟩ :: clipperDogDigsSelectorWord :: target :: clipperYankArgWord I ::
        ⟨502⟩ :: [sel])
      (clipperDogDigsCalldataMem v tab (clipperYankSalesHashMemRefresh I))
      (UInt256.ofNat 7) ByteArray.empty (cA, σ) k C)
    (hcodeSizeDog : Reasoning.Theory.extCodeSizeWord σ target ≠ ⟨0⟩)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD code I g (initState cA gh bl σStart σ₀ g A I) ⟨2317⟩
      (⟨0⟩ :: ⟨196⟩ :: clipperDogDigsSelectorWord :: target ::
        clipperYankArgWord I :: ⟨502⟩ :: [sel])
      (clipperDogDigsCalldataMem v tab (clipperYankSalesHashMemRefresh I))
      (UInt256.ofNat 7) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, _, rd2316⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨2301⟩) (okPc := ⟨2313⟩)
      rd2301 hcodeSizeDog
      (by clipper_yank_decode) (by clipper_yank_decode)
      (by clipper_yank_decode) (by clipper_yank_decode)
      (by clipper_yank_decode) (by clipper_yank_decode)
      (clipperYankJumpDest2313 v hpatch)
      (by clipper_yank_decode) (by clipper_yank_decode)
      (by clipper_yank_decode)
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨k2317, C2317, rd2317raw⟩ :=
    RD.callDepthLimit rd2316 (by clipper_yank_decode) hdepth (by evm_ov)
  refine ⟨k2317, C2317, ?_⟩
  have hmin :
      (min (⟨0⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw :
      UInt256.ofNat
        (MachineState.M (MachineState.M (UInt256.ofNat 7).toNat
          (⟨128⟩ : UInt256).toNat (⟨68⟩ : UInt256).toNat)
          (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) =
        UInt256.ofNat 7 := by
    native_decide
  simpa [hmin, byteArray_write_len_zero, haw] using rd2317raw

theorem RD.clipperYankDogDigsCallSuccessToFluxSetup
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {sel target : UInt256}
    (rd : RD code ee g s0 ⟨2317⟩
      (⟨1⟩ :: ⟨196⟩ :: clipperDogDigsSelectorWord :: target ::
        clipperYankArgWord ee :: ⟨502⟩ :: [sel])
      mem aw o acc k C) :
    ∃ k' C', RD code ee g s0 ⟨2335⟩
      (⟨196⟩ :: clipperDogDigsSelectorWord :: target ::
        clipperYankArgWord ee :: ⟨502⟩ :: [sel])
      mem aw o acc k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨2317⟩) (okPc := ⟨2333⟩) rd
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by clipper_yank_decode) (by clipper_yank_decode)
    (by clipper_yank_decode) (by clipper_yank_decode)
    (by clipper_yank_decode) (clipperYankJumpDest2333 v hpatch)
    (by clipper_yank_decode) (by clipper_yank_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)

abbrev clipperYankNotRunningAuctionWord : UInt256 :=
  ⟨0x436c69707065722f6e6f742d72756e6e696e672d61756374696f6e0000000000⟩

set_option maxHeartbeats 1000000 in
theorem clipperYankX_inactiveAuctionTail {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (h : RD code I g s0 ⟨2108⟩ [clipperYankArgWord I, ⟨502⟩, sel]
      (clipperYankSalesHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g s0 := by
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ (by clipper_yank_decode) (by evm_ov),
    raw dup1 (by clipper_yank_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by clipper_yank_decode)
      mem_cost
      (mloadFreePtrValue (by rw [clipperYankSalesHashMem_size I]; decide)
        (by decide) (clipperYankSalesHashMem_read64 I))
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by clipper_yank_decode)
    (by evm_ov)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ (by clipper_yank_decode) (by evm_ov),
    raw shl (by clipper_yank_decode) (by evm_ov),
    raw dup2 (by clipper_yank_decode) (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 (clipperYankSalesHashMem I))
      (UInt256.ofNat 5) (by clipper_yank_decode) mem_cost (by rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_yank_decode) (by evm_ov),
    raw push1 ⟨4⟩ (by clipper_yank_decode) (by evm_ov),
    raw dup3 (by clipper_yank_decode) (by evm_ov),
    raw add (by clipper_yank_decode) (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 (clipperYankSalesHashMem I))
      (UInt256.ofNat 6) (by clipper_yank_decode) mem_cost (by rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨27⟩ (by clipper_yank_decode) (by evm_ov),
    raw push1 ⟨36⟩ (by clipper_yank_decode) (by evm_ov),
    raw dup3 (by clipper_yank_decode) (by evm_ov),
    raw add (by clipper_yank_decode) (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 ⟨27⟩ (clipperYankSalesHashMem I))
      (UInt256.ofNat 7) (by clipper_yank_decode) mem_cost (by rfl)
      (by decide) (by evm_ov)]
  have rdWord := rdPrefix.pushConst clipperYankNotRunningAuctionWord
    (width := 32) (op := .PUSH32) (by decide) (by clipper_yank_decode)
    (by evm_ov)
  exact evm_run rdWord with [
    raw push1 ⟨68⟩ (by clipper_yank_decode) (by evm_ov),
    raw dup3 (by clipper_yank_decode) (by evm_ov),
    raw add (by clipper_yank_decode) (by evm_ov),
    raw mstore 3
      (solcErrorStringMem3 ⟨27⟩ clipperYankNotRunningAuctionWord
        (clipperYankSalesHashMem I))
      (UInt256.ofNat 8) (by clipper_yank_decode) mem_cost (by rfl)
      (by decide) (by evm_ov),
    raw swap1 (by clipper_yank_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by clipper_yank_decode)
      mem_cost
      (solcErrorStringMem3_mload64 ⟨27⟩ clipperYankNotRunningAuctionWord
        (clipperYankSalesHashMem_size I) (clipperYankSalesHashMem_read64 I))
      (by decide) (by evm_ov),
    raw swap1 (by clipper_yank_decode) (by evm_ov),
    raw dup2 (by clipper_yank_decode) (by evm_ov),
    raw swap1 (by clipper_yank_decode) (by evm_ov),
    raw sub (by clipper_yank_decode) (by evm_ov),
    raw push1 ⟨100⟩ (by clipper_yank_decode) (by evm_ov),
    raw add (by clipper_yank_decode) (by evm_ov),
    raw swap1 (by clipper_yank_decode) (by evm_ov),
    raw rev 0 (by clipper_yank_decode) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem clipperYankX_usrZero {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (husr : clipperYankSalesUsrWord σ I = ⟨0⟩)
    (h : RD code I g s0 ⟨2077⟩
      [clipperYankArgWord I, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g s0 := by
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC
            ((clipperYankSalesHashMem I).readWithPadding 0 64))) =
        clipperYankSalesBaseSlot I := by
    rw [clipperYankSalesHashMem, clipperYankSalesBaseSlot_eq I]
    exact twoWordHashMem_solcMappingSlot ⟨12⟩ (clipperYankArgWord I)
      (clipperRelyAuthHashMem_size I)
  have rd2081pre := evm_run h with [
    raw push1 ⟨0⟩ (by clipper_yank_decode) (by evm_ov),
    raw dup2 (by clipper_yank_decode) (by evm_ov),
    raw dup2 (by clipper_yank_decode) (by evm_ov)]
  have rd2082 := rd2081pre.mstore 0
    (wordAt0Mem (clipperYankArgWord I) (clipperRelyAuthHashMem I))
    (UInt256.ofNat 3) (by clipper_yank_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd2086pre := evm_run rd2082 with [
    raw push1 ⟨12⟩ (by clipper_yank_decode) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_yank_decode) (by evm_ov)]
  have rd2087 := rd2086pre.mstore 0 (clipperYankSalesHashMem I)
    (UInt256.ofNat 3) (by clipper_yank_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd2090pre := evm_run rd2087 with [
    raw push1 ⟨64⟩ (by clipper_yank_decode) (by evm_ov),
    raw swap1 (by clipper_yank_decode) (by evm_ov)]
  have rd2091 := rd2090pre.keccak256 0 (clipperYankSalesBaseSlot I)
    (UInt256.ofNat 3) (by clipper_yank_decode) mem_cost hslot (by native_decide)
    (by evm_ov)
  have rd2094pre := evm_run rd2091 with [
    raw push1 ⟨3⟩ (by clipper_yank_decode) (by evm_ov),
    raw add (by clipper_yank_decode) (by evm_ov)]
  rw [u256_add_comm ⟨3⟩ (clipperYankSalesBaseSlot I)] at rd2094pre
  obtain ⟨k2095, C2095, rd2095raw⟩ := rd2094pre.sload
    (by clipper_yank_decode) (by evm_ov)
  have rd2095 : RD code I g s0 ⟨2095⟩
      (solcSlotWord σ I (clipperYankSalesUsrSlot I) :: clipperYankArgWord I ::
        ⟨502⟩ :: [sel])
      (clipperYankSalesHashMem I)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2095 C2095 := by
    simpa [clipperYankSalesUsrSlot, solcSlotWord, clipperYankSalesHashMem] using rd2095raw
  have rd2104pre := evm_run rd2095 with [
    raw push1 ⟨1⟩ (by clipper_yank_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_yank_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_yank_decode) (by evm_ov),
    raw shl (by clipper_yank_decode) (by evm_ov),
    raw sub (by clipper_yank_decode) (by evm_ov),
    raw and (by clipper_yank_decode) (by evm_ov)]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
    solcAddrMask from by native_decide] at rd2104pre
  have rd2107 := rd2104pre.pushConst (⟨2184⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_yank_decode) (by evm_ov)
  have husrStack :
      UInt256.land solcAddrMask (solcSlotWord σ I (clipperYankSalesUsrSlot I)) = ⟨0⟩ := by
    simpa [clipperYankSalesUsrWord, u256_land_comm] using husr
  have rd2108 := rd2107.jumpiNT (by clipper_yank_decode) husrStack (by evm_ov)
  exact clipperYankX_inactiveAuctionTail (v := v) hpatch rd2108

theorem clipperYankLockRevertTailWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcErrorStringRevertTailWf code (⟨2003⟩ : UInt256) ⟨21⟩
      ⟨24634883019371952566956220926897864252907853633881⟩ ⟨90⟩ .PUSH21 21 := by
  unfold solcErrorStringRevertTailWf
  dsimp
  refine
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩ <;> (norm_num1; clipper_yank_decode)

theorem clipperYankLockedStringWord :
    UInt256.shiftLeft ⟨24634883019371952566956220926897864252907853633881⟩ ⟨90⟩ =
      ⟨30496508052792062404420069455133111715513420844312188351800969105462834233344⟩ := by
  native_decide

set_option maxHeartbeats 1000000 in
theorem clipperYankX_locked {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hlocked : solcSlotWord σ I ⟨13⟩ ≠ ⟨0⟩)
    (h : RD code I g s0 ⟨1994⟩
      [clipperYankArgWord I, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g s0 := by
  have rd1997pre := evm_run h with [
    raw jumpdest (by clipper_yank_decode) (by evm_ov),
    raw push1 ⟨13⟩ (by clipper_yank_decode) (by evm_ov)]
  obtain ⟨k1998, C1998, rd1998raw⟩ := rd1997pre.sload
    (by clipper_yank_decode) (by evm_ov)
  have rd1998 : RD code I g s0 ⟨1998⟩
      (solcSlotWord σ I ⟨13⟩ :: clipperYankArgWord I :: ⟨502⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1998 C1998 := by
    simpa [solcSlotWord] using rd1998raw
  have rd1999pre := rd1998.iszero (by clipper_yank_decode) (by evm_ov)
  rw [isZero_eq_zero_of_ne hlocked] at rd1999pre
  have rd2002 := rd1999pre.pushConst (⟨2071⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_yank_decode) (by evm_ov)
  have rd2003 := rd2002.jumpiNT (by clipper_yank_decode)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcErrorStringRevertTail rd2003
    (clipperYankLockRevertTailWf v hpatch)
    (by decide)
    clipperYankLockedStringWord
    (clipperRelyAuthHashMem_size I)
    (clipperRelyAuthHashMem_read64 I)
    (by simp)

end Benchmarks.Dss.Clipper
