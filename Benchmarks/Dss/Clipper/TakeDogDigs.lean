import Benchmarks.Dss.Clipper.TakeVatMoveSource
import Benchmarks.Dss.Clipper.YankEVM
import Benchmarks.Dss.Clipper.YankVatEVM

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

theorem clipperTakeDogDigsSelectorMem_size {mem : ByteArray}
    (hmem : mem.size = 260) :
    (clipperDogDigsSelectorMem mem).size = 260 := by
  unfold clipperDogDigsSelectorMem
  exact toByteArray_write32_size_of_le mem clipperDogDigsSelectorShifted 128 260 260
    hmem (by omega) (by omega)

theorem clipperTakeDogDigsIlkMem_size (v : ClipperImmutables) {mem : ByteArray}
    (hmem : mem.size = 260) :
    (clipperDogDigsIlkMem v mem).size = 260 := by
  unfold clipperDogDigsIlkMem
  exact toByteArray_write32_size_of_le (clipperDogDigsSelectorMem mem)
    (clipperYankIlkWord v) 132 260 260
    (clipperTakeDogDigsSelectorMem_size hmem)
    (by rw [clipperTakeDogDigsSelectorMem_size hmem]; omega) (by omega)

theorem clipperTakeDogDigsCalldataMem_size (v : ClipperImmutables) (tab : UInt256)
    {mem : ByteArray} (hmem : mem.size = 260) :
    (clipperDogDigsCalldataMem v tab mem).size = 260 := by
  unfold clipperDogDigsCalldataMem
  exact toByteArray_write32_size_of_le (clipperDogDigsIlkMem v mem) tab 164 260 260
    (clipperTakeDogDigsIlkMem_size v hmem)
    (by rw [clipperTakeDogDigsIlkMem_size v hmem]; omega) (by omega)

theorem clipperTakeDogDigsCalldataMem_read64 (v : ClipperImmutables)
    (tab : UInt256) {mem : ByteArray} (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperDogDigsCalldataMem v tab mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperDogDigsCalldataMem
  rw [toByteArray_write_read_below_of_gap tab _ 164 64
      (by rw [clipperTakeDogDigsIlkMem_size v hmem]; omega) (by omega)
      (by rw [clipperTakeDogDigsIlkMem_size v hmem]; native_decide)]
  unfold clipperDogDigsIlkMem
  rw [toByteArray_write_read_below_of_gap (clipperYankIlkWord v) _ 132 64
      (by rw [clipperTakeDogDigsSelectorMem_size hmem]; omega) (by omega)
      (by rw [clipperTakeDogDigsSelectorMem_size hmem]; native_decide)]
  unfold clipperDogDigsSelectorMem
  rw [toByteArray_write_read_below_of_gap clipperDogDigsSelectorShifted _ 128 64
      (by rw [hmem]; omega) (by omega) (by rw [hmem]; native_decide)]
  exact hread64

theorem clipperTakeDogDigsCalldataMem_mload64 (v : ClipperImmutables)
    (tab : UInt256) {mem : ByteArray} (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (clipperDogDigsCalldataMem v tab mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((clipperDogDigsCalldataMem v tab mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ := by
  exact mloadFreePtrValue
    (mem := clipperDogDigsCalldataMem v tab mem) (aw := UInt256.ofNat 9)
    (by rw [clipperTakeDogDigsCalldataMem_size v tab hmem]; norm_num)
    (by decide)
    (clipperTakeDogDigsCalldataMem_read64 v tab hmem hread64)

theorem clipperTakeDogDigsSelectorMem_read128_4 {mem : ByteArray}
    (hmem : mem.size = 260) :
    (clipperDogDigsSelectorMem mem).readWithPadding 128 4 = dogDigsSelector := by
  unfold clipperDogDigsSelectorMem
  rw [toByteArray_write_read_window_of_gap clipperDogDigsSelectorShifted mem 128 0 4
    (by norm_num) (by norm_num) (by norm_num) (by rw [hmem]; native_decide)]
  rw [toByteArray_eq_toBytesBE]
  native_decide

theorem clipperTakeDogDigsCalldataMem_read128_4 (v : ClipperImmutables)
    (tab : UInt256) {mem : ByteArray} (hmem : mem.size = 260) :
    (clipperDogDigsCalldataMem v tab mem).readWithPadding 128 4 =
      dogDigsSelector := by
  unfold clipperDogDigsCalldataMem
  rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
    (by rw [clipperTakeDogDigsIlkMem_size v hmem]; native_decide)
    (by omega) (by rw [clipperTakeDogDigsIlkMem_size v hmem]; native_decide)
    (by norm_num) (by norm_num)]
  unfold clipperDogDigsIlkMem
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by rw [clipperTakeDogDigsSelectorMem_size hmem]; omega)
    (by omega) (by rw [clipperTakeDogDigsSelectorMem_size hmem]; omega)
    (by norm_num) (by norm_num)]
  exact clipperTakeDogDigsSelectorMem_read128_4 hmem

theorem clipperTakeDogDigsCalldataMem_read132_32 (v : ClipperImmutables)
    (tab : UInt256) {mem : ByteArray} (hmem : mem.size = 260) :
    (clipperDogDigsCalldataMem v tab mem).readWithPadding 132 32 =
      UInt256.toByteArray (clipperYankIlkWord v) := by
  unfold clipperDogDigsCalldataMem
  rw [write32_read_below _ _ 164 132 (by rw [toByteArray_size])
    (by rw [clipperTakeDogDigsIlkMem_size v hmem]; native_decide) (by omega)]
  unfold clipperDogDigsIlkMem
  rw [write32_read_back _ _ 132 (by rw [toByteArray_size])
    (by rw [clipperTakeDogDigsSelectorMem_size hmem]; omega)]
  rw [show (UInt256.toByteArray (clipperYankIlkWord v)).extract 0 32 =
      UInt256.toByteArray (clipperYankIlkWord v) by
    rw [show 32 = (UInt256.toByteArray (clipperYankIlkWord v)).size by
      rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem clipperTakeDogDigsCalldataMem_read164_32 (v : ClipperImmutables)
    (tab : UInt256) {mem : ByteArray} (hmem : mem.size = 260) :
    (clipperDogDigsCalldataMem v tab mem).readWithPadding 164 32 =
      UInt256.toByteArray tab := by
  unfold clipperDogDigsCalldataMem
  rw [write32_read_back _ _ 164 (by rw [toByteArray_size])
    (by rw [clipperTakeDogDigsIlkMem_size v hmem]; native_decide)]
  rw [show (UInt256.toByteArray tab).extract 0 32 = UInt256.toByteArray tab by
    rw [show 32 = (UInt256.toByteArray tab).size by rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem clipperTakeDogDigsCalldataMem_read128_68 (v : ClipperImmutables)
    (tab : UInt256) {mem : ByteArray} (hmem : mem.size = 260) :
    (clipperDogDigsCalldataMem v tab mem).readWithPadding 128 68 =
      dogDigsSelector ++ UInt256.toByteArray (clipperYankIlkWord v) ++
        UInt256.toByteArray tab := by
  rw [byteArray_readWithPadding_split _ 128 4 64 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [clipperTakeDogDigsCalldataMem_size v tab hmem]; native_decide)]
  rw [byteArray_readWithPadding_split _ 132 32 32 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [clipperTakeDogDigsCalldataMem_size v tab hmem]; native_decide)]
  rw [clipperTakeDogDigsCalldataMem_read128_4 v tab hmem,
    clipperTakeDogDigsCalldataMem_read132_32 v tab hmem,
    clipperTakeDogDigsCalldataMem_read164_32 v tab hmem, ByteArray.append_assoc]

theorem clipperTakeDogDigsEncode_eq (v : ClipperImmutables) (tab : UInt256)
    {mem : ByteArray} (hmem : mem.size = 260) :
    (config v).externalABI.encode? "digs" [v.ilk, .int (Int.ofNat tab.toNat)] =
      some ((clipperDogDigsCalldataMem v tab mem).readWithPadding 128 68) := by
  rcases v.ilk_wf with ⟨bs, hilk, hlen⟩
  rw [hilk]
  have hilkWord :
      clipperYankIlkWord v = EVM.Word.ofNat (fromBytesBigEndian bs) := by
    simp [clipperYankIlkWord, hilk]
  rw [clipperTakeDogDigsCalldataMem_read128_68 v tab hmem, hilkWord]
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

theorem clipperTakeJumpDest4915 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨4915⟩ : UInt256) = true := by
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

theorem clipperTakeJumpDest4911 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨4911⟩ : UInt256) = true := by
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

theorem clipperTakeJumpDest4976 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨4976⟩ : UInt256) = true := by
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

theorem clipperTakeJumpDest4996 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨4996⟩ : UInt256) = true := by
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

theorem clipperTakeJumpDest5020 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨5020⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 6000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperTakeJumpDest5025 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨5025⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 6000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperTakeJumpDest5222 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨5222⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 6000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperTakeJumpDest5250 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨5250⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 6000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperTakeIlkPatchPayload4866 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {bs : List UInt8} (hilk : v.ilk = .fixedBytes ⟨31, by decide⟩ bs)
    (hlen : bs.length = 32) :
    code.extract' 4866 4898 =
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
      PatchesWindowDisjoint32 4866 4898
        [(5046, ilkBytes), (6800, ilkBytes), (8747, ilkBytes),
          (1463, vatBytes), (2437, vatBytes), (3145, vatBytes), (4318, vatBytes),
          (4441, vatBytes), (4751, vatBytes), (5115, vatBytes), (6295, vatBytes),
          (7936, vatBytes)] := by
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | hfalse
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
    (pre :=
      [(1510, ilkBytes), (1661, ilkBytes), (2221, ilkBytes), (2369, ilkBytes),
        (4239, ilkBytes)])
    (post :=
      [(5046, ilkBytes), (6800, ilkBytes), (8747, ilkBytes),
        (1463, vatBytes), (2437, vatBytes), (3145, vatBytes), (4318, vatBytes),
        (4441, vatBytes), (4751, vatBytes), (5115, vatBytes), (6295, vatBytes),
        (7936, vatBytes)])
    (off := 4866) (value := ilkBytes)
    (by
      simpa [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, hilk,
        hlen, List.lookup_cons, ilkBytes, vatBytes] using hpatch)
    hsize hpost (by norm_num) (by norm_num)

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem clipperTakeIlkPush32Decode4865 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {bs : List UInt8} (hilk : v.ilk = .fixedBytes ⟨31, by decide⟩ bs)
    (hlen : bs.length = 32) :
    decode code (⟨4865⟩ : UInt256) =
      some (.Push .PUSH32, some (EVM.Word.ofNat (fromBytesBigEndian bs), 32)) := by
  unfold decode
  rw [patchRuntime_get?_disjoint hpatch
    (clipperRuntimePatchesWindowDisjoint32Bool v (⟨4865⟩ : UInt256).toNat
      ((⟨4865⟩ : UInt256).toNat + 1) (by native_decide))]
  norm_num
  change some (Operation.Push Operation.POp.PUSH32,
      some (uInt256OfByteArray (code.extract' 4866 4898), 32)) =
    some (Operation.Push Operation.POp.PUSH32,
      some (EVM.Word.ofNat (fromBytesBigEndian bs), 32))
  rw [clipperTakeIlkPatchPayload4866 v hpatch hilk hlen]
  rw [uInt256OfByteArray_word_toBytesBE]

set_option maxHeartbeats 1000000 in
theorem RD.clipperTakeDogDigsOweCallSetupNonzero {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {dog slice owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id :
      UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (rd4850 : RD code ee g s0 ⟨4850⟩
      (dog :: slice :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped ::
        dataLen :: dataStart :: who :: max :: amt :: id :: R)
      mem (UInt256.ofNat 9) rdata (cA, σ) k C)
    (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlotNew : lotNew ≠ ⟨0⟩)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨4964⟩
      (UInt256.land solcAddrMask dog :: UInt256.land solcAddrMask dog :: ⟨0⟩ ::
        ⟨128⟩ :: ⟨68⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨196⟩ ::
        clipperDogDigsSelectorWord :: UInt256.land solcAddrMask dog ::
        dog :: slice :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped ::
        dataLen :: dataStart :: who :: max :: amt :: id :: R)
      (clipperDogDigsCalldataMem v owe mem)
      (UInt256.ofNat 9) rdata (cA, σ) k' C' := by
  rcases v.ilk_wf with ⟨ilkBs, hilk, hlen⟩
  let ilkWord : UInt256 := EVM.Word.ofNat (fromBytesBigEndian ilkBs)
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (mem := mem) (aw := UInt256.ofNat 9)
      (by rw [hmem]; norm_num) (by native_decide) hread64
  have hcallMload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (clipperDogDigsCalldataMem v owe mem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((clipperDogDigsCalldataMem v owe mem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    clipperTakeDogDigsCalldataMem_mload64 v owe hmem hread64
  have rd4860pre := evm_run rd4850 with [
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov)]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
    solcAddrMask from by native_decide] at rd4860pre
  have rd4865 := evm_run rd4860pre with [
    raw push4 clipperDogDigsSelectorWord (by clipper_runtime_decode) (by evm_ov)]
  have rd4898 := rd4865.pushConst ilkWord (width := 32) (op := .PUSH32)
    (by decide)
    (by simpa [ilkWord] using clipperTakeIlkPush32Decode4865 v hpatch hilk hlen)
    (by evm_ov)
  have rd4905pre := evm_run rd4898 with [
    raw dup8 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw eq (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4911⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd4906 := rd4905pre.jumpiNT (by clipper_runtime_decode)
    (u256_eq_of_ne (by intro h; exact hlotNew h.symm)) (by evm_ov)
  have rd4910pre := evm_run rd4906 with [
    raw dup6 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4915⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd4915 := rd4910pre.jump (by clipper_runtime_decode)
    (clipperTakeJumpDest4915 v hpatch) (by evm_ov)
  have rd4919pre := evm_run rd4915 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd4919 := rd4919pre.mload 0 ⟨128⟩ (UInt256.ofNat 9)
    (by clipper_runtime_decode) mem_cost hmload64 (by native_decide) (by evm_ov)
  have rd4930pre := evm_run rd4919 with [
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw push4 ⟨4294967295⟩ (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨224⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  rw [show UInt256.shiftLeft (UInt256.land ⟨4294967295⟩ clipperDogDigsSelectorWord)
      ⟨224⟩ = clipperDogDigsSelectorShifted from by native_decide] at rd4930pre
  have rd4930 := rd4930pre.mstore 0
    (clipperDogDigsSelectorMem mem)
    (UInt256.ofNat 9) (by clipper_runtime_decode) mem_cost (by rfl)
    (by native_decide) (by evm_ov)
  have rd4937pre := evm_run rd4930 with [
    raw push1 ⟨4⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨4⟩ : UInt256) + ⟨128⟩ = ⟨132⟩ from by native_decide] at rd4937pre
  have rd4937 := rd4937pre.mstore 0
    (clipperDogDigsIlkMem v mem)
    (UInt256.ofNat 9) (by clipper_runtime_decode) mem_cost
    (by
      rw [show (⟨132⟩ : UInt256).toNat = 132 from by decide]
      simp [clipperDogDigsIlkMem, clipperYankIlkWord, hilk, ilkWord])
    (by native_decide) (by evm_ov)
  have rd4943pre := evm_run rd4937 with [
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨32⟩ : UInt256) + ⟨132⟩ = ⟨164⟩ from by native_decide] at rd4943pre
  have rd4943 := rd4943pre.mstore 0
    (clipperDogDigsCalldataMem v owe mem)
    (UInt256.ofNat 9) (by clipper_runtime_decode) mem_cost (by rfl)
    (by native_decide) (by evm_ov)
  have rd4955pre := evm_run rd4943 with [
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨32⟩ : UInt256) + ⟨164⟩ = ⟨196⟩ from by native_decide] at rd4955pre
  have rd4955 := rd4955pre.mload 0 ⟨128⟩ (UInt256.ofNat 9)
    (by clipper_runtime_decode) mem_cost hcallMload64 (by native_decide) (by evm_ov)
  have rd4964 := evm_run rd4955 with [
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup8 (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov)]
  rw [show UInt256.sub (⟨196⟩ : UInt256) ⟨128⟩ = ⟨68⟩ from by native_decide]
    at rd4964
  exact ⟨_, _, by simpa [u256_land_comm] using rd4964⟩

set_option maxHeartbeats 1000000 in
theorem RD.clipperTakeDogDigsOweCallSetupZero {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {dog slice owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id :
      UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (rd4850 : RD code ee g s0 ⟨4850⟩
      (dog :: slice :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped ::
        dataLen :: dataStart :: who :: max :: amt :: id :: R)
      mem (UInt256.ofNat 9) rdata (cA, σ) k C)
    (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlotNew : lotNew = ⟨0⟩) (htabNew : tabNew = ⟨0⟩)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨4964⟩
      (UInt256.land solcAddrMask dog :: UInt256.land solcAddrMask dog :: ⟨0⟩ ::
        ⟨128⟩ :: ⟨68⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨196⟩ ::
        clipperDogDigsSelectorWord :: UInt256.land solcAddrMask dog ::
        dog :: slice :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped ::
        dataLen :: dataStart :: who :: max :: amt :: id :: R)
      (clipperDogDigsCalldataMem v owe mem)
      (UInt256.ofNat 9) rdata (cA, σ) k' C' := by
  rcases v.ilk_wf with ⟨ilkBs, hilk, hlen⟩
  let ilkWord : UInt256 := EVM.Word.ofNat (fromBytesBigEndian ilkBs)
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (mem := mem) (aw := UInt256.ofNat 9)
      (by rw [hmem]; norm_num) (by native_decide) hread64
  have hcallMload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (clipperDogDigsCalldataMem v owe mem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((clipperDogDigsCalldataMem v owe mem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    clipperTakeDogDigsCalldataMem_mload64 v owe hmem hread64
  have rd4860pre := evm_run rd4850 with [
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov)]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
    solcAddrMask from by native_decide] at rd4860pre
  have rd4865 := evm_run rd4860pre with [
    raw push4 clipperDogDigsSelectorWord (by clipper_runtime_decode) (by evm_ov)]
  have rd4898 := rd4865.pushConst ilkWord (width := 32) (op := .PUSH32)
    (by decide)
    (by simpa [ilkWord] using clipperTakeIlkPush32Decode4865 v hpatch hilk hlen)
    (by evm_ov)
  have rd4905pre := evm_run rd4898 with [
    raw dup8 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw eq (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4911⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd4911 := rd4905pre.jumpiT (by clipper_runtime_decode)
    (by rw [hlotNew, u256_eq_refl]; decide)
    (clipperTakeJumpDest4911 v hpatch) (by evm_ov)
  have rd4915pre := evm_run rd4911 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw dup6 (by clipper_runtime_decode) (by evm_ov),
    raw dup8 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨4911⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
    (⟨4915⟩ : UInt256) from by native_decide] at rd4915pre
  rw [htabNew, u256_zero_add] at rd4915pre
  have rd4919pre := evm_run rd4915pre with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd4919 := rd4919pre.mload 0 ⟨128⟩ (UInt256.ofNat 9)
    (by clipper_runtime_decode) mem_cost hmload64 (by native_decide) (by evm_ov)
  have rd4930pre := evm_run rd4919 with [
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw push4 ⟨4294967295⟩ (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨224⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  rw [show UInt256.shiftLeft (UInt256.land ⟨4294967295⟩ clipperDogDigsSelectorWord)
      ⟨224⟩ = clipperDogDigsSelectorShifted from by native_decide] at rd4930pre
  have rd4930 := rd4930pre.mstore 0
    (clipperDogDigsSelectorMem mem)
    (UInt256.ofNat 9) (by clipper_runtime_decode) mem_cost (by rfl)
    (by native_decide) (by evm_ov)
  have rd4937pre := evm_run rd4930 with [
    raw push1 ⟨4⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨4⟩ : UInt256) + ⟨128⟩ = ⟨132⟩ from by native_decide] at rd4937pre
  have rd4937 := rd4937pre.mstore 0
    (clipperDogDigsIlkMem v mem)
    (UInt256.ofNat 9) (by clipper_runtime_decode) mem_cost
    (by
      rw [show (⟨132⟩ : UInt256).toNat = 132 from by decide]
      simp [clipperDogDigsIlkMem, clipperYankIlkWord, hilk, ilkWord])
    (by native_decide) (by evm_ov)
  have rd4943pre := evm_run rd4937 with [
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨32⟩ : UInt256) + ⟨132⟩ = ⟨164⟩ from by native_decide] at rd4943pre
  have rd4943 := rd4943pre.mstore 0
    (clipperDogDigsCalldataMem v owe mem)
    (UInt256.ofNat 9) (by clipper_runtime_decode) mem_cost (by rfl)
    (by native_decide) (by evm_ov)
  have rd4955pre := evm_run rd4943 with [
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨32⟩ : UInt256) + ⟨164⟩ = ⟨196⟩ from by native_decide] at rd4955pre
  have rd4955 := rd4955pre.mload 0 ⟨128⟩ (UInt256.ofNat 9)
    (by clipper_runtime_decode) mem_cost hcallMload64 (by native_decide) (by evm_ov)
  have rd4964 := evm_run rd4955 with [
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup8 (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov)]
  rw [show UInt256.sub (⟨196⟩ : UInt256) ⟨128⟩ = ⟨68⟩ from by native_decide]
    at rd4964
  exact ⟨_, _, by simpa [u256_land_comm, htabNew, hlotNew] using rd4964⟩

theorem RD.clipperTakeDogDigsNoCode {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {target dog slice owe tabNew lotNew price tic packed stopped dataLen dataStart who max
      amt id : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (rd4964 : RD code ee g s0 ⟨4964⟩
      (target :: target :: ⟨0⟩ :: ⟨128⟩ :: ⟨68⟩ :: ⟨128⟩ :: ⟨0⟩ ::
        ⟨196⟩ :: clipperDogDigsSelectorWord :: target :: dog :: slice :: owe ::
        tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen :: dataStart ::
        who :: max :: amt :: id :: R)
      mem (UInt256.ofNat 9) rdata (cA, σ) k C)
    (hcodeSizeDog : Reasoning.Theory.uniswapExtCodeSizeWord σ target = ⟨0⟩)
    (hov : R.length + 32 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.uniswapExtcodesizeGuardMissing (pc := ⟨4964⟩) (okPc := ⟨4976⟩)
    rd4964 hcodeSizeDog
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode)
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.clipperTakeDogDigsPostCall {cA0 cA gh bl σ₀ σStart σ I}
    {g : Sat256} {A : Substate} {k C : ℕ}
    {target dog slice owe tabNew lotNew price tic packed stopped dataLen dataStart who max
      amt id : UInt256}
    {R : List UInt256} {baseMem rdata : ByteArray} (v : ClipperImmutables)
    {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (rd4964 : RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨4964⟩
      (target :: target :: ⟨0⟩ :: ⟨128⟩ :: ⟨68⟩ :: ⟨128⟩ :: ⟨0⟩ ::
        ⟨196⟩ :: clipperDogDigsSelectorWord :: target :: dog :: slice :: owe ::
        tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen :: dataStart ::
        who :: max :: amt :: id :: R)
      (clipperDogDigsCalldataMem v owe baseMem)
      (UInt256.ofNat 9) rdata (cA, σ) k C)
    (hbaseMem : baseMem.size = 260)
    (hcodeSizeDog : Reasoning.Theory.uniswapExtCodeSizeWord σ target ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true)
    (hov : R.length + 32 ≤ 1024) :
    ∃ (cA_dog : Batteries.RBSet AccountAddress compare) (σ_dog : AccountMap)
      (zDog : Bool) (outDog : ByteArray) (A_dog : Substate) (k' C' : ℕ),
      RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨4980⟩
        ((if zDog then ⟨1⟩ else ⟨0⟩) :: ⟨196⟩ :: clipperDogDigsSelectorWord ::
          target :: dog :: slice :: owe :: tabNew :: lotNew :: price :: tic ::
          packed :: stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: R)
        (outDog.write 0 (clipperDogDigsCalldataMem v owe baseMem)
          128 (min (⟨0⟩ : UInt256) (UInt256.ofNat outDog.size)).toNat)
        (UInt256.ofNat
          (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
            (⟨128⟩ : UInt256).toNat (⟨68⟩ : UInt256).toNat)
            (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat))
        outDog (cA_dog, σ_dog) k' C' ∧
      typedCallViaEVM (config v)
        { initState cA0 gh bl σStart σ₀ g A I with
          accountMap := σ, createdAccounts := cA }
        (EVM.address (AccountAddress.ofUInt256 target)) "digs" 0
        [v.ilk, .int (Int.ofNat owe.toNat)]
        (zDog,
          { initState cA0 gh bl σStart σ₀ g A I with
            accountMap := σ_dog
            substate := A_dog
            createdAccounts := cA_dog },
          outDog) true ∧
      outDog.size < UInt256.size := by
  obtain ⟨_, _, _, rd4979⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨4964⟩) (okPc := ⟨4976⟩)
      rd4964 hcodeSizeDog
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (clipperTakeJumpDest4976 v hpatch)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode)
      (by simp only [List.length_cons]; omega)
  obtain ⟨cA_dog, σ_dog, zDog, outDog, A_in, callGas, k4980, C4980, hΘpack,
      rd4980raw, houtDogSize⟩ :=
    RD.call rd4979 (by clipper_runtime_decode) hdepth (by evm_ov)
  obtain ⟨g'', A_dog, hΘ⟩ := hΘpack
  refine ⟨cA_dog, σ_dog, zDog, outDog, A_dog, k4980, C4980, ?_, ?_,
    houtDogSize⟩
  · exact rd4980raw
  · let evmDog : EVM.State :=
      { initState cA0 gh bl σStart σ₀ g A I with accountMap := σ, createdAccounts := cA }
    refine callCoincides (cfg := config v)
      (evm := evmDog)
      (name := "digs") (args := [v.ilk, .int (Int.ofNat owe.toNat)])
      (tgt := EVM.address (AccountAddress.ofUInt256 target))
      (targetWord := target)
      (cA' := cA_dog) (σ' := σ_dog) (A' := A_dog) (A_in := A_in)
      (z := zDog) (o := outDog) (g'' := g'') (callGas := callGas)
      (mem := clipperDogDigsCalldataMem v owe baseMem)
      (inOff := ⟨128⟩) (inSize := ⟨68⟩) (callPerm := true)
      (fun h => absurd hdepth (by
        have hI : I.depth = (1024 : Fin 1025) := by
          simpa [evmDog, initState] using h
        rw [hI]
        decide))
      ?_ (by
        simpa [clipperTakeDogDigsCalldataMem_size v owe hbaseMem] using
          clipperTakeDogDigsEncode_eq v owe hbaseMem) ?_
    · apply Fin.ext
      simp [EVM.address, EVM.uintN]
      exact Nat.mod_eq_of_lt (by simp [EVM.twoPow, AccountAddress.size])
    · simpa [evmDog, initState, hperm] using hΘ

theorem RD.clipperTakeDogDigsCallFailure {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {rest : List UInt256}
    (rd : RD code ee g s0 ⟨4980⟩ (⟨0⟩ :: rest) mem aw o acc k C)
    (hosz : o.size < UInt256.size)
    (hov : rest.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.uniswapCallSuccessGuardMissing (pc := ⟨4980⟩) (okPc := ⟨4996⟩)
    rd (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    hosz hov

theorem RD.clipperTakeDogDigsCallSuccessToPostDog {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {target dog slice owe tabNew lotNew price tic packed stopped dataLen dataStart who max
      amt id : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨4980⟩
      (⟨1⟩ :: ⟨196⟩ :: clipperDogDigsSelectorWord :: target :: dog :: slice ::
        owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen ::
        dataStart :: who :: max :: amt :: id :: R)
      mem aw o acc k C)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨5003⟩
      (owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen ::
        dataStart :: who :: max :: amt :: id :: R)
      mem aw o acc k' C' := by
  obtain ⟨_, _, rd4998⟩ :=
    RD.uniswapCallSuccessGuardOk (pc := ⟨4980⟩) (okPc := ⟨4996⟩) rd
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (clipperTakeJumpDest4996 v hpatch)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by simp only [List.length_cons]; omega)
  have rd5003 := evm_run rd4998 with [
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov)]
  exact ⟨_, _, rd5003⟩

theorem RD.clipperTakePostDogLotZeroToRemove {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨5003⟩
      (owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen :: dataStart ::
        who :: max :: amt :: id :: R)
      mem aw o acc k C)
    (hlotNew : lotNew = ⟨0⟩)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8274⟩
      (id :: ⟨5020⟩ :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped ::
        dataLen :: dataStart :: who :: max :: amt :: id :: R)
      mem aw o acc k' C' := by
  have rd5011pre := evm_run rd with [
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw eq (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨5025⟩ (by clipper_runtime_decode) (by evm_ov)]
  have hcond : UInt256.isZero (UInt256.eq ⟨0⟩ lotNew) = ⟨0⟩ := by
    rw [hlotNew]
    native_decide
  have rd5012 := rd5011pre.jumpiNT (by clipper_runtime_decode) hcond (by evm_ov)
  have rd5019pre := evm_run rd5012 with [
    raw push2 ⟨5020⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup14 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8274⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd8274 := rd5019pre.jump (by clipper_runtime_decode)
    (clipperYankJumpDest8274 v hpatch) (by evm_ov)
  exact ⟨_, _, rd8274⟩

theorem RD.clipperTakePostDogLotNonzeroToCallbackGuard {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨5003⟩
      (owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen :: dataStart ::
        who :: max :: amt :: id :: R)
      mem aw o acc k C)
    (hlotNew : lotNew ≠ ⟨0⟩)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨5025⟩
      (owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen :: dataStart ::
        who :: max :: amt :: id :: R)
      mem aw o acc k' C' := by
  have rd5011pre := evm_run rd with [
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw eq (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨5025⟩ (by clipper_runtime_decode) (by evm_ov)]
  have heqZero : UInt256.eq (⟨0⟩ : UInt256) lotNew = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro h; exact hlotNew h.symm)
  have hcond : UInt256.isZero (UInt256.eq ⟨0⟩ lotNew) ≠ ⟨0⟩ := by
    rw [heqZero]
    native_decide
  exact ⟨_, _, rd5011pre.jumpiT (by clipper_runtime_decode) hcond
    (clipperTakeJumpDest5025 v hpatch) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem RD.clipperYankRemoveIdEqMoveToJoinGeneric {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {ret : UInt256}
    {R : List UInt256} {cA σ}
    (rd : RD code ee g s0 ⟨8274⟩ (clipperYankArgWord ee :: ret :: R)
      mem aw o (cA, σ) k C)
    (hlen : solcSlotWord σ ee ⟨11⟩ ≠ ⟨0⟩)
    (heq :
      let lastIndex := solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩
      clipperYankArgWord ee = solcSlotWord σ ee (clipperYankActiveSlot lastIndex))
    (hov : R.length + 32 ≤ 1024) :
    let lastIndex := solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩
    let move := solcSlotWord σ ee (clipperYankActiveSlot lastIndex)
    let activeMem := wordAt0Mem (⟨11⟩ : UInt256) mem
    let aw1 := UInt256.ofNat (MachineState.M aw.toNat 0 32)
    let aw2 := UInt256.ofNat (MachineState.M aw1.toNat 0 32)
    ∃ k' C', RD code ee g s0 ⟨8379⟩ (move :: clipperYankArgWord ee :: ret :: R)
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
    (by simp [activeMem, wordAt0Mem]) (by rfl) (by evm_ov)
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
    simp [lastIndex, clipperYankActiveSlot_eq]
  obtain ⟨k8307, C8307, rd8307slot⟩ :
      ∃ k C, RD code ee g s0 ⟨8307⟩
        (clipperYankActiveSlot lastIndex :: ⟨0⟩ :: clipperYankArgWord ee :: ret :: R)
        activeMem aw2 o (cA, σ) k C := by
    exact ⟨_, _, by simpa [solcSlotWord, hslotActive] using rd8307pre⟩
  obtain ⟨_, _, rd8308raw⟩ := rd8307slot.sload (by clipper_yank_remove_decode) (by evm_ov)
  obtain ⟨k8308, C8308, rd8308⟩ :
      ∃ k C, RD code ee g s0 ⟨8308⟩
        (move :: ⟨0⟩ :: clipperYankArgWord ee :: ret :: R)
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

set_option maxHeartbeats 1000000 in
theorem RD.clipperYankRemoveJoinToReturn {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {ret move : UInt256}
    {R : List UInt256} {cA σ}
    (rd : RD code ee g s0 ⟨8379⟩ (move :: clipperYankArgWord ee :: ret :: R)
      mem aw o (cA, σ) k C)
    (hlen : solcSlotWord σ ee ⟨11⟩ ≠ ⟨0⟩)
    (hactiveMemSize : 64 ≤ (wordAt0Mem (⟨11⟩ : UInt256) mem).size)
    (hperm : ee.perm = true)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 32 ≤ 1024) :
    let lastIndex := solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩
    let activeMem := wordAt0Mem (⟨11⟩ : UInt256) mem
    let aw1 := UInt256.ofNat (MachineState.M aw.toNat 0 32)
    let aw2 := UInt256.ofNat (MachineState.M aw1.toNat 0 32)
    let saleHashMem := twoWordHashMem (clipperYankArgWord ee) ⟨12⟩ activeMem
    let aw3 := UInt256.ofNat (MachineState.M aw2.toNat 0 32)
    let aw4 := UInt256.ofNat (MachineState.M aw3.toNat 32 32)
    let aw5 := UInt256.ofNat (MachineState.M aw4.toNat 0 64)
    ∃ k' C', RD code ee g s0 ret R saleHashMem aw5 o
      (cA, clipperYankRemoveAccountMap σ ee lastIndex) k' C' := by
  intro lastIndex activeMem aw1 aw2 saleHashMem aw3 aw4 aw5
  let len := solcSlotWord σ ee ⟨11⟩
  let saleKeyMem := wordAt0Mem (clipperYankArgWord ee) activeMem
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
    (by simp [activeMem, wordAt0Mem]) (by rfl) (by evm_ov)
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
    simp [lastIndex, clipperYankActiveSlot_eq]
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
          move :: clipperYankArgWord ee :: ret :: R)
        activeMem aw2 o
        (cA, sstoreAccountMap ee.codeOwner σ (clipperYankActiveSlot lastIndex) ⟨0⟩)
        k C := by
    obtain ⟨k', C', rd'⟩ := rd8411pre.sstore hperm (by clipper_yank_remove_decode)
      (by simp only [List.length_cons]; omega)
    exact ⟨k', C', by simpa [solcSlotWord, hslotActive'] using rd'⟩
  have rd8417pre := evm_run rd8412 with [
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap3 (by clipper_yank_remove_decode) (by evm_ov),
    raw add (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap3 (by clipper_yank_remove_decode) (by evm_ov)]
  obtain ⟨k8418, C8418, rd8418⟩ :
      ∃ k C, RD code ee g s0 ⟨8418⟩
        (⟨32⟩ :: ⟨0⟩ :: move :: clipperYankArgWord ee :: ret :: R)
        activeMem aw2 o (cA, clipperYankPopAccountMap σ ee lastIndex) k C := by
    obtain ⟨k', C', rd'⟩ := rd8417pre.sstore hperm (by clipper_yank_remove_decode)
      (by simp only [List.length_cons]; omega)
    exact ⟨k', C', by simpa [clipperYankPopAccountMap, lastIndex] using rd'⟩
  have rd8420pre := evm_run rd8418 with [
    raw swap3 (by clipper_yank_remove_decode) (by evm_ov),
    raw dup2 (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8421 := rd8420pre.mstore (Cₘ aw3 - Cₘ aw2) saleKeyMem aw3
    (by clipper_yank_remove_decode)
    (by
      intro s hawEq hstk
      exact mstoreCost_of_stack hawEq hstk (by simp [aw3]))
    (by simp [saleKeyMem, wordAt0Mem]) (by rfl) (by evm_ov)
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
      ∃ k C, RD code ee g s0 ⟨8434⟩ (base :: ⟨0⟩ :: ret :: R)
        saleHashMem aw5 o (cA, σSale0) k C := by
    obtain ⟨k', C', rd'⟩ := rd8433pre.sstore hperm (by clipper_yank_remove_decode)
      (by simp only [List.length_cons]; omega)
    exact ⟨k', C', by simpa [base, σSale0] using rd'⟩
  have rd8440pre := evm_run rd8434 with [
    raw push1 ⟨1⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw dup2 (by clipper_yank_remove_decode) (by evm_ov),
    raw add (by clipper_yank_remove_decode) (by evm_ov),
    raw dup3 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov)]
  obtain ⟨k8441, C8441, rd8441⟩ :
      ∃ k C, RD code ee g s0 ⟨8441⟩ (base :: ⟨0⟩ :: ret :: R)
        saleHashMem aw5 o (cA, σSale1) k C := by
    obtain ⟨k', C', rd'⟩ := rd8440pre.sstore hperm (by clipper_yank_remove_decode)
      (by simp only [List.length_cons]; omega)
    exact ⟨k', C', by simpa [σSale1] using rd'⟩
  have rd8447pre := evm_run rd8441 with [
    raw push1 ⟨2⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw dup2 (by clipper_yank_remove_decode) (by evm_ov),
    raw add (by clipper_yank_remove_decode) (by evm_ov),
    raw dup3 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov)]
  obtain ⟨k8448, C8448, rd8448⟩ :
      ∃ k C, RD code ee g s0 ⟨8448⟩ (base :: ⟨0⟩ :: ret :: R)
        saleHashMem aw5 o (cA, σSale2) k C := by
    obtain ⟨k', C', rd'⟩ := rd8447pre.sstore hperm (by clipper_yank_remove_decode)
      (by simp only [List.length_cons]; omega)
    exact ⟨k', C', by simpa [σSale2] using rd'⟩
  have rd8454pre := evm_run rd8448 with [
    raw push1 ⟨3⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw dup2 (by clipper_yank_remove_decode) (by evm_ov),
    raw add (by clipper_yank_remove_decode) (by evm_ov),
    raw dup3 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov)]
  obtain ⟨k8455, C8455, rd8455⟩ :
      ∃ k C, RD code ee g s0 ⟨8455⟩ (base :: ⟨0⟩ :: ret :: R)
        saleHashMem aw5 o (cA, σSale3) k C := by
    obtain ⟨k', C', rd'⟩ := rd8454pre.sstore hperm (by clipper_yank_remove_decode)
      (by simp only [List.length_cons]; omega)
    exact ⟨k', C', by simpa [σSale3] using rd'⟩
  have rd8458pre := evm_run rd8455 with [
    raw push1 ⟨4⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw add (by clipper_yank_remove_decode) (by evm_ov)]
  obtain ⟨k8459, C8459, rd8459⟩ :
      ∃ k C, RD code ee g s0 ⟨8459⟩ (ret :: R)
        saleHashMem aw5 o (cA, σRemoved) k C := by
    obtain ⟨k', C', rd'⟩ := rd8458pre.sstore hperm (by clipper_yank_remove_decode)
      (by simp only [List.length_cons]; omega)
    exact ⟨k', C', by
      simpa [σRemoved, clipperYankRemoveAccountMap, clipperYankDeleteSaleAccountMap,
        σSale0, σSale1, σSale2, σSale3, base,
        u256_add_comm (⟨4⟩ : UInt256) base] using rd'⟩
  have rdRet := rd8459.jump (by clipper_yank_remove_decode) hret (by evm_ov)
  exact ⟨_, _, by simpa [σRemoved] using rdRet⟩

theorem RD.clipperTakeRemoveReturnToEventTail {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨5020⟩
      (owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen :: dataStart ::
        who :: max :: amt :: id :: R)
      mem aw o acc k C)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨5250⟩
      (owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen :: dataStart ::
        who :: max :: amt :: id :: R)
      mem aw o acc k' C' := by
  have rd5024 := evm_run rd with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨5250⟩ (by clipper_runtime_decode) (by evm_ov)]
  exact ⟨_, _, rd5024.jump (by clipper_runtime_decode)
    (clipperTakeJumpDest5250 v hpatch) (by evm_ov)⟩

theorem clipperTakeZeroReturndataWrite_eq (out mem : ByteArray) :
    out.write 0 mem 128 (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = mem := by
  have hmin :
      (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat out.size := by
      show (0 : Nat) ≤ (UInt256.ofNat out.size).val.val
      exact Nat.zero_le _
    simp [min, hle]
  simp [hmin, byteArray_write_len_zero]

theorem clipperTakeVatMovePostCallMem_size (σ : AccountMap) (I : ExecutionEnv)
    (owe : UInt256) {baseMem out : ByteArray} (hbaseMem : baseMem.size = 260) :
    (out.write 0 (clipperTakeVatMoveCalldataMem σ I owe baseMem)
      128 (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat).size = 260 := by
  rw [clipperTakeZeroReturndataWrite_eq]
  exact clipperTakeVatMoveCalldataMem_size σ I owe hbaseMem

theorem clipperTakeVatMovePostCallMem_read64 (σ : AccountMap) (I : ExecutionEnv)
    (owe : UInt256) {baseMem out : ByteArray} (hbaseMem : baseMem.size = 260)
    (hread64 : baseMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (out.write 0 (clipperTakeVatMoveCalldataMem σ I owe baseMem)
      128 (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [clipperTakeZeroReturndataWrite_eq]
  exact clipperTakeVatMoveCalldataMem_read64 σ I owe hbaseMem hread64

theorem clipperTakeVatMovePostCallAw_eq :
    UInt256.ofNat
      (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
        (⟨128⟩ : UInt256).toNat (⟨100⟩ : UInt256).toNat)
        (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) =
      UInt256.ofNat 9 := by
  native_decide

abbrev clipperTakeLocalsDigsAmt (evmLoc evmRead evmVat : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe slice' tabNew lotNew : UInt256) : Store :=
  (clipperTakeLocalsMoveRet evmLoc evmRead evmVat I price slice owe0 owe slice'
    tabNew lotNew).insert "digsAmt"
      (.int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat))

abbrev clipperTakeLocalsDigsAmtRet (evmLoc evmRead evmVat : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe slice' tabNew lotNew : UInt256) : Store :=
  (clipperTakeLocalsDigsAmt evmLoc evmRead evmVat I price slice owe0 owe slice'
    tabNew lotNew).insert "_digsRet" .unit

theorem clipperEvalTakeTabAtMoveRet (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsMoveRet evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew))
      evmMove (.var "tab") = .ok (.int (Int.ofNat tabNew.toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsMoveRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsDogLoaded, store_get_ne _ _ (by decide),
    clipperTakeLocalsFluxBuyerRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsLotAssigned, store_get_ne _ _ (by decide),
    clipperTakeLocalsTabAssigned, store_get_self]
  rfl

theorem clipperEvalTakeOweAtMoveRet (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsMoveRet evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew))
      evmMove (.var "owe") =
        .ok (.int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsMoveRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsDogLoaded, store_get_ne _ _ (by decide),
    clipperTakeLocalsFluxBuyerRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsLotAssigned, store_get_ne _ _ (by decide),
    clipperTakeLocalsTabAssigned, store_get_ne _ _ (by decide),
    clipperTakeLocalsLotNew, store_get_ne _ _ (by decide),
    clipperTakeLocalsTabNew, store_get_ne _ _ (by decide),
    clipperTakeLocalsOweTabSlice, store_get_ne _ _ (by decide),
    clipperTakeLocalsOweTab, store_get_self]
  rfl

theorem clipperEvalTakeDigsAmtAtMoveRet (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (htabNew : tabNew = ⟨0⟩) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsMoveRet evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew))
      evmMove (wrap256 (.binary .add (.var "tab") (.var "owe"))) =
        .ok (.int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)) := by
  let moveFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsMoveRet evmLoc evmRead evmVat I price slice owe0 owe slice'
        tabNew lotNew)
  have htabEval : evalExpr? (config v) moveFrame evmMove (.var "tab") = .ok (.int 0) := by
    simpa [moveFrame, htabNew] using
      clipperEvalTakeTabAtMoveRet v evmLoc evmRead evmVat evmMove I price slice owe0
        owe slice' tabNew lotNew
  have howeEval : evalExpr? (config v) moveFrame evmMove (.var "owe") =
      .ok (.int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)) := by
    simpa [moveFrame] using
      clipperEvalTakeOweAtMoveRet v evmLoc evmRead evmVat evmMove I price slice owe0
        owe slice' tabNew lotNew
  have hwordNonzero : ¬wordModulus = 0 := by
    norm_num [wordModulus]
  simp [moveFrame, wrap256, evalExpr?, EvalResult.bind, bind, evalBinaryOp?, htabEval,
    howeEval, hwordNonzero]
  rw [Int.emod_eq_of_lt]
  · exact Int.natCast_nonneg _
  · have hltNat : (clipperTakeSalesTabEVMWord evmRead I).toNat < UInt256.size :=
      (clipperTakeSalesTabEVMWord evmRead I).val.isLt
    norm_num [wordModulus, UInt256.size] at hltNat ⊢
    exact_mod_cast hltNat

theorem clipperEvalTakeDogDigsTargetAtDigsAmt (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDigsAmt evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew))
      evmMove (.var "dog_") =
        .ok (.address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsDigsAmt, store_get_ne _ _ (by decide),
    clipperTakeLocalsMoveRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsDogLoaded, store_get_self]
  rfl

theorem clipperEvalTakeDogCodeGuardDigsAmt_true (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (hcode :
      0 <
        (UInt256.ofNat
          ((evmMove.lookupAccount
            (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)).option
            0 (fun acc => acc.code.size))).toNat) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDigsAmt evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew))
      evmMove (.binary .gt (.extCodeSize (.var "dog_")) (.intLit 0)) =
        .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, clipperEvalTakeDogDigsTargetAtDigsAmt,
    evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem clipperEvalTakeDogCodeGuardDigsAmt_false (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (hnoCode :
      (UInt256.ofNat
        ((evmMove.lookupAccount
          (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)).option
          0 (fun acc => acc.code.size))).toNat = 0) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDigsAmt evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew))
      evmMove (.binary .gt (.extCodeSize (.var "dog_")) (.intLit 0)) =
        .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, clipperEvalTakeDogDigsTargetAtDigsAmt,
    evalBinaryOp?, EVM.Word.ofNat, hnoCode]

theorem clipperEvalTakeDogDigsAmtArgs (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    evalExprs? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDigsAmt evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew))
      evmMove [ilkExpr v, .var "digsAmt"] =
        .ok
          [v.ilk, .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)] := by
  have hilk :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsDigsAmt evmLoc evmRead evmVat I price slice owe0 owe
            slice' tabNew lotNew))
        evmMove (ilkExpr v) = .ok v.ilk := by
    rcases v.ilk_wf with ⟨bs, hbs, _hlen⟩
    simp [ilkExpr, hbs, evalExpr?, pure]
  have hdigs :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsDigsAmt evmLoc evmRead evmVat I price slice owe0 owe
            slice' tabNew lotNew))
        evmMove (.var "digsAmt") =
          .ok (.int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsDigsAmt, store_get_self]
    rfl
  simp only [evalExprs?, hilk, hdigs, EvalResult.bind, bind, pure]

theorem clipperTakeDogDigsOweZeroNoCodeBlock (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (hlotNew : lotNew = ⟨0⟩) (htabNew : tabNew = ⟨0⟩)
    (hnoDogCode :
      (UInt256.ofNat
        ((evmMove.lookupAccount
          (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)).option
          0 (fun acc => acc.code.size))).toNat = 0) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsMoveRet evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew))
      evmMove
      [ .ite
          (.binary .eq (.var "lot") (.intLit 0))
          (wrappingAddInto "digsAmt" (.var "tab") (.var "owe") ++
            checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
              [ilkExpr v, .var "digsAmt"] "_digsRet")
          (checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
            [ilkExpr v, .var "owe"] "_digsRet") ]
      .reverted := by
  let moveFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsMoveRet evmLoc evmRead evmVat I price slice owe0 owe slice'
        tabNew lotNew)
  let digsAmtFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsDigsAmt evmLoc evmRead evmVat I price slice owe0 owe slice'
        tabNew lotNew)
  have hlotCond :
      evalExpr? (config v) moveFrame evmMove
        (.binary .eq (.var "lot") (.intLit 0)) = .ok (.bool true) := by
    simpa [moveFrame] using
      clipperEvalTakeLotEqZero_true v evmLoc evmRead evmVat evmMove I price slice
        owe0 owe slice' tabNew lotNew hlotNew
  have hdigsAmt :
      ExecStmt (config v) moveFrame evmMove
        (.letDecl "digsAmt" (some uint256) (wrap256 (.binary .add (.var "tab") (.var "owe"))))
        (.ok digsAmtFrame evmMove) := by
    have hrhs :=
      clipperEvalTakeDigsAmtAtMoveRet v evmLoc evmRead evmVat evmMove I price slice
        owe0 owe slice' tabNew lotNew htabNew
    simpa [moveFrame, digsAmtFrame, clipperTakeLocalsDigsAmt] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := moveFrame) (evm := evmMove) (name := "digsAmt")
        (ty := some uint256) (expr := wrap256 (.binary .add (.var "tab") (.var "owe")))
        (value := .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)) hrhs)
  have hdogRevert :
      ExecBlock (config v) digsAmtFrame evmMove
        (checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
          [ilkExpr v, .var "digsAmt"] "_digsRet")
        .reverted := by
    have hguard :
        evalExpr? (config v) digsAmtFrame evmMove
          (.binary .gt (.extCodeSize (.var "dog_")) (.intLit 0)) =
            .ok (.bool false) := by
      simpa [digsAmtFrame] using
        clipperEvalTakeDogCodeGuardDigsAmt_false v evmLoc evmRead evmVat evmMove I price
          slice owe0 owe slice' tabNew lotNew hnoDogCode
    simpa [checkedExternalCallStmts, digsAmtFrame] using
      (ExecBlock.consRevert (ExecStmt.requireFalse hguard))
  have hthen :
      ExecBlock (config v) moveFrame evmMove
        (wrappingAddInto "digsAmt" (.var "tab") (.var "owe") ++
          checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
            [ilkExpr v, .var "digsAmt"] "_digsRet")
        .reverted := by
    simpa [wrappingAddInto, moveFrame] using
      (ExecBlock.consNormal hdigsAmt hdogRevert)
  simpa [moveFrame] using
    ExecBlock.consRevert (ExecStmt.iteTrue hlotCond hthen)

theorem clipperTakeDogDigsOweZeroCallFailureBlock (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove evmDog : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) {outDog : ByteArray}
    (hlotNew : lotNew = ⟨0⟩) (htabNew : tabNew = ⟨0⟩)
    (hdogCode :
      0 <
        (UInt256.ofNat
          ((evmMove.lookupAccount
            (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)).option
            0 (fun acc => acc.code.size))).toNat)
    (hcallDog :
      typedCallViaEVM (config v) evmMove
        (EVM.address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat))
        "digs" 0
        [v.ilk, .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)]
        (false, evmDog, outDog) true) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsMoveRet evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew))
      evmMove
      [ .ite
          (.binary .eq (.var "lot") (.intLit 0))
          (wrappingAddInto "digsAmt" (.var "tab") (.var "owe") ++
            checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
              [ilkExpr v, .var "digsAmt"] "_digsRet")
          (checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
            [ilkExpr v, .var "owe"] "_digsRet") ]
      .reverted := by
  let moveFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsMoveRet evmLoc evmRead evmVat I price slice owe0 owe slice'
        tabNew lotNew)
  let digsAmtFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsDigsAmt evmLoc evmRead evmVat I price slice owe0 owe slice'
        tabNew lotNew)
  have hlotCond :
      evalExpr? (config v) moveFrame evmMove
        (.binary .eq (.var "lot") (.intLit 0)) = .ok (.bool true) := by
    simpa [moveFrame] using
      clipperEvalTakeLotEqZero_true v evmLoc evmRead evmVat evmMove I price slice
        owe0 owe slice' tabNew lotNew hlotNew
  have hdigsAmt :
      ExecStmt (config v) moveFrame evmMove
        (.letDecl "digsAmt" (some uint256) (wrap256 (.binary .add (.var "tab") (.var "owe"))))
        (.ok digsAmtFrame evmMove) := by
    have hrhs :=
      clipperEvalTakeDigsAmtAtMoveRet v evmLoc evmRead evmVat evmMove I price slice
        owe0 owe slice' tabNew lotNew htabNew
    simpa [moveFrame, digsAmtFrame, clipperTakeLocalsDigsAmt] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := moveFrame) (evm := evmMove) (name := "digsAmt")
        (ty := some uint256) (expr := wrap256 (.binary .add (.var "tab") (.var "owe")))
        (value := .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)) hrhs)
  have hdogRevert :
      ExecBlock (config v) digsAmtFrame evmMove
        (checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
          [ilkExpr v, .var "digsAmt"] "_digsRet")
        .reverted := by
    have htarget :
        evalExpr? (config v) digsAmtFrame evmMove (.var "dog_") =
          .ok (.address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)) := by
      simpa [digsAmtFrame] using
        clipperEvalTakeDogDigsTargetAtDigsAmt v evmLoc evmRead evmVat evmMove I price
          slice owe0 owe slice' tabNew lotNew
    have hguard :
        evalExpr? (config v) digsAmtFrame evmMove
          (.binary .gt (.extCodeSize (.var "dog_")) (.intLit 0)) =
            .ok (.bool true) := by
      simpa [digsAmtFrame] using
        clipperEvalTakeDogCodeGuardDigsAmt_true v evmLoc evmRead evmVat evmMove I price
          slice owe0 owe slice' tabNew lotNew hdogCode
    have hargs :
        evalExprs? (config v) digsAmtFrame evmMove [ilkExpr v, .var "digsAmt"] =
          .ok [v.ilk, .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)] := by
      simpa [digsAmtFrame] using
        clipperEvalTakeDogDigsAmtArgs v evmLoc evmRead evmVat evmMove I price slice
          owe0 owe slice' tabNew lotNew
    simpa [checkedExternalCallStmts, digsAmtFrame] using
      (ExecBlock.consNormal (ExecStmt.requireTrue hguard)
        (ExecBlock.consRevert
          (ExecStmt.externalCallFailure htarget (by simp [evalExpr?, pure]) hargs hcallDog)))
  have hthen :
      ExecBlock (config v) moveFrame evmMove
        (wrappingAddInto "digsAmt" (.var "tab") (.var "owe") ++
          checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
            [ilkExpr v, .var "digsAmt"] "_digsRet")
        .reverted := by
    simpa [wrappingAddInto, moveFrame] using
      (ExecBlock.consNormal hdigsAmt hdogRevert)
  simpa [moveFrame] using
    ExecBlock.consRevert (ExecStmt.iteTrue hlotCond hthen)

theorem clipperTakeDogDigsOweZeroCallSuccessBlock (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove evmDog : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) {outDog : ByteArray}
    (hlotNew : lotNew = ⟨0⟩) (htabNew : tabNew = ⟨0⟩)
    (hdogCode :
      0 <
        (UInt256.ofNat
          ((evmMove.lookupAccount
            (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)).option
            0 (fun acc => acc.code.size))).toNat)
    (hcallDog :
      typedCallViaEVM (config v) evmMove
        (EVM.address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat))
        "digs" 0
        [v.ilk, .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)]
        (true, evmDog, outDog) true) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsMoveRet evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew))
      evmMove
      [ .ite
          (.binary .eq (.var "lot") (.intLit 0))
          (wrappingAddInto "digsAmt" (.var "tab") (.var "owe") ++
            checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
              [ilkExpr v, .var "digsAmt"] "_digsRet")
          (checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
            [ilkExpr v, .var "owe"] "_digsRet") ]
      (.ok
        (Frame.mk (contract v)
          (clipperTakeLocalsDigsAmtRet evmLoc evmRead evmVat I price slice owe0 owe
            slice' tabNew lotNew))
        evmDog) := by
  let moveFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsMoveRet evmLoc evmRead evmVat I price slice owe0 owe slice'
        tabNew lotNew)
  let digsAmtFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsDigsAmt evmLoc evmRead evmVat I price slice owe0 owe slice'
        tabNew lotNew)
  let digsRetFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsDigsAmtRet evmLoc evmRead evmVat I price slice owe0 owe slice'
        tabNew lotNew)
  have hlotCond :
      evalExpr? (config v) moveFrame evmMove
        (.binary .eq (.var "lot") (.intLit 0)) = .ok (.bool true) := by
    simpa [moveFrame] using
      clipperEvalTakeLotEqZero_true v evmLoc evmRead evmVat evmMove I price slice
        owe0 owe slice' tabNew lotNew hlotNew
  have hdigsAmt :
      ExecStmt (config v) moveFrame evmMove
        (.letDecl "digsAmt" (some uint256) (wrap256 (.binary .add (.var "tab") (.var "owe"))))
        (.ok digsAmtFrame evmMove) := by
    have hrhs :=
      clipperEvalTakeDigsAmtAtMoveRet v evmLoc evmRead evmVat evmMove I price slice
        owe0 owe slice' tabNew lotNew htabNew
    simpa [moveFrame, digsAmtFrame, clipperTakeLocalsDigsAmt] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := moveFrame) (evm := evmMove) (name := "digsAmt")
        (ty := some uint256) (expr := wrap256 (.binary .add (.var "tab") (.var "owe")))
        (value := .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)) hrhs)
  have hdogOk :
      ExecBlock (config v) digsAmtFrame evmMove
        (checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
          [ilkExpr v, .var "digsAmt"] "_digsRet")
        (.ok digsRetFrame evmDog) := by
    have htarget :
        evalExpr? (config v) digsAmtFrame evmMove (.var "dog_") =
          .ok (.address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)) := by
      simpa [digsAmtFrame] using
        clipperEvalTakeDogDigsTargetAtDigsAmt v evmLoc evmRead evmVat evmMove I price
          slice owe0 owe slice' tabNew lotNew
    have hguard :
        evalExpr? (config v) digsAmtFrame evmMove
          (.binary .gt (.extCodeSize (.var "dog_")) (.intLit 0)) =
            .ok (.bool true) := by
      simpa [digsAmtFrame] using
        clipperEvalTakeDogCodeGuardDigsAmt_true v evmLoc evmRead evmVat evmMove I price
          slice owe0 owe slice' tabNew lotNew hdogCode
    have hargs :
        evalExprs? (config v) digsAmtFrame evmMove [ilkExpr v, .var "digsAmt"] =
          .ok [v.ilk, .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)] := by
      simpa [digsAmtFrame] using
        clipperEvalTakeDogDigsAmtArgs v evmLoc evmRead evmVat evmMove I price slice
          owe0 owe slice' tabNew lotNew
    simpa [checkedExternalCallStmts, digsAmtFrame, digsRetFrame,
      clipperTakeLocalsDigsAmtRet, collapseReturns] using
      (ExecBlock.consNormal (ExecStmt.requireTrue hguard)
        (ExecBlock.consNormal
          (ExecStmt.externalCallSuccess htarget (by simp [evalExpr?, pure]) hargs hcallDog
            (clipperTakeDecodeDigsVoid v outDog))
          ExecBlock.nil))
  have hthen :
      ExecBlock (config v) moveFrame evmMove
        (wrappingAddInto "digsAmt" (.var "tab") (.var "owe") ++
          checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
            [ilkExpr v, .var "digsAmt"] "_digsRet")
        (.ok digsRetFrame evmDog) := by
    simpa [wrappingAddInto, moveFrame, digsRetFrame] using
      (ExecBlock.consNormal hdigsAmt hdogOk)
  simpa [moveFrame, digsRetFrame] using
    ExecBlock.consNormal (ExecStmt.iteTrue hlotCond hthen) ExecBlock.nil

theorem clipperTakeLocalsDigsAmtRet_removeArgs (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmDog : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    evalExprs? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDigsAmtRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmDog [.var "id"] =
        .ok [clipperYankArgValue I] := by
  have hgetId :
      (clipperTakeLocalsDigsAmtRet evmLoc evmRead evmVat I price slice owe0 owe
        slice' tabNew lotNew).get? "id" = some (clipperYankArgValue I) := by
    rw [clipperTakeLocalsDigsAmtRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsDigsAmt, store_get_ne _ _ (by decide),
      clipperTakeLocalsMoveRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsDogLoaded, store_get_ne _ _ (by decide),
      clipperTakeLocalsFluxBuyerRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweTabSlice, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweTab, store_get_ne _ _ (by decide),
      clipperTakeLocalsOwe, store_get_ne _ _ (by decide),
      clipperTakeLocalsOwe0, store_get_ne _ _ (by decide),
      clipperTakeLocalsSlice, store_get_ne _ _ (by decide),
      clipperTakeLocalsTab, store_get_ne _ _ (by decide),
      clipperTakeLocalsLot, store_get_ne _ _ (by decide),
      clipperTakeLocalsPrice, store_get_ne _ _ (by decide),
      clipperTakeLocalsDone, store_get_ne _ _ (by decide),
      clipperTakeLocalsSt, store_get_ne _ _ (by decide),
      clipperTakeLocalsTic, store_get_ne _ _ (by decide),
      clipperTakeLocalsUsr, store_get_ne _ _ (by decide),
      clipperTakeStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
  have hidEval :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsDigsAmtRet evmLoc evmRead evmVat I price slice owe0 owe
            slice' tabNew lotNew))
        evmDog (.var "id") = .ok (clipperYankArgValue I) := by
    simp only [evalExpr?]
    rw [hgetId]
    rfl
  exact evalExprs?_singleton hidEval

theorem clipperTakeLocalsDigsAmtRet_removeRet_locked
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    ((clipperTakeLocalsDigsAmtRet evmLoc evmRead evmVat I price slice owe0 owe
      slice' tabNew lotNew).insert "_removeRet" .unit).get? "locked" = none := by
  simp [clipperTakeLocalsDigsAmtRet, clipperTakeLocalsDigsAmt,
    clipperTakeLocalsMoveRet, clipperTakeLocalsDogLoaded, clipperTakeLocalsFluxBuyerRet,
    clipperTakeLocalsLotAssigned, clipperTakeLocalsTabAssigned, clipperTakeLocalsLotNew,
    clipperTakeLocalsTabNew, clipperTakeLocalsOweTabSlice, clipperTakeLocalsOweTab,
    clipperTakeLocalsOwe, clipperTakeLocalsOwe0, clipperTakeLocalsSlice,
    clipperTakeLocalsTab, clipperTakeLocalsLot, clipperTakeLocalsPrice,
    clipperTakeLocalsDone, clipperTakeLocalsSt, clipperTakeLocalsTic,
    clipperTakeLocalsUsr, clipperTakeStore]

theorem clipperEvalTakeLotEqZeroAtDigsAmtRet_true (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmDog : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (hlotNew : lotNew = ⟨0⟩) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDigsAmtRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmDog (.binary .eq (.var "lot") (.intLit 0)) =
        .ok (.bool true) := by
  subst lotNew
  simp only [evalExpr?, EvalResult.bind, bind, pure]
  rw [clipperTakeLocalsDigsAmtRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsDigsAmt, store_get_ne _ _ (by decide),
    clipperTakeLocalsMoveRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsDogLoaded, store_get_ne _ _ (by decide),
    clipperTakeLocalsFluxBuyerRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsLotAssigned, store_get_self]
  change evalBinaryOp? .eq (.int 0) (.int 0) = .ok (.bool true)
  unfold evalBinaryOp?
  rfl

theorem clipperTakeDogDigsOweZeroRemoveIdEqMoveSourceOk (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove evmDog : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) {outDog : ByteArray}
    {acc : Account}
    (hlotNew : lotNew = ⟨0⟩) (htabNew : tabNew = ⟨0⟩)
    (hdogCode :
      0 <
        (UInt256.ofNat
          ((evmMove.lookupAccount
            (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)).option
            0 (fun acc => acc.code.size))).toNat)
    (hcallDog :
      typedCallViaEVM (config v) evmMove
        (EVM.address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat))
        "digs" 0
        [v.ilk, .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)]
        (true, evmDog, outDog) true)
    (hacc : evmDog.accountMap.find? evmDog.executionEnv.codeOwner = some acc)
    (hlen : Solm.EVM.storageLoad evmDog evmDog.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩)
    (heq :
      clipperYankArgWord I =
        Solm.EVM.storageLoad evmDog evmDog.executionEnv.codeOwner
          (clipperYankActiveSlot
            (UInt256.sub
              (Solm.EVM.storageLoad evmDog evmDog.executionEnv.codeOwner ⟨11⟩) ⟨1⟩))) :
    let lastIndex :=
      UInt256.sub (Solm.EVM.storageLoad evmDog evmDog.executionEnv.codeOwner ⟨11⟩) ⟨1⟩
    let evmRemove := clipperYankDeleteSaleState (clipperYankRemovePopState evmDog lastIndex) I
    let frameRemoveRet : Frame :=
      { contract := contract v,
        locals :=
          (clipperTakeLocalsDigsAmtRet evmLoc evmRead evmVat I price slice owe0 owe
            slice' tabNew lotNew).insert "_removeRet" .unit }
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsMoveRet evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew))
      evmMove
      [ .ite
          (.binary .eq (.var "lot") (.intLit 0))
          (wrappingAddInto "digsAmt" (.var "tab") (.var "owe") ++
            checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
              [ilkExpr v, .var "digsAmt"] "_digsRet")
          (checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
            [ilkExpr v, .var "owe"] "_digsRet"),
        .ite
          (.binary .eq (.var "lot") (.intLit 0))
          [ .internalCall "_remove" [.var "id"] "_removeRet" ]
          [ .ite
              (.binary .eq (.var "tab") (.intLit 0))
              (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
                [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
                [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
              [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
                .assign .storage (salesF (.var "id") "lot") (.var "lot") ] ],
        .assign .storage lockedRef (.intLit 0) ]
      (.ok frameRemoveRet
        (Solm.EVM.storageStore evmRemove evmRemove.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
  intro lastIndex evmRemove frameRemoveRet
  let move :=
    Solm.EVM.storageLoad evmDog evmDog.executionEnv.codeOwner
      (clipperYankActiveSlot lastIndex)
  let moveFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsMoveRet evmLoc evmRead evmVat I price slice owe0 owe slice'
        tabNew lotNew)
  let digsRetFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsDigsAmtRet evmLoc evmRead evmVat I price slice owe0 owe
        slice' tabNew lotNew)
  have hdog :
      ExecBlock (config v) moveFrame evmMove
        [ .ite
          (.binary .eq (.var "lot") (.intLit 0))
          (wrappingAddInto "digsAmt" (.var "tab") (.var "owe") ++
            checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
              [ilkExpr v, .var "digsAmt"] "_digsRet")
          (checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
            [ilkExpr v, .var "owe"] "_digsRet") ]
        (.ok digsRetFrame evmDog) := by
    simpa [moveFrame, digsRetFrame] using
      clipperTakeDogDigsOweZeroCallSuccessBlock v evmLoc evmRead evmVat evmMove
        evmDog I price slice owe0 owe slice' tabNew lotNew hlotNew htabNew
        hdogCode hcallDog
  have hremoveBody :
      ExecFuncBody (config v)
        { contract := contract v, locals := clipperYankRemoveStore I } evmDog
        removeFunction.body
        (.returned { contract := contract v, locals := clipperYankRemoveMoveStore I lastIndex move }
          evmRemove none) := by
    simpa [lastIndex, move, evmRemove] using
      clipperYankRemoveIdEqMoveSource v evmDog I hacc hlen heq
  have hremove :
      ExecStmt (config v) digsRetFrame evmDog
        (.internalCall "_remove" [.var "id"] "_removeRet")
        (.ok frameRemoveRet evmRemove) := by
    simpa [resumeAfterInternalCall, digsRetFrame, frameRemoveRet] using
      (internalCallFunctionReturn
        (cfg := config v)
        (caller := digsRetFrame)
        (evm := evmDog)
        (name := "_remove") (retVar := "_removeRet")
        (args := [.var "id"])
        (argVals := [clipperYankArgValue I])
        (callee := removeFunction)
        (locals := clipperYankRemoveStore I)
        (calleeSolm := { contract := contract v, locals := clipperYankRemoveMoveStore I lastIndex move })
        (calleeEvm := evmRemove)
        (value := none)
        (clipperTakeLocalsDigsAmtRet_removeArgs v evmLoc evmRead evmVat evmDog I price
          slice owe0 owe slice' tabNew lotNew)
        (clipperYankRemoveLookup v)
        (clipperYankRemoveBind I)
        hremoveBody)
  have hlotCond :
      evalExpr? (config v) digsRetFrame evmDog
        (.binary .eq (.var "lot") (.intLit 0)) = .ok (.bool true) := by
    simpa [digsRetFrame] using
      clipperEvalTakeLotEqZeroAtDigsAmtRet_true v evmLoc evmRead evmVat evmDog I
        price slice owe0 owe slice' tabNew lotNew hlotNew
  have hremoveIte :
      ExecStmt (config v) digsRetFrame evmDog
        (.ite
          (.binary .eq (.var "lot") (.intLit 0))
          [ .internalCall "_remove" [.var "id"] "_removeRet" ]
          [ .ite
              (.binary .eq (.var "tab") (.intLit 0))
              (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
                [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
                [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
              [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
                .assign .storage (salesF (.var "id") "lot") (.var "lot") ] ])
        (.ok frameRemoveRet evmRemove) := by
    exact ExecStmt.iteTrue hlotCond (ExecBlock.consNormal hremove ExecBlock.nil)
  have hzero :
      evalExpr? (config v) frameRemoveRet evmRemove (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure, frameRemoveRet]
  have hassign :
      assignStorageRef? (config v) frameRemoveRet evmRemove
        .storage lockedRef (.int 0) =
        .ok (frameRemoveRet,
          Solm.EVM.storageStore evmRemove evmRemove.executionEnv.codeOwner ⟨13⟩ ⟨0⟩) := by
    simpa [frameRemoveRet] using
      assign_clipperLocked v evmRemove
        ((clipperTakeLocalsDigsAmtRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew).insert "_removeRet" .unit)
        (clipperTakeLocalsDigsAmtRet_removeRet_locked evmLoc evmRead evmVat I price
          slice owe0 owe slice' tabNew lotNew)
        ⟨0⟩
  have hunlock :
      ExecStmt (config v) frameRemoveRet evmRemove
        (.assign .storage lockedRef (.intLit 0))
        (.ok frameRemoveRet
          (Solm.EVM.storageStore evmRemove evmRemove.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
    exact ExecStmt.assign hzero hassign
  have htail :
      ExecBlock (config v) digsRetFrame evmDog
        [ .ite
          (.binary .eq (.var "lot") (.intLit 0))
          [ .internalCall "_remove" [.var "id"] "_removeRet" ]
          [ .ite
              (.binary .eq (.var "tab") (.intLit 0))
              (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
                [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
                [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
              [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
                .assign .storage (salesF (.var "id") "lot") (.var "lot") ] ],
          .assign .storage lockedRef (.intLit 0) ]
        (.ok frameRemoveRet
          (Solm.EVM.storageStore evmRemove evmRemove.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
    exact ExecBlock.consNormal hremoveIte (ExecBlock.consNormal hunlock ExecBlock.nil)
  simpa [moveFrame, digsRetFrame] using
    execBlockAppendOk hdog htail

end Benchmarks.Dss.Clipper
