import Benchmarks.Dss.Clipper.TakePostStatus

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

abbrev clipperTakeVatMoveSelectorSeed : UInt256 :=
  ⟨3140843579⟩

abbrev clipperTakeVatMoveSelectorShifted : UInt256 :=
  UInt256.shiftLeft clipperTakeVatMoveSelectorSeed ⟨224⟩

abbrev clipperTakeVatMoveSelectorWord : UInt256 :=
  ⟨3140843579⟩

abbrev clipperTakeVowTarget (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (solcSlotWord σ I ⟨2⟩) solcAddrMask

theorem clipperTakeJumpDest4825 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨4825⟩ : UInt256) = true := by
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

theorem clipperTakeJumpDest4845 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨4845⟩ : UInt256) = true := by
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

noncomputable def clipperTakeVatMoveSelectorMem (mem : ByteArray) : ByteArray :=
  clipperTakeVatMoveSelectorShifted.toByteArray.write 0 mem 128 32

noncomputable def clipperTakeVatMoveSenderMem (I : ExecutionEnv) (mem : ByteArray) :
    ByteArray :=
  (solcSourceWord I).toByteArray.write 0 (clipperTakeVatMoveSelectorMem mem) 132 32

noncomputable def clipperTakeVatMoveVowMem (σ : AccountMap) (I : ExecutionEnv)
    (mem : ByteArray) : ByteArray :=
  (clipperTakeVowTarget σ I).toByteArray.write 0
    (clipperTakeVatMoveSenderMem I mem) 164 32

noncomputable def clipperTakeVatMoveCalldataMem (σ : AccountMap) (I : ExecutionEnv)
    (owe : UInt256) (mem : ByteArray) : ByteArray :=
  owe.toByteArray.write 0 (clipperTakeVatMoveVowMem σ I mem) 196 32

theorem clipperTakeVatMoveSelectorMem_size {mem : ByteArray} (hmem : mem.size = 260) :
    (clipperTakeVatMoveSelectorMem mem).size = 260 := by
  unfold clipperTakeVatMoveSelectorMem
  exact toByteArray_write32_size_of_le mem clipperTakeVatMoveSelectorShifted 128 260 260
    hmem (by omega) (by omega)

theorem clipperTakeVatMoveSenderMem_size (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 260) :
    (clipperTakeVatMoveSenderMem I mem).size = 260 := by
  unfold clipperTakeVatMoveSenderMem
  exact toByteArray_write32_size_of_le (clipperTakeVatMoveSelectorMem mem)
    (solcSourceWord I) 132 260 260 (clipperTakeVatMoveSelectorMem_size hmem)
    (by rw [clipperTakeVatMoveSelectorMem_size hmem]; omega) (by omega)

theorem clipperTakeVatMoveVowMem_size (σ : AccountMap) (I : ExecutionEnv)
    {mem : ByteArray} (hmem : mem.size = 260) :
    (clipperTakeVatMoveVowMem σ I mem).size = 260 := by
  unfold clipperTakeVatMoveVowMem
  exact toByteArray_write32_size_of_le (clipperTakeVatMoveSenderMem I mem)
    (clipperTakeVowTarget σ I) 164 260 260 (clipperTakeVatMoveSenderMem_size I hmem)
    (by rw [clipperTakeVatMoveSenderMem_size I hmem]; omega) (by omega)

theorem clipperTakeVatMoveCalldataMem_size (σ : AccountMap) (I : ExecutionEnv)
    (owe : UInt256) {mem : ByteArray} (hmem : mem.size = 260) :
    (clipperTakeVatMoveCalldataMem σ I owe mem).size = 260 := by
  unfold clipperTakeVatMoveCalldataMem
  exact toByteArray_write32_size_of_le (clipperTakeVatMoveVowMem σ I mem)
    owe 196 260 260 (clipperTakeVatMoveVowMem_size σ I hmem)
    (by rw [clipperTakeVatMoveVowMem_size σ I hmem]; omega) (by omega)

theorem clipperTakeVatMoveCalldataMem_read64 (σ : AccountMap) (I : ExecutionEnv)
    (owe : UInt256) {mem : ByteArray} (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperTakeVatMoveCalldataMem σ I owe mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperTakeVatMoveCalldataMem
  rw [toByteArray_write_read_below_of_gap owe _ 196 64
      (by rw [clipperTakeVatMoveVowMem_size σ I hmem]; omega) (by omega)
      (by rw [clipperTakeVatMoveVowMem_size σ I hmem]; native_decide)]
  unfold clipperTakeVatMoveVowMem
  rw [toByteArray_write_read_below_of_gap (clipperTakeVowTarget σ I) _ 164 64
      (by rw [clipperTakeVatMoveSenderMem_size I hmem]; omega) (by omega)
      (by rw [clipperTakeVatMoveSenderMem_size I hmem]; native_decide)]
  unfold clipperTakeVatMoveSenderMem
  rw [toByteArray_write_read_below_of_gap (solcSourceWord I) _ 132 64
      (by rw [clipperTakeVatMoveSelectorMem_size hmem]; omega) (by omega)
      (by rw [clipperTakeVatMoveSelectorMem_size hmem]; native_decide)]
  unfold clipperTakeVatMoveSelectorMem
  rw [toByteArray_write_read_below_of_gap clipperTakeVatMoveSelectorShifted _ 128 64
      (by rw [hmem]; omega) (by omega) (by rw [hmem]; native_decide)]
  exact hread64

theorem clipperTakeVatMoveSelectorMem_read128_4 {mem : ByteArray}
    (hmem : mem.size = 260) :
    (clipperTakeVatMoveSelectorMem mem).readWithPadding 128 4 = vatMoveSelector := by
  unfold clipperTakeVatMoveSelectorMem
  rw [toByteArray_write_read_window_of_gap clipperTakeVatMoveSelectorShifted mem 128 0 4
    (by norm_num) (by norm_num) (by norm_num) (by rw [hmem]; native_decide)]
  rw [toByteArray_eq_toBytesBE]
  native_decide

theorem clipperTakeVatMoveCalldataMem_read128_4 (σ : AccountMap) (I : ExecutionEnv)
    (owe : UInt256) {mem : ByteArray} (hmem : mem.size = 260) :
    (clipperTakeVatMoveCalldataMem σ I owe mem).readWithPadding 128 4 =
      vatMoveSelector := by
  have hSender : (clipperTakeVatMoveSenderMem I mem).size = 260 :=
    clipperTakeVatMoveSenderMem_size I hmem
  have hVow : (clipperTakeVatMoveVowMem σ I mem).size = 260 :=
    clipperTakeVatMoveVowMem_size σ I hmem
  unfold clipperTakeVatMoveCalldataMem
  rw [write32_read_below_len _ _ 196 128 4 (by rw [toByteArray_size])
    (by rw [hVow]; omega) (by omega) (by rw [hVow]; omega) (by norm_num)
    (by norm_num)]
  unfold clipperTakeVatMoveVowMem
  rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
    (by rw [hSender]; omega) (by omega) (by rw [hSender]; omega) (by norm_num)
    (by norm_num)]
  unfold clipperTakeVatMoveSenderMem
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by rw [clipperTakeVatMoveSelectorMem_size hmem]; omega) (by omega)
    (by rw [clipperTakeVatMoveSelectorMem_size hmem]; omega) (by norm_num)
    (by norm_num)]
  exact clipperTakeVatMoveSelectorMem_read128_4 hmem

theorem clipperTakeVatMoveCalldataMem_read132_32 (σ : AccountMap) (I : ExecutionEnv)
    (owe : UInt256) {mem : ByteArray} (hmem : mem.size = 260) :
    (clipperTakeVatMoveCalldataMem σ I owe mem).readWithPadding 132 32 =
      UInt256.toByteArray (solcSourceWord I) := by
  have hSender : (clipperTakeVatMoveSenderMem I mem).size = 260 :=
    clipperTakeVatMoveSenderMem_size I hmem
  have hVow : (clipperTakeVatMoveVowMem σ I mem).size = 260 :=
    clipperTakeVatMoveVowMem_size σ I hmem
  unfold clipperTakeVatMoveCalldataMem
  rw [write32_read_below _ _ 196 132 (by rw [toByteArray_size])
    (by rw [hVow]; omega) (by omega)]
  unfold clipperTakeVatMoveVowMem
  rw [write32_read_below _ _ 164 132 (by rw [toByteArray_size])
    (by rw [hSender]; omega) (by omega)]
  unfold clipperTakeVatMoveSenderMem
  rw [write32_read_back _ _ 132 (by rw [toByteArray_size])
    (by rw [clipperTakeVatMoveSelectorMem_size hmem]; omega)]
  rw [show (UInt256.toByteArray (solcSourceWord I)).extract 0 32 =
      UInt256.toByteArray (solcSourceWord I) by
    rw [show 32 = (UInt256.toByteArray (solcSourceWord I)).size by rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem clipperTakeVatMoveCalldataMem_read164_32 (σ : AccountMap) (I : ExecutionEnv)
    (owe : UInt256) {mem : ByteArray} (hmem : mem.size = 260) :
    (clipperTakeVatMoveCalldataMem σ I owe mem).readWithPadding 164 32 =
      UInt256.toByteArray (clipperTakeVowTarget σ I) := by
  have hVow : (clipperTakeVatMoveVowMem σ I mem).size = 260 :=
    clipperTakeVatMoveVowMem_size σ I hmem
  unfold clipperTakeVatMoveCalldataMem
  rw [write32_read_below _ _ 196 164 (by rw [toByteArray_size])
    (by rw [hVow]; omega) (by omega)]
  unfold clipperTakeVatMoveVowMem
  rw [write32_read_back _ _ 164 (by rw [toByteArray_size])
    (by rw [clipperTakeVatMoveSenderMem_size I hmem]; omega)]
  rw [show (UInt256.toByteArray (clipperTakeVowTarget σ I)).extract 0 32 =
      UInt256.toByteArray (clipperTakeVowTarget σ I) by
    rw [show 32 = (UInt256.toByteArray (clipperTakeVowTarget σ I)).size by
      rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem clipperTakeVatMoveCalldataMem_read196_32 (σ : AccountMap) (I : ExecutionEnv)
    (owe : UInt256) {mem : ByteArray} (hmem : mem.size = 260) :
    (clipperTakeVatMoveCalldataMem σ I owe mem).readWithPadding 196 32 =
      UInt256.toByteArray owe := by
  unfold clipperTakeVatMoveCalldataMem
  rw [write32_read_back _ _ 196 (by rw [toByteArray_size])
    (by rw [clipperTakeVatMoveVowMem_size σ I hmem]; omega)]
  rw [show (UInt256.toByteArray owe).extract 0 32 = UInt256.toByteArray owe by
    rw [show 32 = (UInt256.toByteArray owe).size by rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem clipperTakeVatMoveCalldataMem_read128_100 (σ : AccountMap) (I : ExecutionEnv)
    (owe : UInt256) {mem : ByteArray} (hmem : mem.size = 260) :
    (clipperTakeVatMoveCalldataMem σ I owe mem).readWithPadding 128 100 =
      vatMoveSelector ++ UInt256.toByteArray (solcSourceWord I) ++
        UInt256.toByteArray (clipperTakeVowTarget σ I) ++ UInt256.toByteArray owe := by
  rw [byteArray_readWithPadding_split _ 128 4 96 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [clipperTakeVatMoveCalldataMem_size σ I owe hmem]; omega)]
  rw [byteArray_readWithPadding_split _ 132 32 64 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [clipperTakeVatMoveCalldataMem_size σ I owe hmem]; omega)]
  rw [byteArray_readWithPadding_split _ 164 32 32 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [clipperTakeVatMoveCalldataMem_size σ I owe hmem]; omega)]
  rw [clipperTakeVatMoveCalldataMem_read128_4 σ I owe hmem,
    clipperTakeVatMoveCalldataMem_read132_32 σ I owe hmem,
    clipperTakeVatMoveCalldataMem_read164_32 σ I owe hmem,
    clipperTakeVatMoveCalldataMem_read196_32 σ I owe hmem]
  simp [ByteArray.append_assoc]

theorem clipperTakeVatMoveEncode_eq (v : ClipperImmutables) (σ : AccountMap)
    (I : ExecutionEnv) (owe : UInt256) {mem : ByteArray} (hmem : mem.size = 260) :
    (config v).externalABI.encode? "move"
      [.address I.source, .address (AccountAddress.ofNat (clipperTakeVowTarget σ I).toNat),
        .int (Int.ofNat owe.toNat)] =
      some ((clipperTakeVatMoveCalldataMem σ I owe mem).readWithPadding 128 100) := by
  rw [clipperTakeVatMoveCalldataMem_read128_100 σ I owe hmem]
  have hsource : EVM.word I.source.val = solcSourceWord I := by
    unfold solcSourceWord EVM.word EVM.uintN UInt256.ofNat
    rfl
  have hvowClean : UInt256.land (clipperTakeVowTarget σ I) solcAddrMask =
      clipperTakeVowTarget σ I := by
    have hcanon : (clipperTakeVowTarget σ I).toNat < EVM.addressModulus := by
      simpa [clipperTakeVowTarget] using
        solcAddrMask_result_canonical (solcSlotWord σ I ⟨2⟩)
    exact solcAddrMask_clean hcanon
  have hvowWord :
      EVM.word (AccountAddress.ofNat (clipperTakeVowTarget σ I).toNat).val =
        clipperTakeVowTarget σ I := by
    simpa [hvowClean] using clipperTakeWhoAddressWord (clipperTakeVowTarget σ I)
  have howeWord : EVM.word owe.toNat = owe := u256_ofNat_toNat owe
  have howeLt : owe.toNat < EVM.twoPow 256 := by
    change owe.val.val < UInt256.size
    exact owe.val.isLt
  change externalABI.encode? "move"
      [.address I.source, .address (AccountAddress.ofNat (clipperTakeVowTarget σ I).toNat),
        .int (Int.ofNat owe.toNat)] =
    some (vatMoveSelector ++ UInt256.toByteArray (solcSourceWord I) ++
      UInt256.toByteArray (clipperTakeVowTarget σ I) ++ UInt256.toByteArray owe)
  unfold externalABI ABI.encodeCallWithSelector? ABI.encodeABIValues?
  simp [ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType, addr,
    uint256, uint256Int, selectorBytes, vatMoveSelector, howeLt, howeWord, hsource,
    hvowWord, word_toBytesBE_toByteArray_eq_toByteArray, ByteArray.append_assoc]

theorem clipperTakeVatPatchPayload4751 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    code.extract' 4751 4783 =
      ({ data := (EVM.Word.ofNat (↑v.vat : Nat)).toBytesBE.toArray } : ByteArray) := by
  rcases v.ilk_wf with ⟨bs, hilk, hlen⟩
  let ilkBytes : ByteArray :=
    { data := (EVM.Word.ofNat (fromBytesBigEndian bs)).toBytesBE.toArray }
  let vatBytes : ByteArray :=
    { data := (EVM.Word.ofNat (↑v.vat : Nat)).toBytesBE.toArray }
  have hsize : vatBytes.size = 32 := by
    simpa [vatBytes] using word_toBytesBE_toByteArray_size (EVM.Word.ofNat (↑v.vat : Nat))
  have hpost :
      PatchesWindowDisjoint32 4751 4783
        [(5115, vatBytes), (6295, vatBytes), (7936, vatBytes)] := by
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff] at hp
    rcases hp with rfl | rfl | rfl | hfalse
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · cases hfalse
  exact patchRuntime_extract'_exact_split (template := clipperBytecode)
    (pre :=
      [(1510, ilkBytes), (1661, ilkBytes), (2221, ilkBytes), (2369, ilkBytes),
        (4239, ilkBytes), (4866, ilkBytes), (5046, ilkBytes), (6800, ilkBytes),
        (8747, ilkBytes), (1463, vatBytes), (2437, vatBytes), (3145, vatBytes),
        (4318, vatBytes), (4441, vatBytes)])
    (post := [(5115, vatBytes), (6295, vatBytes), (7936, vatBytes)])
    (off := 4751) (value := vatBytes)
    (by
      simpa [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, hilk, hlen,
        List.lookup_cons, ilkBytes, vatBytes] using hpatch)
    hsize hpost (by norm_num) (by norm_num)

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem clipperTakeVatPush32Decode4750 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    decode code (⟨4750⟩ : UInt256) =
      some (.Push .PUSH32, some (EVM.Word.ofNat (↑v.vat : Nat), 32)) := by
  unfold decode
  rw [patchRuntime_get?_disjoint hpatch
    (clipperRuntimePatchesWindowDisjoint32Bool v (⟨4750⟩ : UInt256).toNat
      ((⟨4750⟩ : UInt256).toNat + 1) (by native_decide))]
  norm_num
  change some (Operation.Push Operation.POp.PUSH32,
      some (uInt256OfByteArray (code.extract' 4751 4783), 32)) =
    some (Operation.Push Operation.POp.PUSH32,
      some (EVM.Word.ofNat (↑v.vat : Nat), 32))
  rw [clipperTakeVatPatchPayload4751 v hpatch]
  rw [uInt256OfByteArray_word_toBytesBE]

set_option maxHeartbeats 1000000 in
theorem RD.clipperTakeVatMoveExtcodesizeGuard {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {dog slice owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id :
      UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (rd4701 : RD code ee g s0 ⟨4701⟩
      (dog :: slice :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped ::
        dataLen :: dataStart :: who :: max :: amt :: id :: R)
      mem (UInt256.ofNat 9) rdata (cA, σ) k C)
    (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨4813⟩
      (clipperTakeVatTarget v :: clipperTakeVatTarget v :: ⟨0⟩ :: ⟨128⟩ ::
        ⟨100⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨228⟩ :: clipperTakeVatMoveSelectorWord ::
        clipperTakeVatTarget v :: dog :: slice :: owe :: tabNew :: lotNew :: price :: tic ::
        packed :: stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: R)
      (clipperTakeVatMoveCalldataMem σ ee owe mem)
      (UInt256.ofNat 9) rdata (cA, σ) k' C' := by
  let vatWord : UInt256 := EVM.Word.ofNat (↑v.vat : Nat)
  have hbaseMload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (mem := mem) (aw := UInt256.ofNat 9)
      (by rw [hmem]; norm_num) (by native_decide) hread64
  have hcallMload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (clipperTakeVatMoveCalldataMem σ ee owe mem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((clipperTakeVatMoveCalldataMem σ ee owe mem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (mem := clipperTakeVatMoveCalldataMem σ ee owe mem)
      (aw := UInt256.ofNat 9)
      (by rw [clipperTakeVatMoveCalldataMem_size σ ee owe hmem]; norm_num)
      (by native_decide)
      (clipperTakeVatMoveCalldataMem_read64 σ ee owe hmem hread64)
  have rd4708pre := evm_run rd4701 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨2⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rd4705raw⟩ := rd4708pre.sload
    (by clipper_runtime_decode) (by evm_ov)
  have rd4708pre := evm_run rd4705raw with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov)]
  have rd4709 := rd4708pre.mload 0 ⟨128⟩ (UInt256.ofNat 9)
    (by clipper_runtime_decode) mem_cost hbaseMload64 (by native_decide) (by evm_ov)
  have rd4717pre := evm_run rd4709 with [
    raw push4 clipperTakeVatMoveSelectorSeed (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨224⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  rw [show UInt256.shiftLeft clipperTakeVatMoveSelectorSeed ⟨224⟩ =
    clipperTakeVatMoveSelectorShifted from rfl] at rd4717pre
  have rd4719 := rd4717pre.mstore 0
    (clipperTakeVatMoveSelectorMem mem)
    (UInt256.ofNat 9) (by clipper_runtime_decode) mem_cost (by rfl)
    (by native_decide) (by evm_ov)
  have rd4724pre := evm_run rd4719 with [
    raw caller (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨4⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨128⟩ : UInt256) + ⟨4⟩ = ⟨132⟩ from by native_decide] at rd4724pre
  have rd4725 := rd4724pre.mstore 0
    (clipperTakeVatMoveSenderMem ee mem)
    (UInt256.ofNat 9) (by clipper_runtime_decode) mem_cost (by rfl)
    (by native_decide) (by evm_ov)
  have rd4740pre := evm_run rd4725 with [
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨36⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov)]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
    solcAddrMask from by native_decide] at rd4740pre
  rw [show (⟨128⟩ : UInt256) + ⟨36⟩ = ⟨164⟩ from by native_decide] at rd4740pre
  have rd4741 := rd4740pre.mstore 0
    (clipperTakeVatMoveVowMem σ ee mem)
    (UInt256.ofNat 9) (by clipper_runtime_decode) mem_cost
    (by
      rw [show (⟨164⟩ : UInt256).toNat = 164 from by decide]
      simp [clipperTakeVatMoveVowMem, clipperTakeVowTarget, solcSlotWord,
        u256_land_comm])
    (by native_decide) (by evm_ov)
  have rd4747pre := evm_run rd4741 with [
    raw push1 ⟨68⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup7 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨128⟩ : UInt256) + ⟨68⟩ = ⟨196⟩ from by native_decide] at rd4747pre
  have rd4748 := rd4747pre.mstore 0
    (clipperTakeVatMoveCalldataMem σ ee owe mem)
    (UInt256.ofNat 9) (by clipper_runtime_decode) mem_cost (by rfl)
    (by native_decide) (by evm_ov)
  have rd4749pre := evm_run rd4748 with [
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  have rd4750 := rd4749pre.mload 0 ⟨128⟩ (UInt256.ofNat 9)
    (by clipper_runtime_decode) mem_cost hcallMload64 (by native_decide) (by evm_ov)
  have rd4783 := rd4750.pushConst vatWord (width := 32) (op := .PUSH32)
    (by decide)
    (by simpa [vatWord] using clipperTakeVatPush32Decode4750 v hpatch)
    (by evm_ov)
  have rd4813 := evm_run rd4783 with [
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw push4 clipperTakeVatMoveSelectorWord (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨100⟩ (by clipper_runtime_decode) (by evm_ov),
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
  rw [show (⟨128⟩ : UInt256) + ⟨100⟩ = ⟨228⟩ from by native_decide] at rd4813
  rw [show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ = ⟨0⟩ from by native_decide]
    at rd4813
  rw [show (⟨0⟩ : UInt256) + ⟨100⟩ = ⟨100⟩ from by native_decide] at rd4813
  rw [show UInt256.land solcAddrMask vatWord = clipperTakeVatTarget v from by rfl] at rd4813
  exact ⟨_, _, by simpa [clipperTakeVatTarget, vatWord, u256_land_comm] using rd4813⟩

theorem RD.clipperTakeVatMoveNoCode {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {dog slice owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id :
      UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (rd4701 : RD code ee g s0 ⟨4701⟩
      (dog :: slice :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped ::
        dataLen :: dataStart :: who :: max :: amt :: id :: R)
      mem (UInt256.ofNat 9) rdata (cA, σ) k C)
    (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSizeVat :
      Reasoning.Theory.extCodeSizeWord σ (clipperTakeVatTarget v) = ⟨0⟩)
    (hov : R.length + 32 ≤ 1024) :
    RDrev code g s0 := by
  obtain ⟨_, _, rd4813⟩ :=
    RD.clipperTakeVatMoveExtcodesizeGuard (v := v) (hpatch := hpatch)
      rd4701 hmem hread64 hov
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨4813⟩) (okPc := ⟨4825⟩)
    rd4813 hcodeSizeVat
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode)
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.clipperTakeVatMovePostCall {cA0 cA gh bl σ₀ σStart σ I}
    {g : Sat256} {A : Substate} {k C : ℕ}
    {dog slice owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id :
      UInt256}
    {R : List UInt256} {baseMem rdata : ByteArray} (v : ClipperImmutables)
    {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (rd4813 : RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨4813⟩
      (clipperTakeVatTarget v :: clipperTakeVatTarget v :: ⟨0⟩ :: ⟨128⟩ ::
        ⟨100⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨228⟩ :: clipperTakeVatMoveSelectorWord ::
        clipperTakeVatTarget v :: dog :: slice :: owe :: tabNew :: lotNew :: price :: tic ::
        packed :: stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: R)
      (clipperTakeVatMoveCalldataMem σ I owe baseMem)
      (UInt256.ofNat 9) rdata (cA, σ) k C)
    (hbaseMem : baseMem.size = 260)
    (hcodeSizeVat :
      Reasoning.Theory.extCodeSizeWord σ (clipperTakeVatTarget v) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true)
    (hov : R.length + 32 ≤ 1024) :
    ∃ (cA_vat : Batteries.RBSet AccountAddress compare) (σ_vat : AccountMap)
      (zVat : Bool) (outVat : ByteArray) (A_vat : Substate) (k' C' : ℕ),
      RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨4829⟩
        ((if zVat then ⟨1⟩ else ⟨0⟩) :: ⟨228⟩ :: clipperTakeVatMoveSelectorWord ::
          clipperTakeVatTarget v :: dog :: slice :: owe :: tabNew :: lotNew :: price ::
          tic :: packed :: stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: R)
        (outVat.write 0 (clipperTakeVatMoveCalldataMem σ I owe baseMem)
          128 (min (⟨0⟩ : UInt256) (UInt256.ofNat outVat.size)).toNat)
        (UInt256.ofNat
          (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
            (⟨128⟩ : UInt256).toNat (⟨100⟩ : UInt256).toNat)
            (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat))
        outVat (cA_vat, σ_vat) k' C' ∧
      typedCallViaEVM (config v)
        { initState cA0 gh bl σStart σ₀ g A I with
          accountMap := σ, createdAccounts := cA }
        (EVM.address v.vat) "move" 0
        [.address I.source, .address (AccountAddress.ofNat (clipperTakeVowTarget σ I).toNat),
          .int (Int.ofNat owe.toNat)]
        (zVat,
          { initState cA0 gh bl σStart σ₀ g A I with
            accountMap := σ_vat
            substate := A_vat
            createdAccounts := cA_vat },
          outVat) true ∧
      outVat.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd4828⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨4813⟩) (okPc := ⟨4825⟩)
      rd4813 hcodeSizeVat
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (clipperTakeJumpDest4825 v hpatch)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode)
      (by simp only [List.length_cons]; omega)
  obtain ⟨cA_vat, σ_vat, zVat, outVat, A_in, callGas, k4829, C4829, hΘpack,
      rd4829raw, houtVatSize⟩ :=
    RD.call rd4828 (by clipper_runtime_decode) hdepth (by evm_ov)
  obtain ⟨g'', A_vat, hΘ⟩ := hΘpack
  refine ⟨cA_vat, σ_vat, zVat, outVat, A_vat, k4829, C4829, ?_, ?_,
    houtVatSize⟩
  · exact rd4829raw
  · let evmVat : EVM.State :=
      { initState cA0 gh bl σStart σ₀ g A I with
        accountMap := σ, createdAccounts := cA }
    refine callCoincides (cfg := config v)
      (evm := evmVat)
      (name := "move")
      (args :=
        [.address I.source,
          .address (AccountAddress.ofNat (clipperTakeVowTarget σ I).toNat),
          .int (Int.ofNat owe.toNat)])
      (tgt := EVM.address v.vat) (targetWord := clipperTakeVatTarget v)
      (cA' := cA_vat) (σ' := σ_vat) (A' := A_vat) (A_in := A_in)
      (z := zVat) (o := outVat) (g'' := g'') (callGas := callGas)
      (mem := clipperTakeVatMoveCalldataMem σ I owe baseMem)
      (inOff := ⟨128⟩) (inSize := ⟨100⟩) (callPerm := true)
      (fun h => absurd hdepth (by
        have hI : I.depth = (1024 : Fin 1025) := by
          simpa [evmVat, initState] using h
        rw [hI]
        decide))
      ?_ ?_ ?_
    · rw [clipperTakeVatTargetAddress v]
      exact clipperTakeEVMAddressAccountAddress v.vat
    · simpa [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
        show (⟨100⟩ : UInt256).toNat = 100 from by decide] using
        clipperTakeVatMoveEncode_eq v σ I owe hbaseMem
    · simpa [evmVat, initState, hperm] using hΘ

theorem RD.clipperTakeVatMoveCallFailure {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    (rd : RD code ee g s0 ⟨4829⟩ (⟨0⟩ :: R) mem aw o acc k C)
    (hosz : o.size < UInt256.size)
    (hov : R.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨4829⟩) (okPc := ⟨4845⟩)
    rd (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    hosz hov

theorem RD.clipperTakeVatMoveCallSuccessToDogDigs {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {dog slice owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id :
      UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨4829⟩
      (⟨1⟩ :: ⟨228⟩ :: clipperTakeVatMoveSelectorWord :: clipperTakeVatTarget v ::
        dog :: slice :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped ::
        dataLen :: dataStart :: who :: max :: amt :: id :: R)
      mem aw o acc k C)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨4850⟩
      (dog :: slice :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped ::
        dataLen :: dataStart :: who :: max :: amt :: id :: R)
      mem aw o acc k' C' := by
  obtain ⟨_, _, rd4847⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨4829⟩) (okPc := ⟨4845⟩) rd
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (clipperTakeJumpDest4845 v hpatch)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by simp only [List.length_cons]; omega)
  have rd4850 := evm_run rd4847 with [
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov)]
  exact ⟨_, _, rd4850⟩

end Benchmarks.Dss.Clipper
