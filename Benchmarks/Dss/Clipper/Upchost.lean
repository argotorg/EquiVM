import Benchmarks.Dss.Clipper.Arithmetic
import Benchmarks.Dss.Clipper.Dog
import Benchmarks.Dss.Clipper.ExternalCall
import Benchmarks.Dss.Clipper.Vat
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

theorem clipperUpchostSelectorWord {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I (clipperSelBytes 24)) :
    clipperSelWord I = clipperSelNat 24 := by
  simpa [clipperSelWord, solcSelectorWord, clipperSelNat] using
    solcSelectorWord_eq_of_beq I hsz 0x0c 0xbb 0x58 0x62 (clipperSelNat 24)
      (by native_decide) (by simpa [clipperSelBytes, selIs] using hsel)

theorem clipperDispatch_upchost (v : ClipperImmutables) {I : ExecutionEnv}
    (hsel : selIs I (clipperSelBytes 24)) :
    dispatchMsg (contract v) I.calldata = some (upchostTransition v) := by
  refine dispatchMsg_eq_some_of_split (contract := contract v)
    (pre :=
      [activeTransition, bufTransition, calcTransition, chipTransition, chostTransition,
        countTransition, cuspTransition, denyTransition, dogTransition, fileUintTransition,
        fileAddressTransition, getStatusTransition, ilkTransition v, kickTransition v,
        kicksTransition, listTransition, redoTransition v, relyTransition, salesTransition,
        spotterTransition, stoppedTransition, tailTransition, takeTransition v, tipTransition])
    (post := [vatTransition v, vowTransition, wardsTransition, yankTransition v])
    (ti := upchostTransition v) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · rfl
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | hfalse
    · rw [selectorOf, activeSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, bufSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, calcSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, chipSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, chostSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, countSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, cuspSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, denySelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, dogSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, fileUintSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, fileAddressSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, getStatusSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, ilkSelectorBytes v, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, kickSelectorBytes v, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, kicksSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, listSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, redoSelectorBytes v, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, relySelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, salesSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, spotterSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, stoppedSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, tailSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, takeSelectorBytes v, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, tipSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · cases hfalse
  · rw [selectorOf, upchostSelectorBytes v]
    simpa [clipperSelBytes] using hsel

theorem clipperDecode_upchost (v : ClipperImmutables) {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode ((upchostTransition v).params.map Param.name)
      (transitionSignature (upchostTransition v)).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode (config v).abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldataWithMode_empty_ok hsz

set_option maxHeartbeats 1000000 in
theorem clipperReachUpchostBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : ClipperImmutables)
    {code : ByteArray} (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (clipperSelBytes 24)) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨494⟩ : UInt256)
      [clipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := clipperReachRoot (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hpatch hcode hwv hsz hsize
  have hword := clipperUpchostSelectorWord hsz hsel
  have h260 := clipperSplitTaken (pc := (⟨32⟩ : UInt256)) (pivot := clipperSelNat 20)
    (tgt := (⟨260⟩ : UInt256)) h32
    (by
        change decode code (⟨32⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨32⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 20, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨32⟩ : UInt256)) = some (.GT, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨32⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨260⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨32⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨260⟩ : UInt256) (by native_decide))
    (by simp)
  have h369 := clipperSplitTaken (pc := (⟨261⟩ : UInt256)) (pivot := clipperSelNat 9)
    (tgt := (⟨369⟩ : UInt256))
    (h260.jumpdest
      (by
          change decode code (⟨260⟩ : UInt256) = some (.JUMPDEST, .none)
          clipper_decode)
      (by simp))
    (by
        change decode code (⟨261⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨261⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 9, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨261⟩ : UInt256)) = some (.GT, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨261⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨369⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨261⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨369⟩ : UInt256) (by native_decide))
    (by simp)
  have h429 := clipperSplitTaken (pc := (⟨370⟩ : UInt256)) (pivot := clipperSelNat 21)
    (tgt := (⟨429⟩ : UInt256))
    (h369.jumpdest
      (by
          change decode code (⟨369⟩ : UInt256) = some (.JUMPDEST, .none)
          clipper_decode)
      (by simp))
    (by
        change decode code (⟨370⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨370⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 21, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨370⟩ : UInt256)) = some (.GT, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨370⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨429⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨370⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨429⟩ : UInt256) (by native_decide))
    (by simp)
  have h441 := clipperArmNotTaken (pc := (⟨430⟩ : UInt256))
    (next := (⟨441⟩ : UInt256)) (sel := clipperSelNat 5)
    (tgt := (⟨468⟩ : UInt256))
    (h429.jumpdest
      (by
          change decode code (⟨429⟩ : UInt256) = some (.JUMPDEST, .none)
          clipper_decode)
      (by simp))
    (by
        change decode code (⟨430⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨430⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 5, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨430⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨430⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨468⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨430⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; native_decide)
    (by native_decide)
    (by simp)
  have h494 := clipperArmTaken (pc := (⟨441⟩ : UInt256)) (sel := clipperSelNat 24)
    (tgt := (⟨494⟩ : UInt256)) h441
    (by
        change decode code (⟨441⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨441⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 24, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨441⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨441⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨494⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨441⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨494⟩ : UInt256) (by native_decide))
    (by simp)
  exact ⟨_, _, h494⟩

theorem clipperEvalIlkExpr (v : ClipperImmutables) (evm : EVM.State) (locals : Store) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm (ilkExpr v) =
      .ok v.ilk := by
  rcases v.ilk_wf with ⟨bs, hilk, _hlen⟩
  simp [ilkExpr, hilk, evalExpr?, pure]

theorem clipperEvalIlkArg (v : ClipperImmutables) (evm : EVM.State) (locals : Store) :
    evalExprs? (config v) { contract := contract v, locals := locals } evm [ilkExpr v] =
      .ok [v.ilk] := by
  simp [evalExprs?, clipperEvalIlkExpr, EvalResult.bind, bind, pure]

/-! ## First `vatIlks(ilk)` call shape -/

abbrev clipperVatIlksSelectorWord : UInt256 :=
  ⟨3647180086⟩

abbrev clipperVatIlksSelectorShifted : UInt256 :=
  UInt256.shiftLeft clipperVatIlksSelectorWord ⟨224⟩

abbrev clipperUpchostVatTarget (v : ClipperImmutables) : UInt256 :=
  UInt256.land solcAddrMask (EVM.Word.ofNat (↑v.vat : Nat))

abbrev clipperUpchostDogTarget (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (solcSlotWord σ I ⟨1⟩)

abbrev clipperUpchostIlkWord (v : ClipperImmutables) : UInt256 :=
  EVM.Word.ofNat (fromBytesBigEndian (match v.ilk with
    | .fixedBytes _ bs => bs
    | _ => []))

noncomputable def clipperVatIlksSelectorMem (mem : ByteArray) : ByteArray :=
  clipperVatIlksSelectorShifted.toByteArray.write 0 mem 128 32

noncomputable def clipperVatIlksCalldataMem (ilk : UInt256) (mem : ByteArray) : ByteArray :=
  ilk.toByteArray.write 0 (clipperVatIlksSelectorMem mem) 132 32

abbrev clipperDogChopSelectorSeed : UInt256 :=
  ⟨452086951⟩

abbrev clipperDogChopSelectorShifted : UInt256 :=
  UInt256.shiftLeft clipperDogChopSelectorSeed ⟨227⟩

abbrev clipperDogChopSelectorWord : UInt256 :=
  ⟨3616695608⟩

noncomputable def clipperDogChopSelectorMem (mem : ByteArray) : ByteArray :=
  clipperDogChopSelectorShifted.toByteArray.write 0 mem 128 32

theorem clipperVatIlksSelectorMem_size {mem : ByteArray} (hmem : mem.size = 96) :
    (clipperVatIlksSelectorMem mem).size = 160 := by
  unfold clipperVatIlksSelectorMem
  exact toByteArray_write32_size_of_ge mem clipperVatIlksSelectorShifted 128 96 160 hmem
    (by omega) (by native_decide) (by omega)

theorem clipperVatIlksSelectorMem_read64 {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperVatIlksSelectorMem mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperVatIlksSelectorMem
  have hpreserve :
      ((UInt256.toByteArray clipperVatIlksSelectorShifted).write 0 mem 128 32).readWithPadding
          64 32 =
        mem.readWithPadding 64 32 :=
    toByteArray_write_read_below_of_gap (b := clipperVatIlksSelectorShifted) (mem := mem)
      (off := 128) (read := 64) (hread := by simp [hmem])
      (hbelow := by native_decide) (hgap := by rw [hmem]; native_decide)
  rw [hpreserve, hread64]

theorem clipperVatIlksCalldataMem_size (ilk : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (clipperVatIlksCalldataMem ilk mem).size = 164 := by
  unfold clipperVatIlksCalldataMem
  exact toByteArray_write32_size_of_le (clipperVatIlksSelectorMem mem) ilk 132 160 164
    (clipperVatIlksSelectorMem_size hmem)
    (by rw [clipperVatIlksSelectorMem_size hmem]; omega) (by omega)

theorem clipperVatIlksCalldataMem_read64 (ilk : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperVatIlksCalldataMem ilk mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperVatIlksCalldataMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [clipperVatIlksSelectorMem_size hmem]; omega) (by omega),
    clipperVatIlksSelectorMem_read64 hmem hread64]

theorem clipperVatIlksSelectorMem_selector {mem : ByteArray} (hmem : mem.size = 96) :
    (clipperVatIlksSelectorMem mem).extract 128 132 = vatIlksSelector := by
  unfold clipperVatIlksSelectorMem
  have hgap : 128 - mem.size < USize.size := by
    rw [hmem]
    native_decide
  rw [toByteArray_write_eq clipperVatIlksSelectorShifted mem 128 (by omega) hgap]
  have hprefix :
      (mem ++ ffi.ByteArray.zeroes (128 - mem.size)).size = 128 := by
    rw [ByteArray.size_append, ByteArray_zeroes_size, hmem]
  rw [extract_append_right_window _ _ 128 132 (by rw [hprefix]), hprefix,
    show 128 - 128 = 0 from rfl, show 132 - 128 = 4 from rfl,
    toByteArray_eq_toBytesBE]
  native_decide

theorem clipperVatIlksCalldataMem_read128_36 (ilk : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (clipperVatIlksCalldataMem ilk mem).readWithPadding 128 36 =
      vatIlksSelector ++ ilk.toByteArray := by
  rw [readWithPadding_eq_extract' _ 128 36 (by norm_num) (by norm_num)
      (by rw [clipperVatIlksCalldataMem_size ilk hmem]), clipperVatIlksCalldataMem,
    write32_eq _ (clipperVatIlksSelectorMem mem) 132 (by rw [toByteArray_size])
      (by rw [clipperVatIlksSelectorMem_size hmem]; omega)]
  have hAsz : ((clipperVatIlksSelectorMem mem).extract 0 132).size = 132 := by
    rw [ByteArray.size_extract, clipperVatIlksSelectorMem_size hmem]
    omega
  have hBsz : (ilk.toByteArray.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]
    omega
  have hPsz :
      ((clipperVatIlksSelectorMem mem).extract 0 132 ++
        ilk.toByteArray.extract 0 32).size = 164 := by
    rw [ByteArray.size_append, hAsz, hBsz]
  have hBfull : ilk.toByteArray.extract 0 32 = ilk.toByteArray := by
    have h := @ByteArray.extract_zero_size ilk.toByteArray
    rwa [toByteArray_size] at h
  rw [extract_append_left _ _ _ _ (by rw [hPsz]),
    extract_append_span _ _ 128 164 (by rw [hAsz]; omega) (by rw [hAsz]; omega),
    hAsz, extract_prefix _ 132 128 132 (by omega), clipperVatIlksSelectorMem_selector hmem,
    extract_extract_BA, show (0 : ℕ) + 0 = 0 from rfl,
    show min (0 + (164 - 132)) 32 = 32 from by omega, hBfull]

theorem clipperVatIlksEncode_eq (v : ClipperImmutables) :
    (config v).externalABI.encode? "vatIlks" [v.ilk] =
      some ((clipperVatIlksCalldataMem (clipperUpchostIlkWord v)
        solcFreePtrMem).readWithPadding 128 36) := by
  rcases v.ilk_wf with ⟨bs, hilk, hlen⟩
  rw [hilk]
  have hilkWord :
      clipperUpchostIlkWord v = EVM.Word.ofNat (fromBytesBigEndian bs) := by
    simp [clipperUpchostIlkWord, hilk]
  rw [hilkWord]
  change (config v).externalABI.encode? "vatIlks" [.fixedBytes ⟨31, by decide⟩ bs] =
    some ((clipperVatIlksCalldataMem (EVM.Word.ofNat (fromBytesBigEndian bs))
      solcFreePtrMem).readWithPadding 128 36)
  rw [clipperVatIlksCalldataMem_read128_36 _ solcFreePtrMem_size]
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
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, bytes32, bytes32Width, vatIlksSelector,
    selectorBytes, hlen, ABI.zeroBytes, hwordBytes, hbsByteArray]

noncomputable def clipperVatIlksPostCallMem (v : ClipperImmutables) (out : ByteArray) :
    ByteArray :=
  out.write 0 (clipperVatIlksCalldataMem (clipperUpchostIlkWord v) solcFreePtrMem) 128
    (min (⟨160⟩ : UInt256) (UInt256.ofNat out.size)).toNat

noncomputable def clipperDogChopCalldataMem (v : ClipperImmutables)
    (out : ByteArray) : ByteArray :=
  (clipperUpchostIlkWord v).toByteArray.write 0
    (clipperDogChopSelectorMem (clipperVatIlksPostCallMem v out)) 132 32

noncomputable def clipperDogChopPostCallMem (v : ClipperImmutables)
    (out outDog : ByteArray) : ByteArray :=
  outDog.write 0 (clipperDogChopCalldataMem v out) 128
    (min (⟨32⟩ : UInt256) (UInt256.ofNat outDog.size)).toNat

abbrev clipperDogChopPostCallAw : UInt256 :=
  UInt256.ofNat
    (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
      (⟨128⟩ : UInt256).toNat (⟨36⟩ : UInt256).toNat)
      (⟨128⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat)

abbrev clipperDogChopNat (outDog : ByteArray) : Nat :=
  fromByteArrayBigEndian (outDog.extract 0 32)

abbrev clipperDogChopWord (outDog : ByteArray) : UInt256 :=
  UInt256.ofNat (clipperDogChopNat outDog)

abbrev clipperDogChopValue (outDog : ByteArray) : Value :=
  .int (Int.ofNat (clipperDogChopNat outDog))

abbrev clipperDogChopValues (outDog : ByteArray) : List Value :=
  [clipperDogChopValue outDog]


abbrev clipperVatIlksDustWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 128 160))

abbrev clipperVatIlksArtWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))

abbrev clipperVatIlksRateWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 32 64))

abbrev clipperVatIlksSpotWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 64 96))

abbrev clipperVatIlksLineWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 96 128))

theorem clipperBytesToWord_drop_take32_eq_extract (out : ByteArray) (start : Nat) :
    ABI.bytesToWord ((out.toList.drop start).take 32) =
      UInt256.ofNat (fromByteArrayBigEndian (out.extract start (start + 32))) := by
  unfold ABI.bytesToWord fromByteArrayBigEndian
  congr 1
  rw [byteArray_toList_eq (out.extract start (start + 32)), ByteArray.data_extract,
    Array.toList_extract, List.extract_eq_take_drop, byteArray_toList_eq]
  simp [byteArray_toList_eq]

theorem clipperVatIlksPostCallWrite_size_gt64 {base : ByteArray} (out : ByteArray) (L : ℕ)
    (hbase : base.size = 164) (hLo : L ≤ out.size) :
    64 < (out.write 0 base 128 L).size := by
  rcases Nat.eq_zero_or_pos L with hzero | hpos
  · subst L
    rw [byteArray_write_len_zero, hbase]
    norm_num
  · by_cases hin : 128 + L ≤ base.size
    · rw [write_eq_gen out base 128 L (by omega) hLo hin, ByteArray.size_append,
        ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
        ByteArray.size_extract, hbase]
      omega
    · have hdest : 128 ≤ base.size := by
        rw [hbase]
        omega
      have hext : base.size < 128 + L := Nat.lt_of_not_ge hin
      rw [write_eq_gen_extend out base 128 L (by omega) hLo hdest hext,
        ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract, hbase]
      omega

theorem clipperVatIlksPostCallMem_size_gt64 (v : ClipperImmutables) (out : ByteArray)
    (hshort : out.size < 160) (hout : out.size < UInt256.size) :
    64 < (clipperVatIlksPostCallMem v out).size := by
  unfold clipperVatIlksPostCallMem
  have hlen :
      (min (⟨160⟩ : UInt256) (UInt256.ofNat out.size)).toNat = out.size :=
    umin_ofNat_right_toNat_of_lt (c := 160) (n := out.size) (by decide) hshort hout
  rw [hlen]
  exact clipperVatIlksPostCallWrite_size_gt64 out out.size
    (clipperVatIlksCalldataMem_size (clipperUpchostIlkWord v) solcFreePtrMem_size) le_rfl

theorem clipperVatIlksPostCallMem_read64 (v : ClipperImmutables) (out : ByteArray)
    (hshort : out.size < 160) (hout : out.size < UInt256.size) :
    (clipperVatIlksPostCallMem v out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperVatIlksPostCallMem
  have hlen :
      (min (⟨160⟩ : UInt256) (UInt256.ofNat out.size)).toNat = out.size :=
    umin_ofNat_right_toNat_of_lt (c := 160) (n := out.size) (by decide) hshort hout
  rw [hlen]
  change (out.write 0 (clipperVatIlksCalldataMem (clipperUpchostIlkWord v) solcFreePtrMem)
      128 out.size).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩
  by_cases hzero : out.size = 0
  · rw [hzero, byteArray_write_len_zero]
    exact clipperVatIlksCalldataMem_read64 (clipperUpchostIlkWord v) solcFreePtrMem_size
      solcFreePtrMem_read64
  · rw [write_read_below_gen_extend out
        (clipperVatIlksCalldataMem (clipperUpchostIlkWord v) solcFreePtrMem)
        128 out.size 64 hzero le_rfl
        (by rw [clipperVatIlksCalldataMem_size (clipperUpchostIlkWord v)
          solcFreePtrMem_size]; omega)
        (by omega)]
    exact clipperVatIlksCalldataMem_read64 (clipperUpchostIlkWord v) solcFreePtrMem_size
      solcFreePtrMem_read64

theorem clipperVatIlksPostCallMem_mload64 (v : ClipperImmutables) (out : ByteArray)
    (hshort : out.size < 160) (hout : out.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (clipperVatIlksPostCallMem v out).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((clipperVatIlksPostCallMem v out).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by
      have hgt := clipperVatIlksPostCallMem_size_gt64 v out hshort hout
      omega)
    (by decide)
    (clipperVatIlksPostCallMem_read64 v out hshort hout)

theorem clipperVatIlksPostCallMem_size_long (v : ClipperImmutables) (out : ByteArray)
    (hlo : 160 ≤ out.size) (hout : out.size < UInt256.size) :
    (clipperVatIlksPostCallMem v out).size = 288 := by
  unfold clipperVatIlksPostCallMem
  have hlen :
      (min (⟨160⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 160 :=
    umin_ofNat_right_toNat_of_ge (c := 160) (n := out.size) (by decide) hlo hout
  have hbaseSize :
      (clipperVatIlksCalldataMem (clipperUpchostIlkWord v) solcFreePtrMem).size = 164 :=
    clipperVatIlksCalldataMem_size (clipperUpchostIlkWord v) solcFreePtrMem_size
  rw [hlen]
  change (out.write 0 (clipperVatIlksCalldataMem (clipperUpchostIlkWord v) solcFreePtrMem)
    128 160).size = 288
  rw [write_eq_gen_extend out
    (clipperVatIlksCalldataMem (clipperUpchostIlkWord v) solcFreePtrMem) 128 160
    (by omega) (by omega) (by rw [hbaseSize]; omega) (by rw [hbaseSize]; omega)]
  rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
  rw [hbaseSize]
  omega

theorem clipperVatIlksPostCallMem_read64_long (v : ClipperImmutables) (out : ByteArray)
    (hlo : 160 ≤ out.size) (hout : out.size < UInt256.size) :
    (clipperVatIlksPostCallMem v out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperVatIlksPostCallMem
  have hlen :
      (min (⟨160⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 160 :=
    umin_ofNat_right_toNat_of_ge (c := 160) (n := out.size) (by decide) hlo hout
  have hbaseSize :
      (clipperVatIlksCalldataMem (clipperUpchostIlkWord v) solcFreePtrMem).size = 164 :=
    clipperVatIlksCalldataMem_size (clipperUpchostIlkWord v) solcFreePtrMem_size
  rw [hlen]
  change (out.write 0 (clipperVatIlksCalldataMem (clipperUpchostIlkWord v) solcFreePtrMem)
      128 160).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩
  rw [write_read_below_gen_extend out
    (clipperVatIlksCalldataMem (clipperUpchostIlkWord v) solcFreePtrMem)
    128 160 64 (by omega) (by omega) (by rw [hbaseSize]; omega) (by omega)]
  exact clipperVatIlksCalldataMem_read64 (clipperUpchostIlkWord v) solcFreePtrMem_size
    solcFreePtrMem_read64

theorem clipperVatIlksPostCallMem_mload64_long (v : ClipperImmutables) (out : ByteArray)
    (hlo : 160 ≤ out.size) (hout : out.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (clipperVatIlksPostCallMem v out).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((clipperVatIlksPostCallMem v out).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by rw [clipperVatIlksPostCallMem_size_long v out hlo hout]; decide)
    (by decide)
    (clipperVatIlksPostCallMem_read64_long v out hlo hout)

theorem clipperDogChopSelectorMem_size_long (v : ClipperImmutables) (out : ByteArray)
    (hlo : 160 ≤ out.size) (hout : out.size < UInt256.size) :
    (clipperDogChopSelectorMem (clipperVatIlksPostCallMem v out)).size = 288 := by
  unfold clipperDogChopSelectorMem
  exact toByteArray_write32_size_of_le (clipperVatIlksPostCallMem v out)
    clipperDogChopSelectorShifted 128 288 288
    (clipperVatIlksPostCallMem_size_long v out hlo hout)
    (by rw [clipperVatIlksPostCallMem_size_long v out hlo hout]; omega)
    (by omega)

theorem clipperDogChopSelectorMem_read64_long (v : ClipperImmutables) (out : ByteArray)
    (hlo : 160 ≤ out.size) (hout : out.size < UInt256.size) :
    (clipperDogChopSelectorMem (clipperVatIlksPostCallMem v out)).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperDogChopSelectorMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
    (by rw [clipperVatIlksPostCallMem_size_long v out hlo hout]; omega) (by omega)]
  exact clipperVatIlksPostCallMem_read64_long v out hlo hout

theorem clipperDogChopCalldataMem_size_long (v : ClipperImmutables) (out : ByteArray)
    (hlo : 160 ≤ out.size) (hout : out.size < UInt256.size) :
    (clipperDogChopCalldataMem v out).size = 288 := by
  unfold clipperDogChopCalldataMem
  exact toByteArray_write32_size_of_le
    (clipperDogChopSelectorMem (clipperVatIlksPostCallMem v out))
    (clipperUpchostIlkWord v) 132 288 288
    (clipperDogChopSelectorMem_size_long v out hlo hout)
    (by rw [clipperDogChopSelectorMem_size_long v out hlo hout]; omega)
    (by omega)

theorem clipperDogChopCalldataMem_read64_long (v : ClipperImmutables) (out : ByteArray)
    (hlo : 160 ≤ out.size) (hout : out.size < UInt256.size) :
    (clipperDogChopCalldataMem v out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperDogChopCalldataMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [clipperDogChopSelectorMem_size_long v out hlo hout]; omega) (by omega)]
  exact clipperDogChopSelectorMem_read64_long v out hlo hout

theorem clipperDogChopCalldataMem_mload64_long (v : ClipperImmutables) (out : ByteArray)
    (hlo : 160 ≤ out.size) (hout : out.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (clipperDogChopCalldataMem v out).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((clipperDogChopCalldataMem v out).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by rw [clipperDogChopCalldataMem_size_long v out hlo hout]; decide)
    (by decide)
    (clipperDogChopCalldataMem_read64_long v out hlo hout)

theorem clipperDogChopPostCallAw_eq :
    clipperDogChopPostCallAw = UInt256.ofNat 9 := by
  native_decide

theorem clipperDogChopPostCallMem_size (v : ClipperImmutables) (out outDog : ByteArray)
    (hlo : 160 ≤ out.size) (hout : out.size < UInt256.size)
    (houtDog : outDog.size < UInt256.size) :
    (clipperDogChopPostCallMem v out outDog).size = 288 := by
  unfold clipperDogChopPostCallMem
  have hbase :
      (clipperDogChopCalldataMem v out).size = 288 :=
    clipperDogChopCalldataMem_size_long v out hlo hout
  by_cases hshort : outDog.size < 32
  · have hlen :
        (min (⟨32⟩ : UInt256) (UInt256.ofNat outDog.size)).toNat = outDog.size :=
      umin_ofNat_right_toNat_of_lt (c := 32) (n := outDog.size) (by decide)
        hshort houtDog
    rw [hlen]
    by_cases hzero : outDog.size = 0
    · rw [hzero, byteArray_write_len_zero, hbase]
    · rw [write_eq_gen outDog (clipperDogChopCalldataMem v out) 128 outDog.size hzero
        le_rfl (by rw [hbase]; omega)]
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract, hbase]
      omega
  · have hloDog : 32 ≤ outDog.size := by omega
    have hlen :
        (min (⟨32⟩ : UInt256) (UInt256.ofNat outDog.size)).toNat = 32 :=
      umin_ofNat_right_toNat_of_ge (c := 32) (n := outDog.size) (by decide)
        hloDog houtDog
    rw [hlen]
    rw [write_eq_gen outDog (clipperDogChopCalldataMem v out) 128 32
      (by omega) (by omega) (by rw [hbase]; omega)]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, hbase]
    omega

theorem clipperDogChopPostCallMem_read64 (v : ClipperImmutables) (out outDog : ByteArray)
    (hlo : 160 ≤ out.size) (hout : out.size < UInt256.size)
    (houtDog : outDog.size < UInt256.size) :
    (clipperDogChopPostCallMem v out outDog).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperDogChopPostCallMem
  by_cases hshort : outDog.size < 32
  · have hlen :
        (min (⟨32⟩ : UInt256) (UInt256.ofNat outDog.size)).toNat = outDog.size :=
      umin_ofNat_right_toNat_of_lt (c := 32) (n := outDog.size) (by decide)
        hshort houtDog
    rw [hlen]
    by_cases hzero : outDog.size = 0
    · rw [hzero, byteArray_write_len_zero]
      exact clipperDogChopCalldataMem_read64_long v out hlo hout
    · rw [write_read_below_gen_extend outDog (clipperDogChopCalldataMem v out)
        128 outDog.size 64 hzero le_rfl
        (by rw [clipperDogChopCalldataMem_size_long v out hlo hout]; omega)
        (by omega)]
      exact clipperDogChopCalldataMem_read64_long v out hlo hout
  · have hloDog : 32 ≤ outDog.size := by omega
    have hlen :
        (min (⟨32⟩ : UInt256) (UInt256.ofNat outDog.size)).toNat = 32 :=
      umin_ofNat_right_toNat_of_ge (c := 32) (n := outDog.size) (by decide)
        hloDog houtDog
    rw [hlen]
    rw [write_read_below_gen_extend outDog (clipperDogChopCalldataMem v out)
      128 32 64 (by omega) (by omega)
      (by rw [clipperDogChopCalldataMem_size_long v out hlo hout]; omega)
      (by omega)]
    exact clipperDogChopCalldataMem_read64_long v out hlo hout

theorem clipperDogChopPostCallMem_mload64 (v : ClipperImmutables) (out outDog : ByteArray)
    (hlo : 160 ≤ out.size) (hout : out.size < UInt256.size)
    (houtDog : outDog.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (clipperDogChopPostCallMem v out outDog).size
        ∨ (⟨64⟩ : UInt256) ≥ clipperDogChopPostCallAw * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((clipperDogChopPostCallMem v out outDog).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  rw [clipperDogChopPostCallAw_eq]
  exact mloadFreePtrValue
    (by rw [clipperDogChopPostCallMem_size v out outDog hlo hout houtDog]; decide)
    (by decide)
    (clipperDogChopPostCallMem_read64 v out outDog hlo hout houtDog)

theorem clipperDogChopPostCallMem_read128 (v : ClipperImmutables) (out outDog : ByteArray)
    (hlo : 160 ≤ out.size) (hout : out.size < UInt256.size)
    (hloDog : 32 ≤ outDog.size) (houtDog : outDog.size < UInt256.size) :
    (clipperDogChopPostCallMem v out outDog).readWithPadding 128 32 =
      outDog.extract 0 32 := by
  unfold clipperDogChopPostCallMem
  have hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat outDog.size)).toNat = 32 :=
    umin_ofNat_right_toNat_of_ge (c := 32) (n := outDog.size) (by decide)
      hloDog houtDog
  rw [hlen]
  exact write32_read_back outDog (clipperDogChopCalldataMem v out) 128 hloDog
    (by rw [clipperDogChopCalldataMem_size_long v out hlo hout]; omega)

theorem clipperDogChopPostCallMem_mload128 (v : ClipperImmutables) (out outDog : ByteArray)
    (hlo : 160 ≤ out.size) (hout : out.size < UInt256.size)
    (hloDog : 32 ≤ outDog.size) (houtDog : outDog.size < UInt256.size) :
    (if (⟨128⟩ : UInt256).toNat ≥ (clipperDogChopPostCallMem v out outDog).size
        ∨ (⟨128⟩ : UInt256) ≥ clipperDogChopPostCallAw * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((clipperDogChopPostCallMem v out outDog).readWithPadding
          (⟨128⟩ : UInt256).toNat 32))) =
      clipperDogChopWord outDog := by
  have hsize := clipperDogChopPostCallMem_size v out outDog hlo hout houtDog
  have hread := clipperDogChopPostCallMem_read128 v out outDog hlo hout hloDog houtDog
  rw [clipperDogChopPostCallAw_eq]
  have hcond :
      ¬ ((⟨128⟩ : UInt256).toNat ≥ (clipperDogChopPostCallMem v out outDog).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩) := by
    rw [hsize]
    decide
  rw [if_neg hcond]
  change UInt256.ofNat
    (fromByteArrayBigEndian ((clipperDogChopPostCallMem v out outDog).readWithPadding 128 32)) =
      clipperDogChopWord outDog
  rw [hread]

theorem clipperDogChopSelectorMem_selector_long (v : ClipperImmutables)
    (out : ByteArray) (hlo : 160 ≤ out.size) (hout : out.size < UInt256.size) :
    (clipperDogChopSelectorMem (clipperVatIlksPostCallMem v out)).extract 128 132 =
      dogChopSelector := by
  unfold clipperDogChopSelectorMem
  rw [write32_eq _ _ 128 (by rw [toByteArray_size])
    (by rw [clipperVatIlksPostCallMem_size_long v out hlo hout]; omega)]
  have hAsz : ((clipperVatIlksPostCallMem v out).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, clipperVatIlksPostCallMem_size_long v out hlo hout]
    omega
  have hBsz : (clipperDogChopSelectorShifted.toByteArray.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]
    omega
  rw [extract_append_left
    ((clipperVatIlksPostCallMem v out).extract 0 128 ++
      clipperDogChopSelectorShifted.toByteArray.extract 0 32)
    ((clipperVatIlksPostCallMem v out).extract (128 + 32)
      (clipperVatIlksPostCallMem v out).size) 128 132
    (by rw [ByteArray.size_append, hAsz, hBsz]; omega)]
  rw [extract_append_right_window
    ((clipperVatIlksPostCallMem v out).extract 0 128)
    (clipperDogChopSelectorShifted.toByteArray.extract 0 32) 128 132
    (by rw [hAsz])]
  rw [hAsz, extract_extract_BA, show (0 : ℕ) + 0 = 0 from rfl,
    show min (0 + (132 - 128)) 32 = 4 from by omega, toByteArray_eq_toBytesBE]
  native_decide

theorem clipperDogChopCalldataMem_read128_36 (v : ClipperImmutables)
    (out : ByteArray) (hlo : 160 ≤ out.size) (hout : out.size < UInt256.size) :
    (clipperDogChopCalldataMem v out).readWithPadding 128 36 =
      dogChopSelector ++ (clipperUpchostIlkWord v).toByteArray := by
  rw [readWithPadding_eq_extract' _ 128 36 (by norm_num) (by norm_num)
      (by rw [clipperDogChopCalldataMem_size_long v out hlo hout]; omega),
    clipperDogChopCalldataMem,
    write32_eq _ (clipperDogChopSelectorMem (clipperVatIlksPostCallMem v out)) 132
      (by rw [toByteArray_size])
      (by rw [clipperDogChopSelectorMem_size_long v out hlo hout]; omega)]
  have hAsz :
      ((clipperDogChopSelectorMem (clipperVatIlksPostCallMem v out)).extract 0 132).size =
        132 := by
    rw [ByteArray.size_extract, clipperDogChopSelectorMem_size_long v out hlo hout]
    omega
  have hBsz : ((clipperUpchostIlkWord v).toByteArray.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]
    omega
  have hPsz :
      ((clipperDogChopSelectorMem (clipperVatIlksPostCallMem v out)).extract 0 132 ++
        (clipperUpchostIlkWord v).toByteArray.extract 0 32).size = 164 := by
    rw [ByteArray.size_append, hAsz, hBsz]
  have hBfull :
      (clipperUpchostIlkWord v).toByteArray.extract 0 32 =
        (clipperUpchostIlkWord v).toByteArray := by
    have h := @ByteArray.extract_zero_size (clipperUpchostIlkWord v).toByteArray
    rwa [toByteArray_size] at h
  rw [extract_append_left _ _ _ _ (by rw [hPsz]),
    extract_append_span _ _ 128 164 (by rw [hAsz]; omega) (by rw [hAsz]; omega),
    hAsz, extract_prefix _ 132 128 132 (by omega),
    clipperDogChopSelectorMem_selector_long v out hlo hout,
    extract_extract_BA, show (0 : ℕ) + 0 = 0 from rfl,
    show min (0 + (164 - 132)) 32 = 32 from by omega, hBfull]

theorem clipperDogChopEncode_eq (v : ClipperImmutables) (out : ByteArray)
    (hlo : 160 ≤ out.size) (hout : out.size < UInt256.size) :
    (config v).externalABI.encode? "chop" [v.ilk] =
      some ((clipperDogChopCalldataMem v out).readWithPadding 128 36) := by
  rcases v.ilk_wf with ⟨bs, hilk, hlen⟩
  rw [hilk]
  have hilkWord :
      clipperUpchostIlkWord v = EVM.Word.ofNat (fromBytesBigEndian bs) := by
    simp [clipperUpchostIlkWord, hilk]
  rw [clipperDogChopCalldataMem_read128_36 v out hlo hout, hilkWord]
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
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, bytes32, bytes32Width, dogChopSelector,
    selectorBytes, hlen, ABI.zeroBytes, hwordBytes, hbsByteArray]

theorem clipperVatIlksPostCallMem_read256_long (v : ClipperImmutables) (out : ByteArray)
    (hlo : 160 ≤ out.size) (hout : out.size < UInt256.size) :
    (clipperVatIlksPostCallMem v out).readWithPadding 256 32 = out.extract 128 160 := by
  unfold clipperVatIlksPostCallMem
  have hlen :
      (min (⟨160⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 160 :=
    umin_ofNat_right_toNat_of_ge (c := 160) (n := out.size) (by decide) hlo hout
  have hbaseSize :
      (clipperVatIlksCalldataMem (clipperUpchostIlkWord v) solcFreePtrMem).size = 164 :=
    clipperVatIlksCalldataMem_size (clipperUpchostIlkWord v) solcFreePtrMem_size
  rw [hlen]
  change (out.write 0 (clipperVatIlksCalldataMem (clipperUpchostIlkWord v) solcFreePtrMem)
      128 160).readWithPadding 256 32 = out.extract 128 160
  rw [write_eq_gen_extend out
    (clipperVatIlksCalldataMem (clipperUpchostIlkWord v) solcFreePtrMem) 128 160
    (by omega) (by omega) (by rw [hbaseSize]; omega) (by rw [hbaseSize]; omega)]
  have hprefix :
      ((clipperVatIlksCalldataMem (clipperUpchostIlkWord v) solcFreePtrMem).extract
        0 128).size = 128 := by
    rw [ByteArray.size_extract, hbaseSize]
    omega
  have hsrc : (out.extract 0 160).size = 160 := by
    rw [ByteArray.size_extract]
    omega
  have hmemSize :
      ((clipperVatIlksCalldataMem (clipperUpchostIlkWord v) solcFreePtrMem).extract 0 128 ++
        out.extract 0 160).size = 288 := by
    rw [ByteArray.size_append, hprefix, hsrc]
  have hreadIn :
      256 + 32 ≤
        ((clipperVatIlksCalldataMem (clipperUpchostIlkWord v) solcFreePtrMem).extract
            0 128 ++
          out.extract 0 160).size := by
    rw [hmemSize]
  rw [readWithPadding_eq_extract _ 256 hreadIn]
  rw [extract_append_right_window _ _ 256 288 (by rw [hprefix]; omega), hprefix]
  rw [show 256 - 128 = 128 by omega, show 288 - 128 = 160 by omega]
  rw [extract_extract_BA]
  norm_num

theorem clipperVatIlksPostCallMem_mload256_long (v : ClipperImmutables) (out : ByteArray)
    (hlo : 160 ≤ out.size) (hout : out.size < UInt256.size) :
    (if (⟨256⟩ : UInt256).toNat ≥ (clipperVatIlksPostCallMem v out).size
        ∨ (⟨256⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((clipperVatIlksPostCallMem v out).readWithPadding (⟨256⟩ : UInt256).toNat 32))) =
      clipperVatIlksDustWord out := by
  unfold clipperVatIlksDustWord
  rw [if_neg]
  · change UInt256.ofNat
      (fromByteArrayBigEndian ((clipperVatIlksPostCallMem v out).readWithPadding 256 32)) =
        UInt256.ofNat (fromByteArrayBigEndian (out.extract 128 160))
    rw [clipperVatIlksPostCallMem_read256_long v out hlo hout]
  · exact not_or.mpr
      ⟨by rw [clipperVatIlksPostCallMem_size_long v out hlo hout]; decide,
        by native_decide⟩

theorem clipperVatIlksDecode_none_short_aux {out : ByteArray} (hshort : out.size < 160) :
    ABI.decodeReturnValuesWithMode? DecodeMode.solcV1Signed
      [uint256, uint256, uint256, uint256, uint256] out = none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq
    (types := [uint256, uint256, uint256, uint256, uint256]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.solcV1Signed)
    (types := [uint256, uint256, uint256, uint256, uint256]) (bytes := out.toList)
    (cursor := 0) (total := 32 * [uint256, uint256, uint256, uint256, uint256].length)
    (by decide) (by simp)]
  cases hdec : decodeScalarWordsWithMode? DecodeMode.solcV1Signed
      [uint256, uint256, uint256, uint256, uint256] out.toList 0 with
  | none => rfl
  | some values =>
      have hlenDecoded :=
        decodeScalarWordsWithMode?_some_length (mode := DecodeMode.solcV1Signed)
          (types := [uint256, uint256, uint256, uint256, uint256])
          (bytes := out.toList) (cursor := 0) (values := values) (by omega) hdec
      rw [hlen] at hlenDecoded
      simp only [List.length_cons, List.length_nil, Nat.zero_add] at hlenDecoded
      omega

theorem clipperVatIlksDecode_none_short {v : ClipperImmutables} {out : ByteArray}
    (hshort : out.size < 160) :
    (config v).externalABI.decode? "vatIlks" out = none := by
  have h := clipperVatIlksDecode_none_short_aux (out := out) hshort
  simpa [config, externalABI] using h

theorem clipperVatIlksDecode_ok_aux {out : ByteArray} (hlo : 160 ≤ out.size) :
    ABI.decodeReturnValuesWithMode? DecodeMode.solcV1Signed
      [abiUInt256, abiUInt256, abiUInt256, abiUInt256, abiUInt256] out =
      some [.int (Int.ofNat (clipperVatIlksArtWord out).toNat),
        .int (Int.ofNat (clipperVatIlksRateWord out).toNat),
        .int (Int.ofNat (clipperVatIlksSpotWord out).toNat),
        .int (Int.ofNat (clipperVatIlksLineWord out).toNat),
        .int (Int.ofNat (clipperVatIlksDustWord out).toNat)] := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake0 : ((out.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  have htake32 : ((out.toList.drop 32).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have htake64 : ((out.toList.drop 64).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have htake96 : ((out.toList.drop 96).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have htake128 : ((out.toList.drop 128).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have hword0 : ABI.bytesToWord ((out.toList.drop 0).take 32) =
      clipperVatIlksArtWord out := by
    simpa [clipperVatIlksArtWord] using clipperBytesToWord_drop_take32_eq_extract out 0
  have hword1 : ABI.bytesToWord ((out.toList.drop 32).take 32) =
      clipperVatIlksRateWord out := by
    simpa [clipperVatIlksRateWord] using clipperBytesToWord_drop_take32_eq_extract out 32
  have hword2 : ABI.bytesToWord ((out.toList.drop 64).take 32) =
      clipperVatIlksSpotWord out := by
    simpa [clipperVatIlksSpotWord] using clipperBytesToWord_drop_take32_eq_extract out 64
  have hword3 : ABI.bytesToWord ((out.toList.drop 96).take 32) =
      clipperVatIlksLineWord out := by
    simpa [clipperVatIlksLineWord] using clipperBytesToWord_drop_take32_eq_extract out 96
  have hword4 : ABI.bytesToWord ((out.toList.drop 128).take 32) =
      clipperVatIlksDustWord out := by
    simpa [clipperVatIlksDustWord] using clipperBytesToWord_drop_take32_eq_extract out 128
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq
    (types := [abiUInt256, abiUInt256, abiUInt256, abiUInt256, abiUInt256]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.solcV1Signed)
    (types := [abiUInt256, abiUInt256, abiUInt256, abiUInt256, abiUInt256])
    (bytes := out.toList) (cursor := 0)
    (total := 32 * [abiUInt256, abiUInt256, abiUInt256, abiUInt256, abiUInt256].length)
    (by decide) (by simp)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.solcV1Signed)
    (bytes := out.toList) (start := 0) htake0]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.solcV1Signed)
    (bytes := out.toList) (start := 32) htake32]
  simp only [Option.bind_some]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.solcV1Signed)
    (bytes := out.toList) (start := 64) htake64]
  simp only [Option.bind_some]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.solcV1Signed)
    (bytes := out.toList) (start := 96) htake96]
  simp only [Option.bind_some]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.solcV1Signed)
    (bytes := out.toList) (start := 128) htake128]
  simp only [Option.bind_some]
  rw [hword0, hword1, hword2, hword3, hword4]

theorem clipperVatIlksDecode_ok {v : ClipperImmutables} {out : ByteArray}
    (hlo : 160 ≤ out.size) :
    (config v).externalABI.decode? "vatIlks" out =
      some [.int (Int.ofNat (clipperVatIlksArtWord out).toNat),
        .int (Int.ofNat (clipperVatIlksRateWord out).toNat),
        .int (Int.ofNat (clipperVatIlksSpotWord out).toNat),
        .int (Int.ofNat (clipperVatIlksLineWord out).toNat),
        .int (Int.ofNat (clipperVatIlksDustWord out).toNat)] := by
  have h := clipperVatIlksDecode_ok_aux (out := out) hlo
  simpa [config, externalABI, uint256, uint256Int, abiUInt256] using h

theorem clipperDogChopDecode_none_short {v : ClipperImmutables} {outDog : ByteArray}
    (hshort : outDog.size < 32) :
    (config v).externalABI.decode? "chop" outDog = none := by
  simpa [config, externalABI, decodeReturn?, uint256, uint256Int, abiUInt256] using
    (decodeReturnValueWithMode_solcV1Signed_uint256_none_short (returndata := outDog) hshort)

theorem clipperDogChopDecode_ok {v : ClipperImmutables} {outDog : ByteArray}
    (hlo : 32 ≤ outDog.size) :
    (config v).externalABI.decode? "chop" outDog = some (clipperDogChopValues outDog) := by
  simpa [config, externalABI, decodeReturn?, clipperDogChopValues, clipperDogChopValue,
    clipperDogChopNat, uint256, uint256Int, abiUInt256] using
    (decodeReturnValueWithMode_solcV1Signed_uint256_ok (returndata := outDog) hlo)

abbrev clipperVatIlksValues (out : ByteArray) : List Value :=
  [.int (Int.ofNat (clipperVatIlksArtWord out).toNat),
    .int (Int.ofNat (clipperVatIlksRateWord out).toNat),
    .int (Int.ofNat (clipperVatIlksSpotWord out).toNat),
    .int (Int.ofNat (clipperVatIlksLineWord out).toNat),
    .int (Int.ofNat (clipperVatIlksDustWord out).toNat)]

abbrev clipperUpchostVatIlkLocals (out : ByteArray) : Store :=
  (∅ : Store).insert "vatIlk" (collapseReturns (clipperVatIlksValues out))

abbrev clipperUpchostDustLocals (out : ByteArray) : Store :=
  (clipperUpchostVatIlkLocals out).insert "_dust"
    (.int (Int.ofNat (clipperVatIlksDustWord out).toNat))

abbrev clipperUpchostChopLocals (out outDog : ByteArray) : Store :=
  (clipperUpchostDustLocals out).insert "chop" (clipperDogChopValue outDog)

abbrev clipperUpchostChostWord (out outDog : ByteArray) : UInt256 :=
  UInt256.div (UInt256.mul (clipperVatIlksDustWord out) (clipperDogChopWord outDog))
    ⟨1000000000000000000⟩

abbrev clipperUpchostChostLocals (out outDog : ByteArray) : Store :=
  (clipperUpchostChopLocals out outDog).insert "chostNew"
    (.int (Int.ofNat (clipperUpchostChostWord out outDog).toNat))

theorem clipperUpchostPatchesWindowDisjoint32Bool (v : ClipperImmutables)
    (lo hi : Nat)
    (h : patchOffsetsWindowDisjoint32Bool lo hi
      [1510, 1661, 2221, 2369, 4239, 4866, 5046, 6800, 8747,
       1463, 2437, 3145, 4318, 4441, 4751, 5115, 6295, 7936] = true) :
    PatchesWindowDisjoint32 lo hi (patches v) := by
  apply patchesWindowDisjoint32_of_offsets_bool
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk, patchOffsetsWindowDisjoint32Bool]
  | some bs =>
      simpa [hIlk] using h

theorem clipperUpchostDecodeDisjoint (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {pc : UInt256} {res : Operation × Option (UInt256 × Nat)}
    (hbyte : patchOffsetsWindowDisjoint32Bool pc.toNat (pc.toNat + 1)
      [1510, 1661, 2221, 2369, 4239, 4866, 5046, 6800, 8747,
       1463, 2437, 3145, 4318, 4441, 4751, 5115, 6295, 7936] = true)
    (hargs :
      patchOffsetsWindowDisjoint32Bool (pc.toNat + 1)
        (pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2))
        [1510, 1661, 2221, 2369, 4239, 4866, 5046, 6800, 8747,
         1463, 2437, 3145, 4318, 4441, 4751, 5115, 6295, 7936] = true)
    (hdec : decode clipperBytecode pc = some res)
    (hi64 : pc.toNat + 1 < 2 ^ 64)
    (harg64 :
      pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2) < 2 ^ 64) :
    decode code pc = some res :=
  patchRuntime_decode_disjoint_of_decode_res hpatch
    (clipperUpchostPatchesWindowDisjoint32Bool v pc.toNat (pc.toNat + 1) hbyte)
    (clipperUpchostPatchesWindowDisjoint32Bool v (pc.toNat + 1)
      (pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2)) hargs)
    hdec hi64 harg64

macro "clipper_upchost_decode" : tactic =>
  `(tactic| first
    | clipper_decode
    | exact clipperUpchostDecodeDisjoint _ (by assumption)
        (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by native_decide))

theorem clipperUpchostVatPatchPayload (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    code.extract' 1463 1495 =
      ({ data := (EVM.Word.ofNat (↑v.vat : Nat)).toBytesBE.toArray } : ByteArray) := by
  rcases v with ⟨ilk, vat, hwf⟩
  rcases hwf with ⟨ilkBs, hilk, hlen⟩
  subst ilk
  let ilkBytes : ByteArray :=
    { data := (EVM.Word.ofNat (fromBytesBigEndian ilkBs)).toBytesBE.toArray }
  let vatBytes : ByteArray :=
    { data := (EVM.Word.ofNat (↑vat : Nat)).toBytesBE.toArray }
  have hsize : vatBytes.size = 32 := by
    simpa [vatBytes] using word_toBytesBE_toByteArray_size (EVM.Word.ofNat (↑vat : Nat))
  have hpost :
      PatchesWindowDisjoint32 1463 1495
        [(2437, vatBytes), (3145, vatBytes), (4318, vatBytes), (4441, vatBytes),
          (4751, vatBytes), (5115, vatBytes), (6295, vatBytes), (7936, vatBytes)] := by
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hfalse
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
        (4239, ilkBytes), (4866, ilkBytes), (5046, ilkBytes), (6800, ilkBytes),
        (8747, ilkBytes)])
    (post :=
      [(2437, vatBytes), (3145, vatBytes), (4318, vatBytes), (4441, vatBytes),
        (4751, vatBytes), (5115, vatBytes), (6295, vatBytes), (7936, vatBytes)])
    (off := 1463) (value := vatBytes)
    (by
      simpa [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord,
        List.lookup_cons, hlen, ilkBytes, vatBytes] using hpatch)
    hsize hpost (by norm_num) (by norm_num)

theorem clipperUpchostIlkPatchPayload (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {bs : List UInt8} (hilk : v.ilk = .fixedBytes ⟨31, by decide⟩ bs)
    (hlen : bs.length = 32) :
    code.extract' 1510 1542 =
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
      PatchesWindowDisjoint32 1510 1542
        [(1661, ilkBytes), (2221, ilkBytes), (2369, ilkBytes), (4239, ilkBytes),
          (4866, ilkBytes), (5046, ilkBytes), (6800, ilkBytes), (8747, ilkBytes),
          (1463, vatBytes), (2437, vatBytes), (3145, vatBytes), (4318, vatBytes),
          (4441, vatBytes), (4751, vatBytes), (5115, vatBytes), (6295, vatBytes),
          (7936, vatBytes)] := by
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hfalse
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
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · cases hfalse
  exact patchRuntime_extract'_exact_split (template := clipperBytecode)
    (pre := [])
    (post :=
      [(1661, ilkBytes), (2221, ilkBytes), (2369, ilkBytes), (4239, ilkBytes),
        (4866, ilkBytes), (5046, ilkBytes), (6800, ilkBytes), (8747, ilkBytes),
        (1463, vatBytes), (2437, vatBytes), (3145, vatBytes), (4318, vatBytes),
        (4441, vatBytes), (4751, vatBytes), (5115, vatBytes), (6295, vatBytes),
        (7936, vatBytes)])
    (off := 1510) (value := ilkBytes)
    (by
      simpa [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, hilk, hlen,
        List.lookup_cons, ilkBytes, vatBytes] using hpatch)
    hsize hpost (by norm_num) (by norm_num)

theorem clipperUpchostIlkPatchPayload1661 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {bs : List UInt8} (hilk : v.ilk = .fixedBytes ⟨31, by decide⟩ bs)
    (hlen : bs.length = 32) :
    code.extract' 1661 1693 =
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
      PatchesWindowDisjoint32 1661 1693
        [(2221, ilkBytes), (2369, ilkBytes), (4239, ilkBytes), (4866, ilkBytes),
          (5046, ilkBytes), (6800, ilkBytes), (8747, ilkBytes),
          (1463, vatBytes), (2437, vatBytes), (3145, vatBytes), (4318, vatBytes),
          (4441, vatBytes), (4751, vatBytes), (5115, vatBytes), (6295, vatBytes),
          (7936, vatBytes)] := by
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | hfalse
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
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · cases hfalse
  exact patchRuntime_extract'_exact_split (template := clipperBytecode)
    (pre := [(1510, ilkBytes)])
    (post :=
      [(2221, ilkBytes), (2369, ilkBytes), (4239, ilkBytes), (4866, ilkBytes),
        (5046, ilkBytes), (6800, ilkBytes), (8747, ilkBytes), (1463, vatBytes),
        (2437, vatBytes), (3145, vatBytes), (4318, vatBytes), (4441, vatBytes),
        (4751, vatBytes), (5115, vatBytes), (6295, vatBytes), (7936, vatBytes)])
    (off := 1661) (value := ilkBytes)
    (by
      simpa [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, hilk, hlen,
        List.lookup_cons, ilkBytes, vatBytes] using hpatch)
    hsize hpost (by norm_num) (by norm_num)

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem clipperUpchostVatPush32Decode (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    decode code (⟨1462⟩ : UInt256) =
      some (.Push .PUSH32, some (EVM.Word.ofNat (↑v.vat : Nat), 32)) := by
  unfold decode
  rw [patchRuntime_get?_disjoint hpatch
    (by apply clipperUpchostPatchesWindowDisjoint32Bool v; native_decide)]
  change some (Operation.Push Operation.POp.PUSH32,
      some (uInt256OfByteArray (code.extract' 1463 1495), 32)) =
    some (Operation.Push Operation.POp.PUSH32, some (EVM.Word.ofNat (↑v.vat : Nat), 32))
  rw [clipperUpchostVatPatchPayload v hpatch]
  rw [uInt256OfByteArray_word_toBytesBE]

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem clipperUpchostIlkPush32Decode (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {bs : List UInt8} (hilk : v.ilk = .fixedBytes ⟨31, by decide⟩ bs)
    (hlen : bs.length = 32) :
    decode code (⟨1509⟩ : UInt256) =
      some (.Push .PUSH32, some (EVM.Word.ofNat (fromBytesBigEndian bs), 32)) := by
  unfold decode
  rw [patchRuntime_get?_disjoint hpatch
    (by apply clipperUpchostPatchesWindowDisjoint32Bool v; native_decide)]
  change some (Operation.Push Operation.POp.PUSH32,
      some (uInt256OfByteArray (code.extract' 1510 1542), 32)) =
    some (Operation.Push Operation.POp.PUSH32,
      some (EVM.Word.ofNat (fromBytesBigEndian bs), 32))
  rw [clipperUpchostIlkPatchPayload v hpatch hilk hlen]
  rw [uInt256OfByteArray_word_toBytesBE]

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem clipperUpchostIlkPush32Decode1660 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {bs : List UInt8} (hilk : v.ilk = .fixedBytes ⟨31, by decide⟩ bs)
    (hlen : bs.length = 32) :
    decode code (⟨1660⟩ : UInt256) =
      some (.Push .PUSH32, some (EVM.Word.ofNat (fromBytesBigEndian bs), 32)) := by
  unfold decode
  rw [patchRuntime_get?_disjoint hpatch
    (by apply clipperUpchostPatchesWindowDisjoint32Bool v; native_decide)]
  change some (Operation.Push Operation.POp.PUSH32,
      some (uInt256OfByteArray (code.extract' 1661 1693), 32)) =
    some (Operation.Push Operation.POp.PUSH32,
      some (EVM.Word.ofNat (fromBytesBigEndian bs), 32))
  rw [clipperUpchostIlkPatchPayload1661 v hpatch hilk hlen]
  rw [uInt256OfByteArray_word_toBytesBE]

set_option maxHeartbeats 1000000 in
theorem RD.clipperUpchostToVatIlksExtcodesizeGuard
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {k C : ℕ} {sel : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (rd : RD code ee g s0 ⟨494⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      rdata (cA, σ) k C) :
    ∃ k' C', RD code ee g s0 ⟨1583⟩
      (clipperUpchostVatTarget v :: clipperUpchostVatTarget v ::
        ⟨0⟩ :: ⟨128⟩ :: ⟨36⟩ :: ⟨128⟩ :: ⟨160⟩ :: ⟨164⟩ ::
        clipperVatIlksSelectorWord :: clipperUpchostVatTarget v ::
        ⟨0⟩ :: ⟨502⟩ :: sel :: [])
      (clipperVatIlksCalldataMem (clipperUpchostIlkWord v) solcFreePtrMem)
      (UInt256.ofNat 6) rdata (cA, σ) k' C' := by
  rcases v.ilk_wf with ⟨ilkBs, hilk, hlen⟩
  let vatWord : UInt256 := EVM.Word.ofNat (↑v.vat : Nat)
  let ilkWord : UInt256 := EVM.Word.ofNat (fromBytesBigEndian ilkBs)
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ solcFreePtrMem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (solcFreePtrMem.readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [solcFreePtrMem_size]; decide) (by decide)
      solcFreePtrMem_read64
  have hcallMemSize :
      (clipperVatIlksCalldataMem ilkWord solcFreePtrMem).size = 164 := by
    exact clipperVatIlksCalldataMem_size ilkWord solcFreePtrMem_size
  have hcallRead64 :
      (clipperVatIlksCalldataMem ilkWord solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ := by
    exact clipperVatIlksCalldataMem_read64 ilkWord solcFreePtrMem_size solcFreePtrMem_read64
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (clipperVatIlksCalldataMem ilkWord solcFreePtrMem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((clipperVatIlksCalldataMem ilkWord solcFreePtrMem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hcallMemSize]; decide) (by decide) hcallRead64
  have rd1459 := evm_run rd with [
    raw jumpdest (by clipper_upchost_decode) (by evm_ov),
    raw push2 ⟨502⟩ (by clipper_upchost_decode) (by evm_ov),
    raw push2 ⟨1459⟩ (by clipper_upchost_decode) (by evm_ov),
    raw jump (by clipper_upchost_decode)
      (clipperJumpDestBeforeFirstPatch v hpatch (⟨1459⟩ : UInt256) (by native_decide))
      (by evm_ov),
    raw jumpdest (by clipper_upchost_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_upchost_decode) (by evm_ov)]
  have rd1495 := rd1459.pushConst vatWord (width := 32) (op := .PUSH32)
    (by decide) (by simpa [vatWord] using clipperUpchostVatPush32Decode v hpatch)
    (by evm_ov)
  have rd1509 := evm_run rd1495 with [
    raw push1 ⟨1⟩ (by clipper_upchost_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_upchost_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_upchost_decode) (by evm_ov),
    raw shl (by clipper_upchost_decode) (by evm_ov),
    raw sub (by clipper_upchost_decode) (by evm_ov),
    raw and (by clipper_upchost_decode) (by evm_ov),
    raw push4 clipperVatIlksSelectorWord (by clipper_upchost_decode) (by evm_ov)]
  have rd1542 := rd1509.pushConst ilkWord (width := 32) (op := .PUSH32)
    (by decide)
    (by simpa [ilkWord] using clipperUpchostIlkPush32Decode v hpatch hilk hlen)
    (by evm_ov)
  have rd1583 := evm_run rd1542 with [
    raw push1 ⟨64⟩ (by clipper_upchost_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by clipper_upchost_decode)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw dup3 (by clipper_upchost_decode) (by evm_ov),
    raw push4 ⟨4294967295⟩ (by clipper_upchost_decode) (by evm_ov),
    raw and (by clipper_upchost_decode) (by evm_ov),
    raw push1 ⟨224⟩ (by clipper_upchost_decode) (by evm_ov),
    raw shl (by clipper_upchost_decode) (by evm_ov),
    raw dup2 (by clipper_upchost_decode) (by evm_ov),
    raw mstore 6 (clipperVatIlksSelectorMem solcFreePtrMem) (UInt256.ofNat 5)
      (by clipper_upchost_decode) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by clipper_upchost_decode) (by evm_ov),
    raw add (by clipper_upchost_decode) (by evm_ov),
    raw dup1 (by clipper_upchost_decode) (by evm_ov),
    raw dup3 (by clipper_upchost_decode) (by evm_ov),
    raw dup2 (by clipper_upchost_decode) (by evm_ov),
    raw mstore 3 (clipperVatIlksCalldataMem ilkWord solcFreePtrMem) (UInt256.ofNat 6)
      (by clipper_upchost_decode) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_upchost_decode) (by evm_ov),
    raw add (by clipper_upchost_decode) (by evm_ov),
    raw swap2 (by clipper_upchost_decode) (by evm_ov),
    raw pop (by clipper_upchost_decode) (by evm_ov),
    raw pop (by clipper_upchost_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_upchost_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_upchost_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by clipper_upchost_decode)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw dup1 (by clipper_upchost_decode) (by evm_ov),
    raw dup4 (by clipper_upchost_decode) (by evm_ov),
    raw sub (by clipper_upchost_decode) (by evm_ov),
    raw dup2 (by clipper_upchost_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_upchost_decode) (by evm_ov),
    raw dup8 (by clipper_upchost_decode) (by evm_ov),
    raw dup1 (by clipper_upchost_decode) (by evm_ov)]
  exact ⟨_, _, by
    simpa [vatWord, clipperUpchostVatTarget, clipperVatIlksSelectorWord,
      clipperVatIlksSelectorShifted, clipperVatIlksSelectorMem,
      clipperVatIlksCalldataMem, clipperUpchostIlkWord, hilk, ilkWord, solcAddrMask,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide,
      show UInt256.land (⟨4294967295⟩ : UInt256) clipperVatIlksSelectorWord =
        clipperVatIlksSelectorWord from by native_decide,
      show (⟨128⟩ : UInt256) + ⟨4⟩ = ⟨132⟩ from by native_decide,
      show (⟨132⟩ : UInt256) + ⟨32⟩ = ⟨164⟩ from by native_decide,
      show UInt256.sub (⟨164⟩ : UInt256) ⟨128⟩ = ⟨36⟩ from by native_decide]
      using rd1583⟩

theorem RD.clipperUpchostVatIlksNoCode
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {k C : ℕ} {sel : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (rd : RD code ee g s0 ⟨494⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      rdata (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (clipperUpchostVatTarget v) = ⟨0⟩) :
    RDrev code g s0 := by
  obtain ⟨k', C', rd1583⟩ :=
    RD.clipperUpchostToVatIlksExtcodesizeGuard v hpatch rd
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨1583⟩) (okPc := ⟨1595⟩)
    rd1583 hcodeSize
    (by clipper_upchost_decode) (by clipper_upchost_decode) (by clipper_upchost_decode)
    (by clipper_upchost_decode) (by clipper_upchost_decode) (by clipper_upchost_decode)
    (by clipper_upchost_decode) (by clipper_upchost_decode) (by clipper_upchost_decode)
    (by simp)

theorem clipperEvalVatCodeGuard_false (v : ClipperImmutables) (evm : EVM.State)
    (locals : Store)
    (hnoCode :
      (UInt256.ofNat ((evm.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat =
        0) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)) =
        .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, clipperEvalVat, evalBinaryOp?, EVM.Word.ofNat,
    hnoCode]

theorem clipperEvalVatCodeGuard_true (v : ClipperImmutables) (evm : EVM.State)
    (locals : Store)
    (hcode :
      0 <
        (UInt256.ofNat ((evm.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)) =
        .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, clipperEvalVat, evalBinaryOp?, EVM.Word.ofNat,
    hcode]

theorem clipperUpchostBodyVatNoCode (v : ClipperImmutables) (evm : EVM.State)
    (locals : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnoCode :
      (UInt256.ofNat ((evm.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat =
        0) :
    ExecTransitionBody (config v) (contract v) evm locals (upchostTransition v).body
      .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simp only [upchostTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true hwv
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (clipperEvalVatCodeGuard_false v evm locals hnoCode))

theorem clipperUpchostVatTargetAddress (v : ClipperImmutables) :
    AccountAddress.ofUInt256 (clipperUpchostVatTarget v) = v.vat := by
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
  simpa [clipperUpchostVatTarget, hclean] using clipperAddressOfWordOfNat v.vat

theorem clipperUpchostDogTarget_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    clipperUpchostDogTarget σ I = clipperUpchostDogTarget τ I := by
  have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
  simp [clipperUpchostDogTarget, solcSlotWord, hslot]

theorem clipperEvalDogTarget (v : ClipperImmutables) (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "dog" = none) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.storage dogRef) =
      .ok (.address (AccountAddress.ofUInt256
        (clipperUpchostDogTarget evm.accountMap evm.executionEnv))) := by
  rw [clipperEvalDog v evm locals hbase]
  simp [clipperUpchostDogTarget, solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
    Account.lookupStorage, accountAddress_ofUInt256_eq_ofNat_toNat, u256_land_comm]

theorem clipperEvalDogCodeGuard_false (v : ClipperImmutables) (evm : EVM.State)
    (locals : Store) (hbase : locals.get? "dog" = none)
    (hnoCode :
      (UInt256.ofNat ((evm.lookupAccount
        (AccountAddress.ofUInt256
          (clipperUpchostDogTarget evm.accountMap evm.executionEnv))).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage dogRef)) (.intLit 0)) =
        .ok (.bool false) := by
  have hnoCode' :
      (EVM.Word.ofNat ((evm.lookupAccount
        (AccountAddress.ofUInt256
          (clipperUpchostDogTarget evm.accountMap evm.executionEnv))).option 0
          (fun acc => acc.code.size))).toNat = 0 := by
    simpa using hnoCode
  simp [evalExpr?, EvalResult.bind, bind, clipperEvalDogTarget v evm locals hbase,
    evalBinaryOp?, hnoCode']

theorem clipperEvalDogCodeGuard_true (v : ClipperImmutables) (evm : EVM.State)
    (locals : Store) (hbase : locals.get? "dog" = none)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount
        (AccountAddress.ofUInt256
          (clipperUpchostDogTarget evm.accountMap evm.executionEnv))).option 0
          (fun acc => acc.code.size))).toNat) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage dogRef)) (.intLit 0)) =
        .ok (.bool true) := by
  have hcode' :
      0 < (EVM.Word.ofNat ((evm.lookupAccount
        (AccountAddress.ofUInt256
          (clipperUpchostDogTarget evm.accountMap evm.executionEnv))).option 0
          (fun acc => acc.code.size))).toNat := by
    simpa using hcode
  simp [evalExpr?, EvalResult.bind, bind, clipperEvalDogTarget v evm locals hbase,
    evalBinaryOp?, hcode']

theorem clipperEVMAddressAccountAddress (a : AccountAddress) :
    EVM.address a = a := by
  apply Fin.ext
  simp [EVM.address, EVM.uintN]
  exact Nat.mod_eq_of_lt (by simp [EVM.twoPow, AccountAddress.size])

theorem clipperJumpDest1595 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨1595⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 2000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperJumpDest1615 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨1615⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 2000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperJumpDest1637 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨1637⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 2000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperJumpDest1757 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨1757⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 2000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperJumpDest1777 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨1777⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 2000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperJumpDest1799 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨1799⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 2000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperJumpDest8238 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨8238⟩ : UInt256) = true := by
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

theorem RD.clipperUpchostVatIlksPostCall
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨494⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (clipperUpchostVatTarget v) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hperm : I.perm = true) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (o : ByteArray) (A' : Substate) (k C : ℕ),
      RD code I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1599⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨164⟩ :: clipperVatIlksSelectorWord ::
          clipperUpchostVatTarget v :: ⟨0⟩ :: ⟨502⟩ :: sel :: [])
        (o.write 0 (clipperVatIlksCalldataMem (clipperUpchostIlkWord v) solcFreePtrMem)
          128 (min (⟨160⟩ : UInt256) (UInt256.ofNat o.size)).toNat)
        (UInt256.ofNat 9) o (cA', σ') k C
    ∧ typedCallViaEVM (config v)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address v.vat) "vatIlks" 0 [v.ilk]
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' }, o) true
    ∧ o.size < UInt256.size := by
  obtain ⟨_, _, rd494⟩ := hreach
  obtain ⟨_, _, rd1583⟩ :=
    RD.clipperUpchostToVatIlksExtcodesizeGuard v hpatch rd494
  obtain ⟨gasWord, _, _, rd1598⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨1583⟩) (okPc := ⟨1595⟩)
      rd1583 hcodeSize
      (by clipper_upchost_decode) (by clipper_upchost_decode)
      (by clipper_upchost_decode) (by clipper_upchost_decode)
      (by clipper_upchost_decode) (by clipper_upchost_decode)
      (clipperJumpDest1595 v hpatch)
      (by clipper_upchost_decode) (by clipper_upchost_decode)
      (by clipper_upchost_decode)
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨cA', σ', z, o, A_in, callGas, k1599, C1599, hΘpack, rd1599raw, hosz⟩ :=
    RD.call rd1598 (by clipper_upchost_decode) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, o, A', k1599, C1599, ?_, ?_, hosz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
          (⟨128⟩ : UInt256).toNat (⟨36⟩ : UInt256).toNat)
          (⟨128⟩ : UInt256).toNat (⟨160⟩ : UInt256).toNat) =
          UInt256.ofNat 9 := by
      native_decide
    exact haw ▸ rd1599raw
  · refine callCoincides (cfg := config v)
      (evm := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (name := "vatIlks") (args := [v.ilk])
      (tgt := EVM.address v.vat) (targetWord := clipperUpchostVatTarget v)
      (cA' := cA') (σ' := σ') (A' := A') (A_in := A_in) (z := z)
      (o := o) (g'' := g'') (callGas := callGas)
      (mem := clipperVatIlksCalldataMem (clipperUpchostIlkWord v) solcFreePtrMem)
      (inOff := ⟨128⟩) (inSize := ⟨36⟩) (callPerm := true)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      ?_ (by simpa using clipperVatIlksEncode_eq v) ?_
    · rw [clipperUpchostVatTargetAddress v]
      exact clipperEVMAddressAccountAddress v.vat
    · simpa [initState, hperm] using hΘ

set_option maxHeartbeats 1000000 in
theorem RD.clipperUpchostVatIlksCallDepthLimit
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨494⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (clipperUpchostVatTarget v) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1599⟩
      (⟨0⟩ :: ⟨164⟩ :: clipperVatIlksSelectorWord :: clipperUpchostVatTarget v ::
        ⟨0⟩ :: ⟨502⟩ :: sel :: [])
      (clipperVatIlksCalldataMem (clipperUpchostIlkWord v) solcFreePtrMem)
      (UInt256.ofNat 9) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd494⟩ := hreach
  obtain ⟨_, _, rd1583⟩ :=
    RD.clipperUpchostToVatIlksExtcodesizeGuard v hpatch rd494
  obtain ⟨gasWord, _, _, rd1598⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨1583⟩) (okPc := ⟨1595⟩)
      rd1583 hcodeSize
      (by clipper_upchost_decode) (by clipper_upchost_decode)
      (by clipper_upchost_decode) (by clipper_upchost_decode)
      (by clipper_upchost_decode) (by clipper_upchost_decode)
      (clipperJumpDest1595 v hpatch)
      (by clipper_upchost_decode) (by clipper_upchost_decode)
      (by clipper_upchost_decode)
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨k1599, C1599, rd1599raw⟩ :=
    RD.callDepthLimit rd1598 (by clipper_upchost_decode) hdepth (by evm_ov)
  refine ⟨k1599, C1599, ?_⟩
  have hmin :
      (min (⟨160⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
        (⟨128⟩ : UInt256).toNat (⟨36⟩ : UInt256).toNat)
        (⟨128⟩ : UInt256).toNat (⟨160⟩ : UInt256).toNat) =
        UInt256.ofNat 9 := by
    native_decide
  simpa [hmin, byteArray_write_len_zero, haw] using rd1599raw

theorem RD.clipperUpchostVatIlksCallFailure
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {rest : List UInt256}
    (rd : RD code ee g s0 ⟨1599⟩ (⟨0⟩ :: rest) mem aw o acc k C)
    (hosz : o.size < UInt256.size)
    (hov : rest.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨1599⟩) (okPc := ⟨1615⟩)
    rd (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by clipper_upchost_decode) (by clipper_upchost_decode)
    (by clipper_upchost_decode) (by clipper_upchost_decode)
    (by clipper_upchost_decode) (by clipper_upchost_decode)
    (by clipper_upchost_decode) (by clipper_upchost_decode)
    (by clipper_upchost_decode) (by clipper_upchost_decode)
    (by clipper_upchost_decode) (by clipper_upchost_decode)
    hosz hov

theorem RD.clipperUpchostVatIlksCallSuccessToDecode
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {sel : UInt256}
    (rd : RD code ee g s0 ⟨1599⟩
      (⟨1⟩ :: ⟨164⟩ :: clipperVatIlksSelectorWord :: clipperUpchostVatTarget v ::
        ⟨0⟩ :: ⟨502⟩ :: sel :: [])
      mem aw o acc k C) :
    ∃ k' C', RD code ee g s0 ⟨1617⟩
      (⟨164⟩ :: clipperVatIlksSelectorWord :: clipperUpchostVatTarget v ::
        ⟨0⟩ :: ⟨502⟩ :: sel :: [])
      mem aw o acc k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨1599⟩) (okPc := ⟨1615⟩) rd
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by clipper_upchost_decode) (by clipper_upchost_decode)
    (by clipper_upchost_decode) (by clipper_upchost_decode)
    (by clipper_upchost_decode) (clipperJumpDest1615 v hpatch)
    (by clipper_upchost_decode) (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem RD.clipperUpchostVatIlksReturnDecodeShortReverts
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {out : ByteArray} {k C : ℕ} {sel : UInt256}
    (rd1617 : RD code ee g s0 ⟨1617⟩
      (⟨164⟩ :: clipperVatIlksSelectorWord :: clipperUpchostVatTarget v ::
        ⟨0⟩ :: ⟨502⟩ :: sel :: [])
      (clipperVatIlksPostCallMem v out) (UInt256.ofNat 9) out acc k C)
    (hshort : out.size < 160) (hout : out.size < UInt256.size) :
    RDrev code g s0 := by
  have rdPop0 := RD.pop rd1617 (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPop1 := RD.pop rdPop0 (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPop2 := RD.pop rdPop1 (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPush64 := RD.push1 rdPop2 ⟨64⟩ (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdMload64 := RD.mload 0 ⟨128⟩ (UInt256.ofNat 9) rdPush64
    (by clipper_upchost_decode)
    mem_cost
    (clipperVatIlksPostCallMem_mload64 v out hshort hout)
    (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdReturndatasize := RD.returndatasize rdMload64 (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPush160 := RD.push1 rdReturndatasize ⟨160⟩ (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdDup2 := RD.dup2 rdPush160 (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdLt := RD.lt rdDup2 (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨160⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide,
      ulit_toNat' out.size hout]
    exact hshort
  have rdIszero := RD.iszero rdLt (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPushOk := RD.push2 rdIszero ⟨1637⟩ (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hcond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat out.size) (⟨160⟩ : UInt256)) =
        ⟨0⟩ := by
    rw [hlt]
    decide
  have rdFallthrough := RD.jumpiNT rdPushOk (by clipper_upchost_decode) hcond
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact RD.solcPush1Dup1Revert0 rdFallthrough
    (by clipper_upchost_decode) (by clipper_upchost_decode)
    (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem RD.clipperUpchostVatIlksReturnDecodeOk
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {out : ByteArray} {k C : ℕ} {sel : UInt256}
    (rd1617 : RD code ee g s0 ⟨1617⟩
      (⟨164⟩ :: clipperVatIlksSelectorWord :: clipperUpchostVatTarget v ::
        ⟨0⟩ :: ⟨502⟩ :: sel :: [])
      (clipperVatIlksPostCallMem v out) (UInt256.ofNat 9) out acc k C)
    (hlo : 160 ≤ out.size) (hout : out.size < UInt256.size) :
    ∃ k' C', RD code ee g s0 ⟨1643⟩
      (clipperVatIlksDustWord out :: ⟨0⟩ :: ⟨502⟩ :: sel :: [])
      (clipperVatIlksPostCallMem v out) (UInt256.ofNat 9) out acc k' C' := by
  have rdPop0 := RD.pop rd1617 (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPop1 := RD.pop rdPop0 (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPop2 := RD.pop rdPop1 (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPush64 := RD.push1 rdPop2 ⟨64⟩ (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdMload64 := RD.mload 0 ⟨128⟩ (UInt256.ofNat 9) rdPush64
    (by clipper_upchost_decode)
    mem_cost
    (clipperVatIlksPostCallMem_mload64_long v out hlo hout)
    (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdReturndatasize := RD.returndatasize rdMload64 (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPush160 := RD.push1 rdReturndatasize ⟨160⟩ (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdDup2 := RD.dup2 rdPush160 (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdLt := RD.lt rdDup2 (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨160⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide,
      ulit_toNat' out.size hout]
    exact hlo
  have rdIszero := RD.iszero rdLt (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPushOk := RD.push2 rdIszero ⟨1637⟩ (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hcond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat out.size) (⟨160⟩ : UInt256)) ≠
        ⟨0⟩ := by
    rw [hlt]
    decide
  have rdJumpi := RD.jumpiT rdPushOk (by clipper_upchost_decode) hcond
    (clipperJumpDest1637 v hpatch)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdJumpdest := RD.jumpdest rdJumpi (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPopLen := RD.pop rdJumpdest (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPush128 := RD.push1 rdPopLen ⟨128⟩ (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdAdd := RD.add rdPush128 (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdMload256 := RD.mload 0 (clipperVatIlksDustWord out) (UInt256.ofNat 9) rdAdd
    (by clipper_upchost_decode)
    mem_cost
    (clipperVatIlksPostCallMem_mload256_long v out hlo hout)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa using rdMload256⟩

set_option maxHeartbeats 1000000 in
theorem RD.clipperUpchostToDogChopExtcodesizeGuard
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {out : ByteArray} {k C : ℕ} {sel : UInt256}
    (rd1643 : RD code ee g s0 ⟨1643⟩
      (clipperVatIlksDustWord out :: ⟨0⟩ :: ⟨502⟩ :: sel :: [])
      (clipperVatIlksPostCallMem v out) (UInt256.ofNat 9) out (cA, σ) k C)
    (hlo : 160 ≤ out.size) (hout : out.size < UInt256.size) :
    ∃ k' C', RD code ee g s0 ⟨1745⟩
      (clipperUpchostDogTarget σ ee :: clipperUpchostDogTarget σ ee ::
        ⟨0⟩ :: ⟨128⟩ :: ⟨36⟩ :: ⟨128⟩ :: ⟨32⟩ :: ⟨164⟩ ::
        clipperDogChopSelectorWord :: clipperUpchostDogTarget σ ee ::
        clipperVatIlksDustWord out :: ⟨1806⟩ :: clipperVatIlksDustWord out ::
        ⟨502⟩ :: sel :: [])
      (clipperDogChopCalldataMem v out) (UInt256.ofNat 9) out (cA, σ) k' C' := by
  have rdPushDogSlot := RD.push1 rd1643 ⟨1⟩ (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rdSloadRaw⟩ := rdPushDogSlot.sload (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hrdSload : ∃ k' C', RD code ee g s0 ⟨1646⟩
      (solcSlotWord σ ee ⟨1⟩ :: clipperVatIlksDustWord out ::
        ⟨0⟩ :: ⟨502⟩ :: sel :: [])
      (clipperVatIlksPostCallMem v out) (UInt256.ofNat 9) out (cA, σ) k' C' :=
    ⟨_, _, by simpa [solcSlotWord] using rdSloadRaw⟩
  obtain ⟨_, _, rdSload⟩ := hrdSload
  have rdPush64 := RD.push1 rdSload ⟨64⟩ (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdDup64 := RD.dup1 rdPush64 (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdMload64a := RD.mload 0 ⟨128⟩ (UInt256.ofNat 9) rdDup64
    (by clipper_upchost_decode)
    mem_cost
    (clipperVatIlksPostCallMem_mload64_long v out hlo hout)
    (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPushSelectorSeed := RD.push4 rdMload64a clipperDogChopSelectorSeed
    (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPushShift := RD.push1 rdPushSelectorSeed ⟨227⟩ (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdShl := RD.shl rdPushShift (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdDupFree0 := RD.dup2 rdShl (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdStoreSelector := RD.mstore 0
    (clipperDogChopSelectorMem (clipperVatIlksPostCallMem v out)) (UInt256.ofNat 9)
    rdDupFree0 (by clipper_upchost_decode)
    mem_cost
    (by rfl)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  rcases v.ilk_wf with ⟨ilkBs, hilk, hlen⟩
  have rdPushIlk := rdStoreSelector.pushConst (clipperUpchostIlkWord v)
    (width := 32) (op := .PUSH32) (by decide)
    (by
      simpa [clipperUpchostIlkWord, hilk] using
        clipperUpchostIlkPush32Decode1660 v hpatch hilk hlen)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPush4 := RD.push1 rdPushIlk ⟨4⟩ (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdDupFree1 := RD.dup3 rdPush4 (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdAddArgOff := RD.add rdDupFree1 (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdStoreIlk := RD.mstore 0 (clipperDogChopCalldataMem v out) (UInt256.ofNat 9)
    rdAddArgOff (by clipper_upchost_decode)
    mem_cost
    (by
      rw [show (((⟨128⟩ : UInt256) + ⟨4⟩).toNat = 132) from by native_decide]
      rfl)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdSwap1a := RD.swap1 rdStoreIlk (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdMload64b := RD.mload 0 ⟨128⟩ (UInt256.ofNat 9) rdSwap1a
    (by clipper_upchost_decode)
    mem_cost
    (clipperDogChopCalldataMem_mload64_long v out hlo hout)
    (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdSwap3a := RD.swap3 rdMload64b (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdSwap4a := RD.swap4 rdSwap3a (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPop := RD.pop rdSwap4a (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPushRet := RD.push2 rdPop ⟨1806⟩ (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdSwap3b := RD.swap3 rdPushRet (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdDupDust := RD.dup5 rdSwap3b (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdSwap3c := RD.swap3 rdDupDust (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPushOne0 := RD.push1 rdSwap3c ⟨1⟩ (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPushOne1 := RD.push1 rdPushOne0 ⟨1⟩ (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPush160 := RD.push1 rdPushOne1 ⟨160⟩ (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdMaskBase := RD.shl rdPush160 (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdMask := RD.sub rdMaskBase (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdAndRaw := RD.and rdMask (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hrdAnd : ∃ k' C', RD code ee g s0 ⟨1718⟩
      (clipperUpchostDogTarget σ ee :: ⟨128⟩ :: ⟨128⟩ ::
        clipperVatIlksDustWord out :: ⟨1806⟩ :: clipperVatIlksDustWord out ::
        ⟨502⟩ :: sel :: [])
      (clipperDogChopCalldataMem v out) (UInt256.ofNat 9) out (cA, σ) k' C' :=
    ⟨_, _, by
      simpa [clipperUpchostDogTarget,
        show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide] using rdAndRaw⟩
  obtain ⟨_, _, rdAnd⟩ := hrdAnd
  have rdSwap2a := RD.swap2 rdAnd (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPushSelector := RD.push4 rdSwap2a clipperDogChopSelectorWord
    (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdSwap2b := RD.swap2 rdPushSelector (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPush36 := RD.push1 rdSwap2b ⟨36⟩ (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdDup36 := RD.dup1 rdPush36 (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdDupFree2 := RD.dup4 rdDup36 (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdAddOutOffRaw := RD.add rdDupFree2 (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hrdAddOutOff : ∃ k' C', RD code ee g s0 ⟨1730⟩
      (⟨164⟩ :: ⟨36⟩ :: ⟨128⟩ :: ⟨128⟩ ::
        clipperDogChopSelectorWord :: clipperUpchostDogTarget σ ee ::
        clipperVatIlksDustWord out :: ⟨1806⟩ :: clipperVatIlksDustWord out ::
        ⟨502⟩ :: sel :: [])
      (clipperDogChopCalldataMem v out) (UInt256.ofNat 9) out (cA, σ) k' C' :=
    ⟨_, _, by simpa using rdAddOutOffRaw⟩
  obtain ⟨_, _, rdAddOutOff⟩ := hrdAddOutOff
  have rdSwap3d := RD.swap3 rdAddOutOff (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPush32 := RD.push1 rdSwap3d ⟨32⟩ (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdSwap3e := RD.swap3 rdPush32 (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdSwap2c := RD.swap2 rdSwap3e (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdSwap1b := RD.swap1 rdSwap2c (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdDupFree3 := RD.dup3 rdSwap1b (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdSwap1c := RD.swap1 rdDupFree3 (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdSubPtrRaw := RD.sub rdSwap1c (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hrdSubPtr : ∃ k' C', RD code ee g s0 ⟨1739⟩
      (⟨0⟩ :: ⟨36⟩ :: ⟨128⟩ :: ⟨32⟩ :: ⟨164⟩ ::
        clipperDogChopSelectorWord :: clipperUpchostDogTarget σ ee ::
        clipperVatIlksDustWord out :: ⟨1806⟩ :: clipperVatIlksDustWord out ::
        ⟨502⟩ :: sel :: [])
      (clipperDogChopCalldataMem v out) (UInt256.ofNat 9) out (cA, σ) k' C' :=
    ⟨_, _, by simpa using rdSubPtrRaw⟩
  obtain ⟨_, _, rdSubPtr⟩ := hrdSubPtr
  have rdAddInSizeRaw := RD.add rdSubPtr (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hrdAddInSize : ∃ k' C', RD code ee g s0 ⟨1740⟩
      (⟨36⟩ :: ⟨128⟩ :: ⟨32⟩ :: ⟨164⟩ ::
        clipperDogChopSelectorWord :: clipperUpchostDogTarget σ ee ::
        clipperVatIlksDustWord out :: ⟨1806⟩ :: clipperVatIlksDustWord out ::
        ⟨502⟩ :: sel :: [])
      (clipperDogChopCalldataMem v out) (UInt256.ofNat 9) out (cA, σ) k' C' :=
    ⟨_, _, by simpa using rdAddInSizeRaw⟩
  obtain ⟨_, _, rdAddInSize⟩ := hrdAddInSize
  have rdDupInOff := RD.dup2 rdAddInSize (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPushZero := RD.push1 rdDupInOff ⟨0⟩ (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdDupTarget := RD.dup8 rdPushZero (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdDupTarget2 := RD.dup1 rdDupTarget (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa using rdDupTarget2⟩

theorem RD.clipperUpchostDogChopNoCode
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {out : ByteArray} {k C : ℕ} {sel : UInt256}
    (rd1643 : RD code ee g s0 ⟨1643⟩
      (clipperVatIlksDustWord out :: ⟨0⟩ :: ⟨502⟩ :: sel :: [])
      (clipperVatIlksPostCallMem v out) (UInt256.ofNat 9) out (cA, σ) k C)
    (hlo : 160 ≤ out.size) (hout : out.size < UInt256.size)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (clipperUpchostDogTarget σ ee) = ⟨0⟩) :
    RDrev code g s0 := by
  obtain ⟨_, _, rd1745⟩ :=
    RD.clipperUpchostToDogChopExtcodesizeGuard v hpatch rd1643 hlo hout
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨1745⟩) (okPc := ⟨1757⟩)
    rd1745 hcodeSize
    (by clipper_upchost_decode) (by clipper_upchost_decode) (by clipper_upchost_decode)
    (by clipper_upchost_decode) (by clipper_upchost_decode) (by clipper_upchost_decode)
    (by clipper_upchost_decode) (by clipper_upchost_decode) (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.clipperUpchostDogChopPostCall
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ σ₀ A I} {g : Sat256} {cA_vat : Batteries.RBSet AccountAddress compare}
    {σ_vat : AccountMap} {A_vat : Substate} {out : ByteArray} {k C : ℕ} {sel : UInt256}
    (rd1643 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨1643⟩
      (clipperVatIlksDustWord out :: ⟨0⟩ :: ⟨502⟩ :: sel :: [])
      (clipperVatIlksPostCallMem v out) (UInt256.ofNat 9) out (cA_vat, σ_vat) k C)
    (hlo : 160 ≤ out.size) (hout : out.size < UInt256.size)
    (hcodeSizeDog :
      Reasoning.Theory.extCodeSizeWord σ_vat
        (clipperUpchostDogTarget σ_vat I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true) :
    ∃ (cA_dog : Batteries.RBSet AccountAddress compare) (σ_dog : AccountMap)
      (zDog : Bool) (outDog : ByteArray) (A_dog : Substate) (k' C' : ℕ),
      RD code I g (initState cA gh bl σ σ₀ g A I) ⟨1761⟩
        ((if zDog then ⟨1⟩ else ⟨0⟩) :: ⟨164⟩ :: clipperDogChopSelectorWord ::
          clipperUpchostDogTarget σ_vat I :: clipperVatIlksDustWord out ::
          ⟨1806⟩ :: clipperVatIlksDustWord out :: ⟨502⟩ :: sel :: [])
        (outDog.write 0 (clipperDogChopCalldataMem v out) 128
          (min (⟨32⟩ : UInt256) (UInt256.ofNat outDog.size)).toNat)
        (UInt256.ofNat
          (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
            (⟨128⟩ : UInt256).toNat (⟨36⟩ : UInt256).toNat)
            (⟨128⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat))
        outDog (cA_dog, σ_dog) k' C' ∧
      typedCallViaEVM (config v)
        { initState cA gh bl σ σ₀ g A I with
          accountMap := σ_vat
          substate := A_vat
          createdAccounts := cA_vat }
        (EVM.address (AccountAddress.ofUInt256 (clipperUpchostDogTarget σ_vat I)))
        "chop" 0 [v.ilk]
        (zDog,
          { initState cA gh bl σ σ₀ g A I with
            accountMap := σ_dog
            substate := A_dog
            createdAccounts := cA_dog },
          outDog) true ∧
      outDog.size < UInt256.size := by
  obtain ⟨_, _, rd1745⟩ :=
    RD.clipperUpchostToDogChopExtcodesizeGuard v hpatch rd1643 hlo hout
  obtain ⟨_, _, _, rd1760⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨1745⟩) (okPc := ⟨1757⟩)
      rd1745 hcodeSizeDog
      (by clipper_upchost_decode) (by clipper_upchost_decode)
      (by clipper_upchost_decode) (by clipper_upchost_decode)
      (by clipper_upchost_decode) (by clipper_upchost_decode)
      (clipperJumpDest1757 v hpatch)
      (by clipper_upchost_decode) (by clipper_upchost_decode)
      (by clipper_upchost_decode)
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨cA_dog, σ_dog, zDog, outDog, A_in, callGas, k1761, C1761, hΘpack,
      rd1761raw, houtDogSize⟩ :=
    RD.call rd1760 (by clipper_upchost_decode) hdepth (by evm_ov)
  obtain ⟨g'', A_dog, hΘ⟩ := hΘpack
  refine ⟨cA_dog, σ_dog, zDog, outDog, A_dog, k1761, C1761, ?_, ?_, houtDogSize⟩
  · exact rd1761raw
  · let evmVat : EVM.State :=
      { initState cA gh bl σ σ₀ g A I with
        accountMap := σ_vat
        substate := A_vat
        createdAccounts := cA_vat }
    refine callCoincides (cfg := config v)
      (evm := evmVat)
      (name := "chop") (args := [v.ilk])
      (tgt := EVM.address (AccountAddress.ofUInt256 (clipperUpchostDogTarget σ_vat I)))
      (targetWord := clipperUpchostDogTarget σ_vat I)
      (cA' := cA_dog) (σ' := σ_dog) (A' := A_dog) (A_in := A_in)
      (z := zDog) (o := outDog) (g'' := g'') (callGas := callGas)
      (mem := clipperDogChopCalldataMem v out)
      (inOff := ⟨128⟩) (inSize := ⟨36⟩) (callPerm := true)
      (fun h => absurd hdepth (by
        have hI : I.depth = (1024 : Fin 1025) := by
          simpa [evmVat, initState] using h
        rw [hI]
        decide))
      ?_ (by simpa using clipperDogChopEncode_eq v out hlo hout) ?_
    · exact clipperEVMAddressAccountAddress
        (AccountAddress.ofUInt256 (clipperUpchostDogTarget σ_vat I))
    · simpa [evmVat, initState, hperm] using hΘ

theorem RD.clipperUpchostDogChopCallFailure
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {rest : List UInt256}
    (rd : RD code ee g s0 ⟨1761⟩ (⟨0⟩ :: rest) mem aw o acc k C)
    (hosz : o.size < UInt256.size)
    (hov : rest.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨1761⟩) (okPc := ⟨1777⟩)
    rd (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by clipper_upchost_decode) (by clipper_upchost_decode)
    (by clipper_upchost_decode) (by clipper_upchost_decode)
    (by clipper_upchost_decode) (by clipper_upchost_decode)
    (by clipper_upchost_decode) (by clipper_upchost_decode)
    (by clipper_upchost_decode) (by clipper_upchost_decode)
    (by clipper_upchost_decode) (by clipper_upchost_decode)
    hosz hov

theorem RD.clipperUpchostDogChopCallSuccessToDecode
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {sel target dust : UInt256}
    (rd : RD code ee g s0 ⟨1761⟩
      (⟨1⟩ :: ⟨164⟩ :: clipperDogChopSelectorWord :: target :: dust ::
        ⟨1806⟩ :: dust :: ⟨502⟩ :: sel :: [])
      mem aw o acc k C) :
    ∃ k' C', RD code ee g s0 ⟨1779⟩
      (⟨164⟩ :: clipperDogChopSelectorWord :: target :: dust ::
        ⟨1806⟩ :: dust :: ⟨502⟩ :: sel :: [])
      mem aw o acc k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨1761⟩) (okPc := ⟨1777⟩) rd
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by clipper_upchost_decode) (by clipper_upchost_decode)
    (by clipper_upchost_decode) (by clipper_upchost_decode)
    (by clipper_upchost_decode) (clipperJumpDest1777 v hpatch)
    (by clipper_upchost_decode) (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem RD.clipperUpchostDogChopReturnDecodeShortReverts
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {out outDog : ByteArray} {k C : ℕ} {sel target dust : UInt256}
    (rd1779 : RD code ee g s0 ⟨1779⟩
      (⟨164⟩ :: clipperDogChopSelectorWord :: target :: dust ::
        ⟨1806⟩ :: dust :: ⟨502⟩ :: sel :: [])
      (clipperDogChopPostCallMem v out outDog) clipperDogChopPostCallAw outDog acc k C)
    (hlo : 160 ≤ out.size) (hout : out.size < UInt256.size)
    (hshortDog : outDog.size < 32) (houtDog : outDog.size < UInt256.size) :
    RDrev code g s0 := by
  have rdPop0 := RD.pop rd1779 (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPop1 := RD.pop rdPop0 (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPop2 := RD.pop rdPop1 (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPush64 := RD.push1 rdPop2 ⟨64⟩ (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdMload64 := RD.mload 0 ⟨128⟩ clipperDogChopPostCallAw rdPush64
    (by clipper_upchost_decode)
    mem_cost
    (clipperDogChopPostCallMem_mload64 v out outDog hlo hout houtDog)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdReturndatasize := RD.returndatasize rdMload64 (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPush32 := RD.push1 rdReturndatasize ⟨32⟩ (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdDup2 := RD.dup2 rdPush32 (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdLt := RD.lt rdDup2 (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hlt : UInt256.lt (UInt256.ofNat outDog.size) (⟨32⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      ulit_toNat' outDog.size houtDog]
    exact hshortDog
  have rdIszero := RD.iszero rdLt (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPushOk := RD.push2 rdIszero ⟨1799⟩ (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hcond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat outDog.size) (⟨32⟩ : UInt256)) =
        ⟨0⟩ := by
    rw [hlt]
    decide
  have rdFallthrough := RD.jumpiNT rdPushOk (by clipper_upchost_decode) hcond
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact RD.solcPush1Dup1Revert0 rdFallthrough
    (by clipper_upchost_decode) (by clipper_upchost_decode)
    (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem RD.clipperUpchostDogChopReturnDecodeOk
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {out outDog : ByteArray} {k C : ℕ} {sel target dust : UInt256}
    (rd1779 : RD code ee g s0 ⟨1779⟩
      (⟨164⟩ :: clipperDogChopSelectorWord :: target :: dust ::
        ⟨1806⟩ :: dust :: ⟨502⟩ :: sel :: [])
      (clipperDogChopPostCallMem v out outDog) clipperDogChopPostCallAw outDog acc k C)
    (hlo : 160 ≤ out.size) (hout : out.size < UInt256.size)
    (hloDog : 32 ≤ outDog.size) (houtDog : outDog.size < UInt256.size) :
    ∃ k' C', RD code ee g s0 ⟨8238⟩
      (clipperDogChopWord outDog :: dust :: ⟨1806⟩ :: dust :: ⟨502⟩ :: sel :: [])
      (clipperDogChopPostCallMem v out outDog) clipperDogChopPostCallAw outDog acc k' C' := by
  have rdPop0 := RD.pop rd1779 (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPop1 := RD.pop rdPop0 (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPop2 := RD.pop rdPop1 (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPush64 := RD.push1 rdPop2 ⟨64⟩ (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdMload64 := RD.mload 0 ⟨128⟩ clipperDogChopPostCallAw rdPush64
    (by clipper_upchost_decode)
    mem_cost
    (clipperDogChopPostCallMem_mload64 v out outDog hlo hout houtDog)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdReturndatasize := RD.returndatasize rdMload64 (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPush32 := RD.push1 rdReturndatasize ⟨32⟩ (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdDup2 := RD.dup2 rdPush32 (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdLt := RD.lt rdDup2 (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hlt : UInt256.lt (UInt256.ofNat outDog.size) (⟨32⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      ulit_toNat' outDog.size houtDog]
    exact hloDog
  have rdIszero := RD.iszero rdLt (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPushOk := RD.push2 rdIszero ⟨1799⟩ (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hcond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat outDog.size) (⟨32⟩ : UInt256)) ≠
        ⟨0⟩ := by
    rw [hlt]
    decide
  have rdJumpi := RD.jumpiT rdPushOk (by clipper_upchost_decode) hcond
    (clipperJumpDest1799 v hpatch)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdJumpdest := RD.jumpdest rdJumpi (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPopLen := RD.pop rdJumpdest (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdMload128 := RD.mload 0 (clipperDogChopWord outDog) clipperDogChopPostCallAw
    rdPopLen (by clipper_upchost_decode) mem_cost
    (clipperDogChopPostCallMem_mload128 v out outDog hlo hout hloDog houtDog)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPushWmul := RD.push2 rdMload128 ⟨8238⟩ (by clipper_upchost_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, rdPushWmul.jump (by clipper_upchost_decode) (clipperJumpDest8238 v hpatch)
    (by simp only [List.length_cons, List.length_nil]; omega)⟩

theorem clipperExtCodeSizeWord_ne_zero_lookup_code_pos {σ : AccountMap} {target : UInt256}
    {addr : AccountAddress}
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hne : Reasoning.Theory.extCodeSizeWord σ target ≠ ⟨0⟩) :
    0 < (UInt256.ofNat ((σ.find? addr).option 0 (fun acc => acc.code.size))).toNat := by
  subst addr
  unfold Reasoning.Theory.extCodeSizeWord at hne
  cases hacc : σ.find? (AccountAddress.ofUInt256 target) with
  | none =>
      exfalso
      exact hne (by simp [hacc, Option.option])
  | some acc =>
      have hwordNe : UInt256.ofNat acc.code.size ≠ (⟨0⟩ : UInt256) := by
        intro hzero
        exact hne (by simpa [hacc] using hzero)
      have htoNatNe : (UInt256.ofNat acc.code.size).toNat ≠ 0 := by
        intro hzeroNat
        apply hwordNe
        cases hword : UInt256.ofNat acc.code.size with
        | mk val =>
            cases val using Fin.cases
            · rfl
            · simp [UInt256.toNat, hword] at hzeroNat
      simpa [hacc] using Nat.pos_of_ne_zero htoNatNe

theorem clipperUpchostBodyVatIlksCallFailure (v : ClipperImmutables) (evm evmVat : EVM.State)
    (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hvatCode :
      0 < (UInt256.ofNat ((evm.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address v.vat) "vatIlks" 0 [v.ilk]
        (false, evmVat, out) true) :
    ExecTransitionBody (config v) (contract v) evm ∅ (upchostTransition v).body
      .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simp only [upchostTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true hwv
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact clipperEvalVatCodeGuard_true v evm ∅ hvatCode
  exact ExecBlock.consRevert
    (ExecStmt.externalCallFailure (clipperEvalVat v evm ∅) (by simp [evalExpr?, pure])
      (clipperEvalIlkArg v evm ∅) hcall)

theorem clipperUpchostBodyVatIlksDecodeRevert (v : ClipperImmutables) (evm evmVat : EVM.State)
    (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hvatCode :
      0 < (UInt256.ofNat ((evm.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address v.vat) "vatIlks" 0 [v.ilk]
        (true, evmVat, out) true)
    (hdec : (config v).externalABI.decode? "vatIlks" out = none) :
    ExecTransitionBody (config v) (contract v) evm ∅ (upchostTransition v).body
      .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simp only [upchostTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true hwv
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact clipperEvalVatCodeGuard_true v evm ∅ hvatCode
  exact ExecBlock.consRevert
    (ExecStmt.externalCallReturnDecodeRevert (clipperEvalVat v evm ∅)
      (by simp [evalExpr?, pure]) (clipperEvalIlkArg v evm ∅) hcall hdec)

theorem clipperEvalVatIlkDust (v : ClipperImmutables) (evm : EVM.State)
    (out : ByteArray) :
    evalExpr? (config v) { contract := contract v, locals := clipperUpchostVatIlkLocals out }
      evm (.tupleGet (.var "vatIlk") 4) =
      .ok (.int (Int.ofNat (clipperVatIlksDustWord out).toNat)) := by
  have hvar :
      evalExpr? (config v)
        { contract := contract v, locals := clipperUpchostVatIlkLocals out }
        evm (.var "vatIlk") =
        .ok (collapseReturns (clipperVatIlksValues out)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
      ((clipperUpchostVatIlkLocals out).get? "vatIlk") =
        .ok (collapseReturns (clipperVatIlksValues out))
    rw [clipperUpchostVatIlkLocals, store_get_self]
    simp [EvalResult.ofOption]
  rw [evalExpr?]
  simp [hvar, tupleGetValue?, EvalResult.bind, bind, collapseReturns]

theorem clipperUpchostDustLocals_get_dog (out : ByteArray) :
    (clipperUpchostDustLocals out).get? "dog" = none := by
  rw [clipperUpchostDustLocals, store_get_ne _ _ (by decide),
    clipperUpchostVatIlkLocals, store_get_ne _ _ (by decide)]
  simp

theorem clipperUpchostBodyDogChopNoCode (v : ClipperImmutables) (evm evmVat : EVM.State)
    (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hvatCode :
      0 < (UInt256.ofNat ((evm.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address v.vat) "vatIlks" 0 [v.ilk]
        (true, evmVat, out) true)
    (hdec : (config v).externalABI.decode? "vatIlks" out = some (clipperVatIlksValues out))
    (hnoDogCode :
      (UInt256.ofNat ((evmVat.lookupAccount
        (AccountAddress.ofUInt256
          (clipperUpchostDogTarget evmVat.accountMap evmVat.executionEnv))).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    ExecTransitionBody (config v) (contract v) evm ∅ (upchostTransition v).body
      .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simp only [upchostTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true hwv
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact clipperEvalVatCodeGuard_true v evm ∅ hvatCode
  refine ExecBlock.consNormal
    (solm' := { contract := contract v, locals := clipperUpchostVatIlkLocals out })
    (evm' := evmVat) ?_ ?_
  · simpa [clipperUpchostVatIlkLocals] using
      (ExecStmt.externalCallSuccess (clipperEvalVat v evm ∅) (by simp [evalExpr?, pure])
        (clipperEvalIlkArg v evm ∅) hcall hdec)
  refine ExecBlock.consNormal
    (solm' := { contract := contract v, locals := clipperUpchostDustLocals out })
    (evm' := evmVat) ?_ ?_
  · simpa [clipperUpchostVatIlkLocals, clipperUpchostDustLocals] using
      (ExecStmt.letDecl
        (cfg := config v)
        (solm := { contract := contract v, locals := clipperUpchostVatIlkLocals out })
        (evm := evmVat)
        (name := "_dust")
        (ty := some uint256)
        (expr := .tupleGet (.var "vatIlk") 4)
        (value := .int (Int.ofNat (clipperVatIlksDustWord out).toNat))
        (clipperEvalVatIlkDust v evmVat out))
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (clipperEvalDogCodeGuard_false v evmVat
      (clipperUpchostDustLocals out) (clipperUpchostDustLocals_get_dog out) hnoDogCode))

theorem clipperUpchostBodyDogChopCallFailure (v : ClipperImmutables)
    (evm evmVat evmDog : EVM.State) (out outDog : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hvatCode :
      0 < (UInt256.ofNat ((evm.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallVat :
      typedCallViaEVM (config v) evm (EVM.address v.vat) "vatIlks" 0 [v.ilk]
        (true, evmVat, out) true)
    (hdecVat : (config v).externalABI.decode? "vatIlks" out = some (clipperVatIlksValues out))
    (hdogCode :
      0 < (UInt256.ofNat ((evmVat.lookupAccount
        (AccountAddress.ofUInt256
          (clipperUpchostDogTarget evmVat.accountMap evmVat.executionEnv))).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDog :
      typedCallViaEVM (config v) evmVat
        (EVM.address (AccountAddress.ofUInt256
          (clipperUpchostDogTarget evmVat.accountMap evmVat.executionEnv)))
        "chop" 0 [v.ilk] (false, evmDog, outDog) true) :
    ExecTransitionBody (config v) (contract v) evm ∅ (upchostTransition v).body
      .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simp only [upchostTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true hwv
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact clipperEvalVatCodeGuard_true v evm ∅ hvatCode
  refine ExecBlock.consNormal
    (solm' := { contract := contract v, locals := clipperUpchostVatIlkLocals out })
    (evm' := evmVat) ?_ ?_
  · simpa [clipperUpchostVatIlkLocals] using
      (ExecStmt.externalCallSuccess (clipperEvalVat v evm ∅) (by simp [evalExpr?, pure])
        (clipperEvalIlkArg v evm ∅) hcallVat hdecVat)
  refine ExecBlock.consNormal
    (solm' := { contract := contract v, locals := clipperUpchostDustLocals out })
    (evm' := evmVat) ?_ ?_
  · simpa [clipperUpchostVatIlkLocals, clipperUpchostDustLocals] using
      (ExecStmt.letDecl
        (cfg := config v)
        (solm := { contract := contract v, locals := clipperUpchostVatIlkLocals out })
        (evm := evmVat)
        (name := "_dust")
        (ty := some uint256)
        (expr := .tupleGet (.var "vatIlk") 4)
        (value := .int (Int.ofNat (clipperVatIlksDustWord out).toNat))
        (clipperEvalVatIlkDust v evmVat out))
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact clipperEvalDogCodeGuard_true v evmVat (clipperUpchostDustLocals out)
      (clipperUpchostDustLocals_get_dog out) hdogCode
  exact ExecBlock.consRevert
    (ExecStmt.externalCallFailure
      (clipperEvalDogTarget v evmVat (clipperUpchostDustLocals out)
        (clipperUpchostDustLocals_get_dog out))
      (by simp [evalExpr?, pure])
      (clipperEvalIlkArg v evmVat (clipperUpchostDustLocals out))
      hcallDog)

theorem clipperUpchostBodyDogChopDecodeRevert (v : ClipperImmutables)
    (evm evmVat evmDog : EVM.State) (out outDog : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hvatCode :
      0 < (UInt256.ofNat ((evm.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallVat :
      typedCallViaEVM (config v) evm (EVM.address v.vat) "vatIlks" 0 [v.ilk]
        (true, evmVat, out) true)
    (hdecVat : (config v).externalABI.decode? "vatIlks" out = some (clipperVatIlksValues out))
    (hdogCode :
      0 < (UInt256.ofNat ((evmVat.lookupAccount
        (AccountAddress.ofUInt256
          (clipperUpchostDogTarget evmVat.accountMap evmVat.executionEnv))).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDog :
      typedCallViaEVM (config v) evmVat
        (EVM.address (AccountAddress.ofUInt256
          (clipperUpchostDogTarget evmVat.accountMap evmVat.executionEnv)))
        "chop" 0 [v.ilk] (true, evmDog, outDog) true)
    (hdecDog : (config v).externalABI.decode? "chop" outDog = none) :
    ExecTransitionBody (config v) (contract v) evm ∅ (upchostTransition v).body
      .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simp only [upchostTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true hwv
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact clipperEvalVatCodeGuard_true v evm ∅ hvatCode
  refine ExecBlock.consNormal
    (solm' := { contract := contract v, locals := clipperUpchostVatIlkLocals out })
    (evm' := evmVat) ?_ ?_
  · simpa [clipperUpchostVatIlkLocals] using
      (ExecStmt.externalCallSuccess (clipperEvalVat v evm ∅) (by simp [evalExpr?, pure])
        (clipperEvalIlkArg v evm ∅) hcallVat hdecVat)
  refine ExecBlock.consNormal
    (solm' := { contract := contract v, locals := clipperUpchostDustLocals out })
    (evm' := evmVat) ?_ ?_
  · simpa [clipperUpchostVatIlkLocals, clipperUpchostDustLocals] using
      (ExecStmt.letDecl
        (cfg := config v)
        (solm := { contract := contract v, locals := clipperUpchostVatIlkLocals out })
        (evm := evmVat)
        (name := "_dust")
        (ty := some uint256)
        (expr := .tupleGet (.var "vatIlk") 4)
        (value := .int (Int.ofNat (clipperVatIlksDustWord out).toNat))
        (clipperEvalVatIlkDust v evmVat out))
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact clipperEvalDogCodeGuard_true v evmVat (clipperUpchostDustLocals out)
      (clipperUpchostDustLocals_get_dog out) hdogCode
  exact ExecBlock.consRevert
    (ExecStmt.externalCallReturnDecodeRevert
      (clipperEvalDogTarget v evmVat (clipperUpchostDustLocals out)
        (clipperUpchostDustLocals_get_dog out))
      (by simp [evalExpr?, pure])
      (clipperEvalIlkArg v evmVat (clipperUpchostDustLocals out))
      hcallDog hdecDog)

theorem clipperUpchostChopLocals_get_dog (out outDog : ByteArray) :
    (clipperUpchostChopLocals out outDog).get? "dog" = none := by
  rw [clipperUpchostChopLocals, store_get_ne _ _ (by decide),
    clipperUpchostDustLocals_get_dog]

theorem clipperUpchostChostLocals_get_chost (out outDog : ByteArray) :
    (clipperUpchostChostLocals out outDog).get? "chost" = none := by
  rw [clipperUpchostChostLocals, store_get_ne _ _ (by decide),
    clipperUpchostChopLocals, store_get_ne _ _ (by decide),
    clipperUpchostDustLocals, store_get_ne _ _ (by decide),
    clipperUpchostVatIlkLocals, store_get_ne _ _ (by decide)]
  simp

theorem clipperEvalUpchostDustArg (v : ClipperImmutables) (evm : EVM.State)
    (out outDog : ByteArray) :
    evalExpr? (config v) { contract := contract v, locals := clipperUpchostChopLocals out outDog }
      evm (.var "_dust") =
      .ok (.int (Int.ofNat (clipperVatIlksDustWord out).toNat)) := by
  simp only [evalExpr?, clipperUpchostChopLocals, clipperUpchostDustLocals]
  rw [store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperEvalUpchostChopArg (v : ClipperImmutables) (evm : EVM.State)
    (out outDog : ByteArray) (hloDog : 32 ≤ outDog.size) :
    evalExpr? (config v) { contract := contract v, locals := clipperUpchostChopLocals out outDog }
      evm (.var "chop") =
      .ok (.int (Int.ofNat (clipperDogChopWord outDog).toNat)) := by
  have hlt := Reasoning.Theory.fromByteArrayBigEndian_extract0_32_lt
    (returndata := outDog) hloDog
  simp only [evalExpr?, clipperUpchostChopLocals]
  rw [store_get_self]
  simp [EvalResult.ofOption, clipperDogChopValue, clipperDogChopWord, clipperDogChopNat,
    UInt256.toNat_ofNat_of_lt hlt]

theorem clipperEvalUpchostWmulArgs (v : ClipperImmutables) (evm : EVM.State)
    (out outDog : ByteArray) (hloDog : 32 ≤ outDog.size) :
    evalExprs? (config v) { contract := contract v, locals := clipperUpchostChopLocals out outDog }
      evm [.var "_dust", .var "chop"] =
      .ok [.int (Int.ofNat (clipperVatIlksDustWord out).toNat),
        .int (Int.ofNat (clipperDogChopWord outDog).toNat)] :=
  clipperEvalExprsUintBinary v evm (clipperUpchostChopLocals out outDog)
    (clipperVatIlksDustWord out) (clipperDogChopWord outDog)
    (clipperEvalUpchostDustArg v evm out outDog)
    (clipperEvalUpchostChopArg v evm out outDog hloDog)

theorem clipperEvalUpchostChostNew (v : ClipperImmutables) (evm : EVM.State)
    (out outDog : ByteArray) :
    evalExpr? (config v) { contract := contract v, locals := clipperUpchostChostLocals out outDog }
      evm (.var "chostNew") =
      .ok (.int (Int.ofNat (clipperUpchostChostWord out outDog).toNat)) := by
  simp only [evalExpr?, clipperUpchostChostLocals]
  rw [store_get_self]
  rfl

theorem evalStorageRef_clipperUpchost_chost (v : ClipperImmutables) (evm : EVM.State)
    (out outDog : ByteArray) :
    evalStorageRef (config v) { contract := contract v, locals := clipperUpchostChostLocals out outDog }
      evm chostRef = .ok { base := "chost", steps := [] } := by
  simp [chostRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]

set_option maxHeartbeats 1000000 in
theorem clipperUpchostAssignChost (v : ClipperImmutables) (evm : EVM.State)
    (out outDog : ByteArray) :
    assignStorageRef? (config v)
      { contract := contract v, locals := clipperUpchostChostLocals out outDog } evm
      .storage chostRef (.int (Int.ofNat (clipperUpchostChostWord out outDog).toNat)) =
      .ok ({ contract := contract v, locals := clipperUpchostChostLocals out outDog },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨9⟩
          (clipperUpchostChostWord out outDog)) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (loc := wordLoc ⟨9⟩)
      (hbase := clipperUpchostChostLocals_get_chost out outDog)
      (her := evalStorageRef_clipperUpchost_chost v evm out outDog)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa using storageLocStore_uint256 evm ⟨9⟩ (clipperUpchostChostWord out outDog)

theorem clipperUpchostBodyDogChopSuccess (v : ClipperImmutables)
    (evm evmVat evmDog : EVM.State) (out outDog : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hvatCode :
      0 < (UInt256.ofNat ((evm.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallVat :
      typedCallViaEVM (config v) evm (EVM.address v.vat) "vatIlks" 0 [v.ilk]
        (true, evmVat, out) true)
    (hdecVat : (config v).externalABI.decode? "vatIlks" out = some (clipperVatIlksValues out))
    (hdogCode :
      0 < (UInt256.ofNat ((evmVat.lookupAccount
        (AccountAddress.ofUInt256
          (clipperUpchostDogTarget evmVat.accountMap evmVat.executionEnv))).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDog :
      typedCallViaEVM (config v) evmVat
        (EVM.address (AccountAddress.ofUInt256
          (clipperUpchostDogTarget evmVat.accountMap evmVat.executionEnv)))
        "chop" 0 [v.ilk] (true, evmDog, outDog) true)
    (hdecDog : (config v).externalABI.decode? "chop" outDog = some (clipperDogChopValues outDog))
    (hloDog : 32 ≤ outDog.size)
    (hmul : (clipperVatIlksDustWord out).toNat * (clipperDogChopWord outDog).toNat <
      UInt256.size) :
    ExecTransitionBody (config v) (contract v) evm ∅ (upchostTransition v).body
      (.returned { contract := contract v, locals := clipperUpchostChostLocals out outDog }
        (Solm.EVM.storageStore evmDog evmDog.executionEnv.codeOwner ⟨9⟩
          (clipperUpchostChostWord out outDog)) none) := by
  refine ExecFuncBody.execBlockOK ?_
  simp only [upchostTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true hwv
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact clipperEvalVatCodeGuard_true v evm ∅ hvatCode
  refine ExecBlock.consNormal
    (solm' := { contract := contract v, locals := clipperUpchostVatIlkLocals out })
    (evm' := evmVat) ?_ ?_
  · simpa [clipperUpchostVatIlkLocals] using
      (ExecStmt.externalCallSuccess (clipperEvalVat v evm ∅) (by simp [evalExpr?, pure])
        (clipperEvalIlkArg v evm ∅) hcallVat hdecVat)
  refine ExecBlock.consNormal
    (solm' := { contract := contract v, locals := clipperUpchostDustLocals out })
    (evm' := evmVat) ?_ ?_
  · simpa [clipperUpchostVatIlkLocals, clipperUpchostDustLocals] using
      (ExecStmt.letDecl
        (cfg := config v)
        (solm := { contract := contract v, locals := clipperUpchostVatIlkLocals out })
        (evm := evmVat)
        (name := "_dust")
        (ty := some uint256)
        (expr := .tupleGet (.var "vatIlk") 4)
        (value := .int (Int.ofNat (clipperVatIlksDustWord out).toNat))
        (clipperEvalVatIlkDust v evmVat out))
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact clipperEvalDogCodeGuard_true v evmVat (clipperUpchostDustLocals out)
      (clipperUpchostDustLocals_get_dog out) hdogCode
  refine ExecBlock.consNormal
    (solm' := { contract := contract v, locals := clipperUpchostChopLocals out outDog })
    (evm' := evmDog) ?_ ?_
  · simpa [clipperUpchostChopLocals] using
      (ExecStmt.externalCallSuccess
        (clipperEvalDogTarget v evmVat (clipperUpchostDustLocals out)
          (clipperUpchostDustLocals_get_dog out))
        (by simp [evalExpr?, pure])
        (clipperEvalIlkArg v evmVat (clipperUpchostDustLocals out))
        hcallDog hdecDog)
  let afterWmul : Frame := { contract := contract v, locals := clipperUpchostChostLocals out outDog }
  have hwmul :
      ExecStmt (config v)
        { contract := contract v, locals := clipperUpchostChopLocals out outDog } evmDog
        (.internalCall "wmul" [.var "_dust", .var "chop"] "chostNew")
        (.ok afterWmul evmDog) := by
    simpa [afterWmul, clipperUpchostChostLocals, resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (cfg := config v)
        (caller := { contract := contract v, locals := clipperUpchostChopLocals out outDog })
        (evm := evmDog) (calleeEvm := evmDog)
        (name := "wmul") (retVar := "chostNew")
        (args := [.var "_dust", .var "chop"])
        (argVals := [.int (Int.ofNat (clipperVatIlksDustWord out).toNat),
          .int (Int.ofNat (clipperDogChopWord outDog).toNat)])
        (callee := wmulFunction)
        (locals := clipperUintBinaryLocals (clipperVatIlksDustWord out)
          (clipperDogChopWord outDog))
        (calleeSolm :=
          { contract := contract v,
            locals := clipperWmulReturnLocals (clipperVatIlksDustWord out)
              (clipperDogChopWord outDog)
              (UInt256.mul (clipperVatIlksDustWord out) (clipperDogChopWord outDog)) })
        (value := some [.int (Int.ofNat (clipperUpchostChostWord out outDog).toNat)])
        (clipperEvalUpchostWmulArgs v evmDog out outDog hloDog)
        (clipperLookupWmulFunction v)
        (clipperBindParamsWmul (clipperVatIlksDustWord out) (clipperDogChopWord outDog))
        (clipperWmulFunctionReturns v evmDog (clipperVatIlksDustWord out)
          (clipperDogChopWord outDog) hmul))
  refine ExecBlock.consNormal hwmul ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign (clipperEvalUpchostChostNew v evmDog out outDog)
      (clipperUpchostAssignChost v evmDog out outDog))
    ExecBlock.nil

theorem clipperUpchostBodyDogChopWmulRevert (v : ClipperImmutables)
    (evm evmVat evmDog : EVM.State) (out outDog : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hvatCode :
      0 < (UInt256.ofNat ((evm.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallVat :
      typedCallViaEVM (config v) evm (EVM.address v.vat) "vatIlks" 0 [v.ilk]
        (true, evmVat, out) true)
    (hdecVat : (config v).externalABI.decode? "vatIlks" out = some (clipperVatIlksValues out))
    (hdogCode :
      0 < (UInt256.ofNat ((evmVat.lookupAccount
        (AccountAddress.ofUInt256
          (clipperUpchostDogTarget evmVat.accountMap evmVat.executionEnv))).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallDog :
      typedCallViaEVM (config v) evmVat
        (EVM.address (AccountAddress.ofUInt256
          (clipperUpchostDogTarget evmVat.accountMap evmVat.executionEnv)))
        "chop" 0 [v.ilk] (true, evmDog, outDog) true)
    (hdecDog : (config v).externalABI.decode? "chop" outDog = some (clipperDogChopValues outDog))
    (hloDog : 32 ≤ outDog.size)
    (hover : UInt256.size ≤
      (clipperVatIlksDustWord out).toNat * (clipperDogChopWord outDog).toNat) :
    ExecTransitionBody (config v) (contract v) evm ∅ (upchostTransition v).body
      .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simp only [upchostTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true hwv
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact clipperEvalVatCodeGuard_true v evm ∅ hvatCode
  refine ExecBlock.consNormal
    (solm' := { contract := contract v, locals := clipperUpchostVatIlkLocals out })
    (evm' := evmVat) ?_ ?_
  · simpa [clipperUpchostVatIlkLocals] using
      (ExecStmt.externalCallSuccess (clipperEvalVat v evm ∅) (by simp [evalExpr?, pure])
        (clipperEvalIlkArg v evm ∅) hcallVat hdecVat)
  refine ExecBlock.consNormal
    (solm' := { contract := contract v, locals := clipperUpchostDustLocals out })
    (evm' := evmVat) ?_ ?_
  · simpa [clipperUpchostVatIlkLocals, clipperUpchostDustLocals] using
      (ExecStmt.letDecl
        (cfg := config v)
        (solm := { contract := contract v, locals := clipperUpchostVatIlkLocals out })
        (evm := evmVat)
        (name := "_dust")
        (ty := some uint256)
        (expr := .tupleGet (.var "vatIlk") 4)
        (value := .int (Int.ofNat (clipperVatIlksDustWord out).toNat))
        (clipperEvalVatIlkDust v evmVat out))
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact clipperEvalDogCodeGuard_true v evmVat (clipperUpchostDustLocals out)
      (clipperUpchostDustLocals_get_dog out) hdogCode
  refine ExecBlock.consNormal
    (solm' := { contract := contract v, locals := clipperUpchostChopLocals out outDog })
    (evm' := evmDog) ?_ ?_
  · simpa [clipperUpchostChopLocals] using
      (ExecStmt.externalCallSuccess
        (clipperEvalDogTarget v evmVat (clipperUpchostDustLocals out)
          (clipperUpchostDustLocals_get_dog out))
        (by simp [evalExpr?, pure])
        (clipperEvalIlkArg v evmVat (clipperUpchostDustLocals out))
        hcallDog hdecDog)
  have hwmul :
      ExecStmt (config v)
        { contract := contract v, locals := clipperUpchostChopLocals out outDog } evmDog
        (.internalCall "wmul" [.var "_dust", .var "chop"] "chostNew") .reverted := by
    exact internalCallFunctionRevert
      (cfg := config v)
      (caller := { contract := contract v, locals := clipperUpchostChopLocals out outDog })
      (evm := evmDog)
      (name := "wmul") (retVar := "chostNew")
      (args := [.var "_dust", .var "chop"])
      (argVals := [.int (Int.ofNat (clipperVatIlksDustWord out).toNat),
        .int (Int.ofNat (clipperDogChopWord outDog).toNat)])
      (callee := wmulFunction)
      (locals := clipperUintBinaryLocals (clipperVatIlksDustWord out)
        (clipperDogChopWord outDog))
      (clipperEvalUpchostWmulArgs v evmDog out outDog hloDog)
      (clipperLookupWmulFunction v)
      (clipperBindParamsWmul (clipperVatIlksDustWord out) (clipperDogChopWord outDog))
      (clipperWmulFunctionReverts v evmDog (clipperVatIlksDustWord out)
        (clipperDogChopWord outDog) hover)
  exact ExecBlock.consRevert hwmul

theorem clipperUpchostDogChopNoCodeBodyCore (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ'_evm : AccountMap}
    {A'_evm : Substate} {out : ByteArray} {k C : ℕ}
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg (contract v) I.calldata = some (upchostTransition v))
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode ((upchostTransition v).params.map Param.name)
        (transitionSignature (upchostTransition v)).paramTypes I.calldata = some ∅)
    (rd1599 : RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1599⟩
      (⟨1⟩ :: ⟨164⟩ :: clipperVatIlksSelectorWord :: clipperUpchostVatTarget v ::
        ⟨0⟩ :: ⟨502⟩ :: sel :: [])
      (clipperVatIlksPostCallMem v out) (UInt256.ofNat 9) out (cA', σ'_evm) k C)
    (hcallVat :
      typedCallViaEVM (config v) (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address v.vat) "vatIlks" 0 [v.ilk]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'_evm
              substate := A'_evm
              createdAccounts := cA' },
          out) true)
    (hlo : 160 ≤ out.size)
    (hout : out.size < UInt256.size)
    (hvatCodeSolm :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcodeSizeDog :
      Reasoning.Theory.extCodeSizeWord σ'_evm
        (clipperUpchostDogTarget σ'_evm I) = ⟨0⟩) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, rd1617⟩ := RD.clipperUpchostVatIlksCallSuccessToDecode v hpatch rd1599
  obtain ⟨_, _, rd1643⟩ := RD.clipperUpchostVatIlksReturnDecodeOk v hpatch rd1617 hlo hout
  have hrev :
      RDrev code (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    RD.clipperUpchostDogChopNoCode v hpatch rd1643 hlo hout hcodeSizeDog
  obtain ⟨σ'_solm, A'_solm, hcallSolmRaw, hStateCall⟩ :=
    typedCallViaEVM_initState_EVMStateEquiv (hcall := hcallVat)
      (by simp [initState]) hAccounts
  let evmVatSolm : EVM.State :=
    { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σ'_solm
        substate := A'_solm
        createdAccounts := cA' }
  have hcallSolm :
      typedCallViaEVM (config v) (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address v.vat) "vatIlks" 0 [v.ilk]
        (true, evmVatSolm, out) true := by
    simpa [evmVatSolm] using hcallSolmRaw
  have hAccountsVat : accountMapEquiv σ'_evm σ'_solm := by
    simpa [initState] using hStateCall.accountMap
  have hdogTargetEq :
      clipperUpchostDogTarget σ'_evm I = clipperUpchostDogTarget σ'_solm I :=
    clipperUpchostDogTarget_accountMapEquiv hAccountsVat
  have hcodeSizeDogSolm :
      Reasoning.Theory.extCodeSizeWord σ'_solm
        (clipperUpchostDogTarget σ'_solm I) = ⟨0⟩ := by
    rw [← hdogTargetEq]
    rw [← Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccountsVat
      (clipperUpchostDogTarget σ'_evm I)]
    exact hcodeSizeDog
  have hnoDogCode :
      (UInt256.ofNat
        ((evmVatSolm.lookupAccount
          (AccountAddress.ofUInt256
            (clipperUpchostDogTarget evmVatSolm.accountMap evmVatSolm.executionEnv))).option
            (0 : Nat) (fun acc => acc.code.size))).toNat = 0 := by
    simpa [evmVatSolm, State.lookupAccount, initState] using
      clipperExtCodeSizeWord_zero_lookup_code_zero
        (σ := σ'_solm) (target := clipperUpchostDogTarget σ'_solm I)
        (addr := AccountAddress.ofUInt256 (clipperUpchostDogTarget σ'_solm I))
        rfl hcodeSizeDogSolm
  have hdecVat :
      (config v).externalABI.decode? "vatIlks" out = some (clipperVatIlksValues out) := by
    simpa [clipperVatIlksValues] using clipperVatIlksDecode_ok (v := v) hlo
  have hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (upchostTransition v).body .reverted := by
    exact clipperUpchostBodyDogChopNoCode v
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      evmVatSolm
      out (by simp only [initState]; exact hwv) hvatCodeSolm hcallSolm hdecVat hnoDogCode
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem clipperUpchostDogChopCallFailureBodyCore (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {cA_vat : Batteries.RBSet AccountAddress compare} {σ_vat : AccountMap}
    {A_vat : Substate} {out : ByteArray} {kVat CVat : ℕ}
    {cA_dog : Batteries.RBSet AccountAddress compare} {σ_dog : AccountMap}
    {A_dog : Substate} {outDog : ByteArray} {kDog CDog : ℕ}
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg (contract v) I.calldata = some (upchostTransition v))
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode ((upchostTransition v).params.map Param.name)
        (transitionSignature (upchostTransition v)).paramTypes I.calldata = some ∅)
    (rd1599 : RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1599⟩
      (⟨1⟩ :: ⟨164⟩ :: clipperVatIlksSelectorWord :: clipperUpchostVatTarget v ::
        ⟨0⟩ :: ⟨502⟩ :: sel :: [])
      (clipperVatIlksPostCallMem v out) (UInt256.ofNat 9) out (cA_vat, σ_vat)
      kVat CVat)
    (hcallVat :
      typedCallViaEVM (config v) (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address v.vat) "vatIlks" 0 [v.ilk]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ_vat
              substate := A_vat
              createdAccounts := cA_vat },
          out) true)
    (rd1761 : RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1761⟩
      (⟨0⟩ :: ⟨164⟩ :: clipperDogChopSelectorWord :: clipperUpchostDogTarget σ_vat I ::
        clipperVatIlksDustWord out :: ⟨1806⟩ :: clipperVatIlksDustWord out ::
        ⟨502⟩ :: sel :: [])
      (clipperDogChopPostCallMem v out outDog) clipperDogChopPostCallAw outDog
      (cA_dog, σ_dog) kDog CDog)
    (hcallDog :
      typedCallViaEVM (config v)
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ_vat
          substate := A_vat
          createdAccounts := cA_vat }
        (EVM.address (AccountAddress.ofUInt256 (clipperUpchostDogTarget σ_vat I)))
        "chop" 0 [v.ilk]
        (false,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_dog
            substate := A_dog
            createdAccounts := cA_dog },
          outDog) true)
    (hlo : 160 ≤ out.size)
    (hout : out.size < UInt256.size)
    (houtDog : outDog.size < UInt256.size)
    (hvatCodeSolm :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcodeSizeDog :
      Reasoning.Theory.extCodeSizeWord σ_vat
        (clipperUpchostDogTarget σ_vat I) ≠ ⟨0⟩) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.clipperUpchostDogChopCallFailure v hpatch rd1761 houtDog (by simp)
  obtain ⟨_, _, rd1617⟩ := RD.clipperUpchostVatIlksCallSuccessToDecode v hpatch rd1599
  obtain ⟨_, _, _rd1643⟩ := RD.clipperUpchostVatIlksReturnDecodeOk v hpatch rd1617 hlo hout
  obtain ⟨σ_vat_solm, A_vat_solm, hcallVatSolmRaw, hStateVat⟩ :=
    typedCallViaEVM_initState_EVMStateEquiv (hcall := hcallVat)
      (by simp [initState]) hAccounts
  let evmVatSolm : EVM.State :=
    { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σ_vat_solm
        substate := A_vat_solm
        createdAccounts := cA_vat }
  have hcallVatSolm :
      typedCallViaEVM (config v) (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address v.vat) "vatIlks" 0 [v.ilk]
        (true, evmVatSolm, out) true := by
    simpa [evmVatSolm] using hcallVatSolmRaw
  have hAccountsVat : accountMapEquiv σ_vat σ_vat_solm := by
    simpa [initState] using hStateVat.accountMap
  have hdogTargetEq :
      clipperUpchostDogTarget σ_vat I = clipperUpchostDogTarget σ_vat_solm I :=
    clipperUpchostDogTarget_accountMapEquiv hAccountsVat
  have hcodeSizeDogSolm :
      Reasoning.Theory.extCodeSizeWord σ_vat_solm
        (clipperUpchostDogTarget σ_vat_solm I) ≠ ⟨0⟩ := by
    intro hzero
    exact hcodeSizeDog (by
      rw [Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccountsVat
        (clipperUpchostDogTarget σ_vat I), hdogTargetEq]
      exact hzero)
  have hdogCodeSolm :
      0 < (UInt256.ofNat ((evmVatSolm.lookupAccount
        (AccountAddress.ofUInt256
          (clipperUpchostDogTarget evmVatSolm.accountMap evmVatSolm.executionEnv))).option 0
          (fun acc => acc.code.size))).toNat := by
    simpa [evmVatSolm, State.lookupAccount, initState] using
      clipperExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ_vat_solm) (target := clipperUpchostDogTarget σ_vat_solm I)
        (addr := AccountAddress.ofUInt256 (clipperUpchostDogTarget σ_vat_solm I))
        rfl hcodeSizeDogSolm
  let evmVatEvm : EVM.State :=
    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σ_vat
      substate := A_vat
      createdAccounts := cA_vat }
  obtain ⟨σ_dog_solm, A_dog_solm, hcallDogSolmRaw, _hAccountsDog⟩ :=
    typedCallViaEVM_accountMapEquiv_noSubstate
      (evm_solm := evmVatSolm) hcallDog hStateVat.accountMap
      (by simp [evmVatSolm, initState])
      (by simp [evmVatSolm])
      (by simp [evmVatSolm, initState])
      (by simp [evmVatSolm, initState])
      (by simp [evmVatSolm, initState])
  let evmDogSolm : EVM.State :=
    { evmVatSolm with
      accountMap := σ_dog_solm
      substate := A_dog_solm
      createdAccounts := cA_dog }
  have hcallDogSolm :
      typedCallViaEVM (config v) evmVatSolm
        (EVM.address (AccountAddress.ofUInt256
          (clipperUpchostDogTarget evmVatSolm.accountMap evmVatSolm.executionEnv)))
        "chop" 0 [v.ilk] (false, evmDogSolm, outDog) true := by
    simpa [evmDogSolm, evmVatSolm, hdogTargetEq] using hcallDogSolmRaw
  have hdecVat :
      (config v).externalABI.decode? "vatIlks" out = some (clipperVatIlksValues out) := by
    simpa [clipperVatIlksValues] using clipperVatIlksDecode_ok (v := v) hlo
  have hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (upchostTransition v).body .reverted := by
    exact clipperUpchostBodyDogChopCallFailure v
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      evmVatSolm evmDogSolm out outDog (by simp only [initState]; exact hwv)
      hvatCodeSolm hcallVatSolm hdecVat hdogCodeSolm hcallDogSolm
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem clipperUpchostDogChopDecodeShortBodyCore (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {cA_vat : Batteries.RBSet AccountAddress compare} {σ_vat : AccountMap}
    {A_vat : Substate} {out : ByteArray} {kVat CVat : ℕ}
    {cA_dog : Batteries.RBSet AccountAddress compare} {σ_dog : AccountMap}
    {A_dog : Substate} {outDog : ByteArray} {kDog CDog : ℕ}
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg (contract v) I.calldata = some (upchostTransition v))
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode ((upchostTransition v).params.map Param.name)
        (transitionSignature (upchostTransition v)).paramTypes I.calldata = some ∅)
    (rd1599 : RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1599⟩
      (⟨1⟩ :: ⟨164⟩ :: clipperVatIlksSelectorWord :: clipperUpchostVatTarget v ::
        ⟨0⟩ :: ⟨502⟩ :: sel :: [])
      (clipperVatIlksPostCallMem v out) (UInt256.ofNat 9) out (cA_vat, σ_vat)
      kVat CVat)
    (hcallVat :
      typedCallViaEVM (config v) (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address v.vat) "vatIlks" 0 [v.ilk]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ_vat
              substate := A_vat
              createdAccounts := cA_vat },
          out) true)
    (rd1761 : RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1761⟩
      (⟨1⟩ :: ⟨164⟩ :: clipperDogChopSelectorWord :: clipperUpchostDogTarget σ_vat I ::
        clipperVatIlksDustWord out :: ⟨1806⟩ :: clipperVatIlksDustWord out ::
        ⟨502⟩ :: sel :: [])
      (clipperDogChopPostCallMem v out outDog) clipperDogChopPostCallAw outDog
      (cA_dog, σ_dog) kDog CDog)
    (hcallDog :
      typedCallViaEVM (config v)
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ_vat
          substate := A_vat
          createdAccounts := cA_vat }
        (EVM.address (AccountAddress.ofUInt256 (clipperUpchostDogTarget σ_vat I)))
        "chop" 0 [v.ilk]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_dog
            substate := A_dog
            createdAccounts := cA_dog },
          outDog) true)
    (hlo : 160 ≤ out.size)
    (hout : out.size < UInt256.size)
    (hshortDog : outDog.size < 32)
    (houtDog : outDog.size < UInt256.size)
    (hvatCodeSolm :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcodeSizeDog :
      Reasoning.Theory.extCodeSizeWord σ_vat
        (clipperUpchostDogTarget σ_vat I) ≠ ⟨0⟩) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, rd1779⟩ := RD.clipperUpchostDogChopCallSuccessToDecode v hpatch rd1761
  have hrev :=
    RD.clipperUpchostDogChopReturnDecodeShortReverts v hpatch rd1779 hlo hout hshortDog
      houtDog
  obtain ⟨_, _, rd1617⟩ := RD.clipperUpchostVatIlksCallSuccessToDecode v hpatch rd1599
  obtain ⟨_, _, _rd1643⟩ := RD.clipperUpchostVatIlksReturnDecodeOk v hpatch rd1617 hlo hout
  obtain ⟨σ_vat_solm, A_vat_solm, hcallVatSolmRaw, hStateVat⟩ :=
    typedCallViaEVM_initState_EVMStateEquiv (hcall := hcallVat)
      (by simp [initState]) hAccounts
  let evmVatSolm : EVM.State :=
    { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σ_vat_solm
        substate := A_vat_solm
        createdAccounts := cA_vat }
  have hcallVatSolm :
      typedCallViaEVM (config v) (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address v.vat) "vatIlks" 0 [v.ilk]
        (true, evmVatSolm, out) true := by
    simpa [evmVatSolm] using hcallVatSolmRaw
  have hAccountsVat : accountMapEquiv σ_vat σ_vat_solm := by
    simpa [initState] using hStateVat.accountMap
  have hdogTargetEq :
      clipperUpchostDogTarget σ_vat I = clipperUpchostDogTarget σ_vat_solm I :=
    clipperUpchostDogTarget_accountMapEquiv hAccountsVat
  have hcodeSizeDogSolm :
      Reasoning.Theory.extCodeSizeWord σ_vat_solm
        (clipperUpchostDogTarget σ_vat_solm I) ≠ ⟨0⟩ := by
    intro hzero
    exact hcodeSizeDog (by
      rw [Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccountsVat
        (clipperUpchostDogTarget σ_vat I), hdogTargetEq]
      exact hzero)
  have hdogCodeSolm :
      0 < (UInt256.ofNat ((evmVatSolm.lookupAccount
        (AccountAddress.ofUInt256
          (clipperUpchostDogTarget evmVatSolm.accountMap evmVatSolm.executionEnv))).option 0
          (fun acc => acc.code.size))).toNat := by
    simpa [evmVatSolm, State.lookupAccount, initState] using
      clipperExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ_vat_solm) (target := clipperUpchostDogTarget σ_vat_solm I)
        (addr := AccountAddress.ofUInt256 (clipperUpchostDogTarget σ_vat_solm I))
        rfl hcodeSizeDogSolm
  let evmVatEvm : EVM.State :=
    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σ_vat
      substate := A_vat
      createdAccounts := cA_vat }
  obtain ⟨σ_dog_solm, A_dog_solm, hcallDogSolmRaw, _hAccountsDog⟩ :=
    typedCallViaEVM_accountMapEquiv_noSubstate
      (evm_solm := evmVatSolm) hcallDog hStateVat.accountMap
      (by simp [evmVatSolm, initState])
      (by simp [evmVatSolm])
      (by simp [evmVatSolm, initState])
      (by simp [evmVatSolm, initState])
      (by simp [evmVatSolm, initState])
  let evmDogSolm : EVM.State :=
    { evmVatSolm with
      accountMap := σ_dog_solm
      substate := A_dog_solm
      createdAccounts := cA_dog }
  have hcallDogSolm :
      typedCallViaEVM (config v) evmVatSolm
        (EVM.address (AccountAddress.ofUInt256
          (clipperUpchostDogTarget evmVatSolm.accountMap evmVatSolm.executionEnv)))
        "chop" 0 [v.ilk] (true, evmDogSolm, outDog) true := by
    simpa [evmDogSolm, evmVatSolm, hdogTargetEq] using hcallDogSolmRaw
  have hdecVat :
      (config v).externalABI.decode? "vatIlks" out = some (clipperVatIlksValues out) := by
    simpa [clipperVatIlksValues] using clipperVatIlksDecode_ok (v := v) hlo
  have hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (upchostTransition v).body .reverted := by
    exact clipperUpchostBodyDogChopDecodeRevert v
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      evmVatSolm evmDogSolm out outDog (by simp only [initState]; exact hwv)
      hvatCodeSolm hcallVatSolm hdecVat hdogCodeSolm hcallDogSolm
        (clipperDogChopDecode_none_short hshortDog)
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem clipperUpchostDogChopSuccessBodyCore (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {cA_vat : Batteries.RBSet AccountAddress compare} {σ_vat : AccountMap}
    {A_vat : Substate} {out : ByteArray} {kVat CVat : ℕ}
    {cA_dog : Batteries.RBSet AccountAddress compare} {σ_dog : AccountMap}
    {A_dog : Substate} {outDog : ByteArray} {kDog CDog : ℕ}
    (hcode : I.code = code) (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg (contract v) I.calldata = some (upchostTransition v))
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode ((upchostTransition v).params.map Param.name)
        (transitionSignature (upchostTransition v)).paramTypes I.calldata = some ∅)
    (rd1599 : RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1599⟩
      (⟨1⟩ :: ⟨164⟩ :: clipperVatIlksSelectorWord :: clipperUpchostVatTarget v ::
        ⟨0⟩ :: ⟨502⟩ :: sel :: [])
      (clipperVatIlksPostCallMem v out) (UInt256.ofNat 9) out (cA_vat, σ_vat)
      kVat CVat)
    (hcallVat :
      typedCallViaEVM (config v) (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address v.vat) "vatIlks" 0 [v.ilk]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ_vat
              substate := A_vat
              createdAccounts := cA_vat },
          out) true)
    (rd1761 : RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1761⟩
      (⟨1⟩ :: ⟨164⟩ :: clipperDogChopSelectorWord :: clipperUpchostDogTarget σ_vat I ::
        clipperVatIlksDustWord out :: ⟨1806⟩ :: clipperVatIlksDustWord out ::
        ⟨502⟩ :: sel :: [])
      (clipperDogChopPostCallMem v out outDog) clipperDogChopPostCallAw outDog
      (cA_dog, σ_dog) kDog CDog)
    (hcallDog :
      typedCallViaEVM (config v)
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ_vat
          substate := A_vat
          createdAccounts := cA_vat }
        (EVM.address (AccountAddress.ofUInt256 (clipperUpchostDogTarget σ_vat I)))
        "chop" 0 [v.ilk]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_dog
            substate := A_dog
            createdAccounts := cA_dog },
          outDog) true)
    (hlo : 160 ≤ out.size)
    (hout : out.size < UInt256.size)
    (hloDog : 32 ≤ outDog.size)
    (houtDog : outDog.size < UInt256.size)
    (hvatCodeSolm :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcodeSizeDog :
      Reasoning.Theory.extCodeSizeWord σ_vat
        (clipperUpchostDogTarget σ_vat I) ≠ ⟨0⟩)
    (hmul :
      (clipperVatIlksDustWord out).toNat * (clipperDogChopWord outDog).toNat <
        UInt256.size) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, rd1779⟩ := RD.clipperUpchostDogChopCallSuccessToDecode v hpatch rd1761
  obtain ⟨_, _, rd8238⟩ :=
    RD.clipperUpchostDogChopReturnDecodeOk v hpatch rd1779 hlo hout hloDog houtDog
  obtain ⟨_, _, rd1806⟩ :=
    Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperWmulRoutine
      v hpatch rd8238 (by simpa [Nat.mul_comm] using hmul)
      (clipperJumpDest1806 v hpatch) (by simp)
  have hret :
      RDret code (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA_dog,
          sstoreAccountMap I.codeOwner σ_dog ⟨9⟩ (clipperUpchostChostWord out outDog))
        ByteArray.empty := by
    exact Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperUpchostStoreChostReturn v hpatch
      (by
        simpa [clipperUpchostChostWord,
          u256_mul_comm (clipperDogChopWord outDog) (clipperVatIlksDustWord out)] using
          rd1806)
      hperm
  obtain ⟨_, _, _rd1617⟩ := RD.clipperUpchostVatIlksCallSuccessToDecode v hpatch rd1599
  obtain ⟨σ_vat_solm, A_vat_solm, hcallVatSolmRaw, hStateVat⟩ :=
    typedCallViaEVM_initState_EVMStateEquiv (hcall := hcallVat)
      (by simp [initState]) hAccounts
  let evmVatSolm : EVM.State :=
    { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σ_vat_solm
        substate := A_vat_solm
        createdAccounts := cA_vat }
  have hcallVatSolm :
      typedCallViaEVM (config v) (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address v.vat) "vatIlks" 0 [v.ilk]
        (true, evmVatSolm, out) true := by
    simpa [evmVatSolm] using hcallVatSolmRaw
  have hAccountsVat : accountMapEquiv σ_vat σ_vat_solm := by
    simpa [initState] using hStateVat.accountMap
  have hdogTargetEq :
      clipperUpchostDogTarget σ_vat I = clipperUpchostDogTarget σ_vat_solm I :=
    clipperUpchostDogTarget_accountMapEquiv hAccountsVat
  have hcodeSizeDogSolm :
      Reasoning.Theory.extCodeSizeWord σ_vat_solm
        (clipperUpchostDogTarget σ_vat_solm I) ≠ ⟨0⟩ := by
    intro hzero
    exact hcodeSizeDog (by
      rw [Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccountsVat
        (clipperUpchostDogTarget σ_vat I), hdogTargetEq]
      exact hzero)
  have hdogCodeSolm :
      0 < (UInt256.ofNat ((evmVatSolm.lookupAccount
        (AccountAddress.ofUInt256
          (clipperUpchostDogTarget evmVatSolm.accountMap evmVatSolm.executionEnv))).option 0
          (fun acc => acc.code.size))).toNat := by
    simpa [evmVatSolm, State.lookupAccount, initState] using
      clipperExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ_vat_solm) (target := clipperUpchostDogTarget σ_vat_solm I)
        (addr := AccountAddress.ofUInt256 (clipperUpchostDogTarget σ_vat_solm I))
        rfl hcodeSizeDogSolm
  obtain ⟨σ_dog_solm, A_dog_solm, hcallDogSolmRaw, hAccountsDog⟩ :=
    typedCallViaEVM_accountMapEquiv_noSubstate
      (evm_solm := evmVatSolm) hcallDog hStateVat.accountMap
      (by simp [evmVatSolm, initState])
      (by simp [evmVatSolm])
      (by simp [evmVatSolm, initState])
      (by simp [evmVatSolm, initState])
      (by simp [evmVatSolm, initState])
  let evmDogSolm : EVM.State :=
    { evmVatSolm with
      accountMap := σ_dog_solm
      substate := A_dog_solm
      createdAccounts := cA_dog }
  have hcallDogSolm :
      typedCallViaEVM (config v) evmVatSolm
        (EVM.address (AccountAddress.ofUInt256
          (clipperUpchostDogTarget evmVatSolm.accountMap evmVatSolm.executionEnv)))
        "chop" 0 [v.ilk] (true, evmDogSolm, outDog) true := by
    simpa [evmDogSolm, evmVatSolm, hdogTargetEq] using hcallDogSolmRaw
  have hdecVat :
      (config v).externalABI.decode? "vatIlks" out = some (clipperVatIlksValues out) := by
    simpa [clipperVatIlksValues] using clipperVatIlksDecode_ok (v := v) hlo
  have hdecDog :
      (config v).externalABI.decode? "chop" outDog = some (clipperDogChopValues outDog) :=
    clipperDogChopDecode_ok (v := v) hloDog
  have hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (upchostTransition v).body
        (.returned { contract := contract v, locals := clipperUpchostChostLocals out outDog }
          (Solm.EVM.storageStore evmDogSolm evmDogSolm.executionEnv.codeOwner ⟨9⟩
            (clipperUpchostChostWord out outDog)) none) := by
    exact clipperUpchostBodyDogChopSuccess v
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      evmVatSolm evmDogSolm out outDog (by simp only [initState]; exact hwv)
      hvatCodeSolm hcallVatSolm hdecVat hdogCodeSolm hcallDogSolm hdecDog hloDog hmul
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    (by simp [evmDogSolm, evmVatSolm, initState, storageStore_createdAccounts])
    (by
      simpa [evmDogSolm, evmVatSolm, initState, storageStore_accountMap] using
        accountMapEquiv_sstoreAccountMap I.codeOwner ⟨9⟩
          (clipperUpchostChostWord out outDog) hAccountsDog)
    (by
      simpa [upchostTransition] using
        (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
          (dvs := []) rfl (by native_decide) (by native_decide)))

theorem clipperUpchostDogChopWmulRevertBodyCore (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {cA_vat : Batteries.RBSet AccountAddress compare} {σ_vat : AccountMap}
    {A_vat : Substate} {out : ByteArray} {kVat CVat : ℕ}
    {cA_dog : Batteries.RBSet AccountAddress compare} {σ_dog : AccountMap}
    {A_dog : Substate} {outDog : ByteArray} {kDog CDog : ℕ}
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg (contract v) I.calldata = some (upchostTransition v))
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode ((upchostTransition v).params.map Param.name)
        (transitionSignature (upchostTransition v)).paramTypes I.calldata = some ∅)
    (rd1599 : RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1599⟩
      (⟨1⟩ :: ⟨164⟩ :: clipperVatIlksSelectorWord :: clipperUpchostVatTarget v ::
        ⟨0⟩ :: ⟨502⟩ :: sel :: [])
      (clipperVatIlksPostCallMem v out) (UInt256.ofNat 9) out (cA_vat, σ_vat)
      kVat CVat)
    (hcallVat :
      typedCallViaEVM (config v) (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address v.vat) "vatIlks" 0 [v.ilk]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ_vat
              substate := A_vat
              createdAccounts := cA_vat },
          out) true)
    (rd1761 : RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1761⟩
      (⟨1⟩ :: ⟨164⟩ :: clipperDogChopSelectorWord :: clipperUpchostDogTarget σ_vat I ::
        clipperVatIlksDustWord out :: ⟨1806⟩ :: clipperVatIlksDustWord out ::
        ⟨502⟩ :: sel :: [])
      (clipperDogChopPostCallMem v out outDog) clipperDogChopPostCallAw outDog
      (cA_dog, σ_dog) kDog CDog)
    (hcallDog :
      typedCallViaEVM (config v)
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ_vat
          substate := A_vat
          createdAccounts := cA_vat }
        (EVM.address (AccountAddress.ofUInt256 (clipperUpchostDogTarget σ_vat I)))
        "chop" 0 [v.ilk]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_dog
            substate := A_dog
            createdAccounts := cA_dog },
          outDog) true)
    (hlo : 160 ≤ out.size)
    (hout : out.size < UInt256.size)
    (hloDog : 32 ≤ outDog.size)
    (houtDog : outDog.size < UInt256.size)
    (hvatCodeSolm :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcodeSizeDog :
      Reasoning.Theory.extCodeSizeWord σ_vat
        (clipperUpchostDogTarget σ_vat I) ≠ ⟨0⟩)
    (hover :
      UInt256.size ≤
        (clipperVatIlksDustWord out).toNat * (clipperDogChopWord outDog).toNat) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, rd1779⟩ := RD.clipperUpchostDogChopCallSuccessToDecode v hpatch rd1761
  obtain ⟨_, _, rd8238⟩ :=
    RD.clipperUpchostDogChopReturnDecodeOk v hpatch rd1779 hlo hout hloDog houtDog
  have hrev :
      RDrev code (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperWmulRoutineRevert
      v hpatch rd8238 (by simpa [Nat.mul_comm] using hover)
      (by simp)
  obtain ⟨_, _, _rd1617⟩ := RD.clipperUpchostVatIlksCallSuccessToDecode v hpatch rd1599
  obtain ⟨σ_vat_solm, A_vat_solm, hcallVatSolmRaw, hStateVat⟩ :=
    typedCallViaEVM_initState_EVMStateEquiv (hcall := hcallVat)
      (by simp [initState]) hAccounts
  let evmVatSolm : EVM.State :=
    { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σ_vat_solm
        substate := A_vat_solm
        createdAccounts := cA_vat }
  have hcallVatSolm :
      typedCallViaEVM (config v) (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address v.vat) "vatIlks" 0 [v.ilk]
        (true, evmVatSolm, out) true := by
    simpa [evmVatSolm] using hcallVatSolmRaw
  have hAccountsVat : accountMapEquiv σ_vat σ_vat_solm := by
    simpa [initState] using hStateVat.accountMap
  have hdogTargetEq :
      clipperUpchostDogTarget σ_vat I = clipperUpchostDogTarget σ_vat_solm I :=
    clipperUpchostDogTarget_accountMapEquiv hAccountsVat
  have hcodeSizeDogSolm :
      Reasoning.Theory.extCodeSizeWord σ_vat_solm
        (clipperUpchostDogTarget σ_vat_solm I) ≠ ⟨0⟩ := by
    intro hzero
    exact hcodeSizeDog (by
      rw [Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccountsVat
        (clipperUpchostDogTarget σ_vat I), hdogTargetEq]
      exact hzero)
  have hdogCodeSolm :
      0 < (UInt256.ofNat ((evmVatSolm.lookupAccount
        (AccountAddress.ofUInt256
          (clipperUpchostDogTarget evmVatSolm.accountMap evmVatSolm.executionEnv))).option 0
          (fun acc => acc.code.size))).toNat := by
    simpa [evmVatSolm, State.lookupAccount, initState] using
      clipperExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ_vat_solm) (target := clipperUpchostDogTarget σ_vat_solm I)
        (addr := AccountAddress.ofUInt256 (clipperUpchostDogTarget σ_vat_solm I))
        rfl hcodeSizeDogSolm
  obtain ⟨σ_dog_solm, A_dog_solm, hcallDogSolmRaw, _hAccountsDog⟩ :=
    typedCallViaEVM_accountMapEquiv_noSubstate
      (evm_solm := evmVatSolm) hcallDog hStateVat.accountMap
      (by simp [evmVatSolm, initState])
      (by simp [evmVatSolm])
      (by simp [evmVatSolm, initState])
      (by simp [evmVatSolm, initState])
      (by simp [evmVatSolm, initState])
  let evmDogSolm : EVM.State :=
    { evmVatSolm with
      accountMap := σ_dog_solm
      substate := A_dog_solm
      createdAccounts := cA_dog }
  have hcallDogSolm :
      typedCallViaEVM (config v) evmVatSolm
        (EVM.address (AccountAddress.ofUInt256
          (clipperUpchostDogTarget evmVatSolm.accountMap evmVatSolm.executionEnv)))
        "chop" 0 [v.ilk] (true, evmDogSolm, outDog) true := by
    simpa [evmDogSolm, evmVatSolm, hdogTargetEq] using hcallDogSolmRaw
  have hdecVat :
      (config v).externalABI.decode? "vatIlks" out = some (clipperVatIlksValues out) := by
    simpa [clipperVatIlksValues] using clipperVatIlksDecode_ok (v := v) hlo
  have hdecDog :
      (config v).externalABI.decode? "chop" outDog = some (clipperDogChopValues outDog) :=
    clipperDogChopDecode_ok (v := v) hloDog
  have hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (upchostTransition v).body .reverted := by
    exact clipperUpchostBodyDogChopWmulRevert v
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      evmVatSolm evmDogSolm out outDog (by simp only [initState]; exact hwv)
      hvatCodeSolm hcallVatSolm hdecVat hdogCodeSolm hcallDogSolm hdecDog hloDog hover
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem clipperUpchostVatIlksCallFailureBodyCore (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ'_evm : AccountMap}
    {A'_evm : Substate} {out mem : ByteArray} {aw : UInt256} {k C : ℕ}
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg (contract v) I.calldata = some (upchostTransition v))
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode ((upchostTransition v).params.map Param.name)
        (transitionSignature (upchostTransition v)).paramTypes I.calldata = some ∅)
    (rd1599 : RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1599⟩
      (⟨0⟩ :: ⟨164⟩ :: clipperVatIlksSelectorWord :: clipperUpchostVatTarget v ::
        ⟨0⟩ :: ⟨502⟩ :: sel :: [])
      mem aw out (cA', σ'_evm) k C)
    (hcallVat :
      typedCallViaEVM (config v) (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address v.vat) "vatIlks" 0 [v.ilk]
        (false,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'_evm
              substate := A'_evm
              createdAccounts := cA' },
          out) true)
    (hosz : out.size < UInt256.size)
    (hvatCodeSolm :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev :=
    RD.clipperUpchostVatIlksCallFailure v hpatch rd1599 hosz (by simp)
  obtain ⟨σ'_solm, A'_solm, hcallSolmRaw, _hStateCall⟩ :=
    typedCallViaEVM_initState_EVMStateEquiv (hcall := hcallVat)
      (by simp [initState]) hAccounts
  have hcallSolm :
      typedCallViaEVM (config v) (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address v.vat) "vatIlks" 0 [v.ilk]
        (false,
          { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := cA' },
          out) true := by
    simpa using hcallSolmRaw
  have hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (upchostTransition v).body .reverted := by
    exact clipperUpchostBodyVatIlksCallFailure v
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ'_solm
          substate := A'_solm
          createdAccounts := cA' }
      out (by simp only [initState]; exact hwv) hvatCodeSolm hcallSolm
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem clipperUpchostVatIlksDecodeShortBodyCore (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ'_evm : AccountMap}
    {A'_evm : Substate} {out : ByteArray} {k C : ℕ}
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg (contract v) I.calldata = some (upchostTransition v))
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode ((upchostTransition v).params.map Param.name)
        (transitionSignature (upchostTransition v)).paramTypes I.calldata = some ∅)
    (rd1599 : RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1599⟩
      (⟨1⟩ :: ⟨164⟩ :: clipperVatIlksSelectorWord :: clipperUpchostVatTarget v ::
        ⟨0⟩ :: ⟨502⟩ :: sel :: [])
      (clipperVatIlksPostCallMem v out) (UInt256.ofNat 9) out (cA', σ'_evm) k C)
    (hcallVat :
      typedCallViaEVM (config v) (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address v.vat) "vatIlks" 0 [v.ilk]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'_evm
              substate := A'_evm
              createdAccounts := cA' },
          out) true)
    (hshort : out.size < 160)
    (hout : out.size < UInt256.size)
    (hvatCodeSolm :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, rd1617⟩ := RD.clipperUpchostVatIlksCallSuccessToDecode v hpatch rd1599
  have hrev := RD.clipperUpchostVatIlksReturnDecodeShortReverts v hpatch rd1617 hshort hout
  obtain ⟨σ'_solm, A'_solm, hcallSolmRaw, _hStateCall⟩ :=
    typedCallViaEVM_initState_EVMStateEquiv (hcall := hcallVat)
      (by simp [initState]) hAccounts
  have hcallSolm :
      typedCallViaEVM (config v) (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address v.vat) "vatIlks" 0 [v.ilk]
        (true,
          { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := cA' },
          out) true := by
    simpa using hcallSolmRaw
  have hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (upchostTransition v).body .reverted := by
    exact clipperUpchostBodyVatIlksDecodeRevert v
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ'_solm
          substate := A'_solm
          createdAccounts := cA' }
      out (by simp only [initState]; exact hwv) hvatCodeSolm hcallSolm
      (clipperVatIlksDecode_none_short hshort)
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem clipperUpchostVatNoCodeBodyCore (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg (contract v) I.calldata = some (upchostTransition v))
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode ((upchostTransition v).params.map Param.name)
        (transitionSignature (upchostTransition v)).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨494⟩ [clipperSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcodeSizeVat :
      Reasoning.Theory.extCodeSizeWord σ_evm (clipperUpchostVatTarget v) = ⟨0⟩) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, rd494⟩ := hreach
  have hrev :
      RDrev code (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    RD.clipperUpchostVatIlksNoCode v hpatch rd494 hcodeSizeVat
  have hcodeSizeVatSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm (clipperUpchostVatTarget v) = ⟨0⟩ := by
    rw [← Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
      (clipperUpchostVatTarget v)]
    exact hcodeSizeVat
  have hnoCode :
      (UInt256.ofNat
        (Option.option 0 (fun acc => acc.code.size)
          ((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            v.vat))).toNat = 0 := by
    simpa [State.lookupAccount, initState] using
      clipperExtCodeSizeWord_zero_lookup_code_zero
        (σ := σ_solm) (target := clipperUpchostVatTarget v) (addr := v.vat)
        ((clipperUpchostVatTargetAddress v).symm) hcodeSizeVatSolm
  have hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (upchostTransition v).body .reverted := by
    exact clipperUpchostBodyVatNoCode v
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
      (by simp only [initState]; exact hwv) hnoCode
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem clipperUpchostBody (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (clipperSelBytes 24))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (clipperSelBytes 24) (by native_decide) hsel
  have hdispatch := clipperDispatch_upchost v hsel
  have hdecode := clipperDecode_upchost v hsz
  have hreach := clipperReachUpchostBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    v hpatch hcode hwv hsz hsize hsel
  by_cases hcodeSizeVat :
      Reasoning.Theory.extCodeSizeWord σ_evm (clipperUpchostVatTarget v) = ⟨0⟩
  · exact clipperUpchostVatNoCodeBodyCore v hpatch hcode hwv hdispatch hdecode hreach
      hAccounts hcodeSizeVat
  ·
      have hcodeSizeVatNE :
          Reasoning.Theory.extCodeSizeWord σ_evm (clipperUpchostVatTarget v) ≠
            ⟨0⟩ := hcodeSizeVat
      have hcodeSizeVatSolmNE :
          Reasoning.Theory.extCodeSizeWord σ_solm
              (clipperUpchostVatTarget v) ≠ ⟨0⟩ := by
        intro hzero
        exact hcodeSizeVatNE (by
          rw [Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
            (clipperUpchostVatTarget v)]
          exact hzero)
      have hvatCodeSolm :
          0 < (UInt256.ofNat
            (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
              v.vat).option 0 (fun acc => acc.code.size))).toNat := by
        simpa [State.lookupAccount, initState] using
          clipperExtCodeSizeWord_ne_zero_lookup_code_pos
            (σ := σ_solm) (target := clipperUpchostVatTarget v) (addr := v.vat)
            ((clipperUpchostVatTargetAddress v).symm) hcodeSizeVatSolmNE
      by_cases hdepthLt : I.depth.val < 1024
      · obtain ⟨cA_vat, σ_vat, zVat, outVat, A_vat, k1599, C1599,
            rd1599, hcallVatEvmRaw, houtVatSize⟩ :=
          RD.clipperUpchostVatIlksPostCall v hpatch hreach hcodeSizeVatNE hdepthLt hperm
        cases zVat
        · have hcallVatEvm :
              typedCallViaEVM (config v)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                (EVM.address v.vat) "vatIlks" 0 [v.ilk]
                (false,
                  { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                      accountMap := σ_vat
                      substate := A_vat
                      createdAccounts := cA_vat },
                  outVat) true := by
            simpa using hcallVatEvmRaw
          exact clipperUpchostVatIlksCallFailureBodyCore v hpatch hcode hwv hdispatch hdecode
            (by simpa using rd1599) hcallVatEvm houtVatSize hvatCodeSolm hAccounts
        · have hcallVatEvm :
              typedCallViaEVM (config v)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                (EVM.address v.vat) "vatIlks" 0 [v.ilk]
                (true,
                  { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                      accountMap := σ_vat
                      substate := A_vat
                      createdAccounts := cA_vat },
                  outVat) true := by
            simpa using hcallVatEvmRaw
          by_cases hshort : outVat.size < 160
          · exact clipperUpchostVatIlksDecodeShortBodyCore v hpatch hcode hwv hdispatch
              hdecode (by simpa [clipperVatIlksPostCallMem] using rd1599) hcallVatEvm
              hshort houtVatSize hvatCodeSolm hAccounts
          · have hloVat : 160 ≤ outVat.size := by omega
            by_cases hcodeSizeDog :
                Reasoning.Theory.extCodeSizeWord σ_vat
                  (clipperUpchostDogTarget σ_vat I) = ⟨0⟩
            · exact clipperUpchostDogChopNoCodeBodyCore v hpatch hcode hwv hdispatch
                hdecode (by simpa [clipperVatIlksPostCallMem] using rd1599) hcallVatEvm
                hloVat houtVatSize hvatCodeSolm hAccounts hcodeSizeDog
            · have hcodeSizeDogNE :
                  Reasoning.Theory.extCodeSizeWord σ_vat
                    (clipperUpchostDogTarget σ_vat I) ≠ ⟨0⟩ := hcodeSizeDog
              obtain ⟨_, _, rd1617Dog⟩ :=
                RD.clipperUpchostVatIlksCallSuccessToDecode v hpatch
                  (by simpa [clipperVatIlksPostCallMem] using rd1599)
              obtain ⟨k1643, C1643, rd1643Dog⟩ :=
                RD.clipperUpchostVatIlksReturnDecodeOk v hpatch rd1617Dog
                  hloVat houtVatSize
              obtain ⟨cA_dog, σ_dog, zDog, outDog, A_dog, k1761, C1761,
                  rd1761, hcallDogEvmRaw, houtDogSize⟩ :=
                RD.clipperUpchostDogChopPostCall
                  (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                  (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
                  (cA_vat := cA_vat) (σ_vat := σ_vat) (A_vat := A_vat)
                  (out := outVat) (k := k1643) (C := C1643)
                  (sel := clipperSelWord I) v hpatch rd1643Dog
                  hloVat houtVatSize hcodeSizeDogNE hdepthLt hperm
              cases zDog
              · have hcallDogEvm :
                    typedCallViaEVM (config v)
                      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                        accountMap := σ_vat
                        substate := A_vat
                        createdAccounts := cA_vat }
                      (EVM.address (AccountAddress.ofUInt256
                        (clipperUpchostDogTarget σ_vat I)))
                      "chop" 0 [v.ilk]
                      (false,
                        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                          accountMap := σ_dog
                          substate := A_dog
                          createdAccounts := cA_dog },
                        outDog) true := by
                  simpa using hcallDogEvmRaw
                exact clipperUpchostDogChopCallFailureBodyCore v hpatch hcode hwv
                  hdispatch hdecode (by simpa [clipperVatIlksPostCallMem] using rd1599)
                  hcallVatEvm
                  (by simpa [clipperDogChopPostCallMem, clipperDogChopPostCallAw] using rd1761)
                  hcallDogEvm hloVat houtVatSize houtDogSize hvatCodeSolm hAccounts
                  hcodeSizeDogNE
              · have hcallDogEvm :
                    typedCallViaEVM (config v)
                      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                        accountMap := σ_vat
                        substate := A_vat
                        createdAccounts := cA_vat }
                      (EVM.address (AccountAddress.ofUInt256
                        (clipperUpchostDogTarget σ_vat I)))
                      "chop" 0 [v.ilk]
                      (true,
                        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                          accountMap := σ_dog
                          substate := A_dog
                          createdAccounts := cA_dog },
                        outDog) true := by
                  simpa using hcallDogEvmRaw
                exact if hshortDog : outDog.size < 32 then
                  clipperUpchostDogChopDecodeShortBodyCore v hpatch hcode hwv
                    hdispatch hdecode (by simpa [clipperVatIlksPostCallMem] using rd1599)
                    hcallVatEvm
                    (by simpa [clipperDogChopPostCallMem, clipperDogChopPostCallAw]
                      using rd1761)
                    hcallDogEvm hloVat houtVatSize hshortDog houtDogSize hvatCodeSolm
                    hAccounts hcodeSizeDogNE
                else by
                  have hloDog : 32 ≤ outDog.size := by omega
                  by_cases hmul :
                      (clipperVatIlksDustWord outVat).toNat *
                        (clipperDogChopWord outDog).toNat < UInt256.size
                  · exact clipperUpchostDogChopSuccessBodyCore v hpatch hcode hperm hwv
                      hdispatch hdecode
                      (by simpa [clipperVatIlksPostCallMem] using rd1599)
                      hcallVatEvm
                      (by
                        simpa [clipperDogChopPostCallMem, clipperDogChopPostCallAw]
                          using rd1761)
                      hcallDogEvm hloVat houtVatSize hloDog houtDogSize hvatCodeSolm
                      hAccounts hcodeSizeDogNE hmul
                  · have hover :
                        UInt256.size ≤
                          (clipperVatIlksDustWord outVat).toNat *
                            (clipperDogChopWord outDog).toNat :=
                      Nat.le_of_not_gt hmul
                    exact clipperUpchostDogChopWmulRevertBodyCore v hpatch hcode hwv
                      hdispatch hdecode
                      (by simpa [clipperVatIlksPostCallMem] using rd1599)
                      hcallVatEvm
                      (by
                        simpa [clipperDogChopPostCallMem, clipperDogChopPostCallAw]
                          using rd1761)
                      hcallDogEvm hloVat houtVatSize hloDog houtDogSize hvatCodeSolm
                      hAccounts hcodeSizeDogNE hover
      · have hdepthEq : I.depth = 1024 := by
          have hval : I.depth.val = 1024 := by
            have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
            omega
          apply Fin.ext
          simpa using hval
        obtain ⟨k1599, C1599, rd1599⟩ :=
          RD.clipperUpchostVatIlksCallDepthLimit v hpatch hreach hcodeSizeVatNE hdepthEq
        let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
        let A_vat := (evmE.addAccessedAccount (EVM.address v.vat)).substate
        have hdepthInit : evmE.executionEnv.depth = 1024 := by
          simpa [evmE, initState] using hdepthEq
        have hcallVatEvm :
            typedCallViaEVM (config v) evmE (EVM.address v.vat) "vatIlks" 0 [v.ilk]
              (false,
                { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                    accountMap := σ_evm
                    substate := A_vat
                    createdAccounts := cA },
                ByteArray.empty) true := by
          simpa [evmE, A_vat, initState] using
            (callNotMade_depthLimit (cfg := config v) (evm := evmE)
              (tgt := EVM.address v.vat) (name := "vatIlks") (args := [v.ilk])
              (callPerm := true)
              (calldata :=
                (clipperVatIlksCalldataMem (clipperUpchostIlkWord v)
                  solcFreePtrMem).readWithPadding 128 36)
              (clipperVatIlksEncode_eq v) hdepthInit)
        exact clipperUpchostVatIlksCallFailureBodyCore v hpatch hcode hwv hdispatch hdecode
          (by simpa using rd1599) hcallVatEvm (by native_decide) hvatCodeSolm hAccounts

end Benchmarks.Dss.Clipper
