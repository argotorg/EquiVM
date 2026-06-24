import Examples.StringStore.Getters

/-!
# StringStore — no-argument clear branches

This module contains the dispatcher and Solm-side facts for `clearCurrent()` and `clearAll()`.
Keeping these out of `Runtime.lean` lets the final runtime assembly theorem be edited without
re-elaborating these branch facts.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace StringStore

theorem stringStoreDispatch_clearCurrent {cd : ByteArray}
    (hsel : ((⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg stringStoreContract cd = some clearCurrentTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [setTransition, appendToHistoryTransition, replaceFromHistoryTransition,
      dropLastTransition])
    (post := [clearAllTransition, storeRawTransition, currentLengthGetter, historyLengthGetter,
      rawLengthGetter]) rfl ?_
    (by rw [selectorOf, clearCurrentSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · rw [selectorOf, setSelectorBytes, hcd]; decide
  · rw [selectorOf, appendToHistorySelectorBytes, hcd]; decide
  · rw [selectorOf, replaceFromHistorySelectorBytes, hcd]; decide
  · rw [selectorOf, dropLastSelectorBytes, hcd]; decide

theorem stringStoreDispatch_clearAll {cd : ByteArray}
    (hsel : ((⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg stringStoreContract cd = some clearAllTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [setTransition, appendToHistoryTransition, replaceFromHistoryTransition,
      dropLastTransition, clearCurrentTransition])
    (post := [storeRawTransition, currentLengthGetter, historyLengthGetter, rawLengthGetter]) rfl ?_
    (by rw [selectorOf, clearAllSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, setSelectorBytes, hcd]; decide
  · rw [selectorOf, appendToHistorySelectorBytes, hcd]; decide
  · rw [selectorOf, replaceFromHistorySelectorBytes, hcd]; decide
  · rw [selectorOf, dropLastSelectorBytes, hcd]; decide
  · rw [selectorOf, clearCurrentSelectorBytes, hcd]; decide

theorem stringStoreReachClearCurrent {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stringStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨442⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  have hmatches := stringStoreHighMatches 2 (by omega) hsz hsel
  exact stringStoreReachHighBody 2 (by omega) ⟨442⟩ hcode hwv hsz hsize
    (stringStorePivotNotTaken 2 (by omega) hsz hsel)
    hmatches.1 hmatches.2 (by jump_dest) (by decide)

theorem stringStoreReachClearAll {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stringStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨472⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  have hmatches := stringStoreHighMatches 3 (by omega) hsz hsel
  exact stringStoreReachHighBody 3 (by omega) ⟨472⟩ hcode hwv hsz hsize
    (stringStorePivotNotTaken 3 (by omega) hsz hsel)
    hmatches.1 hmatches.2 (by jump_dest) (by decide)

theorem bool_eq_false_of_not_true {b : Bool} (h : ¬ b = true) : b = false := by
  cases b <;> simp at h ⊢

abbrev emptyBytesKeccakValue : Value :=
  .fixedBytes ⟨31, by decide⟩ (ffi.KEC (ByteArray.mk #[])).toList

/-- `keccak256("")` ABI-encodes as its 32-byte hash.  `ffi.KEC` is opaque to Lean, matching the
selector axioms in `Bytecode.lean`; this records the standard fixed output size for this concrete
hash. -/
axiom emptyBytesKeccakReturnEncoding :
    encodeReturnValue? bytes32 emptyBytesKeccakValue = some (ffi.KEC (ByteArray.mk #[]))

theorem evalKeccakNewBytesZero {cfg solm evm} :
    evalExpr? cfg solm evm (.keccak256 (.newBytes (.intLit 0))) =
      .ok emptyBytesKeccakValue := by
  simp [emptyBytesKeccakValue, evalExpr?, EvalResult.bind, bind, pure]

theorem clearCurrentBodyReturns {evm evm' : EVM.State}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hdel : deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
      evm currentRef = .ok evm') :
    ExecTransitionBody stringStoreConfig stringStoreContract evm ∅ clearCurrentTransition.body
      (.returned { contract := stringStoreContract, locals := ∅ } evm'
        (some emptyBytesKeccakValue)) := by
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.delete hdel) <|
        ExecBlock.consReturn (ExecStmt.return evalKeccakNewBytesZero)

theorem uInt256_shiftRight_zero_left (s : UInt256) :
    UInt256.shiftRight (⟨0⟩ : UInt256) s = ⟨0⟩ := by
  cases s with
  | mk val =>
    unfold UInt256.shiftRight
    simp
    intro _
    apply Fin.ext
    rw [Fin.shiftRight_val]
    simp [Nat.zero_shiftRight]

theorem fromBytes'_zero_take1_wordLE :
    fromBytes' ((EVM.Word.toBytesLEWithSizeProof (⟨0⟩ : UInt256)).1.take 1) = 0 := by
  native_decide

theorem fromBytes'_zero_take32_wordLE :
    fromBytes' ((EVM.Word.toBytesLEWithSizeProof (⟨0⟩ : UInt256)).1.take 32) = 0 := by
  native_decide

theorem fromBytes'_evmWordZero_take32_wordLE :
    fromBytes' ((EVM.Word.toBytesLEWithSizeProof (EVM.word 0)).1.take 32) = 0 := by
  native_decide

theorem storageLocLoad_bytesLikeLengthLoc_zero {evm : EVM.State} {base : UInt256}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner base = ⟨0⟩) :
    storageLocLoad evm (bytesLikeLengthLoc base evm) = .int 0 := by
  unfold bytesLikeLengthLoc checkBytesPacked storageLocLoad wordToElem
  simp [hload, uint256Int, fromBytes'_zero_take1_wordLE, uInt256_shiftRight_zero_left]

theorem checkBytesPacked_of_storageLoad_land_one_zero {evm : EVM.State}
    {base header : UInt256}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner base = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩) :
    checkBytesPacked base evm = true := by
  unfold checkBytesPacked
  rw [hload]
  have hmod : header.toNat % 2 = 0 := by
    have h := congrArg UInt256.toNat hflag
    simpa [uInt256_land_one_toNat] using h
  cases header with
  | mk val =>
      cases val with
      | mk n hn =>
          have hnmod : n % 2 = 0 := by
            simpa [UInt256.toNat] using hmod
          have hfin :
              (⟨n, hn⟩ : Fin UInt256.size) % (2 : Fin UInt256.size) = 0 := by
            apply Fin.ext
            change n % (2 % UInt256.size) = 0
            rw [show 2 % UInt256.size = 2 from by norm_num [UInt256.size], hnmod]
          simp [hfin]

theorem solidityDecodeBytesLengthHeader_zero :
    solidityDecodeBytesLengthHeader ⟨0⟩ = .ok 0 := by
  have hflag : UInt256.land (⟨0⟩ : UInt256) ⟨1⟩ = ⟨0⟩ := by native_decide
  have hraw : UInt256.div (⟨0⟩ : UInt256) ⟨2⟩ = ⟨0⟩ := by native_decide
  have hmask : UInt256.land (⟨0⟩ : UInt256) ⟨127⟩ = ⟨0⟩ := by native_decide
  have hlt : UInt256.lt (UInt256.land (⟨0⟩ : UInt256) ⟨127⟩) ⟨32⟩ = ⟨1⟩ := by
    native_decide
  have hvalid : UInt256.sub (⟨0⟩ : UInt256)
      (UInt256.lt (UInt256.land (⟨0⟩ : UInt256) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    native_decide
  have hvalidFinal : UInt256.sub (⟨0⟩ : UInt256)
      (UInt256.lt (⟨0⟩ : UInt256) ⟨32⟩) ≠ ⟨0⟩ := by
    native_decide
  simp [solidityDecodeBytesLengthHeader, hflag, hraw, hmask, hvalidFinal]

theorem solidityDecodeBytesLengthHeader_short_valid {header len : UInt256}
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    solidityDecodeBytesLengthHeader header = .ok len.toNat := by
  have hvalid0 : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hflag] using hvalid
  simp [solidityDecodeBytesLengthHeader, hflag, ← hlen, hvalid0]

theorem solidityDecodeBytesLengthHeader_long_valid {header len : UInt256}
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    solidityDecodeBytesLengthHeader header = .ok len.toNat := by
  simp [solidityDecodeBytesLengthHeader, hflag, ← hlen, hvalid]

theorem checkBytesPacked_of_storageLoad_land_one_ne_zero {evm : EVM.State}
    {base header : UInt256}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner base = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩) :
    checkBytesPacked base evm = false := by
  have hlandOne : UInt256.land header ⟨1⟩ = ⟨1⟩ := by
    have hbit := uInt256_land_one_toNat header
    have hbitLt : (UInt256.land header ⟨1⟩).toNat < 2 := by
      rw [hbit]
      exact Nat.mod_lt _ (by decide)
    have hbitNeZero : (UInt256.land header ⟨1⟩).toNat ≠ 0 := by
      intro hzero
      apply hflag
      rw [← u256_ofNat_toNat (UInt256.land header ⟨1⟩), hzero]
      rfl
    have hto : (UInt256.land header ⟨1⟩).toNat = 1 := by
      omega
    rw [← u256_ofNat_toNat (UInt256.land header ⟨1⟩), hto]
    rfl
  have hmod : header.toNat % 2 = 1 := by
    have h := congrArg UInt256.toNat hlandOne
    simpa [uInt256_land_one_toNat] using h
  unfold checkBytesPacked
  rw [hload]
  cases header with
  | mk val =>
      cases val with
      | mk n hn =>
          have hnmod : n % 2 = 1 := by
            simpa [UInt256.toNat] using hmod
          have hfinNe :
              ¬ ((⟨n, hn⟩ : Fin UInt256.size) % (2 : Fin UInt256.size) = 0) := by
            intro hfin
            have hval := congrArg Fin.val hfin
            change n % (2 % UInt256.size) = 0 at hval
            rw [show 2 % UInt256.size = 2 from by norm_num [UInt256.size]] at hval
            omega
          exact decide_eq_false hfinNe

theorem storageLocLoad_uint256_zero {evm : EVM.State} {slot : UInt256}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot = ⟨0⟩) :
    storageLocLoad evm (uint256Loc slot) = .int 0 := by
  unfold storageLocLoad uint256Loc wordToElem
  simp [hload, uint256Int, fromBytes'_zero_take32_wordLE]

theorem storageLocStore_uint256_zero (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (uint256Loc slot) (.int 0) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot ⟨0⟩) := by
  unfold storageLocStore uint256Loc storageLocWriteWord valueToWord
  simp [EVM.wordOfInt, EVM.word]
  congr
  rw [List.drop_eq_nil_of_le]
  · simpa [List.append_nil] using fromBytes'_evmWordZero_take32_wordLE
  · rw [(EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2]

theorem deleteCurrentShortZero {evm : EVM.State}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = ⟨0⟩)
    (_hloc : storageLocLoad evm (bytesLikeLengthLoc ⟨0⟩ evm) = .int 0) :
    deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
      evm currentRef =
        .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ ⟨0⟩) := by
  have hdecode : solidityDecodeBytesLengthHeader (⟨0⟩ : UInt256) = .ok 0 :=
    solidityDecodeBytesLengthHeader_zero
  simp [deleteStorage?, resolveStorageRef?, evalStorageRef, evalStorageRefSteps, currentRef,
    storageTypeAt?, stringStoreConfig, stringStoreContract, storageDecls, stringSt,
    clearStorage?, clearStorageBytesLike?, stringStoreStorageLayout,
    solidityPrepareBytesWrite?, solidityBytesBaseSlotAndLength?, stringStoreLayout,
    hdecode, checkBytesPacked, solidityBytesHeaderWord, hload,
    EvalResult.ofOption, EvalResult.bind, bind, pure]
  rfl

theorem deleteCurrentShortPacked {evm : EVM.State} {header len : UInt256}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = header)
    (hpacked : checkBytesPacked ⟨0⟩ evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
      evm currentRef =
        .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ ⟨0⟩) := by
  have hdecode : solidityDecodeBytesLengthHeader header = .ok len.toNat :=
    solidityDecodeBytesLengthHeader_short_valid hflag hlen hvalid
  simp [deleteStorage?, resolveStorageRef?, evalStorageRef, evalStorageRefSteps, currentRef,
    storageTypeAt?, stringStoreConfig, stringStoreContract, storageDecls, stringSt,
    clearStorage?, clearStorageBytesLike?, stringStoreStorageLayout,
    solidityPrepareBytesWrite?, solidityBytesBaseSlotAndLength?, stringStoreLayout,
    hdecode, bytesLikeLengthLoc, hload, hpacked, solidityBytesHeaderWord,
    EvalResult.ofOption, EvalResult.bind, bind, pure]
  rfl

theorem deleteCurrentLongPrepared {evm : EVM.State} {header len : UInt256}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
      evm currentRef =
        .ok (clearSolidityBytesDataWordsFrom
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ ⟨0⟩)
          ⟨0⟩ 0 ((len.toNat + 31) / 32)) := by
  have hdecode : solidityDecodeBytesLengthHeader header = .ok len.toNat :=
    solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalid
  have hpacked : checkBytesPacked ⟨0⟩ evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hload hflag
  simp [deleteStorage?, resolveStorageRef?, evalStorageRef, evalStorageRefSteps, currentRef,
    storageTypeAt?, stringStoreConfig, stringStoreContract, storageDecls, stringSt,
    clearStorage?, clearStorageBytesLike?, stringStoreStorageLayout,
    solidityPrepareBytesWrite?, solidityBytesBaseSlotAndLength?, stringStoreLayout,
    hdecode, bytesLikeLengthLoc, hload, hpacked, solidityBytesHeaderWord,
    EvalResult.ofOption, EvalResult.bind, bind, pure]
  rfl

theorem deleteRawShortZero {evm : EVM.State}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ = ⟨0⟩)
    (_hloc : storageLocLoad evm (bytesLikeLengthLoc ⟨2⟩ evm) = .int 0) :
    deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
      evm rawRef =
        .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩ ⟨0⟩) := by
  have hdecode : solidityDecodeBytesLengthHeader (⟨0⟩ : UInt256) = .ok 0 :=
    solidityDecodeBytesLengthHeader_zero
  simp [deleteStorage?, resolveStorageRef?, evalStorageRef, evalStorageRefSteps, rawRef,
    storageTypeAt?, stringStoreConfig, stringStoreContract, storageDecls, stringSt, bytesSt,
    clearStorage?, clearStorageBytesLike?, stringStoreStorageLayout,
    solidityPrepareBytesWrite?, solidityBytesBaseSlotAndLength?, stringStoreLayout,
    hdecode, checkBytesPacked, solidityBytesHeaderWord, hload,
    EvalResult.ofOption, EvalResult.bind, bind, pure]
  rfl

theorem deleteRawShortPacked {evm : EVM.State} {header len : UInt256}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ = header)
    (hpacked : checkBytesPacked ⟨2⟩ evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
      evm rawRef =
        .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩ ⟨0⟩) := by
  have hdecode : solidityDecodeBytesLengthHeader header = .ok len.toNat :=
    solidityDecodeBytesLengthHeader_short_valid hflag hlen hvalid
  simp [deleteStorage?, resolveStorageRef?, evalStorageRef, evalStorageRefSteps, rawRef,
    storageTypeAt?, stringStoreConfig, stringStoreContract, storageDecls, stringSt, bytesSt,
    clearStorage?, clearStorageBytesLike?, stringStoreStorageLayout,
    solidityPrepareBytesWrite?, solidityBytesBaseSlotAndLength?, stringStoreLayout,
    hdecode, bytesLikeLengthLoc, hload, hpacked, solidityBytesHeaderWord,
    EvalResult.ofOption, EvalResult.bind, bind, pure]
  rfl

theorem deleteRawLongPrepared {evm : EVM.State} {header len : UInt256}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
      evm rawRef =
        .ok (clearSolidityBytesDataWordsFrom
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩ ⟨0⟩)
          ⟨2⟩ 0 ((len.toNat + 31) / 32)) := by
  have hdecode : solidityDecodeBytesLengthHeader header = .ok len.toNat :=
    solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalid
  have hpacked : checkBytesPacked ⟨2⟩ evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hload hflag
  simp [deleteStorage?, resolveStorageRef?, evalStorageRef, evalStorageRefSteps, rawRef,
    storageTypeAt?, stringStoreConfig, stringStoreContract, storageDecls, stringSt, bytesSt,
    clearStorage?, clearStorageBytesLike?, stringStoreStorageLayout,
    solidityPrepareBytesWrite?, solidityBytesBaseSlotAndLength?, stringStoreLayout,
    hdecode, bytesLikeLengthLoc, hload, hpacked, solidityBytesHeaderWord,
    EvalResult.ofOption, EvalResult.bind, bind, pure]
  rfl

theorem deleteRawMalformedLong {evm : EVM.State} {header : UInt256}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
      evm rawRef = .revert := by
  have hdecode : solidityDecodeBytesLengthHeader header = .revert := by
    simp [solidityDecodeBytesLengthHeader, hflag, hbad]
  have hlenSlot : (bytesLikeLengthLoc ⟨2⟩ evm).slot = ⟨2⟩ := by
    unfold bytesLikeLengthLoc
    split <;> rfl
  have hdecodeLoad :
      solidityDecodeBytesLengthHeader
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (bytesLikeLengthLoc ⟨2⟩ evm).slot) =
        .revert := by
    rw [hlenSlot, hload]
    exact hdecode
  simp [deleteStorage?, resolveStorageRef?, evalStorageRef, evalStorageRefSteps, rawRef,
    storageTypeAt?, stringStoreConfig, stringStoreContract, storageDecls, stringSt, bytesSt,
    clearStorage?, clearStorageBytesLike?, storagePrepareResultToEval, stringStoreStorageLayout,
    solidityPrepareBytesWrite?, solidityBytesBaseSlotAndLength?, stringStoreLayout,
    hload, hdecode,
    EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem deleteRawMalformedShort {evm : EVM.State} {header : UInt256}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
      evm rawRef = .revert := by
  have hdecode : solidityDecodeBytesLengthHeader header = .revert := by
    have hbad0 :
        UInt256.sub ⟨0⟩
          (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩ := by
      simpa [hflag] using hbad
    simp [solidityDecodeBytesLengthHeader, hflag, hbad0]
  have hlenSlot : (bytesLikeLengthLoc ⟨2⟩ evm).slot = ⟨2⟩ := by
    unfold bytesLikeLengthLoc
    split <;> rfl
  have hdecodeLoad :
      solidityDecodeBytesLengthHeader
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (bytesLikeLengthLoc ⟨2⟩ evm).slot) =
        .revert := by
    rw [hlenSlot, hload]
    exact hdecode
  simp [deleteStorage?, resolveStorageRef?, evalStorageRef, evalStorageRefSteps, rawRef,
    storageTypeAt?, stringStoreConfig, stringStoreContract, storageDecls, stringSt, bytesSt,
    clearStorage?, clearStorageBytesLike?, storagePrepareResultToEval, stringStoreStorageLayout,
    solidityPrepareBytesWrite?, solidityBytesBaseSlotAndLength?, stringStoreLayout,
    hload, hdecode,
    EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem deleteHistoryZero {evm : EVM.State}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩) :
    deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
      evm historyRef =
        .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ ⟨0⟩) := by
  have hloc : storageLocLoad evm (uint256Loc ⟨1⟩) = .int 0 :=
    storageLocLoad_uint256_zero hload
  simp [deleteStorage?, resolveStorageRef?, evalStorageRef, evalStorageRefSteps, historyRef,
    storageTypeAt?, stringStoreConfig, stringStoreContract, storageDecls, stringSt, bytesSt,
    EvalResult.ofOption, EvalResult.bind, bind, pure]
  simp [clearStorage?, stringStoreStorageLayout, stringStoreLayout, hloc,
    clearArrayElems?, storageLocStore_uint256_zero, EvalResult.ofOption]

theorem clearCurrent_len_toNat_lt_sign_of_div2 {header len : UInt256}
    (hlen : len = UInt256.div header ⟨2⟩) :
    len.toNat < 2 ^ 255 := by
  have hlenNat : len.toNat = header.toNat / 2 := by
    rw [hlen, udiv_toNat]
    rw [show (⟨2⟩ : UInt256).toNat = 2 from by decide]
  rw [hlenNat]
  apply Nat.div_lt_of_lt_mul
  have hheader : header.toNat < UInt256.size := header.val.isLt
  norm_num [UInt256.size] at hheader ⊢
  exact hheader

theorem clearCurrent_land_one_eq_one_of_ne_zero {w : UInt256}
    (h : UInt256.land w ⟨1⟩ ≠ ⟨0⟩) :
    UInt256.land w ⟨1⟩ = ⟨1⟩ := by
  apply u256_inj
  change (UInt256.land w ⟨1⟩).toNat = 1
  have hbit := uInt256_land_one_toNat w
  have hlt : (UInt256.land w ⟨1⟩).toNat < 2 := by
    rw [hbit]
    exact Nat.mod_lt _ (by decide)
  have hne : (UInt256.land w ⟨1⟩).toNat ≠ 0 := by
    intro hz
    exact h (uint256_toNat_eq_zero hz)
  omega

theorem clearCurrent_ult_eq_one_of_ne_zero {a b : UInt256}
    (h : UInt256.lt a b ≠ ⟨0⟩) :
    UInt256.lt a b = ⟨1⟩ := by
  have hlt := ult_ne_zero_toNat_lt h
  exact ult_one hlt

theorem clearCurrentLongValid_gt31 {header len : UInt256}
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    UInt256.lt ⟨31⟩ len ≠ ⟨0⟩ := by
  have hland : UInt256.land header ⟨1⟩ = ⟨1⟩ :=
    clearCurrent_land_one_eq_one_of_ne_zero hflag
  have hnotLt32 : UInt256.lt len ⟨32⟩ = ⟨0⟩ := by
    by_contra hltNotZero
    have hltOne : UInt256.lt len ⟨32⟩ = ⟨1⟩ :=
      clearCurrent_ult_eq_one_of_ne_zero hltNotZero
    exact hvalid (by simp [hland, hltOne, UInt256.sub])
  have hge32 : 32 ≤ len.toNat := by
    by_contra hlt
    have hltOne : UInt256.lt len ⟨32⟩ = ⟨1⟩ :=
      ult_one (by
        simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using
          Nat.lt_of_not_ge hlt)
    rw [hltOne] at hnotLt32
    contradiction
  rw [show UInt256.lt ⟨31⟩ len = ⟨1⟩ from
    ult_one (by
      rw [show (⟨31⟩ : UInt256).toNat = 31 from by decide]
      omega)]
  decide

theorem stringStoreX_clearCurrentReachDeleteDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨442⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3189⟩
      [currentLengthHeaderWord σ I, ⟨2210⟩, ⟨0⟩, ⟨2057⟩, ⟨0⟩, ⟨450⟩,
        stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd442⟩ := hreach
  have rd2044 := evm_run rd442 with [
    jumpdest, push2 ⟨450⟩, push2 ⟨2044⟩, jump (by jump_dest)]
  have rd2201 := evm_run rd2044 with [
    jumpdest, push0, push0, push0, push2 ⟨2057⟩, swap2, swap1, push2 ⟨2198⟩,
    jump (by jump_dest), jumpdest, pop, dup1]
  obtain ⟨_, _, rd2202₀⟩ := rd2201.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2202⟩ :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2202⟩
        [currentLengthHeaderWord σ I, ⟨0⟩, ⟨2057⟩, ⟨0⟩, ⟨450⟩,
          stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [currentLengthHeaderWord, initState] using rd2202₀⟩
  exact ⟨_, _, evm_run rd2202 with [
    push2 ⟨2210⟩, swap1, push2 ⟨3189⟩, jump (by jump_dest)]⟩

theorem stringStoreX_clearCurrentDeleteShortZero {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨442⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hheader : currentLengthHeaderWord σ I = ⟨0⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2057⟩
      [⟨0⟩, ⟨450⟩, stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) k C := by
  have hdecoded₀ := stringStoreX_bytesLengthDecoderShortValidMem
    (hreach := stringStoreX_clearCurrentReachDeleteDecoder hreach)
    (header := currentLengthHeaderWord σ I) (ret := ⟨2210⟩)
    (rest := [⟨0⟩, ⟨2057⟩, ⟨0⟩, ⟨450⟩, stringStoreSelWord I])
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by rw [hheader]; decide)
    (by rw [hheader]; decide)
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2210₀⟩ := hdecoded₀
  obtain ⟨_, _, rd2210⟩ :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2210⟩
        [⟨0⟩, ⟨0⟩, ⟨2057⟩, ⟨0⟩, ⟨450⟩, stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [hheader] using rd2210₀⟩
  have rd2213pre := evm_run rd2210 with [jumpdest, push0, dup3]
  obtain ⟨_, _, rd2214⟩ := rd2213pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2214' :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2214⟩
        [⟨0⟩, ⟨0⟩, ⟨2057⟩, ⟨0⟩, ⟨450⟩, stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) k C := by
    exact ⟨_, _, by simpa [initState] using rd2214⟩
  obtain ⟨_, _, rd2214⟩ := rd2214'
  have rd2228 := evm_run rd2214 with [dup1, push1 ⟨31⟩, lt, push2 ⟨2228⟩]
  have rd2222 := rd2228.jumpiNT (by native_decide) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2254 := evm_run rd2222 with [
    pop, pop, push2 ⟨2254⟩, jump (by jump_dest)]
  exact ⟨_, _, evm_run rd2254 with [jumpdest, jump (by jump_dest)]⟩

theorem stringStoreX_clearCurrentDeleteShortValid {cA gh bl σ σ₀ A I} {g : Sat256}
    {len : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨442⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hlen :
      len = UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2057⟩
      [⟨0⟩, ⟨450⟩, stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) k C := by
  have hvalidHeader :
      UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩ := by
    simpa [← hlen] using hvalid
  have hdecoded₀ := stringStoreX_bytesLengthDecoderShortValidMem
    (hreach := stringStoreX_clearCurrentReachDeleteDecoder hreach)
    (header := currentLengthHeaderWord σ I) (ret := ⟨2210⟩)
    (rest := [⟨0⟩, ⟨2057⟩, ⟨0⟩, ⟨450⟩, stringStoreSelWord I])
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    hflag
    hvalidHeader
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2210₀⟩ := hdecoded₀
  obtain ⟨_, _, rd2210⟩ :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2210⟩
        [len, ⟨0⟩, ⟨2057⟩, ⟨0⟩, ⟨450⟩, stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [← hlen] using rd2210₀⟩
  have rd2213pre := evm_run rd2210 with [jumpdest, push0, dup3]
  obtain ⟨_, _, rd2214⟩ := rd2213pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2214' :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2214⟩
        [len, ⟨0⟩, ⟨2057⟩, ⟨0⟩, ⟨450⟩, stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) k C := by
    exact ⟨_, _, by simpa [initState] using rd2214⟩
  obtain ⟨_, _, rd2214⟩ := rd2214'
  have hvalid0 : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hflag] using hvalid
  have hlt32 : len.toNat < 32 := currentLength_short_valid_lt32 hvalid0
  have hnotGt31 : UInt256.lt ⟨31⟩ len = ⟨0⟩ :=
    currentLength_notGt31_of_lt32 hlt32
  have rd2228 := evm_run rd2214 with [dup1, push1 ⟨31⟩, lt, push2 ⟨2228⟩]
  have rd2222 := rd2228.jumpiNT (by native_decide) hnotGt31
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2254 := evm_run rd2222 with [
    pop, pop, push2 ⟨2254⟩, jump (by jump_dest)]
  exact ⟨_, _, evm_run rd2254 with [jumpdest, jump (by jump_dest)]⟩

noncomputable def clearCurrentBaseMem : ByteArray :=
  (⟨0⟩ : UInt256).toByteArray.write 0 solcFreePtrMem 0 32

noncomputable def clearCurrentBaseWord : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC (clearCurrentBaseMem.readWithPadding 0 32)))

theorem stringStoreX_clearCurrentDeleteLongValidToLoop {cA gh bl σ σ₀ A I} {g : Sat256}
    {len : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨442⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlen : len = UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩)
    (hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2342⟩
      [⟨0⟩, UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩, clearCurrentBaseWord,
        ⟨2253⟩, ⟨2057⟩, ⟨0⟩, ⟨450⟩, stringStoreSelWord I]
      clearCurrentBaseMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) k C := by
  have hdecoded₀ := stringStoreX_bytesLengthDecoderLongValidMem
    (hreach := stringStoreX_clearCurrentReachDeleteDecoder hreach)
    (header := currentLengthHeaderWord σ I) (ret := ⟨2210⟩)
    (rest := [⟨0⟩, ⟨2057⟩, ⟨0⟩, ⟨450⟩, stringStoreSelWord I])
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    hflag hvalid
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2210₀⟩ := hdecoded₀
  obtain ⟨_, _, rd2210⟩ :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2210⟩
        [len, ⟨0⟩, ⟨2057⟩, ⟨0⟩, ⟨450⟩, stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [← hlen] using rd2210₀⟩
  have rd2213pre := evm_run rd2210 with [jumpdest, push0, dup3]
  obtain ⟨_, _, rd2214⟩ := rd2213pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2214' :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2214⟩
        [len, ⟨0⟩, ⟨2057⟩, ⟨0⟩, ⟨450⟩, stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) k C := by
    exact ⟨_, _, by simpa [initState] using rd2214⟩
  obtain ⟨_, _, rd2214⟩ := rd2214'
  have rd2228 := evm_run rd2214 with [dup1, push1 ⟨31⟩, lt, push2 ⟨2228⟩]
  have rd2228J := rd2228.jumpiT (by native_decide) hgt31 (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2242 := evm_run rd2228J with [
    jumpdest, push1 ⟨31⟩, add, push1 ⟨32⟩, swap1, div, swap1, push0,
    raw mstore 0 clearCurrentBaseMem (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by simp [clearCurrentBaseMem])
      (by decide) (by evm_ov),
    push1 ⟨32⟩, push0]
  have rd2243 := evm_run rd2242 with [
    raw keccak256 0 clearCurrentBaseWord (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]; rfl)
      (by decide) (by evm_ov)]
  exact ⟨_, _, evm_run rd2243 with [
    swap1, push2 ⟨2253⟩, swap2, swap1, push2 ⟨2340⟩, jump (by jump_dest),
    jumpdest, push0]⟩

noncomputable def clearCurrentLenMem : ByteArray :=
  (⟨0⟩ : UInt256).toByteArray.write 0 solcFreePtrMem 128 32

noncomputable def clearCurrentBytesMem : ByteArray :=
  (⟨160⟩ : UInt256).toByteArray.write 0 clearCurrentLenMem 64 32

noncomputable def clearCurrentHashReturnMem (hashWord : UInt256) : ByteArray :=
  hashWord.toByteArray.write 0 clearCurrentBytesMem 160 32

noncomputable def clearCurrentLongLenMem : ByteArray :=
  (⟨0⟩ : UInt256).toByteArray.write 0 clearCurrentBaseMem 128 32

noncomputable def clearCurrentLongBytesMem : ByteArray :=
  (⟨160⟩ : UInt256).toByteArray.write 0 clearCurrentLongLenMem 64 32

noncomputable def clearCurrentLongHashReturnMem (hashWord : UInt256) : ByteArray :=
  hashWord.toByteArray.write 0 clearCurrentLongBytesMem 160 32

noncomputable def clearAllHistoryBaseMem : ByteArray :=
  (⟨1⟩ : UInt256).toByteArray.write 0 solcFreePtrMem 0 32

noncomputable def clearAllHistoryBaseWord : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC (clearAllHistoryBaseMem.readWithPadding 0 32)))

noncomputable def clearRawBaseMem : ByteArray :=
  (⟨2⟩ : UInt256).toByteArray.write 0 solcFreePtrMem 0 32

noncomputable def clearRawBaseWord : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC (clearRawBaseMem.readWithPadding 0 32)))

axiom clearAllHistoryBaseMem_from_clearRawBaseMem :
    (⟨1⟩ : UInt256).toByteArray.write 0 clearRawBaseMem 0 32 = clearAllHistoryBaseMem

axiom clearAllHistoryBaseMem_from_clearCurrentBaseMem :
    (⟨1⟩ : UInt256).toByteArray.write 0 clearCurrentBaseMem 0 32 = clearAllHistoryBaseMem

axiom clearRawBaseMem_from_clearCurrentBaseMem :
    (⟨2⟩ : UInt256).toByteArray.write 0 clearCurrentBaseMem 0 32 = clearRawBaseMem

theorem stringStoreX_clearDataWordsLoopDone {cA gh bl σinit σ₀ A I} {g : Sat256}
    {τ : AccountMap} {idx count base ret : UInt256} {rest : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2342⟩
      (idx :: count :: base :: ret :: rest) mem aw rdata (cA, τ) k C)
    (hdone : UInt256.gt count idx = ⟨0⟩)
    (hret : (D_J stringStoreBytecode 0).contains ret = true)
    (hov : rest.length + 6 ≤ 1024) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ret rest mem aw rdata (cA, τ) k C := by
  obtain ⟨_, _, rd2342⟩ := hreach
  have hcond : UInt256.isZero (UInt256.gt count idx) ≠ ⟨0⟩ := by
    rw [hdone]
    decide
  have hovStack : (idx :: count :: base :: ret :: rest).length ≤ 1024 := by
    simp only [List.length_cons]
    omega
  have hlenBase : (base :: ret :: rest).length = rest.length + 2 := by
    simp only [List.length_cons]
  have hlenRet : (ret :: rest).length = rest.length + 1 := by
    simp only [List.length_cons]
  have hlenRet : (ret :: rest).length = rest.length + 1 := by
    simp only [List.length_cons]
  have hlenCount : (count :: base :: ret :: rest).length = rest.length + 3 := by
    simp only [List.length_cons]
  have hlenIdx : (idx :: count :: base :: ret :: rest).length = rest.length + 4 := by
    simp only [List.length_cons]
  have hlenCond :
      (UInt256.isZero (UInt256.gt count idx) :: idx :: count :: base :: ret :: rest).length =
        rest.length + 5 := by
    simp only [List.length_cons]
  have hovCondStack :
      (UInt256.isZero (UInt256.gt count idx) :: idx :: count :: base :: ret :: rest).length ≤
        1024 := by
    simp only [List.length_cons]
    omega
  have rd2343 := rd2342.jumpdest (by native_decide) hovStack
  have rd2344 := rd2343.dup1 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2345 := rd2344.dup3 (by native_decide)
    (by rw [hlenBase]; omega)
  have rd2346 := rd2345.gt (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2347 := rd2346.iszero (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2350 := rd2347.push2 ⟨2364⟩ (by native_decide)
    (by rw [hlenCond]; omega)
  have rd2364 := rd2350.jumpiT (by native_decide) hcond (by jump_dest)
    (by rw [hlenIdx]; omega)
  have rd2365 := rd2364.jumpdest (by native_decide) hovStack
  have rd2366 := rd2365.pop (by native_decide)
    (by rw [hlenCount]; omega)
  have rd2367 := rd2366.pop (by native_decide)
    (by rw [hlenBase]; omega)
  have rd2368 := rd2367.pop (by native_decide)
    (by rw [hlenRet]; omega)
  exact ⟨_, _, rd2368.jump (by native_decide) hret (by omega)⟩

theorem stringStoreX_clearDataWordsLoopStep {cA gh bl σinit σ₀ A I} {g : Sat256}
    {τ : AccountMap} {idx count base ret : UInt256} {rest : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2342⟩
      (idx :: count :: base :: ret :: rest) mem aw rdata (cA, τ) k C)
    (hcontinue : UInt256.isZero (UInt256.gt count idx) = ⟨0⟩)
    (hov : rest.length + 6 ≤ 1024) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2342⟩
      (((⟨1⟩ : UInt256) + idx) :: count :: base :: ret :: rest) mem aw rdata
      (cA, sstoreAccountMap I.codeOwner τ (idx + base) ⟨0⟩) k C := by
  obtain ⟨_, _, rd2342⟩ := hreach
  have hovStack : (idx :: count :: base :: ret :: rest).length ≤ 1024 := by
    simp only [List.length_cons]
    omega
  have hlenBase : (base :: ret :: rest).length = rest.length + 2 := by
    simp only [List.length_cons]
  have hlenRet : (ret :: rest).length = rest.length + 1 := by
    simp only [List.length_cons]
  have hlenIdx : (idx :: count :: base :: ret :: rest).length = rest.length + 4 := by
    simp only [List.length_cons]
  have hlenCond :
      (UInt256.isZero (UInt256.gt count idx) :: idx :: count :: base :: ret :: rest).length =
        rest.length + 5 := by
    simp only [List.length_cons]
  have rd2343 := rd2342.jumpdest (by native_decide) hovStack
  have rd2344 := rd2343.dup1 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2345 := rd2344.dup3 (by native_decide)
    (by rw [hlenBase]; omega)
  have rd2346 := rd2345.gt (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2347 := rd2346.iszero (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2350 := rd2347.push2 ⟨2364⟩ (by native_decide)
    (by rw [hlenCond]; omega)
  have rd2351 := rd2350.jumpiNT (by native_decide) hcontinue
    (by rw [hlenIdx]; omega)
  have rd2352 := rd2351.dup3 (by native_decide)
    (by rw [hlenRet]; omega)
  have rd2353 := rd2352.dup2 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2354 := rd2353.add (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2355 := rd2354.push0 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2356 := rd2355.swap1 (by native_decide)
    (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd2357⟩ := rd2356.sstore hperm (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2359 := rd2357.push1 ⟨1⟩ (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2360 := rd2359.add (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2363 := rd2360.push2 ⟨2342⟩ (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, rd2363.jump (by native_decide) (by jump_dest)
    (by simp only [List.length_cons]; omega)⟩

def clearDataWordsLoopIndex (idx : UInt256) : Nat → UInt256
  | 0 => idx
  | n + 1 => (⟨1⟩ : UInt256) + clearDataWordsLoopIndex idx n

theorem clearDataWordsLoopIndex_zero_ofNat :
    ∀ i, clearDataWordsLoopIndex ⟨0⟩ i = UInt256.ofNat i
  | 0 => rfl
  | i + 1 => by
      simp [clearDataWordsLoopIndex, clearDataWordsLoopIndex_zero_ofNat i,
        u256_one_add_ofNat]

theorem clearDataWordsLoopIndex_succ_base (idx : UInt256) :
    ∀ i, clearDataWordsLoopIndex ((⟨1⟩ : UInt256) + idx) i =
      (⟨1⟩ : UInt256) + clearDataWordsLoopIndex idx i
  | 0 => rfl
  | i + 1 => by
      simp [clearDataWordsLoopIndex, clearDataWordsLoopIndex_succ_base idx i]

def clearDataWordsForwardFrom (owner : AccountAddress) (τ : AccountMap)
    (base idx : UInt256) : Nat → AccountMap
  | 0 => τ
  | n + 1 =>
      clearDataWordsForwardFrom owner
        (sstoreAccountMap owner τ (base + idx) ⟨0⟩) base ((⟨1⟩ : UInt256) + idx) n

theorem stringStoreX_clearDataWordsLoopGenerated {cA gh bl σinit σ₀ A I} {g : Sat256}
    {τ : AccountMap} {idx count base ret : UInt256} {rest : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256} {fuel : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2342⟩
      (idx :: count :: base :: ret :: rest) mem aw rdata (cA, τ) k C)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero (UInt256.gt count (clearDataWordsLoopIndex idx i)) = ⟨0⟩)
    (hdone : UInt256.gt count (clearDataWordsLoopIndex idx fuel) = ⟨0⟩)
    (hret : (D_J stringStoreBytecode 0).contains ret = true)
    (hov : rest.length + 6 ≤ 1024) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ret rest mem aw rdata
      (cA, clearDataWordsForwardFrom I.codeOwner τ base idx fuel) k C := by
  induction fuel generalizing idx τ with
  | zero =>
      simpa [clearDataWordsLoopIndex, clearDataWordsForwardFrom] using
        stringStoreX_clearDataWordsLoopDone
          (σinit := σinit) (τ := τ) (idx := idx) (count := count) (base := base)
          (ret := ret) (rest := rest) (mem := mem) (aw := aw) (rdata := rdata)
          hreach hdone hret hov
  | succ n ih =>
      have hstep := stringStoreX_clearDataWordsLoopStep
        (σinit := σinit) (τ := τ) (idx := idx) (count := count) (base := base)
        (ret := ret) (rest := rest) (mem := mem) (aw := aw) (rdata := rdata)
        hperm hreach
        (by simpa [clearDataWordsLoopIndex] using hcontinue 0 (Nat.zero_lt_succ n))
        hov
      have hstep' :
          ∃ k C, RD stringStoreBytecode I g
            (initState cA gh bl σinit σ₀ g A I) ⟨2342⟩
            (((⟨1⟩ : UInt256) + idx) :: count :: base :: ret :: rest) mem aw rdata
            (cA, sstoreAccountMap I.codeOwner τ (base + idx) ⟨0⟩) k C := by
        simpa [u256_add_comm idx base] using hstep
      have hcontinueTail : ∀ i, i < n →
          UInt256.isZero
            (UInt256.gt count (clearDataWordsLoopIndex ((⟨1⟩ : UInt256) + idx) i)) =
              ⟨0⟩ := by
        intro i hi
        simpa [clearDataWordsLoopIndex, clearDataWordsLoopIndex_succ_base] using
          hcontinue (i + 1) (Nat.succ_lt_succ hi)
      have hdoneTail :
          UInt256.gt count (clearDataWordsLoopIndex ((⟨1⟩ : UInt256) + idx) n) = ⟨0⟩ := by
        simpa [clearDataWordsLoopIndex, clearDataWordsLoopIndex_succ_base] using hdone
      simpa [clearDataWordsForwardFrom] using
        ih
          (idx := (⟨1⟩ : UInt256) + idx)
          (τ := sstoreAccountMap I.codeOwner τ (base + idx) ⟨0⟩)
          hstep' hcontinueTail hdoneTail

theorem stringStoreX_clearCurrentLoopReturnToHash {cA gh bl σinit σ₀ A I} {g : Sat256}
    {τ : AccountMap} {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2253⟩
      [⟨2057⟩, ⟨0⟩, ⟨450⟩, stringStoreSelWord I] mem aw rdata (cA, τ) k C) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2057⟩
      [⟨0⟩, ⟨450⟩, stringStoreSelWord I] mem aw rdata (cA, τ) k C := by
  obtain ⟨_, _, rd2253⟩ := hreach
  exact ⟨_, _, evm_run rd2253 with [jumpdest, jumpdest, jump (by jump_dest)]⟩

theorem stringStoreX_clearCurrentDeleteLongValidToHashWithLoopSchedule
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {len : UInt256} {fuel : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨442⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlen : len = UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩)
    (hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.gt (UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩)
          (clearDataWordsLoopIndex ⟨0⟩ i)) = ⟨0⟩)
    (hdone :
      UInt256.gt (UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩)
        (clearDataWordsLoopIndex ⟨0⟩ fuel) = ⟨0⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2057⟩
      [⟨0⟩, ⟨450⟩, stringStoreSelWord I]
      clearCurrentBaseMem (UInt256.ofNat 3) ByteArray.empty
      (cA, clearDataWordsForwardFrom I.codeOwner
        (sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
        clearCurrentBaseWord ⟨0⟩ fuel) k C := by
  have hloopStart := stringStoreX_clearCurrentDeleteLongValidToLoop
    (g := g) hperm hreach hflag hvalid hlen hgt31
  have hloop := stringStoreX_clearDataWordsLoopGenerated
    (σinit := σ) (τ := sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
    (idx := (⟨0⟩ : UInt256))
    (count := UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩)
    (base := clearCurrentBaseWord)
    (ret := (⟨2253⟩ : UInt256))
    (rest := [⟨2057⟩, ⟨0⟩, ⟨450⟩, stringStoreSelWord I])
    (mem := clearCurrentBaseMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (fuel := fuel)
    hperm hloopStart hcontinue hdone (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact stringStoreX_clearCurrentLoopReturnToHash hloop

theorem clearSolidityBytesDataWordsFrom_executionEnv
    (evm : EVM.State) (baseSlot : UInt256) (idx fuel : Nat) :
    (clearSolidityBytesDataWordsFrom evm baseSlot idx fuel).executionEnv =
      evm.executionEnv := by
  induction fuel generalizing evm idx with
  | zero => rfl
  | succ n ih =>
      simp [clearSolidityBytesDataWordsFrom, ih, storageStore_executionEnv]

theorem clearSolidityBytesDataWordsFrom_createdAccounts
    (evm : EVM.State) (baseSlot : UInt256) (idx fuel : Nat) :
    (clearSolidityBytesDataWordsFrom evm baseSlot idx fuel).createdAccounts =
      evm.createdAccounts := by
  induction fuel generalizing evm idx with
  | zero => rfl
  | succ n ih =>
      simp [clearSolidityBytesDataWordsFrom, ih, storageStore_createdAccounts]

theorem clearSolidityBytesDataWordsFrom_accountMap
    (evm : EVM.State) (baseSlot : UInt256) (idx fuel : Nat) :
    (clearSolidityBytesDataWordsFrom evm baseSlot idx fuel).accountMap =
      clearDataWordsForwardFrom evm.executionEnv.codeOwner evm.accountMap
        (solidityBytesDataBaseSlot baseSlot) (UInt256.ofNat idx) fuel := by
  induction fuel generalizing evm idx with
  | zero => rfl
  | succ n ih =>
      simp [clearSolidityBytesDataWordsFrom, clearDataWordsForwardFrom, solidityBytesDataSlot,
        storageStore_accountMap, storageStore_executionEnv, ih, u256_one_add_ofNat]

axiom clearSolidityRawDataWords_preserves_historyLoad (evm : EVM.State) (fuel : Nat) :
    Solm.EVM.storageLoad (clearSolidityBytesDataWordsFrom evm ⟨2⟩ 0 fuel)
        (clearSolidityBytesDataWordsFrom evm ⟨2⟩ 0 fuel).executionEnv.codeOwner ⟨1⟩ =
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩

axiom clearSolidityCurrentDataWords_preserves_rawLoad (evm : EVM.State) (fuel : Nat) :
    Solm.EVM.storageLoad (clearSolidityBytesDataWordsFrom evm ⟨0⟩ 0 fuel)
        (clearSolidityBytesDataWordsFrom evm ⟨0⟩ 0 fuel).executionEnv.codeOwner ⟨2⟩ =
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩

axiom clearSolidityCurrentDataWords_preserves_historyLoad (evm : EVM.State) (fuel : Nat) :
    Solm.EVM.storageLoad (clearSolidityBytesDataWordsFrom evm ⟨0⟩ 0 fuel)
        (clearSolidityBytesDataWordsFrom evm ⟨0⟩ 0 fuel).executionEnv.codeOwner ⟨1⟩ =
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩

theorem accountMapEquiv_clearDataWordsForwardFrom {σ τ : AccountMap}
    (owner : AccountAddress) (base idx : UInt256) :
    ∀ fuel, accountMapEquiv σ τ →
      accountMapEquiv
        (clearDataWordsForwardFrom owner σ base idx fuel)
        (clearDataWordsForwardFrom owner τ base idx fuel)
  | 0, hAccounts => hAccounts
  | n + 1, hAccounts => by
      simp [clearDataWordsForwardFrom]
      exact accountMapEquiv_clearDataWordsForwardFrom owner base ((⟨1⟩ : UInt256) + idx) n
        (accountMapEquiv_sstoreAccountMap owner (base + idx) ⟨0⟩ hAccounts)

theorem clearDataWordsForwardFrom_storage_findD_ne
    (σ : AccountMap) (owner : AccountAddress) (readSlot base idx : UInt256)
    (fuel : Nat)
    (hne : ∀ i, i < fuel → readSlot ≠ base + clearDataWordsLoopIndex idx i) :
    (((clearDataWordsForwardFrom owner σ base idx fuel).find? owner).option
        (default : UInt256) (fun acc => acc.storage.findD readSlot (default : UInt256))) =
      ((σ.find? owner).option (default : UInt256)
        (fun acc => acc.storage.findD readSlot (default : UInt256))) := by
  induction fuel generalizing σ idx with
  | zero => rfl
  | succ n ih =>
      have hhead : readSlot ≠ base + idx := by
        simpa [clearDataWordsLoopIndex] using hne 0 (Nat.zero_lt_succ n)
      have htail : ∀ i, i < n →
          readSlot ≠ base + clearDataWordsLoopIndex ((⟨1⟩ : UInt256) + idx) i := by
        intro i hi
        simpa [clearDataWordsLoopIndex, clearDataWordsLoopIndex_succ_base] using
          hne (i + 1) (Nat.succ_lt_succ hi)
      simpa [clearDataWordsForwardFrom] using
        (ih (sstoreAccountMap owner σ (base + idx) ⟨0⟩)
            ((⟨1⟩ : UInt256) + idx) htail).trans
          (sstoreAccountMap_storage_findD_ne σ owner readSlot (base + idx) ⟨0⟩ hhead)

axiom clearRawDataSlot_ne_historyLengthSlot (idx : UInt256) :
    (⟨1⟩ : UInt256) ≠ clearRawBaseWord + idx

axiom clearCurrentDataSlot_ne_rawLengthSlot (idx : UInt256) :
    (⟨2⟩ : UInt256) ≠ clearCurrentBaseWord + idx

axiom clearCurrentDataSlot_ne_historyLengthSlot (idx : UInt256) :
    (⟨1⟩ : UInt256) ≠ clearCurrentBaseWord + idx

theorem clearCurrentLenMem_eq :
    clearCurrentLenMem =
      (solcFreePtrMem ++ ffi.ByteArray.zeroes (USize.ofNat 32)) ++
        UInt256.toByteArray ⟨0⟩ := by
  rw [clearCurrentLenMem,
    toByteArray_write_eq _ _ _ (by rw [solcFreePtrMem_size]; decide)
      (by rw [solcFreePtrMem_size]; exact lt_usize _ (by norm_num))]
  norm_num [solcFreePtrMem_size]

theorem clearCurrentLenMem_size : clearCurrentLenMem.size = 160 := by
  rw [clearCurrentLenMem_eq, ByteArray.size_append, ByteArray.size_append,
    solcFreePtrMem_size, zeroes_ofNat_size _ (by norm_num), toByteArray_size]

theorem clearCurrentLenMem_read64 :
    clearCurrentLenMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [readWithPadding_eq_extract _ _ (by have := clearCurrentLenMem_size; omega),
    clearCurrentLenMem_eq,
    extract_append_left _ _ _ _
      (by rw [ByteArray.size_append, solcFreePtrMem_size,
        zeroes_ofNat_size _ (by norm_num)]; omega),
    extract_append_left _ _ _ _ (by rw [solcFreePtrMem_size]),
    ← readWithPadding_eq_extract _ _ (by have := solcFreePtrMem_size; omega),
    solcFreePtrMem_read64]

theorem clearCurrentLenMem_read128 :
    clearCurrentLenMem.readWithPadding 128 32 = UInt256.toByteArray ⟨0⟩ := by
  rw [readWithPadding_eq_extract _ _ (by have := clearCurrentLenMem_size; omega),
    clearCurrentLenMem_eq,
    extract_append_right' _ _ _ _
      (by rw [ByteArray.size_append, solcFreePtrMem_size,
        zeroes_ofNat_size _ (by norm_num)])
      (by rw [ByteArray.size_append, solcFreePtrMem_size,
        zeroes_ofNat_size _ (by norm_num), toByteArray_size])]

theorem clearCurrentBytesMem_size : clearCurrentBytesMem.size = 160 := by
  rw [clearCurrentBytesMem,
    write32_eq (UInt256.toByteArray ⟨160⟩) clearCurrentLenMem 64
      (by rw [toByteArray_size]) (by rw [clearCurrentLenMem_size]; decide),
    ByteArray.size_append, ByteArray.size_append]
  have hprefix : (clearCurrentLenMem.extract 0 64).size = 64 := by
    rw [ByteArray.size_extract, clearCurrentLenMem_size]
    omega
  have hword : ((UInt256.toByteArray ⟨160⟩).extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]
    omega
  have htail : (clearCurrentLenMem.extract (64 + 32) clearCurrentLenMem.size).size = 64 := by
    rw [ByteArray.size_extract, clearCurrentLenMem_size]
    omega
  rw [hprefix, hword, htail]

theorem clearCurrentBytesMem_read64 :
    clearCurrentBytesMem.readWithPadding 64 32 = UInt256.toByteArray ⟨160⟩ := by
  rw [clearCurrentBytesMem]
  rw [write32_read_back (UInt256.toByteArray ⟨160⟩) clearCurrentLenMem 64
    (by rw [toByteArray_size])
    (by rw [clearCurrentLenMem_size]; decide)]
  rw [toByteArray_extract_all]

theorem clearCurrentBytesMem_read128 :
    clearCurrentBytesMem.readWithPadding 128 32 = UInt256.toByteArray ⟨0⟩ := by
  rw [clearCurrentBytesMem]
  have hsame :
      ((UInt256.toByteArray ⟨160⟩).write 0 clearCurrentLenMem 64 32).readWithPadding
          128 32 =
        clearCurrentLenMem.readWithPadding 128 32 :=
    write32_read_above (UInt256.toByteArray ⟨160⟩) clearCurrentLenMem 64 128
      (by rw [toByteArray_size])
      (by rw [clearCurrentLenMem_size]; decide)
      (by decide)
      (by rw [clearCurrentLenMem_size])
  rw [hsame]
  exact clearCurrentLenMem_read128

theorem clearCurrentBytesMem_mload64 :
    (if (⟨64⟩ : UInt256).toNat ≥ clearCurrentBytesMem.size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          (clearCurrentBytesMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨160⟩ :=
  mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 5) (v := (⟨160⟩ : UInt256))
    (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, clearCurrentBytesMem_size];
        decide)
    (by decide)
    (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
      clearCurrentBytesMem_read64)

theorem clearCurrentBytesMem_mload128 :
    (if (⟨128⟩ : UInt256).toNat ≥ clearCurrentBytesMem.size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          (clearCurrentBytesMem.readWithPadding (⟨128⟩ : UInt256).toNat 32))) = ⟨0⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨128⟩ : UInt256)) (aw := UInt256.ofNat 5) (v := (⟨0⟩ : UInt256))
    (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide, clearCurrentBytesMem_size];
        decide)
    (by decide)
    (by simpa [show (⟨128⟩ : UInt256).toNat = 128 from by decide] using
      clearCurrentBytesMem_read128)

theorem clearCurrentBytesMem_keccakEmpty :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (clearCurrentBytesMem.readWithPadding (⟨160⟩ : UInt256).toNat
          (⟨0⟩ : UInt256).toNat)))
      = uInt256OfByteArray (ffi.KEC ByteArray.empty) := by
  rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide,
    show (⟨0⟩ : UInt256).toNat = 0 from by decide]
  simp [ByteArray.readWithPadding, ByteArray.readWithoutPadding, clearCurrentBytesMem_size,
    zeroes_zero, uInt256OfByteArray_eq]

theorem clearCurrentHashReturnMem_size (hashWord : UInt256) :
    (clearCurrentHashReturnMem hashWord).size = 192 := by
  rw [clearCurrentHashReturnMem,
    toByteArray_write_eq _ _ _ (by rw [clearCurrentBytesMem_size])
      (by rw [clearCurrentBytesMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append,
    clearCurrentBytesMem_size, zeroes_ofNat_size _ (by norm_num), toByteArray_size]

theorem clearCurrentHashReturnMem_read64 (hashWord : UInt256) :
    (clearCurrentHashReturnMem hashWord).readWithPadding 64 32 =
      UInt256.toByteArray ⟨160⟩ := by
  rw [clearCurrentHashReturnMem]
  rw [write32_read_below (UInt256.toByteArray hashWord) clearCurrentBytesMem 160 64
    (by rw [toByteArray_size])
    (by rw [clearCurrentBytesMem_size])
    (by decide)]
  exact clearCurrentBytesMem_read64

theorem clearCurrentHashReturnMem_mload64 (hashWord : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (clearCurrentHashReturnMem hashWord).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((clearCurrentHashReturnMem hashWord).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) = ⟨160⟩ :=
  mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 6) (v := (⟨160⟩ : UInt256))
    (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
        clearCurrentHashReturnMem_size]; decide)
    (by decide)
    (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
      clearCurrentHashReturnMem_read64 hashWord)

theorem clearCurrentHashReturnMem_read160 (hashWord : UInt256) :
    (clearCurrentHashReturnMem hashWord).readWithPadding 160 32 =
      UInt256.toByteArray hashWord := by
  rw [clearCurrentHashReturnMem]
  rw [write32_read_back (UInt256.toByteArray hashWord) clearCurrentBytesMem 160
    (by rw [toByteArray_size])
    (by rw [clearCurrentBytesMem_size])]
  rw [toByteArray_extract_all]

theorem clearCurrentBaseMem_size : clearCurrentBaseMem.size = 96 := by
  rw [clearCurrentBaseMem,
    write32_eq (UInt256.toByteArray ⟨0⟩) solcFreePtrMem 0
      (by rw [toByteArray_size]) (by decide),
    ByteArray.size_append, ByteArray.size_append]
  have hprefix : (solcFreePtrMem.extract 0 0).size = 0 := by
    rw [ByteArray.size_extract]
    omega
  have hword : ((UInt256.toByteArray ⟨0⟩).extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]
    omega
  have htail : (solcFreePtrMem.extract (0 + 32) solcFreePtrMem.size).size = 64 := by
    rw [ByteArray.size_extract, solcFreePtrMem_size]
    omega
  rw [hprefix, hword, htail]

theorem clearCurrentBaseMem_read0 :
    clearCurrentBaseMem.readWithPadding 0 32 = UInt256.toByteArray ⟨0⟩ := by
  rw [clearCurrentBaseMem]
  rw [write32_read_back (UInt256.toByteArray ⟨0⟩) solcFreePtrMem 0
    (by rw [toByteArray_size])
    (by decide)]
  rw [toByteArray_extract_all]

theorem clearCurrentBaseWord_eq_solidityBytesDataBaseSlot :
    clearCurrentBaseWord = solidityBytesDataBaseSlot ⟨0⟩ := by
  rw [clearCurrentBaseWord, solidityBytesDataBaseSlot, clearCurrentBaseMem_read0,
    uInt256OfByteArray_eq]

theorem clearRawBaseMem_read0 :
    clearRawBaseMem.readWithPadding 0 32 = UInt256.toByteArray ⟨2⟩ := by
  rw [clearRawBaseMem]
  rw [write32_read_back (UInt256.toByteArray ⟨2⟩) solcFreePtrMem 0
    (by rw [toByteArray_size])
    (by decide)]
  rw [toByteArray_extract_all]

theorem clearRawBaseWord_eq_solidityBytesDataBaseSlot :
    clearRawBaseWord = solidityBytesDataBaseSlot ⟨2⟩ := by
  rw [clearRawBaseWord, solidityBytesDataBaseSlot, clearRawBaseMem_read0,
    uInt256OfByteArray_eq]

theorem clearCurrentBaseMem_read64 :
    clearCurrentBaseMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [clearCurrentBaseMem]
  have hsame :
      ((UInt256.toByteArray ⟨0⟩).write 0 solcFreePtrMem 0 32).readWithPadding 64 32 =
        solcFreePtrMem.readWithPadding 64 32 :=
    write32_read_above (UInt256.toByteArray ⟨0⟩) solcFreePtrMem 0 64
      (by rw [toByteArray_size])
      (by decide)
      (by decide)
      (by rw [solcFreePtrMem_size])
  rw [hsame]
  exact solcFreePtrMem_read64

theorem clearCurrentBaseMem_mload64 :
    (if (⟨64⟩ : UInt256).toNat ≥ clearCurrentBaseMem.size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          (clearCurrentBaseMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
  mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 3) (v := (⟨128⟩ : UInt256))
    (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, clearCurrentBaseMem_size];
        decide)
    (by decide)
    (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
      clearCurrentBaseMem_read64)

theorem clearCurrentLongLenMem_eq :
    clearCurrentLongLenMem =
      (clearCurrentBaseMem ++ ffi.ByteArray.zeroes (USize.ofNat 32)) ++
        UInt256.toByteArray ⟨0⟩ := by
  rw [clearCurrentLongLenMem,
    toByteArray_write_eq _ _ _ (by rw [clearCurrentBaseMem_size]; decide)
      (by rw [clearCurrentBaseMem_size]; exact lt_usize _ (by norm_num))]
  norm_num [clearCurrentBaseMem_size]

theorem clearCurrentLongLenMem_size : clearCurrentLongLenMem.size = 160 := by
  rw [clearCurrentLongLenMem_eq, ByteArray.size_append, ByteArray.size_append,
    clearCurrentBaseMem_size, zeroes_ofNat_size _ (by norm_num), toByteArray_size]

theorem clearCurrentLongLenMem_read64 :
    clearCurrentLongLenMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [readWithPadding_eq_extract _ _ (by have := clearCurrentLongLenMem_size; omega),
    clearCurrentLongLenMem_eq,
    extract_append_left _ _ _ _
      (by rw [ByteArray.size_append, clearCurrentBaseMem_size,
        zeroes_ofNat_size _ (by norm_num)]; omega),
    extract_append_left _ _ _ _ (by rw [clearCurrentBaseMem_size]),
    ← readWithPadding_eq_extract _ _ (by have := clearCurrentBaseMem_size; omega),
    clearCurrentBaseMem_read64]

theorem clearCurrentLongLenMem_read128 :
    clearCurrentLongLenMem.readWithPadding 128 32 = UInt256.toByteArray ⟨0⟩ := by
  rw [readWithPadding_eq_extract _ _ (by have := clearCurrentLongLenMem_size; omega),
    clearCurrentLongLenMem_eq,
    extract_append_right' _ _ _ _
      (by rw [ByteArray.size_append, clearCurrentBaseMem_size,
        zeroes_ofNat_size _ (by norm_num)])
      (by rw [ByteArray.size_append, clearCurrentBaseMem_size,
        zeroes_ofNat_size _ (by norm_num), toByteArray_size])]

theorem clearCurrentLongBytesMem_size : clearCurrentLongBytesMem.size = 160 := by
  rw [clearCurrentLongBytesMem,
    write32_eq (UInt256.toByteArray ⟨160⟩) clearCurrentLongLenMem 64
      (by rw [toByteArray_size]) (by rw [clearCurrentLongLenMem_size]; decide),
    ByteArray.size_append, ByteArray.size_append]
  have hprefix : (clearCurrentLongLenMem.extract 0 64).size = 64 := by
    rw [ByteArray.size_extract, clearCurrentLongLenMem_size]
    omega
  have hword : ((UInt256.toByteArray ⟨160⟩).extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]
    omega
  have htail : (clearCurrentLongLenMem.extract (64 + 32) clearCurrentLongLenMem.size).size = 64 := by
    rw [ByteArray.size_extract, clearCurrentLongLenMem_size]
    omega
  rw [hprefix, hword, htail]

theorem clearCurrentLongBytesMem_read64 :
    clearCurrentLongBytesMem.readWithPadding 64 32 = UInt256.toByteArray ⟨160⟩ := by
  rw [clearCurrentLongBytesMem]
  rw [write32_read_back (UInt256.toByteArray ⟨160⟩) clearCurrentLongLenMem 64
    (by rw [toByteArray_size])
    (by rw [clearCurrentLongLenMem_size]; decide)]
  rw [toByteArray_extract_all]

theorem clearCurrentLongBytesMem_read128 :
    clearCurrentLongBytesMem.readWithPadding 128 32 = UInt256.toByteArray ⟨0⟩ := by
  rw [clearCurrentLongBytesMem]
  have hsame :
      ((UInt256.toByteArray ⟨160⟩).write 0 clearCurrentLongLenMem 64 32).readWithPadding
          128 32 =
        clearCurrentLongLenMem.readWithPadding 128 32 :=
    write32_read_above (UInt256.toByteArray ⟨160⟩) clearCurrentLongLenMem 64 128
      (by rw [toByteArray_size])
      (by rw [clearCurrentLongLenMem_size]; decide)
      (by decide)
      (by rw [clearCurrentLongLenMem_size])
  rw [hsame]
  exact clearCurrentLongLenMem_read128

theorem clearCurrentLongBytesMem_mload64 :
    (if (⟨64⟩ : UInt256).toNat ≥ clearCurrentLongBytesMem.size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          (clearCurrentLongBytesMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨160⟩ :=
  mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 5) (v := (⟨160⟩ : UInt256))
    (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
        clearCurrentLongBytesMem_size]; decide)
    (by decide)
    (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
      clearCurrentLongBytesMem_read64)

theorem clearCurrentLongBytesMem_mload128 :
    (if (⟨128⟩ : UInt256).toNat ≥ clearCurrentLongBytesMem.size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          (clearCurrentLongBytesMem.readWithPadding (⟨128⟩ : UInt256).toNat 32))) = ⟨0⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨128⟩ : UInt256)) (aw := UInt256.ofNat 5) (v := (⟨0⟩ : UInt256))
    (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
        clearCurrentLongBytesMem_size]; decide)
    (by decide)
    (by simpa [show (⟨128⟩ : UInt256).toNat = 128 from by decide] using
      clearCurrentLongBytesMem_read128)

theorem clearCurrentLongBytesMem_keccakEmpty :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (clearCurrentLongBytesMem.readWithPadding (⟨160⟩ : UInt256).toNat
          (⟨0⟩ : UInt256).toNat)))
      = uInt256OfByteArray (ffi.KEC ByteArray.empty) := by
  rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide,
    show (⟨0⟩ : UInt256).toNat = 0 from by decide]
  simp [ByteArray.readWithPadding, ByteArray.readWithoutPadding,
    clearCurrentLongBytesMem_size, zeroes_zero, uInt256OfByteArray_eq]

theorem clearCurrentLongHashReturnMem_size (hashWord : UInt256) :
    (clearCurrentLongHashReturnMem hashWord).size = 192 := by
  rw [clearCurrentLongHashReturnMem,
    toByteArray_write_eq _ _ _ (by rw [clearCurrentLongBytesMem_size])
      (by rw [clearCurrentLongBytesMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append,
    clearCurrentLongBytesMem_size, zeroes_ofNat_size _ (by norm_num), toByteArray_size]

theorem clearCurrentLongHashReturnMem_read64 (hashWord : UInt256) :
    (clearCurrentLongHashReturnMem hashWord).readWithPadding 64 32 =
      UInt256.toByteArray ⟨160⟩ := by
  rw [clearCurrentLongHashReturnMem]
  rw [write32_read_below (UInt256.toByteArray hashWord) clearCurrentLongBytesMem 160 64
    (by rw [toByteArray_size])
    (by rw [clearCurrentLongBytesMem_size])
    (by decide)]
  exact clearCurrentLongBytesMem_read64

theorem clearCurrentLongHashReturnMem_mload64 (hashWord : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (clearCurrentLongHashReturnMem hashWord).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((clearCurrentLongHashReturnMem hashWord).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) = ⟨160⟩ :=
  mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 6) (v := (⟨160⟩ : UInt256))
    (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
        clearCurrentLongHashReturnMem_size]; decide)
    (by decide)
    (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
      clearCurrentLongHashReturnMem_read64 hashWord)

theorem clearCurrentLongHashReturnMem_read160 (hashWord : UInt256) :
    (clearCurrentLongHashReturnMem hashWord).readWithPadding 160 32 =
      UInt256.toByteArray hashWord := by
  rw [clearCurrentLongHashReturnMem]
  rw [write32_read_back (UInt256.toByteArray hashWord) clearCurrentLongBytesMem 160
    (by rw [toByteArray_size])
    (by rw [clearCurrentLongBytesMem_size])]
  rw [toByteArray_extract_all]

abbrev emptyKeccakWord : UInt256 :=
  uInt256OfByteArray (ffi.KEC ByteArray.empty)

/-- `ffi.KEC` is opaque, so the fixed 32-byte output-size roundtrip is recorded for this concrete
empty hash. -/
axiom emptyKeccakWord_toByteArray :
    UInt256.toByteArray emptyKeccakWord = ffi.KEC ByteArray.empty

theorem stringStoreX_clearCurrentHashEmpty {cA gh bl σ σ₀ A I} {g : Sat256}
    {σ' : AccountMap}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2057⟩
      [⟨0⟩, ⟨450⟩, stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ') k C) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨450⟩
      [emptyKeccakWord, stringStoreSelWord I]
      clearCurrentBytesMem (UInt256.ofNat 5) ByteArray.empty (cA, σ') k C := by
  obtain ⟨_, _, rd2057⟩ := hreach
  have rd2059 := evm_run rd2057 with [jumpdest, push0]
  have rd2068 := RD.pushConst rd2059 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2074 := evm_run rd2068 with [dup2, gt, iszero, push2 ⟨2083⟩]
  have rd2083 := rd2074.jumpiT (by native_decide) (by decide) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2091 := evm_run rd2083 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      solcFreePtrMem_mload64
      (by decide) (by evm_ov),
    swap1, dup1, dup3,
    raw mstore 6 clearCurrentLenMem (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov)]
  have rd2107 := evm_run rd2091 with [
    dup1, push1 ⟨31⟩, add, push1 ⟨31⟩, not, and, push1 ⟨32⟩, add, dup3, add,
    push1 ⟨64⟩,
    raw mstore 0 clearCurrentBytesMem (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by evm_ov)]
  have rd2113 := evm_run rd2107 with [dup1, iszero, push2 ⟨2133⟩]
  have rd2133 := rd2113.jumpiT (by native_decide) (by decide) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2141 := evm_run rd2133 with [
    jumpdest, pop, dup1,
    raw mload 0 ⟨0⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost
      clearCurrentBytesMem_mload128
      (by decide) (by evm_ov),
    swap1, push1 ⟨32⟩, add]
  have rd2142 := evm_run rd2141 with [
    raw keccak256 0 emptyKeccakWord (UInt256.ofNat 5) (by native_decide)
      mem_cost
      clearCurrentBytesMem_keccakEmpty
      (by decide) (by evm_ov)]
  exact ⟨_, _, evm_run rd2142 with [swap1, pop, swap1, jump (by jump_dest)]⟩

theorem stringStoreX_clearCurrentReturnFromWrapper {cA gh bl σ σ₀ A I} {g : Sat256}
    {σ' : AccountMap}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨450⟩
      [emptyKeccakWord, stringStoreSelWord I]
      clearCurrentBytesMem (UInt256.ofNat 5) ByteArray.empty (cA, σ') k C) :
    RDret stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ')
      (UInt256.toByteArray emptyKeccakWord) := by
  obtain ⟨_, _, rd450⟩ := hreach
  have rd3074 := evm_run rd450 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨160⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost
      clearCurrentBytesMem_mload64
      (by decide) (by evm_ov),
    push2 ⟨463⟩, swap2, swap1, push2 ⟨3074⟩, jump (by jump_dest)]
  have rd3059 := evm_run rd3074 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop, push2 ⟨3093⟩,
    push0, dup4, add, dup5, push2 ⟨3059⟩, jump (by jump_dest)]
  have rd3050 := evm_run rd3059 with [
    jumpdest, push2 ⟨3068⟩, dup2, push2 ⟨3050⟩, jump (by jump_dest)]
  have rd3068 := evm_run rd3050 with [
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd3093 := evm_run rd3068 with [
    jumpdest, dup3,
    raw mstore 3 (clearCurrentHashReturnMem emptyKeccakWord) (UInt256.ofNat 6)
      (by native_decide)
      mem_cost
      (by rw [show (((⟨160⟩ : UInt256) + ⟨0⟩).toNat) = 160 from by decide]; rfl)
      (by decide) (by evm_ov),
    pop, pop, jump (by jump_dest)]
  have rd463 := evm_run rd3093 with [
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  exact evm_run rd463 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨160⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost
      (clearCurrentHashReturnMem_mload64 emptyKeccakWord)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray emptyKeccakWord) (by native_decide)
      mem_cost
      (by
        rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide,
          show (UInt256.sub ((⟨160⟩ : UInt256) + ⟨32⟩) ⟨160⟩).toNat = 32 from by decide,
          clearCurrentHashReturnMem_read160])
      (by evm_ov)]

theorem stringStoreX_clearCurrentHashEmptyLongMem {cA gh bl σ σ₀ A I} {g : Sat256}
    {σ' : AccountMap}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2057⟩
      [⟨0⟩, ⟨450⟩, stringStoreSelWord I]
      clearCurrentBaseMem (UInt256.ofNat 3) ByteArray.empty (cA, σ') k C) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨450⟩
      [emptyKeccakWord, stringStoreSelWord I]
      clearCurrentLongBytesMem (UInt256.ofNat 5) ByteArray.empty (cA, σ') k C := by
  obtain ⟨_, _, rd2057⟩ := hreach
  have rd2059 := evm_run rd2057 with [jumpdest, push0]
  have rd2068 := RD.pushConst rd2059 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2074 := evm_run rd2068 with [dup2, gt, iszero, push2 ⟨2083⟩]
  have rd2083 := rd2074.jumpiT (by native_decide) (by decide) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2091 := evm_run rd2083 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      clearCurrentBaseMem_mload64
      (by decide) (by evm_ov),
    swap1, dup1, dup3,
    raw mstore 6 clearCurrentLongLenMem (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov)]
  have rd2107 := evm_run rd2091 with [
    dup1, push1 ⟨31⟩, add, push1 ⟨31⟩, not, and, push1 ⟨32⟩, add, dup3, add,
    push1 ⟨64⟩,
    raw mstore 0 clearCurrentLongBytesMem (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by evm_ov)]
  have rd2113 := evm_run rd2107 with [dup1, iszero, push2 ⟨2133⟩]
  have rd2133 := rd2113.jumpiT (by native_decide) (by decide) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2141 := evm_run rd2133 with [
    jumpdest, pop, dup1,
    raw mload 0 ⟨0⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost
      clearCurrentLongBytesMem_mload128
      (by decide) (by evm_ov),
    swap1, push1 ⟨32⟩, add]
  have rd2142 := evm_run rd2141 with [
    raw keccak256 0 emptyKeccakWord (UInt256.ofNat 5) (by native_decide)
      mem_cost
      clearCurrentLongBytesMem_keccakEmpty
      (by decide) (by evm_ov)]
  exact ⟨_, _, evm_run rd2142 with [swap1, pop, swap1, jump (by jump_dest)]⟩

theorem stringStoreX_clearCurrentReturnFromLongWrapper {cA gh bl σ σ₀ A I} {g : Sat256}
    {σ' : AccountMap}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨450⟩
      [emptyKeccakWord, stringStoreSelWord I]
      clearCurrentLongBytesMem (UInt256.ofNat 5) ByteArray.empty (cA, σ') k C) :
    RDret stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ')
      (UInt256.toByteArray emptyKeccakWord) := by
  obtain ⟨_, _, rd450⟩ := hreach
  have rd3074 := evm_run rd450 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨160⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost
      clearCurrentLongBytesMem_mload64
      (by decide) (by evm_ov),
    push2 ⟨463⟩, swap2, swap1, push2 ⟨3074⟩, jump (by jump_dest)]
  have rd3059 := evm_run rd3074 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop, push2 ⟨3093⟩,
    push0, dup4, add, dup5, push2 ⟨3059⟩, jump (by jump_dest)]
  have rd3050 := evm_run rd3059 with [
    jumpdest, push2 ⟨3068⟩, dup2, push2 ⟨3050⟩, jump (by jump_dest)]
  have rd3068 := evm_run rd3050 with [
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd3093 := evm_run rd3068 with [
    jumpdest, dup3,
    raw mstore 3 (clearCurrentLongHashReturnMem emptyKeccakWord) (UInt256.ofNat 6)
      (by native_decide)
      mem_cost
      (by rw [show (((⟨160⟩ : UInt256) + ⟨0⟩).toNat) = 160 from by decide]; rfl)
      (by decide) (by evm_ov),
    pop, pop, jump (by jump_dest)]
  have rd463 := evm_run rd3093 with [
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  exact evm_run rd463 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨160⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost
      (clearCurrentLongHashReturnMem_mload64 emptyKeccakWord)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray emptyKeccakWord) (by native_decide)
      mem_cost
      (by
        rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide,
          show (UInt256.sub ((⟨160⟩ : UInt256) + ⟨32⟩) ⟨160⟩).toNat = 32 from by decide,
          clearCurrentLongHashReturnMem_read160])
      (by evm_ov)]

theorem stringStoreX_clearCurrentLongValidWithLoopSchedule {cA gh bl σ σ₀ A I}
    {g : Sat256} {len : UInt256} {fuel : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨442⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlen : len = UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩)
    (hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.gt (UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩)
          (clearDataWordsLoopIndex ⟨0⟩ i)) = ⟨0⟩)
    (hdone :
      UInt256.gt (UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩)
        (clearDataWordsLoopIndex ⟨0⟩ fuel) = ⟨0⟩) :
    RDret stringStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, clearDataWordsForwardFrom I.codeOwner
        (sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
        clearCurrentBaseWord ⟨0⟩ fuel)
      (ffi.KEC ByteArray.empty) := by
  have htoHash := stringStoreX_clearCurrentDeleteLongValidToHashWithLoopSchedule
    (g := g) (fuel := fuel) hperm hreach hflag hvalid hlen hgt31 hcontinue hdone
  have htoWrapper := stringStoreX_clearCurrentHashEmptyLongMem htoHash
  have hret := stringStoreX_clearCurrentReturnFromLongWrapper htoWrapper
  simpa [emptyKeccakWord_toByteArray] using hret

theorem stringStoreX_clearCurrentLongValid {cA gh bl σ σ₀ A I}
    {g : Sat256} {len : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨442⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlen : len = UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩)
    (hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩) :
    RDret stringStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, clearDataWordsForwardFrom I.codeOwner
        (sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
        clearCurrentBaseWord ⟨0⟩
        (UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩).toNat)
      (ffi.KEC ByteArray.empty) := by
  let count := UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩
  have hcontinue : ∀ i, i < count.toNat →
      UInt256.isZero (UInt256.gt count (clearDataWordsLoopIndex ⟨0⟩ i)) = ⟨0⟩ := by
    intro i hi
    have hidx : (clearDataWordsLoopIndex ⟨0⟩ i).toNat = i := by
      rw [clearDataWordsLoopIndex_zero_ofNat]
      exact ulit_toNat' i (lt_trans hi count.val.isLt)
    have hgt : UInt256.gt count (clearDataWordsLoopIndex ⟨0⟩ i) = ⟨1⟩ :=
      ugt_one (by simpa [hidx] using hi)
    rw [hgt]
    decide
  have hdone :
      UInt256.gt count (clearDataWordsLoopIndex ⟨0⟩ count.toNat) = ⟨0⟩ := by
    rw [clearDataWordsLoopIndex_zero_ofNat, u256_ofNat_toNat count]
    exact ugt_zero (a := count) (b := count) (Nat.le_refl _)
  simpa [count] using
    stringStoreX_clearCurrentLongValidWithLoopSchedule
      (g := g) (len := len) (fuel := count.toNat)
      hperm hreach hflag hvalid hlen hgt31 hcontinue hdone

theorem stringStoreX_clearCurrentShortZeroValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨442⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hheader : currentLengthHeaderWord σ I = ⟨0⟩) :
    RDret stringStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
      (ffi.KEC ByteArray.empty) := by
  have hret := stringStoreX_clearCurrentReturnFromWrapper
    (stringStoreX_clearCurrentHashEmpty
      (stringStoreX_clearCurrentDeleteShortZero hperm hreach hheader))
  simpa [emptyKeccakWord_toByteArray] using hret

theorem stringStoreX_clearCurrentShortValid {cA gh bl σ σ₀ A I} {g : Sat256}
    {len : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨442⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hlen :
      len = UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    RDret stringStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
      (ffi.KEC ByteArray.empty) := by
  have hret := stringStoreX_clearCurrentReturnFromWrapper
    (stringStoreX_clearCurrentHashEmpty
      (stringStoreX_clearCurrentDeleteShortValid hperm hreach hflag hlen hvalid))
  simpa [emptyKeccakWord_toByteArray] using hret

theorem stringStoreX_bytesLengthDecoderShortValidMemAcc {cA gh bl σinit σ₀ A I}
    {g : Sat256} {τ : AccountMap} {header ret : UInt256} {rest : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨3189⟩
      (header :: ret :: rest) mem aw rdata (cA, τ) k C)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hret : (D_J stringStoreBytecode 0).contains ret = true)
    (hov : rest.length + 6 ≤ 1024) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ret
      (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩ :: rest)
      mem aw rdata (cA, τ) k C := by
  obtain ⟨_, _, rd3189⟩ := hreach
  have rd3202 := evm_run rd3189 with [
    jumpdest, push0, push1 ⟨2⟩, dup3, div, swap1, pop,
    push1 ⟨1⟩, dup3, and, dup1, push2 ⟨3212⟩]
  have rd3206 := rd3202.jumpiNT (by decide) hflag
    (by simp only [List.length_cons]; omega)
  have rd3223 := evm_run rd3206 with [
    push1 ⟨127⟩, dup3, and, swap2, pop, jumpdest,
    push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨3231⟩]
  have rd3231 := rd3223.jumpiT (by decide) hvalid (by jump_dest)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rd3231 with [
    jumpdest, pop, swap2, swap1, pop, raw jump (by native_decide) hret
      (by simp only [List.length_cons]; omega)]⟩

theorem stringStoreX_bytesLengthDecoderLongValidMemAcc {cA gh bl σinit σ₀ A I}
    {g : Sat256} {τ : AccountMap} {header ret : UInt256} {rest : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨3189⟩
      (header :: ret :: rest) mem aw rdata (cA, τ) k C)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hret : (D_J stringStoreBytecode 0).contains ret = true)
    (hov : rest.length + 6 ≤ 1024) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ret
      (UInt256.div header ⟨2⟩ :: rest)
      mem aw rdata (cA, τ) k C := by
  obtain ⟨_, _, rd3189⟩ := hreach
  have rd3202 := evm_run rd3189 with [
    jumpdest, push0, push1 ⟨2⟩, dup3, div, swap1, pop,
    push1 ⟨1⟩, dup3, and, dup1, push2 ⟨3212⟩]
  have rd3212 := rd3202.jumpiT (by decide) hflag (by jump_dest)
    (by simp only [List.length_cons]; omega)
  have rd3223 := evm_run rd3212 with [
    jumpdest, push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨3231⟩]
  have rd3231 := rd3223.jumpiT (by decide) hvalid (by jump_dest)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rd3231 with [
    jumpdest, pop, swap2, swap1, pop, raw jump (by native_decide) hret
      (by simp only [List.length_cons]; omega)]⟩

theorem stringStoreX_rawLengthMalformedPanicAcc {cA gh bl σinit σ₀ A I} {g : Sat256}
    {τ : AccountMap} {stk : List UInt256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨3223⟩ stk
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C)
    (hov : stk.length + 3 ≤ 1024) :
    RDrev stringStoreBytecode g (initState cA gh bl σinit σ₀ g A I) := by
  obtain ⟨_, _, rd3223⟩ := hreach
  have rd3144 := evm_run rd3223 with [
    push2 ⟨3230⟩, push2 ⟨3144⟩, jump (by jump_dest)]
  have rd3145 := rd3144.jumpdest (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd3178 := rd3145.pushConst solcPanicSelectorWord (width := 32)
    (op := Operation.POp.PUSH32) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact evm_run rd3178 with [
    push0,
    raw mstore 0 solcPanic22Mem1 (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl]; rfl)
      (by decide) (by simp only [List.length_cons]; omega),
    push1 ⟨34⟩, push1 ⟨4⟩,
    raw mstore 0 solcPanic22Mem (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; rfl)
      (by decide) (by simp only [List.length_cons]; omega),
    push1 ⟨36⟩, push0,
    raw rev 0 (by native_decide) mem_cost
      (by simp only [List.length_cons]; omega)]

theorem stringStoreX_bytesLengthDecoderLongMalformedAcc {cA gh bl σinit σ₀ A I}
    {g : Sat256} {τ : AccountMap} {header ret : UInt256} {rest : List UInt256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨3189⟩
      (header :: ret :: rest) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, τ) k C)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) = ⟨0⟩)
    (hov : rest.length + 8 ≤ 1024) :
    RDrev stringStoreBytecode g (initState cA gh bl σinit σ₀ g A I) := by
  obtain ⟨_, _, rd3189⟩ := hreach
  have rd3202 := evm_run rd3189 with [
    jumpdest, push0, push1 ⟨2⟩, dup3, div, swap1, pop,
    push1 ⟨1⟩, dup3, and, dup1, push2 ⟨3212⟩]
  have rd3212 := rd3202.jumpiT (by decide) hflag (by jump_dest)
    (by simp only [List.length_cons]; omega)
  have rd3223 := evm_run rd3212 with [
    jumpdest, push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨3231⟩]
  have rd3223' := rd3223.jumpiNT (by decide) hbad
    (by simp only [List.length_cons]; omega)
  exact stringStoreX_rawLengthMalformedPanicAcc ⟨_, _, rd3223'⟩
    (by simp only [List.length_cons]; omega)

theorem stringStoreX_bytesLengthDecoderShortMalformedAcc {cA gh bl σinit σ₀ A I}
    {g : Sat256} {τ : AccountMap} {header ret : UInt256} {rest : List UInt256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨3189⟩
      (header :: ret :: rest) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, τ) k C)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩)
    (hov : rest.length + 8 ≤ 1024) :
    RDrev stringStoreBytecode g (initState cA gh bl σinit σ₀ g A I) := by
  obtain ⟨_, _, rd3189⟩ := hreach
  have rd3202 := evm_run rd3189 with [
    jumpdest, push0, push1 ⟨2⟩, dup3, div, swap1, pop,
    push1 ⟨1⟩, dup3, and, dup1, push2 ⟨3212⟩]
  have rd3206 := rd3202.jumpiNT (by decide) hflag
    (by simp only [List.length_cons]; omega)
  have rd3223 := evm_run rd3206 with [
    push1 ⟨127⟩, dup3, and, swap2, pop, jumpdest,
    push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨3231⟩]
  have rd3223' := rd3223.jumpiNT (by decide) hbad
    (by simp only [List.length_cons]; omega)
  exact stringStoreX_rawLengthMalformedPanicAcc ⟨_, _, rd3223'⟩
    (by simp only [List.length_cons]; omega)

theorem stringStoreX_clearAllDeleteCurrentShortZero {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨472⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hheader : currentLengthHeaderWord σ I = ⟨0⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2158⟩
      [⟨480⟩, stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) k C := by
  obtain ⟨_, _, rd472⟩ := hreach
  have rd2146 := evm_run rd472 with [
    jumpdest, push2 ⟨480⟩, push2 ⟨2146⟩, jump (by jump_dest)]
  have rd2198 := evm_run rd2146 with [
    jumpdest, push0, push0, push2 ⟨2158⟩, swap2, swap1, push2 ⟨2198⟩,
    jump (by jump_dest)]
  have rd2201 := evm_run rd2198 with [jumpdest, pop, dup1]
  obtain ⟨_, _, rd2202₀⟩ := rd2201.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2202⟩ :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2202⟩
        [currentLengthHeaderWord σ I, ⟨0⟩, ⟨2158⟩, ⟨480⟩, stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [currentLengthHeaderWord, initState] using rd2202₀⟩
  have hreach3189 :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨3189⟩
        [currentLengthHeaderWord σ I, ⟨2210⟩, ⟨0⟩, ⟨2158⟩, ⟨480⟩,
          stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, evm_run rd2202 with [
      push2 ⟨2210⟩, swap1, push2 ⟨3189⟩, jump (by jump_dest)]⟩
  have hdecoded₀ := stringStoreX_bytesLengthDecoderShortValidMem
    (hreach := hreach3189)
    (header := currentLengthHeaderWord σ I) (ret := ⟨2210⟩)
    (rest := [⟨0⟩, ⟨2158⟩, ⟨480⟩, stringStoreSelWord I])
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by rw [hheader]; decide)
    (by rw [hheader]; decide)
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2210₀⟩ := hdecoded₀
  obtain ⟨_, _, rd2210⟩ :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2210⟩
        [⟨0⟩, ⟨0⟩, ⟨2158⟩, ⟨480⟩, stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [hheader] using rd2210₀⟩
  have rd2213pre := evm_run rd2210 with [jumpdest, push0, dup3]
  obtain ⟨_, _, rd2214⟩ := rd2213pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2214' :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2214⟩
        [⟨0⟩, ⟨0⟩, ⟨2158⟩, ⟨480⟩, stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) k C := by
    exact ⟨_, _, by simpa [initState] using rd2214⟩
  obtain ⟨_, _, rd2214⟩ := rd2214'
  have rd2228 := evm_run rd2214 with [dup1, push1 ⟨31⟩, lt, push2 ⟨2228⟩]
  have rd2222 := rd2228.jumpiNT (by native_decide) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2254 := evm_run rd2222 with [pop, pop, push2 ⟨2254⟩, jump (by jump_dest)]
  exact ⟨_, _, evm_run rd2254 with [jumpdest, jump (by jump_dest)]⟩

theorem stringStoreX_clearAllDeleteCurrentShortValid {cA gh bl σ σ₀ A I} {g : Sat256}
    {len : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨472⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hlen :
      len = UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2158⟩
      [⟨480⟩, stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) k C := by
  obtain ⟨_, _, rd472⟩ := hreach
  have rd2146 := evm_run rd472 with [
    jumpdest, push2 ⟨480⟩, push2 ⟨2146⟩, jump (by jump_dest)]
  have rd2198 := evm_run rd2146 with [
    jumpdest, push0, push0, push2 ⟨2158⟩, swap2, swap1, push2 ⟨2198⟩,
    jump (by jump_dest)]
  have rd2201 := evm_run rd2198 with [jumpdest, pop, dup1]
  obtain ⟨_, _, rd2202₀⟩ := rd2201.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2202⟩ :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2202⟩
        [currentLengthHeaderWord σ I, ⟨0⟩, ⟨2158⟩, ⟨480⟩, stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [currentLengthHeaderWord, initState] using rd2202₀⟩
  have hreach3189 :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨3189⟩
        [currentLengthHeaderWord σ I, ⟨2210⟩, ⟨0⟩, ⟨2158⟩, ⟨480⟩,
          stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, evm_run rd2202 with [
      push2 ⟨2210⟩, swap1, push2 ⟨3189⟩, jump (by jump_dest)]⟩
  have hdecoded₀ := stringStoreX_bytesLengthDecoderShortValidMem
    (hreach := hreach3189)
    (header := currentLengthHeaderWord σ I) (ret := ⟨2210⟩)
    (rest := [⟨0⟩, ⟨2158⟩, ⟨480⟩, stringStoreSelWord I])
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    hflag
    (by simpa [hlen] using hvalid)
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2210₀⟩ := hdecoded₀
  obtain ⟨_, _, rd2210⟩ :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2210⟩
        [len, ⟨0⟩, ⟨2158⟩, ⟨480⟩, stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [← hlen] using rd2210₀⟩
  have rd2213pre := evm_run rd2210 with [jumpdest, push0, dup3]
  obtain ⟨_, _, rd2214⟩ := rd2213pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2214' :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2214⟩
        [len, ⟨0⟩, ⟨2158⟩, ⟨480⟩, stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) k C := by
    exact ⟨_, _, by simpa [initState] using rd2214⟩
  obtain ⟨_, _, rd2214⟩ := rd2214'
  have hvalid0 : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hflag] using hvalid
  have hlt32 : len.toNat < 32 := currentLength_short_valid_lt32 hvalid0
  have hnotGt31 : UInt256.lt ⟨31⟩ len = ⟨0⟩ :=
    currentLength_notGt31_of_lt32 hlt32
  have rd2228 := evm_run rd2214 with [dup1, push1 ⟨31⟩, lt, push2 ⟨2228⟩]
  have rd2222 := rd2228.jumpiNT (by native_decide) hnotGt31
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2254 := evm_run rd2222 with [pop, pop, push2 ⟨2254⟩, jump (by jump_dest)]
  exact ⟨_, _, evm_run rd2254 with [jumpdest, jump (by jump_dest)]⟩

theorem stringStoreX_clearAllCurrentShortMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨472⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) = ⟨0⟩) :
    RDrev stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd472⟩ := hreach
  have rd2146 := evm_run rd472 with [
    jumpdest, push2 ⟨480⟩, push2 ⟨2146⟩, jump (by jump_dest)]
  have rd2198 := evm_run rd2146 with [
    jumpdest, push0, push0, push2 ⟨2158⟩, swap2, swap1, push2 ⟨2198⟩,
    jump (by jump_dest)]
  have rd2201 := evm_run rd2198 with [jumpdest, pop, dup1]
  obtain ⟨_, _, rd2202₀⟩ := rd2201.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2202⟩ :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2202⟩
        [currentLengthHeaderWord σ I, ⟨0⟩, ⟨2158⟩, ⟨480⟩, stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [currentLengthHeaderWord, initState] using rd2202₀⟩
  have hreach3189 :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨3189⟩
        [currentLengthHeaderWord σ I, ⟨2210⟩, ⟨0⟩, ⟨2158⟩, ⟨480⟩,
          stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, evm_run rd2202 with [
      push2 ⟨2210⟩, swap1, push2 ⟨3189⟩, jump (by jump_dest)]⟩
  exact stringStoreX_bytesLengthDecoderShortMalformed
    (hreach := hreach3189)
    (header := currentLengthHeaderWord σ I) (ret := ⟨2210⟩)
    (rest := [⟨0⟩, ⟨2158⟩, ⟨480⟩, stringStoreSelWord I])
    hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem stringStoreX_clearAllCurrentLongMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨472⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) =
          ⟨0⟩) :
    RDrev stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd472⟩ := hreach
  have rd2146 := evm_run rd472 with [
    jumpdest, push2 ⟨480⟩, push2 ⟨2146⟩, jump (by jump_dest)]
  have rd2198 := evm_run rd2146 with [
    jumpdest, push0, push0, push2 ⟨2158⟩, swap2, swap1, push2 ⟨2198⟩,
    jump (by jump_dest)]
  have rd2201 := evm_run rd2198 with [jumpdest, pop, dup1]
  obtain ⟨_, _, rd2202₀⟩ := rd2201.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2202⟩ :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2202⟩
        [currentLengthHeaderWord σ I, ⟨0⟩, ⟨2158⟩, ⟨480⟩, stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [currentLengthHeaderWord, initState] using rd2202₀⟩
  have hreach3189 :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨3189⟩
        [currentLengthHeaderWord σ I, ⟨2210⟩, ⟨0⟩, ⟨2158⟩, ⟨480⟩,
          stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, evm_run rd2202 with [
      push2 ⟨2210⟩, swap1, push2 ⟨3189⟩, jump (by jump_dest)]⟩
  exact stringStoreX_bytesLengthDecoderLongMalformed
    (hreach := hreach3189)
    (header := currentLengthHeaderWord σ I) (ret := ⟨2210⟩)
    (rest := [⟨0⟩, ⟨2158⟩, ⟨480⟩, stringStoreSelWord I])
    hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem stringStoreX_clearAllDeleteCurrentLongValidToLoop {cA gh bl σ σ₀ A I}
    {g : Sat256} {len : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨472⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlen : len = UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩)
    (hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2342⟩
      [⟨0⟩, UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩, clearCurrentBaseWord,
        ⟨2253⟩, ⟨2158⟩, ⟨480⟩, stringStoreSelWord I]
      clearCurrentBaseMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) k C := by
  obtain ⟨_, _, rd472⟩ := hreach
  have rd2146 := evm_run rd472 with [
    jumpdest, push2 ⟨480⟩, push2 ⟨2146⟩, jump (by jump_dest)]
  have rd2198 := evm_run rd2146 with [
    jumpdest, push0, push0, push2 ⟨2158⟩, swap2, swap1, push2 ⟨2198⟩,
    jump (by jump_dest)]
  have rd2201 := evm_run rd2198 with [jumpdest, pop, dup1]
  obtain ⟨_, _, rd2202₀⟩ := rd2201.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2202⟩ :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2202⟩
        [currentLengthHeaderWord σ I, ⟨0⟩, ⟨2158⟩, ⟨480⟩, stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [currentLengthHeaderWord, initState] using rd2202₀⟩
  have hreach3189 :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨3189⟩
        [currentLengthHeaderWord σ I, ⟨2210⟩, ⟨0⟩, ⟨2158⟩, ⟨480⟩,
          stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, evm_run rd2202 with [
      push2 ⟨2210⟩, swap1, push2 ⟨3189⟩, jump (by jump_dest)]⟩
  have hdecoded₀ := stringStoreX_bytesLengthDecoderLongValidMem
    (hreach := hreach3189)
    (header := currentLengthHeaderWord σ I) (ret := ⟨2210⟩)
    (rest := [⟨0⟩, ⟨2158⟩, ⟨480⟩, stringStoreSelWord I])
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    hflag hvalid
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2210₀⟩ := hdecoded₀
  obtain ⟨_, _, rd2210⟩ :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2210⟩
        [len, ⟨0⟩, ⟨2158⟩, ⟨480⟩, stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [← hlen] using rd2210₀⟩
  have rd2213pre := evm_run rd2210 with [jumpdest, push0, dup3]
  obtain ⟨_, _, rd2214⟩ := rd2213pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2214' :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2214⟩
        [len, ⟨0⟩, ⟨2158⟩, ⟨480⟩, stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) k C := by
    exact ⟨_, _, by simpa [initState] using rd2214⟩
  obtain ⟨_, _, rd2214⟩ := rd2214'
  have rd2228 := evm_run rd2214 with [dup1, push1 ⟨31⟩, lt, push2 ⟨2228⟩]
  have rd2228J := rd2228.jumpiT (by native_decide) hgt31 (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2242 := evm_run rd2228J with [
    jumpdest, push1 ⟨31⟩, add, push1 ⟨32⟩, swap1, div, swap1, push0,
    raw mstore 0 clearCurrentBaseMem (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by simp [clearCurrentBaseMem])
      (by decide) (by evm_ov),
    push1 ⟨32⟩, push0]
  have rd2243 := evm_run rd2242 with [
    raw keccak256 0 clearCurrentBaseWord (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]; rfl)
      (by decide) (by evm_ov)]
  exact ⟨_, _, evm_run rd2243 with [
    swap1, push2 ⟨2253⟩, swap2, swap1, push2 ⟨2340⟩, jump (by jump_dest),
    jumpdest, push0]⟩

theorem stringStoreX_clearAllDeleteRawShortZero {cA gh bl σinit σ₀ A I} {g : Sat256}
    {τ : AccountMap}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2158⟩
      [⟨480⟩, stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, τ) k C)
    (hheader : rawLengthHeaderWord τ I = ⟨0⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2171⟩
      [⟨480⟩, stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner τ ⟨2⟩ ⟨0⟩) k C := by
  obtain ⟨_, _, rd2158⟩ := hreach
  have rd2256 := evm_run rd2158 with [
    jumpdest, push1 ⟨2⟩, push0, push2 ⟨2171⟩, swap2, swap1, push2 ⟨2256⟩,
    jump (by jump_dest)]
  have rd2259 := evm_run rd2256 with [jumpdest, pop, dup1]
  obtain ⟨_, _, rd2260₀⟩ := rd2259.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2260⟩ :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2260⟩
        [rawLengthHeaderWord τ I, ⟨2⟩, ⟨2171⟩, ⟨480⟩, stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, by simpa [rawLengthHeaderWord, initState] using rd2260₀⟩
  have hreach3189 :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨3189⟩
        [rawLengthHeaderWord τ I, ⟨2268⟩, ⟨2⟩, ⟨2171⟩, ⟨480⟩,
          stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, evm_run rd2260 with [
      push2 ⟨2268⟩, swap1, push2 ⟨3189⟩, jump (by jump_dest)]⟩
  have hdecoded₀ := stringStoreX_bytesLengthDecoderShortValidMemAcc
    (hreach := hreach3189)
    (header := rawLengthHeaderWord τ I) (ret := ⟨2268⟩)
    (rest := [⟨2⟩, ⟨2171⟩, ⟨480⟩, stringStoreSelWord I])
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by rw [hheader]; decide)
    (by rw [hheader]; decide)
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2268₀⟩ := hdecoded₀
  obtain ⟨_, _, rd2268⟩ :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2268⟩
        [⟨0⟩, ⟨2⟩, ⟨2171⟩, ⟨480⟩, stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, by simpa [hheader] using rd2268₀⟩
  have rd2271pre := evm_run rd2268 with [jumpdest, push0, dup3]
  obtain ⟨_, _, rd2272⟩ := rd2271pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2272' :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2272⟩
        [⟨0⟩, ⟨2⟩, ⟨2171⟩, ⟨480⟩, stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner τ ⟨2⟩ ⟨0⟩) k C := by
    exact ⟨_, _, by simpa [initState] using rd2272⟩
  obtain ⟨_, _, rd2272⟩ := rd2272'
  have rd2286 := evm_run rd2272 with [dup1, push1 ⟨31⟩, lt, push2 ⟨2286⟩]
  have rd2280 := rd2286.jumpiNT (by native_decide) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2312 := evm_run rd2280 with [pop, pop, push2 ⟨2312⟩, jump (by jump_dest)]
  exact ⟨_, _, evm_run rd2312 with [jumpdest, jump (by jump_dest)]⟩

theorem stringStoreX_clearAllDeleteRawShortZeroFromCurrentBaseMem
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2158⟩
      [⟨480⟩, stringStoreSelWord I]
      clearCurrentBaseMem (UInt256.ofNat 3) ByteArray.empty
      (cA, τ) k C)
    (hheader : rawLengthHeaderWord τ I = ⟨0⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2171⟩
      [⟨480⟩, stringStoreSelWord I]
      clearCurrentBaseMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner τ ⟨2⟩ ⟨0⟩) k C := by
  obtain ⟨_, _, rd2158⟩ := hreach
  have rd2256 := evm_run rd2158 with [
    jumpdest, push1 ⟨2⟩, push0, push2 ⟨2171⟩, swap2, swap1, push2 ⟨2256⟩,
    jump (by jump_dest)]
  have rd2259 := evm_run rd2256 with [jumpdest, pop, dup1]
  obtain ⟨_, _, rd2260₀⟩ := rd2259.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2260⟩ :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2260⟩
        [rawLengthHeaderWord τ I, ⟨2⟩, ⟨2171⟩, ⟨480⟩, stringStoreSelWord I]
        clearCurrentBaseMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, by simpa [rawLengthHeaderWord, initState] using rd2260₀⟩
  have hreach3189 :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨3189⟩
        [rawLengthHeaderWord τ I, ⟨2268⟩, ⟨2⟩, ⟨2171⟩, ⟨480⟩,
          stringStoreSelWord I]
        clearCurrentBaseMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, evm_run rd2260 with [
      push2 ⟨2268⟩, swap1, push2 ⟨3189⟩, jump (by jump_dest)]⟩
  have hdecoded₀ := stringStoreX_bytesLengthDecoderShortValidMemAcc
    (hreach := hreach3189)
    (header := rawLengthHeaderWord τ I) (ret := ⟨2268⟩)
    (rest := [⟨2⟩, ⟨2171⟩, ⟨480⟩, stringStoreSelWord I])
    (mem := clearCurrentBaseMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by rw [hheader]; decide)
    (by rw [hheader]; decide)
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2268₀⟩ := hdecoded₀
  obtain ⟨_, _, rd2268⟩ :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2268⟩
        [⟨0⟩, ⟨2⟩, ⟨2171⟩, ⟨480⟩, stringStoreSelWord I]
        clearCurrentBaseMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, by simpa [hheader] using rd2268₀⟩
  have rd2271pre := evm_run rd2268 with [jumpdest, push0, dup3]
  obtain ⟨_, _, rd2272⟩ := rd2271pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2272' :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2272⟩
        [⟨0⟩, ⟨2⟩, ⟨2171⟩, ⟨480⟩, stringStoreSelWord I]
        clearCurrentBaseMem (UInt256.ofNat 3) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner τ ⟨2⟩ ⟨0⟩) k C := by
    exact ⟨_, _, by simpa [initState] using rd2272⟩
  obtain ⟨_, _, rd2272⟩ := rd2272'
  have rd2286 := evm_run rd2272 with [dup1, push1 ⟨31⟩, lt, push2 ⟨2286⟩]
  have rd2280 := rd2286.jumpiNT (by native_decide) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2312 := evm_run rd2280 with [pop, pop, push2 ⟨2312⟩, jump (by jump_dest)]
  exact ⟨_, _, evm_run rd2312 with [jumpdest, jump (by jump_dest)]⟩

theorem stringStoreX_clearAllDeleteRawShortValid {cA gh bl σinit σ₀ A I} {g : Sat256}
    {τ : AccountMap} {len : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2158⟩
      [⟨480⟩, stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, τ) k C)
    (hflag : UInt256.land (rawLengthHeaderWord τ I) ⟨1⟩ = ⟨0⟩)
    (hlen :
      len = UInt256.land (UInt256.div (rawLengthHeaderWord τ I) ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land (rawLengthHeaderWord τ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2171⟩
      [⟨480⟩, stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner τ ⟨2⟩ ⟨0⟩) k C := by
  obtain ⟨_, _, rd2158⟩ := hreach
  have rd2256 := evm_run rd2158 with [
    jumpdest, push1 ⟨2⟩, push0, push2 ⟨2171⟩, swap2, swap1, push2 ⟨2256⟩,
    jump (by jump_dest)]
  have rd2259 := evm_run rd2256 with [jumpdest, pop, dup1]
  obtain ⟨_, _, rd2260₀⟩ := rd2259.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2260⟩ :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2260⟩
        [rawLengthHeaderWord τ I, ⟨2⟩, ⟨2171⟩, ⟨480⟩, stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, by simpa [rawLengthHeaderWord, initState] using rd2260₀⟩
  have hreach3189 :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨3189⟩
        [rawLengthHeaderWord τ I, ⟨2268⟩, ⟨2⟩, ⟨2171⟩, ⟨480⟩,
          stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, evm_run rd2260 with [
      push2 ⟨2268⟩, swap1, push2 ⟨3189⟩, jump (by jump_dest)]⟩
  have hdecoded₀ := stringStoreX_bytesLengthDecoderShortValidMemAcc
    (hreach := hreach3189)
    (header := rawLengthHeaderWord τ I) (ret := ⟨2268⟩)
    (rest := [⟨2⟩, ⟨2171⟩, ⟨480⟩, stringStoreSelWord I])
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    hflag
    (by simpa [hlen] using hvalid)
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2268₀⟩ := hdecoded₀
  obtain ⟨_, _, rd2268⟩ :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2268⟩
        [len, ⟨2⟩, ⟨2171⟩, ⟨480⟩, stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, by simpa [← hlen] using rd2268₀⟩
  have rd2271pre := evm_run rd2268 with [jumpdest, push0, dup3]
  obtain ⟨_, _, rd2272⟩ := rd2271pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2272' :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2272⟩
        [len, ⟨2⟩, ⟨2171⟩, ⟨480⟩, stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner τ ⟨2⟩ ⟨0⟩) k C := by
    exact ⟨_, _, by simpa [initState] using rd2272⟩
  obtain ⟨_, _, rd2272⟩ := rd2272'
  have hvalid0 : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hflag] using hvalid
  have hlt32 : len.toNat < 32 := currentLength_short_valid_lt32 hvalid0
  have hnotGt31 : UInt256.lt ⟨31⟩ len = ⟨0⟩ :=
    currentLength_notGt31_of_lt32 hlt32
  have rd2286 := evm_run rd2272 with [dup1, push1 ⟨31⟩, lt, push2 ⟨2286⟩]
  have rd2280 := rd2286.jumpiNT (by native_decide) hnotGt31
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2312 := evm_run rd2280 with [pop, pop, push2 ⟨2312⟩, jump (by jump_dest)]
  exact ⟨_, _, evm_run rd2312 with [jumpdest, jump (by jump_dest)]⟩

theorem stringStoreX_clearAllDeleteRawShortValidFromCurrentBaseMem
    {cA gh bl σinit σ₀ A I} {g : Sat256}
    {τ : AccountMap} {len : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2158⟩
      [⟨480⟩, stringStoreSelWord I]
      clearCurrentBaseMem (UInt256.ofNat 3) ByteArray.empty
      (cA, τ) k C)
    (hflag : UInt256.land (rawLengthHeaderWord τ I) ⟨1⟩ = ⟨0⟩)
    (hlen :
      len = UInt256.land (UInt256.div (rawLengthHeaderWord τ I) ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land (rawLengthHeaderWord τ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2171⟩
      [⟨480⟩, stringStoreSelWord I]
      clearCurrentBaseMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner τ ⟨2⟩ ⟨0⟩) k C := by
  obtain ⟨_, _, rd2158⟩ := hreach
  have rd2256 := evm_run rd2158 with [
    jumpdest, push1 ⟨2⟩, push0, push2 ⟨2171⟩, swap2, swap1, push2 ⟨2256⟩,
    jump (by jump_dest)]
  have rd2259 := evm_run rd2256 with [jumpdest, pop, dup1]
  obtain ⟨_, _, rd2260₀⟩ := rd2259.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2260⟩ :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2260⟩
        [rawLengthHeaderWord τ I, ⟨2⟩, ⟨2171⟩, ⟨480⟩, stringStoreSelWord I]
        clearCurrentBaseMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, by simpa [rawLengthHeaderWord, initState] using rd2260₀⟩
  have hreach3189 :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨3189⟩
        [rawLengthHeaderWord τ I, ⟨2268⟩, ⟨2⟩, ⟨2171⟩, ⟨480⟩,
          stringStoreSelWord I]
        clearCurrentBaseMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, evm_run rd2260 with [
      push2 ⟨2268⟩, swap1, push2 ⟨3189⟩, jump (by jump_dest)]⟩
  have hdecoded₀ := stringStoreX_bytesLengthDecoderShortValidMemAcc
    (hreach := hreach3189)
    (header := rawLengthHeaderWord τ I) (ret := ⟨2268⟩)
    (rest := [⟨2⟩, ⟨2171⟩, ⟨480⟩, stringStoreSelWord I])
    (mem := clearCurrentBaseMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    hflag
    (by simpa [hlen] using hvalid)
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2268₀⟩ := hdecoded₀
  obtain ⟨_, _, rd2268⟩ :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2268⟩
        [len, ⟨2⟩, ⟨2171⟩, ⟨480⟩, stringStoreSelWord I]
        clearCurrentBaseMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, by simpa [← hlen] using rd2268₀⟩
  have rd2271pre := evm_run rd2268 with [jumpdest, push0, dup3]
  obtain ⟨_, _, rd2272⟩ := rd2271pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2272' :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2272⟩
        [len, ⟨2⟩, ⟨2171⟩, ⟨480⟩, stringStoreSelWord I]
        clearCurrentBaseMem (UInt256.ofNat 3) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner τ ⟨2⟩ ⟨0⟩) k C := by
    exact ⟨_, _, by simpa [initState] using rd2272⟩
  obtain ⟨_, _, rd2272⟩ := rd2272'
  have hvalid0 : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hflag] using hvalid
  have hlt32 : len.toNat < 32 := currentLength_short_valid_lt32 hvalid0
  have hnotGt31 : UInt256.lt ⟨31⟩ len = ⟨0⟩ :=
    currentLength_notGt31_of_lt32 hlt32
  have rd2286 := evm_run rd2272 with [dup1, push1 ⟨31⟩, lt, push2 ⟨2286⟩]
  have rd2280 := rd2286.jumpiNT (by native_decide) hnotGt31
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2312 := evm_run rd2280 with [pop, pop, push2 ⟨2312⟩, jump (by jump_dest)]
  exact ⟨_, _, evm_run rd2312 with [jumpdest, jump (by jump_dest)]⟩

theorem stringStoreX_clearAllDeleteRawLongValidToLoop {cA gh bl σinit σ₀ A I}
    {g : Sat256} {τ : AccountMap} {len : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2158⟩
      [⟨480⟩, stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, τ) k C)
    (hflag : UInt256.land (rawLengthHeaderWord τ I) ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div (rawLengthHeaderWord τ I) ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land (rawLengthHeaderWord τ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩)
    (hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2342⟩
      [⟨0⟩, UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩, clearRawBaseWord,
        ⟨2311⟩, ⟨2171⟩, ⟨480⟩, stringStoreSelWord I]
      clearRawBaseMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner τ ⟨2⟩ ⟨0⟩) k C := by
  obtain ⟨_, _, rd2158⟩ := hreach
  have rd2256 := evm_run rd2158 with [
    jumpdest, push1 ⟨2⟩, push0, push2 ⟨2171⟩, swap2, swap1, push2 ⟨2256⟩,
    jump (by jump_dest)]
  have rd2259 := evm_run rd2256 with [jumpdest, pop, dup1]
  obtain ⟨_, _, rd2260₀⟩ := rd2259.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2260⟩ :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2260⟩
        [rawLengthHeaderWord τ I, ⟨2⟩, ⟨2171⟩, ⟨480⟩, stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, by simpa [rawLengthHeaderWord, initState] using rd2260₀⟩
  have hreach3189 :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨3189⟩
        [rawLengthHeaderWord τ I, ⟨2268⟩, ⟨2⟩, ⟨2171⟩, ⟨480⟩,
          stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, evm_run rd2260 with [
      push2 ⟨2268⟩, swap1, push2 ⟨3189⟩, jump (by jump_dest)]⟩
  have hdecoded₀ := stringStoreX_bytesLengthDecoderLongValidMemAcc
    (hreach := hreach3189)
    (header := rawLengthHeaderWord τ I) (ret := ⟨2268⟩)
    (rest := [⟨2⟩, ⟨2171⟩, ⟨480⟩, stringStoreSelWord I])
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    hflag
    (by simpa [← hlen] using hvalid)
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2268₀⟩ := hdecoded₀
  obtain ⟨_, _, rd2268⟩ :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2268⟩
        [len, ⟨2⟩, ⟨2171⟩, ⟨480⟩, stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, by simpa [← hlen] using rd2268₀⟩
  have rd2271pre := evm_run rd2268 with [jumpdest, push0, dup3]
  obtain ⟨_, _, rd2272⟩ := rd2271pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2272' :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2272⟩
        [len, ⟨2⟩, ⟨2171⟩, ⟨480⟩, stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner τ ⟨2⟩ ⟨0⟩) k C := by
    exact ⟨_, _, by simpa [initState] using rd2272⟩
  obtain ⟨_, _, rd2272⟩ := rd2272'
  have rd2286 := evm_run rd2272 with [dup1, push1 ⟨31⟩, lt, push2 ⟨2286⟩]
  have rd2286J := rd2286.jumpiT (by native_decide) hgt31 (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2300 := evm_run rd2286J with [
    jumpdest, push1 ⟨31⟩, add, push1 ⟨32⟩, swap1, div, swap1, push0,
    raw mstore 0 clearRawBaseMem (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by simp [clearRawBaseMem])
      (by decide) (by evm_ov),
    push1 ⟨32⟩, push0]
  have rd2301 := evm_run rd2300 with [
    raw keccak256 0 clearRawBaseWord (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]; rfl)
      (by decide) (by evm_ov)]
  exact ⟨_, _, evm_run rd2301 with [
    swap1, push2 ⟨2311⟩, swap2, swap1, push2 ⟨2340⟩, jump (by jump_dest),
    jumpdest, push0]⟩

theorem stringStoreX_clearAllRawLongLoopReturn {cA gh bl σinit σ₀ A I} {g : Sat256}
    {τ : AccountMap} {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2311⟩
      [⟨2171⟩, ⟨480⟩, stringStoreSelWord I] mem aw rdata (cA, τ) k C) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2171⟩
      [⟨480⟩, stringStoreSelWord I] mem aw rdata (cA, τ) k C := by
  obtain ⟨_, _, rd2311⟩ := hreach
  exact ⟨_, _, evm_run rd2311 with [jumpdest, jumpdest, jump (by jump_dest)]⟩

theorem stringStoreX_clearAllCurrentLongLoopReturnToRaw
    {cA gh bl σinit σ₀ A I} {g : Sat256}
    {τ : AccountMap} {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2253⟩
      [⟨2158⟩, ⟨480⟩, stringStoreSelWord I] mem aw rdata (cA, τ) k C) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2158⟩
      [⟨480⟩, stringStoreSelWord I] mem aw rdata (cA, τ) k C := by
  obtain ⟨_, _, rd2253⟩ := hreach
  exact ⟨_, _, evm_run rd2253 with [jumpdest, jumpdest, jump (by jump_dest)]⟩

theorem stringStoreX_clearAllDeleteCurrentLongValidWithLoopSchedule
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {len : UInt256} {fuel : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨472⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlen : len = UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩)
    (hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.gt (UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩)
          (clearDataWordsLoopIndex ⟨0⟩ i)) = ⟨0⟩)
    (hdone :
      UInt256.gt (UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩)
        (clearDataWordsLoopIndex ⟨0⟩ fuel) = ⟨0⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2158⟩
      [⟨480⟩, stringStoreSelWord I]
      clearCurrentBaseMem (UInt256.ofNat 3) ByteArray.empty
      (cA, clearDataWordsForwardFrom I.codeOwner
        (sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
        clearCurrentBaseWord ⟨0⟩ fuel) k C := by
  have hloopStart := stringStoreX_clearAllDeleteCurrentLongValidToLoop
    (g := g) (len := len) hperm hreach hflag hvalid hlen hgt31
  have hloop := stringStoreX_clearDataWordsLoopGenerated
    (σinit := σ) (τ := sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
    (idx := (⟨0⟩ : UInt256))
    (count := UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩)
    (base := clearCurrentBaseWord)
    (ret := (⟨2253⟩ : UInt256))
    (rest := [⟨2158⟩, ⟨480⟩, stringStoreSelWord I])
    (mem := clearCurrentBaseMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (fuel := fuel)
    hperm hloopStart hcontinue hdone (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact stringStoreX_clearAllCurrentLongLoopReturnToRaw hloop

theorem stringStoreX_clearAllDeleteCurrentLongValid
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨472⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlen : len = UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩)
    (hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2158⟩
      [⟨480⟩, stringStoreSelWord I]
      clearCurrentBaseMem (UInt256.ofNat 3) ByteArray.empty
      (cA, clearDataWordsForwardFrom I.codeOwner
        (sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
        clearCurrentBaseWord ⟨0⟩
        (UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩).toNat) k C := by
  let count := UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩
  have hcontinue : ∀ i, i < count.toNat →
      UInt256.isZero (UInt256.gt count (clearDataWordsLoopIndex ⟨0⟩ i)) = ⟨0⟩ := by
    intro i hi
    have hidx : (clearDataWordsLoopIndex ⟨0⟩ i).toNat = i := by
      rw [clearDataWordsLoopIndex_zero_ofNat]
      exact ulit_toNat' i (lt_trans hi count.val.isLt)
    have hgt : UInt256.gt count (clearDataWordsLoopIndex ⟨0⟩ i) = ⟨1⟩ :=
      ugt_one (by simpa [hidx] using hi)
    rw [hgt]
    decide
  have hdone :
      UInt256.gt count (clearDataWordsLoopIndex ⟨0⟩ count.toNat) = ⟨0⟩ := by
    rw [clearDataWordsLoopIndex_zero_ofNat, u256_ofNat_toNat count]
    exact ugt_zero (a := count) (b := count) (Nat.le_refl _)
  simpa [count] using
    stringStoreX_clearAllDeleteCurrentLongValidWithLoopSchedule
      (g := g) (len := len) (fuel := count.toNat)
      hperm hreach hflag hvalid hlen hgt31 hcontinue hdone

theorem stringStoreX_clearAllDeleteRawLongValidWithLoopSchedule
    {cA gh bl σinit σ₀ A I} {g : Sat256}
    {τ : AccountMap} {len : UInt256} {fuel : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2158⟩
      [⟨480⟩, stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, τ) k C)
    (hflag : UInt256.land (rawLengthHeaderWord τ I) ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div (rawLengthHeaderWord τ I) ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land (rawLengthHeaderWord τ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩)
    (hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.gt (UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩)
          (clearDataWordsLoopIndex ⟨0⟩ i)) = ⟨0⟩)
    (hdone :
      UInt256.gt (UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩)
        (clearDataWordsLoopIndex ⟨0⟩ fuel) = ⟨0⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2171⟩
      [⟨480⟩, stringStoreSelWord I]
      clearRawBaseMem (UInt256.ofNat 3) ByteArray.empty
      (cA, clearDataWordsForwardFrom I.codeOwner
        (sstoreAccountMap I.codeOwner τ ⟨2⟩ ⟨0⟩)
        clearRawBaseWord ⟨0⟩ fuel) k C := by
  have hloopStart := stringStoreX_clearAllDeleteRawLongValidToLoop
    (g := g) (τ := τ) (len := len) hperm hreach hflag hlen hvalid hgt31
  have hloop := stringStoreX_clearDataWordsLoopGenerated
    (σinit := σinit)
    (τ := sstoreAccountMap I.codeOwner τ ⟨2⟩ ⟨0⟩)
    (idx := (⟨0⟩ : UInt256))
    (count := UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩)
    (base := clearRawBaseWord)
    (ret := (⟨2311⟩ : UInt256))
    (rest := [⟨2171⟩, ⟨480⟩, stringStoreSelWord I])
    (mem := clearRawBaseMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (fuel := fuel)
    hperm hloopStart hcontinue hdone (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact stringStoreX_clearAllRawLongLoopReturn hloop

theorem stringStoreX_clearAllDeleteRawLongValid
    {cA gh bl σinit σ₀ A I} {g : Sat256}
    {τ : AccountMap} {len : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2158⟩
      [⟨480⟩, stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, τ) k C)
    (hflag : UInt256.land (rawLengthHeaderWord τ I) ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div (rawLengthHeaderWord τ I) ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land (rawLengthHeaderWord τ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩)
    (hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2171⟩
      [⟨480⟩, stringStoreSelWord I]
      clearRawBaseMem (UInt256.ofNat 3) ByteArray.empty
      (cA, clearDataWordsForwardFrom I.codeOwner
        (sstoreAccountMap I.codeOwner τ ⟨2⟩ ⟨0⟩)
        clearRawBaseWord ⟨0⟩
        (UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩).toNat) k C := by
  let count := UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩
  have hcontinue : ∀ i, i < count.toNat →
      UInt256.isZero (UInt256.gt count (clearDataWordsLoopIndex ⟨0⟩ i)) = ⟨0⟩ := by
    intro i hi
    have hidx : (clearDataWordsLoopIndex ⟨0⟩ i).toNat = i := by
      rw [clearDataWordsLoopIndex_zero_ofNat]
      exact ulit_toNat' i (lt_trans hi count.val.isLt)
    have hgt : UInt256.gt count (clearDataWordsLoopIndex ⟨0⟩ i) = ⟨1⟩ :=
      ugt_one (by simpa [hidx] using hi)
    rw [hgt]
    decide
  have hdone :
      UInt256.gt count (clearDataWordsLoopIndex ⟨0⟩ count.toNat) = ⟨0⟩ := by
    rw [clearDataWordsLoopIndex_zero_ofNat, u256_ofNat_toNat count]
    exact ugt_zero (a := count) (b := count) (Nat.le_refl _)
  simpa [count] using
    stringStoreX_clearAllDeleteRawLongValidWithLoopSchedule
      (g := g) (τ := τ) (len := len) (fuel := count.toNat)
      hperm hreach hflag hlen hvalid hgt31 hcontinue hdone

theorem stringStoreX_clearAllDeleteRawLongValidFromCurrentBaseMem
    {cA gh bl σinit σ₀ A I} {g : Sat256}
    {τ : AccountMap} {len : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2158⟩
      [⟨480⟩, stringStoreSelWord I]
      clearCurrentBaseMem (UInt256.ofNat 3) ByteArray.empty
      (cA, τ) k C)
    (hflag : UInt256.land (rawLengthHeaderWord τ I) ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div (rawLengthHeaderWord τ I) ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land (rawLengthHeaderWord τ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩)
    (hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2171⟩
      [⟨480⟩, stringStoreSelWord I]
      clearRawBaseMem (UInt256.ofNat 3) ByteArray.empty
      (cA, clearDataWordsForwardFrom I.codeOwner
        (sstoreAccountMap I.codeOwner τ ⟨2⟩ ⟨0⟩)
        clearRawBaseWord ⟨0⟩
        (UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩).toNat) k C := by
  let count := UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩
  obtain ⟨_, _, rd2158⟩ := hreach
  have rd2256 := evm_run rd2158 with [
    jumpdest, push1 ⟨2⟩, push0, push2 ⟨2171⟩, swap2, swap1, push2 ⟨2256⟩,
    jump (by jump_dest)]
  have rd2259 := evm_run rd2256 with [jumpdest, pop, dup1]
  obtain ⟨_, _, rd2260₀⟩ := rd2259.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2260⟩ :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2260⟩
        [rawLengthHeaderWord τ I, ⟨2⟩, ⟨2171⟩, ⟨480⟩, stringStoreSelWord I]
        clearCurrentBaseMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, by simpa [rawLengthHeaderWord, initState] using rd2260₀⟩
  have hreach3189 :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨3189⟩
        [rawLengthHeaderWord τ I, ⟨2268⟩, ⟨2⟩, ⟨2171⟩, ⟨480⟩,
          stringStoreSelWord I]
        clearCurrentBaseMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, evm_run rd2260 with [
      push2 ⟨2268⟩, swap1, push2 ⟨3189⟩, jump (by jump_dest)]⟩
  have hdecoded₀ := stringStoreX_bytesLengthDecoderLongValidMemAcc
    (hreach := hreach3189)
    (header := rawLengthHeaderWord τ I) (ret := ⟨2268⟩)
    (rest := [⟨2⟩, ⟨2171⟩, ⟨480⟩, stringStoreSelWord I])
    (mem := clearCurrentBaseMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    hflag
    (by simpa [← hlen] using hvalid)
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2268₀⟩ := hdecoded₀
  obtain ⟨_, _, rd2268⟩ :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2268⟩
        [len, ⟨2⟩, ⟨2171⟩, ⟨480⟩, stringStoreSelWord I]
        clearCurrentBaseMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, by simpa [← hlen] using rd2268₀⟩
  have rd2271pre := evm_run rd2268 with [jumpdest, push0, dup3]
  obtain ⟨_, _, rd2272⟩ := rd2271pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2272' :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2272⟩
        [len, ⟨2⟩, ⟨2171⟩, ⟨480⟩, stringStoreSelWord I]
        clearCurrentBaseMem (UInt256.ofNat 3) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner τ ⟨2⟩ ⟨0⟩) k C := by
    exact ⟨_, _, by simpa [initState] using rd2272⟩
  obtain ⟨_, _, rd2272⟩ := rd2272'
  have rd2286 := evm_run rd2272 with [dup1, push1 ⟨31⟩, lt, push2 ⟨2286⟩]
  have rd2286J := rd2286.jumpiT (by native_decide) hgt31 (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2300 := evm_run rd2286J with [
    jumpdest, push1 ⟨31⟩, add, push1 ⟨32⟩, swap1, div, swap1, push0,
    raw mstore 0 clearRawBaseMem (UInt256.ofNat 3) (by native_decide)
      mem_cost
      clearRawBaseMem_from_clearCurrentBaseMem
      (by decide) (by evm_ov),
    push1 ⟨32⟩, push0]
  have rd2301 := evm_run rd2300 with [
    raw keccak256 0 clearRawBaseWord (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]; rfl)
      (by decide) (by evm_ov)]
  have hloopStart :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2342⟩
        [⟨0⟩, count, clearRawBaseWord, ⟨2311⟩, ⟨2171⟩, ⟨480⟩,
          stringStoreSelWord I]
        clearRawBaseMem (UInt256.ofNat 3) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner τ ⟨2⟩ ⟨0⟩) k C := by
    exact ⟨_, _, by
      simpa [count] using
        (evm_run rd2301 with [
          swap1, push2 ⟨2311⟩, swap2, swap1, push2 ⟨2340⟩, jump (by jump_dest),
          jumpdest, push0])⟩
  have hcontinue : ∀ i, i < count.toNat →
      UInt256.isZero (UInt256.gt count (clearDataWordsLoopIndex ⟨0⟩ i)) = ⟨0⟩ := by
    intro i hi
    have hidx : (clearDataWordsLoopIndex ⟨0⟩ i).toNat = i := by
      rw [clearDataWordsLoopIndex_zero_ofNat]
      exact ulit_toNat' i (lt_trans hi count.val.isLt)
    have hgt : UInt256.gt count (clearDataWordsLoopIndex ⟨0⟩ i) = ⟨1⟩ :=
      ugt_one (by simpa [hidx] using hi)
    rw [hgt]
    decide
  have hdone :
      UInt256.gt count (clearDataWordsLoopIndex ⟨0⟩ count.toNat) = ⟨0⟩ := by
    rw [clearDataWordsLoopIndex_zero_ofNat, u256_ofNat_toNat count]
    exact ugt_zero (a := count) (b := count) (Nat.le_refl _)
  have hloop := stringStoreX_clearDataWordsLoopGenerated
    (σinit := σinit)
    (τ := sstoreAccountMap I.codeOwner τ ⟨2⟩ ⟨0⟩)
    (idx := (⟨0⟩ : UInt256))
    (count := count)
    (base := clearRawBaseWord)
    (ret := (⟨2311⟩ : UInt256))
    (rest := [⟨2171⟩, ⟨480⟩, stringStoreSelWord I])
    (mem := clearRawBaseMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (fuel := count.toNat)
    hperm hloopStart hcontinue hdone (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  simpa [count] using stringStoreX_clearAllRawLongLoopReturn hloop

theorem stringStoreX_clearAllRawShortMalformed {cA gh bl σinit σ₀ A I} {g : Sat256}
    {τ : AccountMap}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2158⟩
      [⟨480⟩, stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, τ) k C)
    (hflag : UInt256.land (rawLengthHeaderWord τ I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (rawLengthHeaderWord τ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (rawLengthHeaderWord τ I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) = ⟨0⟩) :
    RDrev stringStoreBytecode g (initState cA gh bl σinit σ₀ g A I) := by
  obtain ⟨_, _, rd2158⟩ := hreach
  have rd2256 := evm_run rd2158 with [
    jumpdest, push1 ⟨2⟩, push0, push2 ⟨2171⟩, swap2, swap1, push2 ⟨2256⟩,
    jump (by jump_dest)]
  have rd2259 := evm_run rd2256 with [jumpdest, pop, dup1]
  obtain ⟨_, _, rd2260₀⟩ := rd2259.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2260⟩ :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2260⟩
        [rawLengthHeaderWord τ I, ⟨2⟩, ⟨2171⟩, ⟨480⟩, stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, by simpa [rawLengthHeaderWord, initState] using rd2260₀⟩
  have hreach3189 :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨3189⟩
        [rawLengthHeaderWord τ I, ⟨2268⟩, ⟨2⟩, ⟨2171⟩, ⟨480⟩,
          stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, evm_run rd2260 with [
      push2 ⟨2268⟩, swap1, push2 ⟨3189⟩, jump (by jump_dest)]⟩
  exact stringStoreX_bytesLengthDecoderShortMalformedAcc
    (hreach := hreach3189)
    (header := rawLengthHeaderWord τ I) (ret := ⟨2268⟩)
    (rest := [⟨2⟩, ⟨2171⟩, ⟨480⟩, stringStoreSelWord I])
    hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem stringStoreX_clearAllRawLongMalformed {cA gh bl σinit σ₀ A I} {g : Sat256}
    {τ : AccountMap}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2158⟩
      [⟨480⟩, stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, τ) k C)
    (hflag : UInt256.land (rawLengthHeaderWord τ I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (rawLengthHeaderWord τ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (rawLengthHeaderWord τ I) ⟨2⟩) ⟨32⟩) =
          ⟨0⟩) :
    RDrev stringStoreBytecode g (initState cA gh bl σinit σ₀ g A I) := by
  obtain ⟨_, _, rd2158⟩ := hreach
  have rd2256 := evm_run rd2158 with [
    jumpdest, push1 ⟨2⟩, push0, push2 ⟨2171⟩, swap2, swap1, push2 ⟨2256⟩,
    jump (by jump_dest)]
  have rd2259 := evm_run rd2256 with [jumpdest, pop, dup1]
  obtain ⟨_, _, rd2260₀⟩ := rd2259.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2260⟩ :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2260⟩
        [rawLengthHeaderWord τ I, ⟨2⟩, ⟨2171⟩, ⟨480⟩, stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, by simpa [rawLengthHeaderWord, initState] using rd2260₀⟩
  have hreach3189 :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨3189⟩
        [rawLengthHeaderWord τ I, ⟨2268⟩, ⟨2⟩, ⟨2171⟩, ⟨480⟩,
          stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, evm_run rd2260 with [
      push2 ⟨2268⟩, swap1, push2 ⟨3189⟩, jump (by jump_dest)]⟩
  exact stringStoreX_bytesLengthDecoderLongMalformedAcc
    (hreach := hreach3189)
    (header := rawLengthHeaderWord τ I) (ret := ⟨2268⟩)
    (rest := [⟨2⟩, ⟨2171⟩, ⟨480⟩, stringStoreSelWord I])
    hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

axiom stringStoreX_clearAllRawShortMalformedFromCurrentBaseMem
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2158⟩
      [⟨480⟩, stringStoreSelWord I]
      clearCurrentBaseMem (UInt256.ofNat 3) ByteArray.empty
      (cA, τ) k C)
    (hflag : UInt256.land (rawLengthHeaderWord τ I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (rawLengthHeaderWord τ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (rawLengthHeaderWord τ I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) = ⟨0⟩) :
    RDrev stringStoreBytecode g (initState cA gh bl σinit σ₀ g A I)

axiom stringStoreX_clearAllRawLongMalformedFromCurrentBaseMem
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2158⟩
      [⟨480⟩, stringStoreSelWord I]
      clearCurrentBaseMem (UInt256.ofNat 3) ByteArray.empty
      (cA, τ) k C)
    (hflag : UInt256.land (rawLengthHeaderWord τ I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (rawLengthHeaderWord τ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (rawLengthHeaderWord τ I) ⟨2⟩) ⟨32⟩) =
          ⟨0⟩) :
    RDrev stringStoreBytecode g (initState cA gh bl σinit σ₀ g A I)

theorem stringStoreX_clearAllDeleteHistoryZero {cA gh bl σinit σ₀ A I} {g : Sat256}
    {τ : AccountMap}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2171⟩
      [⟨480⟩, stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, τ) k C)
    (hheader : historyLengthWord τ I = ⟨0⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2184⟩
      [⟨480⟩, stringStoreSelWord I]
      clearAllHistoryBaseMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner τ ⟨1⟩ ⟨0⟩) k C := by
  obtain ⟨_, _, rd2171⟩ := hreach
  have rd2314 := evm_run rd2171 with [
    jumpdest, push1 ⟨1⟩, push0, push2 ⟨2184⟩, swap2, swap1, push2 ⟨2314⟩,
    jump (by jump_dest)]
  have rd2317 := evm_run rd2314 with [jumpdest, pop, dup1]
  obtain ⟨_, _, rd2318₀⟩ := rd2317.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2318⟩ :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2318⟩
        [historyLengthWord τ I, ⟨1⟩, ⟨2184⟩, ⟨480⟩, stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, by simpa [historyLengthWord, initState] using rd2318₀⟩
  have rd2320pre := evm_run rd2318 with [push0, dup3]
  obtain ⟨_, _, rd2321⟩ := rd2320pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2321' :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2321⟩
        [historyLengthWord τ I, ⟨1⟩, ⟨2184⟩, ⟨480⟩, stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner τ ⟨1⟩ ⟨0⟩) k C := by
    exact ⟨_, _, by simpa [initState] using rd2321⟩
  obtain ⟨_, _, rd2321⟩ := rd2321'
  have rd2324 := evm_run rd2321 with [
    swap1, push0,
    raw mstore 0 clearAllHistoryBaseMem (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, push0]
  have rd2328 := evm_run rd2324 with [
    raw keccak256 0 clearAllHistoryBaseWord (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by decide) (by evm_ov)]
  have rd2369 := evm_run rd2328 with [
    swap1, push2 ⟨2338⟩, swap2, swap1, push2 ⟨2369⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd2369₀⟩ :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2369⟩
        [⟨0⟩, clearAllHistoryBaseWord, ⟨2338⟩, ⟨2184⟩, ⟨480⟩, stringStoreSelWord I]
        clearAllHistoryBaseMem (UInt256.ofNat 3) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner τ ⟨1⟩ ⟨0⟩) k C := by
    exact ⟨_, _, by simpa [hheader] using rd2369⟩
  have rd2376 := evm_run rd2369₀ with [
    jumpdest, push0, jumpdest, dup1, dup3, gt, iszero, push2 ⟨2401⟩]
  have rd2401 := rd2376.jumpiT (by native_decide) (by decide) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2338 := evm_run rd2401 with [jumpdest, pop, pop, pop, jump (by jump_dest)]
  exact ⟨_, _, evm_run rd2338 with [jumpdest, jump (by jump_dest)]⟩

theorem stringStoreX_clearAllDeleteHistoryZeroFromRawBaseMem
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2171⟩
      [⟨480⟩, stringStoreSelWord I]
      clearRawBaseMem (UInt256.ofNat 3) ByteArray.empty
      (cA, τ) k C)
    (hheader : historyLengthWord τ I = ⟨0⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2184⟩
      [⟨480⟩, stringStoreSelWord I]
      clearAllHistoryBaseMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner τ ⟨1⟩ ⟨0⟩) k C := by
  obtain ⟨_, _, rd2171⟩ := hreach
  have rd2314 := evm_run rd2171 with [
    jumpdest, push1 ⟨1⟩, push0, push2 ⟨2184⟩, swap2, swap1, push2 ⟨2314⟩,
    jump (by jump_dest)]
  have rd2317 := evm_run rd2314 with [jumpdest, pop, dup1]
  obtain ⟨_, _, rd2318₀⟩ := rd2317.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2318⟩ :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2318⟩
        [historyLengthWord τ I, ⟨1⟩, ⟨2184⟩, ⟨480⟩, stringStoreSelWord I]
        clearRawBaseMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, by simpa [historyLengthWord, initState] using rd2318₀⟩
  have rd2320pre := evm_run rd2318 with [push0, dup3]
  obtain ⟨_, _, rd2321⟩ := rd2320pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2321' :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2321⟩
        [historyLengthWord τ I, ⟨1⟩, ⟨2184⟩, ⟨480⟩, stringStoreSelWord I]
        clearRawBaseMem (UInt256.ofNat 3) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner τ ⟨1⟩ ⟨0⟩) k C := by
    exact ⟨_, _, by simpa [initState] using rd2321⟩
  obtain ⟨_, _, rd2321⟩ := rd2321'
  have rd2324 := evm_run rd2321 with [
    swap1, push0,
    raw mstore 0 clearAllHistoryBaseMem (UInt256.ofNat 3) (by native_decide)
      mem_cost
      clearAllHistoryBaseMem_from_clearRawBaseMem
      (by decide) (by evm_ov),
    push1 ⟨32⟩, push0]
  have rd2328 := evm_run rd2324 with [
    raw keccak256 0 clearAllHistoryBaseWord (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by decide) (by evm_ov)]
  have rd2369 := evm_run rd2328 with [
    swap1, push2 ⟨2338⟩, swap2, swap1, push2 ⟨2369⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd2369₀⟩ :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2369⟩
        [⟨0⟩, clearAllHistoryBaseWord, ⟨2338⟩, ⟨2184⟩, ⟨480⟩, stringStoreSelWord I]
        clearAllHistoryBaseMem (UInt256.ofNat 3) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner τ ⟨1⟩ ⟨0⟩) k C := by
    exact ⟨_, _, by simpa [hheader] using rd2369⟩
  have rd2376 := evm_run rd2369₀ with [
    jumpdest, push0, jumpdest, dup1, dup3, gt, iszero, push2 ⟨2401⟩]
  have rd2401 := rd2376.jumpiT (by native_decide) (by decide) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2338 := evm_run rd2401 with [jumpdest, pop, pop, pop, jump (by jump_dest)]
  exact ⟨_, _, evm_run rd2338 with [jumpdest, jump (by jump_dest)]⟩

theorem stringStoreX_clearAllDeleteHistoryZeroFromCurrentBaseMem
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2171⟩
      [⟨480⟩, stringStoreSelWord I]
      clearCurrentBaseMem (UInt256.ofNat 3) ByteArray.empty
      (cA, τ) k C)
    (hheader : historyLengthWord τ I = ⟨0⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2184⟩
      [⟨480⟩, stringStoreSelWord I]
      clearAllHistoryBaseMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner τ ⟨1⟩ ⟨0⟩) k C := by
  obtain ⟨_, _, rd2171⟩ := hreach
  have rd2314 := evm_run rd2171 with [
    jumpdest, push1 ⟨1⟩, push0, push2 ⟨2184⟩, swap2, swap1, push2 ⟨2314⟩,
    jump (by jump_dest)]
  have rd2317 := evm_run rd2314 with [jumpdest, pop, dup1]
  obtain ⟨_, _, rd2318₀⟩ := rd2317.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2318⟩ :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2318⟩
        [historyLengthWord τ I, ⟨1⟩, ⟨2184⟩, ⟨480⟩, stringStoreSelWord I]
        clearCurrentBaseMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, by simpa [historyLengthWord, initState] using rd2318₀⟩
  have rd2320pre := evm_run rd2318 with [push0, dup3]
  obtain ⟨_, _, rd2321⟩ := rd2320pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2321' :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2321⟩
        [historyLengthWord τ I, ⟨1⟩, ⟨2184⟩, ⟨480⟩, stringStoreSelWord I]
        clearCurrentBaseMem (UInt256.ofNat 3) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner τ ⟨1⟩ ⟨0⟩) k C := by
    exact ⟨_, _, by simpa [initState] using rd2321⟩
  obtain ⟨_, _, rd2321⟩ := rd2321'
  have rd2324 := evm_run rd2321 with [
    swap1, push0,
    raw mstore 0 clearAllHistoryBaseMem (UInt256.ofNat 3) (by native_decide)
      mem_cost
      clearAllHistoryBaseMem_from_clearCurrentBaseMem
      (by decide) (by evm_ov),
    push1 ⟨32⟩, push0]
  have rd2328 := evm_run rd2324 with [
    raw keccak256 0 clearAllHistoryBaseWord (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by decide) (by evm_ov)]
  have rd2369 := evm_run rd2328 with [
    swap1, push2 ⟨2338⟩, swap2, swap1, push2 ⟨2369⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd2369₀⟩ :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2369⟩
        [⟨0⟩, clearAllHistoryBaseWord, ⟨2338⟩, ⟨2184⟩, ⟨480⟩, stringStoreSelWord I]
        clearAllHistoryBaseMem (UInt256.ofNat 3) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner τ ⟨1⟩ ⟨0⟩) k C := by
    exact ⟨_, _, by simpa [hheader] using rd2369⟩
  have rd2376 := evm_run rd2369₀ with [
    jumpdest, push0, jumpdest, dup1, dup3, gt, iszero, push2 ⟨2401⟩]
  have rd2401 := rd2376.jumpiT (by native_decide) (by decide) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2338 := evm_run rd2401 with [jumpdest, pop, pop, pop, jump (by jump_dest)]
  exact ⟨_, _, evm_run rd2338 with [jumpdest, jump (by jump_dest)]⟩

theorem stringStoreX_clearAllShortZeroValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨472⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hcurrent : currentLengthHeaderWord σ I = ⟨0⟩)
    (hraw : rawLengthHeaderWord σ I = ⟨0⟩)
    (hhistory : historyLengthWord σ I = ⟨0⟩) :
    RDret stringStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) ⟨2⟩ ⟨0⟩)
        ⟨1⟩ ⟨0⟩)
      ByteArray.empty := by
  let σ1 := sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩
  let σ2 := sstoreAccountMap I.codeOwner σ1 ⟨2⟩ ⟨0⟩
  have h1 := stringStoreX_clearAllDeleteCurrentShortZero hperm hreach hcurrent
  have hraw1 : rawLengthHeaderWord σ1 I = ⟨0⟩ := by
    have hne := sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨2⟩ ⟨0⟩ ⟨0⟩
      (by decide)
    simpa [σ1, rawLengthHeaderWord] using hne.trans hraw
  have h2 := stringStoreX_clearAllDeleteRawShortZero
    (σinit := σ) (τ := σ1) hperm h1 hraw1
  have hhistory1 : historyLengthWord σ1 I = ⟨0⟩ := by
    have hne := sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨1⟩ ⟨0⟩ ⟨0⟩
      (by decide)
    simpa [σ1, historyLengthWord] using hne.trans hhistory
  have hhistory2 : historyLengthWord σ2 I = ⟨0⟩ := by
    have hne := sstoreAccountMap_storage_findD_ne σ1 I.codeOwner ⟨1⟩ ⟨2⟩ ⟨0⟩
      (by decide)
    simpa [σ2, historyLengthWord] using hne.trans hhistory1
  have h3 := stringStoreX_clearAllDeleteHistoryZero
    (σinit := σ) (τ := σ2) hperm h2 hhistory2
  obtain ⟨_, _, rd2184⟩ := h3
  have rd480 := evm_run rd2184 with [jumpdest, jump (by jump_dest)]
  exact (evm_run rd480 with [jumpdest]).stop (by decide) (by evm_ov)

theorem stringStoreX_clearAllCurrentShortRawHistoryZeroValid
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨472⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hlen :
      len = UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩)
    (hraw : rawLengthHeaderWord σ I = ⟨0⟩)
    (hhistory : historyLengthWord σ I = ⟨0⟩) :
    RDret stringStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) ⟨2⟩ ⟨0⟩)
        ⟨1⟩ ⟨0⟩)
      ByteArray.empty := by
  let σ1 := sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩
  let σ2 := sstoreAccountMap I.codeOwner σ1 ⟨2⟩ ⟨0⟩
  have h1 := stringStoreX_clearAllDeleteCurrentShortValid
    (g := g) (len := len) hperm hreach hflag hlen hvalid
  have hraw1 : rawLengthHeaderWord σ1 I = ⟨0⟩ := by
    have hne := sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨2⟩ ⟨0⟩ ⟨0⟩
      (by decide)
    simpa [σ1, rawLengthHeaderWord] using hne.trans hraw
  have h2 := stringStoreX_clearAllDeleteRawShortZero
    (σinit := σ) (τ := σ1) hperm h1 hraw1
  have hhistory1 : historyLengthWord σ1 I = ⟨0⟩ := by
    have hne := sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨1⟩ ⟨0⟩ ⟨0⟩
      (by decide)
    simpa [σ1, historyLengthWord] using hne.trans hhistory
  have hhistory2 : historyLengthWord σ2 I = ⟨0⟩ := by
    have hne := sstoreAccountMap_storage_findD_ne σ1 I.codeOwner ⟨1⟩ ⟨2⟩ ⟨0⟩
      (by decide)
    simpa [σ2, historyLengthWord] using hne.trans hhistory1
  have h3 := stringStoreX_clearAllDeleteHistoryZero
    (σinit := σ) (τ := σ2) hperm h2 hhistory2
  obtain ⟨_, _, rd2184⟩ := h3
  have rd480 := evm_run rd2184 with [jumpdest, jump (by jump_dest)]
  exact (evm_run rd480 with [jumpdest]).stop (by decide) (by evm_ov)

theorem stringStoreX_clearAllCurrentZeroRawShortHistoryZeroValid
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨472⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hcurrent : currentLengthHeaderWord σ I = ⟨0⟩)
    (hflag : UInt256.land (rawLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hlen :
      len = UInt256.land (UInt256.div (rawLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land (rawLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩)
    (hhistory : historyLengthWord σ I = ⟨0⟩) :
    RDret stringStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) ⟨2⟩ ⟨0⟩)
        ⟨1⟩ ⟨0⟩)
      ByteArray.empty := by
  let σ1 := sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩
  let σ2 := sstoreAccountMap I.codeOwner σ1 ⟨2⟩ ⟨0⟩
  have h1 := stringStoreX_clearAllDeleteCurrentShortZero hperm hreach hcurrent
  have hraw1 : rawLengthHeaderWord σ1 I = rawLengthHeaderWord σ I := by
    have hne := sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨2⟩ ⟨0⟩ ⟨0⟩
      (by decide)
    simpa [σ1, rawLengthHeaderWord] using hne
  have hflag1 : UInt256.land (rawLengthHeaderWord σ1 I) ⟨1⟩ = ⟨0⟩ := by
    simpa [hraw1] using hflag
  have hlen1 :
      len = UInt256.land (UInt256.div (rawLengthHeaderWord σ1 I) ⟨2⟩) ⟨127⟩ := by
    simpa [hraw1] using hlen
  have hvalid1 : UInt256.sub (UInt256.land (rawLengthHeaderWord σ1 I) ⟨1⟩)
      (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hraw1] using hvalid
  have h2 := stringStoreX_clearAllDeleteRawShortValid
    (σinit := σ) (τ := σ1) (len := len) hperm h1 hflag1 hlen1 hvalid1
  have hhistory1 : historyLengthWord σ1 I = ⟨0⟩ := by
    have hne := sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨1⟩ ⟨0⟩ ⟨0⟩
      (by decide)
    simpa [σ1, historyLengthWord] using hne.trans hhistory
  have hhistory2 : historyLengthWord σ2 I = ⟨0⟩ := by
    have hne := sstoreAccountMap_storage_findD_ne σ1 I.codeOwner ⟨1⟩ ⟨2⟩ ⟨0⟩
      (by decide)
    simpa [σ2, historyLengthWord] using hne.trans hhistory1
  have h3 := stringStoreX_clearAllDeleteHistoryZero
    (σinit := σ) (τ := σ2) hperm h2 hhistory2
  obtain ⟨_, _, rd2184⟩ := h3
  have rd480 := evm_run rd2184 with [jumpdest, jump (by jump_dest)]
  exact (evm_run rd480 with [jumpdest]).stop (by decide) (by evm_ov)

theorem stringStoreX_clearAllCurrentZeroRawLongHistoryZeroValid
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨472⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hcurrent : currentLengthHeaderWord σ I = ⟨0⟩)
    (hrawFlag : UInt256.land (rawLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hrawLen : len = UInt256.div (rawLengthHeaderWord σ I) ⟨2⟩)
    (hrawValid : UInt256.sub (UInt256.land (rawLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩)
    (hhistory : historyLengthWord σ I = ⟨0⟩) :
    RDret stringStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (clearDataWordsForwardFrom I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) ⟨2⟩ ⟨0⟩)
          clearRawBaseWord ⟨0⟩
          (UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩).toNat)
        ⟨1⟩ ⟨0⟩)
      ByteArray.empty := by
  let σ1 := sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩
  let σ2 := sstoreAccountMap I.codeOwner σ1 ⟨2⟩ ⟨0⟩
  let count := UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩
  let σ3 := clearDataWordsForwardFrom I.codeOwner σ2 clearRawBaseWord ⟨0⟩ count.toNat
  have h1 := stringStoreX_clearAllDeleteCurrentShortZero hperm hreach hcurrent
  have hraw1 : rawLengthHeaderWord σ1 I = rawLengthHeaderWord σ I := by
    have hne := sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨2⟩ ⟨0⟩ ⟨0⟩
      (by decide)
    simpa [σ1, rawLengthHeaderWord] using hne
  have hrawFlag1 : UInt256.land (rawLengthHeaderWord σ1 I) ⟨1⟩ ≠ ⟨0⟩ := by
    simpa [hraw1] using hrawFlag
  have hrawLen1 : len = UInt256.div (rawLengthHeaderWord σ1 I) ⟨2⟩ := by
    simpa [hraw1] using hrawLen
  have hrawValid1 : UInt256.sub (UInt256.land (rawLengthHeaderWord σ1 I) ⟨1⟩)
      (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hraw1] using hrawValid
  have hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩ :=
    clearCurrentLongValid_gt31
      (header := rawLengthHeaderWord σ1 I) (len := len)
      hrawFlag1 hrawValid1
  have h2 := stringStoreX_clearAllDeleteRawLongValid
    (σinit := σ) (τ := σ1) (len := len) hperm h1 hrawFlag1 hrawLen1 hrawValid1 hgt31
  have hhistory1 : historyLengthWord σ1 I = ⟨0⟩ := by
    have hne := sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨1⟩ ⟨0⟩ ⟨0⟩
      (by decide)
    simpa [σ1, historyLengthWord] using hne.trans hhistory
  have hhistory2 : historyLengthWord σ2 I = ⟨0⟩ := by
    have hne := sstoreAccountMap_storage_findD_ne σ1 I.codeOwner ⟨1⟩ ⟨2⟩ ⟨0⟩
      (by decide)
    simpa [σ2, historyLengthWord] using hne.trans hhistory1
  have hhistory3 : historyLengthWord σ3 I = ⟨0⟩ := by
    have hpres := clearDataWordsForwardFrom_storage_findD_ne
      σ2 I.codeOwner ⟨1⟩ clearRawBaseWord ⟨0⟩ count.toNat
      (by
        intro i hi
        exact clearRawDataSlot_ne_historyLengthSlot (clearDataWordsLoopIndex ⟨0⟩ i))
    simpa [σ3, historyLengthWord] using hpres.trans hhistory2
  have h3 := stringStoreX_clearAllDeleteHistoryZeroFromRawBaseMem
    (σinit := σ) (τ := σ3) hperm (by simpa [σ2, σ3, count] using h2) hhistory3
  obtain ⟨_, _, rd2184⟩ := h3
  have rd480 := evm_run rd2184 with [jumpdest, jump (by jump_dest)]
  simpa [σ1, σ2, σ3, count] using
    (evm_run rd480 with [jumpdest]).stop (by decide) (by evm_ov)

theorem stringStoreX_clearAllCurrentShortRawLongHistoryZeroValid
    {cA gh bl σ σ₀ A I} {g : Sat256} {currentLen rawLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨472⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hcurrentFlag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hcurrentLen :
      currentLen = UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hcurrentValid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt currentLen ⟨32⟩) ≠ ⟨0⟩)
    (hrawFlag : UInt256.land (rawLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hrawLen : rawLen = UInt256.div (rawLengthHeaderWord σ I) ⟨2⟩)
    (hrawValid : UInt256.sub (UInt256.land (rawLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt rawLen ⟨32⟩) ≠ ⟨0⟩)
    (hhistory : historyLengthWord σ I = ⟨0⟩) :
    RDret stringStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (clearDataWordsForwardFrom I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) ⟨2⟩ ⟨0⟩)
          clearRawBaseWord ⟨0⟩
          (UInt256.div ((⟨31⟩ : UInt256) + rawLen) ⟨32⟩).toNat)
        ⟨1⟩ ⟨0⟩)
      ByteArray.empty := by
  let σ1 := sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩
  let σ2 := sstoreAccountMap I.codeOwner σ1 ⟨2⟩ ⟨0⟩
  let count := UInt256.div ((⟨31⟩ : UInt256) + rawLen) ⟨32⟩
  let σ3 := clearDataWordsForwardFrom I.codeOwner σ2 clearRawBaseWord ⟨0⟩ count.toNat
  have h1 := stringStoreX_clearAllDeleteCurrentShortValid
    (g := g) (len := currentLen) hperm hreach hcurrentFlag hcurrentLen hcurrentValid
  have hraw1 : rawLengthHeaderWord σ1 I = rawLengthHeaderWord σ I := by
    have hne := sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨2⟩ ⟨0⟩ ⟨0⟩
      (by decide)
    simpa [σ1, rawLengthHeaderWord] using hne
  have hrawFlag1 : UInt256.land (rawLengthHeaderWord σ1 I) ⟨1⟩ ≠ ⟨0⟩ := by
    simpa [hraw1] using hrawFlag
  have hrawLen1 : rawLen = UInt256.div (rawLengthHeaderWord σ1 I) ⟨2⟩ := by
    simpa [hraw1] using hrawLen
  have hrawValid1 : UInt256.sub (UInt256.land (rawLengthHeaderWord σ1 I) ⟨1⟩)
      (UInt256.lt rawLen ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hraw1] using hrawValid
  have hgt31 : UInt256.lt ⟨31⟩ rawLen ≠ ⟨0⟩ :=
    clearCurrentLongValid_gt31
      (header := rawLengthHeaderWord σ1 I) (len := rawLen)
      hrawFlag1 hrawValid1
  have h2 := stringStoreX_clearAllDeleteRawLongValid
    (σinit := σ) (τ := σ1) (len := rawLen)
    hperm h1 hrawFlag1 hrawLen1 hrawValid1 hgt31
  have hhistory1 : historyLengthWord σ1 I = ⟨0⟩ := by
    have hne := sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨1⟩ ⟨0⟩ ⟨0⟩
      (by decide)
    simpa [σ1, historyLengthWord] using hne.trans hhistory
  have hhistory2 : historyLengthWord σ2 I = ⟨0⟩ := by
    have hne := sstoreAccountMap_storage_findD_ne σ1 I.codeOwner ⟨1⟩ ⟨2⟩ ⟨0⟩
      (by decide)
    simpa [σ2, historyLengthWord] using hne.trans hhistory1
  have hhistory3 : historyLengthWord σ3 I = ⟨0⟩ := by
    have hpres := clearDataWordsForwardFrom_storage_findD_ne
      σ2 I.codeOwner ⟨1⟩ clearRawBaseWord ⟨0⟩ count.toNat
      (by
        intro i hi
        exact clearRawDataSlot_ne_historyLengthSlot (clearDataWordsLoopIndex ⟨0⟩ i))
    simpa [σ3, historyLengthWord] using hpres.trans hhistory2
  have h3 := stringStoreX_clearAllDeleteHistoryZeroFromRawBaseMem
    (σinit := σ) (τ := σ3) hperm (by simpa [σ2, σ3, count] using h2) hhistory3
  obtain ⟨_, _, rd2184⟩ := h3
  have rd480 := evm_run rd2184 with [jumpdest, jump (by jump_dest)]
  simpa [σ1, σ2, σ3, count] using
    (evm_run rd480 with [jumpdest]).stop (by decide) (by evm_ov)

theorem stringStoreX_clearAllCurrentLongRawHistoryZeroValid
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨472⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩)
    (hlen : len = UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩)
    (hraw : rawLengthHeaderWord σ I = ⟨0⟩)
    (hhistory : historyLengthWord σ I = ⟨0⟩) :
    RDret stringStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (clearDataWordsForwardFrom I.codeOwner
            (sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
            clearCurrentBaseWord ⟨0⟩
            (UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩).toNat)
          ⟨2⟩ ⟨0⟩)
        ⟨1⟩ ⟨0⟩)
      ByteArray.empty := by
  let count := UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩
  let σ1 := clearDataWordsForwardFrom I.codeOwner
    (sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) clearCurrentBaseWord ⟨0⟩ count.toNat
  let σ2 := sstoreAccountMap I.codeOwner σ1 ⟨2⟩ ⟨0⟩
  have hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩ :=
    clearCurrentLongValid_gt31
      (header := currentLengthHeaderWord σ I) (len := len)
      hflag hvalid
  have h1 := stringStoreX_clearAllDeleteCurrentLongValid
    (g := g) (len := len) hperm hreach hflag (by simpa [← hlen] using hvalid) hlen hgt31
  have hrawAfterSlot0 : rawLengthHeaderWord (sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) I =
      ⟨0⟩ := by
    have hne := sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨2⟩ ⟨0⟩ ⟨0⟩
      (by decide)
    simpa [rawLengthHeaderWord] using hne.trans hraw
  have hraw1 : rawLengthHeaderWord σ1 I = ⟨0⟩ := by
    have hpres := clearDataWordsForwardFrom_storage_findD_ne
      (sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
      I.codeOwner ⟨2⟩ clearCurrentBaseWord ⟨0⟩ count.toNat
      (by
        intro i hi
        exact clearCurrentDataSlot_ne_rawLengthSlot (clearDataWordsLoopIndex ⟨0⟩ i))
    simpa [σ1, rawLengthHeaderWord] using hpres.trans hrawAfterSlot0
  have h2 := stringStoreX_clearAllDeleteRawShortZeroFromCurrentBaseMem
    (σinit := σ) (τ := σ1) hperm (by simpa [σ1, count] using h1) hraw1
  have hhistoryAfterSlot0 : historyLengthWord (sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) I =
      ⟨0⟩ := by
    have hne := sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨1⟩ ⟨0⟩ ⟨0⟩
      (by decide)
    simpa [historyLengthWord] using hne.trans hhistory
  have hhistory1 : historyLengthWord σ1 I = ⟨0⟩ := by
    have hpres := clearDataWordsForwardFrom_storage_findD_ne
      (sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
      I.codeOwner ⟨1⟩ clearCurrentBaseWord ⟨0⟩ count.toNat
      (by
        intro i hi
        exact clearCurrentDataSlot_ne_historyLengthSlot (clearDataWordsLoopIndex ⟨0⟩ i))
    simpa [σ1, historyLengthWord] using hpres.trans hhistoryAfterSlot0
  have hhistory2 : historyLengthWord σ2 I = ⟨0⟩ := by
    have hne := sstoreAccountMap_storage_findD_ne σ1 I.codeOwner ⟨1⟩ ⟨2⟩ ⟨0⟩
      (by decide)
    simpa [σ2, historyLengthWord] using hne.trans hhistory1
  have h3 := stringStoreX_clearAllDeleteHistoryZeroFromCurrentBaseMem
    (σinit := σ) (τ := σ2) hperm (by simpa [σ2] using h2) hhistory2
  obtain ⟨_, _, rd2184⟩ := h3
  have rd480 := evm_run rd2184 with [jumpdest, jump (by jump_dest)]
  simpa [σ1, σ2, count] using
    (evm_run rd480 with [jumpdest]).stop (by decide) (by evm_ov)

theorem stringStoreX_clearAllCurrentLongRawShortHistoryZeroValid
    {cA gh bl σ σ₀ A I} {g : Sat256} {currentLen rawLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨472⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hcurrentFlag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hcurrentValid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt currentLen ⟨32⟩) ≠ ⟨0⟩)
    (hcurrentLen : currentLen = UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩)
    (hrawFlag : UInt256.land (rawLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hrawLen :
      rawLen = UInt256.land (UInt256.div (rawLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hrawValid : UInt256.sub (UInt256.land (rawLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt rawLen ⟨32⟩) ≠ ⟨0⟩)
    (hhistory : historyLengthWord σ I = ⟨0⟩) :
    RDret stringStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (clearDataWordsForwardFrom I.codeOwner
            (sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
            clearCurrentBaseWord ⟨0⟩
            (UInt256.div ((⟨31⟩ : UInt256) + currentLen) ⟨32⟩).toNat)
          ⟨2⟩ ⟨0⟩)
        ⟨1⟩ ⟨0⟩)
      ByteArray.empty := by
  let count := UInt256.div ((⟨31⟩ : UInt256) + currentLen) ⟨32⟩
  let σ1 := clearDataWordsForwardFrom I.codeOwner
    (sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) clearCurrentBaseWord ⟨0⟩ count.toNat
  let σ2 := sstoreAccountMap I.codeOwner σ1 ⟨2⟩ ⟨0⟩
  have hgt31 : UInt256.lt ⟨31⟩ currentLen ≠ ⟨0⟩ :=
    clearCurrentLongValid_gt31
      (header := currentLengthHeaderWord σ I) (len := currentLen)
      hcurrentFlag hcurrentValid
  have h1 := stringStoreX_clearAllDeleteCurrentLongValid
    (g := g) (len := currentLen) hperm hreach hcurrentFlag
    (by simpa [← hcurrentLen] using hcurrentValid) hcurrentLen hgt31
  have hrawAfterSlot0 :
      rawLengthHeaderWord (sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) I =
        rawLengthHeaderWord σ I := by
    have hne := sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨2⟩ ⟨0⟩ ⟨0⟩
      (by decide)
    simpa [rawLengthHeaderWord] using hne
  have hraw1 : rawLengthHeaderWord σ1 I = rawLengthHeaderWord σ I := by
    have hpres := clearDataWordsForwardFrom_storage_findD_ne
      (sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
      I.codeOwner ⟨2⟩ clearCurrentBaseWord ⟨0⟩ count.toNat
      (by
        intro i hi
        exact clearCurrentDataSlot_ne_rawLengthSlot (clearDataWordsLoopIndex ⟨0⟩ i))
    simpa [σ1, rawLengthHeaderWord] using hpres.trans hrawAfterSlot0
  have hrawFlag1 : UInt256.land (rawLengthHeaderWord σ1 I) ⟨1⟩ = ⟨0⟩ := by
    simpa [hraw1] using hrawFlag
  have hrawLen1 :
      rawLen = UInt256.land (UInt256.div (rawLengthHeaderWord σ1 I) ⟨2⟩) ⟨127⟩ := by
    simpa [hraw1] using hrawLen
  have hrawValid1 : UInt256.sub (UInt256.land (rawLengthHeaderWord σ1 I) ⟨1⟩)
      (UInt256.lt rawLen ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hraw1] using hrawValid
  have h2 := stringStoreX_clearAllDeleteRawShortValidFromCurrentBaseMem
    (σinit := σ) (τ := σ1) (len := rawLen)
    hperm (by simpa [σ1, count] using h1) hrawFlag1 hrawLen1 hrawValid1
  have hhistoryAfterSlot0 :
      historyLengthWord (sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) I = ⟨0⟩ := by
    have hne := sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨1⟩ ⟨0⟩ ⟨0⟩
      (by decide)
    simpa [historyLengthWord] using hne.trans hhistory
  have hhistory1 : historyLengthWord σ1 I = ⟨0⟩ := by
    have hpres := clearDataWordsForwardFrom_storage_findD_ne
      (sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
      I.codeOwner ⟨1⟩ clearCurrentBaseWord ⟨0⟩ count.toNat
      (by
        intro i hi
        exact clearCurrentDataSlot_ne_historyLengthSlot (clearDataWordsLoopIndex ⟨0⟩ i))
    simpa [σ1, historyLengthWord] using hpres.trans hhistoryAfterSlot0
  have hhistory2 : historyLengthWord σ2 I = ⟨0⟩ := by
    have hne := sstoreAccountMap_storage_findD_ne σ1 I.codeOwner ⟨1⟩ ⟨2⟩ ⟨0⟩
      (by decide)
    simpa [σ2, historyLengthWord] using hne.trans hhistory1
  have h3 := stringStoreX_clearAllDeleteHistoryZeroFromCurrentBaseMem
    (σinit := σ) (τ := σ2) hperm (by simpa [σ2] using h2) hhistory2
  obtain ⟨_, _, rd2184⟩ := h3
  have rd480 := evm_run rd2184 with [jumpdest, jump (by jump_dest)]
  simpa [σ1, σ2, count] using
    (evm_run rd480 with [jumpdest]).stop (by decide) (by evm_ov)

theorem stringStoreX_clearAllCurrentLongRawLongHistoryZeroValid
    {cA gh bl σ σ₀ A I} {g : Sat256} {currentLen rawLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨472⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hcurrentFlag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hcurrentValid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt currentLen ⟨32⟩) ≠ ⟨0⟩)
    (hcurrentLen : currentLen = UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩)
    (hrawFlag : UInt256.land (rawLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hrawLen : rawLen = UInt256.div (rawLengthHeaderWord σ I) ⟨2⟩)
    (hrawValid : UInt256.sub (UInt256.land (rawLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt rawLen ⟨32⟩) ≠ ⟨0⟩)
    (hhistory : historyLengthWord σ I = ⟨0⟩) :
    RDret stringStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (clearDataWordsForwardFrom I.codeOwner
          (sstoreAccountMap I.codeOwner
            (clearDataWordsForwardFrom I.codeOwner
              (sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
              clearCurrentBaseWord ⟨0⟩
              (UInt256.div ((⟨31⟩ : UInt256) + currentLen) ⟨32⟩).toNat)
            ⟨2⟩ ⟨0⟩)
          clearRawBaseWord ⟨0⟩
          (UInt256.div ((⟨31⟩ : UInt256) + rawLen) ⟨32⟩).toNat)
        ⟨1⟩ ⟨0⟩)
      ByteArray.empty := by
  let currentCount := UInt256.div ((⟨31⟩ : UInt256) + currentLen) ⟨32⟩
  let rawCount := UInt256.div ((⟨31⟩ : UInt256) + rawLen) ⟨32⟩
  let σ1 := clearDataWordsForwardFrom I.codeOwner
    (sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) clearCurrentBaseWord ⟨0⟩ currentCount.toNat
  let σ2 := sstoreAccountMap I.codeOwner σ1 ⟨2⟩ ⟨0⟩
  let σ3 := clearDataWordsForwardFrom I.codeOwner σ2 clearRawBaseWord ⟨0⟩ rawCount.toNat
  have hcurrentGt31 : UInt256.lt ⟨31⟩ currentLen ≠ ⟨0⟩ :=
    clearCurrentLongValid_gt31
      (header := currentLengthHeaderWord σ I) (len := currentLen)
      hcurrentFlag hcurrentValid
  have h1 := stringStoreX_clearAllDeleteCurrentLongValid
    (g := g) (len := currentLen) hperm hreach hcurrentFlag
    (by simpa [← hcurrentLen] using hcurrentValid) hcurrentLen hcurrentGt31
  have hrawAfterSlot0 :
      rawLengthHeaderWord (sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) I =
        rawLengthHeaderWord σ I := by
    have hne := sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨2⟩ ⟨0⟩ ⟨0⟩
      (by decide)
    simpa [rawLengthHeaderWord] using hne
  have hraw1 : rawLengthHeaderWord σ1 I = rawLengthHeaderWord σ I := by
    have hpres := clearDataWordsForwardFrom_storage_findD_ne
      (sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
      I.codeOwner ⟨2⟩ clearCurrentBaseWord ⟨0⟩ currentCount.toNat
      (by
        intro i hi
        exact clearCurrentDataSlot_ne_rawLengthSlot (clearDataWordsLoopIndex ⟨0⟩ i))
    simpa [σ1, rawLengthHeaderWord] using hpres.trans hrawAfterSlot0
  have hrawFlag1 : UInt256.land (rawLengthHeaderWord σ1 I) ⟨1⟩ ≠ ⟨0⟩ := by
    simpa [hraw1] using hrawFlag
  have hrawLen1 : rawLen = UInt256.div (rawLengthHeaderWord σ1 I) ⟨2⟩ := by
    simpa [hraw1] using hrawLen
  have hrawValid1 : UInt256.sub (UInt256.land (rawLengthHeaderWord σ1 I) ⟨1⟩)
      (UInt256.lt rawLen ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hraw1] using hrawValid
  have hrawGt31 : UInt256.lt ⟨31⟩ rawLen ≠ ⟨0⟩ :=
    clearCurrentLongValid_gt31
      (header := rawLengthHeaderWord σ1 I) (len := rawLen)
      hrawFlag1 hrawValid1
  have h2 := stringStoreX_clearAllDeleteRawLongValidFromCurrentBaseMem
    (σinit := σ) (τ := σ1) (len := rawLen)
    hperm (by simpa [σ1, currentCount] using h1)
    hrawFlag1 hrawLen1 hrawValid1 hrawGt31
  have hhistoryAfterSlot0 :
      historyLengthWord (sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) I = ⟨0⟩ := by
    have hne := sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨1⟩ ⟨0⟩ ⟨0⟩
      (by decide)
    simpa [historyLengthWord] using hne.trans hhistory
  have hhistory1 : historyLengthWord σ1 I = ⟨0⟩ := by
    have hpres := clearDataWordsForwardFrom_storage_findD_ne
      (sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
      I.codeOwner ⟨1⟩ clearCurrentBaseWord ⟨0⟩ currentCount.toNat
      (by
        intro i hi
        exact clearCurrentDataSlot_ne_historyLengthSlot (clearDataWordsLoopIndex ⟨0⟩ i))
    simpa [σ1, historyLengthWord] using hpres.trans hhistoryAfterSlot0
  have hhistory2 : historyLengthWord σ2 I = ⟨0⟩ := by
    have hne := sstoreAccountMap_storage_findD_ne σ1 I.codeOwner ⟨1⟩ ⟨2⟩ ⟨0⟩
      (by decide)
    simpa [σ2, historyLengthWord] using hne.trans hhistory1
  have hhistory3 : historyLengthWord σ3 I = ⟨0⟩ := by
    have hpres := clearDataWordsForwardFrom_storage_findD_ne
      σ2 I.codeOwner ⟨1⟩ clearRawBaseWord ⟨0⟩ rawCount.toNat
      (by
        intro i hi
        exact clearRawDataSlot_ne_historyLengthSlot (clearDataWordsLoopIndex ⟨0⟩ i))
    simpa [σ3, historyLengthWord] using hpres.trans hhistory2
  have h3 := stringStoreX_clearAllDeleteHistoryZeroFromRawBaseMem
    (σinit := σ) (τ := σ3) hperm
    (by simpa [σ2, σ3, rawCount] using h2) hhistory3
  obtain ⟨_, _, rd2184⟩ := h3
  have rd480 := evm_run rd2184 with [jumpdest, jump (by jump_dest)]
  simpa [σ1, σ2, σ3, currentCount, rawCount] using
    (evm_run rd480 with [jumpdest]).stop (by decide) (by evm_ov)

theorem stringStoreX_clearAllCurrentShortRawShortHistoryZeroValid
    {cA gh bl σ σ₀ A I} {g : Sat256} {currentLen rawLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨472⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hcurrentFlag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hcurrentLen :
      currentLen = UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hcurrentValid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt currentLen ⟨32⟩) ≠ ⟨0⟩)
    (hrawFlag : UInt256.land (rawLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hrawLen :
      rawLen = UInt256.land (UInt256.div (rawLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hrawValid : UInt256.sub (UInt256.land (rawLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt rawLen ⟨32⟩) ≠ ⟨0⟩)
    (hhistory : historyLengthWord σ I = ⟨0⟩) :
    RDret stringStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) ⟨2⟩ ⟨0⟩)
        ⟨1⟩ ⟨0⟩)
      ByteArray.empty := by
  let σ1 := sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩
  let σ2 := sstoreAccountMap I.codeOwner σ1 ⟨2⟩ ⟨0⟩
  have h1 := stringStoreX_clearAllDeleteCurrentShortValid
    (g := g) (len := currentLen) hperm hreach hcurrentFlag hcurrentLen hcurrentValid
  have hraw1 : rawLengthHeaderWord σ1 I = rawLengthHeaderWord σ I := by
    have hne := sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨2⟩ ⟨0⟩ ⟨0⟩
      (by decide)
    simpa [σ1, rawLengthHeaderWord] using hne
  have hrawFlag1 : UInt256.land (rawLengthHeaderWord σ1 I) ⟨1⟩ = ⟨0⟩ := by
    simpa [hraw1] using hrawFlag
  have hrawLen1 :
      rawLen = UInt256.land (UInt256.div (rawLengthHeaderWord σ1 I) ⟨2⟩) ⟨127⟩ := by
    simpa [hraw1] using hrawLen
  have hrawValid1 : UInt256.sub (UInt256.land (rawLengthHeaderWord σ1 I) ⟨1⟩)
      (UInt256.lt rawLen ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hraw1] using hrawValid
  have h2 := stringStoreX_clearAllDeleteRawShortValid
    (σinit := σ) (τ := σ1) (len := rawLen) hperm h1 hrawFlag1 hrawLen1 hrawValid1
  have hhistory1 : historyLengthWord σ1 I = ⟨0⟩ := by
    have hne := sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨1⟩ ⟨0⟩ ⟨0⟩
      (by decide)
    simpa [σ1, historyLengthWord] using hne.trans hhistory
  have hhistory2 : historyLengthWord σ2 I = ⟨0⟩ := by
    have hne := sstoreAccountMap_storage_findD_ne σ1 I.codeOwner ⟨1⟩ ⟨2⟩ ⟨0⟩
      (by decide)
    simpa [σ2, historyLengthWord] using hne.trans hhistory1
  have h3 := stringStoreX_clearAllDeleteHistoryZero
    (σinit := σ) (τ := σ2) hperm h2 hhistory2
  obtain ⟨_, _, rd2184⟩ := h3
  have rd480 := evm_run rd2184 with [jumpdest, jump (by jump_dest)]
  exact (evm_run rd480 with [jumpdest]).stop (by decide) (by evm_ov)

theorem stringStoreClearCurrentShortZeroOfEVM {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨0⟩ = ⟨0⟩)
    (hloc :
      storageLocLoad (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesLikeLengthLoc ⟨0⟩
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) = .int 0)
    (hret : RDret stringStoreBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      (cA, sstoreAccountMap I.codeOwner σ_evm ⟨0⟩ ⟨0⟩)
      (ffi.KEC (ByteArray.mk #[]))) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := clearCurrentSelector_size hsel
  have hd := stringStoreDispatch_clearCurrent (cd := I.calldata) hsel'
  have hdec := stringStoreDecode_clearCurrent (I := I) hsz
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ ⟨0⟩
  have hdel :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evmSolm0 currentRef = .ok evmSolm1 := by
    simpa [evmSolm0, evmSolm1, initState] using
      deleteCurrentShortZero
        (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        hload hloc
  have hbody :
      ExecTransitionBody stringStoreConfig stringStoreContract evmSolm0 ∅
        clearCurrentTransition.body
        (.returned { contract := stringStoreContract, locals := ∅ } evmSolm1
          (some emptyBytesKeccakValue)) := by
    exact clearCurrentBodyReturns (evm := evmSolm0) (evm' := evmSolm1)
      (by simp [evmSolm0, initState]; exact hwv) hdel
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts])
    (by
      simp [evmSolm1, evmSolm0, initState, storageStore_accountMap]
      exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩ ⟨0⟩ hAccounts)
    (returnEquiv_of_encode emptyBytesKeccakReturnEncoding)

theorem stringStoreClearCurrentShortPackedOfEVM {cA gh bl σ_evm σ_solm σ₀ A I}
    {g len : UInt256}
    (hcode : I.code = stringStoreBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        ⟨0⟩ = currentLengthHeaderWord σ_evm I)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hlen :
      len = UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩)
    (hret : RDret stringStoreBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      (cA, sstoreAccountMap I.codeOwner σ_evm ⟨0⟩ ⟨0⟩)
      (ffi.KEC (ByteArray.mk #[]))) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := clearCurrentSelector_size hsel
  have hd := stringStoreDispatch_clearCurrent (cd := I.calldata) hsel'
  have hdec := stringStoreDecode_clearCurrent (I := I) hsz
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ ⟨0⟩
  have hpacked :
      checkBytesPacked ⟨0⟩
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hload hflag
  have hdel :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evmSolm0 currentRef = .ok evmSolm1 := by
    simpa [evmSolm0, evmSolm1, initState] using
      deleteCurrentShortPacked
        (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (header := currentLengthHeaderWord σ_evm I) (len := len)
        hload hpacked hflag hlen hvalid
  have hbody :
      ExecTransitionBody stringStoreConfig stringStoreContract evmSolm0 ∅
        clearCurrentTransition.body
        (.returned { contract := stringStoreContract, locals := ∅ } evmSolm1
          (some emptyBytesKeccakValue)) := by
    exact clearCurrentBodyReturns (evm := evmSolm0) (evm' := evmSolm1)
      (by simp [evmSolm0, initState]; exact hwv) hdel
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts])
    (by
      simp [evmSolm1, evmSolm0, initState, storageStore_accountMap]
      exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩ ⟨0⟩ hAccounts)
    (returnEquiv_of_encode emptyBytesKeccakReturnEncoding)

theorem stringStoreClearCurrentShortZeroRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hheader : currentLengthHeaderWord σ_evm I = ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
    simpa [currentLengthHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨0⟩ = ⟨0⟩ := by
    have hload' :
        Solm.EVM.storageLoad
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          I.codeOwner ⟨0⟩ = currentLengthHeaderWord σ_evm I := by
      simp [Solm.EVM.storageLoad, initState, State.lookupAccount, Account.lookupStorage,
        currentLengthHeaderWord, hslot]
    simpa [hheader] using hload'
  have hloc :
      storageLocLoad (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesLikeLengthLoc ⟨0⟩
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) = .int 0 :=
    storageLocLoad_bytesLikeLengthLoc_zero (base := ⟨0⟩) hload
  have hreach := stringStoreReachClearCurrent (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv (clearCurrentSelector_size hsel) hsize hsel
  have hret := stringStoreX_clearCurrentShortZeroValid
    (g := Sat256.ofUInt256 g) hperm hreach hheader
  exact stringStoreClearCurrentShortZeroOfEVM hcode hsize hperm hwv hsel hAccounts
    hload hloc hret

theorem stringStoreClearCurrentShortValidRuntime_of_layout
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g len : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hlen :
      len = UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩)
    (hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        ⟨0⟩ = currentLengthHeaderWord σ_evm I) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hreach := stringStoreReachClearCurrent (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv (clearCurrentSelector_size hsel) hsize hsel
  have hret := stringStoreX_clearCurrentShortValid
    (g := Sat256.ofUInt256 g) hperm hreach hflag hlen hvalid
  exact stringStoreClearCurrentShortPackedOfEVM
    hcode hsize hperm hwv hsel hAccounts hload hflag hlen hvalid hret

theorem stringStoreClearCurrentShortValidRuntime_of_header
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g len : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hlen :
      len = UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
    simpa [currentLengthHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        ⟨0⟩ = currentLengthHeaderWord σ_evm I := by
    simp [Solm.EVM.storageLoad, initState, State.lookupAccount, Account.lookupStorage,
      currentLengthHeaderWord, hslot]
  exact stringStoreClearCurrentShortValidRuntime_of_layout
    hcode hsize hperm hwv hsel hAccounts hflag hlen hvalid hload

theorem stringStoreClearCurrentLongValidRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (_hheader : currentLengthHeaderWord σ_evm I ≠ ⟨0⟩)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len := UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩
  have hlen : len = UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩ := rfl
  have hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩ :=
    clearCurrentLongValid_gt31
      (header := currentLengthHeaderWord σ_evm I) (len := len) hflag (by simpa [len] using hvalid)
  have hlenLt : len.toNat < 2 ^ 255 :=
    clearCurrent_len_toNat_lt_sign_of_div2
      (header := currentLengthHeaderWord σ_evm I) (len := len) hlen
  have hcountNat :
      (UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩).toNat =
        (len.toNat + 31) / 32 := by
    have hadd : (((⟨31⟩ : UInt256) + len).toNat = 31 + len.toNat) := by
      rw [uadd_toNat, show (⟨31⟩ : UInt256).toNat = 31 from by decide]
      rw [Nat.add_comm 31 len.toNat]
      exact Nat.mod_eq_of_lt (by
        have hsize : (2 : Nat) ^ 255 + 31 < UInt256.size := by
          norm_num [UInt256.size]
        nlinarith)
    rw [udiv_toNat, hadd, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
    rw [Nat.add_comm 31 len.toNat]
  have hsel' : ((⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := clearCurrentSelector_size hsel
  have hd := stringStoreDispatch_clearCurrent (cd := I.calldata) hsel'
  have hdec := stringStoreDecode_clearCurrent (I := I) hsz
  have hreach := stringStoreReachClearCurrent (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv (clearCurrentSelector_size hsel) hsize hsel
  have hret := stringStoreX_clearCurrentLongValid
    (g := Sat256.ofUInt256 g) (len := len)
    hperm hreach hflag (by simpa [len] using hvalid) hlen hgt31
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolmLen := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ ⟨0⟩
  let evmSolm1 := clearSolidityBytesDataWordsFrom evmSolmLen ⟨0⟩ 0 ((len.toNat + 31) / 32)
  have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
    simpa [currentLengthHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        currentLengthHeaderWord σ_evm I := by
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, currentLengthHeaderWord, hslot]
  have hdel :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evmSolm0 currentRef = .ok evmSolm1 := by
    simpa [evmSolm0, evmSolmLen, evmSolm1, initState, hlen] using
      deleteCurrentLongPrepared
        (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (header := currentLengthHeaderWord σ_evm I) (len := len)
        hload hflag hlen (by simpa [len] using hvalid)
  have hbody :
      ExecTransitionBody stringStoreConfig stringStoreContract evmSolm0 ∅
        clearCurrentTransition.body
        (.returned { contract := stringStoreContract, locals := ∅ } evmSolm1
          (some emptyBytesKeccakValue)) := by
    exact clearCurrentBodyReturns (evm := evmSolm0) (evm' := evmSolm1)
      (by simp [evmSolm0, initState]; exact hwv) hdel
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by
      simp [evmSolm1, evmSolmLen, evmSolm0, clearSolidityBytesDataWordsFrom_createdAccounts,
        storageStore_createdAccounts, initState])
    (by
      simp [evmSolm1, evmSolmLen, evmSolm0, clearSolidityBytesDataWordsFrom_accountMap,
        storageStore_accountMap, storageStore_executionEnv, initState, hcountNat,
        clearCurrentBaseWord_eq_solidityBytesDataBaseSlot]
      exact accountMapEquiv_clearDataWordsForwardFrom I.codeOwner
        (solidityBytesDataBaseSlot ⟨0⟩) ⟨0⟩ ((len.toNat + 31) / 32)
        (accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩ ⟨0⟩ hAccounts))
    (returnEquiv_of_encode emptyBytesKeccakReturnEncoding)

theorem clearCurrentBodyRevertsOfDelete
    {evm : EVM.State}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hdel : deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
      evm currentRef = .revert) :
    ExecTransitionBody stringStoreConfig stringStoreContract evm ∅ clearCurrentTransition.body
      .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert (ExecStmt.deleteRevert hdel)

theorem deleteCurrentMalformedLong {evm : EVM.State} {header : UInt256}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
      evm currentRef = .revert := by
  have hdecode : solidityDecodeBytesLengthHeader header = .revert := by
    simp [solidityDecodeBytesLengthHeader, hflag, hbad]
  have hlenSlot : (bytesLikeLengthLoc ⟨0⟩ evm).slot = ⟨0⟩ := by
    unfold bytesLikeLengthLoc
    split <;> rfl
  have hdecodeLoad :
      solidityDecodeBytesLengthHeader
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (bytesLikeLengthLoc ⟨0⟩ evm).slot) =
        .revert := by
    rw [hlenSlot, hload]
    exact hdecode
  simp [deleteStorage?, resolveStorageRef?, evalStorageRef, evalStorageRefSteps, currentRef,
    storageTypeAt?, stringStoreConfig, stringStoreContract, storageDecls, stringSt,
    clearStorage?, clearStorageBytesLike?, storagePrepareResultToEval, stringStoreStorageLayout,
    solidityPrepareBytesWrite?, solidityBytesBaseSlotAndLength?, stringStoreLayout,
    hload, hdecode,
    EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem deleteCurrentMalformedShort {evm : EVM.State} {header : UInt256}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
      evm currentRef = .revert := by
  have hdecode : solidityDecodeBytesLengthHeader header = .revert := by
    have hbad0 :
        UInt256.sub ⟨0⟩
          (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩ := by
      simpa [hflag] using hbad
    simp [solidityDecodeBytesLengthHeader, hflag, hbad0]
  have hlenSlot : (bytesLikeLengthLoc ⟨0⟩ evm).slot = ⟨0⟩ := by
    unfold bytesLikeLengthLoc
    split <;> rfl
  have hdecodeLoad :
      solidityDecodeBytesLengthHeader
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (bytesLikeLengthLoc ⟨0⟩ evm).slot) =
        .revert := by
    rw [hlenSlot, hload]
    exact hdecode
  simp [deleteStorage?, resolveStorageRef?, evalStorageRef, evalStorageRefSteps, currentRef,
    storageTypeAt?, stringStoreConfig, stringStoreContract, storageDecls, stringSt,
    clearStorage?, clearStorageBytesLike?, storagePrepareResultToEval, stringStoreStorageLayout,
    solidityPrepareBytesWrite?, solidityBytesBaseSlotAndLength?, stringStoreLayout,
    hload, hdecode,
    EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem stringStoreClearCurrentLongMalformedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := clearCurrentSelector_size hsel
  have hd := stringStoreDispatch_clearCurrent (cd := I.calldata) hsel'
  have hdec := stringStoreDecode_clearCurrent (I := I) hsz
  have hreach := stringStoreReachClearCurrent (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv (clearCurrentSelector_size hsel) hsize hsel
  have hrev := stringStoreX_bytesLengthDecoderLongMalformed
    (hreach := stringStoreX_clearCurrentReachDeleteDecoder hreach)
    (header := currentLengthHeaderWord σ_evm I) (ret := ⟨2210⟩)
    (rest := [⟨0⟩, ⟨2057⟩, ⟨0⟩, ⟨450⟩, stringStoreSelWord I])
    hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
    simpa [currentLengthHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        ⟨0⟩ = currentLengthHeaderWord σ_evm I := by
    simp [Solm.EVM.storageLoad, initState, State.lookupAccount, Account.lookupStorage,
      currentLengthHeaderWord, hslot]
  have hbody :
      ExecTransitionBody stringStoreConfig stringStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        clearCurrentTransition.body .reverted := by
    exact clearCurrentBodyRevertsOfDelete
      (by simp only [initState]; exact hwv)
      (deleteCurrentMalformedLong (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        hload hflag hbad)
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem stringStoreClearCurrentShortMalformedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := clearCurrentSelector_size hsel
  have hd := stringStoreDispatch_clearCurrent (cd := I.calldata) hsel'
  have hdec := stringStoreDecode_clearCurrent (I := I) hsz
  have hreach := stringStoreReachClearCurrent (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv (clearCurrentSelector_size hsel) hsize hsel
  have hrev := stringStoreX_bytesLengthDecoderShortMalformed
    (hreach := stringStoreX_clearCurrentReachDeleteDecoder hreach)
    (header := currentLengthHeaderWord σ_evm I) (ret := ⟨2210⟩)
    (rest := [⟨0⟩, ⟨2057⟩, ⟨0⟩, ⟨450⟩, stringStoreSelWord I])
    hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
    simpa [currentLengthHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        ⟨0⟩ = currentLengthHeaderWord σ_evm I := by
    simp [Solm.EVM.storageLoad, initState, State.lookupAccount, Account.lookupStorage,
      currentLengthHeaderWord, hslot]
  have hbody :
      ExecTransitionBody stringStoreConfig stringStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        clearCurrentTransition.body .reverted := by
    exact clearCurrentBodyRevertsOfDelete
      (by simp only [initState]; exact hwv)
      (deleteCurrentMalformedShort (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        hload hflag hbad)
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem stringStoreClearCurrentRuntime_of_nonzeroHeader
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hheader : currentLengthHeaderWord σ_evm I = ⟨0⟩
  · exact stringStoreClearCurrentShortZeroRuntime
      hcode hsize hperm hwv hsel hAccounts hheader
  · by_cases hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩
    · by_cases hvalid :
        UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt
            (UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩
      · exact stringStoreClearCurrentShortValidRuntime_of_header
          (len := UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          hcode hsize hperm hwv hsel hAccounts hflag rfl hvalid
      · have hbad :
            UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
              (UInt256.lt
                (UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
                ⟨32⟩) = ⟨0⟩ := by
          by_contra hbad
          exact hvalid hbad
        exact stringStoreClearCurrentShortMalformedRuntime
          hcode hsize hperm hwv hsel hAccounts hflag hbad
    · by_cases hvalidLong :
        UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩
      · exact stringStoreClearCurrentLongValidRuntime
          hcode hsize hperm hwv hsel hAccounts hheader hflag hvalidLong
      · have hbad :
            UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
              (UInt256.lt (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) = ⟨0⟩ := by
          by_contra hbad
          exact hvalidLong hbad
        exact stringStoreClearCurrentLongMalformedRuntime
          hcode hsize hperm hwv hsel hAccounts hflag hbad

theorem clearAllBodyReturns {evm evm₁ evm₂ evm₃ : EVM.State}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hdelCurrent : deleteStorage? stringStoreConfig
      { contract := stringStoreContract, locals := ∅ } evm currentRef = .ok evm₁)
    (hdelRaw : deleteStorage? stringStoreConfig
      { contract := stringStoreContract, locals := ∅ } evm₁ rawRef = .ok evm₂)
    (hdelHistory : deleteStorage? stringStoreConfig
      { contract := stringStoreContract, locals := ∅ } evm₂ historyRef = .ok evm₃) :
    ExecTransitionBody stringStoreConfig stringStoreContract evm ∅ clearAllTransition.body
      (.returned { contract := stringStoreContract, locals := ∅ } evm₃ none) := by
  exact ExecFuncBody.execBlockOK <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.delete hdelCurrent) <|
        ExecBlock.consNormal (ExecStmt.delete hdelRaw) <|
          ExecBlock.consNormal (ExecStmt.delete hdelHistory) ExecBlock.nil

theorem clearAllBodyRevertsOfCurrentDelete {evm : EVM.State}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hdelCurrent : deleteStorage? stringStoreConfig
      { contract := stringStoreContract, locals := ∅ } evm currentRef = .revert) :
    ExecTransitionBody stringStoreConfig stringStoreContract evm ∅ clearAllTransition.body
      .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert (ExecStmt.deleteRevert hdelCurrent)

theorem clearAllBodyRevertsOfRawDelete {evm evm₁ : EVM.State}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hdelCurrent : deleteStorage? stringStoreConfig
      { contract := stringStoreContract, locals := ∅ } evm currentRef = .ok evm₁)
    (hdelRaw : deleteStorage? stringStoreConfig
      { contract := stringStoreContract, locals := ∅ } evm₁ rawRef = .revert) :
    ExecTransitionBody stringStoreConfig stringStoreContract evm ∅ clearAllTransition.body
      .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.delete hdelCurrent) <|
        ExecBlock.consRevert (ExecStmt.deleteRevert hdelRaw)

theorem clearAllBodyReturnsShortZero {evm : EVM.State}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hcurrent : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = ⟨0⟩)
    (hraw : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ = ⟨0⟩)
    (hhistory : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩) :
    ExecTransitionBody stringStoreConfig stringStoreContract evm ∅ clearAllTransition.body
      (.returned { contract := stringStoreContract, locals := ∅ }
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ ⟨0⟩)
            evm.executionEnv.codeOwner ⟨2⟩ ⟨0⟩)
          evm.executionEnv.codeOwner ⟨1⟩ ⟨0⟩) none) := by
  set evm₁ := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ ⟨0⟩ with hevm₁
  set evm₂ := Solm.EVM.storageStore evm₁ evm.executionEnv.codeOwner ⟨2⟩ ⟨0⟩ with hevm₂
  have henv₁ : evm₁.executionEnv = evm.executionEnv := by
    rw [hevm₁, storageStore_executionEnv]
  have hlocCurrent := storageLocLoad_bytesLikeLengthLoc_zero (base := ⟨0⟩) hcurrent
  have hdelCurrent :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evm currentRef = .ok evm₁ := by
    simpa [hevm₁] using deleteCurrentShortZero hcurrent hlocCurrent
  have hraw₁ :
      Solm.EVM.storageLoad evm₁ evm₁.executionEnv.codeOwner ⟨2⟩ = ⟨0⟩ := by
    rw [hevm₁, storageStore_executionEnv]
    have hne := sstoreAccountMap_storage_findD_ne evm.accountMap evm.executionEnv.codeOwner
      ⟨2⟩ ⟨0⟩ ⟨0⟩ (by decide)
    unfold Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
    rw [storageStore_accountMap]
    simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using hne.trans hraw
  have hlocRaw := storageLocLoad_bytesLikeLengthLoc_zero (evm := evm₁) (base := ⟨2⟩) hraw₁
  have hdelRaw :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evm₁ rawRef = .ok evm₂ := by
    simpa [hevm₂, henv₁] using deleteRawShortZero hraw₁ hlocRaw
  have hhistory₁ :
      Solm.EVM.storageLoad evm₁ evm₁.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
    rw [hevm₁, storageStore_executionEnv]
    have hne := sstoreAccountMap_storage_findD_ne evm.accountMap evm.executionEnv.codeOwner
      ⟨1⟩ ⟨0⟩ ⟨0⟩ (by decide)
    unfold Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
    rw [storageStore_accountMap]
    simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using
      hne.trans hhistory
  have hhistory₂ :
      Solm.EVM.storageLoad evm₂ evm₂.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
    rw [hevm₂, storageStore_executionEnv, henv₁]
    have hne := sstoreAccountMap_storage_findD_ne evm₁.accountMap evm.executionEnv.codeOwner
      ⟨1⟩ ⟨2⟩ ⟨0⟩ (by decide)
    have hhistory₁orig :
        Solm.EVM.storageLoad evm₁ evm.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
      simpa [henv₁] using hhistory₁
    unfold Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
    rw [storageStore_accountMap]
    simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using
      hne.trans hhistory₁orig
  have hdelHistory :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evm₂ historyRef =
          .ok (Solm.EVM.storageStore evm₂ evm₂.executionEnv.codeOwner ⟨1⟩ ⟨0⟩) :=
    deleteHistoryZero hhistory₂
  simpa [hevm₁, hevm₂, henv₁, storageStore_executionEnv] using
    clearAllBodyReturns hwv hdelCurrent hdelRaw hdelHistory

theorem clearAllBodyReturnsCurrentShortRawHistoryZero {evm : EVM.State} {header len : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hcurrent : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩)
    (hraw : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ = ⟨0⟩)
    (hhistory : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩) :
    ExecTransitionBody stringStoreConfig stringStoreContract evm ∅ clearAllTransition.body
      (.returned { contract := stringStoreContract, locals := ∅ }
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ ⟨0⟩)
            evm.executionEnv.codeOwner ⟨2⟩ ⟨0⟩)
          evm.executionEnv.codeOwner ⟨1⟩ ⟨0⟩) none) := by
  set evm₁ := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ ⟨0⟩ with hevm₁
  set evm₂ := Solm.EVM.storageStore evm₁ evm.executionEnv.codeOwner ⟨2⟩ ⟨0⟩ with hevm₂
  have henv₁ : evm₁.executionEnv = evm.executionEnv := by
    rw [hevm₁, storageStore_executionEnv]
  have hpacked : checkBytesPacked ⟨0⟩ evm = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hcurrent hflag
  have hdelCurrent :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evm currentRef = .ok evm₁ := by
    simpa [hevm₁] using deleteCurrentShortPacked hcurrent hpacked hflag hlen hvalid
  have hraw₁ :
      Solm.EVM.storageLoad evm₁ evm₁.executionEnv.codeOwner ⟨2⟩ = ⟨0⟩ := by
    rw [hevm₁, storageStore_executionEnv]
    have hne := sstoreAccountMap_storage_findD_ne evm.accountMap evm.executionEnv.codeOwner
      ⟨2⟩ ⟨0⟩ ⟨0⟩ (by decide)
    unfold Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
    rw [storageStore_accountMap]
    simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using hne.trans hraw
  have hlocRaw := storageLocLoad_bytesLikeLengthLoc_zero (evm := evm₁) (base := ⟨2⟩) hraw₁
  have hdelRaw :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evm₁ rawRef = .ok evm₂ := by
    simpa [hevm₂, henv₁] using deleteRawShortZero hraw₁ hlocRaw
  have hhistory₁ :
      Solm.EVM.storageLoad evm₁ evm₁.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
    rw [hevm₁, storageStore_executionEnv]
    have hne := sstoreAccountMap_storage_findD_ne evm.accountMap evm.executionEnv.codeOwner
      ⟨1⟩ ⟨0⟩ ⟨0⟩ (by decide)
    unfold Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
    rw [storageStore_accountMap]
    simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using
      hne.trans hhistory
  have hhistory₂ :
      Solm.EVM.storageLoad evm₂ evm₂.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
    rw [hevm₂, storageStore_executionEnv, henv₁]
    have hne := sstoreAccountMap_storage_findD_ne evm₁.accountMap evm.executionEnv.codeOwner
      ⟨1⟩ ⟨2⟩ ⟨0⟩ (by decide)
    have hhistory₁orig :
        Solm.EVM.storageLoad evm₁ evm.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
      simpa [henv₁] using hhistory₁
    unfold Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
    rw [storageStore_accountMap]
    simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using
      hne.trans hhistory₁orig
  have hdelHistory :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evm₂ historyRef =
          .ok (Solm.EVM.storageStore evm₂ evm₂.executionEnv.codeOwner ⟨1⟩ ⟨0⟩) :=
    deleteHistoryZero hhistory₂
  simpa [hevm₁, hevm₂, henv₁, storageStore_executionEnv] using
    clearAllBodyReturns hwv hdelCurrent hdelRaw hdelHistory

theorem clearAllBodyReturnsCurrentZeroRawShortHistoryZero
    {evm : EVM.State} {header len : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hcurrent : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = ⟨0⟩)
    (hraw : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩)
    (hhistory : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩) :
    ExecTransitionBody stringStoreConfig stringStoreContract evm ∅ clearAllTransition.body
      (.returned { contract := stringStoreContract, locals := ∅ }
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ ⟨0⟩)
            evm.executionEnv.codeOwner ⟨2⟩ ⟨0⟩)
          evm.executionEnv.codeOwner ⟨1⟩ ⟨0⟩) none) := by
  set evm₁ := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ ⟨0⟩ with hevm₁
  set evm₂ := Solm.EVM.storageStore evm₁ evm.executionEnv.codeOwner ⟨2⟩ ⟨0⟩ with hevm₂
  have henv₁ : evm₁.executionEnv = evm.executionEnv := by
    rw [hevm₁, storageStore_executionEnv]
  have hlocCurrent := storageLocLoad_bytesLikeLengthLoc_zero (base := ⟨0⟩) hcurrent
  have hdelCurrent :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evm currentRef = .ok evm₁ := by
    simpa [hevm₁] using deleteCurrentShortZero hcurrent hlocCurrent
  have hraw₁ :
      Solm.EVM.storageLoad evm₁ evm₁.executionEnv.codeOwner ⟨2⟩ = header := by
    rw [hevm₁, storageStore_executionEnv]
    have hne := sstoreAccountMap_storage_findD_ne evm.accountMap evm.executionEnv.codeOwner
      ⟨2⟩ ⟨0⟩ ⟨0⟩ (by decide)
    unfold Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
    rw [storageStore_accountMap]
    simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using hne.trans hraw
  have hpacked : checkBytesPacked ⟨2⟩ evm₁ = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hraw₁ hflag
  have hdelRaw :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evm₁ rawRef = .ok evm₂ := by
    simpa [hevm₂, henv₁] using deleteRawShortPacked hraw₁ hpacked hflag hlen hvalid
  have hhistory₁ :
      Solm.EVM.storageLoad evm₁ evm₁.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
    rw [hevm₁, storageStore_executionEnv]
    have hne := sstoreAccountMap_storage_findD_ne evm.accountMap evm.executionEnv.codeOwner
      ⟨1⟩ ⟨0⟩ ⟨0⟩ (by decide)
    unfold Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
    rw [storageStore_accountMap]
    simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using
      hne.trans hhistory
  have hhistory₂ :
      Solm.EVM.storageLoad evm₂ evm₂.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
    rw [hevm₂, storageStore_executionEnv, henv₁]
    have hne := sstoreAccountMap_storage_findD_ne evm₁.accountMap evm.executionEnv.codeOwner
      ⟨1⟩ ⟨2⟩ ⟨0⟩ (by decide)
    have hhistory₁orig :
        Solm.EVM.storageLoad evm₁ evm.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
      simpa [henv₁] using hhistory₁
    unfold Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
    rw [storageStore_accountMap]
    simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using
      hne.trans hhistory₁orig
  have hdelHistory :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evm₂ historyRef =
          .ok (Solm.EVM.storageStore evm₂ evm₂.executionEnv.codeOwner ⟨1⟩ ⟨0⟩) :=
    deleteHistoryZero hhistory₂
  simpa [hevm₁, hevm₂, henv₁, storageStore_executionEnv] using
    clearAllBodyReturns hwv hdelCurrent hdelRaw hdelHistory

theorem clearAllBodyReturnsCurrentZeroRawLongHistoryZero
    {evm : EVM.State} {header len : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hcurrent : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = ⟨0⟩)
    (hraw : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩)
    (hhistory : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩) :
    ExecTransitionBody stringStoreConfig stringStoreContract evm ∅ clearAllTransition.body
      (.returned { contract := stringStoreContract, locals := ∅ }
        (Solm.EVM.storageStore
          (clearSolidityBytesDataWordsFrom
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ ⟨0⟩)
              evm.executionEnv.codeOwner ⟨2⟩ ⟨0⟩)
            ⟨2⟩ 0 ((len.toNat + 31) / 32))
          evm.executionEnv.codeOwner ⟨1⟩ ⟨0⟩) none) := by
  set evm₁ := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ ⟨0⟩ with hevm₁
  set evm₂len := Solm.EVM.storageStore evm₁ evm.executionEnv.codeOwner ⟨2⟩ ⟨0⟩
    with hevm₂len
  set evm₂ := clearSolidityBytesDataWordsFrom evm₂len ⟨2⟩ 0 ((len.toNat + 31) / 32)
    with hevm₂
  have henv₁ : evm₁.executionEnv = evm.executionEnv := by
    rw [hevm₁, storageStore_executionEnv]
  have henv₂len : evm₂len.executionEnv = evm.executionEnv := by
    rw [hevm₂len, storageStore_executionEnv, henv₁]
  have hlocCurrent := storageLocLoad_bytesLikeLengthLoc_zero (base := ⟨0⟩) hcurrent
  have hdelCurrent :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evm currentRef = .ok evm₁ := by
    simpa [hevm₁] using deleteCurrentShortZero hcurrent hlocCurrent
  have hraw₁ :
      Solm.EVM.storageLoad evm₁ evm₁.executionEnv.codeOwner ⟨2⟩ = header := by
    rw [hevm₁, storageStore_executionEnv]
    have hne := sstoreAccountMap_storage_findD_ne evm.accountMap evm.executionEnv.codeOwner
      ⟨2⟩ ⟨0⟩ ⟨0⟩ (by decide)
    unfold Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
    rw [storageStore_accountMap]
    simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using hne.trans hraw
  have hdelRaw :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evm₁ rawRef = .ok evm₂ := by
    simpa [hevm₂, hevm₂len, henv₁] using
      deleteRawLongPrepared hraw₁ hflag hlen hvalid
  have hhistory₁ :
      Solm.EVM.storageLoad evm₁ evm₁.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
    rw [hevm₁, storageStore_executionEnv]
    have hne := sstoreAccountMap_storage_findD_ne evm.accountMap evm.executionEnv.codeOwner
      ⟨1⟩ ⟨0⟩ ⟨0⟩ (by decide)
    unfold Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
    rw [storageStore_accountMap]
    simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using
      hne.trans hhistory
  have hhistory₂len :
      Solm.EVM.storageLoad evm₂len evm₂len.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
    rw [hevm₂len, storageStore_executionEnv, henv₁]
    have hne := sstoreAccountMap_storage_findD_ne evm₁.accountMap evm.executionEnv.codeOwner
      ⟨1⟩ ⟨2⟩ ⟨0⟩ (by decide)
    have hhistory₁orig :
        Solm.EVM.storageLoad evm₁ evm.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
      simpa [henv₁] using hhistory₁
    unfold Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
    rw [storageStore_accountMap]
    simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using
      hne.trans hhistory₁orig
  have hhistory₂ :
      Solm.EVM.storageLoad evm₂ evm₂.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
    simpa [hevm₂] using
      (clearSolidityRawDataWords_preserves_historyLoad evm₂len
        ((len.toNat + 31) / 32)).trans hhistory₂len
  have hdelHistory :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evm₂ historyRef =
          .ok (Solm.EVM.storageStore evm₂ evm₂.executionEnv.codeOwner ⟨1⟩ ⟨0⟩) :=
    deleteHistoryZero hhistory₂
  simpa [hevm₁, hevm₂len, hevm₂, henv₁, henv₂len,
    storageStore_executionEnv, clearSolidityBytesDataWordsFrom_executionEnv] using
    clearAllBodyReturns hwv hdelCurrent hdelRaw hdelHistory

theorem clearAllBodyReturnsCurrentShortRawLongHistoryZero
    {evm : EVM.State} {currentHeader currentLen rawHeader rawLen : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hcurrent : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = currentHeader)
    (hcurrentFlag : UInt256.land currentHeader ⟨1⟩ = ⟨0⟩)
    (hcurrentLen : currentLen = UInt256.land (UInt256.div currentHeader ⟨2⟩) ⟨127⟩)
    (hcurrentValid : UInt256.sub (UInt256.land currentHeader ⟨1⟩)
        (UInt256.lt currentLen ⟨32⟩) ≠ ⟨0⟩)
    (hraw : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ = rawHeader)
    (hrawFlag : UInt256.land rawHeader ⟨1⟩ ≠ ⟨0⟩)
    (hrawLen : rawLen = UInt256.div rawHeader ⟨2⟩)
    (hrawValid : UInt256.sub (UInt256.land rawHeader ⟨1⟩)
        (UInt256.lt rawLen ⟨32⟩) ≠ ⟨0⟩)
    (hhistory : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩) :
    ExecTransitionBody stringStoreConfig stringStoreContract evm ∅ clearAllTransition.body
      (.returned { contract := stringStoreContract, locals := ∅ }
        (Solm.EVM.storageStore
          (clearSolidityBytesDataWordsFrom
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ ⟨0⟩)
              evm.executionEnv.codeOwner ⟨2⟩ ⟨0⟩)
            ⟨2⟩ 0 ((rawLen.toNat + 31) / 32))
          evm.executionEnv.codeOwner ⟨1⟩ ⟨0⟩) none) := by
  set evm₁ := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ ⟨0⟩ with hevm₁
  set evm₂len := Solm.EVM.storageStore evm₁ evm.executionEnv.codeOwner ⟨2⟩ ⟨0⟩
    with hevm₂len
  set evm₂ := clearSolidityBytesDataWordsFrom evm₂len ⟨2⟩ 0 ((rawLen.toNat + 31) / 32)
    with hevm₂
  have henv₁ : evm₁.executionEnv = evm.executionEnv := by
    rw [hevm₁, storageStore_executionEnv]
  have henv₂len : evm₂len.executionEnv = evm.executionEnv := by
    rw [hevm₂len, storageStore_executionEnv, henv₁]
  have hpackedCurrent : checkBytesPacked ⟨0⟩ evm = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hcurrent hcurrentFlag
  have hdelCurrent :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evm currentRef = .ok evm₁ := by
    simpa [hevm₁] using
      deleteCurrentShortPacked hcurrent hpackedCurrent hcurrentFlag hcurrentLen hcurrentValid
  have hraw₁ :
      Solm.EVM.storageLoad evm₁ evm₁.executionEnv.codeOwner ⟨2⟩ = rawHeader := by
    rw [hevm₁, storageStore_executionEnv]
    have hne := sstoreAccountMap_storage_findD_ne evm.accountMap evm.executionEnv.codeOwner
      ⟨2⟩ ⟨0⟩ ⟨0⟩ (by decide)
    unfold Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
    rw [storageStore_accountMap]
    simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using hne.trans hraw
  have hdelRaw :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evm₁ rawRef = .ok evm₂ := by
    simpa [hevm₂, hevm₂len, henv₁] using
      deleteRawLongPrepared hraw₁ hrawFlag hrawLen hrawValid
  have hhistory₁ :
      Solm.EVM.storageLoad evm₁ evm₁.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
    rw [hevm₁, storageStore_executionEnv]
    have hne := sstoreAccountMap_storage_findD_ne evm.accountMap evm.executionEnv.codeOwner
      ⟨1⟩ ⟨0⟩ ⟨0⟩ (by decide)
    unfold Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
    rw [storageStore_accountMap]
    simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using
      hne.trans hhistory
  have hhistory₂len :
      Solm.EVM.storageLoad evm₂len evm₂len.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
    rw [hevm₂len, storageStore_executionEnv, henv₁]
    have hne := sstoreAccountMap_storage_findD_ne evm₁.accountMap evm.executionEnv.codeOwner
      ⟨1⟩ ⟨2⟩ ⟨0⟩ (by decide)
    have hhistory₁orig :
        Solm.EVM.storageLoad evm₁ evm.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
      simpa [henv₁] using hhistory₁
    unfold Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
    rw [storageStore_accountMap]
    simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using
      hne.trans hhistory₁orig
  have hhistory₂ :
      Solm.EVM.storageLoad evm₂ evm₂.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
    simpa [hevm₂] using
      (clearSolidityRawDataWords_preserves_historyLoad evm₂len
        ((rawLen.toNat + 31) / 32)).trans hhistory₂len
  have hdelHistory :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evm₂ historyRef =
          .ok (Solm.EVM.storageStore evm₂ evm₂.executionEnv.codeOwner ⟨1⟩ ⟨0⟩) :=
    deleteHistoryZero hhistory₂
  simpa [hevm₁, hevm₂len, hevm₂, henv₁, henv₂len,
    storageStore_executionEnv, clearSolidityBytesDataWordsFrom_executionEnv] using
    clearAllBodyReturns hwv hdelCurrent hdelRaw hdelHistory

theorem clearAllBodyReturnsCurrentLongRawHistoryZero
    {evm : EVM.State} {currentHeader currentLen : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hcurrent : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = currentHeader)
    (hcurrentFlag : UInt256.land currentHeader ⟨1⟩ ≠ ⟨0⟩)
    (hcurrentLen : currentLen = UInt256.div currentHeader ⟨2⟩)
    (hcurrentValid : UInt256.sub (UInt256.land currentHeader ⟨1⟩)
        (UInt256.lt currentLen ⟨32⟩) ≠ ⟨0⟩)
    (hraw : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ = ⟨0⟩)
    (hhistory : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩) :
    ExecTransitionBody stringStoreConfig stringStoreContract evm ∅ clearAllTransition.body
      (.returned { contract := stringStoreContract, locals := ∅ }
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (clearSolidityBytesDataWordsFrom
              (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ ⟨0⟩)
              ⟨0⟩ 0 ((currentLen.toNat + 31) / 32))
            evm.executionEnv.codeOwner ⟨2⟩ ⟨0⟩)
          evm.executionEnv.codeOwner ⟨1⟩ ⟨0⟩) none) := by
  set evm₁len := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ ⟨0⟩
    with hevm₁len
  set evm₁ := clearSolidityBytesDataWordsFrom evm₁len ⟨0⟩ 0
    ((currentLen.toNat + 31) / 32) with hevm₁
  set evm₂ := Solm.EVM.storageStore evm₁ evm.executionEnv.codeOwner ⟨2⟩ ⟨0⟩ with hevm₂
  have henv₁len : evm₁len.executionEnv = evm.executionEnv := by
    rw [hevm₁len, storageStore_executionEnv]
  have henv₁ : evm₁.executionEnv = evm.executionEnv := by
    rw [hevm₁, clearSolidityBytesDataWordsFrom_executionEnv, henv₁len]
  have hdelCurrent :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evm currentRef = .ok evm₁ := by
    simpa [hevm₁len, hevm₁] using
      deleteCurrentLongPrepared hcurrent hcurrentFlag hcurrentLen hcurrentValid
  have hraw₁ :
      Solm.EVM.storageLoad evm₁ evm₁.executionEnv.codeOwner ⟨2⟩ = ⟨0⟩ := by
    simpa [hevm₁] using
      (clearSolidityCurrentDataWords_preserves_rawLoad evm₁len
        ((currentLen.toNat + 31) / 32)).trans (by
          rw [hevm₁len, storageStore_executionEnv]
          have hne := sstoreAccountMap_storage_findD_ne evm.accountMap
            evm.executionEnv.codeOwner ⟨2⟩ ⟨0⟩ ⟨0⟩ (by decide)
          unfold Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
          rw [storageStore_accountMap]
          simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using
            hne.trans hraw)
  have hlocRaw := storageLocLoad_bytesLikeLengthLoc_zero (evm := evm₁) (base := ⟨2⟩) hraw₁
  have hdelRaw :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evm₁ rawRef = .ok evm₂ := by
    simpa [hevm₂, henv₁] using deleteRawShortZero hraw₁ hlocRaw
  have hhistory₁ :
      Solm.EVM.storageLoad evm₁ evm₁.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
    simpa [hevm₁] using
      (clearSolidityCurrentDataWords_preserves_historyLoad evm₁len
        ((currentLen.toNat + 31) / 32)).trans (by
          rw [hevm₁len, storageStore_executionEnv]
          have hne := sstoreAccountMap_storage_findD_ne evm.accountMap
            evm.executionEnv.codeOwner ⟨1⟩ ⟨0⟩ ⟨0⟩ (by decide)
          unfold Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
          rw [storageStore_accountMap]
          simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using
            hne.trans hhistory)
  have hhistory₂ :
      Solm.EVM.storageLoad evm₂ evm₂.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
    rw [hevm₂, storageStore_executionEnv, henv₁]
    have hne := sstoreAccountMap_storage_findD_ne evm₁.accountMap evm.executionEnv.codeOwner
      ⟨1⟩ ⟨2⟩ ⟨0⟩ (by decide)
    have hhistory₁orig :
        Solm.EVM.storageLoad evm₁ evm.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
      simpa [henv₁] using hhistory₁
    unfold Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
    rw [storageStore_accountMap]
    simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using
      hne.trans hhistory₁orig
  have hdelHistory :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evm₂ historyRef =
          .ok (Solm.EVM.storageStore evm₂ evm₂.executionEnv.codeOwner ⟨1⟩ ⟨0⟩) :=
    deleteHistoryZero hhistory₂
  simpa [hevm₁len, hevm₁, hevm₂, henv₁len, henv₁,
    storageStore_executionEnv, clearSolidityBytesDataWordsFrom_executionEnv] using
    clearAllBodyReturns hwv hdelCurrent hdelRaw hdelHistory

theorem clearAllBodyReturnsCurrentLongRawShortHistoryZero
    {evm : EVM.State} {currentHeader currentLen rawHeader rawLen : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hcurrent : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = currentHeader)
    (hcurrentFlag : UInt256.land currentHeader ⟨1⟩ ≠ ⟨0⟩)
    (hcurrentLen : currentLen = UInt256.div currentHeader ⟨2⟩)
    (hcurrentValid : UInt256.sub (UInt256.land currentHeader ⟨1⟩)
        (UInt256.lt currentLen ⟨32⟩) ≠ ⟨0⟩)
    (hraw : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ = rawHeader)
    (hrawFlag : UInt256.land rawHeader ⟨1⟩ = ⟨0⟩)
    (hrawLen : rawLen = UInt256.land (UInt256.div rawHeader ⟨2⟩) ⟨127⟩)
    (hrawValid : UInt256.sub (UInt256.land rawHeader ⟨1⟩)
        (UInt256.lt rawLen ⟨32⟩) ≠ ⟨0⟩)
    (hhistory : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩) :
    ExecTransitionBody stringStoreConfig stringStoreContract evm ∅ clearAllTransition.body
      (.returned { contract := stringStoreContract, locals := ∅ }
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (clearSolidityBytesDataWordsFrom
              (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ ⟨0⟩)
              ⟨0⟩ 0 ((currentLen.toNat + 31) / 32))
            evm.executionEnv.codeOwner ⟨2⟩ ⟨0⟩)
          evm.executionEnv.codeOwner ⟨1⟩ ⟨0⟩) none) := by
  set evm₁len := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ ⟨0⟩
    with hevm₁len
  set evm₁ := clearSolidityBytesDataWordsFrom evm₁len ⟨0⟩ 0
    ((currentLen.toNat + 31) / 32) with hevm₁
  set evm₂ := Solm.EVM.storageStore evm₁ evm.executionEnv.codeOwner ⟨2⟩ ⟨0⟩ with hevm₂
  have henv₁len : evm₁len.executionEnv = evm.executionEnv := by
    rw [hevm₁len, storageStore_executionEnv]
  have henv₁ : evm₁.executionEnv = evm.executionEnv := by
    rw [hevm₁, clearSolidityBytesDataWordsFrom_executionEnv, henv₁len]
  have hdelCurrent :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evm currentRef = .ok evm₁ := by
    simpa [hevm₁len, hevm₁] using
      deleteCurrentLongPrepared hcurrent hcurrentFlag hcurrentLen hcurrentValid
  have hraw₁ :
      Solm.EVM.storageLoad evm₁ evm₁.executionEnv.codeOwner ⟨2⟩ = rawHeader := by
    simpa [hevm₁] using
      (clearSolidityCurrentDataWords_preserves_rawLoad evm₁len
        ((currentLen.toNat + 31) / 32)).trans (by
          rw [hevm₁len, storageStore_executionEnv]
          have hne := sstoreAccountMap_storage_findD_ne evm.accountMap
            evm.executionEnv.codeOwner ⟨2⟩ ⟨0⟩ ⟨0⟩ (by decide)
          unfold Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
          rw [storageStore_accountMap]
          simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using
            hne.trans hraw)
  have hpackedRaw : checkBytesPacked ⟨2⟩ evm₁ = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hraw₁ hrawFlag
  have hdelRaw :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evm₁ rawRef = .ok evm₂ := by
    simpa [hevm₂, henv₁] using
      deleteRawShortPacked hraw₁ hpackedRaw hrawFlag hrawLen hrawValid
  have hhistory₁ :
      Solm.EVM.storageLoad evm₁ evm₁.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
    simpa [hevm₁] using
      (clearSolidityCurrentDataWords_preserves_historyLoad evm₁len
        ((currentLen.toNat + 31) / 32)).trans (by
          rw [hevm₁len, storageStore_executionEnv]
          have hne := sstoreAccountMap_storage_findD_ne evm.accountMap
            evm.executionEnv.codeOwner ⟨1⟩ ⟨0⟩ ⟨0⟩ (by decide)
          unfold Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
          rw [storageStore_accountMap]
          simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using
            hne.trans hhistory)
  have hhistory₂ :
      Solm.EVM.storageLoad evm₂ evm₂.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
    rw [hevm₂, storageStore_executionEnv, henv₁]
    have hne := sstoreAccountMap_storage_findD_ne evm₁.accountMap evm.executionEnv.codeOwner
      ⟨1⟩ ⟨2⟩ ⟨0⟩ (by decide)
    have hhistory₁orig :
        Solm.EVM.storageLoad evm₁ evm.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
      simpa [henv₁] using hhistory₁
    unfold Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
    rw [storageStore_accountMap]
    simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using
      hne.trans hhistory₁orig
  have hdelHistory :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evm₂ historyRef =
          .ok (Solm.EVM.storageStore evm₂ evm₂.executionEnv.codeOwner ⟨1⟩ ⟨0⟩) :=
    deleteHistoryZero hhistory₂
  simpa [hevm₁len, hevm₁, hevm₂, henv₁len, henv₁,
    storageStore_executionEnv, clearSolidityBytesDataWordsFrom_executionEnv] using
    clearAllBodyReturns hwv hdelCurrent hdelRaw hdelHistory

theorem clearAllBodyReturnsCurrentLongRawLongHistoryZero
    {evm : EVM.State} {currentHeader currentLen rawHeader rawLen : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hcurrent : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = currentHeader)
    (hcurrentFlag : UInt256.land currentHeader ⟨1⟩ ≠ ⟨0⟩)
    (hcurrentLen : currentLen = UInt256.div currentHeader ⟨2⟩)
    (hcurrentValid : UInt256.sub (UInt256.land currentHeader ⟨1⟩)
        (UInt256.lt currentLen ⟨32⟩) ≠ ⟨0⟩)
    (hraw : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ = rawHeader)
    (hrawFlag : UInt256.land rawHeader ⟨1⟩ ≠ ⟨0⟩)
    (hrawLen : rawLen = UInt256.div rawHeader ⟨2⟩)
    (hrawValid : UInt256.sub (UInt256.land rawHeader ⟨1⟩)
        (UInt256.lt rawLen ⟨32⟩) ≠ ⟨0⟩)
    (hhistory : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩) :
    ExecTransitionBody stringStoreConfig stringStoreContract evm ∅ clearAllTransition.body
      (.returned { contract := stringStoreContract, locals := ∅ }
        (Solm.EVM.storageStore
          (clearSolidityBytesDataWordsFrom
            (Solm.EVM.storageStore
              (clearSolidityBytesDataWordsFrom
                (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ ⟨0⟩)
                ⟨0⟩ 0 ((currentLen.toNat + 31) / 32))
              evm.executionEnv.codeOwner ⟨2⟩ ⟨0⟩)
            ⟨2⟩ 0 ((rawLen.toNat + 31) / 32))
          evm.executionEnv.codeOwner ⟨1⟩ ⟨0⟩) none) := by
  set evm₁len := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ ⟨0⟩
    with hevm₁len
  set evm₁ := clearSolidityBytesDataWordsFrom evm₁len ⟨0⟩ 0
    ((currentLen.toNat + 31) / 32) with hevm₁
  set evm₂len := Solm.EVM.storageStore evm₁ evm.executionEnv.codeOwner ⟨2⟩ ⟨0⟩
    with hevm₂len
  set evm₂ := clearSolidityBytesDataWordsFrom evm₂len ⟨2⟩ 0
    ((rawLen.toNat + 31) / 32) with hevm₂
  have henv₁len : evm₁len.executionEnv = evm.executionEnv := by
    rw [hevm₁len, storageStore_executionEnv]
  have henv₁ : evm₁.executionEnv = evm.executionEnv := by
    rw [hevm₁, clearSolidityBytesDataWordsFrom_executionEnv, henv₁len]
  have henv₂len : evm₂len.executionEnv = evm.executionEnv := by
    rw [hevm₂len, storageStore_executionEnv, henv₁]
  have hdelCurrent :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evm currentRef = .ok evm₁ := by
    simpa [hevm₁len, hevm₁] using
      deleteCurrentLongPrepared hcurrent hcurrentFlag hcurrentLen hcurrentValid
  have hraw₁ :
      Solm.EVM.storageLoad evm₁ evm₁.executionEnv.codeOwner ⟨2⟩ = rawHeader := by
    simpa [hevm₁] using
      (clearSolidityCurrentDataWords_preserves_rawLoad evm₁len
        ((currentLen.toNat + 31) / 32)).trans (by
          rw [hevm₁len, storageStore_executionEnv]
          have hne := sstoreAccountMap_storage_findD_ne evm.accountMap
            evm.executionEnv.codeOwner ⟨2⟩ ⟨0⟩ ⟨0⟩ (by decide)
          unfold Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
          rw [storageStore_accountMap]
          simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using
            hne.trans hraw)
  have hdelRaw :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evm₁ rawRef = .ok evm₂ := by
    simpa [hevm₂, hevm₂len, henv₁] using
      deleteRawLongPrepared hraw₁ hrawFlag hrawLen hrawValid
  have hhistory₁ :
      Solm.EVM.storageLoad evm₁ evm₁.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
    simpa [hevm₁] using
      (clearSolidityCurrentDataWords_preserves_historyLoad evm₁len
        ((currentLen.toNat + 31) / 32)).trans (by
          rw [hevm₁len, storageStore_executionEnv]
          have hne := sstoreAccountMap_storage_findD_ne evm.accountMap
            evm.executionEnv.codeOwner ⟨1⟩ ⟨0⟩ ⟨0⟩ (by decide)
          unfold Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
          rw [storageStore_accountMap]
          simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using
            hne.trans hhistory)
  have hhistory₂len :
      Solm.EVM.storageLoad evm₂len evm₂len.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
    rw [hevm₂len, storageStore_executionEnv, henv₁]
    have hne := sstoreAccountMap_storage_findD_ne evm₁.accountMap evm.executionEnv.codeOwner
      ⟨1⟩ ⟨2⟩ ⟨0⟩ (by decide)
    have hhistory₁orig :
        Solm.EVM.storageLoad evm₁ evm.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
      simpa [henv₁] using hhistory₁
    unfold Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
    rw [storageStore_accountMap]
    simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using
      hne.trans hhistory₁orig
  have hhistory₂ :
      Solm.EVM.storageLoad evm₂ evm₂.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
    simpa [hevm₂] using
      (clearSolidityRawDataWords_preserves_historyLoad evm₂len
        ((rawLen.toNat + 31) / 32)).trans hhistory₂len
  have hdelHistory :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evm₂ historyRef =
          .ok (Solm.EVM.storageStore evm₂ evm₂.executionEnv.codeOwner ⟨1⟩ ⟨0⟩) :=
    deleteHistoryZero hhistory₂
  simpa [hevm₁len, hevm₁, hevm₂len, hevm₂, henv₁len, henv₁, henv₂len,
    storageStore_executionEnv, clearSolidityBytesDataWordsFrom_executionEnv] using
    clearAllBodyReturns hwv hdelCurrent hdelRaw hdelHistory

theorem clearAllBodyReturnsCurrentShortRawShortHistoryZero
    {evm : EVM.State} {currentHeader currentLen rawHeader rawLen : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hcurrent : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = currentHeader)
    (hcurrentFlag : UInt256.land currentHeader ⟨1⟩ = ⟨0⟩)
    (hcurrentLen : currentLen = UInt256.land (UInt256.div currentHeader ⟨2⟩) ⟨127⟩)
    (hcurrentValid : UInt256.sub (UInt256.land currentHeader ⟨1⟩)
        (UInt256.lt currentLen ⟨32⟩) ≠ ⟨0⟩)
    (hraw : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ = rawHeader)
    (hrawFlag : UInt256.land rawHeader ⟨1⟩ = ⟨0⟩)
    (hrawLen : rawLen = UInt256.land (UInt256.div rawHeader ⟨2⟩) ⟨127⟩)
    (hrawValid : UInt256.sub (UInt256.land rawHeader ⟨1⟩)
        (UInt256.lt rawLen ⟨32⟩) ≠ ⟨0⟩)
    (hhistory : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩) :
    ExecTransitionBody stringStoreConfig stringStoreContract evm ∅ clearAllTransition.body
      (.returned { contract := stringStoreContract, locals := ∅ }
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ ⟨0⟩)
            evm.executionEnv.codeOwner ⟨2⟩ ⟨0⟩)
          evm.executionEnv.codeOwner ⟨1⟩ ⟨0⟩) none) := by
  set evm₁ := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ ⟨0⟩ with hevm₁
  set evm₂ := Solm.EVM.storageStore evm₁ evm.executionEnv.codeOwner ⟨2⟩ ⟨0⟩ with hevm₂
  have henv₁ : evm₁.executionEnv = evm.executionEnv := by
    rw [hevm₁, storageStore_executionEnv]
  have hpackedCurrent : checkBytesPacked ⟨0⟩ evm = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hcurrent hcurrentFlag
  have hdelCurrent :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evm currentRef = .ok evm₁ := by
    simpa [hevm₁] using
      deleteCurrentShortPacked hcurrent hpackedCurrent hcurrentFlag hcurrentLen hcurrentValid
  have hraw₁ :
      Solm.EVM.storageLoad evm₁ evm₁.executionEnv.codeOwner ⟨2⟩ = rawHeader := by
    rw [hevm₁, storageStore_executionEnv]
    have hne := sstoreAccountMap_storage_findD_ne evm.accountMap evm.executionEnv.codeOwner
      ⟨2⟩ ⟨0⟩ ⟨0⟩ (by decide)
    unfold Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
    rw [storageStore_accountMap]
    simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using hne.trans hraw
  have hpackedRaw : checkBytesPacked ⟨2⟩ evm₁ = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hraw₁ hrawFlag
  have hdelRaw :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evm₁ rawRef = .ok evm₂ := by
    simpa [hevm₂, henv₁] using
      deleteRawShortPacked hraw₁ hpackedRaw hrawFlag hrawLen hrawValid
  have hhistory₁ :
      Solm.EVM.storageLoad evm₁ evm₁.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
    rw [hevm₁, storageStore_executionEnv]
    have hne := sstoreAccountMap_storage_findD_ne evm.accountMap evm.executionEnv.codeOwner
      ⟨1⟩ ⟨0⟩ ⟨0⟩ (by decide)
    unfold Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
    rw [storageStore_accountMap]
    simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using
      hne.trans hhistory
  have hhistory₂ :
      Solm.EVM.storageLoad evm₂ evm₂.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
    rw [hevm₂, storageStore_executionEnv, henv₁]
    have hne := sstoreAccountMap_storage_findD_ne evm₁.accountMap evm.executionEnv.codeOwner
      ⟨1⟩ ⟨2⟩ ⟨0⟩ (by decide)
    have hhistory₁orig :
        Solm.EVM.storageLoad evm₁ evm.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
      simpa [henv₁] using hhistory₁
    unfold Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
    rw [storageStore_accountMap]
    simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using
      hne.trans hhistory₁orig
  have hdelHistory :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evm₂ historyRef =
          .ok (Solm.EVM.storageStore evm₂ evm₂.executionEnv.codeOwner ⟨1⟩ ⟨0⟩) :=
    deleteHistoryZero hhistory₂
  simpa [hevm₁, hevm₂, henv₁, storageStore_executionEnv] using
    clearAllBodyReturns hwv hdelCurrent hdelRaw hdelHistory

theorem stringStoreClearAllShortZeroRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcurrent : currentLengthHeaderWord σ_evm I = ⟨0⟩)
    (hraw : rawLengthHeaderWord σ_evm I = ⟨0⟩)
    (hhistory : historyLengthWord σ_evm I = ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := clearAllSelector_size hsel
  have hd := stringStoreDispatch_clearAll (cd := I.calldata) hsel'
  have hdec := stringStoreDecode_clearAll (I := I) hsz
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hcurrentSolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ = ⟨0⟩ := by
    have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
      simpa [currentLengthHeaderWord] using hword.symm
    have hload' :
        Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
          currentLengthHeaderWord σ_evm I := by
      simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
        Account.lookupStorage, currentLengthHeaderWord, hslot]
    simpa [hcurrent] using hload'
  have hrawSolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ = ⟨0⟩ := by
    have hword := rawLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) := by
      simpa [rawLengthHeaderWord] using hword.symm
    have hload' :
        Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ =
          rawLengthHeaderWord σ_evm I := by
      simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
        Account.lookupStorage, rawLengthHeaderWord, hslot]
    simpa [hraw] using hload'
  have hhistorySolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) := by
      exact (accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩).symm
    have hload' :
        Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ =
          historyLengthWord σ_evm I := by
      simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
        Account.lookupStorage, historyLengthWord, hslot]
    simpa [hhistory] using hload'
  have hbody := clearAllBodyReturnsShortZero
    (evm := evmSolm0) (by simp [evmSolm0, initState]; exact hwv)
    hcurrentSolm hrawSolm hhistorySolm
  have hreach := stringStoreReachClearAll (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv (clearAllSelector_size hsel) hsize hsel
  have hret := stringStoreX_clearAllShortZeroValid
    (g := Sat256.ofUInt256 g) hperm hreach hcurrent hraw hhistory
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm0, initState, storageStore_createdAccounts])
    (by
      simp [evmSolm0, initState, storageStore_accountMap]
      exact accountMapEquiv_sstoreAccountMap_three I.codeOwner I.codeOwner I.codeOwner
        ⟨0⟩ ⟨0⟩ ⟨2⟩ ⟨0⟩ ⟨1⟩ ⟨0⟩ hAccounts)
    (returnEquiv.void rfl rfl rfl)

theorem stringStoreClearAllCurrentShortRawHistoryZeroRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g len : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hlen :
      len = UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩)
    (hraw : rawLengthHeaderWord σ_evm I = ⟨0⟩)
    (hhistory : historyLengthWord σ_evm I = ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := clearAllSelector_size hsel
  have hd := stringStoreDispatch_clearAll (cd := I.calldata) hsel'
  have hdec := stringStoreDecode_clearAll (I := I) hsz
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hcurrentSolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        currentLengthHeaderWord σ_evm I := by
    have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
      simpa [currentLengthHeaderWord] using hword.symm
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, currentLengthHeaderWord, hslot]
  have hrawSolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ = ⟨0⟩ := by
    have hword := rawLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) := by
      simpa [rawLengthHeaderWord] using hword.symm
    have hload' :
        Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ =
          rawLengthHeaderWord σ_evm I := by
      simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
        Account.lookupStorage, rawLengthHeaderWord, hslot]
    simpa [hraw] using hload'
  have hhistorySolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) := by
      exact (accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩).symm
    have hload' :
        Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ =
          historyLengthWord σ_evm I := by
      simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
        Account.lookupStorage, historyLengthWord, hslot]
    simpa [hhistory] using hload'
  have hbody := clearAllBodyReturnsCurrentShortRawHistoryZero
    (evm := evmSolm0) (header := currentLengthHeaderWord σ_evm I) (len := len)
    (by simp [evmSolm0, initState]; exact hwv)
    hcurrentSolm hflag hlen hvalid hrawSolm hhistorySolm
  have hreach := stringStoreReachClearAll (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv (clearAllSelector_size hsel) hsize hsel
  have hret := stringStoreX_clearAllCurrentShortRawHistoryZeroValid
    (g := Sat256.ofUInt256 g) (len := len)
    hperm hreach hflag hlen hvalid hraw hhistory
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm0, initState, storageStore_createdAccounts])
    (by
      simp [evmSolm0, initState, storageStore_accountMap]
      exact accountMapEquiv_sstoreAccountMap_three I.codeOwner I.codeOwner I.codeOwner
        ⟨0⟩ ⟨0⟩ ⟨2⟩ ⟨0⟩ ⟨1⟩ ⟨0⟩ hAccounts)
    (returnEquiv.void rfl rfl rfl)

theorem stringStoreClearAllCurrentZeroRawShortHistoryZeroRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g len : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcurrent : currentLengthHeaderWord σ_evm I = ⟨0⟩)
    (hflag : UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hlen :
      len = UInt256.land (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩)
    (hhistory : historyLengthWord σ_evm I = ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := clearAllSelector_size hsel
  have hd := stringStoreDispatch_clearAll (cd := I.calldata) hsel'
  have hdec := stringStoreDecode_clearAll (I := I) hsz
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hcurrentSolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ = ⟨0⟩ := by
    have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
      simpa [currentLengthHeaderWord] using hword.symm
    have hload' :
        Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
          currentLengthHeaderWord σ_evm I := by
      simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
        Account.lookupStorage, currentLengthHeaderWord, hslot]
    simpa [hcurrent] using hload'
  have hrawSolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ =
        rawLengthHeaderWord σ_evm I := by
    have hword := rawLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) := by
      simpa [rawLengthHeaderWord] using hword.symm
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, rawLengthHeaderWord, hslot]
  have hhistorySolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) := by
      exact (accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩).symm
    have hload' :
        Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ =
          historyLengthWord σ_evm I := by
      simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
        Account.lookupStorage, historyLengthWord, hslot]
    simpa [hhistory] using hload'
  have hbody := clearAllBodyReturnsCurrentZeroRawShortHistoryZero
    (evm := evmSolm0) (header := rawLengthHeaderWord σ_evm I) (len := len)
    (by simp [evmSolm0, initState]; exact hwv)
    hcurrentSolm hrawSolm hflag hlen hvalid hhistorySolm
  have hreach := stringStoreReachClearAll (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv (clearAllSelector_size hsel) hsize hsel
  have hret := stringStoreX_clearAllCurrentZeroRawShortHistoryZeroValid
    (g := Sat256.ofUInt256 g) (len := len)
    hperm hreach hcurrent hflag hlen hvalid hhistory
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm0, initState, storageStore_createdAccounts])
    (by
      simp [evmSolm0, initState, storageStore_accountMap]
      exact accountMapEquiv_sstoreAccountMap_three I.codeOwner I.codeOwner I.codeOwner
        ⟨0⟩ ⟨0⟩ ⟨2⟩ ⟨0⟩ ⟨1⟩ ⟨0⟩ hAccounts)
    (returnEquiv.void rfl rfl rfl)

theorem stringStoreClearAllCurrentZeroRawLongHistoryZeroRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g len : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcurrent : currentLengthHeaderWord σ_evm I = ⟨0⟩)
    (hflag : UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩)
    (hhistory : historyLengthWord σ_evm I = ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hlenLt : len.toNat < 2 ^ 255 :=
    clearCurrent_len_toNat_lt_sign_of_div2
      (header := rawLengthHeaderWord σ_evm I) (len := len) hlen
  have hcountNat :
      (UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩).toNat =
        (len.toNat + 31) / 32 := by
    have hadd : (((⟨31⟩ : UInt256) + len).toNat = 31 + len.toNat) := by
      rw [uadd_toNat, show (⟨31⟩ : UInt256).toNat = 31 from by decide]
      rw [Nat.add_comm 31 len.toNat]
      exact Nat.mod_eq_of_lt (by
        have hsize : (2 : Nat) ^ 255 + 31 < UInt256.size := by
          norm_num [UInt256.size]
        nlinarith)
    rw [udiv_toNat, hadd, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
    rw [Nat.add_comm 31 len.toNat]
  have hsel' : ((⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := clearAllSelector_size hsel
  have hd := stringStoreDispatch_clearAll (cd := I.calldata) hsel'
  have hdec := stringStoreDecode_clearAll (I := I) hsz
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hcurrentSolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ = ⟨0⟩ := by
    have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
      simpa [currentLengthHeaderWord] using hword.symm
    have hload' :
        Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
          currentLengthHeaderWord σ_evm I := by
      simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
        Account.lookupStorage, currentLengthHeaderWord, hslot]
    simpa [hcurrent] using hload'
  have hrawSolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ =
        rawLengthHeaderWord σ_evm I := by
    have hword := rawLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) := by
      simpa [rawLengthHeaderWord] using hword.symm
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, rawLengthHeaderWord, hslot]
  have hhistorySolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) := by
      exact (accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩).symm
    have hload' :
        Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ =
          historyLengthWord σ_evm I := by
      simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
        Account.lookupStorage, historyLengthWord, hslot]
    simpa [hhistory] using hload'
  have hbody := clearAllBodyReturnsCurrentZeroRawLongHistoryZero
    (evm := evmSolm0) (header := rawLengthHeaderWord σ_evm I) (len := len)
    (by simp [evmSolm0, initState]; exact hwv)
    hcurrentSolm hrawSolm hflag hlen hvalid hhistorySolm
  have hreach := stringStoreReachClearAll (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv (clearAllSelector_size hsel) hsize hsel
  have hret := stringStoreX_clearAllCurrentZeroRawLongHistoryZeroValid
    (g := Sat256.ofUInt256 g) (len := len)
    hperm hreach hcurrent hflag hlen hvalid hhistory
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by
      simp [evmSolm0, initState, storageStore_createdAccounts,
        clearSolidityBytesDataWordsFrom_createdAccounts])
    (by
      simp [evmSolm0, initState, storageStore_accountMap, storageStore_executionEnv,
        clearSolidityBytesDataWordsFrom_accountMap, hcountNat,
        clearRawBaseWord_eq_solidityBytesDataBaseSlot]
      have hafterCurrent :=
        accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩ ⟨0⟩ hAccounts
      have hafterRawLen :=
        accountMapEquiv_sstoreAccountMap I.codeOwner ⟨2⟩ ⟨0⟩ hafterCurrent
      have hafterRawData :=
        accountMapEquiv_clearDataWordsForwardFrom I.codeOwner
          (solidityBytesDataBaseSlot ⟨2⟩) (⟨0⟩ : UInt256) ((len.toNat + 31) / 32)
          hafterRawLen
      exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨1⟩ ⟨0⟩ hafterRawData)
    (returnEquiv.void rfl rfl rfl)

theorem stringStoreClearAllCurrentShortRawLongHistoryZeroRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g currentLen rawLen : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcurrentFlag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hcurrentLen :
      currentLen =
        UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
    (hcurrentValid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt currentLen ⟨32⟩) ≠ ⟨0⟩)
    (hrawFlag : UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hrawLen : rawLen = UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩)
    (hrawValid : UInt256.sub (UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt rawLen ⟨32⟩) ≠ ⟨0⟩)
    (hhistory : historyLengthWord σ_evm I = ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hlenLt : rawLen.toNat < 2 ^ 255 :=
    clearCurrent_len_toNat_lt_sign_of_div2
      (header := rawLengthHeaderWord σ_evm I) (len := rawLen) hrawLen
  have hcountNat :
      (UInt256.div ((⟨31⟩ : UInt256) + rawLen) ⟨32⟩).toNat =
        (rawLen.toNat + 31) / 32 := by
    have hadd : (((⟨31⟩ : UInt256) + rawLen).toNat = 31 + rawLen.toNat) := by
      rw [uadd_toNat, show (⟨31⟩ : UInt256).toNat = 31 from by decide]
      rw [Nat.add_comm 31 rawLen.toNat]
      exact Nat.mod_eq_of_lt (by
        have hsize : (2 : Nat) ^ 255 + 31 < UInt256.size := by
          norm_num [UInt256.size]
        nlinarith)
    rw [udiv_toNat, hadd, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
    rw [Nat.add_comm 31 rawLen.toNat]
  have hsel' : ((⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := clearAllSelector_size hsel
  have hd := stringStoreDispatch_clearAll (cd := I.calldata) hsel'
  have hdec := stringStoreDecode_clearAll (I := I) hsz
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hcurrentSolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        currentLengthHeaderWord σ_evm I := by
    have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
      simpa [currentLengthHeaderWord] using hword.symm
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, currentLengthHeaderWord, hslot]
  have hrawSolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ =
        rawLengthHeaderWord σ_evm I := by
    have hword := rawLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) := by
      simpa [rawLengthHeaderWord] using hword.symm
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, rawLengthHeaderWord, hslot]
  have hhistorySolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) := by
      exact (accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩).symm
    have hload' :
        Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ =
          historyLengthWord σ_evm I := by
      simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
        Account.lookupStorage, historyLengthWord, hslot]
    simpa [hhistory] using hload'
  have hbody := clearAllBodyReturnsCurrentShortRawLongHistoryZero
    (evm := evmSolm0)
    (currentHeader := currentLengthHeaderWord σ_evm I) (currentLen := currentLen)
    (rawHeader := rawLengthHeaderWord σ_evm I) (rawLen := rawLen)
    (by simp [evmSolm0, initState]; exact hwv)
    hcurrentSolm hcurrentFlag hcurrentLen hcurrentValid
    hrawSolm hrawFlag hrawLen hrawValid hhistorySolm
  have hreach := stringStoreReachClearAll (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv (clearAllSelector_size hsel) hsize hsel
  have hret := stringStoreX_clearAllCurrentShortRawLongHistoryZeroValid
    (g := Sat256.ofUInt256 g) (currentLen := currentLen) (rawLen := rawLen)
    hperm hreach hcurrentFlag hcurrentLen hcurrentValid hrawFlag hrawLen hrawValid hhistory
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by
      simp [evmSolm0, initState, storageStore_createdAccounts,
        clearSolidityBytesDataWordsFrom_createdAccounts])
    (by
      simp [evmSolm0, initState, storageStore_accountMap, storageStore_executionEnv,
        clearSolidityBytesDataWordsFrom_accountMap, hcountNat,
        clearRawBaseWord_eq_solidityBytesDataBaseSlot]
      have hafterCurrent :=
        accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩ ⟨0⟩ hAccounts
      have hafterRawLen :=
        accountMapEquiv_sstoreAccountMap I.codeOwner ⟨2⟩ ⟨0⟩ hafterCurrent
      have hafterRawData :=
        accountMapEquiv_clearDataWordsForwardFrom I.codeOwner
          (solidityBytesDataBaseSlot ⟨2⟩) (⟨0⟩ : UInt256) ((rawLen.toNat + 31) / 32)
          hafterRawLen
      have hfinal :=
        (@accountMapEquiv_sstoreAccountMap _ _ I.codeOwner ⟨1⟩ ⟨0⟩ hafterRawData)
      simpa [evmSolm0, initState, storageStore_executionEnv,
        clearSolidityBytesDataWordsFrom_executionEnv] using hfinal)
    (returnEquiv.void rfl rfl rfl)

theorem stringStoreClearAllCurrentLongRawHistoryZeroRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hraw : rawLengthHeaderWord σ_evm I = ⟨0⟩)
    (hhistory : historyLengthWord σ_evm I = ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len := UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩
  have hlen : len = UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩ := rfl
  have hlenLt : len.toNat < 2 ^ 255 :=
    clearCurrent_len_toNat_lt_sign_of_div2
      (header := currentLengthHeaderWord σ_evm I) (len := len) hlen
  have hcountNat :
      (UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩).toNat =
        (len.toNat + 31) / 32 := by
    have hadd : (((⟨31⟩ : UInt256) + len).toNat = 31 + len.toNat) := by
      rw [uadd_toNat, show (⟨31⟩ : UInt256).toNat = 31 from by decide]
      rw [Nat.add_comm 31 len.toNat]
      exact Nat.mod_eq_of_lt (by
        have hsize : (2 : Nat) ^ 255 + 31 < UInt256.size := by
          norm_num [UInt256.size]
        nlinarith)
    rw [udiv_toNat, hadd, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
    rw [Nat.add_comm 31 len.toNat]
  have hsel' : ((⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := clearAllSelector_size hsel
  have hd := stringStoreDispatch_clearAll (cd := I.calldata) hsel'
  have hdec := stringStoreDecode_clearAll (I := I) hsz
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hcurrentSolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        currentLengthHeaderWord σ_evm I := by
    have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
      simpa [currentLengthHeaderWord] using hword.symm
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, currentLengthHeaderWord, hslot]
  have hrawSolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ = ⟨0⟩ := by
    have hword := rawLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) := by
      simpa [rawLengthHeaderWord] using hword.symm
    have hload' :
        Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ =
          rawLengthHeaderWord σ_evm I := by
      simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
        Account.lookupStorage, rawLengthHeaderWord, hslot]
    simpa [hraw] using hload'
  have hhistorySolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) := by
      exact (accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩).symm
    have hload' :
        Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ =
          historyLengthWord σ_evm I := by
      simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
        Account.lookupStorage, historyLengthWord, hslot]
    simpa [hhistory] using hload'
  have hbody := clearAllBodyReturnsCurrentLongRawHistoryZero
    (evm := evmSolm0) (currentHeader := currentLengthHeaderWord σ_evm I)
    (currentLen := len)
    (by simp [evmSolm0, initState]; exact hwv)
    hcurrentSolm hflag hlen (by simpa [len] using hvalid) hrawSolm hhistorySolm
  have hreach := stringStoreReachClearAll (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv (clearAllSelector_size hsel) hsize hsel
  have hret := stringStoreX_clearAllCurrentLongRawHistoryZeroValid
    (g := Sat256.ofUInt256 g) (len := len)
    hperm hreach hflag (by simpa [len] using hvalid) hlen hraw hhistory
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by
      simp [evmSolm0, initState, storageStore_createdAccounts,
        clearSolidityBytesDataWordsFrom_createdAccounts])
    (by
      simp [evmSolm0, initState, storageStore_accountMap, storageStore_executionEnv,
        clearSolidityBytesDataWordsFrom_accountMap, hcountNat,
        clearCurrentBaseWord_eq_solidityBytesDataBaseSlot]
      have hafterCurrentLen :=
        accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩ ⟨0⟩ hAccounts
      have hafterCurrentData :=
        accountMapEquiv_clearDataWordsForwardFrom I.codeOwner
          (solidityBytesDataBaseSlot ⟨0⟩) (⟨0⟩ : UInt256) ((len.toNat + 31) / 32)
          hafterCurrentLen
      have hafterRaw :=
        accountMapEquiv_sstoreAccountMap I.codeOwner ⟨2⟩ ⟨0⟩ hafterCurrentData
      exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨1⟩ ⟨0⟩ hafterRaw)
    (returnEquiv.void rfl rfl rfl)

theorem stringStoreClearAllCurrentLongRawShortHistoryZeroRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g currentLen rawLen : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcurrentFlag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hcurrentValid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt currentLen ⟨32⟩) ≠ ⟨0⟩)
    (hcurrentLen : currentLen = UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩)
    (hrawFlag : UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hrawLen :
      rawLen = UInt256.land (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
    (hrawValid : UInt256.sub (UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt rawLen ⟨32⟩) ≠ ⟨0⟩)
    (hhistory : historyLengthWord σ_evm I = ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hlenLt : currentLen.toNat < 2 ^ 255 :=
    clearCurrent_len_toNat_lt_sign_of_div2
      (header := currentLengthHeaderWord σ_evm I) (len := currentLen) hcurrentLen
  have hcountNat :
      (UInt256.div ((⟨31⟩ : UInt256) + currentLen) ⟨32⟩).toNat =
        (currentLen.toNat + 31) / 32 := by
    have hadd : (((⟨31⟩ : UInt256) + currentLen).toNat = 31 + currentLen.toNat) := by
      rw [uadd_toNat, show (⟨31⟩ : UInt256).toNat = 31 from by decide]
      rw [Nat.add_comm 31 currentLen.toNat]
      exact Nat.mod_eq_of_lt (by
        have hsize : (2 : Nat) ^ 255 + 31 < UInt256.size := by
          norm_num [UInt256.size]
        nlinarith)
    rw [udiv_toNat, hadd, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
    rw [Nat.add_comm 31 currentLen.toNat]
  have hsel' : ((⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := clearAllSelector_size hsel
  have hd := stringStoreDispatch_clearAll (cd := I.calldata) hsel'
  have hdec := stringStoreDecode_clearAll (I := I) hsz
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hcurrentSolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        currentLengthHeaderWord σ_evm I := by
    have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
      simpa [currentLengthHeaderWord] using hword.symm
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, currentLengthHeaderWord, hslot]
  have hrawSolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ =
        rawLengthHeaderWord σ_evm I := by
    have hword := rawLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) := by
      simpa [rawLengthHeaderWord] using hword.symm
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, rawLengthHeaderWord, hslot]
  have hhistorySolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) := by
      exact (accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩).symm
    have hload' :
        Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ =
          historyLengthWord σ_evm I := by
      simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
        Account.lookupStorage, historyLengthWord, hslot]
    simpa [hhistory] using hload'
  have hbody := clearAllBodyReturnsCurrentLongRawShortHistoryZero
    (evm := evmSolm0)
    (currentHeader := currentLengthHeaderWord σ_evm I) (currentLen := currentLen)
    (rawHeader := rawLengthHeaderWord σ_evm I) (rawLen := rawLen)
    (by simp [evmSolm0, initState]; exact hwv)
    hcurrentSolm hcurrentFlag hcurrentLen hcurrentValid
    hrawSolm hrawFlag hrawLen hrawValid hhistorySolm
  have hreach := stringStoreReachClearAll (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv (clearAllSelector_size hsel) hsize hsel
  have hret := stringStoreX_clearAllCurrentLongRawShortHistoryZeroValid
    (g := Sat256.ofUInt256 g) (currentLen := currentLen) (rawLen := rawLen)
    hperm hreach hcurrentFlag hcurrentValid hcurrentLen hrawFlag hrawLen hrawValid hhistory
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by
      simp [evmSolm0, initState, storageStore_createdAccounts,
        clearSolidityBytesDataWordsFrom_createdAccounts])
    (by
      simp [evmSolm0, initState, storageStore_accountMap, storageStore_executionEnv,
        clearSolidityBytesDataWordsFrom_accountMap, hcountNat,
        clearCurrentBaseWord_eq_solidityBytesDataBaseSlot]
      have hafterCurrentLen :=
        accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩ ⟨0⟩ hAccounts
      have hafterCurrentData :=
        accountMapEquiv_clearDataWordsForwardFrom I.codeOwner
          (solidityBytesDataBaseSlot ⟨0⟩) (⟨0⟩ : UInt256) ((currentLen.toNat + 31) / 32)
          hafterCurrentLen
      have hafterRaw :=
        accountMapEquiv_sstoreAccountMap I.codeOwner ⟨2⟩ ⟨0⟩ hafterCurrentData
      exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨1⟩ ⟨0⟩ hafterRaw)
    (returnEquiv.void rfl rfl rfl)

theorem stringStoreClearAllCurrentLongRawLongHistoryZeroRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g currentLen rawLen : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcurrentFlag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hcurrentValid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt currentLen ⟨32⟩) ≠ ⟨0⟩)
    (hcurrentLen : currentLen = UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩)
    (hrawFlag : UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hrawLen : rawLen = UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩)
    (hrawValid : UInt256.sub (UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt rawLen ⟨32⟩) ≠ ⟨0⟩)
    (hhistory : historyLengthWord σ_evm I = ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hcurrentLenLt : currentLen.toNat < 2 ^ 255 :=
    clearCurrent_len_toNat_lt_sign_of_div2
      (header := currentLengthHeaderWord σ_evm I) (len := currentLen) hcurrentLen
  have hcurrentCountNat :
      (UInt256.div ((⟨31⟩ : UInt256) + currentLen) ⟨32⟩).toNat =
        (currentLen.toNat + 31) / 32 := by
    have hadd : (((⟨31⟩ : UInt256) + currentLen).toNat = 31 + currentLen.toNat) := by
      rw [uadd_toNat, show (⟨31⟩ : UInt256).toNat = 31 from by decide]
      rw [Nat.add_comm 31 currentLen.toNat]
      exact Nat.mod_eq_of_lt (by
        have hsize : (2 : Nat) ^ 255 + 31 < UInt256.size := by
          norm_num [UInt256.size]
        nlinarith)
    rw [udiv_toNat, hadd, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
    rw [Nat.add_comm 31 currentLen.toNat]
  have hrawLenLt : rawLen.toNat < 2 ^ 255 :=
    clearCurrent_len_toNat_lt_sign_of_div2
      (header := rawLengthHeaderWord σ_evm I) (len := rawLen) hrawLen
  have hrawCountNat :
      (UInt256.div ((⟨31⟩ : UInt256) + rawLen) ⟨32⟩).toNat =
        (rawLen.toNat + 31) / 32 := by
    have hadd : (((⟨31⟩ : UInt256) + rawLen).toNat = 31 + rawLen.toNat) := by
      rw [uadd_toNat, show (⟨31⟩ : UInt256).toNat = 31 from by decide]
      rw [Nat.add_comm 31 rawLen.toNat]
      exact Nat.mod_eq_of_lt (by
        have hsize : (2 : Nat) ^ 255 + 31 < UInt256.size := by
          norm_num [UInt256.size]
        nlinarith)
    rw [udiv_toNat, hadd, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
    rw [Nat.add_comm 31 rawLen.toNat]
  have hsel' : ((⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := clearAllSelector_size hsel
  have hd := stringStoreDispatch_clearAll (cd := I.calldata) hsel'
  have hdec := stringStoreDecode_clearAll (I := I) hsz
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hcurrentSolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        currentLengthHeaderWord σ_evm I := by
    have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
      simpa [currentLengthHeaderWord] using hword.symm
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, currentLengthHeaderWord, hslot]
  have hrawSolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ =
        rawLengthHeaderWord σ_evm I := by
    have hword := rawLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) := by
      simpa [rawLengthHeaderWord] using hword.symm
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, rawLengthHeaderWord, hslot]
  have hhistorySolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) := by
      exact (accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩).symm
    have hload' :
        Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ =
          historyLengthWord σ_evm I := by
      simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
        Account.lookupStorage, historyLengthWord, hslot]
    simpa [hhistory] using hload'
  have hbody := clearAllBodyReturnsCurrentLongRawLongHistoryZero
    (evm := evmSolm0)
    (currentHeader := currentLengthHeaderWord σ_evm I) (currentLen := currentLen)
    (rawHeader := rawLengthHeaderWord σ_evm I) (rawLen := rawLen)
    (by simp [evmSolm0, initState]; exact hwv)
    hcurrentSolm hcurrentFlag hcurrentLen hcurrentValid
    hrawSolm hrawFlag hrawLen hrawValid hhistorySolm
  have hreach := stringStoreReachClearAll (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv (clearAllSelector_size hsel) hsize hsel
  have hret := stringStoreX_clearAllCurrentLongRawLongHistoryZeroValid
    (g := Sat256.ofUInt256 g) (currentLen := currentLen) (rawLen := rawLen)
    hperm hreach hcurrentFlag hcurrentValid hcurrentLen hrawFlag hrawLen hrawValid hhistory
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by
      simp [evmSolm0, initState, storageStore_createdAccounts,
        clearSolidityBytesDataWordsFrom_createdAccounts])
    (by
      simp [evmSolm0, initState, storageStore_accountMap, storageStore_executionEnv,
        clearSolidityBytesDataWordsFrom_accountMap, hcurrentCountNat, hrawCountNat,
        clearCurrentBaseWord_eq_solidityBytesDataBaseSlot,
        clearRawBaseWord_eq_solidityBytesDataBaseSlot]
      have hafterCurrentLen :=
        accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩ ⟨0⟩ hAccounts
      have hafterCurrentData :=
        accountMapEquiv_clearDataWordsForwardFrom I.codeOwner
          (solidityBytesDataBaseSlot ⟨0⟩) (⟨0⟩ : UInt256) ((currentLen.toNat + 31) / 32)
          hafterCurrentLen
      have hafterRawLen :=
        accountMapEquiv_sstoreAccountMap I.codeOwner ⟨2⟩ ⟨0⟩ hafterCurrentData
      have hafterRawData :=
        accountMapEquiv_clearDataWordsForwardFrom I.codeOwner
          (solidityBytesDataBaseSlot ⟨2⟩) (⟨0⟩ : UInt256) ((rawLen.toNat + 31) / 32)
          hafterRawLen
      have hfinal :=
        (@accountMapEquiv_sstoreAccountMap _ _ I.codeOwner ⟨1⟩ ⟨0⟩ hafterRawData)
      simpa [evmSolm0, initState, storageStore_executionEnv,
        clearSolidityBytesDataWordsFrom_executionEnv] using hfinal)
    (returnEquiv.void rfl rfl rfl)

theorem stringStoreClearAllCurrentShortRawShortHistoryZeroRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g currentLen rawLen : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcurrentFlag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hcurrentLen :
      currentLen =
        UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
    (hcurrentValid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt currentLen ⟨32⟩) ≠ ⟨0⟩)
    (hrawFlag : UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hrawLen :
      rawLen = UInt256.land (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
    (hrawValid : UInt256.sub (UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt rawLen ⟨32⟩) ≠ ⟨0⟩)
    (hhistory : historyLengthWord σ_evm I = ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := clearAllSelector_size hsel
  have hd := stringStoreDispatch_clearAll (cd := I.calldata) hsel'
  have hdec := stringStoreDecode_clearAll (I := I) hsz
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hcurrentSolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        currentLengthHeaderWord σ_evm I := by
    have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
      simpa [currentLengthHeaderWord] using hword.symm
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, currentLengthHeaderWord, hslot]
  have hrawSolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ =
        rawLengthHeaderWord σ_evm I := by
    have hword := rawLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) := by
      simpa [rawLengthHeaderWord] using hword.symm
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, rawLengthHeaderWord, hslot]
  have hhistorySolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) := by
      exact (accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩).symm
    have hload' :
        Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ =
          historyLengthWord σ_evm I := by
      simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
        Account.lookupStorage, historyLengthWord, hslot]
    simpa [hhistory] using hload'
  have hbody := clearAllBodyReturnsCurrentShortRawShortHistoryZero
    (evm := evmSolm0)
    (currentHeader := currentLengthHeaderWord σ_evm I) (currentLen := currentLen)
    (rawHeader := rawLengthHeaderWord σ_evm I) (rawLen := rawLen)
    (by simp [evmSolm0, initState]; exact hwv)
    hcurrentSolm hcurrentFlag hcurrentLen hcurrentValid
    hrawSolm hrawFlag hrawLen hrawValid hhistorySolm
  have hreach := stringStoreReachClearAll (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv (clearAllSelector_size hsel) hsize hsel
  have hret := stringStoreX_clearAllCurrentShortRawShortHistoryZeroValid
    (g := Sat256.ofUInt256 g) (currentLen := currentLen) (rawLen := rawLen)
    hperm hreach hcurrentFlag hcurrentLen hcurrentValid hrawFlag hrawLen hrawValid hhistory
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm0, initState, storageStore_createdAccounts])
    (by
      simp [evmSolm0, initState, storageStore_accountMap]
      exact accountMapEquiv_sstoreAccountMap_three I.codeOwner I.codeOwner I.codeOwner
        ⟨0⟩ ⟨0⟩ ⟨2⟩ ⟨0⟩ ⟨1⟩ ⟨0⟩ hAccounts)
    (returnEquiv.void rfl rfl rfl)

theorem stringStoreClearAllCurrentShortMalformedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := clearAllSelector_size hsel
  have hd := stringStoreDispatch_clearAll (cd := I.calldata) hsel'
  have hdec := stringStoreDecode_clearAll (I := I) hsz
  have hreach := stringStoreReachClearAll (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv (clearAllSelector_size hsel) hsize hsel
  have hrev := stringStoreX_clearAllCurrentShortMalformed
    (g := Sat256.ofUInt256 g) hreach hflag hbad
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
    simpa [currentLengthHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        currentLengthHeaderWord σ_evm I := by
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, currentLengthHeaderWord, hslot]
  have hbody :
      ExecTransitionBody stringStoreConfig stringStoreContract evmSolm0 ∅
        clearAllTransition.body .reverted := by
    exact clearAllBodyRevertsOfCurrentDelete
      (evm := evmSolm0) (by simp [evmSolm0, initState]; exact hwv)
      (deleteCurrentMalformedShort (evm := evmSolm0)
        hload hflag hbad)
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem stringStoreClearAllCurrentLongMalformedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) =
          ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := clearAllSelector_size hsel
  have hd := stringStoreDispatch_clearAll (cd := I.calldata) hsel'
  have hdec := stringStoreDecode_clearAll (I := I) hsz
  have hreach := stringStoreReachClearAll (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv (clearAllSelector_size hsel) hsize hsel
  have hrev := stringStoreX_clearAllCurrentLongMalformed
    (g := Sat256.ofUInt256 g) hreach hflag hbad
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
    simpa [currentLengthHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        currentLengthHeaderWord σ_evm I := by
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, currentLengthHeaderWord, hslot]
  have hbody :
      ExecTransitionBody stringStoreConfig stringStoreContract evmSolm0 ∅
        clearAllTransition.body .reverted := by
    exact clearAllBodyRevertsOfCurrentDelete
      (evm := evmSolm0) (by simp [evmSolm0, initState]; exact hwv)
      (deleteCurrentMalformedLong (evm := evmSolm0)
        hload hflag hbad)
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem stringStoreClearAllCurrentZeroRawShortMalformedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcurrent : currentLengthHeaderWord σ_evm I = ⟨0⟩)
    (hrawFlag : UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hrawBad : UInt256.sub (UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := clearAllSelector_size hsel
  have hd := stringStoreDispatch_clearAll (cd := I.calldata) hsel'
  have hdec := stringStoreDecode_clearAll (I := I) hsz
  let σ1 := sstoreAccountMap I.codeOwner σ_evm ⟨0⟩ ⟨0⟩
  have hreach := stringStoreReachClearAll (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv (clearAllSelector_size hsel) hsize hsel
  have h1 := stringStoreX_clearAllDeleteCurrentShortZero
    (g := Sat256.ofUInt256 g) hperm hreach hcurrent
  have hraw1 : rawLengthHeaderWord σ1 I = rawLengthHeaderWord σ_evm I := by
    have hne := sstoreAccountMap_storage_findD_ne σ_evm I.codeOwner ⟨2⟩ ⟨0⟩ ⟨0⟩
      (by decide)
    simpa [σ1, rawLengthHeaderWord] using hne
  have hrawFlag1 : UInt256.land (rawLengthHeaderWord σ1 I) ⟨1⟩ = ⟨0⟩ := by
    simpa [hraw1] using hrawFlag
  have hrawBad1 : UInt256.sub (UInt256.land (rawLengthHeaderWord σ1 I) ⟨1⟩)
      (UInt256.lt
        (UInt256.land (UInt256.div (rawLengthHeaderWord σ1 I) ⟨2⟩) ⟨127⟩)
        ⟨32⟩) = ⟨0⟩ := by
    simpa [hraw1] using hrawBad
  have hrev := stringStoreX_clearAllRawShortMalformed
    (g := Sat256.ofUInt256 g) (τ := σ1) h1 hrawFlag1 hrawBad1
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ ⟨0⟩
  have hcurrentSolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ = ⟨0⟩ := by
    have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
      simpa [currentLengthHeaderWord] using hword.symm
    have hload' :
        Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
          currentLengthHeaderWord σ_evm I := by
      simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
        Account.lookupStorage, currentLengthHeaderWord, hslot]
    simpa [hcurrent] using hload'
  have hrawSolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ =
        rawLengthHeaderWord σ_evm I := by
    have hword := rawLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) := by
      simpa [rawLengthHeaderWord] using hword.symm
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, rawLengthHeaderWord, hslot]
  have hdelCurrent :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evmSolm0 currentRef = .ok evmSolm1 := by
    have hloc := storageLocLoad_bytesLikeLengthLoc_zero (base := ⟨0⟩) hcurrentSolm
    simpa [evmSolm1] using deleteCurrentShortZero hcurrentSolm hloc
  have henv1 : evmSolm1.executionEnv = evmSolm0.executionEnv := by
    simp [evmSolm1, storageStore_executionEnv]
  have hrawSolm1 :
      Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨2⟩ =
        rawLengthHeaderWord σ_evm I := by
    simp only [evmSolm1, storageStore_executionEnv]
    have hne := sstoreAccountMap_storage_findD_ne evmSolm0.accountMap
      evmSolm0.executionEnv.codeOwner ⟨2⟩ ⟨0⟩ ⟨0⟩ (by decide)
    unfold Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
    rw [storageStore_accountMap]
    simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using
      hne.trans hrawSolm
  have hdelRaw :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evmSolm1 rawRef = .revert := by
    simpa [henv1] using
      deleteRawMalformedShort (evm := evmSolm1)
        hrawSolm1 hrawFlag hrawBad
  have hbody :
      ExecTransitionBody stringStoreConfig stringStoreContract evmSolm0 ∅
        clearAllTransition.body .reverted :=
    clearAllBodyRevertsOfRawDelete
      (evm := evmSolm0) (evm₁ := evmSolm1)
      (by simp [evmSolm0, initState]; exact hwv) hdelCurrent hdelRaw
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem stringStoreClearAllCurrentZeroRawLongMalformedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcurrent : currentLengthHeaderWord σ_evm I = ⟨0⟩)
    (hrawFlag : UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hrawBad : UInt256.sub (UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) =
          ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := clearAllSelector_size hsel
  have hd := stringStoreDispatch_clearAll (cd := I.calldata) hsel'
  have hdec := stringStoreDecode_clearAll (I := I) hsz
  let σ1 := sstoreAccountMap I.codeOwner σ_evm ⟨0⟩ ⟨0⟩
  have hreach := stringStoreReachClearAll (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv (clearAllSelector_size hsel) hsize hsel
  have h1 := stringStoreX_clearAllDeleteCurrentShortZero
    (g := Sat256.ofUInt256 g) hperm hreach hcurrent
  have hraw1 : rawLengthHeaderWord σ1 I = rawLengthHeaderWord σ_evm I := by
    have hne := sstoreAccountMap_storage_findD_ne σ_evm I.codeOwner ⟨2⟩ ⟨0⟩ ⟨0⟩
      (by decide)
    simpa [σ1, rawLengthHeaderWord] using hne
  have hrawFlag1 : UInt256.land (rawLengthHeaderWord σ1 I) ⟨1⟩ ≠ ⟨0⟩ := by
    simpa [hraw1] using hrawFlag
  have hrawBad1 : UInt256.sub (UInt256.land (rawLengthHeaderWord σ1 I) ⟨1⟩)
      (UInt256.lt (UInt256.div (rawLengthHeaderWord σ1 I) ⟨2⟩) ⟨32⟩) =
        ⟨0⟩ := by
    simpa [hraw1] using hrawBad
  have hrev := stringStoreX_clearAllRawLongMalformed
    (g := Sat256.ofUInt256 g) (τ := σ1) h1 hrawFlag1 hrawBad1
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ ⟨0⟩
  have hcurrentSolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ = ⟨0⟩ := by
    have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
      simpa [currentLengthHeaderWord] using hword.symm
    have hload' :
        Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
          currentLengthHeaderWord σ_evm I := by
      simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
        Account.lookupStorage, currentLengthHeaderWord, hslot]
    simpa [hcurrent] using hload'
  have hrawSolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ =
        rawLengthHeaderWord σ_evm I := by
    have hword := rawLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) := by
      simpa [rawLengthHeaderWord] using hword.symm
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, rawLengthHeaderWord, hslot]
  have hdelCurrent :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evmSolm0 currentRef = .ok evmSolm1 := by
    have hloc := storageLocLoad_bytesLikeLengthLoc_zero (base := ⟨0⟩) hcurrentSolm
    simpa [evmSolm1] using deleteCurrentShortZero hcurrentSolm hloc
  have henv1 : evmSolm1.executionEnv = evmSolm0.executionEnv := by
    simp [evmSolm1, storageStore_executionEnv]
  have hrawSolm1 :
      Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨2⟩ =
        rawLengthHeaderWord σ_evm I := by
    simp only [evmSolm1, storageStore_executionEnv]
    have hne := sstoreAccountMap_storage_findD_ne evmSolm0.accountMap
      evmSolm0.executionEnv.codeOwner ⟨2⟩ ⟨0⟩ ⟨0⟩ (by decide)
    unfold Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
    rw [storageStore_accountMap]
    simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using
      hne.trans hrawSolm
  have hdelRaw :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evmSolm1 rawRef = .revert := by
    simpa [henv1] using
      deleteRawMalformedLong (evm := evmSolm1)
        hrawSolm1 hrawFlag hrawBad
  have hbody :
      ExecTransitionBody stringStoreConfig stringStoreContract evmSolm0 ∅
        clearAllTransition.body .reverted :=
    clearAllBodyRevertsOfRawDelete
      (evm := evmSolm0) (evm₁ := evmSolm1)
      (by simp [evmSolm0, initState]; exact hwv) hdelCurrent hdelRaw
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem stringStoreClearAllCurrentShortRawShortMalformedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g currentLen : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcurrentFlag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hcurrentLen :
      currentLen =
        UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
    (hcurrentValid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt currentLen ⟨32⟩) ≠ ⟨0⟩)
    (hrawFlag : UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hrawBad : UInt256.sub (UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := clearAllSelector_size hsel
  have hd := stringStoreDispatch_clearAll (cd := I.calldata) hsel'
  have hdec := stringStoreDecode_clearAll (I := I) hsz
  let σ1 := sstoreAccountMap I.codeOwner σ_evm ⟨0⟩ ⟨0⟩
  have hreach := stringStoreReachClearAll (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv (clearAllSelector_size hsel) hsize hsel
  have h1 := stringStoreX_clearAllDeleteCurrentShortValid
    (g := Sat256.ofUInt256 g) (len := currentLen)
    hperm hreach hcurrentFlag hcurrentLen hcurrentValid
  have hraw1 : rawLengthHeaderWord σ1 I = rawLengthHeaderWord σ_evm I := by
    have hne := sstoreAccountMap_storage_findD_ne σ_evm I.codeOwner ⟨2⟩ ⟨0⟩ ⟨0⟩
      (by decide)
    simpa [σ1, rawLengthHeaderWord] using hne
  have hrawFlag1 : UInt256.land (rawLengthHeaderWord σ1 I) ⟨1⟩ = ⟨0⟩ := by
    simpa [hraw1] using hrawFlag
  have hrawBad1 : UInt256.sub (UInt256.land (rawLengthHeaderWord σ1 I) ⟨1⟩)
      (UInt256.lt
        (UInt256.land (UInt256.div (rawLengthHeaderWord σ1 I) ⟨2⟩) ⟨127⟩)
        ⟨32⟩) = ⟨0⟩ := by
    simpa [hraw1] using hrawBad
  have hrev := stringStoreX_clearAllRawShortMalformed
    (g := Sat256.ofUInt256 g) (τ := σ1) h1 hrawFlag1 hrawBad1
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ ⟨0⟩
  have hcurrentSolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        currentLengthHeaderWord σ_evm I := by
    have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
      simpa [currentLengthHeaderWord] using hword.symm
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, currentLengthHeaderWord, hslot]
  have hrawSolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ =
        rawLengthHeaderWord σ_evm I := by
    have hword := rawLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) := by
      simpa [rawLengthHeaderWord] using hword.symm
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, rawLengthHeaderWord, hslot]
  have hdelCurrent :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evmSolm0 currentRef = .ok evmSolm1 := by
    have hpacked : checkBytesPacked ⟨0⟩ evmSolm0 = true :=
      checkBytesPacked_of_storageLoad_land_one_zero hcurrentSolm hcurrentFlag
    simpa [evmSolm1] using
      deleteCurrentShortPacked hcurrentSolm hpacked hcurrentFlag hcurrentLen hcurrentValid
  have henv1 : evmSolm1.executionEnv = evmSolm0.executionEnv := by
    simp [evmSolm1, storageStore_executionEnv]
  have hrawSolm1 :
      Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨2⟩ =
        rawLengthHeaderWord σ_evm I := by
    simp only [evmSolm1, storageStore_executionEnv]
    have hne := sstoreAccountMap_storage_findD_ne evmSolm0.accountMap
      evmSolm0.executionEnv.codeOwner ⟨2⟩ ⟨0⟩ ⟨0⟩ (by decide)
    unfold Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
    rw [storageStore_accountMap]
    simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using
      hne.trans hrawSolm
  have hdelRaw :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evmSolm1 rawRef = .revert := by
    simpa [henv1] using
      deleteRawMalformedShort (evm := evmSolm1)
        hrawSolm1 hrawFlag hrawBad
  have hbody :
      ExecTransitionBody stringStoreConfig stringStoreContract evmSolm0 ∅
        clearAllTransition.body .reverted :=
    clearAllBodyRevertsOfRawDelete
      (evm := evmSolm0) (evm₁ := evmSolm1)
      (by simp [evmSolm0, initState]; exact hwv) hdelCurrent hdelRaw
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem stringStoreClearAllCurrentShortRawLongMalformedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g currentLen : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcurrentFlag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hcurrentLen :
      currentLen =
        UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
    (hcurrentValid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt currentLen ⟨32⟩) ≠ ⟨0⟩)
    (hrawFlag : UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hrawBad : UInt256.sub (UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) =
          ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := clearAllSelector_size hsel
  have hd := stringStoreDispatch_clearAll (cd := I.calldata) hsel'
  have hdec := stringStoreDecode_clearAll (I := I) hsz
  let σ1 := sstoreAccountMap I.codeOwner σ_evm ⟨0⟩ ⟨0⟩
  have hreach := stringStoreReachClearAll (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv (clearAllSelector_size hsel) hsize hsel
  have h1 := stringStoreX_clearAllDeleteCurrentShortValid
    (g := Sat256.ofUInt256 g) (len := currentLen)
    hperm hreach hcurrentFlag hcurrentLen hcurrentValid
  have hraw1 : rawLengthHeaderWord σ1 I = rawLengthHeaderWord σ_evm I := by
    have hne := sstoreAccountMap_storage_findD_ne σ_evm I.codeOwner ⟨2⟩ ⟨0⟩ ⟨0⟩
      (by decide)
    simpa [σ1, rawLengthHeaderWord] using hne
  have hrawFlag1 : UInt256.land (rawLengthHeaderWord σ1 I) ⟨1⟩ ≠ ⟨0⟩ := by
    simpa [hraw1] using hrawFlag
  have hrawBad1 : UInt256.sub (UInt256.land (rawLengthHeaderWord σ1 I) ⟨1⟩)
      (UInt256.lt (UInt256.div (rawLengthHeaderWord σ1 I) ⟨2⟩) ⟨32⟩) =
        ⟨0⟩ := by
    simpa [hraw1] using hrawBad
  have hrev := stringStoreX_clearAllRawLongMalformed
    (g := Sat256.ofUInt256 g) (τ := σ1) h1 hrawFlag1 hrawBad1
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ ⟨0⟩
  have hcurrentSolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        currentLengthHeaderWord σ_evm I := by
    have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
      simpa [currentLengthHeaderWord] using hword.symm
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, currentLengthHeaderWord, hslot]
  have hrawSolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ =
        rawLengthHeaderWord σ_evm I := by
    have hword := rawLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) := by
      simpa [rawLengthHeaderWord] using hword.symm
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, rawLengthHeaderWord, hslot]
  have hdelCurrent :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evmSolm0 currentRef = .ok evmSolm1 := by
    have hpacked : checkBytesPacked ⟨0⟩ evmSolm0 = true :=
      checkBytesPacked_of_storageLoad_land_one_zero hcurrentSolm hcurrentFlag
    simpa [evmSolm1] using
      deleteCurrentShortPacked hcurrentSolm hpacked hcurrentFlag hcurrentLen hcurrentValid
  have henv1 : evmSolm1.executionEnv = evmSolm0.executionEnv := by
    simp [evmSolm1, storageStore_executionEnv]
  have hrawSolm1 :
      Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨2⟩ =
        rawLengthHeaderWord σ_evm I := by
    simp only [evmSolm1, storageStore_executionEnv]
    have hne := sstoreAccountMap_storage_findD_ne evmSolm0.accountMap
      evmSolm0.executionEnv.codeOwner ⟨2⟩ ⟨0⟩ ⟨0⟩ (by decide)
    unfold Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
    rw [storageStore_accountMap]
    simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using
      hne.trans hrawSolm
  have hdelRaw :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evmSolm1 rawRef = .revert := by
    simpa [henv1] using
      deleteRawMalformedLong (evm := evmSolm1)
        hrawSolm1 hrawFlag hrawBad
  have hbody :
      ExecTransitionBody stringStoreConfig stringStoreContract evmSolm0 ∅
        clearAllTransition.body .reverted :=
    clearAllBodyRevertsOfRawDelete
      (evm := evmSolm0) (evm₁ := evmSolm1)
      (by simp [evmSolm0, initState]; exact hwv) hdelCurrent hdelRaw
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem stringStoreClearAllCurrentLongRawShortMalformedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g currentLen : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcurrentFlag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hcurrentValid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt currentLen ⟨32⟩) ≠ ⟨0⟩)
    (hcurrentLen : currentLen = UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩)
    (hrawFlag : UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hrawBad : UInt256.sub (UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hcurrentGt31 : UInt256.lt ⟨31⟩ currentLen ≠ ⟨0⟩ :=
    clearCurrentLongValid_gt31
      (header := currentLengthHeaderWord σ_evm I) (len := currentLen)
      hcurrentFlag hcurrentValid
  have hcurrentLenLt : currentLen.toNat < 2 ^ 255 :=
    clearCurrent_len_toNat_lt_sign_of_div2
      (header := currentLengthHeaderWord σ_evm I) (len := currentLen) hcurrentLen
  have hcurrentCountNat :
      (UInt256.div ((⟨31⟩ : UInt256) + currentLen) ⟨32⟩).toNat =
        (currentLen.toNat + 31) / 32 := by
    have hadd : (((⟨31⟩ : UInt256) + currentLen).toNat = 31 + currentLen.toNat) := by
      rw [uadd_toNat, show (⟨31⟩ : UInt256).toNat = 31 from by decide]
      rw [Nat.add_comm 31 currentLen.toNat]
      exact Nat.mod_eq_of_lt (by
        have hsize : (2 : Nat) ^ 255 + 31 < UInt256.size := by
          norm_num [UInt256.size]
        nlinarith)
    rw [udiv_toNat, hadd, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
    rw [Nat.add_comm 31 currentLen.toNat]
  have hsel' : ((⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := clearAllSelector_size hsel
  have hd := stringStoreDispatch_clearAll (cd := I.calldata) hsel'
  have hdec := stringStoreDecode_clearAll (I := I) hsz
  let currentCount := UInt256.div ((⟨31⟩ : UInt256) + currentLen) ⟨32⟩
  let σ1 := clearDataWordsForwardFrom I.codeOwner
    (sstoreAccountMap I.codeOwner σ_evm ⟨0⟩ ⟨0⟩) clearCurrentBaseWord ⟨0⟩ currentCount.toNat
  have hreach := stringStoreReachClearAll (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv (clearAllSelector_size hsel) hsize hsel
  have h1 := stringStoreX_clearAllDeleteCurrentLongValid
    (g := Sat256.ofUInt256 g) (len := currentLen)
    hperm hreach hcurrentFlag
    (by simpa [← hcurrentLen] using hcurrentValid) hcurrentLen hcurrentGt31
  have hrawAfterSlot0 :
      rawLengthHeaderWord (sstoreAccountMap I.codeOwner σ_evm ⟨0⟩ ⟨0⟩) I =
        rawLengthHeaderWord σ_evm I := by
    have hne := sstoreAccountMap_storage_findD_ne σ_evm I.codeOwner ⟨2⟩ ⟨0⟩ ⟨0⟩
      (by decide)
    simpa [rawLengthHeaderWord] using hne
  have hraw1 : rawLengthHeaderWord σ1 I = rawLengthHeaderWord σ_evm I := by
    have hpres := clearDataWordsForwardFrom_storage_findD_ne
      (sstoreAccountMap I.codeOwner σ_evm ⟨0⟩ ⟨0⟩)
      I.codeOwner ⟨2⟩ clearCurrentBaseWord ⟨0⟩ currentCount.toNat
      (by
        intro i hi
        exact clearCurrentDataSlot_ne_rawLengthSlot (clearDataWordsLoopIndex ⟨0⟩ i))
    simpa [σ1, rawLengthHeaderWord] using hpres.trans hrawAfterSlot0
  have hrawFlag1 : UInt256.land (rawLengthHeaderWord σ1 I) ⟨1⟩ = ⟨0⟩ := by
    simpa [hraw1] using hrawFlag
  have hrawBad1 : UInt256.sub (UInt256.land (rawLengthHeaderWord σ1 I) ⟨1⟩)
      (UInt256.lt
        (UInt256.land (UInt256.div (rawLengthHeaderWord σ1 I) ⟨2⟩) ⟨127⟩)
        ⟨32⟩) = ⟨0⟩ := by
    simpa [hraw1] using hrawBad
  have hrev := stringStoreX_clearAllRawShortMalformedFromCurrentBaseMem
    (g := Sat256.ofUInt256 g) (τ := σ1)
    (by simpa [σ1, currentCount] using h1) hrawFlag1 hrawBad1
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1Len := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ ⟨0⟩
  let evmSolm1 := clearSolidityBytesDataWordsFrom evmSolm1Len ⟨0⟩ 0
    ((currentLen.toNat + 31) / 32)
  have hcurrentSolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        currentLengthHeaderWord σ_evm I := by
    have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
      simpa [currentLengthHeaderWord] using hword.symm
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, currentLengthHeaderWord, hslot]
  have hrawSolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ =
        rawLengthHeaderWord σ_evm I := by
    have hword := rawLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) := by
      simpa [rawLengthHeaderWord] using hword.symm
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, rawLengthHeaderWord, hslot]
  have hdelCurrent :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evmSolm0 currentRef = .ok evmSolm1 := by
    simpa [evmSolm0, evmSolm1Len, evmSolm1, hcurrentLen] using
      deleteCurrentLongPrepared
        (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (header := currentLengthHeaderWord σ_evm I) (len := currentLen)
        hcurrentSolm hcurrentFlag hcurrentLen hcurrentValid
  have hrawSolm1 :
      Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨2⟩ =
        rawLengthHeaderWord σ_evm I := by
    simpa [evmSolm1, evmSolm1Len] using
      (clearSolidityCurrentDataWords_preserves_rawLoad evmSolm1Len
        ((currentLen.toNat + 31) / 32)).trans (by
          simp only [evmSolm1Len, storageStore_executionEnv]
          have hne := sstoreAccountMap_storage_findD_ne evmSolm0.accountMap
            evmSolm0.executionEnv.codeOwner ⟨2⟩ ⟨0⟩ ⟨0⟩ (by decide)
          unfold Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
          rw [storageStore_accountMap]
          simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using
            hne.trans hrawSolm)
  have hdelRaw :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evmSolm1 rawRef = .revert := by
    exact deleteRawMalformedShort (evm := evmSolm1)
      hrawSolm1 hrawFlag hrawBad
  have hbody :
      ExecTransitionBody stringStoreConfig stringStoreContract evmSolm0 ∅
        clearAllTransition.body .reverted :=
    clearAllBodyRevertsOfRawDelete
      (evm := evmSolm0) (evm₁ := evmSolm1)
      (by simp [evmSolm0, initState]; exact hwv) hdelCurrent hdelRaw
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem stringStoreClearAllCurrentLongRawLongMalformedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g currentLen : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcurrentFlag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hcurrentValid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt currentLen ⟨32⟩) ≠ ⟨0⟩)
    (hcurrentLen : currentLen = UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩)
    (hrawFlag : UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hrawBad : UInt256.sub (UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) =
          ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hcurrentGt31 : UInt256.lt ⟨31⟩ currentLen ≠ ⟨0⟩ :=
    clearCurrentLongValid_gt31
      (header := currentLengthHeaderWord σ_evm I) (len := currentLen)
      hcurrentFlag hcurrentValid
  have hcurrentLenLt : currentLen.toNat < 2 ^ 255 :=
    clearCurrent_len_toNat_lt_sign_of_div2
      (header := currentLengthHeaderWord σ_evm I) (len := currentLen) hcurrentLen
  have hcurrentCountNat :
      (UInt256.div ((⟨31⟩ : UInt256) + currentLen) ⟨32⟩).toNat =
        (currentLen.toNat + 31) / 32 := by
    have hadd : (((⟨31⟩ : UInt256) + currentLen).toNat = 31 + currentLen.toNat) := by
      rw [uadd_toNat, show (⟨31⟩ : UInt256).toNat = 31 from by decide]
      rw [Nat.add_comm 31 currentLen.toNat]
      exact Nat.mod_eq_of_lt (by
        have hsize : (2 : Nat) ^ 255 + 31 < UInt256.size := by
          norm_num [UInt256.size]
        nlinarith)
    rw [udiv_toNat, hadd, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
    rw [Nat.add_comm 31 currentLen.toNat]
  have hsel' : ((⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := clearAllSelector_size hsel
  have hd := stringStoreDispatch_clearAll (cd := I.calldata) hsel'
  have hdec := stringStoreDecode_clearAll (I := I) hsz
  let currentCount := UInt256.div ((⟨31⟩ : UInt256) + currentLen) ⟨32⟩
  let σ1 := clearDataWordsForwardFrom I.codeOwner
    (sstoreAccountMap I.codeOwner σ_evm ⟨0⟩ ⟨0⟩) clearCurrentBaseWord ⟨0⟩ currentCount.toNat
  have hreach := stringStoreReachClearAll (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv (clearAllSelector_size hsel) hsize hsel
  have h1 := stringStoreX_clearAllDeleteCurrentLongValid
    (g := Sat256.ofUInt256 g) (len := currentLen)
    hperm hreach hcurrentFlag
    (by simpa [← hcurrentLen] using hcurrentValid) hcurrentLen hcurrentGt31
  have hrawAfterSlot0 :
      rawLengthHeaderWord (sstoreAccountMap I.codeOwner σ_evm ⟨0⟩ ⟨0⟩) I =
        rawLengthHeaderWord σ_evm I := by
    have hne := sstoreAccountMap_storage_findD_ne σ_evm I.codeOwner ⟨2⟩ ⟨0⟩ ⟨0⟩
      (by decide)
    simpa [rawLengthHeaderWord] using hne
  have hraw1 : rawLengthHeaderWord σ1 I = rawLengthHeaderWord σ_evm I := by
    have hpres := clearDataWordsForwardFrom_storage_findD_ne
      (sstoreAccountMap I.codeOwner σ_evm ⟨0⟩ ⟨0⟩)
      I.codeOwner ⟨2⟩ clearCurrentBaseWord ⟨0⟩ currentCount.toNat
      (by
        intro i hi
        exact clearCurrentDataSlot_ne_rawLengthSlot (clearDataWordsLoopIndex ⟨0⟩ i))
    simpa [σ1, rawLengthHeaderWord] using hpres.trans hrawAfterSlot0
  have hrawFlag1 : UInt256.land (rawLengthHeaderWord σ1 I) ⟨1⟩ ≠ ⟨0⟩ := by
    simpa [hraw1] using hrawFlag
  have hrawBad1 : UInt256.sub (UInt256.land (rawLengthHeaderWord σ1 I) ⟨1⟩)
      (UInt256.lt (UInt256.div (rawLengthHeaderWord σ1 I) ⟨2⟩) ⟨32⟩) =
        ⟨0⟩ := by
    simpa [hraw1] using hrawBad
  have hrev := stringStoreX_clearAllRawLongMalformedFromCurrentBaseMem
    (g := Sat256.ofUInt256 g) (τ := σ1)
    (by simpa [σ1, currentCount] using h1) hrawFlag1 hrawBad1
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1Len := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ ⟨0⟩
  let evmSolm1 := clearSolidityBytesDataWordsFrom evmSolm1Len ⟨0⟩ 0
    ((currentLen.toNat + 31) / 32)
  have hcurrentSolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        currentLengthHeaderWord σ_evm I := by
    have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
      simpa [currentLengthHeaderWord] using hword.symm
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, currentLengthHeaderWord, hslot]
  have hrawSolm :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ =
        rawLengthHeaderWord σ_evm I := by
    have hword := rawLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) := by
      simpa [rawLengthHeaderWord] using hword.symm
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, rawLengthHeaderWord, hslot]
  have hdelCurrent :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evmSolm0 currentRef = .ok evmSolm1 := by
    simpa [evmSolm0, evmSolm1Len, evmSolm1, hcurrentLen] using
      deleteCurrentLongPrepared
        (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (header := currentLengthHeaderWord σ_evm I) (len := currentLen)
        hcurrentSolm hcurrentFlag hcurrentLen hcurrentValid
  have hrawSolm1 :
      Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨2⟩ =
        rawLengthHeaderWord σ_evm I := by
    simpa [evmSolm1, evmSolm1Len] using
      (clearSolidityCurrentDataWords_preserves_rawLoad evmSolm1Len
        ((currentLen.toNat + 31) / 32)).trans (by
          simp only [evmSolm1Len, storageStore_executionEnv]
          have hne := sstoreAccountMap_storage_findD_ne evmSolm0.accountMap
            evmSolm0.executionEnv.codeOwner ⟨2⟩ ⟨0⟩ ⟨0⟩ (by decide)
          unfold Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
          rw [storageStore_accountMap]
          simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using
            hne.trans hrawSolm)
  have hdelRaw :
      deleteStorage? stringStoreConfig { contract := stringStoreContract, locals := ∅ }
        evmSolm1 rawRef = .revert := by
    exact deleteRawMalformedLong (evm := evmSolm1)
      hrawSolm1 hrawFlag hrawBad
  have hbody :
      ExecTransitionBody stringStoreConfig stringStoreContract evmSolm0 ∅
        clearAllTransition.body .reverted :=
    clearAllBodyRevertsOfRawDelete
      (evm := evmSolm0) (evm₁ := evmSolm1)
      (by simp [evmSolm0, initState]; exact hwv) hdelCurrent hdelRaw
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

axiom stringStoreClearAllHistoryNonzeroRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hhistory : historyLengthWord σ_evm I ≠ ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I

theorem stringStoreClearAllRuntime_of_notAllZero
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xeb, 0xb6, 0x89, 0xa1]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hcurrent : currentLengthHeaderWord σ_evm I = ⟨0⟩
  · by_cases hraw : rawLengthHeaderWord σ_evm I = ⟨0⟩
    · by_cases hhistory : historyLengthWord σ_evm I = ⟨0⟩
      · exact stringStoreClearAllShortZeroRuntime
          hcode hsize hperm hwv hsel hAccounts hcurrent hraw hhistory
      · exact stringStoreClearAllHistoryNonzeroRuntime
          hcode hsize hperm hwv hsel hAccounts hhistory
    · by_cases hflagRaw : UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩
      · by_cases hvalidRaw :
          UInt256.sub (UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩)
            (UInt256.lt
              (UInt256.land (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
              ⟨32⟩) ≠ ⟨0⟩
        · by_cases hhistory : historyLengthWord σ_evm I = ⟨0⟩
          · exact stringStoreClearAllCurrentZeroRawShortHistoryZeroRuntime
              (len := UInt256.land
                (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
              hcode hsize hperm hwv hsel hAccounts hcurrent hflagRaw rfl hvalidRaw hhistory
          · exact stringStoreClearAllHistoryNonzeroRuntime
              hcode hsize hperm hwv hsel hAccounts hhistory
        · have hrawBad :
              UInt256.sub (UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩)
                (UInt256.lt
                  (UInt256.land (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
                  ⟨32⟩) = ⟨0⟩ := by
            by_contra hrawBad
            exact hvalidRaw hrawBad
          exact stringStoreClearAllCurrentZeroRawShortMalformedRuntime
            hcode hsize hperm hwv hsel hAccounts hcurrent hflagRaw hrawBad
      · by_cases hvalidRawLong :
          UInt256.sub (UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩)
            (UInt256.lt (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩
        · by_cases hhistory : historyLengthWord σ_evm I = ⟨0⟩
          · exact stringStoreClearAllCurrentZeroRawLongHistoryZeroRuntime
              (len := UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩)
              hcode hsize hperm hwv hsel hAccounts hcurrent hflagRaw rfl
              hvalidRawLong hhistory
          · exact stringStoreClearAllHistoryNonzeroRuntime
              hcode hsize hperm hwv hsel hAccounts hhistory
        · have hrawBad :
              UInt256.sub (UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩)
                (UInt256.lt (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) =
                  ⟨0⟩ := by
            by_contra hrawBad
            exact hvalidRawLong hrawBad
          exact stringStoreClearAllCurrentZeroRawLongMalformedRuntime
            hcode hsize hperm hwv hsel hAccounts hcurrent hflagRaw hrawBad
  · by_cases hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩
    · by_cases hvalid :
        UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt
            (UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩
      · by_cases hraw : rawLengthHeaderWord σ_evm I = ⟨0⟩
        · by_cases hhistory : historyLengthWord σ_evm I = ⟨0⟩
          · exact stringStoreClearAllCurrentShortRawHistoryZeroRuntime
              (len := UInt256.land
                (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
              hcode hsize hperm hwv hsel hAccounts hflag rfl hvalid hraw hhistory
          · exact stringStoreClearAllHistoryNonzeroRuntime
              hcode hsize hperm hwv hsel hAccounts hhistory
        · by_cases hflagRaw : UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩
          · by_cases hvalidRaw :
              UInt256.sub (UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩)
                (UInt256.lt
                  (UInt256.land (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩)
                    ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩
            · by_cases hhistory : historyLengthWord σ_evm I = ⟨0⟩
              · exact stringStoreClearAllCurrentShortRawShortHistoryZeroRuntime
                  (currentLen := UInt256.land
                    (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
                  (rawLen := UInt256.land
                    (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
                  hcode hsize hperm hwv hsel hAccounts hflag rfl hvalid
                  hflagRaw rfl hvalidRaw hhistory
              · exact stringStoreClearAllHistoryNonzeroRuntime
                  hcode hsize hperm hwv hsel hAccounts hhistory
            · have hrawBad :
                  UInt256.sub (UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩)
                    (UInt256.lt
                      (UInt256.land (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩)
                        ⟨127⟩) ⟨32⟩) = ⟨0⟩ := by
                by_contra hrawBad
                exact hvalidRaw hrawBad
              exact stringStoreClearAllCurrentShortRawShortMalformedRuntime
                (currentLen := UInt256.land
                  (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
                hcode hsize hperm hwv hsel hAccounts hflag rfl hvalid
                hflagRaw hrawBad
          · by_cases hvalidRawLong :
              UInt256.sub (UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩)
                (UInt256.lt (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠
                  ⟨0⟩
            · by_cases hhistory : historyLengthWord σ_evm I = ⟨0⟩
              · exact stringStoreClearAllCurrentShortRawLongHistoryZeroRuntime
                  (currentLen := UInt256.land
                    (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
                  (rawLen := UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩)
                  hcode hsize hperm hwv hsel hAccounts hflag rfl hvalid
                  hflagRaw rfl hvalidRawLong hhistory
              · exact stringStoreClearAllHistoryNonzeroRuntime
                  hcode hsize hperm hwv hsel hAccounts hhistory
            · have hrawBad :
                  UInt256.sub (UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩)
                    (UInt256.lt (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) =
                      ⟨0⟩ := by
                by_contra hrawBad
                exact hvalidRawLong hrawBad
              exact stringStoreClearAllCurrentShortRawLongMalformedRuntime
                (currentLen := UInt256.land
                  (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
                hcode hsize hperm hwv hsel hAccounts hflag rfl hvalid
                hflagRaw hrawBad
      · have hbad :
            UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
              (UInt256.lt
                (UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
                ⟨32⟩) = ⟨0⟩ := by
          by_contra hbad
          exact hvalid hbad
        exact stringStoreClearAllCurrentShortMalformedRuntime
          hcode hsize hperm hwv hsel hAccounts hflag hbad
    · by_cases hvalidLong :
        UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩
      · by_cases hraw : rawLengthHeaderWord σ_evm I = ⟨0⟩
        · by_cases hhistory : historyLengthWord σ_evm I = ⟨0⟩
          · exact stringStoreClearAllCurrentLongRawHistoryZeroRuntime
              hcode hsize hperm hwv hsel hAccounts hflag hvalidLong hraw hhistory
          · exact stringStoreClearAllHistoryNonzeroRuntime
              hcode hsize hperm hwv hsel hAccounts hhistory
        · by_cases hflagRaw : UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩
          · by_cases hvalidRaw :
              UInt256.sub (UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩)
                (UInt256.lt
                  (UInt256.land (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩)
                    ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩
            · by_cases hhistory : historyLengthWord σ_evm I = ⟨0⟩
              · exact stringStoreClearAllCurrentLongRawShortHistoryZeroRuntime
                  (currentLen := UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩)
                  (rawLen := UInt256.land
                    (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
                  hcode hsize hperm hwv hsel hAccounts hflag hvalidLong rfl
                  hflagRaw rfl hvalidRaw hhistory
              · exact stringStoreClearAllHistoryNonzeroRuntime
                  hcode hsize hperm hwv hsel hAccounts hhistory
            · have hrawBad :
                  UInt256.sub (UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩)
                    (UInt256.lt
                      (UInt256.land (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩)
                        ⟨127⟩) ⟨32⟩) = ⟨0⟩ := by
                by_contra hrawBad
                exact hvalidRaw hrawBad
              exact stringStoreClearAllCurrentLongRawShortMalformedRuntime
                (currentLen := UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩)
                hcode hsize hperm hwv hsel hAccounts hflag hvalidLong rfl
                hflagRaw hrawBad
          · by_cases hvalidRawLong :
              UInt256.sub (UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩)
                (UInt256.lt (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠
                  ⟨0⟩
            · by_cases hhistory : historyLengthWord σ_evm I = ⟨0⟩
              · exact stringStoreClearAllCurrentLongRawLongHistoryZeroRuntime
                  (currentLen := UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩)
                  (rawLen := UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩)
                  hcode hsize hperm hwv hsel hAccounts hflag hvalidLong rfl
                  hflagRaw rfl hvalidRawLong hhistory
              · exact stringStoreClearAllHistoryNonzeroRuntime
                  hcode hsize hperm hwv hsel hAccounts hhistory
            · have hrawBad :
                  UInt256.sub (UInt256.land (rawLengthHeaderWord σ_evm I) ⟨1⟩)
                    (UInt256.lt (UInt256.div (rawLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) =
                      ⟨0⟩ := by
                by_contra hrawBad
                exact hvalidRawLong hrawBad
              exact stringStoreClearAllCurrentLongRawLongMalformedRuntime
                (currentLen := UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩)
                hcode hsize hperm hwv hsel hAccounts hflag hvalidLong rfl
                hflagRaw hrawBad
      · have hbad :
            UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
              (UInt256.lt (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) =
                ⟨0⟩ := by
          by_contra hbad
          exact hvalidLong hbad
        exact stringStoreClearAllCurrentLongMalformedRuntime
          hcode hsize hperm hwv hsel hAccounts hflag hbad

end StringStore
