import Benchmarks.Dss.Clipper.GetFeedPrice

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

/-! ## Successful `getFeedPrice()` source path

The revert-only part of the routine lives in `GetFeedPrice.lean`.  This file starts
at the successful `pip.peek()` result and factors the continuation shared by
`kick` and `redo`.
-/

abbrev clipperSpotterParWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))

abbrev clipperSpotterParValues (out : ByteArray) : List Value :=
  [.int (Int.ofNat (clipperSpotterParWord out).toNat)]

theorem clipperSpotterParDecode_none_short {v : ClipperImmutables} {out : ByteArray}
    (hshort : out.size < 32) :
    (config v).externalABI.decode? "par" out = none := by
  simpa [config, externalABI, decodeReturn?, uint256, uint256Int, abiUInt256] using
    (decodeReturnValueWithMode_legacy_uint256_none_short
      (returndata := out) hshort)

theorem clipperSpotterParDecode_ok {v : ClipperImmutables} {out : ByteArray}
    (hlo : 32 ≤ out.size) :
    (config v).externalABI.decode? "par" out =
      some (clipperSpotterParValues out) := by
  have hword :
      (UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))).toNat =
        fromByteArrayBigEndian (out.extract 0 32) :=
    UInt256.toNat_ofNat_of_lt
      (fromByteArrayBigEndian_extract0_32_lt (returndata := out) hlo)
  simpa [config, externalABI, decodeReturn?, clipperSpotterParValues,
    clipperSpotterParWord, uint256, uint256Int, abiUInt256, hword] using
    (decodeReturnValueWithMode_legacy_uint256_ok
      (returndata := out) hlo)

abbrev clipperGetFeedPriceValBlnLocals (outIlks outPeek : ByteArray) : Store :=
  (clipperGetFeedPriceHasLocals outIlks outPeek).insert "valBln"
    (.int (Int.ofNat
      (UInt256.mul (clipperPipPeekValueWord outPeek) (⟨1000000000⟩ : UInt256)).toNat))

abbrev clipperGetFeedPriceParLocals
    (outIlks outPeek outPar : ByteArray) : Store :=
  (clipperGetFeedPriceValBlnLocals outIlks outPeek).insert "par"
    (collapseReturns (clipperSpotterParValues outPar))

abbrev clipperGetFeedPriceResultLocals
    (outIlks outPeek outPar : ByteArray) : Store :=
  (clipperGetFeedPriceParLocals outIlks outPeek outPar).insert "feedPrice"
    (.int (Int.ofNat
      (UInt256.div
        (UInt256.mul
          (UInt256.mul (clipperPipPeekValueWord outPeek) (⟨1000000000⟩ : UInt256))
          clipperRayWord)
        (clipperSpotterParWord outPar)).toNat))

theorem clipperEvalGetFeedPriceHas_true
    (v : ClipperImmutables) (evm : EVM.State) (outIlks outPeek : ByteArray)
    (hnz : clipperPipPeekHasWord outPeek ≠ ⟨0⟩) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperGetFeedPriceHasLocals outIlks outPeek } evm
      (.var "has") = .ok (.bool true) := by
  simp [clipperGetFeedPriceHasLocals, hnz, evalExpr?, EvalResult.ofOption]

theorem clipperEvalGetFeedPriceValCast
    (v : ClipperImmutables) (evm : EVM.State) (outIlks outPeek : ByteArray)
    (hlo : 32 ≤ outPeek.size) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperGetFeedPriceHasLocals outIlks outPeek } evm
      (.cast (.var "val") uint256St) =
      .ok (.int (Int.ofNat (clipperPipPeekValueWord outPeek).toNat)) := by
  let locals := clipperGetFeedPriceHasLocals outIlks outPeek
  have hval :
      evalExpr? (config v) { contract := contract v, locals := locals } evm
        (.var "val") =
          .ok (.fixedBytes abiBytes32Width (clipperPipPeekValueBytes outPeek)) := by
    simp only [locals, clipperGetFeedPriceHasLocals, evalExpr?]
    rw [store_get_ne _ _ (by decide), store_get_self]
    rfl
  have hword :
      ABI.bytesToWord (outPeek.toList.take 32) = clipperPipPeekValueWord outPeek := by
    simpa [clipperPipPeekValueWord] using
      (bytesToWord_take32_eq_extract0_32 (returndata := outPeek))
  have htakeLen : (outPeek.toList.take 32).length = 32 := by
    have hlist : outPeek.toList.length = outPeek.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [List.length_take, hlist]
    omega
  have hfromLt :
      fromBytesBigEndian (outPeek.toList.take 32) < UInt256.size := by
    unfold fromBytesBigEndian
    have hle := EVM.fromBytes'_le (bs := (outPeek.toList.take 32).reverse)
    rw [List.length_reverse, htakeLen] at hle
    simpa [UInt256.size] using hle
  have hwordNat :
      fromBytesBigEndian (outPeek.toList.take 32) =
        (clipperPipPeekValueWord outPeek).toNat := by
    have h := congrArg UInt256.toNat hword
    have hfromLtData :
        fromBytesBigEndian (List.take 32 outPeek.data.toList) < UInt256.size := by
      simpa [byteArray_toList_eq] using hfromLt
    unfold ABI.bytesToWord at h
    simpa [fromByteArrayBigEndian, byteArray_toList_eq,
      UInt256.toNat_ofNat_of_lt hfromLtData] using h
  have hlen : min 32 outPeek.toList.length = fixedBytesSize abiBytes32Width := by
    rw [byteArray_toList_eq, Array.length_toList]
    simp [fixedBytesSize, abiBytes32Width]
    omega
  change evalExpr? (config v) { contract := contract v, locals := locals } evm
    (.cast (.var "val") uint256St) =
      .ok (.int (Int.ofNat (clipperPipPeekValueWord outPeek).toNat))
  simp [evalExpr?, EvalResult.bind, bind, hval, castValue?, fixedBytesToNat?,
    fixedBytesValid, abiBytes32Width, uint256St, uint256Int,
    clipperPipPeekValueBytes, hwordNat, hlen]
  rfl

theorem clipperEvalGetFeedPriceValBlnArgs
    (v : ClipperImmutables) (evm : EVM.State) (outIlks outPeek : ByteArray)
    (hlo : 32 ≤ outPeek.size) :
    evalExprs? (config v)
      { contract := contract v,
        locals := clipperGetFeedPriceHasLocals outIlks outPeek } evm
      [.cast (.var "val") uint256St, .intLit BLN] =
      .ok [.int (Int.ofNat (clipperPipPeekValueWord outPeek).toNat),
        .int (Int.ofNat (⟨1000000000⟩ : UInt256).toNat)] := by
  have hBLN : BLN = Int.ofNat (⟨1000000000⟩ : UInt256).toNat := by native_decide
  simp [evalExprs?, clipperEvalGetFeedPriceValCast v evm outIlks outPeek hlo,
    evalExpr?, hBLN, pure, EvalResult.bind, bind]

theorem clipperEvalGetFeedPriceValBlnMul_ok
    (v : ClipperImmutables) (evm : EVM.State) (outIlks outPeek : ByteArray)
    (hlo : 32 ≤ outPeek.size)
    (hmul :
      (clipperPipPeekValueWord outPeek).toNat *
          (⟨1000000000⟩ : UInt256).toNat < UInt256.size) :
    evalExpr? (config v)
      (Frame.mk (contract v) (clipperGetFeedPriceHasLocals outIlks outPeek)) evm
      (mul256 (.cast (.var "val") uint256St) (.intLit BLN)) =
      .ok (.int (Int.ofNat
        (UInt256.mul (clipperPipPeekValueWord outPeek) ⟨1000000000⟩).toNat)) := by
  let x := clipperPipPeekValueWord outPeek
  let y : UInt256 := ⟨1000000000⟩
  have hcast := clipperEvalGetFeedPriceValCast v evm outIlks outPeek hlo
  have hy : BLN = Int.ofNat y.toNat := by native_decide
  have hlt : ¬ Int.ofNat (x.toNat * y.toNat) ≥ (2 : Int) ^ 256 :=
    not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size, x, y] using hmul))
  have hword : (UInt256.mul x y).toNat = x.toNat * y.toNat := by
    rw [u256_mul_toNat, Nat.mod_eq_of_lt]
    simpa [x, y] using hmul
  simp [mul256, u256, evalExpr?, EvalResult.bind, bind, hcast, hy,
    evalBinaryOp?, uint256Int, x, y, hword]
  rw [if_neg]
  · rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_lt.mpr (Int.natCast_nonneg _)) hbad
    · exact hlt hbad

theorem clipperEvalGetFeedPriceValBlnMul_revert
    (v : ClipperImmutables) (evm : EVM.State) (outIlks outPeek : ByteArray)
    (hlo : 32 ≤ outPeek.size)
    (hover : UInt256.size ≤
      (clipperPipPeekValueWord outPeek).toNat *
        (⟨1000000000⟩ : UInt256).toNat) :
    evalExpr? (config v)
      (Frame.mk (contract v) (clipperGetFeedPriceHasLocals outIlks outPeek)) evm
      (mul256 (.cast (.var "val") uint256St) (.intLit BLN)) = .revert := by
  have hcast := clipperEvalGetFeedPriceValCast v evm outIlks outPeek hlo
  have hBLN : BLN = Int.ofNat (⟨1000000000⟩ : UInt256).toNat := by native_decide
  simp [mul256, u256, evalExpr?, EvalResult.bind, bind, hcast, hBLN,
    evalBinaryOp?, uint256Int]
  intro _
  exact_mod_cast hover

theorem clipperEvalGetFeedPriceValBlnRequire_true
    (v : ClipperImmutables) (evm : EVM.State) (outIlks outPeek : ByteArray)
    (hlo : 32 ≤ outPeek.size)
    (hmul :
      (clipperPipPeekValueWord outPeek).toNat *
          (⟨1000000000⟩ : UInt256).toNat < UInt256.size) :
    evalExpr? (config v)
      (Frame.mk (contract v) (clipperGetFeedPriceValBlnLocals outIlks outPeek)) evm
      (.binary .or
        (.binary .eq (.intLit BLN) (.intLit 0))
        (.binary .eq
          (.binary .div (.var "valBln") (.intLit BLN))
          (.cast (.var "val") uint256St))) = .ok (.bool true) := by
  let x := clipperPipPeekValueWord outPeek
  let y : UInt256 := ⟨1000000000⟩
  have hy : BLN = Int.ofNat y.toNat := by native_decide
  have hy0 : y.toNat ≠ 0 := by native_decide
  have hdiv :
      Int.ofNat (UInt256.mul x y).toNat / Int.ofNat y.toNat = Int.ofNat x.toNat := by
    have hcancel := Reasoning.Theory.clipperMulDiv_cancel (x := y) (y := x)
      (by native_decide) (by simpa [x, y, Nat.mul_comm] using hmul)
    have hnat := congrArg UInt256.toNat hcancel
    rw [udiv_toNat, u256_mul_comm y x] at hnat
    exact (Int.ofNat_ediv_ofNat (a := (UInt256.mul x y).toNat) (b := y.toNat)).trans
      (congrArg Int.ofNat hnat)
  have hval :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperGetFeedPriceValBlnLocals outIlks outPeek)) evm
        (.cast (.var "val") uint256St) = .ok (.int (Int.ofNat x.toNat)) := by
    have hlookup :
        (clipperGetFeedPriceValBlnLocals outIlks outPeek).get? "val" =
          (clipperGetFeedPriceHasLocals outIlks outPeek).get? "val" := by
      exact store_get_ne
        (clipperGetFeedPriceHasLocals outIlks outPeek)
        (.int (Int.ofNat
          (UInt256.mul (clipperPipPeekValueWord outPeek) ⟨1000000000⟩).toNat))
        (k := "valBln") (a := "val") (by decide)
    simpa only [evalExpr?, hlookup, x] using
      clipperEvalGetFeedPriceValCast v evm outIlks outPeek hlo
  have hvalBln :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperGetFeedPriceValBlnLocals outIlks outPeek)) evm
        (.var "valBln") = .ok (.int (Int.ofNat (UInt256.mul x y).toNat)) := by
    simp only [evalExpr?, clipperGetFeedPriceValBlnLocals, store_get_self, x, y]
    rfl
  have hyInt : Int.ofNat y.toNat ≠ 0 := by
    intro hzero
    exact hy0 (Int.ofNat.inj hzero)
  have hleft :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperGetFeedPriceValBlnLocals outIlks outPeek)) evm
        (.binary .eq (.intLit BLN) (.intLit 0)) = .ok (.bool false) := by
    simp [evalExpr?, EvalResult.bind, bind, evalBinaryOp?, hy, hy0, y]
  have hright :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperGetFeedPriceValBlnLocals outIlks outPeek)) evm
        (.binary .eq
          (.binary .div (.var "valBln") (.intLit BLN))
          (.cast (.var "val") uint256St)) = .ok (.bool true) := by
    simp only [evalExpr?, hvalBln, hval, EvalResult.bind, bind, evalBinaryOp?, hy]
    rw [if_neg hyInt, hdiv]
    simp
  simp [evalExpr?, EvalResult.bind, bind, pure, hleft, hright]

theorem clipperGetFeedPriceValBlnMulSuccessBlock
    (v : ClipperImmutables) (evm : EVM.State) (outIlks outPeek : ByteArray)
    (hlo : 32 ≤ outPeek.size)
    (hmul :
      (clipperPipPeekValueWord outPeek).toNat *
          (⟨1000000000⟩ : UInt256).toNat < UInt256.size) :
    ExecBlock (config v)
      (Frame.mk (contract v) (clipperGetFeedPriceHasLocals outIlks outPeek)) evm
      (checkedMulUintInto "valBln" (.cast (.var "val") uint256St) (.intLit BLN))
      (.ok
        (Frame.mk (contract v) (clipperGetFeedPriceValBlnLocals outIlks outPeek)) evm) := by
  have hlet :
      ExecStmt (config v)
        (Frame.mk (contract v) (clipperGetFeedPriceHasLocals outIlks outPeek)) evm
        (.letDecl "valBln" (some uint256)
          (mul256 (.cast (.var "val") uint256St) (.intLit BLN)))
        (.ok
          (Frame.mk (contract v) (clipperGetFeedPriceValBlnLocals outIlks outPeek)) evm) := by
    simpa [clipperGetFeedPriceValBlnLocals] using
      ExecStmt.letDecl
        (clipperEvalGetFeedPriceValBlnMul_ok v evm outIlks outPeek hlo hmul)
  simpa [checkedMulUintInto] using
    (ExecBlock.consNormal hlet
      (ExecBlock.consNormal
        (ExecStmt.requireTrue
          (clipperEvalGetFeedPriceValBlnRequire_true v evm outIlks outPeek hlo hmul))
        ExecBlock.nil))

theorem clipperGetFeedPriceValBlnMulRevertBlock
    (v : ClipperImmutables) (evm : EVM.State) (outIlks outPeek : ByteArray)
    (hlo : 32 ≤ outPeek.size)
    (hover : UInt256.size ≤
      (clipperPipPeekValueWord outPeek).toNat *
        (⟨1000000000⟩ : UInt256).toNat) :
    ExecBlock (config v)
      (Frame.mk (contract v) (clipperGetFeedPriceHasLocals outIlks outPeek)) evm
      (checkedMulUintInto "valBln" (.cast (.var "val") uint256St) (.intLit BLN))
      .reverted := by
  simpa [checkedMulUintInto] using
    ExecBlock.consRevert
      (ExecStmt.letDeclRevert
        (clipperEvalGetFeedPriceValBlnMul_revert v evm outIlks outPeek hlo hover))

theorem clipperGetFeedPriceValBlnLocals_get_spotter
    (outIlks outPeek : ByteArray) :
    (clipperGetFeedPriceValBlnLocals outIlks outPeek).get? "spotter" = none := by
  simp [clipperGetFeedPriceValBlnLocals, clipperGetFeedPriceHasLocals,
    clipperGetFeedPriceValLocals, clipperGetFeedPricePeekLocals,
    clipperGetFeedPricePipLocals, clipperGetFeedPriceSpotterIlkLocals]

theorem clipperGetFeedPriceParNoCode
    (v : ClipperImmutables) (evm : EVM.State) (outIlks outPeek : ByteArray)
    (hnoCode :
      (UInt256.ofNat ((evm.lookupAccount (clipperGetFeedPriceSpotterAddress evm)).option 0
        (fun acc => acc.code.size))).toNat = 0) :
    ExecBlock (config v)
      (Frame.mk (contract v) (clipperGetFeedPriceValBlnLocals outIlks outPeek)) evm
      (checkedExternalCallStmts (.storage spotterRef) "par" (.intLit 0) [] "par")
      .reverted := by
  simpa [checkedExternalCallStmts] using
    checkedExternalCallNoCode
      (cfg := config v) (C := contract v) (evm := evm)
      (locals := clipperGetFeedPriceValBlnLocals outIlks outPeek)
      (receiver := .storage spotterRef) (retVar := "par") (name := "par")
      (sendVal := 0) (args := []) (perm := true)
      (clipperEvalGetFeedPriceSpotterCodeGuard_false v evm
        (clipperGetFeedPriceValBlnLocals outIlks outPeek)
        (clipperGetFeedPriceValBlnLocals_get_spotter outIlks outPeek) hnoCode)

theorem clipperGetFeedPriceParCallFailure
    (v : ClipperImmutables) {evm evmPar : EVM.State}
    (outIlks outPeek : ByteArray) {outPar : ByteArray}
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperGetFeedPriceSpotterAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm
        (EVM.address (clipperGetFeedPriceSpotterAddress evm)) "par" 0 []
        (false, evmPar, outPar) true) :
    ExecBlock (config v)
      (Frame.mk (contract v) (clipperGetFeedPriceValBlnLocals outIlks outPeek)) evm
      (checkedExternalCallStmts (.storage spotterRef) "par" (.intLit 0) [] "par")
      .reverted := by
  simpa [checkedExternalCallStmts] using
    checkedExternalCallFailure
      (cfg := config v) (C := contract v) (evm := evm) (evm' := evmPar)
      (locals := clipperGetFeedPriceValBlnLocals outIlks outPeek)
      (receiver := .storage spotterRef) (retVar := "par") (name := "par")
      (target := clipperGetFeedPriceSpotterAddress evm)
      (sendVal := 0) (args := []) (argVals := []) (out := outPar) (perm := true)
      (clipperEvalGetFeedPriceSpotterCodeGuard_true v evm
        (clipperGetFeedPriceValBlnLocals outIlks outPeek)
        (clipperGetFeedPriceValBlnLocals_get_spotter outIlks outPeek) hcode)
      (clipperEvalGetFeedPriceSpotterTarget v evm
        (clipperGetFeedPriceValBlnLocals outIlks outPeek)
        (clipperGetFeedPriceValBlnLocals_get_spotter outIlks outPeek))
      (by rfl) hcall

theorem clipperGetFeedPriceParDecodeRevert
    (v : ClipperImmutables) {evm evmPar : EVM.State}
    (outIlks outPeek : ByteArray) {outPar : ByteArray}
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperGetFeedPriceSpotterAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm
        (EVM.address (clipperGetFeedPriceSpotterAddress evm)) "par" 0 []
        (true, evmPar, outPar) true)
    (hdec : (config v).externalABI.decode? "par" outPar = none) :
    ExecBlock (config v)
      (Frame.mk (contract v) (clipperGetFeedPriceValBlnLocals outIlks outPeek)) evm
      (checkedExternalCallStmts (.storage spotterRef) "par" (.intLit 0) [] "par")
      .reverted := by
  simpa [checkedExternalCallStmts] using
    checkedExternalCallDecodeRevert
      (cfg := config v) (C := contract v) (evm := evm) (evm' := evmPar)
      (locals := clipperGetFeedPriceValBlnLocals outIlks outPeek)
      (receiver := .storage spotterRef) (retVar := "par") (name := "par")
      (target := clipperGetFeedPriceSpotterAddress evm)
      (sendVal := 0) (args := []) (argVals := []) (out := outPar) (perm := true)
      (clipperEvalGetFeedPriceSpotterCodeGuard_true v evm
        (clipperGetFeedPriceValBlnLocals outIlks outPeek)
        (clipperGetFeedPriceValBlnLocals_get_spotter outIlks outPeek) hcode)
      (clipperEvalGetFeedPriceSpotterTarget v evm
        (clipperGetFeedPriceValBlnLocals outIlks outPeek)
        (clipperGetFeedPriceValBlnLocals_get_spotter outIlks outPeek))
      (by rfl) hcall hdec

theorem clipperGetFeedPriceParSuccess
    (v : ClipperImmutables) {evm evmPar : EVM.State}
    (outIlks outPeek : ByteArray) {outPar : ByteArray}
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperGetFeedPriceSpotterAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm
        (EVM.address (clipperGetFeedPriceSpotterAddress evm)) "par" 0 []
        (true, evmPar, outPar) true)
    (hdec :
      (config v).externalABI.decode? "par" outPar =
        some (clipperSpotterParValues outPar)) :
    ExecBlock (config v)
      (Frame.mk (contract v) (clipperGetFeedPriceValBlnLocals outIlks outPeek)) evm
      (checkedExternalCallStmts (.storage spotterRef) "par" (.intLit 0) [] "par")
      (.ok
        (Frame.mk (contract v) (clipperGetFeedPriceParLocals outIlks outPeek outPar))
        evmPar) := by
  simpa [checkedExternalCallStmts, clipperGetFeedPriceParLocals] using
    checkedExternalCallSuccess
      (cfg := config v) (C := contract v) (evm := evm) (evm' := evmPar)
      (locals := clipperGetFeedPriceValBlnLocals outIlks outPeek)
      (receiver := .storage spotterRef) (retVar := "par") (name := "par")
      (target := clipperGetFeedPriceSpotterAddress evm)
      (sendVal := 0) (args := []) (argVals := []) (out := outPar) (perm := true)
      (value := clipperSpotterParValues outPar)
      (clipperEvalGetFeedPriceSpotterCodeGuard_true v evm
        (clipperGetFeedPriceValBlnLocals outIlks outPeek)
        (clipperGetFeedPriceValBlnLocals_get_spotter outIlks outPeek) hcode)
      (clipperEvalGetFeedPriceSpotterTarget v evm
        (clipperGetFeedPriceValBlnLocals outIlks outPeek)
        (clipperGetFeedPriceValBlnLocals_get_spotter outIlks outPeek))
      (by rfl) hcall hdec

theorem clipperEvalGetFeedPriceRdivArgs
    (v : ClipperImmutables) (evm : EVM.State)
    (outIlks outPeek outPar : ByteArray) :
    evalExprs? (config v)
      (Frame.mk (contract v) (clipperGetFeedPriceParLocals outIlks outPeek outPar)) evm
      [.var "valBln", .var "par"] =
      .ok
        [.int (Int.ofNat
          (UInt256.mul (clipperPipPeekValueWord outPeek) ⟨1000000000⟩).toNat),
        .int (Int.ofNat (clipperSpotterParWord outPar).toNat)] := by
  have hvalBln :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperGetFeedPriceParLocals outIlks outPeek outPar)) evm
        (.var "valBln") =
        .ok (.int (Int.ofNat
          (UInt256.mul (clipperPipPeekValueWord outPeek) ⟨1000000000⟩).toNat)) := by
    simp only [evalExpr?, clipperGetFeedPriceParLocals]
    rw [store_get_ne _ _ (by decide)]
    simp only [clipperGetFeedPriceValBlnLocals, store_get_self]
    rfl
  have hpar :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperGetFeedPriceParLocals outIlks outPeek outPar)) evm
        (.var "par") = .ok (.int (Int.ofNat (clipperSpotterParWord outPar).toNat)) := by
    simp [evalExpr?, clipperGetFeedPriceParLocals, collapseReturns]
    rfl
  simp [evalExprs?, hvalBln, hpar, EvalResult.bind, bind, pure]

theorem clipperEvalGetFeedPriceReturn
    (v : ClipperImmutables) (evm : EVM.State)
    (outIlks outPeek outPar : ByteArray) :
    evalExprs? (config v)
      (Frame.mk (contract v) (clipperGetFeedPriceResultLocals outIlks outPeek outPar)) evm
      [.var "feedPrice"] =
      .ok [.int (Int.ofNat
        (UInt256.div
          (UInt256.mul
            (UInt256.mul (clipperPipPeekValueWord outPeek) ⟨1000000000⟩)
            clipperRayWord)
          (clipperSpotterParWord outPar)).toNat)] := by
  have hfeedPrice :
      evalExpr? (config v)
        (Frame.mk (contract v) (clipperGetFeedPriceResultLocals outIlks outPeek outPar)) evm
        (.var "feedPrice") = .ok (.int (Int.ofNat
          (UInt256.div
            (UInt256.mul
              (UInt256.mul (clipperPipPeekValueWord outPeek) ⟨1000000000⟩)
              clipperRayWord)
            (clipperSpotterParWord outPar)).toNat)) := by
    simp only [evalExpr?, clipperGetFeedPriceResultLocals, store_get_self]
    rfl
  exact evalExprs?_singleton hfeedPrice

theorem clipperGetFeedPriceRdivRevertsMul
    (v : ClipperImmutables) (evm : EVM.State)
    (outIlks outPeek outPar : ByteArray)
    (hover : UInt256.size ≤
      (UInt256.mul (clipperPipPeekValueWord outPeek) ⟨1000000000⟩).toNat *
        clipperRayWord.toNat) :
    ExecBlock (config v)
      (Frame.mk (contract v) (clipperGetFeedPriceParLocals outIlks outPeek outPar)) evm
      [ .internalCall "rdiv" [.var "valBln", .var "par"] "feedPrice",
        .return [.var "feedPrice"] ] .reverted := by
  let x := UInt256.mul (clipperPipPeekValueWord outPeek) ⟨1000000000⟩
  let y := clipperSpotterParWord outPar
  have hcall :
      ExecStmt (config v)
        (Frame.mk (contract v) (clipperGetFeedPriceParLocals outIlks outPeek outPar)) evm
        (.internalCall "rdiv" [.var "valBln", .var "par"] "feedPrice") .reverted :=
    internalCallFunctionRevert
      (cfg := config v)
      (caller := Frame.mk (contract v)
        (clipperGetFeedPriceParLocals outIlks outPeek outPar))
      (evm := evm) (name := "rdiv") (retVar := "feedPrice")
      (args := [.var "valBln", .var "par"])
      (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)])
      (callee := rdivFunction) (locals := clipperUintBinaryLocals x y)
      (by simpa [x, y] using
        clipperEvalGetFeedPriceRdivArgs v evm outIlks outPeek outPar)
      (clipperLookupRdivFunction v) (clipperBindParamsRdiv x y)
      (clipperRdivFunctionRevertsMul v evm x y (by simpa [x] using hover))
  exact ExecBlock.consRevert hcall

theorem clipperGetFeedPriceRdivRevertsDivZero
    (v : ClipperImmutables) (evm : EVM.State)
    (outIlks outPeek outPar : ByteArray)
    (hmul :
      (UInt256.mul (clipperPipPeekValueWord outPeek) ⟨1000000000⟩).toNat *
          clipperRayWord.toNat < UInt256.size)
    (hzero : clipperSpotterParWord outPar = ⟨0⟩) :
    ExecBlock (config v)
      (Frame.mk (contract v) (clipperGetFeedPriceParLocals outIlks outPeek outPar)) evm
      [ .internalCall "rdiv" [.var "valBln", .var "par"] "feedPrice",
        .return [.var "feedPrice"] ] .reverted := by
  let x := UInt256.mul (clipperPipPeekValueWord outPeek) ⟨1000000000⟩
  let y := clipperSpotterParWord outPar
  have hcall :
      ExecStmt (config v)
        (Frame.mk (contract v) (clipperGetFeedPriceParLocals outIlks outPeek outPar)) evm
        (.internalCall "rdiv" [.var "valBln", .var "par"] "feedPrice") .reverted :=
    internalCallFunctionRevert
      (cfg := config v)
      (caller := Frame.mk (contract v)
        (clipperGetFeedPriceParLocals outIlks outPeek outPar))
      (evm := evm) (name := "rdiv") (retVar := "feedPrice")
      (args := [.var "valBln", .var "par"])
      (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)])
      (callee := rdivFunction) (locals := clipperUintBinaryLocals x y)
      (by simpa [x, y] using
        clipperEvalGetFeedPriceRdivArgs v evm outIlks outPeek outPar)
      (clipperLookupRdivFunction v) (clipperBindParamsRdiv x y)
      (clipperRdivFunctionRevertsDivZero v evm x y
        (by simpa [x] using hmul) (by simpa [y] using hzero))
  exact ExecBlock.consRevert hcall

theorem clipperGetFeedPriceRdivReturns
    (v : ClipperImmutables) (evm : EVM.State)
    (outIlks outPeek outPar : ByteArray)
    (hmul :
      (UInt256.mul (clipperPipPeekValueWord outPeek) ⟨1000000000⟩).toNat *
          clipperRayWord.toNat < UInt256.size)
    (hnz : clipperSpotterParWord outPar ≠ ⟨0⟩) :
    ExecBlock (config v)
      (Frame.mk (contract v) (clipperGetFeedPriceParLocals outIlks outPeek outPar)) evm
      [ .internalCall "rdiv" [.var "valBln", .var "par"] "feedPrice",
        .return [.var "feedPrice"] ]
      (.returned
        (Frame.mk (contract v)
          (clipperGetFeedPriceResultLocals outIlks outPeek outPar)) evm
        (some [.int (Int.ofNat
          (UInt256.div
            (UInt256.mul
              (UInt256.mul (clipperPipPeekValueWord outPeek) ⟨1000000000⟩)
              clipperRayWord)
            (clipperSpotterParWord outPar)).toNat)])) := by
  let x := UInt256.mul (clipperPipPeekValueWord outPeek) ⟨1000000000⟩
  let y := clipperSpotterParWord outPar
  let result := UInt256.div (UInt256.mul x clipperRayWord) y
  let resultFrame : Frame :=
    Frame.mk (contract v) (clipperGetFeedPriceResultLocals outIlks outPeek outPar)
  have hcall :
      ExecStmt (config v)
        (Frame.mk (contract v) (clipperGetFeedPriceParLocals outIlks outPeek outPar)) evm
        (.internalCall "rdiv" [.var "valBln", .var "par"] "feedPrice")
        (.ok resultFrame evm) := by
    simpa [resultFrame, clipperGetFeedPriceResultLocals, result,
      resumeAfterInternalCall, x, y] using
      (internalCallFunctionReturn
        (cfg := config v)
        (caller := Frame.mk (contract v)
          (clipperGetFeedPriceParLocals outIlks outPeek outPar))
        (evm := evm) (calleeEvm := evm)
        (name := "rdiv") (retVar := "feedPrice")
        (args := [.var "valBln", .var "par"])
        (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)])
        (callee := rdivFunction) (locals := clipperUintBinaryLocals x y)
        (calleeSolm := Frame.mk (contract v)
          (clipperRdivReturnLocals x y (UInt256.mul x clipperRayWord)))
        (value := some [.int (Int.ofNat result.toNat)])
        (by simpa [x, y] using
          clipperEvalGetFeedPriceRdivArgs v evm outIlks outPeek outPar)
        (clipperLookupRdivFunction v) (clipperBindParamsRdiv x y)
        (clipperRdivFunctionReturns v evm x y
          (by simpa [x] using hmul) (by simpa [y] using hnz)))
  refine ExecBlock.consNormal hcall ?_
  simpa [resultFrame, result, x, y] using
    ExecBlock.consReturn
      (ExecStmt.return (clipperEvalGetFeedPriceReturn v evm outIlks outPeek outPar))

theorem clipperGetFeedPricePrefixToHas
    (v : ClipperImmutables) {evm evmIlks evmPeek : EVM.State}
    {outIlks outPeek : ByteArray}
    (hcodeIlks :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperGetFeedPriceSpotterAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcallIlks :
      typedCallViaEVM (config v) evm
        (EVM.address (clipperGetFeedPriceSpotterAddress evm)) "spotterIlks" 0 [v.ilk]
        (true, evmIlks, outIlks) true)
    (hdecIlks :
      (config v).externalABI.decode? "spotterIlks" outIlks =
        some (clipperSpotterIlksValues outIlks))
    (hcodePip :
      0 < (UInt256.ofNat ((evmIlks.lookupAccount
        (clipperSpotterIlksPipAddress outIlks)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallPeek :
      typedCallViaEVM (config v) evmIlks
        (EVM.address (clipperSpotterIlksPipAddress outIlks)) "peek" 0 []
        (true, evmPeek, outPeek) true)
    (hdecPeek :
      (config v).externalABI.decode? "peek" outPeek =
        some (clipperPipPeekValues outPeek))
    (hnz : clipperPipPeekHasWord outPeek ≠ ⟨0⟩) :
    ExecBlock (config v) ({ contract := contract v, locals := ∅ } : Frame) evm
      (checkedExternalCallStmts (.storage spotterRef) "spotterIlks" (.intLit 0)
          [ilkExpr v] "spotterIlk" ++
        [ .letDecl "pip" (some addr) (tuple0 (.var "spotterIlk")) ] ++
        checkedExternalCallStmts (.var "pip") "peek" (.intLit 0) [] "peekRet" ++
        [ .letDecl "val" (some bytes32) (tuple0 (.var "peekRet")),
          .letDecl "has" (some boolTy) (tuple1 (.var "peekRet")),
          .require (.var "has") ])
      (.ok
        (Frame.mk (contract v) (clipperGetFeedPriceHasLocals outIlks outPeek))
        evmPeek) := by
  let callStmts := checkedExternalCallStmts (.storage spotterRef) "spotterIlks" (.intLit 0)
    [ilkExpr v] "spotterIlk"
  let pipLetStmts : List Stmt :=
    [ .letDecl "pip" (some addr) (tuple0 (.var "spotterIlk")) ]
  let peekStmts := checkedExternalCallStmts (.var "pip") "peek" (.intLit 0) [] "peekRet"
  let valHasStmts : List Stmt :=
    [ .letDecl "val" (some bytes32) (tuple0 (.var "peekRet")),
      .letDecl "has" (some boolTy) (tuple1 (.var "peekRet")),
      .require (.var "has") ]
  let emptyFrame : Frame := { contract := contract v, locals := ∅ }
  let spotterFrame : Frame :=
    { contract := contract v, locals := clipperGetFeedPriceSpotterIlkLocals outIlks }
  let pipFrame : Frame :=
    { contract := contract v, locals := clipperGetFeedPricePipLocals outIlks }
  let peekFrame : Frame :=
    { contract := contract v, locals := clipperGetFeedPricePeekLocals outIlks outPeek }
  let valFrame : Frame :=
    { contract := contract v, locals := clipperGetFeedPriceValLocals outIlks outPeek }
  let hasFrame : Frame :=
    { contract := contract v, locals := clipperGetFeedPriceHasLocals outIlks outPeek }
  have hcallBlock :
      ExecBlock (config v) emptyFrame evm callStmts (.ok spotterFrame evmIlks) := by
    simpa [emptyFrame, spotterFrame, callStmts, clipperGetFeedPriceSpotterIlkLocals] using
      checkedExternalCallSuccess
        (cfg := config v) (C := contract v) (evm := evm) (evm' := evmIlks)
        (locals := ∅) (receiver := .storage spotterRef) (retVar := "spotterIlk")
        (name := "spotterIlks") (target := clipperGetFeedPriceSpotterAddress evm)
        (sendVal := 0) (args := [ilkExpr v]) (argVals := [v.ilk]) (out := outIlks)
        (perm := true) (value := clipperSpotterIlksValues outIlks)
        (clipperEvalGetFeedPriceSpotterCodeGuard_true v evm ∅ (by simp) hcodeIlks)
        (clipperEvalGetFeedPriceSpotterTarget v evm ∅ (by simp))
        (clipperEvalGetFeedPriceIlkArgs v evm) hcallIlks hdecIlks
  have hpipStmt :
      ExecStmt (config v) spotterFrame evmIlks
        (.letDecl "pip" (some addr) (tuple0 (.var "spotterIlk")))
        (.ok pipFrame evmIlks) := by
    simpa [spotterFrame, pipFrame, clipperGetFeedPricePipLocals] using
      ExecStmt.letDecl
        (cfg := config v) (solm := spotterFrame) (evm := evmIlks)
        (name := "pip") (ty := some addr) (expr := tuple0 (.var "spotterIlk"))
        (value := .address (clipperSpotterIlksPipAddress outIlks))
        (clipperEvalGetFeedPricePipFromSpotterIlk v evmIlks outIlks)
  have hpipBlock :
      ExecBlock (config v) spotterFrame evmIlks pipLetStmts (.ok pipFrame evmIlks) :=
    ExecBlock.consNormal hpipStmt ExecBlock.nil
  have hpipReceiver :
      (clipperGetFeedPricePipLocals outIlks).get? "pip" =
        some (.address (clipperSpotterIlksPipAddress outIlks)) := by
    simp [clipperGetFeedPricePipLocals]
  have hpeekBlock :
      ExecBlock (config v) pipFrame evmIlks peekStmts (.ok peekFrame evmPeek) := by
    simpa [pipFrame, peekFrame, peekStmts, clipperGetFeedPricePeekLocals] using
      checkedExternalCallVarSuccess
        (cfg := config v) (C := contract v) (evm := evmIlks) (evm' := evmPeek)
        (locals := clipperGetFeedPricePipLocals outIlks) (receiver := "pip")
        (retVar := "peekRet") (name := "peek")
        (target := clipperSpotterIlksPipAddress outIlks)
        (sendVal := 0) (args := []) (argVals := []) (out := outPeek)
        (perm := true) (value := clipperPipPeekValues outPeek)
        (clipperEvalGetFeedPricePipCodeGuard_true v evmIlks outIlks hcodePip)
        hpipReceiver (by rfl) hcallPeek hdecPeek
  have hvalStmt :
      ExecStmt (config v) peekFrame evmPeek
        (.letDecl "val" (some bytes32) (tuple0 (.var "peekRet")))
        (.ok valFrame evmPeek) := by
    simpa [peekFrame, valFrame, clipperGetFeedPriceValLocals] using
      ExecStmt.letDecl
        (cfg := config v) (solm := peekFrame) (evm := evmPeek)
        (name := "val") (ty := some bytes32) (expr := tuple0 (.var "peekRet"))
        (value := .fixedBytes abiBytes32Width (clipperPipPeekValueBytes outPeek))
        (clipperEvalGetFeedPricePeekVal v evmPeek outIlks outPeek)
  have hhasStmt :
      ExecStmt (config v) valFrame evmPeek
        (.letDecl "has" (some boolTy) (tuple1 (.var "peekRet")))
        (.ok hasFrame evmPeek) := by
    simpa [valFrame, hasFrame, clipperGetFeedPriceHasLocals] using
      ExecStmt.letDecl
        (cfg := config v) (solm := valFrame) (evm := evmPeek)
        (name := "has") (ty := some boolTy) (expr := tuple1 (.var "peekRet"))
        (value := .bool (clipperPipPeekHasWord outPeek != ⟨0⟩))
        (clipperEvalGetFeedPricePeekHas v evmPeek outIlks outPeek)
  have hrequire :
      ExecStmt (config v) hasFrame evmPeek (.require (.var "has"))
        (.ok hasFrame evmPeek) :=
    ExecStmt.requireTrue (clipperEvalGetFeedPriceHas_true v evmPeek outIlks outPeek hnz)
  have hvalHas :
      ExecBlock (config v) peekFrame evmPeek valHasStmts (.ok hasFrame evmPeek) := by
    simpa [valHasStmts] using
      (ExecBlock.consNormal hvalStmt
        (ExecBlock.consNormal hhasStmt (ExecBlock.consNormal hrequire ExecBlock.nil)))
  have hafterPeek :
      ExecBlock (config v) pipFrame evmIlks (peekStmts ++ valHasStmts)
        (.ok hasFrame evmPeek) :=
    execBlock_append hpeekBlock hvalHas
  have hafterPip :
      ExecBlock (config v) spotterFrame evmIlks
        (pipLetStmts ++ (peekStmts ++ valHasStmts)) (.ok hasFrame evmPeek) :=
    execBlock_append hpipBlock hafterPeek
  have hbody :
      ExecBlock (config v) emptyFrame evm
        (callStmts ++ (pipLetStmts ++ (peekStmts ++ valHasStmts)))
        (.ok hasFrame evmPeek) :=
    execBlock_append hcallBlock hafterPip
  simpa [emptyFrame, hasFrame, callStmts, pipLetStmts, peekStmts, valHasStmts,
    List.append_assoc] using hbody

abbrev clipperGetFeedPriceSuccessPrefixStmts (v : ClipperImmutables) : List Stmt :=
  checkedExternalCallStmts (.storage spotterRef) "spotterIlks" (.intLit 0)
      [ilkExpr v] "spotterIlk" ++
    [ .letDecl "pip" (some addr) (tuple0 (.var "spotterIlk")) ] ++
    checkedExternalCallStmts (.var "pip") "peek" (.intLit 0) [] "peekRet" ++
    [ .letDecl "val" (some bytes32) (tuple0 (.var "peekRet")),
      .letDecl "has" (some boolTy) (tuple1 (.var "peekRet")),
      .require (.var "has") ]

abbrev clipperGetFeedPriceSuccessTailStmts : List Stmt :=
  checkedMulUintInto "valBln" (.cast (.var "val") uint256St) (.intLit BLN) ++
    checkedExternalCallStmts (.storage spotterRef) "par" (.intLit 0) [] "par" ++
    [ .internalCall "rdiv" [.var "valBln", .var "par"] "feedPrice",
      .return [.var "feedPrice"] ]

theorem clipperGetFeedPriceSuccessBlockOfTail
    (v : ClipperImmutables) {evm evmPeek : EVM.State}
    {outIlks outPeek : ByteArray} {result : ExecResult}
    (hprefix :
      ExecBlock (config v) (Frame.mk (contract v) ∅) evm
        (clipperGetFeedPriceSuccessPrefixStmts v)
        (.ok (Frame.mk (contract v)
          (clipperGetFeedPriceHasLocals outIlks outPeek)) evmPeek))
    (htail :
      ExecBlock (config v)
        (Frame.mk (contract v) (clipperGetFeedPriceHasLocals outIlks outPeek)) evmPeek
        clipperGetFeedPriceSuccessTailStmts result) :
    ExecBlock (config v) (Frame.mk (contract v) ∅) evm
      (getFeedPriceFunction v).body result := by
  have hwhole := execBlock_append hprefix htail
  simpa [getFeedPriceFunction, clipperGetFeedPriceSuccessPrefixStmts,
    clipperGetFeedPriceSuccessTailStmts, List.append_assoc] using hwhole

theorem clipperGetFeedPriceSuccessFunctionRevertsOfTail
    (v : ClipperImmutables) {evm evmPeek : EVM.State}
    {outIlks outPeek : ByteArray}
    (hprefix :
      ExecBlock (config v) (Frame.mk (contract v) ∅) evm
        (clipperGetFeedPriceSuccessPrefixStmts v)
        (.ok (Frame.mk (contract v)
          (clipperGetFeedPriceHasLocals outIlks outPeek)) evmPeek))
    (htail :
      ExecBlock (config v)
        (Frame.mk (contract v) (clipperGetFeedPriceHasLocals outIlks outPeek)) evmPeek
        clipperGetFeedPriceSuccessTailStmts .reverted) :
    ExecFuncBody (config v) (Frame.mk (contract v) ∅) evm
      (getFeedPriceFunction v).body .reverted :=
  ExecFuncBody.execBlockRevert
    (clipperGetFeedPriceSuccessBlockOfTail v hprefix htail)

theorem clipperGetFeedPriceSuccessFunctionReturnsOfTail
    (v : ClipperImmutables) {evm evmPeek evmResult : EVM.State}
    {outIlks outPeek : ByteArray} {resultFrame : Frame} {values : List Value}
    (hprefix :
      ExecBlock (config v) (Frame.mk (contract v) ∅) evm
        (clipperGetFeedPriceSuccessPrefixStmts v)
        (.ok (Frame.mk (contract v)
          (clipperGetFeedPriceHasLocals outIlks outPeek)) evmPeek))
    (htail :
      ExecBlock (config v)
        (Frame.mk (contract v) (clipperGetFeedPriceHasLocals outIlks outPeek)) evmPeek
        clipperGetFeedPriceSuccessTailStmts
        (.returned resultFrame evmResult (some values))) :
    ExecFuncBody (config v) (Frame.mk (contract v) ∅) evm
      (getFeedPriceFunction v).body
      (.returned resultFrame evmResult (some values)) :=
  ExecFuncBody.execBlockRet
    (clipperGetFeedPriceSuccessBlockOfTail v hprefix htail)

theorem clipperGetFeedPriceSuccessCallRevertsOfTail
    (v : ClipperImmutables) (callerLocals : Store) (retVar : Ident)
    {evm evmPeek : EVM.State} {outIlks outPeek : ByteArray}
    (hprefix :
      ExecBlock (config v) (Frame.mk (contract v) ∅) evm
        (clipperGetFeedPriceSuccessPrefixStmts v)
        (.ok (Frame.mk (contract v)
          (clipperGetFeedPriceHasLocals outIlks outPeek)) evmPeek))
    (htail :
      ExecBlock (config v)
        (Frame.mk (contract v) (clipperGetFeedPriceHasLocals outIlks outPeek)) evmPeek
        clipperGetFeedPriceSuccessTailStmts .reverted) :
    ExecStmt (config v) (Frame.mk (contract v) callerLocals) evm
      (.internalCall "getFeedPrice" [] retVar) .reverted :=
  internalCallFunctionRevert
    (cfg := config v) (caller := Frame.mk (contract v) callerLocals) (evm := evm)
    (name := "getFeedPrice") (retVar := retVar) (args := []) (argVals := [])
    (callee := getFeedPriceFunction v) (locals := ∅) (by rfl)
    (clipperLookupGetFeedPriceFunction v) (clipperBindParamsGetFeedPrice v)
    (clipperGetFeedPriceSuccessFunctionRevertsOfTail v hprefix htail)

theorem clipperGetFeedPriceSuccessCallReturnsOfTail
    (v : ClipperImmutables) (callerLocals : Store) (retVar : Ident)
    {evm evmPeek evmResult : EVM.State}
    {outIlks outPeek : ByteArray} {resultFrame : Frame} {values : List Value}
    (hprefix :
      ExecBlock (config v) (Frame.mk (contract v) ∅) evm
        (clipperGetFeedPriceSuccessPrefixStmts v)
        (.ok (Frame.mk (contract v)
          (clipperGetFeedPriceHasLocals outIlks outPeek)) evmPeek))
    (htail :
      ExecBlock (config v)
        (Frame.mk (contract v) (clipperGetFeedPriceHasLocals outIlks outPeek)) evmPeek
        clipperGetFeedPriceSuccessTailStmts
        (.returned resultFrame evmResult (some values))) :
    ExecStmt (config v) (Frame.mk (contract v) callerLocals) evm
      (.internalCall "getFeedPrice" [] retVar)
      (.ok (Frame.mk (contract v)
        (callerLocals.insert retVar (collapseReturns values))) evmResult) := by
  simpa [resumeAfterInternalCall] using
    (internalCallFunctionReturn
      (cfg := config v) (caller := Frame.mk (contract v) callerLocals)
      (evm := evm) (calleeEvm := evmResult)
      (name := "getFeedPrice") (retVar := retVar) (args := []) (argVals := [])
      (callee := getFeedPriceFunction v) (locals := ∅)
      (calleeSolm := resultFrame) (value := some values) (by rfl)
      (clipperLookupGetFeedPriceFunction v) (clipperBindParamsGetFeedPrice v)
      (clipperGetFeedPriceSuccessFunctionReturnsOfTail v hprefix htail))

theorem clipperGetFeedPriceTailRevertsValBlnOverflow
    (v : ClipperImmutables) (evm : EVM.State) (outIlks outPeek : ByteArray)
    (hlo : 32 ≤ outPeek.size)
    (hover : UInt256.size ≤
      (clipperPipPeekValueWord outPeek).toNat *
        (⟨1000000000⟩ : UInt256).toNat) :
    ExecBlock (config v)
      (Frame.mk (contract v) (clipperGetFeedPriceHasLocals outIlks outPeek)) evm
      clipperGetFeedPriceSuccessTailStmts .reverted := by
  have hmul := clipperGetFeedPriceValBlnMulRevertBlock
    v evm outIlks outPeek hlo hover
  have hwhole := execBlock_append_term
    (s1 := checkedMulUintInto "valBln" (.cast (.var "val") uint256St) (.intLit BLN))
    (s2 := checkedExternalCallStmts (.storage spotterRef) "par" (.intLit 0) [] "par" ++
      [ .internalCall "rdiv" [.var "valBln", .var "par"] "feedPrice",
        .return [.var "feedPrice"] ])
    hmul (by intro frame state h; cases h)
  simpa [clipperGetFeedPriceSuccessTailStmts, List.append_assoc] using hwhole

theorem clipperGetFeedPriceTailRevertsParNoCode
    (v : ClipperImmutables) (evm : EVM.State) (outIlks outPeek : ByteArray)
    (hlo : 32 ≤ outPeek.size)
    (hmul :
      (clipperPipPeekValueWord outPeek).toNat *
          (⟨1000000000⟩ : UInt256).toNat < UInt256.size)
    (hnoCode :
      (UInt256.ofNat ((evm.lookupAccount (clipperGetFeedPriceSpotterAddress evm)).option 0
        (fun acc => acc.code.size))).toNat = 0) :
    ExecBlock (config v)
      (Frame.mk (contract v) (clipperGetFeedPriceHasLocals outIlks outPeek)) evm
      clipperGetFeedPriceSuccessTailStmts .reverted := by
  have hmulBlock := clipperGetFeedPriceValBlnMulSuccessBlock
    v evm outIlks outPeek hlo hmul
  have hpar := clipperGetFeedPriceParNoCode v evm outIlks outPeek hnoCode
  have hmulPar := execBlock_append hmulBlock hpar
  have hwhole := execBlock_append_term
    (s1 := checkedMulUintInto "valBln" (.cast (.var "val") uint256St) (.intLit BLN) ++
      checkedExternalCallStmts (.storage spotterRef) "par" (.intLit 0) [] "par")
    (s2 := [ .internalCall "rdiv" [.var "valBln", .var "par"] "feedPrice",
      .return [.var "feedPrice"] ])
    hmulPar (by intro frame state h; cases h)
  simpa [clipperGetFeedPriceSuccessTailStmts, List.append_assoc] using hwhole

theorem clipperGetFeedPriceTailRevertsParCallFailure
    (v : ClipperImmutables) {evm evmPar : EVM.State}
    (outIlks outPeek : ByteArray) {outPar : ByteArray}
    (hlo : 32 ≤ outPeek.size)
    (hmul :
      (clipperPipPeekValueWord outPeek).toNat *
          (⟨1000000000⟩ : UInt256).toNat < UInt256.size)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperGetFeedPriceSpotterAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm
        (EVM.address (clipperGetFeedPriceSpotterAddress evm)) "par" 0 []
        (false, evmPar, outPar) true) :
    ExecBlock (config v)
      (Frame.mk (contract v) (clipperGetFeedPriceHasLocals outIlks outPeek)) evm
      clipperGetFeedPriceSuccessTailStmts .reverted := by
  have hmulBlock := clipperGetFeedPriceValBlnMulSuccessBlock
    v evm outIlks outPeek hlo hmul
  have hpar := clipperGetFeedPriceParCallFailure v outIlks outPeek hcode hcall
  have hmulPar := execBlock_append hmulBlock hpar
  have hwhole := execBlock_append_term
    (s1 := checkedMulUintInto "valBln" (.cast (.var "val") uint256St) (.intLit BLN) ++
      checkedExternalCallStmts (.storage spotterRef) "par" (.intLit 0) [] "par")
    (s2 := [ .internalCall "rdiv" [.var "valBln", .var "par"] "feedPrice",
      .return [.var "feedPrice"] ])
    hmulPar (by intro frame state h; cases h)
  simpa [clipperGetFeedPriceSuccessTailStmts, List.append_assoc] using hwhole

theorem clipperGetFeedPriceTailRevertsParDecode
    (v : ClipperImmutables) {evm evmPar : EVM.State}
    (outIlks outPeek : ByteArray) {outPar : ByteArray}
    (hlo : 32 ≤ outPeek.size)
    (hmul :
      (clipperPipPeekValueWord outPeek).toNat *
          (⟨1000000000⟩ : UInt256).toNat < UInt256.size)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperGetFeedPriceSpotterAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm
        (EVM.address (clipperGetFeedPriceSpotterAddress evm)) "par" 0 []
        (true, evmPar, outPar) true)
    (hdec : (config v).externalABI.decode? "par" outPar = none) :
    ExecBlock (config v)
      (Frame.mk (contract v) (clipperGetFeedPriceHasLocals outIlks outPeek)) evm
      clipperGetFeedPriceSuccessTailStmts .reverted := by
  have hmulBlock := clipperGetFeedPriceValBlnMulSuccessBlock
    v evm outIlks outPeek hlo hmul
  have hpar := clipperGetFeedPriceParDecodeRevert v outIlks outPeek hcode hcall hdec
  have hmulPar := execBlock_append hmulBlock hpar
  have hwhole := execBlock_append_term
    (s1 := checkedMulUintInto "valBln" (.cast (.var "val") uint256St) (.intLit BLN) ++
      checkedExternalCallStmts (.storage spotterRef) "par" (.intLit 0) [] "par")
    (s2 := [ .internalCall "rdiv" [.var "valBln", .var "par"] "feedPrice",
      .return [.var "feedPrice"] ])
    hmulPar (by intro frame state h; cases h)
  simpa [clipperGetFeedPriceSuccessTailStmts, List.append_assoc] using hwhole

theorem clipperGetFeedPriceTailOfParSuccess
    (v : ClipperImmutables) {evm evmPar : EVM.State}
    (outIlks outPeek : ByteArray) {outPar : ByteArray} {result : ExecResult}
    (hlo : 32 ≤ outPeek.size)
    (hmul :
      (clipperPipPeekValueWord outPeek).toNat *
          (⟨1000000000⟩ : UInt256).toNat < UInt256.size)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperGetFeedPriceSpotterAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm
        (EVM.address (clipperGetFeedPriceSpotterAddress evm)) "par" 0 []
        (true, evmPar, outPar) true)
    (hdec :
      (config v).externalABI.decode? "par" outPar =
        some (clipperSpotterParValues outPar))
    (hrdiv :
      ExecBlock (config v)
        (Frame.mk (contract v) (clipperGetFeedPriceParLocals outIlks outPeek outPar)) evmPar
        [ .internalCall "rdiv" [.var "valBln", .var "par"] "feedPrice",
          .return [.var "feedPrice"] ] result) :
    ExecBlock (config v)
      (Frame.mk (contract v) (clipperGetFeedPriceHasLocals outIlks outPeek)) evm
      clipperGetFeedPriceSuccessTailStmts result := by
  have hmulBlock := clipperGetFeedPriceValBlnMulSuccessBlock
    v evm outIlks outPeek hlo hmul
  have hpar := clipperGetFeedPriceParSuccess v outIlks outPeek hcode hcall hdec
  have hmulPar := execBlock_append hmulBlock hpar
  have hwhole := execBlock_append hmulPar hrdiv
  simpa [clipperGetFeedPriceSuccessTailStmts, List.append_assoc] using hwhole

end Benchmarks.Dss.Clipper
