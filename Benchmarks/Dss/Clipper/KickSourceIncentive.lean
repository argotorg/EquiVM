import Benchmarks.Dss.Clipper.KickSourceTail

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option maxHeartbeats 1000000
set_option linter.unusedTactic false

abbrev clipperKickSourceChipCoinWord (evmTop : EVM.State)
    (I : ExecutionEnv) : UInt256 :=
  UInt256.div
    (UInt256.mul (clipperKickTabWord I) (clipperRedoChipSolmWord evmTop))
    ⟨1000000000000000000⟩

abbrev clipperKickLocalsChipCoin (evmLock evmTop : EVM.State)
    (I : ExecutionEnv) (feedPrice top : UInt256) : Store :=
  (clipperKickLocalsCoinZero evmLock evmTop I feedPrice top).insert "chipCoin"
    (.int (Int.ofNat (clipperKickSourceChipCoinWord evmTop I).toNat))

abbrev clipperKickSourceCoinWord (evmTop : EVM.State)
    (I : ExecutionEnv) : UInt256 :=
  clipperRedoTipSolmWord evmTop + clipperKickSourceChipCoinWord evmTop I

abbrev clipperKickLocalsCoinNew (evmLock evmTop : EVM.State)
    (I : ExecutionEnv) (feedPrice top : UInt256) : Store :=
  (clipperKickLocalsChipCoin evmLock evmTop I feedPrice top).insert "coinNew"
    (.int (Int.ofNat (clipperKickSourceCoinWord evmTop I).toNat))

abbrev clipperKickLocalsCoin (evmLock evmTop : EVM.State)
    (I : ExecutionEnv) (feedPrice top : UInt256) : Store :=
  (clipperKickLocalsCoinNew evmLock evmTop I feedPrice top).insert "coin"
    (.int (Int.ofNat (clipperKickSourceCoinWord evmTop I).toNat))

abbrev clipperKickSourceVowAddress (evm : EVM.State) : AccountAddress :=
  AccountAddress.ofNat
    (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
      solcAddrMask).toNat

abbrev clipperKickLocalsSuckRet (evmLock evmTop : EVM.State)
    (I : ExecutionEnv) (feedPrice top : UInt256) : Store :=
  (clipperKickLocalsCoin evmLock evmTop I feedPrice top).insert "_suckRet" .unit

theorem clipperEvalKickWmulArgs (v : ClipperImmutables)
    (evmLock evmTop evm : EVM.State) (I : ExecutionEnv)
    (feedPrice top : UInt256) :
    evalExprs? config
      { contract := contract,
        locals := clipperKickLocalsCoinZero evmLock evmTop I feedPrice top, immutables := immStore v }
      evm [.var "tab", .var "_chip"] =
      .ok [.int (Int.ofNat (clipperKickTabWord I).toNat),
        .int (Int.ofNat (clipperRedoChipSolmWord evmTop).toNat)] := by
  have htab : evalExpr? config
      { contract := contract,
        locals := clipperKickLocalsCoinZero evmLock evmTop I feedPrice top, immutables := immStore v }
      evm (.var "tab") = .ok (.int (Int.ofNat (clipperKickTabWord I).toNat)) := by
    simp only [evalExpr?, clipperKickLocalsCoinZero, clipperKickLocalsChip,
      clipperKickLocalsTip, clipperKickLocalsTop, clipperKickLocalsFeedPrice]
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), clipperKickLocalsActivePos,
      store_get_ne _ _ (by decide), clipperKickLocalsId,
      store_get_ne _ _ (by decide), clipperKickStore,
      store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_self]
    rfl
  have hchip : evalExpr? config
      { contract := contract,
        locals := clipperKickLocalsCoinZero evmLock evmTop I feedPrice top, immutables := immStore v }
      evm (.var "_chip") =
      .ok (.int (Int.ofNat (clipperRedoChipSolmWord evmTop).toNat)) := by
    simp only [evalExpr?, clipperKickLocalsCoinZero]
    rw [store_get_ne _ _ (by decide), clipperKickLocalsChip, store_get_self]
    rfl
  exact clipperEvalExprsUintBinary v evm
    (clipperKickLocalsCoinZero evmLock evmTop I feedPrice top)
    (clipperKickTabWord I) (clipperRedoChipSolmWord evmTop) htab hchip

theorem clipperKickWmulCallReturns (v : ClipperImmutables)
    (evmLock evmTop : EVM.State) (I : ExecutionEnv) (feedPrice top : UInt256)
    (hmul : (clipperKickTabWord I).toNat *
      (clipperRedoChipSolmWord evmTop).toNat < UInt256.size) :
    ExecStmt config
      { contract := contract,
        locals := clipperKickLocalsCoinZero evmLock evmTop I feedPrice top, immutables := immStore v }
      evmTop (.internalCall "wmul" [.var "tab", .var "_chip"] "chipCoin")
      (.ok (Frame.mk contract (clipperKickLocalsChipCoin evmLock evmTop I feedPrice top) (immStore v)) evmTop) := by
  let tab := clipperKickTabWord I
  let chip := clipperRedoChipSolmWord evmTop
  simpa [resumeAfterInternalCall, clipperKickLocalsChipCoin,
    clipperKickSourceChipCoinWord, tab, chip] using
    (internalCallFunctionReturn
      (cfg := config)
      (caller := Frame.mk contract (clipperKickLocalsCoinZero evmLock evmTop I feedPrice top) (immStore v))
      (evm := evmTop) (calleeEvm := evmTop)
      (name := "wmul") (retVar := "chipCoin")
      (args := [.var "tab", .var "_chip"])
      (argVals := [.int (Int.ofNat tab.toNat), .int (Int.ofNat chip.toNat)])
      (callee := wmulFunction) (locals := clipperUintBinaryLocals tab chip)
      (calleeSolm := Frame.mk contract (clipperWmulReturnLocals tab chip (UInt256.mul tab chip)) (immStore v))
      (value := some [.int (Int.ofNat
        (UInt256.div (UInt256.mul tab chip) ⟨1000000000000000000⟩).toNat)])
      (by simpa [tab, chip] using
        clipperEvalKickWmulArgs v evmLock evmTop evmTop I feedPrice top)
      (clipperLookupWmulFunction) (clipperBindParamsWmul tab chip)
      (clipperWmulFunctionReturns v evmTop tab chip (by simpa [tab, chip] using hmul)))

theorem clipperKickWmulCallReverts (v : ClipperImmutables)
    (evmLock evmTop : EVM.State) (I : ExecutionEnv) (feedPrice top : UInt256)
    (hover : UInt256.size ≤ (clipperKickTabWord I).toNat *
      (clipperRedoChipSolmWord evmTop).toNat) :
    ExecStmt config
      { contract := contract,
        locals := clipperKickLocalsCoinZero evmLock evmTop I feedPrice top, immutables := immStore v }
      evmTop (.internalCall "wmul" [.var "tab", .var "_chip"] "chipCoin")
      .reverted :=
  internalCallFunctionRevert
    (cfg := config)
    (caller := Frame.mk contract (clipperKickLocalsCoinZero evmLock evmTop I feedPrice top) (immStore v))
    (evm := evmTop) (name := "wmul") (retVar := "chipCoin")
    (args := [.var "tab", .var "_chip"])
    (argVals := [.int (Int.ofNat (clipperKickTabWord I).toNat),
      .int (Int.ofNat (clipperRedoChipSolmWord evmTop).toNat)])
    (callee := wmulFunction)
    (locals := clipperUintBinaryLocals (clipperKickTabWord I)
      (clipperRedoChipSolmWord evmTop))
    (clipperEvalKickWmulArgs v evmLock evmTop evmTop I feedPrice top)
    (clipperLookupWmulFunction)
    (clipperBindParamsWmul (clipperKickTabWord I) (clipperRedoChipSolmWord evmTop))
    (clipperWmulFunctionReverts v evmTop (clipperKickTabWord I)
      (clipperRedoChipSolmWord evmTop) hover)

theorem clipperEvalKickTipAtChipCoin (v : ClipperImmutables)
    (evmLock evmTop evm : EVM.State) (I : ExecutionEnv)
    (feedPrice top : UInt256) :
    evalExpr? config
      { contract := contract,
        locals := clipperKickLocalsChipCoin evmLock evmTop I feedPrice top, immutables := immStore v }
      evm (.var "_tip") =
      .ok (.int (Int.ofNat (clipperRedoTipSolmWord evmTop).toNat)) := by
  simp only [evalExpr?, clipperKickLocalsChipCoin, clipperKickLocalsCoinZero,
    clipperKickLocalsChip, clipperKickLocalsTip]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperEvalKickChipCoin (v : ClipperImmutables)
    (evmLock evmTop evm : EVM.State) (I : ExecutionEnv)
    (feedPrice top : UInt256) :
    evalExpr? config
      { contract := contract,
        locals := clipperKickLocalsChipCoin evmLock evmTop I feedPrice top, immutables := immStore v }
      evm (.var "chipCoin") =
      .ok (.int (Int.ofNat (clipperKickSourceChipCoinWord evmTop I).toNat)) := by
  simp only [evalExpr?, clipperKickLocalsChipCoin, store_get_self, EvalResult.ofOption]

theorem clipperEvalKickCoinAddOk (v : ClipperImmutables)
    (evmLock evmTop : EVM.State) (I : ExecutionEnv) (feedPrice top : UInt256)
    (hfit : (clipperRedoTipSolmWord evmTop).toNat +
      (clipperKickSourceChipCoinWord evmTop I).toNat < UInt256.size) :
    evalExpr? config
      { contract := contract,
        locals := clipperKickLocalsChipCoin evmLock evmTop I feedPrice top, immutables := immStore v }
      evmTop (add256 (.var "_tip") (.var "chipCoin")) =
      .ok (.int (Int.ofNat (clipperKickSourceCoinWord evmTop I).toNat)) :=
  clipperEvalAdd256_ok v
    (clipperEvalKickTipAtChipCoin v evmLock evmTop evmTop I feedPrice top)
    (clipperEvalKickChipCoin v evmLock evmTop evmTop I feedPrice top) rfl hfit

theorem clipperEvalKickCoinAddRevert (v : ClipperImmutables)
    (evmLock evmTop : EVM.State) (I : ExecutionEnv) (feedPrice top : UInt256)
    (hover : UInt256.size ≤ (clipperRedoTipSolmWord evmTop).toNat +
      (clipperKickSourceChipCoinWord evmTop I).toNat) :
    evalExpr? config
      { contract := contract,
        locals := clipperKickLocalsChipCoin evmLock evmTop I feedPrice top, immutables := immStore v }
      evmTop (add256 (.var "_tip") (.var "chipCoin")) = .revert :=
  clipperEvalAdd256_revert v
    (clipperEvalKickTipAtChipCoin v evmLock evmTop evmTop I feedPrice top)
    (clipperEvalKickChipCoin v evmLock evmTop evmTop I feedPrice top) hover

theorem clipperKickCheckedAddCoin (v : ClipperImmutables)
    (evmLock evmTop : EVM.State) (I : ExecutionEnv) (feedPrice top : UInt256)
    (hfit : (clipperRedoTipSolmWord evmTop).toNat +
      (clipperKickSourceChipCoinWord evmTop I).toNat < UInt256.size) :
    ExecBlock config
      { contract := contract,
        locals := clipperKickLocalsChipCoin evmLock evmTop I feedPrice top, immutables := immStore v }
      evmTop (checkedAddUintInto "coinNew" (.var "_tip") (.var "chipCoin"))
      (.ok (Frame.mk contract (clipperKickLocalsCoinNew evmLock evmTop I feedPrice top) (immStore v)) evmTop) := by
  have hlet :
      ExecStmt config
        { contract := contract,
          locals := clipperKickLocalsChipCoin evmLock evmTop I feedPrice top, immutables := immStore v }
        evmTop
        (.letDecl "coinNew" (some uint256)
          (add256 (.var "_tip") (.var "chipCoin")))
        (.ok (Frame.mk contract (clipperKickLocalsCoinNew evmLock evmTop I feedPrice top) (immStore v)) evmTop) :=
    ExecStmt.letDecl
      (clipperEvalKickCoinAddOk v evmLock evmTop I feedPrice top hfit)
  have hcoin : (clipperKickSourceCoinWord evmTop I).toNat =
      (clipperRedoTipSolmWord evmTop).toNat +
        (clipperKickSourceChipCoinWord evmTop I).toNat := by
    rw [clipperKickSourceCoinWord, uadd_toNat, Nat.mod_eq_of_lt hfit]
  have htipLe : (clipperRedoTipSolmWord evmTop).toNat ≤
      (clipperKickSourceCoinWord evmTop I).toNat := by omega
  have hcoinEval : evalExpr? config
      { contract := contract,
        locals := clipperKickLocalsCoinNew evmLock evmTop I feedPrice top, immutables := immStore v }
      evmTop (.var "coinNew") =
      .ok (.int (Int.ofNat (clipperKickSourceCoinWord evmTop I).toNat)) := by
    simp only [evalExpr?, clipperKickLocalsCoinNew, store_get_self, EvalResult.ofOption]
  have htipEval : evalExpr? config
      { contract := contract,
        locals := clipperKickLocalsCoinNew evmLock evmTop I feedPrice top, immutables := immStore v }
      evmTop (.var "_tip") =
      .ok (.int (Int.ofNat (clipperRedoTipSolmWord evmTop).toNat)) := by
    simp only [evalExpr?, clipperKickLocalsCoinNew, clipperKickLocalsChipCoin,
      clipperKickLocalsCoinZero, clipperKickLocalsChip, clipperKickLocalsTip]
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_self]
    rfl
  have hreq : evalExpr? config
      { contract := contract,
        locals := clipperKickLocalsCoinNew evmLock evmTop I feedPrice top, immutables := immStore v }
      evmTop (.binary .ge (.var "coinNew") (.var "_tip")) = .ok (.bool true) := by
    simp only [evalExpr?, hcoinEval, htipEval, EvalResult.bind, bind, evalBinaryOp?]
    simpa using htipLe
  simpa [checkedAddUintInto, clipperKickLocalsCoinNew] using
    ExecBlock.consNormal hlet
      (ExecBlock.consNormal (ExecStmt.requireTrue hreq) ExecBlock.nil)

theorem clipperKickCheckedAddCoinReverts (v : ClipperImmutables)
    (evmLock evmTop : EVM.State) (I : ExecutionEnv) (feedPrice top : UInt256)
    (hover : UInt256.size ≤ (clipperRedoTipSolmWord evmTop).toNat +
      (clipperKickSourceChipCoinWord evmTop I).toNat) :
    ExecBlock config
      { contract := contract,
        locals := clipperKickLocalsChipCoin evmLock evmTop I feedPrice top, immutables := immStore v }
      evmTop (checkedAddUintInto "coinNew" (.var "_tip") (.var "chipCoin"))
      .reverted := by
  simpa [checkedAddUintInto] using ExecBlock.consRevert
    (ExecStmt.letDeclRevert
      (clipperEvalKickCoinAddRevert v evmLock evmTop I feedPrice top hover))

theorem clipperKickAssignCoin (v : ClipperImmutables)
    (evmLock evmTop : EVM.State) (I : ExecutionEnv) (feedPrice top : UInt256) :
    ExecStmt config
      { contract := contract,
        locals := clipperKickLocalsCoinNew evmLock evmTop I feedPrice top, immutables := immStore v }
      evmTop (.assign .localVar (varRef "coin") (.var "coinNew"))
      (.ok (Frame.mk contract (clipperKickLocalsCoin evmLock evmTop I feedPrice top) (immStore v)) evmTop) := by
  have hrhs : evalExpr? config
      { contract := contract,
        locals := clipperKickLocalsCoinNew evmLock evmTop I feedPrice top, immutables := immStore v }
      evmTop (.var "coinNew") =
      .ok (.int (Int.ofNat (clipperKickSourceCoinWord evmTop I).toNat)) := by
    simp only [evalExpr?, clipperKickLocalsCoinNew, store_get_self, EvalResult.ofOption]
  apply ExecStmt.assign hrhs
  simp [assignStorageRef?, updateLocalPath?, varRef, clipperKickLocalsCoin,
    pure, bind, EvalResult.bind]

theorem clipperKickLocalsCoin_get_vow (evmLock evmTop : EVM.State)
    (I : ExecutionEnv) (feedPrice top : UInt256) :
    (clipperKickLocalsCoin evmLock evmTop I feedPrice top).get? "vow" = none := by
  simp [clipperKickLocalsCoin, clipperKickLocalsCoinNew,
    clipperKickLocalsChipCoin, clipperKickLocalsCoinZero, clipperKickLocalsChip,
    clipperKickLocalsTip, clipperKickLocalsTop, clipperKickLocalsFeedPrice,
    clipperKickLocalsActivePos, clipperKickLocalsId, clipperKickStore]

theorem clipperEvalKickSuckArgs (v : ClipperImmutables)
    (evmLock evmTop : EVM.State) (I : ExecutionEnv) (feedPrice top : UInt256) :
    evalExprs? config
      { contract := contract,
        locals := clipperKickLocalsCoin evmLock evmTop I feedPrice top, immutables := immStore v }
      evmTop [.storage vowRef, .var "kpr", .var "coin"] =
      .ok [.address (clipperKickSourceVowAddress evmTop), clipperKickKprValue I,
        .int (Int.ofNat (clipperKickSourceCoinWord evmTop I).toNat)] := by
  have hvow := clipperEvalVow v evmTop
    (clipperKickLocalsCoin evmLock evmTop I feedPrice top)
    (clipperKickLocalsCoin_get_vow evmLock evmTop I feedPrice top)
  have hkpr : evalExpr? config
      { contract := contract,
        locals := clipperKickLocalsCoin evmLock evmTop I feedPrice top, immutables := immStore v }
      evmTop (.var "kpr") = .ok (clipperKickKprValue I) := by
    simp only [evalExpr?, clipperKickLocalsCoin, clipperKickLocalsCoinNew,
      clipperKickLocalsChipCoin, clipperKickLocalsCoinZero, clipperKickLocalsChip,
      clipperKickLocalsTip, clipperKickLocalsTop, clipperKickLocalsFeedPrice,
      clipperKickLocalsActivePos, clipperKickLocalsId]
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      clipperKickStore, store_get_self]
    rfl
  have hcoin : evalExpr? config
      { contract := contract,
        locals := clipperKickLocalsCoin evmLock evmTop I feedPrice top, immutables := immStore v }
      evmTop (.var "coin") =
      .ok (.int (Int.ofNat (clipperKickSourceCoinWord evmTop I).toNat)) := by
    simp only [evalExpr?, clipperKickLocalsCoin, store_get_self, EvalResult.ofOption]
  simp only [evalExprs?, hvow, hkpr, hcoin, EvalResult.bind, bind, pure]

theorem clipperKickSuckNoCodeSource (v : ClipperImmutables)
    (evmLock evmTop : EVM.State) (I : ExecutionEnv) (feedPrice top : UInt256)
    (hnoCode : (UInt256.ofNat ((evmTop.lookupAccount v.vat).option 0
      (fun acc => acc.code.size))).toNat = 0) :
    ExecBlock config
      { contract := contract,
        locals := clipperKickLocalsCoin evmLock evmTop I feedPrice top, immutables := immStore v }
      evmTop (checkedExternalCallStmts vatExpr "suck" (.intLit 0)
        [.storage vowRef, .var "kpr", .var "coin"] "_suckRet") .reverted := by
  simpa [checkedExternalCallStmts] using checkedExternalCallNoCode
    (cfg := config) (C := contract) (evm := evmTop)
    (locals := clipperKickLocalsCoin evmLock evmTop I feedPrice top)
    (receiver := vatExpr) (retVar := "_suckRet") (name := "suck")
    (sendVal := 0) (args := [.storage vowRef, .var "kpr", .var "coin"])
    (perm := true)
    (clipperEvalRedoVatCodeGuardFalse v evmTop
      (clipperKickLocalsCoin evmLock evmTop I feedPrice top) hnoCode)

theorem clipperKickSuckCallFailureSource (v : ClipperImmutables)
    (evmLock evmTop evmAfter : EVM.State) (I : ExecutionEnv)
    (feedPrice top : UInt256) (out : ByteArray)
    (hcode : 0 < (UInt256.ofNat ((evmTop.lookupAccount v.vat).option 0
      (fun acc => acc.code.size))).toNat)
    (hcall : typedCallViaEVM config evmTop (EVM.address v.vat) "suck" 0
      [.address (clipperKickSourceVowAddress evmTop), clipperKickKprValue I,
        .int (Int.ofNat (clipperKickSourceCoinWord evmTop I).toNat)]
      (false, evmAfter, out) true) :
    ExecBlock config
      { contract := contract,
        locals := clipperKickLocalsCoin evmLock evmTop I feedPrice top, immutables := immStore v }
      evmTop (checkedExternalCallStmts vatExpr "suck" (.intLit 0)
        [.storage vowRef, .var "kpr", .var "coin"] "_suckRet") .reverted := by
  simpa [checkedExternalCallStmts] using checkedExternalCallFailure
    (clipperEvalRedoVatCodeGuardTrue v evmTop
      (clipperKickLocalsCoin evmLock evmTop I feedPrice top) hcode)
    (clipperEvalVat v evmTop
      (clipperKickLocalsCoin evmLock evmTop I feedPrice top))
    (clipperEvalKickSuckArgs v evmLock evmTop I feedPrice top) hcall

theorem clipperKickSuckCallSuccessSource (v : ClipperImmutables)
    (evmLock evmTop evmAfter : EVM.State) (I : ExecutionEnv)
    (feedPrice top : UInt256) (out : ByteArray)
    (hcode : 0 < (UInt256.ofNat ((evmTop.lookupAccount v.vat).option 0
      (fun acc => acc.code.size))).toNat)
    (hcall : typedCallViaEVM config evmTop (EVM.address v.vat) "suck" 0
      [.address (clipperKickSourceVowAddress evmTop), clipperKickKprValue I,
        .int (Int.ofNat (clipperKickSourceCoinWord evmTop I).toNat)]
      (true, evmAfter, out) true) :
    ExecBlock config
      { contract := contract,
        locals := clipperKickLocalsCoin evmLock evmTop I feedPrice top, immutables := immStore v }
      evmTop (checkedExternalCallStmts vatExpr "suck" (.intLit 0)
        [.storage vowRef, .var "kpr", .var "coin"] "_suckRet")
      (.ok (Frame.mk contract (clipperKickLocalsSuckRet evmLock evmTop I feedPrice top) (immStore v)) evmAfter) := by
  simpa [checkedExternalCallStmts, clipperKickLocalsSuckRet] using
    checkedExternalCallSuccess
      (clipperEvalRedoVatCodeGuardTrue v evmTop
        (clipperKickLocalsCoin evmLock evmTop I feedPrice top) hcode)
      (clipperEvalVat v evmTop
        (clipperKickLocalsCoin evmLock evmTop I feedPrice top))
      (clipperEvalKickSuckArgs v evmLock evmTop I feedPrice top)
      hcall (clipperRedoDecodeSuckVoid out)

end Benchmarks.Dss.Clipper
