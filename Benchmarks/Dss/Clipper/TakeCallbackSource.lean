import Benchmarks.Dss.Clipper.TakeCallbackCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

private theorem clipperEvalBinaryOpGtInt (x y : Int) :
    evalBinaryOp? .gt (.int x) (.int y) = .ok (.bool (x > y)) := by
  rfl

private theorem clipperEvalBinaryOpNeAddress (a b : AccountAddress) :
    evalBinaryOp? .ne (.address a) (.address b) =
      .ok (.bool (!(Value.address a == Value.address b))) := by
  rfl

abbrev clipperTakeLocalsCallbackRet (evmLoc evmRead evmVat : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe slice' tabNew lotNew : UInt256) : Store :=
  (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
    tabNew lotNew).insert "_clipperCallRet" .unit

theorem clipperMaskedAddress_injective {a b : UInt256}
    (haddr : AccountAddress.ofNat (UInt256.land a solcAddrMask).toNat =
      AccountAddress.ofNat (UInt256.land b solcAddrMask).toNat) :
    UInt256.land a solcAddrMask = UInt256.land b solcAddrMask := by
  apply u256_inj
  have ha := solcAddrMask_result_canonical a
  have hb := solcAddrMask_result_canonical b
  have hval := congrArg Fin.val haddr
  have ha' : (UInt256.land a solcAddrMask).toNat < AccountAddress.size := by
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using ha
  have hb' : (UInt256.land b solcAddrMask).toNat < AccountAddress.size := by
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hb
  simp only [AccountAddress.ofNat, Fin.val_ofNat] at hval
  rw [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at hval
  exact hval

theorem clipperTakeAddressOfWord_eq_masked (w : UInt256) :
    AccountAddress.ofNat w.toNat =
      AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat := by
  have h := solcAddressValue_masked w
  have haddr : AccountAddress.ofNat w.toNat =
      AccountAddress.ofNat (UInt256.land solcAddrMask w).toNat :=
    Solm.Value.address.inj h
  simpa [u256_land_comm] using haddr

set_option maxHeartbeats 1000000 in
theorem clipperEvalTakeCallbackGuardTrue (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (hdataLen : clipperTakeDataLenWord I ≠ ⟨0⟩)
    (hpayload : (clipperTakeDataBytes I).length =
      (clipperTakeDataLenWord I).toNat)
    (hwhoVat : UInt256.land (clipperTakeWhoWord I) solcAddrMask ≠
      clipperTakeVatTarget v)
    (hwhoDog : UInt256.land (clipperTakeWhoWord I) solcAddrMask ≠
      UInt256.land (clipperTakeDogEVMWord evmVat) solcAddrMask) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew))
      evmVat
      (.binary .and
        (.binary .gt (bytesLength "data") (.intLit 0))
        (.binary .and
          (.binary .ne (.var "who") (vatExpr v))
          (.binary .ne (.var "who") (.var "dog_")))) =
        .ok (.bool true) := by
  have hlenNat : (clipperTakeDataLenWord I).toNat ≠ 0 := by
    intro hz
    apply hdataLen
    exact uint256_toNat_eq_zero hz
  have hbytesPos : 0 < (clipperTakeDataBytes I).length := by omega
  have hwhoVatAddr :
      AccountAddress.ofNat (clipperTakeWhoWord I).toNat ≠ v.vat := by
    intro hEq
    apply hwhoVat
    have hmasked : AccountAddress.ofNat
        (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat = v.vat := by
      rw [← clipperTakeAddressOfWord_eq_masked (clipperTakeWhoWord I)]
      exact hEq
    rw [← clipperTakeVatTargetAddress v] at hmasked
    rw [accountAddress_ofUInt256_eq_ofNat_toNat] at hmasked
    have htargetClean : UInt256.land (clipperTakeVatTarget v) solcAddrMask =
        clipperTakeVatTarget v :=
      solcAddrMask_clean (by
        simpa [clipperTakeVatTarget, u256_land_comm] using
          solcAddrMask_result_canonical (EVM.Word.ofNat (↑v.vat : Nat)))
    have hmaskedWords := clipperMaskedAddress_injective
      (a := clipperTakeWhoWord I) (b := clipperTakeVatTarget v)
      (by simpa [htargetClean] using hmasked)
    simpa [htargetClean] using hmaskedWords
  have hwhoDogAddr : AccountAddress.ofNat (clipperTakeWhoWord I).toNat ≠
      AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat := by
    intro hEq
    apply hwhoDog
    apply clipperMaskedAddress_injective
    rw [← clipperTakeAddressOfWord_eq_masked (clipperTakeWhoWord I),
      ← clipperTakeAddressOfWord_eq_masked (clipperTakeDogEVMWord evmVat)]
    exact hEq
  have hlen := clipperEvalTakeDataLength v evmLoc evmRead evmVat I price slice owe0 owe
    slice' tabNew lotNew
  have hwho := clipperEvalTakeWhoAtDogLoaded v evmLoc evmRead evmVat I price slice owe0
    owe slice' tabNew lotNew
  have hdog := clipperEvalTakeDogAtDogLoaded v evmLoc evmRead evmVat I price slice owe0
    owe slice' tabNew lotNew
  have hgt : evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew)) evmVat
      (.binary .gt (bytesLength "data") (.intLit 0)) = .ok (.bool true) := by
    rw [evalExpr?]
    simp only [EvalResult.bind, bind]
    rw [hlen]
    simp only [evalExpr?, pure]
    rw [clipperEvalBinaryOpGtInt]
    exact congrArg (fun b => EvalResult.ok (Value.bool b))
      (decide_eq_true (Int.ofNat_lt_ofNat_of_lt hbytesPos))
    all_goals decide
  have hneVat : evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew)) evmVat
      (.binary .ne (.var "who") (vatExpr v)) = .ok (.bool true) := by
    rw [evalExpr?]
    simp only [EvalResult.bind, bind]
    rw [hwho, clipperEvalVat]
    change evalBinaryOp? .ne
      (.address (AccountAddress.ofNat (clipperTakeWhoWord I).toNat))
      (.address v.vat) = .ok (.bool true)
    rw [clipperEvalBinaryOpNeAddress]
    simp [hwhoVatAddr]
    all_goals decide
  have hneDog : evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew)) evmVat
      (.binary .ne (.var "who") (.var "dog_")) = .ok (.bool true) := by
    rw [evalExpr?]
    simp only [EvalResult.bind, bind]
    rw [hwho, hdog]
    change evalBinaryOp? .ne
      (.address (AccountAddress.ofNat (clipperTakeWhoWord I).toNat))
      (.address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)) =
        .ok (.bool true)
    rw [clipperEvalBinaryOpNeAddress]
    simp [hwhoDogAddr]
    all_goals decide
  rw [evalExpr?]
  simp only [EvalResult.bind, bind, pure]
  rw [hgt, evalExpr?]
  simp only [EvalResult.bind, bind, pure]
  rw [hneVat, hneDog]

theorem clipperEvalTakeCallbackTarget (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew))
      evmVat (.var "who") =
        .ok (.address (AccountAddress.ofNat (clipperTakeWhoWord I).toNat)) :=
  clipperEvalTakeWhoAtDogLoaded v evmLoc evmRead evmVat I price slice owe0 owe slice'
    tabNew lotNew

theorem clipperTakeCallbackSkipWhoVatStmt (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (hwho : UInt256.land (clipperTakeWhoWord I) solcAddrMask = clipperTakeVatTarget v) :
    ExecStmt (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew))
      evmVat
      (.ite
        (.binary .and
          (.binary .gt (bytesLength "data") (.intLit 0))
          (.binary .and
            (.binary .ne (.var "who") (vatExpr v))
            (.binary .ne (.var "who") (.var "dog_"))))
        (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
          [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet") [])
      (.ok
        (Frame.mk (contract v)
          (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
            tabNew lotNew)) evmVat) := by
  exact ExecStmt.iteFalse
    (clipperEvalTakeCallbackGuardWhoVat v evmLoc evmRead evmVat I price slice owe0 owe
      slice' tabNew lotNew hwho)
    ExecBlock.nil

theorem clipperTakeCallbackSkipWhoDogStmt (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (hwho : UInt256.land (clipperTakeWhoWord I) solcAddrMask =
      UInt256.land (clipperTakeDogEVMWord evmVat) solcAddrMask) :
    ExecStmt (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew))
      evmVat
      (.ite
        (.binary .and
          (.binary .gt (bytesLength "data") (.intLit 0))
          (.binary .and
            (.binary .ne (.var "who") (vatExpr v))
            (.binary .ne (.var "who") (.var "dog_"))))
        (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
          [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet") [])
      (.ok
        (Frame.mk (contract v)
          (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
            tabNew lotNew)) evmVat) := by
  exact ExecStmt.iteFalse
    (clipperEvalTakeCallbackGuardWhoDog v evmLoc evmRead evmVat I price slice owe0 owe
      slice' tabNew lotNew hwho)
    ExecBlock.nil

theorem clipperEvalTakeCallbackCodeGuardFalse (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (hnoCode :
      (UInt256.ofNat
        ((evmVat.lookupAccount
          (AccountAddress.ofNat (clipperTakeWhoWord I).toNat)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew))
      evmVat (.binary .gt (.extCodeSize (.var "who")) (.intLit 0)) =
        .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind,
    clipperEvalTakeCallbackTarget v evmLoc evmRead evmVat I price slice owe0 owe slice'
      tabNew lotNew,
    evalBinaryOp?, EVM.Word.ofNat, hnoCode]

theorem clipperEvalTakeCallbackCodeGuardTrue (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (hcode : 0 <
      (UInt256.ofNat
        ((evmVat.lookupAccount
          (AccountAddress.ofNat (clipperTakeWhoWord I).toNat)).option 0
          (fun acc => acc.code.size))).toNat) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew))
      evmVat (.binary .gt (.extCodeSize (.var "who")) (.intLit 0)) =
        .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind,
    clipperEvalTakeCallbackTarget v evmLoc evmRead evmVat I price slice owe0 owe slice'
      tabNew lotNew,
    evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem clipperTakeCallbackNoCodeStmt (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (hguard : evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew)) evmVat
      (.binary .and
        (.binary .gt (bytesLength "data") (.intLit 0))
        (.binary .and
          (.binary .ne (.var "who") (vatExpr v))
          (.binary .ne (.var "who") (.var "dog_")))) = .ok (.bool true))
    (hnoCode :
      (UInt256.ofNat
        ((evmVat.lookupAccount
          (AccountAddress.ofNat (clipperTakeWhoWord I).toNat)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    ExecStmt (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew)) evmVat
      (.ite
        (.binary .and
          (.binary .gt (bytesLength "data") (.intLit 0))
          (.binary .and
            (.binary .ne (.var "who") (vatExpr v))
            (.binary .ne (.var "who") (.var "dog_"))))
        (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
          [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet") [])
      .reverted := by
  apply ExecStmt.iteTrue hguard
  simpa [checkedExternalCallStmts] using
    ExecBlock.consRevert (ExecStmt.requireFalse
      (clipperEvalTakeCallbackCodeGuardFalse v evmLoc evmRead evmVat I price slice owe0
        owe slice' tabNew lotNew hnoCode))

theorem clipperTakeCallbackCallFailureStmt (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmCb : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) {outCb : ByteArray}
    (hguard : evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew)) evmVat
      (.binary .and
        (.binary .gt (bytesLength "data") (.intLit 0))
        (.binary .and
          (.binary .ne (.var "who") (vatExpr v))
          (.binary .ne (.var "who") (.var "dog_")))) = .ok (.bool true))
    (hcode : 0 <
      (UInt256.ofNat
        ((evmVat.lookupAccount
          (AccountAddress.ofNat (clipperTakeWhoWord I).toNat)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcall : typedCallViaEVM (config v) evmVat
      (EVM.address (AccountAddress.ofNat (clipperTakeWhoWord I).toNat)) "clipperCall" 0
      [.address evmVat.executionEnv.source,
        .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat),
        .int (Int.ofNat slice'.toNat), clipperTakeDataValue I]
      (false, evmCb, outCb) true) :
    ExecStmt (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew)) evmVat
      (.ite
        (.binary .and
          (.binary .gt (bytesLength "data") (.intLit 0))
          (.binary .and
            (.binary .ne (.var "who") (vatExpr v))
            (.binary .ne (.var "who") (.var "dog_"))))
        (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
          [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet") [])
      .reverted := by
  apply ExecStmt.iteTrue hguard
  let dogFrame := Frame.mk (contract v)
    (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
      tabNew lotNew)
  have hargs := clipperEvalTakeCallbackArgs v evmLoc evmRead evmVat I price slice owe0
    owe slice' tabNew lotNew
  simpa [checkedExternalCallStmts, dogFrame] using
    (ExecBlock.consNormal (ExecStmt.requireTrue
      (clipperEvalTakeCallbackCodeGuardTrue v evmLoc evmRead evmVat I price slice owe0
        owe slice' tabNew lotNew hcode))
      (ExecBlock.consRevert
        (ExecStmt.externalCallFailure
          (clipperEvalTakeCallbackTarget v evmLoc evmRead evmVat I price slice owe0 owe
            slice' tabNew lotNew)
          (by simp [evalExpr?, pure]) (by simpa [dogFrame] using hargs) hcall)))

theorem clipperTakeCallbackCallSuccessStmt (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmCb : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) {outCb : ByteArray}
    (hguard : evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew)) evmVat
      (.binary .and
        (.binary .gt (bytesLength "data") (.intLit 0))
        (.binary .and
          (.binary .ne (.var "who") (vatExpr v))
          (.binary .ne (.var "who") (.var "dog_")))) = .ok (.bool true))
    (hcode : 0 <
      (UInt256.ofNat
        ((evmVat.lookupAccount
          (AccountAddress.ofNat (clipperTakeWhoWord I).toNat)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcall : typedCallViaEVM (config v) evmVat
      (EVM.address (AccountAddress.ofNat (clipperTakeWhoWord I).toNat)) "clipperCall" 0
      [.address evmVat.executionEnv.source,
        .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat),
        .int (Int.ofNat slice'.toNat), clipperTakeDataValue I]
      (true, evmCb, outCb) true) :
    ExecStmt (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew)) evmVat
      (.ite
        (.binary .and
          (.binary .gt (bytesLength "data") (.intLit 0))
          (.binary .and
            (.binary .ne (.var "who") (vatExpr v))
            (.binary .ne (.var "who") (.var "dog_"))))
        (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
          [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet") [])
      (.ok
        (Frame.mk (contract v)
          (clipperTakeLocalsCallbackRet evmLoc evmRead evmVat I price slice owe0 owe slice'
            tabNew lotNew)) evmCb) := by
  apply ExecStmt.iteTrue hguard
  let dogFrame := Frame.mk (contract v)
    (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
      tabNew lotNew)
  let cbFrame := Frame.mk (contract v)
    (clipperTakeLocalsCallbackRet evmLoc evmRead evmVat I price slice owe0 owe slice'
      tabNew lotNew)
  have hargs := clipperEvalTakeCallbackArgs v evmLoc evmRead evmVat I price slice owe0
    owe slice' tabNew lotNew
  simpa [checkedExternalCallStmts, dogFrame, cbFrame, clipperTakeLocalsCallbackRet,
    collapseReturns] using
    (ExecBlock.consNormal (ExecStmt.requireTrue
      (clipperEvalTakeCallbackCodeGuardTrue v evmLoc evmRead evmVat I price slice owe0
        owe slice' tabNew lotNew hcode))
      (ExecBlock.consNormal
        (ExecStmt.externalCallSuccess
          (clipperEvalTakeCallbackTarget v evmLoc evmRead evmVat I price slice owe0 owe
            slice' tabNew lotNew)
          (by simp [evalExpr?, pure]) (by simpa [dogFrame] using hargs) hcall
          (clipperTakeDecodeClipperCallVoid v outCb))
        ExecBlock.nil))

end Benchmarks.Dss.Clipper
