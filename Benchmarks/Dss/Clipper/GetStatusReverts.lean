import Benchmarks.Dss.Clipper.GetStatusBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

theorem clipperStatusFunctionRevertsAgeForPrice (v : ClipperImmutables)
    (evm : EVM.State) (tic top : UInt256)
    (hlt : (clipperTimestampWord evm).toNat < tic.toNat) :
    ExecFuncBody (config v)
      ({ contract := contract v, locals := clipperStatusLocals tic top } : Frame)
      evm statusFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  simpa [statusFunction, checkedExternalCallStmts] using
    (ExecBlock.consRevert
      (clipperStatusAgeForPriceCallReverts v evm tic top hlt))

theorem clipperStatusFunctionRevertsPriceCallFailure (v : ClipperImmutables)
    {evm evmPrice : EVM.State} (tic top : UInt256) {out : ByteArray}
    (hlePrice : tic.toNat ≤ (clipperTimestampWord evm).toNat)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0
        [.int (Int.ofNat top.toNat),
          .int (Int.ofNat (UInt256.sub (clipperTimestampWord evm) tic).toNat)]
        (false, evmPrice, out) false) :
    ExecFuncBody (config v)
      ({ contract := contract v, locals := clipperStatusLocals tic top } : Frame)
      evm statusFunction.body .reverted := by
  let ageForPrice : UInt256 := UInt256.sub (clipperTimestampWord evm) tic
  let startFrame : Frame := { contract := contract v, locals := clipperStatusLocals tic top }
  let ageFrame : Frame :=
    { contract := contract v, locals := clipperStatusAgeForPriceLocals tic top ageForPrice }
  let callStmts :=
    checkedExternalCallStmts (.storage calcRef) "price" (.intLit 0)
      [.var "top", .var "ageForPrice"] "price" (perm := false)
  let tailStmts : List Stmt :=
    [ .internalCall "sub" [.env .timestamp, .var "tic"] "ageForDone",
      .letDecl "done" (some boolTy) (.boolLit false),
      .ite (.binary .gt (.var "ageForDone") (.storage tailRef))
        [ .assign .localVar (varRef "done") (.boolLit true) ]
        ([ .internalCall "rdiv" [.var "price", .var "top"] "ratio",
           .assign .localVar (varRef "done")
             (.binary .lt (.var "ratio") (.storage cuspRef)) ]),
      .return [.var "done", .var "price"] ]
  have hsubPrice :
      ExecBlock (config v) startFrame evm
        [ .internalCall "sub" [.env .timestamp, .var "tic"] "ageForPrice" ]
        (.ok ageFrame evm) := by
    exact ExecBlock.consNormal
      (by
        simpa [startFrame, ageFrame, ageForPrice] using
          clipperStatusAgeForPriceCallReturns v evm tic top hlePrice)
      ExecBlock.nil
  have hcallBlock :
      ExecBlock (config v) ageFrame evm callStmts .reverted := by
    simpa [ageFrame, callStmts, ageForPrice] using
      clipperStatusPriceCallFailure v (evm := evm) (evm' := evmPrice)
        tic top ageForPrice hcode hcall
  have htail :
      ExecBlock (config v) ageFrame evm (callStmts ++ tailStmts) .reverted := by
    exact execBlock_append_term (s1 := callStmts) (s2 := tailStmts)
      hcallBlock (by intro f e h; cases h)
  have hbody :
      ExecBlock (config v) startFrame evm
        ([ .internalCall "sub" [.env .timestamp, .var "tic"] "ageForPrice" ] ++
          callStmts ++ tailStmts)
        .reverted :=
   execBlock_append (s2 := callStmts ++ tailStmts) hsubPrice htail
  apply ExecFuncBody.execBlockRevert
  simpa [statusFunction, checkedExternalCallStmts, startFrame, callStmts, tailStmts] using hbody

theorem clipperStatusFunctionRevertsPriceNoCode (v : ClipperImmutables)
    (evm : EVM.State) (tic top : UInt256)
    (hlePrice : tic.toNat ≤ (clipperTimestampWord evm).toNat)
    (hnoCode :
      (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat = 0) :
    ExecFuncBody (config v)
      ({ contract := contract v, locals := clipperStatusLocals tic top } : Frame)
      evm statusFunction.body .reverted := by
  let ageForPrice : UInt256 := UInt256.sub (clipperTimestampWord evm) tic
  let startFrame : Frame := { contract := contract v, locals := clipperStatusLocals tic top }
  let ageFrame : Frame :=
    { contract := contract v, locals := clipperStatusAgeForPriceLocals tic top ageForPrice }
  let callStmts :=
    checkedExternalCallStmts (.storage calcRef) "price" (.intLit 0)
      [.var "top", .var "ageForPrice"] "price" (perm := false)
  let tailStmts : List Stmt :=
    [ .internalCall "sub" [.env .timestamp, .var "tic"] "ageForDone",
      .letDecl "done" (some boolTy) (.boolLit false),
      .ite (.binary .gt (.var "ageForDone") (.storage tailRef))
        [ .assign .localVar (varRef "done") (.boolLit true) ]
        ([ .internalCall "rdiv" [.var "price", .var "top"] "ratio",
           .assign .localVar (varRef "done")
             (.binary .lt (.var "ratio") (.storage cuspRef)) ]),
      .return [.var "done", .var "price"] ]
  have hsubPrice :
      ExecBlock (config v) startFrame evm
        [ .internalCall "sub" [.env .timestamp, .var "tic"] "ageForPrice" ]
        (.ok ageFrame evm) := by
    exact ExecBlock.consNormal
      (by
        simpa [startFrame, ageFrame, ageForPrice] using
          clipperStatusAgeForPriceCallReturns v evm tic top hlePrice)
      ExecBlock.nil
  have hcallBlock :
      ExecBlock (config v) ageFrame evm callStmts .reverted := by
    simpa [ageFrame, callStmts, ageForPrice] using
      clipperStatusPriceCallNoCode v evm tic top ageForPrice hnoCode
  have htail :
      ExecBlock (config v) ageFrame evm (callStmts ++ tailStmts) .reverted := by
    exact execBlock_append_term (s1 := callStmts) (s2 := tailStmts)
      hcallBlock (by intro f e h; cases h)
  have hbody :
      ExecBlock (config v) startFrame evm
        ([ .internalCall "sub" [.env .timestamp, .var "tic"] "ageForPrice" ] ++
          callStmts ++ tailStmts)
        .reverted :=
   execBlock_append (s2 := callStmts ++ tailStmts) hsubPrice htail
  apply ExecFuncBody.execBlockRevert
  simpa [statusFunction, checkedExternalCallStmts, startFrame, callStmts, tailStmts] using hbody

theorem clipperStatusFunctionRevertsPriceDecode (v : ClipperImmutables)
    {evm evmPrice : EVM.State} (tic top : UInt256) {out : ByteArray}
    (hlePrice : tic.toNat ≤ (clipperTimestampWord evm).toNat)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0
        [.int (Int.ofNat top.toNat),
          .int (Int.ofNat (UInt256.sub (clipperTimestampWord evm) tic).toNat)]
        (true, evmPrice, out) false)
    (hdec : (config v).externalABI.decode? "price" out = none) :
    ExecFuncBody (config v)
      ({ contract := contract v, locals := clipperStatusLocals tic top } : Frame)
      evm statusFunction.body .reverted := by
  let ageForPrice : UInt256 := UInt256.sub (clipperTimestampWord evm) tic
  let startFrame : Frame := { contract := contract v, locals := clipperStatusLocals tic top }
  let ageFrame : Frame :=
    { contract := contract v, locals := clipperStatusAgeForPriceLocals tic top ageForPrice }
  let callStmts :=
    checkedExternalCallStmts (.storage calcRef) "price" (.intLit 0)
      [.var "top", .var "ageForPrice"] "price" (perm := false)
  let tailStmts : List Stmt :=
    [ .internalCall "sub" [.env .timestamp, .var "tic"] "ageForDone",
      .letDecl "done" (some boolTy) (.boolLit false),
      .ite (.binary .gt (.var "ageForDone") (.storage tailRef))
        [ .assign .localVar (varRef "done") (.boolLit true) ]
        ([ .internalCall "rdiv" [.var "price", .var "top"] "ratio",
           .assign .localVar (varRef "done")
             (.binary .lt (.var "ratio") (.storage cuspRef)) ]),
      .return [.var "done", .var "price"] ]
  have hsubPrice :
      ExecBlock (config v) startFrame evm
        [ .internalCall "sub" [.env .timestamp, .var "tic"] "ageForPrice" ]
        (.ok ageFrame evm) := by
    exact ExecBlock.consNormal
      (by
        simpa [startFrame, ageFrame, ageForPrice] using
          clipperStatusAgeForPriceCallReturns v evm tic top hlePrice)
      ExecBlock.nil
  have hcallBlock :
      ExecBlock (config v) ageFrame evm callStmts .reverted := by
    simpa [ageFrame, callStmts, ageForPrice] using
      clipperStatusPriceCallDecodeReverts v (evm := evm) (evm' := evmPrice)
        tic top ageForPrice hcode hcall hdec
  have htail :
      ExecBlock (config v) ageFrame evm (callStmts ++ tailStmts) .reverted := by
    exact execBlock_append_term (s1 := callStmts) (s2 := tailStmts)
      hcallBlock (by intro f e h; cases h)
  have hbody :
      ExecBlock (config v) startFrame evm
        ([ .internalCall "sub" [.env .timestamp, .var "tic"] "ageForPrice" ] ++
          callStmts ++ tailStmts)
        .reverted :=
   execBlock_append (s2 := callStmts ++ tailStmts) hsubPrice htail
  apply ExecFuncBody.execBlockRevert
  simpa [statusFunction, checkedExternalCallStmts, startFrame, callStmts, tailStmts] using hbody

theorem clipperStatusRdivCallRevertsDivZero (v : ClipperImmutables) (evm : EVM.State)
    (tic top ageForPrice price ageForDone : UInt256)
    (hmul : price.toNat * clipperRayWord.toNat < UInt256.size) (htop : top = ⟨0⟩) :
    ExecStmt (config v)
      ({ contract := contract v, locals :=
        clipperStatusDoneLocals tic top ageForPrice price ageForDone } : Frame) evm
      (.internalCall "rdiv" [.var "price", .var "top"] "ratio") .reverted :=
    internalCallFunctionRevert
      (cfg := config v)
      (caller :=
        { contract := contract v,
          locals := clipperStatusDoneLocals tic top ageForPrice price ageForDone })
      (evm := evm)
      (name := "rdiv") (retVar := "ratio")
      (args := [.var "price", .var "top"])
      (argVals := [.int (Int.ofNat price.toNat), .int (Int.ofNat top.toNat)])
      (callee := rdivFunction)
      (locals := clipperUintBinaryLocals price top)
      (clipperEvalStatusRdivArgs v evm tic top ageForPrice price ageForDone)
      (clipperLookupRdivFunction v)
      (clipperBindParamsRdiv price top)
      (clipperRdivFunctionRevertsDivZero v evm price top hmul htop)

theorem clipperStatusFunctionRevertsAgeForDone (v : ClipperImmutables)
    {evm evmPrice : EVM.State} (tic top price : UInt256) {out : ByteArray}
    (hlePrice : tic.toNat ≤ (clipperTimestampWord evm).toNat)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0
        [.int (Int.ofNat top.toNat),
          .int (Int.ofNat (UInt256.sub (clipperTimestampWord evm) tic).toNat)]
        (true, evmPrice, out) false)
    (hdec : (config v).externalABI.decode? "price" out =
      some [.int (Int.ofNat price.toNat)])
    (hltDone : (clipperTimestampWord evmPrice).toNat < tic.toNat) :
    ExecFuncBody (config v)
      ({ contract := contract v, locals := clipperStatusLocals tic top } : Frame)
      evm statusFunction.body .reverted := by
  let ageForPrice : UInt256 := UInt256.sub (clipperTimestampWord evm) tic
  let startFrame : Frame := { contract := contract v, locals := clipperStatusLocals tic top }
  let ageFrame : Frame :=
    { contract := contract v, locals := clipperStatusAgeForPriceLocals tic top ageForPrice }
  let priceFrame : Frame :=
    { contract := contract v, locals := clipperStatusPriceLocals tic top ageForPrice price }
  let callStmts :=
    checkedExternalCallStmts (.storage calcRef) "price" (.intLit 0)
      [.var "top", .var "ageForPrice"] "price" (perm := false)
  let tailStmts : List Stmt :=
    [ .internalCall "sub" [.env .timestamp, .var "tic"] "ageForDone",
      .letDecl "done" (some boolTy) (.boolLit false),
      .ite (.binary .gt (.var "ageForDone") (.storage tailRef))
        [ .assign .localVar (varRef "done") (.boolLit true) ]
        ([ .internalCall "rdiv" [.var "price", .var "top"] "ratio",
           .assign .localVar (varRef "done")
             (.binary .lt (.var "ratio") (.storage cuspRef)) ]),
      .return [.var "done", .var "price"] ]
  have hsubPrice :
      ExecBlock (config v) startFrame evm
        [ .internalCall "sub" [.env .timestamp, .var "tic"] "ageForPrice" ]
        (.ok ageFrame evm) := by
    exact ExecBlock.consNormal
      (by
        simpa [startFrame, ageFrame, ageForPrice] using
          clipperStatusAgeForPriceCallReturns v evm tic top hlePrice)
      ExecBlock.nil
  have hcallBlock :
      ExecBlock (config v) ageFrame evm callStmts (.ok priceFrame evmPrice) := by
    simpa [ageFrame, priceFrame, callStmts, ageForPrice] using
      clipperStatusPriceCallReturns v (evm := evm) (evm' := evmPrice)
        tic top ageForPrice price hcode hcall hdec
  have hsubDone :
      ExecStmt (config v) priceFrame evmPrice
        (.internalCall "sub" [.env .timestamp, .var "tic"] "ageForDone") .reverted := by
    simpa [priceFrame, ageForPrice] using
      clipperStatusAgeForDoneCallReverts v evmPrice tic top ageForPrice price hltDone
  have htail :
      ExecBlock (config v) priceFrame evmPrice tailStmts .reverted := by
    simpa [tailStmts] using ExecBlock.consRevert hsubDone
  have hcallTail :
      ExecBlock (config v) ageFrame evm (callStmts ++ tailStmts) .reverted :=
   execBlock_append (s2 := tailStmts) hcallBlock htail
  have hbody :
      ExecBlock (config v) startFrame evm
        ([ .internalCall "sub" [.env .timestamp, .var "tic"] "ageForPrice" ] ++
          callStmts ++ tailStmts)
        .reverted :=
   execBlock_append (s2 := callStmts ++ tailStmts) hsubPrice hcallTail
  apply ExecFuncBody.execBlockRevert
  simpa [statusFunction, checkedExternalCallStmts, startFrame, callStmts, tailStmts] using hbody

private theorem clipperStatusFunctionRevertsRdivCore (v : ClipperImmutables)
    {evm evmPrice : EVM.State} (tic top price : UInt256) {out : ByteArray}
    (hlePrice : tic.toNat ≤ (clipperTimestampWord evm).toNat)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0
        [.int (Int.ofNat top.toNat),
          .int (Int.ofNat (UInt256.sub (clipperTimestampWord evm) tic).toNat)]
        (true, evmPrice, out) false)
    (hdec : (config v).externalABI.decode? "price" out =
      some [.int (Int.ofNat price.toNat)])
    (hleDone : tic.toNat ≤ (clipperTimestampWord evmPrice).toNat)
    (htail :
      (UInt256.sub (clipperTimestampWord evmPrice) tic).toNat ≤
        (clipperStatusTailWord evmPrice).toNat)
    (hrdiv :
      ExecStmt (config v)
        ({ contract := contract v, locals :=
          clipperStatusDoneLocals tic top (UInt256.sub (clipperTimestampWord evm) tic)
            price (UInt256.sub (clipperTimestampWord evmPrice) tic) } : Frame)
        evmPrice (.internalCall "rdiv" [.var "price", .var "top"] "ratio") .reverted) :
    ExecFuncBody (config v)
      ({ contract := contract v, locals := clipperStatusLocals tic top } : Frame)
      evm statusFunction.body .reverted := by
  let ageForPrice : UInt256 := UInt256.sub (clipperTimestampWord evm) tic
  let ageForDone : UInt256 := UInt256.sub (clipperTimestampWord evmPrice) tic
  let startFrame : Frame := { contract := contract v, locals := clipperStatusLocals tic top }
  let ageFrame : Frame :=
    { contract := contract v, locals := clipperStatusAgeForPriceLocals tic top ageForPrice }
  let priceFrame : Frame :=
    { contract := contract v, locals := clipperStatusPriceLocals tic top ageForPrice price }
  let ageDoneFrame : Frame :=
    { contract := contract v,
      locals := clipperStatusAgeForDoneLocals tic top ageForPrice price ageForDone }
  let doneFrame : Frame :=
    { contract := contract v, locals := clipperStatusDoneLocals tic top ageForPrice price ageForDone }
  let callStmts :=
    checkedExternalCallStmts (.storage calcRef) "price" (.intLit 0)
      [.var "top", .var "ageForPrice"] "price" (perm := false)
  let elseStmts : List Stmt :=
    [ .internalCall "rdiv" [.var "price", .var "top"] "ratio",
      .assign .localVar (varRef "done")
        (.binary .lt (.var "ratio") (.storage cuspRef)) ]
  let tailStmts : List Stmt :=
    [ .internalCall "sub" [.env .timestamp, .var "tic"] "ageForDone",
      .letDecl "done" (some boolTy) (.boolLit false),
      .ite (.binary .gt (.var "ageForDone") (.storage tailRef))
        [ .assign .localVar (varRef "done") (.boolLit true) ] elseStmts,
      .return [.var "done", .var "price"] ]
  have hsubPrice :
      ExecBlock (config v) startFrame evm
        [ .internalCall "sub" [.env .timestamp, .var "tic"] "ageForPrice" ]
        (.ok ageFrame evm) := by
    exact ExecBlock.consNormal
      (by
        simpa [startFrame, ageFrame, ageForPrice] using
          clipperStatusAgeForPriceCallReturns v evm tic top hlePrice)
      ExecBlock.nil
  have hcallBlock :
      ExecBlock (config v) ageFrame evm callStmts (.ok priceFrame evmPrice) := by
    simpa [ageFrame, priceFrame, callStmts, ageForPrice] using
      clipperStatusPriceCallReturns v (evm := evm) (evm' := evmPrice)
        tic top ageForPrice price hcode hcall hdec
  have hsubDone :
      ExecStmt (config v) priceFrame evmPrice
        (.internalCall "sub" [.env .timestamp, .var "tic"] "ageForDone")
        (.ok ageDoneFrame evmPrice) := by
    simpa [priceFrame, ageDoneFrame, ageForDone, ageForPrice] using
      clipperStatusAgeForDoneCallReturns v evmPrice tic top ageForPrice price hleDone
  have hletDone :
      ExecStmt (config v) ageDoneFrame evmPrice
        (.letDecl "done" (some boolTy) (.boolLit false))
        (.ok doneFrame evmPrice) := by
    simpa [ageDoneFrame, doneFrame] using
      clipperStatusLetDoneFalse v evmPrice tic top ageForPrice price ageForDone
  have helse : ExecBlock (config v) doneFrame evmPrice elseStmts .reverted := by
    simpa [doneFrame, elseStmts, ageForPrice, ageForDone] using ExecBlock.consRevert hrdiv
  have hite :
      ExecStmt (config v) doneFrame evmPrice
        (.ite (.binary .gt (.var "ageForDone") (.storage tailRef))
          [ .assign .localVar (varRef "done") (.boolLit true) ] elseStmts)
        .reverted := by
    exact ExecStmt.iteFalse
      (by simpa [doneFrame, ageForDone] using
        (clipperEvalStatusDoneTailCond_false v evmPrice tic top ageForPrice price ageForDone
          htail))
      helse
  have hbranch :
      ExecBlock (config v) doneFrame evmPrice
        [ .ite (.binary .gt (.var "ageForDone") (.storage tailRef))
            [ .assign .localVar (varRef "done") (.boolLit true) ] elseStmts,
          .return [.var "done", .var "price"] ]
        .reverted := by
    exact ExecBlock.consRevert hite
  have htailBlock :
      ExecBlock (config v) priceFrame evmPrice tailStmts .reverted := by
    simpa [tailStmts, doneFrame] using
      ExecBlock.consNormal (solm' := ageDoneFrame) (evm' := evmPrice) hsubDone <|
        ExecBlock.consNormal (solm' := doneFrame) (evm' := evmPrice) hletDone hbranch
  have hcallTail :
      ExecBlock (config v) ageFrame evm (callStmts ++ tailStmts) .reverted :=
   execBlock_append (s2 := tailStmts) hcallBlock htailBlock
  have hbody :
      ExecBlock (config v) startFrame evm
        ([ .internalCall "sub" [.env .timestamp, .var "tic"] "ageForPrice" ] ++
          callStmts ++ tailStmts)
        .reverted :=
   execBlock_append (s2 := callStmts ++ tailStmts) hsubPrice hcallTail
  apply ExecFuncBody.execBlockRevert
  simpa [statusFunction, checkedExternalCallStmts, startFrame, callStmts, elseStmts, tailStmts]
    using hbody

theorem clipperStatusFunctionRevertsRdivMul (v : ClipperImmutables)
    {evm evmPrice : EVM.State} (tic top price : UInt256) {out : ByteArray}
    (hlePrice : tic.toNat ≤ (clipperTimestampWord evm).toNat)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0
        [.int (Int.ofNat top.toNat),
          .int (Int.ofNat (UInt256.sub (clipperTimestampWord evm) tic).toNat)]
        (true, evmPrice, out) false)
    (hdec : (config v).externalABI.decode? "price" out =
      some [.int (Int.ofNat price.toNat)])
    (hleDone : tic.toNat ≤ (clipperTimestampWord evmPrice).toNat)
    (htail :
      (UInt256.sub (clipperTimestampWord evmPrice) tic).toNat ≤
        (clipperStatusTailWord evmPrice).toNat)
    (hover : UInt256.size ≤ price.toNat * clipperRayWord.toNat) :
    ExecFuncBody (config v)
      ({ contract := contract v, locals := clipperStatusLocals tic top } : Frame)
      evm statusFunction.body .reverted := by
  let ageForPrice : UInt256 := UInt256.sub (clipperTimestampWord evm) tic
  let ageForDone : UInt256 := UInt256.sub (clipperTimestampWord evmPrice) tic
  have hrdiv :
      ExecStmt (config v)
        ({ contract := contract v, locals :=
          clipperStatusDoneLocals tic top ageForPrice price ageForDone } : Frame)
        evmPrice (.internalCall "rdiv" [.var "price", .var "top"] "ratio") .reverted := by
    simpa [ageForPrice, ageForDone] using
      clipperStatusRdivCallRevertsMul v evmPrice tic top ageForPrice price ageForDone hover
  exact clipperStatusFunctionRevertsRdivCore v tic top price hlePrice hcode hcall hdec
    hleDone htail (by simpa [ageForPrice, ageForDone] using hrdiv)

theorem clipperStatusFunctionRevertsRdivDivZero (v : ClipperImmutables)
    {evm evmPrice : EVM.State} (tic top price : UInt256) {out : ByteArray}
    (hlePrice : tic.toNat ≤ (clipperTimestampWord evm).toNat)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0
        [.int (Int.ofNat top.toNat),
          .int (Int.ofNat (UInt256.sub (clipperTimestampWord evm) tic).toNat)]
        (true, evmPrice, out) false)
    (hdec : (config v).externalABI.decode? "price" out =
      some [.int (Int.ofNat price.toNat)])
    (hleDone : tic.toNat ≤ (clipperTimestampWord evmPrice).toNat)
    (htail :
      (UInt256.sub (clipperTimestampWord evmPrice) tic).toNat ≤
        (clipperStatusTailWord evmPrice).toNat)
    (hmul : price.toNat * clipperRayWord.toNat < UInt256.size)
    (htop : top = ⟨0⟩) :
    ExecFuncBody (config v)
      ({ contract := contract v, locals := clipperStatusLocals tic top } : Frame)
      evm statusFunction.body .reverted := by
  let ageForPrice : UInt256 := UInt256.sub (clipperTimestampWord evm) tic
  let ageForDone : UInt256 := UInt256.sub (clipperTimestampWord evmPrice) tic
  have hrdiv :
      ExecStmt (config v)
        ({ contract := contract v, locals :=
          clipperStatusDoneLocals tic top ageForPrice price ageForDone } : Frame)
        evmPrice (.internalCall "rdiv" [.var "price", .var "top"] "ratio") .reverted := by
    simpa [ageForPrice, ageForDone] using
      clipperStatusRdivCallRevertsDivZero v evmPrice tic top ageForPrice price ageForDone
        hmul htop
  exact clipperStatusFunctionRevertsRdivCore v tic top price hlePrice hcode hcall hdec
    hleDone htail (by simpa [ageForPrice, ageForDone] using hrdiv)

theorem clipperGetStatusStatusCallRevertsAgeForPrice (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv)
    (hlt : (clipperTimestampWord evm).toNat < (clipperGetStatusTicWord evm I).toNat) :
    ExecStmt (config v)
      { contract := contract v, locals := clipperGetStatusLocalsTic evm I } evm
      (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
      .reverted :=
  internalCallFunctionRevert
    (cfg := config v)
    (caller := { contract := contract v, locals := clipperGetStatusLocalsTic evm I })
    (evm := evm)
    (name := "status") (retVar := "st")
    (args := [.var "tic", .storage (salesF (.var "id") "top")])
    (argVals := [.int (Int.ofNat (clipperGetStatusTicWord evm I).toNat),
      .int (Int.ofNat (clipperGetStatusTopWord evm I).toNat)])
    (callee := statusFunction)
    (locals := clipperStatusLocals (clipperGetStatusTicWord evm I)
      (clipperGetStatusTopWord evm I))
    (clipperEvalGetStatusStatusArgs v evm I)
    (clipperLookupStatusFunction v)
    (clipperBindParamsStatus (clipperGetStatusTicWord evm I)
      (clipperGetStatusTopWord evm I))
    (clipperStatusFunctionRevertsAgeForPrice v evm
      (clipperGetStatusTicWord evm I) (clipperGetStatusTopWord evm I) hlt)

theorem clipperGetStatusStatusCallRevertsPriceCallFailure (v : ClipperImmutables)
    {evm evmPrice : EVM.State} (I : ExecutionEnv) {out : ByteArray}
    (hlePrice : (clipperGetStatusTicWord evm I).toNat ≤ (clipperTimestampWord evm).toNat)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0
        [.int (Int.ofNat (clipperGetStatusTopWord evm I).toNat),
          .int (Int.ofNat
            (UInt256.sub (clipperTimestampWord evm) (clipperGetStatusTicWord evm I)).toNat)]
        (false, evmPrice, out) false) :
    ExecStmt (config v)
      { contract := contract v, locals := clipperGetStatusLocalsTic evm I } evm
      (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
      .reverted :=
  internalCallFunctionRevert
    (cfg := config v)
    (caller := { contract := contract v, locals := clipperGetStatusLocalsTic evm I })
    (evm := evm)
    (name := "status") (retVar := "st")
    (args := [.var "tic", .storage (salesF (.var "id") "top")])
    (argVals := [.int (Int.ofNat (clipperGetStatusTicWord evm I).toNat),
      .int (Int.ofNat (clipperGetStatusTopWord evm I).toNat)])
    (callee := statusFunction)
    (locals := clipperStatusLocals (clipperGetStatusTicWord evm I)
      (clipperGetStatusTopWord evm I))
    (clipperEvalGetStatusStatusArgs v evm I)
    (clipperLookupStatusFunction v)
    (clipperBindParamsStatus (clipperGetStatusTicWord evm I)
      (clipperGetStatusTopWord evm I))
    (clipperStatusFunctionRevertsPriceCallFailure v
      (clipperGetStatusTicWord evm I) (clipperGetStatusTopWord evm I)
      hlePrice hcode hcall)

theorem clipperGetStatusStatusCallRevertsPriceNoCode (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv)
    (hlePrice : (clipperGetStatusTicWord evm I).toNat ≤ (clipperTimestampWord evm).toNat)
    (hnoCode :
      (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat = 0) :
    ExecStmt (config v)
      { contract := contract v, locals := clipperGetStatusLocalsTic evm I } evm
      (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
      .reverted :=
  internalCallFunctionRevert
    (cfg := config v)
    (caller := { contract := contract v, locals := clipperGetStatusLocalsTic evm I })
    (evm := evm)
    (name := "status") (retVar := "st")
    (args := [.var "tic", .storage (salesF (.var "id") "top")])
    (argVals := [.int (Int.ofNat (clipperGetStatusTicWord evm I).toNat),
      .int (Int.ofNat (clipperGetStatusTopWord evm I).toNat)])
    (callee := statusFunction)
    (locals := clipperStatusLocals (clipperGetStatusTicWord evm I)
      (clipperGetStatusTopWord evm I))
    (clipperEvalGetStatusStatusArgs v evm I)
    (clipperLookupStatusFunction v)
    (clipperBindParamsStatus (clipperGetStatusTicWord evm I)
      (clipperGetStatusTopWord evm I))
    (clipperStatusFunctionRevertsPriceNoCode v evm
      (clipperGetStatusTicWord evm I) (clipperGetStatusTopWord evm I)
      hlePrice hnoCode)

theorem clipperGetStatusStatusCallRevertsPriceDecode (v : ClipperImmutables)
    {evm evmPrice : EVM.State} (I : ExecutionEnv) {out : ByteArray}
    (hlePrice : (clipperGetStatusTicWord evm I).toNat ≤ (clipperTimestampWord evm).toNat)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0
        [.int (Int.ofNat (clipperGetStatusTopWord evm I).toNat),
          .int (Int.ofNat
            (UInt256.sub (clipperTimestampWord evm) (clipperGetStatusTicWord evm I)).toNat)]
        (true, evmPrice, out) false)
    (hdec : (config v).externalABI.decode? "price" out = none) :
    ExecStmt (config v)
      { contract := contract v, locals := clipperGetStatusLocalsTic evm I } evm
      (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
      .reverted :=
  internalCallFunctionRevert
    (cfg := config v)
    (caller := { contract := contract v, locals := clipperGetStatusLocalsTic evm I })
    (evm := evm)
    (name := "status") (retVar := "st")
    (args := [.var "tic", .storage (salesF (.var "id") "top")])
    (argVals := [.int (Int.ofNat (clipperGetStatusTicWord evm I).toNat),
      .int (Int.ofNat (clipperGetStatusTopWord evm I).toNat)])
    (callee := statusFunction)
    (locals := clipperStatusLocals (clipperGetStatusTicWord evm I)
      (clipperGetStatusTopWord evm I))
    (clipperEvalGetStatusStatusArgs v evm I)
    (clipperLookupStatusFunction v)
    (clipperBindParamsStatus (clipperGetStatusTicWord evm I)
      (clipperGetStatusTopWord evm I))
    (clipperStatusFunctionRevertsPriceDecode v
      (clipperGetStatusTicWord evm I) (clipperGetStatusTopWord evm I)
      hlePrice hcode hcall hdec)

theorem clipperGetStatusStatusCallRevertsAgeForDone (v : ClipperImmutables)
    {evm evmPrice : EVM.State} (I : ExecutionEnv) (price : UInt256) {out : ByteArray}
    (hlePrice : (clipperGetStatusTicWord evm I).toNat ≤ (clipperTimestampWord evm).toNat)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0
        [.int (Int.ofNat (clipperGetStatusTopWord evm I).toNat),
          .int (Int.ofNat
            (UInt256.sub (clipperTimestampWord evm) (clipperGetStatusTicWord evm I)).toNat)]
        (true, evmPrice, out) false)
    (hdec : (config v).externalABI.decode? "price" out =
      some [.int (Int.ofNat price.toNat)])
    (hltDone : (clipperTimestampWord evmPrice).toNat < (clipperGetStatusTicWord evm I).toNat) :
    ExecStmt (config v)
      { contract := contract v, locals := clipperGetStatusLocalsTic evm I } evm
      (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
      .reverted :=
  internalCallFunctionRevert
    (cfg := config v)
    (caller := { contract := contract v, locals := clipperGetStatusLocalsTic evm I })
    (evm := evm)
    (name := "status") (retVar := "st")
    (args := [.var "tic", .storage (salesF (.var "id") "top")])
    (argVals := [.int (Int.ofNat (clipperGetStatusTicWord evm I).toNat),
      .int (Int.ofNat (clipperGetStatusTopWord evm I).toNat)])
    (callee := statusFunction)
    (locals := clipperStatusLocals (clipperGetStatusTicWord evm I)
      (clipperGetStatusTopWord evm I))
    (clipperEvalGetStatusStatusArgs v evm I)
    (clipperLookupStatusFunction v)
    (clipperBindParamsStatus (clipperGetStatusTicWord evm I)
      (clipperGetStatusTopWord evm I))
    (clipperStatusFunctionRevertsAgeForDone v
      (clipperGetStatusTicWord evm I) (clipperGetStatusTopWord evm I) price
      hlePrice hcode hcall hdec hltDone)

theorem clipperGetStatusStatusCallRevertsRdivMul (v : ClipperImmutables)
    {evm evmPrice : EVM.State} (I : ExecutionEnv) (price : UInt256) {out : ByteArray}
    (hlePrice : (clipperGetStatusTicWord evm I).toNat ≤ (clipperTimestampWord evm).toNat)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0
        [.int (Int.ofNat (clipperGetStatusTopWord evm I).toNat),
          .int (Int.ofNat
            (UInt256.sub (clipperTimestampWord evm) (clipperGetStatusTicWord evm I)).toNat)]
        (true, evmPrice, out) false)
    (hdec : (config v).externalABI.decode? "price" out =
      some [.int (Int.ofNat price.toNat)])
    (hleDone : (clipperGetStatusTicWord evm I).toNat ≤ (clipperTimestampWord evmPrice).toNat)
    (htail :
      (UInt256.sub (clipperTimestampWord evmPrice) (clipperGetStatusTicWord evm I)).toNat ≤
        (clipperStatusTailWord evmPrice).toNat)
    (hover : UInt256.size ≤ price.toNat * clipperRayWord.toNat) :
    ExecStmt (config v)
      { contract := contract v, locals := clipperGetStatusLocalsTic evm I } evm
      (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
      .reverted :=
  internalCallFunctionRevert
    (cfg := config v)
    (caller := { contract := contract v, locals := clipperGetStatusLocalsTic evm I })
    (evm := evm)
    (name := "status") (retVar := "st")
    (args := [.var "tic", .storage (salesF (.var "id") "top")])
    (argVals := [.int (Int.ofNat (clipperGetStatusTicWord evm I).toNat),
      .int (Int.ofNat (clipperGetStatusTopWord evm I).toNat)])
    (callee := statusFunction)
    (locals := clipperStatusLocals (clipperGetStatusTicWord evm I)
      (clipperGetStatusTopWord evm I))
    (clipperEvalGetStatusStatusArgs v evm I)
    (clipperLookupStatusFunction v)
    (clipperBindParamsStatus (clipperGetStatusTicWord evm I)
      (clipperGetStatusTopWord evm I))
    (clipperStatusFunctionRevertsRdivMul v
      (clipperGetStatusTicWord evm I) (clipperGetStatusTopWord evm I) price
      hlePrice hcode hcall hdec hleDone htail hover)

theorem clipperGetStatusStatusCallRevertsRdivDivZero (v : ClipperImmutables)
    {evm evmPrice : EVM.State} (I : ExecutionEnv) (price : UInt256) {out : ByteArray}
    (hlePrice : (clipperGetStatusTicWord evm I).toNat ≤ (clipperTimestampWord evm).toNat)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0
        [.int (Int.ofNat (clipperGetStatusTopWord evm I).toNat),
          .int (Int.ofNat
            (UInt256.sub (clipperTimestampWord evm) (clipperGetStatusTicWord evm I)).toNat)]
        (true, evmPrice, out) false)
    (hdec : (config v).externalABI.decode? "price" out =
      some [.int (Int.ofNat price.toNat)])
    (hleDone : (clipperGetStatusTicWord evm I).toNat ≤ (clipperTimestampWord evmPrice).toNat)
    (htail :
      (UInt256.sub (clipperTimestampWord evmPrice) (clipperGetStatusTicWord evm I)).toNat ≤
        (clipperStatusTailWord evmPrice).toNat)
    (hmul : price.toNat * clipperRayWord.toNat < UInt256.size)
    (htop : clipperGetStatusTopWord evm I = ⟨0⟩) :
    ExecStmt (config v)
      { contract := contract v, locals := clipperGetStatusLocalsTic evm I } evm
      (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
      .reverted :=
  internalCallFunctionRevert
    (cfg := config v)
    (caller := { contract := contract v, locals := clipperGetStatusLocalsTic evm I })
    (evm := evm)
    (name := "status") (retVar := "st")
    (args := [.var "tic", .storage (salesF (.var "id") "top")])
    (argVals := [.int (Int.ofNat (clipperGetStatusTicWord evm I).toNat),
      .int (Int.ofNat (clipperGetStatusTopWord evm I).toNat)])
    (callee := statusFunction)
    (locals := clipperStatusLocals (clipperGetStatusTicWord evm I)
      (clipperGetStatusTopWord evm I))
    (clipperEvalGetStatusStatusArgs v evm I)
    (clipperLookupStatusFunction v)
    (clipperBindParamsStatus (clipperGetStatusTicWord evm I)
      (clipperGetStatusTopWord evm I))
    (clipperStatusFunctionRevertsRdivDivZero v
      (clipperGetStatusTicWord evm I) (clipperGetStatusTopWord evm I) price
      hlePrice hcode hcall hdec hleDone htail hmul htop)

private theorem clipperGetStatusBodyRevertsAtStatusCall (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hstatus :
      ExecStmt (config v)
        { contract := contract v, locals := clipperGetStatusLocalsTic evm I } evm
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        .reverted) :
    ExecTransitionBody (config v) (contract v) evm (clipperGetStatusStore I)
      getStatusTransition.body .reverted := by
  let startFrame : Frame := { contract := contract v, locals := clipperGetStatusStore I }
  let usrFrame : Frame := { contract := contract v, locals := clipperGetStatusLocalsUsr evm I }
  let ticFrame : Frame := { contract := contract v, locals := clipperGetStatusLocalsTic evm I }
  have hletUsr :
      ExecStmt (config v) startFrame evm
        (.letDecl "usr" (some addr) (.storage (salesF (.var "id") "usr")))
        (.ok usrFrame evm) := by
    simpa [startFrame, usrFrame, clipperGetStatusLocalsUsr] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := startFrame) (evm := evm) (name := "usr")
        (ty := some addr) (expr := .storage (salesF (.var "id") "usr"))
        (value := .address (AccountAddress.ofNat (clipperGetStatusUsrWord evm I).toNat))
        (by simpa [startFrame, clipperGetStatusUsrWord] using
          clipperEvalGetStatusSalesUsr v evm I))
  have hletTic :
      ExecStmt (config v) usrFrame evm
        (.letDecl "tic" (some uint96) (.storage (salesF (.var "id") "tic")))
        (.ok ticFrame evm) := by
    simpa [usrFrame, ticFrame, clipperGetStatusLocalsTic] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := usrFrame) (evm := evm) (name := "tic")
        (ty := some uint96) (expr := .storage (salesF (.var "id") "tic"))
        (value := .int (Int.ofNat (clipperGetStatusTicWord evm I).toNat))
        (by simpa [usrFrame] using clipperEvalGetStatusSalesTicAfterUsr v evm I))
  simpa [getStatusTransition, nonpayable, startFrame, ticFrame] using
    (ExecFuncBody.execBlockRevert <|
      ExecBlock.consNormal (solm' := startFrame) (evm' := evm)
        (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (solm' := usrFrame) (evm' := evm) hletUsr <|
      ExecBlock.consNormal (solm' := ticFrame) (evm' := evm) hletTic <|
      ExecBlock.consRevert hstatus)

theorem clipperGetStatusBodyRevertsAgeForPrice (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlt : (clipperTimestampWord evm).toNat < (clipperGetStatusTicWord evm I).toNat) :
    ExecTransitionBody (config v) (contract v) evm (clipperGetStatusStore I)
      getStatusTransition.body .reverted :=
  clipperGetStatusBodyRevertsAtStatusCall v evm I hwv
    (clipperGetStatusStatusCallRevertsAgeForPrice v evm I hlt)

theorem clipperGetStatusBodyRevertsPriceCallFailure (v : ClipperImmutables)
    {evm evmPrice : EVM.State} (I : ExecutionEnv) {out : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlePrice : (clipperGetStatusTicWord evm I).toNat ≤ (clipperTimestampWord evm).toNat)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0
        [.int (Int.ofNat (clipperGetStatusTopWord evm I).toNat),
          .int (Int.ofNat
            (UInt256.sub (clipperTimestampWord evm) (clipperGetStatusTicWord evm I)).toNat)]
        (false, evmPrice, out) false) :
    ExecTransitionBody (config v) (contract v) evm (clipperGetStatusStore I)
      getStatusTransition.body .reverted := by
  let startFrame : Frame := { contract := contract v, locals := clipperGetStatusStore I }
  let usrFrame : Frame := { contract := contract v, locals := clipperGetStatusLocalsUsr evm I }
  let ticFrame : Frame := { contract := contract v, locals := clipperGetStatusLocalsTic evm I }
  have hletUsr :
      ExecStmt (config v) startFrame evm
        (.letDecl "usr" (some addr) (.storage (salesF (.var "id") "usr")))
        (.ok usrFrame evm) := by
    simpa [startFrame, usrFrame, clipperGetStatusLocalsUsr] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := startFrame) (evm := evm) (name := "usr")
        (ty := some addr) (expr := .storage (salesF (.var "id") "usr"))
        (value := .address (AccountAddress.ofNat (clipperGetStatusUsrWord evm I).toNat))
        (by simpa [startFrame, clipperGetStatusUsrWord] using
          clipperEvalGetStatusSalesUsr v evm I))
  have hletTic :
      ExecStmt (config v) usrFrame evm
        (.letDecl "tic" (some uint96) (.storage (salesF (.var "id") "tic")))
        (.ok ticFrame evm) := by
    simpa [usrFrame, ticFrame, clipperGetStatusLocalsTic] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := usrFrame) (evm := evm) (name := "tic")
        (ty := some uint96) (expr := .storage (salesF (.var "id") "tic"))
        (value := .int (Int.ofNat (clipperGetStatusTicWord evm I).toNat))
        (by simpa [usrFrame] using clipperEvalGetStatusSalesTicAfterUsr v evm I))
  have hstatus :
      ExecStmt (config v) ticFrame evm
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        .reverted := by
    simpa [ticFrame] using
      clipperGetStatusStatusCallRevertsPriceCallFailure v I hlePrice hcode hcall
  simpa [getStatusTransition, nonpayable, startFrame] using
    (ExecFuncBody.execBlockRevert <|
      ExecBlock.consNormal (solm' := startFrame) (evm' := evm)
        (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (solm' := usrFrame) (evm' := evm) hletUsr <|
      ExecBlock.consNormal (solm' := ticFrame) (evm' := evm) hletTic <|
      ExecBlock.consRevert hstatus)

theorem clipperGetStatusBodyRevertsPriceNoCode (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlePrice : (clipperGetStatusTicWord evm I).toNat ≤ (clipperTimestampWord evm).toNat)
    (hnoCode :
      (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat = 0) :
    ExecTransitionBody (config v) (contract v) evm (clipperGetStatusStore I)
      getStatusTransition.body .reverted :=
  clipperGetStatusBodyRevertsAtStatusCall v evm I hwv
    (clipperGetStatusStatusCallRevertsPriceNoCode v evm I hlePrice hnoCode)

theorem clipperGetStatusBodyRevertsPriceDecode (v : ClipperImmutables)
    {evm evmPrice : EVM.State} (I : ExecutionEnv) {out : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlePrice : (clipperGetStatusTicWord evm I).toNat ≤ (clipperTimestampWord evm).toNat)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0
        [.int (Int.ofNat (clipperGetStatusTopWord evm I).toNat),
          .int (Int.ofNat
            (UInt256.sub (clipperTimestampWord evm) (clipperGetStatusTicWord evm I)).toNat)]
        (true, evmPrice, out) false)
    (hdec : (config v).externalABI.decode? "price" out = none) :
    ExecTransitionBody (config v) (contract v) evm (clipperGetStatusStore I)
      getStatusTransition.body .reverted :=
  clipperGetStatusBodyRevertsAtStatusCall v evm I hwv
    (clipperGetStatusStatusCallRevertsPriceDecode v I hlePrice hcode hcall hdec)

theorem clipperGetStatusBodyRevertsAgeForDone (v : ClipperImmutables)
    {evm evmPrice : EVM.State} (I : ExecutionEnv) (price : UInt256) {out : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlePrice : (clipperGetStatusTicWord evm I).toNat ≤ (clipperTimestampWord evm).toNat)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0
        [.int (Int.ofNat (clipperGetStatusTopWord evm I).toNat),
          .int (Int.ofNat
            (UInt256.sub (clipperTimestampWord evm) (clipperGetStatusTicWord evm I)).toNat)]
        (true, evmPrice, out) false)
    (hdec : (config v).externalABI.decode? "price" out =
      some [.int (Int.ofNat price.toNat)])
    (hltDone : (clipperTimestampWord evmPrice).toNat < (clipperGetStatusTicWord evm I).toNat) :
    ExecTransitionBody (config v) (contract v) evm (clipperGetStatusStore I)
      getStatusTransition.body .reverted :=
  clipperGetStatusBodyRevertsAtStatusCall v evm I hwv
    (clipperGetStatusStatusCallRevertsAgeForDone v I price hlePrice hcode hcall hdec hltDone)

theorem clipperGetStatusBodyRevertsRdivMul (v : ClipperImmutables)
    {evm evmPrice : EVM.State} (I : ExecutionEnv) (price : UInt256) {out : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlePrice : (clipperGetStatusTicWord evm I).toNat ≤ (clipperTimestampWord evm).toNat)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0
        [.int (Int.ofNat (clipperGetStatusTopWord evm I).toNat),
          .int (Int.ofNat
            (UInt256.sub (clipperTimestampWord evm) (clipperGetStatusTicWord evm I)).toNat)]
        (true, evmPrice, out) false)
    (hdec : (config v).externalABI.decode? "price" out =
      some [.int (Int.ofNat price.toNat)])
    (hleDone : (clipperGetStatusTicWord evm I).toNat ≤ (clipperTimestampWord evmPrice).toNat)
    (htail :
      (UInt256.sub (clipperTimestampWord evmPrice) (clipperGetStatusTicWord evm I)).toNat ≤
        (clipperStatusTailWord evmPrice).toNat)
    (hover : UInt256.size ≤ price.toNat * clipperRayWord.toNat) :
    ExecTransitionBody (config v) (contract v) evm (clipperGetStatusStore I)
      getStatusTransition.body .reverted :=
  clipperGetStatusBodyRevertsAtStatusCall v evm I hwv
    (clipperGetStatusStatusCallRevertsRdivMul v I price hlePrice hcode hcall hdec hleDone
      htail hover)

theorem clipperGetStatusBodyRevertsRdivDivZero (v : ClipperImmutables)
    {evm evmPrice : EVM.State} (I : ExecutionEnv) (price : UInt256) {out : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlePrice : (clipperGetStatusTicWord evm I).toNat ≤ (clipperTimestampWord evm).toNat)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0
        [.int (Int.ofNat (clipperGetStatusTopWord evm I).toNat),
          .int (Int.ofNat
            (UInt256.sub (clipperTimestampWord evm) (clipperGetStatusTicWord evm I)).toNat)]
        (true, evmPrice, out) false)
    (hdec : (config v).externalABI.decode? "price" out =
      some [.int (Int.ofNat price.toNat)])
    (hleDone : (clipperGetStatusTicWord evm I).toNat ≤ (clipperTimestampWord evmPrice).toNat)
    (htail :
      (UInt256.sub (clipperTimestampWord evmPrice) (clipperGetStatusTicWord evm I)).toNat ≤
        (clipperStatusTailWord evmPrice).toNat)
    (hmul : price.toNat * clipperRayWord.toNat < UInt256.size)
    (htop : clipperGetStatusTopWord evm I = ⟨0⟩) :
    ExecTransitionBody (config v) (contract v) evm (clipperGetStatusStore I)
      getStatusTransition.body .reverted :=
  clipperGetStatusBodyRevertsAtStatusCall v evm I hwv
    (clipperGetStatusStatusCallRevertsRdivDivZero v I price hlePrice hcode hcall hdec
      hleDone htail hmul htop)

end Benchmarks.Dss.Clipper
