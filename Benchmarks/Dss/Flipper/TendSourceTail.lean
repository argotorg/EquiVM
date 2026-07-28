import Benchmarks.Dss.Flipper.TendTail

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxHeartbeats 0

namespace Benchmarks.Dss.Flipper

/-! ## Source tail helpers for `tend(uint256,uint256,uint256)` -/

abbrev tendAfterIncreasePayTailStmts : List Stmt :=
  checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
    [sender, .storage (bidsF (.var "id") "gal"),
      wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))]
    "_payRet" ++
  [ .assign .storage (bidsF (.var "id") "bid") (.var "bid") ] ++
  checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
  [ .assign .storage (bidsF (.var "id") "tic") (.var "tic_") ]

theorem flipperTendX_payDepthLimit {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem rdata : ByteArray}
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperVatTargetWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth = (1024 : Fin 1025))
    (h : RD flipperBytecode I g s0 ⟨3686⟩ [tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 3) rdata (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨3800⟩
      (⟨0⟩ :: ⟨228⟩ :: ⟨3140843579⟩ ::
        flipperVatTargetWord σ I :: tendBid I :: tendLot I :: tendId I :: ret :: sel :: [])
      (tendVatPayCallMem mem σ I) (UInt256.ofNat 8) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨gasWord, _, _, rd3799⟩ :=
    flipperTendX_toPayCall hmemSize hmemRead64 hcodeSize h
  obtain ⟨k3800, C3800, rd3800raw⟩ :=
    RD.callDepthLimit rd3799 (by native_decide) hdepth (by evm_ov)
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
        (⟨128⟩ : UInt256).toNat (⟨100⟩ : UInt256).toNat)
        (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 8 := by
    native_decide
  have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    rfl
  have rd3800 : RD flipperBytecode I g s0 ⟨3800⟩
      (⟨0⟩ :: ⟨228⟩ :: ⟨3140843579⟩ ::
        flipperVatTargetWord σ I :: tendBid I :: tendLot I :: tendId I :: ret :: sel :: [])
      (ByteArray.empty.write 0 (tendVatPayCallMem mem σ I) 128
        (min (⟨0⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat)
      (UInt256.ofNat 8) ByteArray.empty (cA, σ) k3800 C3800 := by
    simpa using haw ▸ rd3800raw
  rw [hmin, byteArray_write_len_zero] at rd3800
  exact ⟨_, _, rd3800⟩

theorem flipperTendSourceBlockAfterIncreaseSameCallerTail {cA gh bl σ σ₀ A I}
    {g : UInt256} {r : ExecResult}
    (hwv : I.weiValue = ⟨0⟩)
    (hguy : bidGuyWord (tendId I) σ I ≠ ⟨0⟩)
    (hticGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
          .ok (.bool true))
    (hendGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
          .ok (.bool true))
    (hlotGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
          .ok (.bool true))
    (htabGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .le (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
          .ok (.bool true))
    (hbidGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
          .ok (.bool true))
    (hfitBid : (tendBid I).toNat * flipperONEWord.toNat < UInt256.size)
    (hfitBeg :
      (tendBegWord σ I).toNat * (bidBidWord (tendId I) σ I).toNat < UInt256.size)
    (hinc :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .ge (.var "bidOne") (.var "begBid"))
          (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab")))) =
          .ok (.bool true))
    (hcaller : solcSourceWord I = bidGuyWord (tendId I) σ I)
    (htail :
      ExecBlock config { contract := contract, locals := tendLocalsBidOneBegBid σ I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        tendAfterIncreasePayTailStmts r) :
    let locals := tendLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock config { contract := contract, locals := locals } evm0 tendTransition.body r := by
  intro locals evm0
  have hguyGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) =
          .ok (.bool true) := by
    simpa [locals, evm0] using
      evalExpr_tendGuyNeZero_true (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hguy
  have hmulBid :
      evalExpr? config { contract := contract, locals := locals } evm0
        (mul256 (.var "bid") (.intLit ONE)) =
          .ok (.int (Int.ofNat (tendBidOneWord I).toNat)) := by
    dsimp [locals, evm0]
    exact evalExpr_tendBidOneMul_ok (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hfitBid
  have hreqBid :
      evalExpr? config { contract := contract, locals := tendLocalsBidOne I } evm0
        (.binary .or
          (.binary .eq (.intLit ONE) (.intLit 0))
          (.binary .eq (.binary .div (.var "bidOne") (.intLit ONE)) (.var "bid"))) =
          .ok (.bool true) := by
    simpa [evm0] using
      evalExpr_tendBidOneRequire_ok (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hfitBid
  have hmulBeg :
      evalExpr? config { contract := contract, locals := tendLocalsBidOne I } evm0
        (mul256 (.storage begRef) (.storage (bidsF (.var "id") "bid"))) =
          .ok (.int (Int.ofNat (tendBegBidWord σ I).toNat)) := by
    dsimp [evm0]
    exact evalExpr_tendBegBidMul_ok (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hfitBeg
  have hreqBeg :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        (.binary .or
          (.binary .eq (.storage (bidsF (.var "id") "bid")) (.intLit 0))
          (.binary .eq (.binary .div (.var "begBid")
            (.storage (bidsF (.var "id") "bid"))) (.storage begRef))) =
          .ok (.bool true) := by
    simpa [evm0] using
      evalExpr_tendBegBidRequire_ok (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hfitBeg
  have hcallerFalse :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        (.binary .ne sender (.storage (bidsF (.var "id") "guy"))) =
          .ok (.bool false) := by
    simpa [evm0] using
      evalExpr_tendCallerNeGuy_false (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcaller
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguyGuard) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hticGuard)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hendGuard)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hlotGuard)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using htabGuard)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hbidGuard)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl hmulBid) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreqBid) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl hmulBeg) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreqBeg) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hinc) ?_
  refine ExecBlock.consNormal (ExecStmt.iteFalse hcallerFalse ExecBlock.nil) ?_
  simpa [tendAfterIncreasePayTailStmts] using htail

theorem flipperTendSourceBodyPayNoCodeSameCaller {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hguy : bidGuyWord (tendId I) σ I ≠ ⟨0⟩)
    (hticGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
          .ok (.bool true))
    (hendGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
          .ok (.bool true))
    (hlotGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
          .ok (.bool true))
    (htabGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .le (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
          .ok (.bool true))
    (hbidGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
          .ok (.bool true))
    (hfitBid : (tendBid I).toNat * flipperONEWord.toNat < UInt256.size)
    (hfitBeg :
      (tendBegWord σ I).toNat * (bidBidWord (tendId I) σ I).toNat < UInt256.size)
    (hinc :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .ge (.var "bidOne") (.var "begBid"))
          (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab")))) =
          .ok (.bool true))
    (hcaller : solcSourceWord I = bidGuyWord (tendId I) σ I)
    (hvatNoCode :
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (flipperVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat = 0) :
    let locals := tendLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals tendTransition.body .reverted := by
  intro locals evm0
  have hvat :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        (.storage vatRef) = .ok (.address (flipperVatAddress evm0.accountMap evm0.executionEnv)) := by
    exact evalExpr_flipperStorageVatOfLocals (tendLocalsBidOneBegBid_get_vat σ I)
  have hguardPay :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool false) := by
    apply evalExpr_flipperVatCodeGuard_false_ofLocals hvat
    simpa [evm0, initState] using hvatNoCode
  have hpayBlock :
      ExecBlock config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "gal"),
            wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))]
          "_payRet")
        .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallNoCode (cfg := config) (C := contract) (evm := evm0)
        (locals := tendLocalsBidOneBegBid σ I) (receiver := .storage vatRef)
        (retVar := "_payRet") (name := "move") (sendVal := 0)
        (args := [sender, .storage (bidsF (.var "id") "gal"),
          wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))])
        hguardPay
  have htail :
      ExecBlock config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        tendAfterIncreasePayTailStmts .reverted := by
    exact execBlock_append_term
      (s2 := [ .assign .storage (bidsF (.var "id") "bid") (.var "bid") ] ++
        checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
        [ .assign .storage (bidsF (.var "id") "tic") (.var "tic_") ])
      hpayBlock (by intro f' e' h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 tendTransition.body
        .reverted := by
    simpa [locals, evm0] using
      (flipperTendSourceBlockAfterIncreaseSameCallerTail (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hguy hticGuard
        hendGuard hlotGuard htabGuard hbidGuard hfitBid hfitBeg hinc hcaller htail)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem flipperTendSourceBodyPayCallFailureSameCaller {cA gh bl σ σ₀ A I}
    {g : UInt256} {evmPay : EVM.State} {outPay : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hguy : bidGuyWord (tendId I) σ I ≠ ⟨0⟩)
    (hticGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
          .ok (.bool true))
    (hendGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
          .ok (.bool true))
    (hlotGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
          .ok (.bool true))
    (htabGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .le (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
          .ok (.bool true))
    (hbidGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
          .ok (.bool true))
    (hfitBid : (tendBid I).toNat * flipperONEWord.toNat < UInt256.size)
    (hfitBeg :
      (tendBegWord σ I).toNat * (bidBidWord (tendId I) σ I).toNat < UInt256.size)
    (hinc :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .ge (.var "bidOne") (.var "begBid"))
          (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab")))) =
          .ok (.bool true))
    (hcaller : solcSourceWord I = bidGuyWord (tendId I) σ I)
    (hvatCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (flipperVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallPay :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (flipperVatAddress σ I)) "move" 0
        (tendPayMoveArgValsOf (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I)
        (false, evmPay, outPay) true) :
    let locals := tendLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals tendTransition.body .reverted := by
  intro locals evm0
  have hvat :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        (.storage vatRef) = .ok (.address (flipperVatAddress evm0.accountMap evm0.executionEnv)) := by
    exact evalExpr_flipperStorageVatOfLocals (tendLocalsBidOneBegBid_get_vat σ I)
  have hguardPay :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) := by
    apply evalExpr_flipperVatCodeGuard_true_ofLocals hvat
    simpa [evm0, initState] using hvatCode
  have hargsPay :
      evalExprs? config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        [sender, .storage (bidsF (.var "id") "gal"),
          wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))] =
          .ok (tendPayMoveArgValsOf evm0 I) := by
    exact evalExprs_tendPayMoveArgs_ofLocals
      (tendLocalsBidOneBegBid_get_id σ I)
      (tendLocalsBidOneBegBid_get_bid σ I)
      (tendLocalsBidOneBegBid_get_bids σ I)
  have hcallPay' :
      typedCallViaEVM config evm0
        (EVM.address (flipperVatAddress evm0.accountMap evm0.executionEnv)) "move" 0
        (tendPayMoveArgValsOf evm0 I) (false, evmPay, outPay) true := by
    simpa [evm0, initState] using hcallPay
  have hpayBlock :
      ExecBlock config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "gal"),
            wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))]
          "_payRet")
        .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallFailure (cfg := config) (C := contract) (evm := evm0)
        (evm' := evmPay) (locals := tendLocalsBidOneBegBid σ I)
        (receiver := .storage vatRef) (retVar := "_payRet") (name := "move")
        (target := flipperVatAddress evm0.accountMap evm0.executionEnv) (sendVal := 0)
        (args := [sender, .storage (bidsF (.var "id") "gal"),
          wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))])
        (argVals := tendPayMoveArgValsOf evm0 I) (out := outPay) (perm := true)
        hguardPay hvat hargsPay hcallPay'
  have htail :
      ExecBlock config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        tendAfterIncreasePayTailStmts .reverted := by
    exact execBlock_append_term
      (s2 := [ .assign .storage (bidsF (.var "id") "bid") (.var "bid") ] ++
        checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
        [ .assign .storage (bidsF (.var "id") "tic") (.var "tic_") ])
      hpayBlock (by intro f' e' h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 tendTransition.body
        .reverted := by
    simpa [locals, evm0] using
      (flipperTendSourceBlockAfterIncreaseSameCallerTail (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hguy hticGuard
        hendGuard hlotGuard htabGuard hbidGuard hfitBid hfitBeg hinc hcaller htail)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem flipperTendSourceBodySuccessSameCaller {cA gh bl σ σ₀ A I}
    {g : UInt256} {evmPay : EVM.State} {outPay : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hguy : bidGuyWord (tendId I) σ I ≠ ⟨0⟩)
    (hticGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
          .ok (.bool true))
    (hendGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
          .ok (.bool true))
    (hlotGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
          .ok (.bool true))
    (htabGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .le (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
          .ok (.bool true))
    (hbidGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
          .ok (.bool true))
    (hfitBid : (tendBid I).toNat * flipperONEWord.toNat < UInt256.size)
    (hfitBeg :
      (tendBegWord σ I).toNat * (bidBidWord (tendId I) σ I).toNat < UInt256.size)
    (hinc :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .ge (.var "bidOne") (.var "begBid"))
          (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab")))) =
          .ok (.bool true))
    (hcaller : solcSourceWord I = bidGuyWord (tendId I) σ I)
    (hvatCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (flipperVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallPay :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (flipperVatAddress σ I)) "move" 0
        (tendPayMoveArgValsOf (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I)
        (true, evmPay, outPay) true)
    (hpayTs : evmPay.executionEnv.header.timestamp = I.header.timestamp)
    (hpayOwner : evmPay.executionEnv.codeOwner = I.codeOwner)
    (hfitTic :
      (tendNow48 I).toNat +
          (tendTtlWord
            (Solm.EVM.storageStore evmPay evmPay.executionEnv.codeOwner
              (bidBaseOfWord (tendId I)) (tendBid I)).accountMap I).toNat <
        2 ^ 48) :
    let locals := tendLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evmBid := Solm.EVM.storageStore evmPay evmPay.executionEnv.codeOwner
      (bidBaseOfWord (tendId I)) (tendBid I)
    let evmTic := Solm.EVM.storageStore evmBid evmBid.executionEnv.codeOwner
      (bidPackedSlotOfWord (tendId I))
      (setUint48Offset20Word
        (Solm.EVM.storageLoad evmBid evmBid.executionEnv.codeOwner
          (bidPackedSlotOfWord (tendId I)))
        (tendTicNewWord evmBid.accountMap I))
    ExecTransitionBody config contract evm0 locals tendTransition.body
      (.returned { contract := contract, locals := tendLocalsWithTicFrom σ evmBid.accountMap I }
        evmTic none) := by
  intro locals evm0 evmBid evmTic
  have hvat :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        (.storage vatRef) = .ok (.address (flipperVatAddress evm0.accountMap evm0.executionEnv)) := by
    exact evalExpr_flipperStorageVatOfLocals (tendLocalsBidOneBegBid_get_vat σ I)
  have hguardPay :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) := by
    apply evalExpr_flipperVatCodeGuard_true_ofLocals hvat
    simpa [evm0, initState] using hvatCode
  have hargsPay :
      evalExprs? config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        [sender, .storage (bidsF (.var "id") "gal"),
          wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))] =
          .ok (tendPayMoveArgValsOf evm0 I) := by
    exact evalExprs_tendPayMoveArgs_ofLocals
      (tendLocalsBidOneBegBid_get_id σ I)
      (tendLocalsBidOneBegBid_get_bid σ I)
      (tendLocalsBidOneBegBid_get_bids σ I)
  have hcallPay' :
      typedCallViaEVM config evm0
        (EVM.address (flipperVatAddress evm0.accountMap evm0.executionEnv)) "move" 0
        (tendPayMoveArgValsOf evm0 I) (true, evmPay, outPay) true := by
    simpa [evm0, initState] using hcallPay
  have hdecPay : config.externalABI.decode? "move" outPay = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hpayBlock :
      ExecBlock config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "gal"),
            wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))]
          "_payRet")
        (.ok { contract := contract, locals := tendLocalsAfterPay σ I } evmPay) := by
    simpa [checkedExternalCallStmts, tendLocalsAfterPay] using
      checkedExternalCallSuccess (cfg := config) (C := contract) (evm := evm0)
        (evm' := evmPay) (locals := tendLocalsBidOneBegBid σ I)
        (receiver := .storage vatRef) (retVar := "_payRet") (name := "move")
        (target := flipperVatAddress evm0.accountMap evm0.executionEnv) (sendVal := 0)
        (args := [sender, .storage (bidsF (.var "id") "gal"),
          wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))])
        (argVals := tendPayMoveArgValsOf evm0 I) (out := outPay) (perm := true)
        (value := []) hguardPay hvat hargsPay hcallPay' hdecPay
  have hbidVar :
      evalExpr? config { contract := contract, locals := tendLocalsAfterPay σ I } evmPay
        (.var "bid") = .ok (.int (Int.ofNat (tendBid I).toNat)) := by
    exact evalExpr_varUInt256 (evm := evmPay) (locals := tendLocalsAfterPay σ I)
      (name := "bid") (value := tendBid I) (tendLocalsAfterPay_get_bid σ I)
  have hassignBid :
      assignStorageRef? config { contract := contract, locals := tendLocalsAfterPay σ I } evmPay
        .storage (bidsF (.var "id") "bid") (.int (Int.ofNat (tendBid I).toNat)) =
          .ok ({ contract := contract, locals := tendLocalsAfterPay σ I }, evmBid) := by
    simpa [evmBid] using
      assign_bidBidStorage evmPay (tendId I) (tendBid I)
        (tendLocalsAfterPay_get_id σ I) (tendLocalsAfterPay_get_bids σ I)
  have hletTic :
      evalExpr? config { contract := contract, locals := tendLocalsAfterPay σ I } evmBid
        (wrap48 (.binary .add now48 (.storage ttlRef))) =
          .ok (.int (Int.ofNat (tendTicNewWord evmBid.accountMap I).toNat)) := by
    exact evalExpr_tendTicNew (evm := evmBid) (locals := tendLocalsAfterPay σ I) (I := I)
      (tendLocalsAfterPay_get_ttl σ I)
      (by simpa [evmBid, storageStore_executionEnv] using hpayTs)
      (by simpa [evmBid, storageStore_executionEnv] using hpayOwner)
  have hgeTic :
      evalExpr? config { contract := contract, locals := tendLocalsWithTicFrom σ evmBid.accountMap I }
        evmBid (.binary .ge (.var "tic_") now48) = .ok (.bool true) := by
    exact evalExpr_tendTicNewGeNow_true_from (evm := evmBid)
      (σpre := σ) (σtic := evmBid.accountMap) (I := I)
      (by simpa [evmBid, storageStore_executionEnv] using hpayTs)
      (by simpa [evmBid] using hfitTic)
  have hticVar :
      evalExpr? config { contract := contract, locals := tendLocalsWithTicFrom σ evmBid.accountMap I }
        evmBid (.var "tic_") =
          .ok (.int (Int.ofNat (tendTicNewWord evmBid.accountMap I).toNat)) := by
    exact evalExpr_tendTicVarWithTicFrom (evm := evmBid)
      (σpre := σ) (σtic := evmBid.accountMap) (I := I)
  have hassignTic :
      assignStorageRef? config
          { contract := contract, locals := tendLocalsWithTicFrom σ evmBid.accountMap I }
          evmBid .storage (bidsF (.var "id") "tic")
          (.int (Int.ofNat (tendTicNewWord evmBid.accountMap I).toNat)) =
        .ok ({ contract := contract, locals := tendLocalsWithTicFrom σ evmBid.accountMap I },
          evmTic) := by
    simpa [evmTic] using
      assign_bidTicStorage evmBid (tendId I) (tendTicNewWord evmBid.accountMap I)
        (tendTicNewWord_bound evmBid.accountMap I)
        (tendLocalsWithTicFrom_get_id σ evmBid.accountMap I)
        (tendLocalsWithTicFrom_get_bids σ evmBid.accountMap I)
  have hpost :
      ExecBlock config { contract := contract, locals := tendLocalsAfterPay σ I } evmPay
        ([ .assign .storage (bidsF (.var "id") "bid") (.var "bid") ] ++
          checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
          [ .assign .storage (bidsF (.var "id") "tic") (.var "tic_") ])
        (.ok { contract := contract, locals := tendLocalsWithTicFrom σ evmBid.accountMap I }
          evmTic) := by
    refine ExecBlock.consNormal (ExecStmt.assign hbidVar hassignBid) ?_
    simp only [checkedAdd48Into, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.letDecl hletTic) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hgeTic) ?_
    exact ExecBlock.consNormal (ExecStmt.assign hticVar hassignTic) ExecBlock.nil
  have htail :
      ExecBlock config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        tendAfterIncreasePayTailStmts
        (.ok { contract := contract, locals := tendLocalsWithTicFrom σ evmBid.accountMap I }
          evmTic) := by
    have hjoined :
        ExecBlock config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
          (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
            [sender, .storage (bidsF (.var "id") "gal"),
              wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))]
            "_payRet" ++
          ([ .assign .storage (bidsF (.var "id") "bid") (.var "bid") ] ++
            checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
            [ .assign .storage (bidsF (.var "id") "tic") (.var "tic_") ]))
          (.ok { contract := contract, locals := tendLocalsWithTicFrom σ evmBid.accountMap I }
            evmTic) := by
      exact execBlock_append hpayBlock hpost
    simpa [tendAfterIncreasePayTailStmts, List.append_assoc] using hjoined
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 tendTransition.body
        (.ok { contract := contract, locals := tendLocalsWithTicFrom σ evmBid.accountMap I }
          evmTic) := by
    simpa [locals, evm0] using
      (flipperTendSourceBlockAfterIncreaseSameCallerTail (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hguy hticGuard
        hendGuard hlotGuard htabGuard hbidGuard hfitBid hfitBeg hinc hcaller htail)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockOK hblock

theorem flipperTendSourceBodyAdd48OverflowSameCaller {cA gh bl σ σ₀ A I}
    {g : UInt256} {evmPay : EVM.State} {outPay : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hguy : bidGuyWord (tendId I) σ I ≠ ⟨0⟩)
    (hticGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
          .ok (.bool true))
    (hendGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
          .ok (.bool true))
    (hlotGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
          .ok (.bool true))
    (htabGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .le (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
          .ok (.bool true))
    (hbidGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
          .ok (.bool true))
    (hfitBid : (tendBid I).toNat * flipperONEWord.toNat < UInt256.size)
    (hfitBeg :
      (tendBegWord σ I).toNat * (bidBidWord (tendId I) σ I).toNat < UInt256.size)
    (hinc :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .ge (.var "bidOne") (.var "begBid"))
          (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab")))) =
          .ok (.bool true))
    (hcaller : solcSourceWord I = bidGuyWord (tendId I) σ I)
    (hvatCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (flipperVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallPay :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (flipperVatAddress σ I)) "move" 0
        (tendPayMoveArgValsOf (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I)
        (true, evmPay, outPay) true)
    (hpayTs : evmPay.executionEnv.header.timestamp = I.header.timestamp)
    (hpayOwner : evmPay.executionEnv.codeOwner = I.codeOwner)
    (hoverTic :
      2 ^ 48 ≤
        (tendNow48 I).toNat +
          (tendTtlWord
            (Solm.EVM.storageStore evmPay evmPay.executionEnv.codeOwner
              (bidBaseOfWord (tendId I)) (tendBid I)).accountMap I).toNat) :
    let locals := tendLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals tendTransition.body .reverted := by
  intro locals evm0
  let evmBid := Solm.EVM.storageStore evmPay evmPay.executionEnv.codeOwner
    (bidBaseOfWord (tendId I)) (tendBid I)
  have hvat :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        (.storage vatRef) = .ok (.address (flipperVatAddress evm0.accountMap evm0.executionEnv)) := by
    exact evalExpr_flipperStorageVatOfLocals (tendLocalsBidOneBegBid_get_vat σ I)
  have hguardPay :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) := by
    apply evalExpr_flipperVatCodeGuard_true_ofLocals hvat
    simpa [evm0, initState] using hvatCode
  have hargsPay :
      evalExprs? config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        [sender, .storage (bidsF (.var "id") "gal"),
          wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))] =
          .ok (tendPayMoveArgValsOf evm0 I) := by
    exact evalExprs_tendPayMoveArgs_ofLocals
      (tendLocalsBidOneBegBid_get_id σ I)
      (tendLocalsBidOneBegBid_get_bid σ I)
      (tendLocalsBidOneBegBid_get_bids σ I)
  have hcallPay' :
      typedCallViaEVM config evm0
        (EVM.address (flipperVatAddress evm0.accountMap evm0.executionEnv)) "move" 0
        (tendPayMoveArgValsOf evm0 I) (true, evmPay, outPay) true := by
    simpa [evm0, initState] using hcallPay
  have hdecPay : config.externalABI.decode? "move" outPay = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hpayBlock :
      ExecBlock config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "gal"),
            wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))]
          "_payRet")
        (.ok { contract := contract, locals := tendLocalsAfterPay σ I } evmPay) := by
    simpa [checkedExternalCallStmts, tendLocalsAfterPay] using
      checkedExternalCallSuccess (cfg := config) (C := contract) (evm := evm0)
        (evm' := evmPay) (locals := tendLocalsBidOneBegBid σ I)
        (receiver := .storage vatRef) (retVar := "_payRet") (name := "move")
        (target := flipperVatAddress evm0.accountMap evm0.executionEnv) (sendVal := 0)
        (args := [sender, .storage (bidsF (.var "id") "gal"),
          wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))])
        (argVals := tendPayMoveArgValsOf evm0 I) (out := outPay) (perm := true)
        (value := []) hguardPay hvat hargsPay hcallPay' hdecPay
  have hbidVar :
      evalExpr? config { contract := contract, locals := tendLocalsAfterPay σ I } evmPay
        (.var "bid") = .ok (.int (Int.ofNat (tendBid I).toNat)) := by
    exact evalExpr_varUInt256 (evm := evmPay) (locals := tendLocalsAfterPay σ I)
      (name := "bid") (value := tendBid I) (tendLocalsAfterPay_get_bid σ I)
  have hassignBid :
      assignStorageRef? config { contract := contract, locals := tendLocalsAfterPay σ I } evmPay
        .storage (bidsF (.var "id") "bid") (.int (Int.ofNat (tendBid I).toNat)) =
          .ok ({ contract := contract, locals := tendLocalsAfterPay σ I }, evmBid) := by
    simpa [evmBid] using
      assign_bidBidStorage evmPay (tendId I) (tendBid I)
        (tendLocalsAfterPay_get_id σ I) (tendLocalsAfterPay_get_bids σ I)
  have hletTic :
      evalExpr? config { contract := contract, locals := tendLocalsAfterPay σ I } evmBid
        (wrap48 (.binary .add now48 (.storage ttlRef))) =
          .ok (.int (Int.ofNat (tendTicNewWord evmBid.accountMap I).toNat)) := by
    exact evalExpr_tendTicNew (evm := evmBid) (locals := tendLocalsAfterPay σ I) (I := I)
      (tendLocalsAfterPay_get_ttl σ I)
      (by simpa [evmBid, storageStore_executionEnv] using hpayTs)
      (by simpa [evmBid, storageStore_executionEnv] using hpayOwner)
  have hgeTicFalse :
      evalExpr? config { contract := contract, locals := tendLocalsWithTicFrom σ evmBid.accountMap I }
        evmBid (.binary .ge (.var "tic_") now48) = .ok (.bool false) := by
    have htic := evalExpr_tendTicVarWithTicFrom (evm := evmBid)
      (σpre := σ) (σtic := evmBid.accountMap) (I := I)
    have hnow := evalExpr_tendNow48
      (evm := evmBid) (locals := tendLocalsWithTicFrom σ evmBid.accountMap I) (I := I)
      (by simpa [evmBid, storageStore_executionEnv] using hpayTs)
    have hlt : (tendTicNewWord evmBid.accountMap I).toNat < (tendNow48 I).toNat :=
      tendTicNewWord_lt_now48_overflow (by simpa [evmBid] using hoverTic)
    exact evalExpr_ge_uint256_false htic hnow hlt
  have hpost :
      ExecBlock config { contract := contract, locals := tendLocalsAfterPay σ I } evmPay
        ([ .assign .storage (bidsF (.var "id") "bid") (.var "bid") ] ++
          checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
          [ .assign .storage (bidsF (.var "id") "tic") (.var "tic_") ])
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.assign hbidVar hassignBid) ?_
    simp only [checkedAdd48Into, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.letDecl hletTic) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hgeTicFalse)
  have htail :
      ExecBlock config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        tendAfterIncreasePayTailStmts .reverted := by
    have hjoined :
        ExecBlock config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
          (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
            [sender, .storage (bidsF (.var "id") "gal"),
              wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))]
            "_payRet" ++
          ([ .assign .storage (bidsF (.var "id") "bid") (.var "bid") ] ++
            checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
            [ .assign .storage (bidsF (.var "id") "tic") (.var "tic_") ]))
          .reverted := by
      exact execBlock_append hpayBlock hpost
    simpa [tendAfterIncreasePayTailStmts, List.append_assoc] using hjoined
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 tendTransition.body
        .reverted := by
    simpa [locals, evm0] using
      (flipperTendSourceBlockAfterIncreaseSameCallerTail (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hguy hticGuard
        hendGuard hlotGuard htabGuard hbidGuard hfitBid hfitBeg hinc hcaller htail)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

end Benchmarks.Dss.Flipper
