import Benchmarks.Dss.Clipper.TakeSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

abbrev clipperTakeOweAdjustmentStmt : Stmt :=
  .ite
    (.binary .gt (.var "owe") (.var "tab"))
    [ .assign .localVar (varRef "owe") (.var "tab"),
      .assign .localVar (varRef "slice") (.binary .div (.var "owe") (.var "price")) ]
    [ .ite
      (.binary .and (.binary .lt (.var "owe") (.var "tab"))
        (.binary .lt (.var "slice") (.var "lot")))
      ([ .letDecl "_chost" (some uint256) (.storage chostRef) ] ++
        wrappingSubInto "remainingTab" (.var "tab") (.var "owe") ++
        [ .ite
          (.binary .lt (.var "remainingTab") (.var "_chost"))
          ([ .require (.binary .gt (.var "tab") (.var "_chost")) ] ++
            wrappingSubInto "oweAdjusted" (.var "tab") (.var "_chost") ++
            [ .assign .localVar (varRef "owe") (.var "oweAdjusted"),
              .assign .localVar (varRef "slice")
                (.binary .div (.var "owe") (.var "price")) ])
          [] ])
      [] ]

abbrev clipperTakePostOweFluxStmts (v : ClipperImmutables) : List Stmt :=
  wrappingSubInto "tabNew" (.var "tab") (.var "owe") ++
    wrappingSubInto "lotNew" (.var "lot") (.var "slice") ++
    [ .assign .localVar (varRef "tab") (.var "tabNew"),
      .assign .localVar (varRef "lot") (.var "lotNew") ] ++
    checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
      [ilkExpr v, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet"

abbrev clipperTakeLocalsNoAdjustTabNew (evmLoc evmRead : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe tabNew : UInt256) : Store :=
  (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe).insert
    "tabNew" (.int (Int.ofNat tabNew.toNat))

abbrev clipperTakeLocalsNoAdjustLotNew (evmLoc evmRead : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe tabNew lotNew : UInt256) : Store :=
  (clipperTakeLocalsNoAdjustTabNew evmLoc evmRead I price slice owe0 owe tabNew).insert
    "lotNew" (.int (Int.ofNat lotNew.toNat))

abbrev clipperTakeLocalsNoAdjustTabAssigned (evmLoc evmRead : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe tabNew lotNew : UInt256) : Store :=
  (clipperTakeLocalsNoAdjustLotNew evmLoc evmRead I price slice owe0 owe tabNew
    lotNew).insert "tab" (.int (Int.ofNat tabNew.toNat))

abbrev clipperTakeLocalsNoAdjustLotAssigned (evmLoc evmRead : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe tabNew lotNew : UInt256) : Store :=
  (clipperTakeLocalsNoAdjustTabAssigned evmLoc evmRead I price slice owe0 owe tabNew
    lotNew).insert "lot" (.int (Int.ofNat lotNew.toNat))

theorem clipperEvalTakeTabSubOweAtOwe (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe : UInt256)
    (howeTab : owe.toNat ≤ (clipperTakeSalesTabEVMWord evmRead I).toNat) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe }
      evmRead (wrap256 (.binary .sub (.var "tab") (.var "owe"))) =
      .ok (.int (Int.ofNat (UInt256.sub (clipperTakeSalesTabEVMWord evmRead I) owe).toNat)) := by
  let tab := clipperTakeSalesTabEVMWord evmRead I
  have hsubNat : (UInt256.sub tab owe).toNat = tab.toNat - owe.toNat := by
    exact usub_toNat howeTab
  have hdiff :
      Int.ofNat tab.toNat - Int.ofNat owe.toNat =
        Int.ofNat (tab.toNat - owe.toNat) := by
    exact (Int.ofNat_sub howeTab).symm
  have hltNat : tab.toNat - owe.toNat < UInt256.size := by
    exact lt_of_le_of_lt (Nat.sub_le tab.toNat owe.toNat) tab.val.isLt
  have hlt : Int.ofNat (tab.toNat - owe.toNat) < wordModulus := by
    norm_num [wordModulus, UInt256.size] at hltNat ⊢
    exact_mod_cast hltNat
  have hmod :
      Int.ofNat (tab.toNat - owe.toNat) % wordModulus =
        Int.ofNat (tab.toNat - owe.toNat) := by
    rw [Int.emod_eq_of_lt]
    · exact Int.natCast_nonneg _
    · exact hlt
  have hwordNonzero : ¬wordModulus = 0 := by
    norm_num [wordModulus]
  have hmodLoad :
      (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat -
          Int.ofNat owe.toNat) % wordModulus =
        Int.ofNat ((clipperTakeSalesTabEVMWord evmRead I).toNat - owe.toNat) := by
    rw [show Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat -
        Int.ofNat owe.toNat = Int.ofNat (tab.toNat - owe.toNat) by
      simpa [tab] using hdiff]
    simpa [tab] using hmod
  simp [wrap256, evalExpr?, EvalResult.bind, bind,
    clipperEvalTakeVarTabAtOwe v evmLoc evmRead evmRead I false price slice owe0 owe,
    clipperEvalTakeVarOweAtOwe v evmLoc evmRead evmRead I false price slice owe0 owe,
    evalBinaryOp?, hsubNat, hwordNonzero, tab]
  exact hmodLoad

theorem clipperTakeNoAdjustLetTabNew (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe : UInt256)
    (howeTab : owe.toNat ≤ (clipperTakeSalesTabEVMWord evmRead I).toNat) :
    let tabNew := UInt256.sub (clipperTakeSalesTabEVMWord evmRead I) owe
    ExecStmt (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe))
      evmRead
      (.letDecl "tabNew" (some uint256) (wrap256 (.binary .sub (.var "tab") (.var "owe"))))
      (.ok
        (Frame.mk (contract v)
          (clipperTakeLocalsNoAdjustTabNew evmLoc evmRead I price slice owe0 owe tabNew))
        evmRead) := by
  intro tabNew
  let oweFrame : Frame :=
    Frame.mk (contract v) (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe)
  let tabNewFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsNoAdjustTabNew evmLoc evmRead I price slice owe0 owe tabNew)
  have hrhs :
      evalExpr? (config v) oweFrame evmRead
        (wrap256 (.binary .sub (.var "tab") (.var "owe"))) =
      .ok (.int (Int.ofNat tabNew.toNat)) := by
    simpa [oweFrame, tabNew] using
      clipperEvalTakeTabSubOweAtOwe v evmLoc evmRead I price slice owe0 owe howeTab
  simpa [oweFrame, tabNewFrame, clipperTakeLocalsNoAdjustTabNew] using
    (ExecStmt.letDecl
      (cfg := config v) (solm := oweFrame) (evm := evmRead) (name := "tabNew")
      (ty := some uint256) (expr := wrap256 (.binary .sub (.var "tab") (.var "owe")))
      (value := .int (Int.ofNat tabNew.toNat)) hrhs)

theorem clipperEvalTakeLotSubSliceAtNoAdjustTabNew (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew : UInt256)
    (hsliceLot : slice.toNat ≤ (clipperTakeSalesLotEVMWord evmRead I).toNat) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperTakeLocalsNoAdjustTabNew evmLoc evmRead I price slice owe0 owe
          tabNew }
      evmRead (wrap256 (.binary .sub (.var "lot") (.var "slice"))) =
      .ok (.int (Int.ofNat (UInt256.sub (clipperTakeSalesLotEVMWord evmRead I) slice).toNat)) := by
  have hlot :
      evalExpr? (config v)
        { contract := contract v,
          locals := clipperTakeLocalsNoAdjustTabNew evmLoc evmRead I price slice owe0 owe
            tabNew }
        evmRead (.var "lot") =
      .ok (.int (Int.ofNat (clipperTakeSalesLotEVMWord evmRead I).toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsNoAdjustTabNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsOwe, store_get_ne _ _ (by decide),
      clipperTakeLocalsOwe0, store_get_ne _ _ (by decide),
      clipperTakeLocalsSlice, store_get_ne _ _ (by decide),
      clipperTakeLocalsTab, store_get_ne _ _ (by decide),
      clipperTakeLocalsLot, store_get_self]
    rfl
  have hslice :
      evalExpr? (config v)
        { contract := contract v,
          locals := clipperTakeLocalsNoAdjustTabNew evmLoc evmRead I price slice owe0 owe
            tabNew }
        evmRead (.var "slice") = .ok (.int (Int.ofNat slice.toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsNoAdjustTabNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsOwe, store_get_ne _ _ (by decide),
      clipperTakeLocalsOwe0, store_get_ne _ _ (by decide),
      clipperTakeLocalsSlice, store_get_self]
    rfl
  let lot := clipperTakeSalesLotEVMWord evmRead I
  have hsubNat : (UInt256.sub lot slice).toNat = lot.toNat - slice.toNat := by
    exact usub_toNat hsliceLot
  have hdiff :
      Int.ofNat lot.toNat - Int.ofNat slice.toNat =
        Int.ofNat (lot.toNat - slice.toNat) := by
    exact (Int.ofNat_sub hsliceLot).symm
  have hltNat : lot.toNat - slice.toNat < UInt256.size := by
    exact lt_of_le_of_lt (Nat.sub_le lot.toNat slice.toNat) lot.val.isLt
  have hlt : Int.ofNat (lot.toNat - slice.toNat) < wordModulus := by
    norm_num [wordModulus, UInt256.size] at hltNat ⊢
    exact_mod_cast hltNat
  have hmod :
      Int.ofNat (lot.toNat - slice.toNat) % wordModulus =
        Int.ofNat (lot.toNat - slice.toNat) := by
    rw [Int.emod_eq_of_lt]
    · exact Int.natCast_nonneg _
    · exact hlt
  have hwordNonzero : ¬wordModulus = 0 := by
    norm_num [wordModulus]
  have hmodLoad :
      (Int.ofNat (clipperTakeSalesLotEVMWord evmRead I).toNat -
          Int.ofNat slice.toNat) % wordModulus =
        Int.ofNat ((clipperTakeSalesLotEVMWord evmRead I).toNat - slice.toNat) := by
    rw [show Int.ofNat (clipperTakeSalesLotEVMWord evmRead I).toNat -
        Int.ofNat slice.toNat = Int.ofNat (lot.toNat - slice.toNat) by
      simpa [lot] using hdiff]
    simpa [lot] using hmod
  simp [wrap256, evalExpr?, EvalResult.bind, bind, hlot, hslice, evalBinaryOp?, hsubNat,
    hwordNonzero, lot]
  exact hmodLoad

theorem clipperTakeNoAdjustLetLotNew (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew : UInt256)
    (hsliceLot : slice.toNat ≤ (clipperTakeSalesLotEVMWord evmRead I).toNat) :
    let lotNew := UInt256.sub (clipperTakeSalesLotEVMWord evmRead I) slice
    ExecStmt (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsNoAdjustTabNew evmLoc evmRead I price slice owe0 owe tabNew))
      evmRead
      (.letDecl "lotNew" (some uint256)
        (wrap256 (.binary .sub (.var "lot") (.var "slice"))))
      (.ok
        (Frame.mk (contract v)
          (clipperTakeLocalsNoAdjustLotNew evmLoc evmRead I price slice owe0 owe tabNew
            lotNew))
        evmRead) := by
  intro lotNew
  let tabNewFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsNoAdjustTabNew evmLoc evmRead I price slice owe0 owe tabNew)
  let lotNewFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsNoAdjustLotNew evmLoc evmRead I price slice owe0 owe tabNew lotNew)
  have hrhs :
      evalExpr? (config v) tabNewFrame evmRead
        (wrap256 (.binary .sub (.var "lot") (.var "slice"))) =
      .ok (.int (Int.ofNat lotNew.toNat)) := by
    simpa [tabNewFrame, lotNew] using
      clipperEvalTakeLotSubSliceAtNoAdjustTabNew v evmLoc evmRead I price slice owe0 owe
        tabNew hsliceLot
  simpa [tabNewFrame, lotNewFrame, clipperTakeLocalsNoAdjustLotNew] using
    (ExecStmt.letDecl
      (cfg := config v) (solm := tabNewFrame) (evm := evmRead) (name := "lotNew")
      (ty := some uint256)
      (expr := wrap256 (.binary .sub (.var "lot") (.var "slice")))
      (value := .int (Int.ofNat lotNew.toNat)) hrhs)

theorem clipperTakeNoAdjustAssignTabFromTabNew (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew lotNew : UInt256) :
    ExecStmt (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsNoAdjustLotNew evmLoc evmRead I price slice owe0 owe tabNew
          lotNew))
      evmRead (.assign .localVar (varRef "tab") (.var "tabNew"))
      (.ok
        (Frame.mk (contract v)
          (clipperTakeLocalsNoAdjustTabAssigned evmLoc evmRead I price slice owe0 owe
            tabNew lotNew))
        evmRead) := by
  let lotNewFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsNoAdjustLotNew evmLoc evmRead I price slice owe0 owe tabNew lotNew)
  let tabFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsNoAdjustTabAssigned evmLoc evmRead I price slice owe0 owe tabNew lotNew)
  have hrhs :
      evalExpr? (config v) lotNewFrame evmRead (.var "tabNew") =
      .ok (.int (Int.ofNat tabNew.toNat)) := by
    change evalExpr? (config v)
      { contract := contract v,
        locals := clipperTakeLocalsNoAdjustLotNew evmLoc evmRead I price slice owe0 owe
          tabNew lotNew }
      evmRead (.var "tabNew") = .ok (.int (Int.ofNat tabNew.toNat))
    simp only [evalExpr?]
    rw [clipperTakeLocalsNoAdjustLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsNoAdjustTabNew, store_get_self]
    rfl
  have hassign :
      assignStorageRef? (config v) lotNewFrame evmRead .localVar (varRef "tab")
        (.int (Int.ofNat tabNew.toNat)) = .ok (tabFrame, evmRead) := by
    simp [assignStorageRef?, updateLocalPath?, varRef, lotNewFrame, tabFrame,
      clipperTakeLocalsNoAdjustTabAssigned, pure, bind, EvalResult.bind]
  simpa [lotNewFrame, tabFrame] using ExecStmt.assign hrhs hassign

theorem clipperTakeNoAdjustAssignLotFromLotNew (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew lotNew : UInt256) :
    ExecStmt (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsNoAdjustTabAssigned evmLoc evmRead I price slice owe0 owe tabNew
          lotNew))
      evmRead (.assign .localVar (varRef "lot") (.var "lotNew"))
      (.ok
        (Frame.mk (contract v)
          (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe
            tabNew lotNew))
        evmRead) := by
  let tabFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsNoAdjustTabAssigned evmLoc evmRead I price slice owe0 owe tabNew lotNew)
  let lotFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe tabNew lotNew)
  have hrhs :
      evalExpr? (config v) tabFrame evmRead (.var "lotNew") =
      .ok (.int (Int.ofNat lotNew.toNat)) := by
    change evalExpr? (config v)
      { contract := contract v,
        locals := clipperTakeLocalsNoAdjustTabAssigned evmLoc evmRead I price slice owe0 owe
          tabNew lotNew }
      evmRead (.var "lotNew") = .ok (.int (Int.ofNat lotNew.toNat))
    simp only [evalExpr?]
    rw [clipperTakeLocalsNoAdjustTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsNoAdjustLotNew, store_get_self]
    rfl
  have hassign :
      assignStorageRef? (config v) tabFrame evmRead .localVar (varRef "lot")
        (.int (Int.ofNat lotNew.toNat)) = .ok (lotFrame, evmRead) := by
    simp [assignStorageRef?, updateLocalPath?, varRef, tabFrame, lotFrame,
      clipperTakeLocalsNoAdjustLotAssigned, pure, bind, EvalResult.bind]
  simpa [tabFrame, lotFrame] using ExecStmt.assign hrhs hassign

theorem clipperTakePostNoAdjustSubBlock (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe : UInt256)
    (howeTab : owe.toNat ≤ (clipperTakeSalesTabEVMWord evmRead I).toNat)
    (hsliceLot : slice.toNat ≤ (clipperTakeSalesLotEVMWord evmRead I).toNat) :
    let tabNew := UInt256.sub (clipperTakeSalesTabEVMWord evmRead I) owe
    let lotNew := UInt256.sub (clipperTakeSalesLotEVMWord evmRead I) slice
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe))
      evmRead
      (wrappingSubInto "tabNew" (.var "tab") (.var "owe") ++
        wrappingSubInto "lotNew" (.var "lot") (.var "slice") ++
        [ .assign .localVar (varRef "tab") (.var "tabNew"),
          .assign .localVar (varRef "lot") (.var "lotNew") ])
      (.ok
        (Frame.mk (contract v)
          (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe
            tabNew lotNew))
        evmRead) := by
  intro tabNew lotNew
  let oweFrame : Frame :=
    Frame.mk (contract v) (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe)
  let tabNewFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsNoAdjustTabNew evmLoc evmRead I price slice owe0 owe tabNew)
  let lotNewFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsNoAdjustLotNew evmLoc evmRead I price slice owe0 owe tabNew lotNew)
  let tabFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsNoAdjustTabAssigned evmLoc evmRead I price slice owe0 owe tabNew
        lotNew)
  let lotFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe tabNew
        lotNew)
  have htabNew :
      ExecStmt (config v) oweFrame evmRead
        (.letDecl "tabNew" (some uint256)
          (wrap256 (.binary .sub (.var "tab") (.var "owe"))))
        (.ok tabNewFrame evmRead) := by
    simpa [oweFrame, tabNewFrame, tabNew] using
      clipperTakeNoAdjustLetTabNew v evmLoc evmRead I price slice owe0 owe howeTab
  have hlotNew :
      ExecStmt (config v) tabNewFrame evmRead
        (.letDecl "lotNew" (some uint256)
          (wrap256 (.binary .sub (.var "lot") (.var "slice"))))
        (.ok lotNewFrame evmRead) := by
    simpa [tabNewFrame, lotNewFrame, lotNew] using
      clipperTakeNoAdjustLetLotNew v evmLoc evmRead I price slice owe0 owe tabNew
        hsliceLot
  have hassignTab :
      ExecStmt (config v) lotNewFrame evmRead
        (.assign .localVar (varRef "tab") (.var "tabNew"))
        (.ok tabFrame evmRead) := by
    simpa [lotNewFrame, tabFrame] using
      clipperTakeNoAdjustAssignTabFromTabNew v evmLoc evmRead I price slice owe0 owe
        tabNew lotNew
  have hassignLot :
      ExecStmt (config v) tabFrame evmRead
        (.assign .localVar (varRef "lot") (.var "lotNew"))
        (.ok lotFrame evmRead) := by
    simpa [tabFrame, lotFrame] using
      clipperTakeNoAdjustAssignLotFromLotNew v evmLoc evmRead I price slice owe0 owe
        tabNew lotNew
  simpa [wrappingSubInto, oweFrame, lotFrame] using
    (ExecBlock.consNormal htabNew
      (ExecBlock.consNormal hlotNew
        (ExecBlock.consNormal hassignTab
          (ExecBlock.consNormal hassignLot ExecBlock.nil))))

abbrev clipperTakeLocalsNoAdjustFluxBuyerRet (evmLoc evmRead : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe tabNew lotNew : UInt256) : Store :=
  (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe tabNew
    lotNew).insert "_fluxBuyerRet" .unit

theorem clipperEvalTakeNoAdjustVatFluxBuyerArgs (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew lotNew : UInt256) :
    evalExprs? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe
          tabNew lotNew))
      evmRead [ilkExpr v, thisAddr, .var "who", .var "slice"] =
        .ok
          [v.ilk, .address evmRead.executionEnv.codeOwner,
            .address (AccountAddress.ofNat
              (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
            .int (Int.ofNat slice.toNat)] := by
  rcases v.ilk_wf with ⟨bs, hilk, _hlen⟩
  have hwho :
      Value.address (AccountAddress.ofNat (clipperTakeWhoWord I).toNat) =
        Value.address (AccountAddress.ofNat
          (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat) := by
    rw [solcAddressValue_masked (clipperTakeWhoWord I)]
    rw [u256_land_comm solcAddrMask (clipperTakeWhoWord I)]
  have hilkEval :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe
            tabNew lotNew))
        evmRead (ilkExpr v) = .ok v.ilk := by
    simp [ilkExpr, hilk, evalExpr?, pure]
  have hthisEval :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe
            tabNew lotNew))
        evmRead thisAddr = .ok (.address evmRead.executionEnv.codeOwner) := by
    simp [thisAddr, evalExpr?, envValue, pure]
  have hwhoRaw :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe
            tabNew lotNew))
        evmRead (.var "who") =
          .ok (.address (AccountAddress.ofNat (clipperTakeWhoWord I).toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsNoAdjustLotAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsNoAdjustTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsNoAdjustLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsNoAdjustTabNew, store_get_ne _ _ (by decide),
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
      clipperTakeStore, store_get_ne _ _ (by decide), store_get_self]
    rfl
  have hwhoEval :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe
            tabNew lotNew))
        evmRead (.var "who") =
          .ok (.address (AccountAddress.ofNat
            (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat)) := by
    simpa [hwho] using hwhoRaw
  have hsliceEval :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe
            tabNew lotNew))
        evmRead (.var "slice") = .ok (.int (Int.ofNat slice.toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsNoAdjustLotAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsNoAdjustTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsNoAdjustLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsNoAdjustTabNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsOwe, store_get_ne _ _ (by decide),
      clipperTakeLocalsOwe0, store_get_ne _ _ (by decide),
      clipperTakeLocalsSlice, store_get_self]
    rfl
  simp only [evalExprs?, hilkEval, hthisEval, hwhoEval, hsliceEval, EvalResult.bind, bind,
    pure]

theorem clipperTakeNoAdjustVatFluxBuyerNoCodeBlock (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew lotNew : UInt256)
    (hnoVatCode :
      (UInt256.ofNat ((evmRead.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat =
        0) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe
          tabNew lotNew))
      evmRead
      (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
        [ilkExpr v, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet")
      .reverted := by
  have hguard :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe
            tabNew lotNew))
        evmRead (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)) =
          .ok (.bool false) := by
    exact clipperEvalTakeVatCodeGuard_false v evmRead
      (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe
        tabNew lotNew) hnoVatCode
  simpa [checkedExternalCallStmts] using
    (ExecBlock.consRevert (ExecStmt.requireFalse hguard))

theorem clipperTakeNoAdjustVatFluxBuyerCallFailureBlock (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew lotNew : UInt256) {outVat : ByteArray}
    {argVals : List Value}
    (hvatCode :
      0 <
        (UInt256.ofNat ((evmRead.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hargs :
      evalExprs? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe
            tabNew lotNew))
        evmRead [ilkExpr v, thisAddr, .var "who", .var "slice"] = .ok argVals)
    (hcallVat :
      typedCallViaEVM (config v) evmRead (EVM.address v.vat) "flux" 0 argVals
        (false, evmVat, outVat) true) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe
          tabNew lotNew))
      evmRead
      (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
        [ilkExpr v, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet")
      .reverted := by
  have hguard :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe
            tabNew lotNew))
        evmRead (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)) =
          .ok (.bool true) := by
    exact clipperEvalTakeVatCodeGuard_true v evmRead
      (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe
        tabNew lotNew) hvatCode
  simpa [checkedExternalCallStmts] using
    (ExecBlock.consNormal (ExecStmt.requireTrue hguard)
      (ExecBlock.consRevert
        (ExecStmt.externalCallFailure
          (clipperEvalVat v evmRead
            (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe
              tabNew lotNew))
          (by simp [evalExpr?, pure]) hargs hcallVat)))

theorem clipperTakeNoAdjustVatFluxBuyerCallSuccessBlock (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew lotNew : UInt256) {outVat : ByteArray}
    {argVals : List Value}
    (hvatCode :
      0 <
        (UInt256.ofNat ((evmRead.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hargs :
      evalExprs? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe
            tabNew lotNew))
        evmRead [ilkExpr v, thisAddr, .var "who", .var "slice"] = .ok argVals)
    (hcallVat :
      typedCallViaEVM (config v) evmRead (EVM.address v.vat) "flux" 0 argVals
        (true, evmVat, outVat) true) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe
          tabNew lotNew))
      evmRead
      (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
        [ilkExpr v, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet")
      (.ok
        (Frame.mk (contract v)
          (clipperTakeLocalsNoAdjustFluxBuyerRet evmLoc evmRead I price slice owe0 owe
            tabNew lotNew))
        evmVat) := by
  have hguard :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe
            tabNew lotNew))
        evmRead (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)) =
          .ok (.bool true) := by
    exact clipperEvalTakeVatCodeGuard_true v evmRead
      (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe
        tabNew lotNew) hvatCode
  simpa [checkedExternalCallStmts, clipperTakeLocalsNoAdjustFluxBuyerRet, collapseReturns] using
    (ExecBlock.consNormal (ExecStmt.requireTrue hguard)
      (ExecBlock.consNormal
        (ExecStmt.externalCallSuccess
          (clipperEvalVat v evmRead
            (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe
              tabNew lotNew))
          (by simp [evalExpr?, pure]) hargs hcallVat
          (clipperTakeDecodeFluxVoid v outVat))
        ExecBlock.nil))

theorem clipperTakeNoAdjustPostSubVatFluxNoCodeBlock (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe : UInt256)
    (howeTab : owe.toNat ≤ (clipperTakeSalesTabEVMWord evmRead I).toNat)
    (hsliceLot : slice.toNat ≤ (clipperTakeSalesLotEVMWord evmRead I).toNat)
    (hnoVatCode :
      (UInt256.ofNat ((evmRead.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat =
        0) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe))
      evmRead
      (wrappingSubInto "tabNew" (.var "tab") (.var "owe") ++
        wrappingSubInto "lotNew" (.var "lot") (.var "slice") ++
        [ .assign .localVar (varRef "tab") (.var "tabNew"),
          .assign .localVar (varRef "lot") (.var "lotNew") ] ++
        checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
          [ilkExpr v, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet")
      .reverted := by
  let tabNew := UInt256.sub (clipperTakeSalesTabEVMWord evmRead I) owe
  let lotNew := UInt256.sub (clipperTakeSalesLotEVMWord evmRead I) slice
  let oweFrame : Frame :=
    Frame.mk (contract v) (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe)
  let postSubFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe tabNew
        lotNew)
  have hsubBlock :
      ExecBlock (config v) oweFrame evmRead
        (wrappingSubInto "tabNew" (.var "tab") (.var "owe") ++
          wrappingSubInto "lotNew" (.var "lot") (.var "slice") ++
          [ .assign .localVar (varRef "tab") (.var "tabNew"),
            .assign .localVar (varRef "lot") (.var "lotNew") ])
        (.ok postSubFrame evmRead) := by
    simpa [oweFrame, postSubFrame, tabNew, lotNew] using
      clipperTakePostNoAdjustSubBlock v evmLoc evmRead I price slice owe0 owe howeTab
        hsliceLot
  have hvatRevert :
      ExecBlock (config v) postSubFrame evmRead
        (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
          [ilkExpr v, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet")
        .reverted := by
    simpa [postSubFrame] using
      clipperTakeNoAdjustVatFluxBuyerNoCodeBlock v evmLoc evmRead I price slice owe0 owe
        tabNew lotNew hnoVatCode
  simpa [oweFrame, List.append_assoc] using execBlockAppendRevert hsubBlock hvatRevert

theorem clipperTakeNoAdjustPostSubVatFluxCallFailureBlock (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe : UInt256) {outVat : ByteArray}
    (howeTab : owe.toNat ≤ (clipperTakeSalesTabEVMWord evmRead I).toNat)
    (hsliceLot : slice.toNat ≤ (clipperTakeSalesLotEVMWord evmRead I).toNat)
    (hvatCode :
      0 <
        (UInt256.ofNat ((evmRead.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallVat :
      typedCallViaEVM (config v) evmRead (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmRead.executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
          .int (Int.ofNat slice.toNat)]
        (false, evmVat, outVat) true) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe))
      evmRead
      (wrappingSubInto "tabNew" (.var "tab") (.var "owe") ++
        wrappingSubInto "lotNew" (.var "lot") (.var "slice") ++
        [ .assign .localVar (varRef "tab") (.var "tabNew"),
          .assign .localVar (varRef "lot") (.var "lotNew") ] ++
        checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
          [ilkExpr v, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet")
      .reverted := by
  let tabNew := UInt256.sub (clipperTakeSalesTabEVMWord evmRead I) owe
  let lotNew := UInt256.sub (clipperTakeSalesLotEVMWord evmRead I) slice
  let oweFrame : Frame :=
    Frame.mk (contract v) (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe)
  let postSubFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe tabNew
        lotNew)
  have hsubBlock :
      ExecBlock (config v) oweFrame evmRead
        (wrappingSubInto "tabNew" (.var "tab") (.var "owe") ++
          wrappingSubInto "lotNew" (.var "lot") (.var "slice") ++
          [ .assign .localVar (varRef "tab") (.var "tabNew"),
            .assign .localVar (varRef "lot") (.var "lotNew") ])
        (.ok postSubFrame evmRead) := by
    simpa [oweFrame, postSubFrame, tabNew, lotNew] using
      clipperTakePostNoAdjustSubBlock v evmLoc evmRead I price slice owe0 owe howeTab
        hsliceLot
  have hargs :
      evalExprs? (config v) postSubFrame evmRead
        [ilkExpr v, thisAddr, .var "who", .var "slice"] =
          .ok
            [v.ilk, .address evmRead.executionEnv.codeOwner,
              .address (AccountAddress.ofNat
                (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
              .int (Int.ofNat slice.toNat)] := by
    simpa [postSubFrame] using
      clipperEvalTakeNoAdjustVatFluxBuyerArgs v evmLoc evmRead I price slice owe0 owe
        tabNew lotNew
  have hvatRevert :
      ExecBlock (config v) postSubFrame evmRead
        (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
          [ilkExpr v, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet")
        .reverted := by
    simpa [postSubFrame] using
      clipperTakeNoAdjustVatFluxBuyerCallFailureBlock v evmLoc evmRead evmVat I price slice
        owe0 owe tabNew lotNew hvatCode hargs hcallVat
  simpa [oweFrame, List.append_assoc] using execBlockAppendRevert hsubBlock hvatRevert

theorem clipperTakeNoAdjustPostSubVatFluxCallSuccessBlock (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe : UInt256) {outVat : ByteArray}
    (howeTab : owe.toNat ≤ (clipperTakeSalesTabEVMWord evmRead I).toNat)
    (hsliceLot : slice.toNat ≤ (clipperTakeSalesLotEVMWord evmRead I).toNat)
    (hvatCode :
      0 <
        (UInt256.ofNat ((evmRead.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallVat :
      typedCallViaEVM (config v) evmRead (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmRead.executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
          .int (Int.ofNat slice.toNat)]
        (true, evmVat, outVat) true) :
    let tabNew := UInt256.sub (clipperTakeSalesTabEVMWord evmRead I) owe
    let lotNew := UInt256.sub (clipperTakeSalesLotEVMWord evmRead I) slice
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe))
      evmRead
      (wrappingSubInto "tabNew" (.var "tab") (.var "owe") ++
        wrappingSubInto "lotNew" (.var "lot") (.var "slice") ++
        [ .assign .localVar (varRef "tab") (.var "tabNew"),
          .assign .localVar (varRef "lot") (.var "lotNew") ] ++
        checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
          [ilkExpr v, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet")
      (.ok
        (Frame.mk (contract v)
          (clipperTakeLocalsNoAdjustFluxBuyerRet evmLoc evmRead I price slice owe0 owe
            tabNew lotNew))
        evmVat) := by
  intro tabNew lotNew
  let oweFrame : Frame :=
    Frame.mk (contract v) (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe)
  let postSubFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe tabNew
        lotNew)
  let fluxFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsNoAdjustFluxBuyerRet evmLoc evmRead I price slice owe0 owe tabNew
        lotNew)
  have hsubBlock :
      ExecBlock (config v) oweFrame evmRead
        (wrappingSubInto "tabNew" (.var "tab") (.var "owe") ++
          wrappingSubInto "lotNew" (.var "lot") (.var "slice") ++
          [ .assign .localVar (varRef "tab") (.var "tabNew"),
            .assign .localVar (varRef "lot") (.var "lotNew") ])
        (.ok postSubFrame evmRead) := by
    simpa [oweFrame, postSubFrame, tabNew, lotNew] using
      clipperTakePostNoAdjustSubBlock v evmLoc evmRead I price slice owe0 owe howeTab
        hsliceLot
  have hargs :
      evalExprs? (config v) postSubFrame evmRead
        [ilkExpr v, thisAddr, .var "who", .var "slice"] =
          .ok
            [v.ilk, .address evmRead.executionEnv.codeOwner,
              .address (AccountAddress.ofNat
                (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
              .int (Int.ofNat slice.toNat)] := by
    simpa [postSubFrame] using
      clipperEvalTakeNoAdjustVatFluxBuyerArgs v evmLoc evmRead I price slice owe0 owe
        tabNew lotNew
  have hvatOk :
      ExecBlock (config v) postSubFrame evmRead
        (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
          [ilkExpr v, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet")
        (.ok fluxFrame evmVat) := by
    simpa [postSubFrame, fluxFrame] using
      clipperTakeNoAdjustVatFluxBuyerCallSuccessBlock v evmLoc evmRead evmVat I price slice
        owe0 owe tabNew lotNew hvatCode hargs hcallVat
  simpa [oweFrame, fluxFrame, List.append_assoc] using
    execBlockAppendOk hsubBlock hvatOk

theorem clipperTakeNoAdjustVatFluxNoCodeTailBlock (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (price slice : UInt256)
    (hmul : slice.toNat * price.toNat < UInt256.size)
    (howeTab : (UInt256.mul slice price).toNat ≤ (clipperTakeSalesTabEVMWord evmRead I).toNat)
    (hsliceLot : slice.toNat ≤ (clipperTakeSalesLotEVMWord evmRead I).toNat)
    (hite :
      let owe0 := UInt256.mul slice price
      ExecStmt (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0))
        evmRead clipperTakeOweAdjustmentStmt
        (.ok
          (Frame.mk (contract v)
            (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0))
          evmRead))
    (hnoVatCode :
      (UInt256.ofNat ((evmRead.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat =
        0) :
    ExecBlock (config v)
      (Frame.mk (contract v) (clipperTakeLocalsSlice evmLoc evmRead I false price slice))
      evmRead
      (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
        [ .letDecl "owe" (some uint256) (.var "owe0"),
          clipperTakeOweAdjustmentStmt ] ++
        clipperTakePostOweFluxStmts v)
      .reverted := by
  let owe0 := UInt256.mul slice price
  let sliceFrame : Frame :=
    Frame.mk (contract v) (clipperTakeLocalsSlice evmLoc evmRead I false price slice)
  let oweFrame : Frame :=
    Frame.mk (contract v) (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0)
  have hmulBlock :
      ExecBlock (config v) sliceFrame evmRead
        (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
          [.letDecl "owe" (some uint256) (.var "owe0")])
        (.ok oweFrame evmRead) := by
    simpa [sliceFrame, oweFrame, owe0] using
      clipperTakeOwe0MulSuccessBlock v evmLoc evmRead I price slice hmul
  have hpost :
      ExecBlock (config v) oweFrame evmRead (clipperTakePostOweFluxStmts v) .reverted := by
    simpa [clipperTakePostOweFluxStmts, oweFrame, owe0] using
      clipperTakeNoAdjustPostSubVatFluxNoCodeBlock v evmLoc evmRead I price slice owe0
        owe0 howeTab hsliceLot hnoVatCode
  have hafterIte :
      ExecBlock (config v) oweFrame evmRead
        (clipperTakeOweAdjustmentStmt :: clipperTakePostOweFluxStmts v) .reverted :=
    ExecBlock.consNormal (by simpa [oweFrame, owe0] using hite) hpost
  simpa [sliceFrame, clipperTakePostOweFluxStmts, List.append_assoc] using
    execBlockAppendRevert hmulBlock hafterIte

theorem clipperTakeNoAdjustVatFluxCallFailureTailBlock (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv) (price slice : UInt256)
    {outVat : ByteArray}
    (hmul : slice.toNat * price.toNat < UInt256.size)
    (howeTab : (UInt256.mul slice price).toNat ≤ (clipperTakeSalesTabEVMWord evmRead I).toNat)
    (hsliceLot : slice.toNat ≤ (clipperTakeSalesLotEVMWord evmRead I).toNat)
    (hite :
      let owe0 := UInt256.mul slice price
      ExecStmt (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0))
        evmRead clipperTakeOweAdjustmentStmt
        (.ok
          (Frame.mk (contract v)
            (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0))
          evmRead))
    (hvatCode :
      0 <
        (UInt256.ofNat ((evmRead.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallVat :
      typedCallViaEVM (config v) evmRead (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmRead.executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
          .int (Int.ofNat slice.toNat)]
        (false, evmVat, outVat) true) :
    ExecBlock (config v)
      (Frame.mk (contract v) (clipperTakeLocalsSlice evmLoc evmRead I false price slice))
      evmRead
      (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
        [ .letDecl "owe" (some uint256) (.var "owe0"),
          clipperTakeOweAdjustmentStmt ] ++
        clipperTakePostOweFluxStmts v)
      .reverted := by
  let owe0 := UInt256.mul slice price
  let sliceFrame : Frame :=
    Frame.mk (contract v) (clipperTakeLocalsSlice evmLoc evmRead I false price slice)
  let oweFrame : Frame :=
    Frame.mk (contract v) (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0)
  have hmulBlock :
      ExecBlock (config v) sliceFrame evmRead
        (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
          [.letDecl "owe" (some uint256) (.var "owe0")])
        (.ok oweFrame evmRead) := by
    simpa [sliceFrame, oweFrame, owe0] using
      clipperTakeOwe0MulSuccessBlock v evmLoc evmRead I price slice hmul
  have hpost :
      ExecBlock (config v) oweFrame evmRead (clipperTakePostOweFluxStmts v) .reverted := by
    simpa [clipperTakePostOweFluxStmts, oweFrame, owe0] using
      clipperTakeNoAdjustPostSubVatFluxCallFailureBlock v evmLoc evmRead evmVat I price
        slice owe0 owe0 howeTab hsliceLot hvatCode hcallVat
  have hafterIte :
      ExecBlock (config v) oweFrame evmRead
        (clipperTakeOweAdjustmentStmt :: clipperTakePostOweFluxStmts v) .reverted :=
    ExecBlock.consNormal (by simpa [oweFrame, owe0] using hite) hpost
  simpa [sliceFrame, clipperTakePostOweFluxStmts, List.append_assoc] using
    execBlockAppendRevert hmulBlock hafterIte

theorem clipperTakeNoAdjustVatFluxCallSuccessTailBlock (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv) (price slice : UInt256)
    {outVat : ByteArray}
    (hmul : slice.toNat * price.toNat < UInt256.size)
    (howeTab : (UInt256.mul slice price).toNat ≤ (clipperTakeSalesTabEVMWord evmRead I).toNat)
    (hsliceLot : slice.toNat ≤ (clipperTakeSalesLotEVMWord evmRead I).toNat)
    (hite :
      let owe0 := UInt256.mul slice price
      ExecStmt (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0))
        evmRead clipperTakeOweAdjustmentStmt
        (.ok
          (Frame.mk (contract v)
            (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0))
          evmRead))
    (hvatCode :
      0 <
        (UInt256.ofNat ((evmRead.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallVat :
      typedCallViaEVM (config v) evmRead (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmRead.executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
          .int (Int.ofNat slice.toNat)]
        (true, evmVat, outVat) true) :
    let owe0 := UInt256.mul slice price
    let tabNew := UInt256.sub (clipperTakeSalesTabEVMWord evmRead I) owe0
    let lotNew := UInt256.sub (clipperTakeSalesLotEVMWord evmRead I) slice
    ExecBlock (config v)
      (Frame.mk (contract v) (clipperTakeLocalsSlice evmLoc evmRead I false price slice))
      evmRead
      (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
        [ .letDecl "owe" (some uint256) (.var "owe0"),
          clipperTakeOweAdjustmentStmt ] ++
        clipperTakePostOweFluxStmts v)
      (.ok
        (Frame.mk (contract v)
          (clipperTakeLocalsNoAdjustFluxBuyerRet evmLoc evmRead I price slice owe0 owe0
            tabNew lotNew))
        evmVat) := by
  intro owe0 tabNew lotNew
  let sliceFrame : Frame :=
    Frame.mk (contract v) (clipperTakeLocalsSlice evmLoc evmRead I false price slice)
  let oweFrame : Frame :=
    Frame.mk (contract v) (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0)
  let fluxFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsNoAdjustFluxBuyerRet evmLoc evmRead I price slice owe0 owe0 tabNew
        lotNew)
  have hmulBlock :
      ExecBlock (config v) sliceFrame evmRead
        (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
          [.letDecl "owe" (some uint256) (.var "owe0")])
        (.ok oweFrame evmRead) := by
    simpa [sliceFrame, oweFrame, owe0] using
      clipperTakeOwe0MulSuccessBlock v evmLoc evmRead I price slice hmul
  have hpost :
      ExecBlock (config v) oweFrame evmRead (clipperTakePostOweFluxStmts v)
        (.ok fluxFrame evmVat) := by
    simpa [clipperTakePostOweFluxStmts, oweFrame, fluxFrame, owe0, tabNew, lotNew] using
      clipperTakeNoAdjustPostSubVatFluxCallSuccessBlock v evmLoc evmRead evmVat I price
        slice owe0 owe0 howeTab hsliceLot hvatCode hcallVat
  have hafterIte :
      ExecBlock (config v) oweFrame evmRead
        (clipperTakeOweAdjustmentStmt :: clipperTakePostOweFluxStmts v)
        (.ok fluxFrame evmVat) :=
    ExecBlock.consNormal (by simpa [oweFrame, owe0] using hite) hpost
  simpa [sliceFrame, fluxFrame, clipperTakePostOweFluxStmts, List.append_assoc] using
    execBlockAppendOk hmulBlock hafterIte

end Benchmarks.Dss.Clipper
