import Benchmarks.Dss.Clipper.TakeSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
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

abbrev clipperTakePostOweFluxStmts : List Stmt :=
  wrappingSubInto "tabNew" (.var "tab") (.var "owe") ++
    wrappingSubInto "lotNew" (.var "lot") (.var "slice") ++
    [ .assign .localVar (varRef "tab") (.var "tabNew"),
      .assign .localVar (varRef "lot") (.var "lotNew") ] ++
    checkedExternalCallStmts vatExpr "flux" (.intLit 0)
      [ilkExpr, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet"

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
    evalExpr? config
      { contract := contract,
        locals := clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe, immutables := immStore v }
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
    ExecStmt config
      (Frame.mk contract (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe) (immStore v))
      evmRead
      (.letDecl "tabNew" (some uint256) (wrap256 (.binary .sub (.var "tab") (.var "owe"))))
      (.ok
        (Frame.mk contract (clipperTakeLocalsNoAdjustTabNew evmLoc evmRead I price slice owe0 owe tabNew) (immStore v))
        evmRead) := by
  intro tabNew
  let oweFrame : Frame :=
    Frame.mk contract (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe) (immStore v)
  let tabNewFrame : Frame :=
    Frame.mk contract (clipperTakeLocalsNoAdjustTabNew evmLoc evmRead I price slice owe0 owe tabNew) (immStore v)
  have hrhs :
      evalExpr? config oweFrame evmRead
        (wrap256 (.binary .sub (.var "tab") (.var "owe"))) =
      .ok (.int (Int.ofNat tabNew.toNat)) := by
    simpa [oweFrame, tabNew] using
      clipperEvalTakeTabSubOweAtOwe v evmLoc evmRead I price slice owe0 owe howeTab
  simpa [oweFrame, tabNewFrame, clipperTakeLocalsNoAdjustTabNew] using
    (ExecStmt.letDecl
      (cfg := config) (solm := oweFrame) (evm := evmRead) (name := "tabNew")
      (ty := some uint256) (expr := wrap256 (.binary .sub (.var "tab") (.var "owe")))
      (value := .int (Int.ofNat tabNew.toNat)) hrhs)

theorem clipperEvalTakeLotSubSliceAtNoAdjustTabNew (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew : UInt256)
    (hsliceLot : slice.toNat ≤ (clipperTakeSalesLotEVMWord evmRead I).toNat) :
    evalExpr? config
      { contract := contract,
        locals := clipperTakeLocalsNoAdjustTabNew evmLoc evmRead I price slice owe0 owe
          tabNew, immutables := immStore v }
      evmRead (wrap256 (.binary .sub (.var "lot") (.var "slice"))) =
      .ok (.int (Int.ofNat (UInt256.sub (clipperTakeSalesLotEVMWord evmRead I) slice).toNat)) := by
  have hlot :
      evalExpr? config
        { contract := contract,
          locals := clipperTakeLocalsNoAdjustTabNew evmLoc evmRead I price slice owe0 owe
            tabNew, immutables := immStore v }
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
      evalExpr? config
        { contract := contract,
          locals := clipperTakeLocalsNoAdjustTabNew evmLoc evmRead I price slice owe0 owe
            tabNew, immutables := immStore v }
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
    ExecStmt config
      (Frame.mk contract (clipperTakeLocalsNoAdjustTabNew evmLoc evmRead I price slice owe0 owe tabNew) (immStore v))
      evmRead
      (.letDecl "lotNew" (some uint256)
        (wrap256 (.binary .sub (.var "lot") (.var "slice"))))
      (.ok
        (Frame.mk contract (clipperTakeLocalsNoAdjustLotNew evmLoc evmRead I price slice owe0 owe tabNew
            lotNew) (immStore v))
        evmRead) := by
  intro lotNew
  let tabNewFrame : Frame :=
    Frame.mk contract (clipperTakeLocalsNoAdjustTabNew evmLoc evmRead I price slice owe0 owe tabNew) (immStore v)
  let lotNewFrame : Frame :=
    Frame.mk contract (clipperTakeLocalsNoAdjustLotNew evmLoc evmRead I price slice owe0 owe tabNew lotNew) (immStore v)
  have hrhs :
      evalExpr? config tabNewFrame evmRead
        (wrap256 (.binary .sub (.var "lot") (.var "slice"))) =
      .ok (.int (Int.ofNat lotNew.toNat)) := by
    simpa [tabNewFrame, lotNew] using
      clipperEvalTakeLotSubSliceAtNoAdjustTabNew v evmLoc evmRead I price slice owe0 owe
        tabNew hsliceLot
  simpa [tabNewFrame, lotNewFrame, clipperTakeLocalsNoAdjustLotNew] using
    (ExecStmt.letDecl
      (cfg := config) (solm := tabNewFrame) (evm := evmRead) (name := "lotNew")
      (ty := some uint256)
      (expr := wrap256 (.binary .sub (.var "lot") (.var "slice")))
      (value := .int (Int.ofNat lotNew.toNat)) hrhs)

theorem clipperTakeNoAdjustAssignTabFromTabNew (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew lotNew : UInt256) :
    ExecStmt config
      (Frame.mk contract (clipperTakeLocalsNoAdjustLotNew evmLoc evmRead I price slice owe0 owe tabNew
          lotNew) (immStore v))
      evmRead (.assign .localVar (varRef "tab") (.var "tabNew"))
      (.ok
        (Frame.mk contract (clipperTakeLocalsNoAdjustTabAssigned evmLoc evmRead I price slice owe0 owe
            tabNew lotNew) (immStore v))
        evmRead) := by
  let lotNewFrame : Frame :=
    Frame.mk contract (clipperTakeLocalsNoAdjustLotNew evmLoc evmRead I price slice owe0 owe tabNew lotNew) (immStore v)
  let tabFrame : Frame :=
    Frame.mk contract (clipperTakeLocalsNoAdjustTabAssigned evmLoc evmRead I price slice owe0 owe tabNew lotNew) (immStore v)
  have hrhs :
      evalExpr? config lotNewFrame evmRead (.var "tabNew") =
      .ok (.int (Int.ofNat tabNew.toNat)) := by
    change evalExpr? config
      { contract := contract,
        locals := clipperTakeLocalsNoAdjustLotNew evmLoc evmRead I price slice owe0 owe
          tabNew lotNew, immutables := immStore v }
      evmRead (.var "tabNew") = .ok (.int (Int.ofNat tabNew.toNat))
    simp only [evalExpr?]
    rw [clipperTakeLocalsNoAdjustLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsNoAdjustTabNew, store_get_self]
    rfl
  have hassign :
      assignStorageRef? config lotNewFrame evmRead .localVar (varRef "tab")
        (.int (Int.ofNat tabNew.toNat)) = .ok (tabFrame, evmRead) := by
    simp [assignStorageRef?, updateLocalPath?, varRef, lotNewFrame, tabFrame,
      clipperTakeLocalsNoAdjustTabAssigned, pure, bind, EvalResult.bind]
  simpa [lotNewFrame, tabFrame] using ExecStmt.assign hrhs hassign

theorem clipperTakeNoAdjustAssignLotFromLotNew (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew lotNew : UInt256) :
    ExecStmt config
      (Frame.mk contract (clipperTakeLocalsNoAdjustTabAssigned evmLoc evmRead I price slice owe0 owe tabNew
          lotNew) (immStore v))
      evmRead (.assign .localVar (varRef "lot") (.var "lotNew"))
      (.ok
        (Frame.mk contract (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe
            tabNew lotNew) (immStore v))
        evmRead) := by
  let tabFrame : Frame :=
    Frame.mk contract (clipperTakeLocalsNoAdjustTabAssigned evmLoc evmRead I price slice owe0 owe tabNew lotNew) (immStore v)
  let lotFrame : Frame :=
    Frame.mk contract (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe tabNew lotNew) (immStore v)
  have hrhs :
      evalExpr? config tabFrame evmRead (.var "lotNew") =
      .ok (.int (Int.ofNat lotNew.toNat)) := by
    change evalExpr? config
      { contract := contract,
        locals := clipperTakeLocalsNoAdjustTabAssigned evmLoc evmRead I price slice owe0 owe
          tabNew lotNew, immutables := immStore v }
      evmRead (.var "lotNew") = .ok (.int (Int.ofNat lotNew.toNat))
    simp only [evalExpr?]
    rw [clipperTakeLocalsNoAdjustTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsNoAdjustLotNew, store_get_self]
    rfl
  have hassign :
      assignStorageRef? config tabFrame evmRead .localVar (varRef "lot")
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
    ExecBlock config
      (Frame.mk contract (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe) (immStore v))
      evmRead
      (wrappingSubInto "tabNew" (.var "tab") (.var "owe") ++
        wrappingSubInto "lotNew" (.var "lot") (.var "slice") ++
        [ .assign .localVar (varRef "tab") (.var "tabNew"),
          .assign .localVar (varRef "lot") (.var "lotNew") ])
      (.ok
        (Frame.mk contract (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe
            tabNew lotNew) (immStore v))
        evmRead) := by
  intro tabNew lotNew
  let oweFrame : Frame :=
    Frame.mk contract (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe) (immStore v)
  let tabNewFrame : Frame :=
    Frame.mk contract (clipperTakeLocalsNoAdjustTabNew evmLoc evmRead I price slice owe0 owe tabNew) (immStore v)
  let lotNewFrame : Frame :=
    Frame.mk contract (clipperTakeLocalsNoAdjustLotNew evmLoc evmRead I price slice owe0 owe tabNew lotNew) (immStore v)
  let tabFrame : Frame :=
    Frame.mk contract (clipperTakeLocalsNoAdjustTabAssigned evmLoc evmRead I price slice owe0 owe tabNew
        lotNew) (immStore v)
  let lotFrame : Frame :=
    Frame.mk contract (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe tabNew
        lotNew) (immStore v)
  have htabNew :
      ExecStmt config oweFrame evmRead
        (.letDecl "tabNew" (some uint256)
          (wrap256 (.binary .sub (.var "tab") (.var "owe"))))
        (.ok tabNewFrame evmRead) := by
    simpa [oweFrame, tabNewFrame, tabNew] using
      clipperTakeNoAdjustLetTabNew v evmLoc evmRead I price slice owe0 owe howeTab
  have hlotNew :
      ExecStmt config tabNewFrame evmRead
        (.letDecl "lotNew" (some uint256)
          (wrap256 (.binary .sub (.var "lot") (.var "slice"))))
        (.ok lotNewFrame evmRead) := by
    simpa [tabNewFrame, lotNewFrame, lotNew] using
      clipperTakeNoAdjustLetLotNew v evmLoc evmRead I price slice owe0 owe tabNew
        hsliceLot
  have hassignTab :
      ExecStmt config lotNewFrame evmRead
        (.assign .localVar (varRef "tab") (.var "tabNew"))
        (.ok tabFrame evmRead) := by
    simpa [lotNewFrame, tabFrame] using
      clipperTakeNoAdjustAssignTabFromTabNew v evmLoc evmRead I price slice owe0 owe
        tabNew lotNew
  have hassignLot :
      ExecStmt config tabFrame evmRead
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
    evalExprs? config
      (Frame.mk contract (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe
          tabNew lotNew) (immStore v))
      evmRead [ilkExpr, thisAddr, .var "who", .var "slice"] =
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
      evalExpr? config
        (Frame.mk contract (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe
            tabNew lotNew) (immStore v))
        evmRead ilkExpr = .ok v.ilk := by
    exact evalExpr_ilkExpr
  have hthisEval :
      evalExpr? config
        (Frame.mk contract (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe
            tabNew lotNew) (immStore v))
        evmRead thisAddr = .ok (.address evmRead.executionEnv.codeOwner) := by
    simp [thisAddr, evalExpr?, envValue, pure]
  have hwhoRaw :
      evalExpr? config
        (Frame.mk contract (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe
            tabNew lotNew) (immStore v))
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
      evalExpr? config
        (Frame.mk contract (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe
            tabNew lotNew) (immStore v))
        evmRead (.var "who") =
          .ok (.address (AccountAddress.ofNat
            (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat)) := by
    simpa [hwho] using hwhoRaw
  have hsliceEval :
      evalExpr? config
        (Frame.mk contract (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe
            tabNew lotNew) (immStore v))
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
    ExecBlock config
      (Frame.mk contract (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe
          tabNew lotNew) (immStore v))
      evmRead
      (checkedExternalCallStmts vatExpr "flux" (.intLit 0)
        [ilkExpr, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet")
      .reverted := by
  have hguard :
      evalExpr? config
        (Frame.mk contract (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe
            tabNew lotNew) (immStore v))
        evmRead (.binary .gt (.extCodeSize vatExpr) (.intLit 0)) =
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
      evalExprs? config
        (Frame.mk contract (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe
            tabNew lotNew) (immStore v))
        evmRead [ilkExpr, thisAddr, .var "who", .var "slice"] = .ok argVals)
    (hcallVat :
      typedCallViaEVM config evmRead (EVM.address v.vat) "flux" 0 argVals
        (false, evmVat, outVat) true) :
    ExecBlock config
      (Frame.mk contract (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe
          tabNew lotNew) (immStore v))
      evmRead
      (checkedExternalCallStmts vatExpr "flux" (.intLit 0)
        [ilkExpr, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet")
      .reverted := by
  have hguard :
      evalExpr? config
        (Frame.mk contract (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe
            tabNew lotNew) (immStore v))
        evmRead (.binary .gt (.extCodeSize vatExpr) (.intLit 0)) =
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
      evalExprs? config
        (Frame.mk contract (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe
            tabNew lotNew) (immStore v))
        evmRead [ilkExpr, thisAddr, .var "who", .var "slice"] = .ok argVals)
    (hcallVat :
      typedCallViaEVM config evmRead (EVM.address v.vat) "flux" 0 argVals
        (true, evmVat, outVat) true) :
    ExecBlock config
      (Frame.mk contract (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe
          tabNew lotNew) (immStore v))
      evmRead
      (checkedExternalCallStmts vatExpr "flux" (.intLit 0)
        [ilkExpr, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet")
      (.ok
        (Frame.mk contract (clipperTakeLocalsNoAdjustFluxBuyerRet evmLoc evmRead I price slice owe0 owe
            tabNew lotNew) (immStore v))
        evmVat) := by
  have hguard :
      evalExpr? config
        (Frame.mk contract (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe
            tabNew lotNew) (immStore v))
        evmRead (.binary .gt (.extCodeSize vatExpr) (.intLit 0)) =
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
          (clipperTakeDecodeFluxVoid outVat))
        ExecBlock.nil))

theorem clipperTakeNoAdjustPostSubVatFluxNoCodeBlock (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe : UInt256)
    (howeTab : owe.toNat ≤ (clipperTakeSalesTabEVMWord evmRead I).toNat)
    (hsliceLot : slice.toNat ≤ (clipperTakeSalesLotEVMWord evmRead I).toNat)
    (hnoVatCode :
      (UInt256.ofNat ((evmRead.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat =
        0) :
    ExecBlock config
      (Frame.mk contract (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe) (immStore v))
      evmRead
      (wrappingSubInto "tabNew" (.var "tab") (.var "owe") ++
        wrappingSubInto "lotNew" (.var "lot") (.var "slice") ++
        [ .assign .localVar (varRef "tab") (.var "tabNew"),
          .assign .localVar (varRef "lot") (.var "lotNew") ] ++
        checkedExternalCallStmts vatExpr "flux" (.intLit 0)
          [ilkExpr, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet")
      .reverted := by
  let tabNew := UInt256.sub (clipperTakeSalesTabEVMWord evmRead I) owe
  let lotNew := UInt256.sub (clipperTakeSalesLotEVMWord evmRead I) slice
  let oweFrame : Frame :=
    Frame.mk contract (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe) (immStore v)
  let postSubFrame : Frame :=
    Frame.mk contract (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe tabNew
        lotNew) (immStore v)
  have hsubBlock :
      ExecBlock config oweFrame evmRead
        (wrappingSubInto "tabNew" (.var "tab") (.var "owe") ++
          wrappingSubInto "lotNew" (.var "lot") (.var "slice") ++
          [ .assign .localVar (varRef "tab") (.var "tabNew"),
            .assign .localVar (varRef "lot") (.var "lotNew") ])
        (.ok postSubFrame evmRead) := by
    simpa [oweFrame, postSubFrame, tabNew, lotNew] using
      clipperTakePostNoAdjustSubBlock v evmLoc evmRead I price slice owe0 owe howeTab
        hsliceLot
  have hvatRevert :
      ExecBlock config postSubFrame evmRead
        (checkedExternalCallStmts vatExpr "flux" (.intLit 0)
          [ilkExpr, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet")
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
      typedCallViaEVM config evmRead (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmRead.executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
          .int (Int.ofNat slice.toNat)]
        (false, evmVat, outVat) true) :
    ExecBlock config
      (Frame.mk contract (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe) (immStore v))
      evmRead
      (wrappingSubInto "tabNew" (.var "tab") (.var "owe") ++
        wrappingSubInto "lotNew" (.var "lot") (.var "slice") ++
        [ .assign .localVar (varRef "tab") (.var "tabNew"),
          .assign .localVar (varRef "lot") (.var "lotNew") ] ++
        checkedExternalCallStmts vatExpr "flux" (.intLit 0)
          [ilkExpr, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet")
      .reverted := by
  let tabNew := UInt256.sub (clipperTakeSalesTabEVMWord evmRead I) owe
  let lotNew := UInt256.sub (clipperTakeSalesLotEVMWord evmRead I) slice
  let oweFrame : Frame :=
    Frame.mk contract (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe) (immStore v)
  let postSubFrame : Frame :=
    Frame.mk contract (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe tabNew
        lotNew) (immStore v)
  have hsubBlock :
      ExecBlock config oweFrame evmRead
        (wrappingSubInto "tabNew" (.var "tab") (.var "owe") ++
          wrappingSubInto "lotNew" (.var "lot") (.var "slice") ++
          [ .assign .localVar (varRef "tab") (.var "tabNew"),
            .assign .localVar (varRef "lot") (.var "lotNew") ])
        (.ok postSubFrame evmRead) := by
    simpa [oweFrame, postSubFrame, tabNew, lotNew] using
      clipperTakePostNoAdjustSubBlock v evmLoc evmRead I price slice owe0 owe howeTab
        hsliceLot
  have hargs :
      evalExprs? config postSubFrame evmRead
        [ilkExpr, thisAddr, .var "who", .var "slice"] =
          .ok
            [v.ilk, .address evmRead.executionEnv.codeOwner,
              .address (AccountAddress.ofNat
                (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
              .int (Int.ofNat slice.toNat)] := by
    simpa [postSubFrame] using
      clipperEvalTakeNoAdjustVatFluxBuyerArgs v evmLoc evmRead I price slice owe0 owe
        tabNew lotNew
  have hvatRevert :
      ExecBlock config postSubFrame evmRead
        (checkedExternalCallStmts vatExpr "flux" (.intLit 0)
          [ilkExpr, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet")
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
      typedCallViaEVM config evmRead (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmRead.executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
          .int (Int.ofNat slice.toNat)]
        (true, evmVat, outVat) true) :
    let tabNew := UInt256.sub (clipperTakeSalesTabEVMWord evmRead I) owe
    let lotNew := UInt256.sub (clipperTakeSalesLotEVMWord evmRead I) slice
    ExecBlock config
      (Frame.mk contract (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe) (immStore v))
      evmRead
      (wrappingSubInto "tabNew" (.var "tab") (.var "owe") ++
        wrappingSubInto "lotNew" (.var "lot") (.var "slice") ++
        [ .assign .localVar (varRef "tab") (.var "tabNew"),
          .assign .localVar (varRef "lot") (.var "lotNew") ] ++
        checkedExternalCallStmts vatExpr "flux" (.intLit 0)
          [ilkExpr, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet")
      (.ok
        (Frame.mk contract (clipperTakeLocalsNoAdjustFluxBuyerRet evmLoc evmRead I price slice owe0 owe
            tabNew lotNew) (immStore v))
        evmVat) := by
  intro tabNew lotNew
  let oweFrame : Frame :=
    Frame.mk contract (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe) (immStore v)
  let postSubFrame : Frame :=
    Frame.mk contract (clipperTakeLocalsNoAdjustLotAssigned evmLoc evmRead I price slice owe0 owe tabNew
        lotNew) (immStore v)
  let fluxFrame : Frame :=
    Frame.mk contract (clipperTakeLocalsNoAdjustFluxBuyerRet evmLoc evmRead I price slice owe0 owe tabNew
        lotNew) (immStore v)
  have hsubBlock :
      ExecBlock config oweFrame evmRead
        (wrappingSubInto "tabNew" (.var "tab") (.var "owe") ++
          wrappingSubInto "lotNew" (.var "lot") (.var "slice") ++
          [ .assign .localVar (varRef "tab") (.var "tabNew"),
            .assign .localVar (varRef "lot") (.var "lotNew") ])
        (.ok postSubFrame evmRead) := by
    simpa [oweFrame, postSubFrame, tabNew, lotNew] using
      clipperTakePostNoAdjustSubBlock v evmLoc evmRead I price slice owe0 owe howeTab
        hsliceLot
  have hargs :
      evalExprs? config postSubFrame evmRead
        [ilkExpr, thisAddr, .var "who", .var "slice"] =
          .ok
            [v.ilk, .address evmRead.executionEnv.codeOwner,
              .address (AccountAddress.ofNat
                (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
              .int (Int.ofNat slice.toNat)] := by
    simpa [postSubFrame] using
      clipperEvalTakeNoAdjustVatFluxBuyerArgs v evmLoc evmRead I price slice owe0 owe
        tabNew lotNew
  have hvatOk :
      ExecBlock config postSubFrame evmRead
        (checkedExternalCallStmts vatExpr "flux" (.intLit 0)
          [ilkExpr, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet")
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
      ExecStmt config
        (Frame.mk contract (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0) (immStore v))
        evmRead clipperTakeOweAdjustmentStmt
        (.ok
          (Frame.mk contract (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0) (immStore v))
          evmRead))
    (hnoVatCode :
      (UInt256.ofNat ((evmRead.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat =
        0) :
    ExecBlock config
      (Frame.mk contract (clipperTakeLocalsSlice evmLoc evmRead I false price slice) (immStore v))
      evmRead
      (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
        [ .letDecl "owe" (some uint256) (.var "owe0"),
          clipperTakeOweAdjustmentStmt ] ++
        clipperTakePostOweFluxStmts)
      .reverted := by
  let owe0 := UInt256.mul slice price
  let sliceFrame : Frame :=
    Frame.mk contract (clipperTakeLocalsSlice evmLoc evmRead I false price slice) (immStore v)
  let oweFrame : Frame :=
    Frame.mk contract (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0) (immStore v)
  have hmulBlock :
      ExecBlock config sliceFrame evmRead
        (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
          [.letDecl "owe" (some uint256) (.var "owe0")])
        (.ok oweFrame evmRead) := by
    simpa [sliceFrame, oweFrame, owe0] using
      clipperTakeOwe0MulSuccessBlock v evmLoc evmRead I price slice hmul
  have hpost :
      ExecBlock config oweFrame evmRead (clipperTakePostOweFluxStmts) .reverted := by
    simpa [clipperTakePostOweFluxStmts, oweFrame, owe0] using
      clipperTakeNoAdjustPostSubVatFluxNoCodeBlock v evmLoc evmRead I price slice owe0
        owe0 howeTab hsliceLot hnoVatCode
  have hafterIte :
      ExecBlock config oweFrame evmRead
        (clipperTakeOweAdjustmentStmt :: clipperTakePostOweFluxStmts) .reverted :=
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
      ExecStmt config
        (Frame.mk contract (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0) (immStore v))
        evmRead clipperTakeOweAdjustmentStmt
        (.ok
          (Frame.mk contract (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0) (immStore v))
          evmRead))
    (hvatCode :
      0 <
        (UInt256.ofNat ((evmRead.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallVat :
      typedCallViaEVM config evmRead (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmRead.executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
          .int (Int.ofNat slice.toNat)]
        (false, evmVat, outVat) true) :
    ExecBlock config
      (Frame.mk contract (clipperTakeLocalsSlice evmLoc evmRead I false price slice) (immStore v))
      evmRead
      (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
        [ .letDecl "owe" (some uint256) (.var "owe0"),
          clipperTakeOweAdjustmentStmt ] ++
        clipperTakePostOweFluxStmts)
      .reverted := by
  let owe0 := UInt256.mul slice price
  let sliceFrame : Frame :=
    Frame.mk contract (clipperTakeLocalsSlice evmLoc evmRead I false price slice) (immStore v)
  let oweFrame : Frame :=
    Frame.mk contract (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0) (immStore v)
  have hmulBlock :
      ExecBlock config sliceFrame evmRead
        (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
          [.letDecl "owe" (some uint256) (.var "owe0")])
        (.ok oweFrame evmRead) := by
    simpa [sliceFrame, oweFrame, owe0] using
      clipperTakeOwe0MulSuccessBlock v evmLoc evmRead I price slice hmul
  have hpost :
      ExecBlock config oweFrame evmRead (clipperTakePostOweFluxStmts) .reverted := by
    simpa [clipperTakePostOweFluxStmts, oweFrame, owe0] using
      clipperTakeNoAdjustPostSubVatFluxCallFailureBlock v evmLoc evmRead evmVat I price
        slice owe0 owe0 howeTab hsliceLot hvatCode hcallVat
  have hafterIte :
      ExecBlock config oweFrame evmRead
        (clipperTakeOweAdjustmentStmt :: clipperTakePostOweFluxStmts) .reverted :=
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
      ExecStmt config
        (Frame.mk contract (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0) (immStore v))
        evmRead clipperTakeOweAdjustmentStmt
        (.ok
          (Frame.mk contract (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0) (immStore v))
          evmRead))
    (hvatCode :
      0 <
        (UInt256.ofNat ((evmRead.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallVat :
      typedCallViaEVM config evmRead (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmRead.executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
          .int (Int.ofNat slice.toNat)]
        (true, evmVat, outVat) true) :
    let owe0 := UInt256.mul slice price
    let tabNew := UInt256.sub (clipperTakeSalesTabEVMWord evmRead I) owe0
    let lotNew := UInt256.sub (clipperTakeSalesLotEVMWord evmRead I) slice
    ExecBlock config
      (Frame.mk contract (clipperTakeLocalsSlice evmLoc evmRead I false price slice) (immStore v))
      evmRead
      (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
        [ .letDecl "owe" (some uint256) (.var "owe0"),
          clipperTakeOweAdjustmentStmt ] ++
        clipperTakePostOweFluxStmts)
      (.ok
        (Frame.mk contract (clipperTakeLocalsNoAdjustFluxBuyerRet evmLoc evmRead I price slice owe0 owe0
            tabNew lotNew) (immStore v))
        evmVat) := by
  intro owe0 tabNew lotNew
  let sliceFrame : Frame :=
    Frame.mk contract (clipperTakeLocalsSlice evmLoc evmRead I false price slice) (immStore v)
  let oweFrame : Frame :=
    Frame.mk contract (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0) (immStore v)
  let fluxFrame : Frame :=
    Frame.mk contract (clipperTakeLocalsNoAdjustFluxBuyerRet evmLoc evmRead I price slice owe0 owe0 tabNew
        lotNew) (immStore v)
  have hmulBlock :
      ExecBlock config sliceFrame evmRead
        (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
          [.letDecl "owe" (some uint256) (.var "owe0")])
        (.ok oweFrame evmRead) := by
    simpa [sliceFrame, oweFrame, owe0] using
      clipperTakeOwe0MulSuccessBlock v evmLoc evmRead I price slice hmul
  have hpost :
      ExecBlock config oweFrame evmRead (clipperTakePostOweFluxStmts)
        (.ok fluxFrame evmVat) := by
    simpa [clipperTakePostOweFluxStmts, oweFrame, fluxFrame, owe0, tabNew, lotNew] using
      clipperTakeNoAdjustPostSubVatFluxCallSuccessBlock v evmLoc evmRead evmVat I price
        slice owe0 owe0 howeTab hsliceLot hvatCode hcallVat
  have hafterIte :
      ExecBlock config oweFrame evmRead
        (clipperTakeOweAdjustmentStmt :: clipperTakePostOweFluxStmts)
        (.ok fluxFrame evmVat) :=
    ExecBlock.consNormal (by simpa [oweFrame, owe0] using hite) hpost
  simpa [sliceFrame, fluxFrame, clipperTakePostOweFluxStmts, List.append_assoc] using
    execBlockAppendOk hmulBlock hafterIte

end Benchmarks.Dss.Clipper
