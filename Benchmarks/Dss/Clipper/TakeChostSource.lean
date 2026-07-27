import Benchmarks.Dss.Clipper.TakeNoAdjustSource
import Benchmarks.Dss.Clipper.Chost

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option maxHeartbeats 1200000

abbrev clipperTakeLocalsChost (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe chost : UInt256) : Store :=
  (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe).insert
    "_chost" (.int (Int.ofNat chost.toNat))

abbrev clipperTakeLocalsRemainingTab (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe chost remainingTab : UInt256) : Store :=
  (clipperTakeLocalsChost evmLoc evmRead I price slice owe0 owe chost).insert
    "remainingTab" (.int (Int.ofNat remainingTab.toNat))

abbrev clipperTakeLocalsOweAdjusted (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe chost remainingTab oweAdjusted : UInt256) : Store :=
  (clipperTakeLocalsRemainingTab evmLoc evmRead I price slice owe0 owe chost remainingTab).insert
    "oweAdjusted" (.int (Int.ofNat oweAdjusted.toNat))

abbrev clipperTakeLocalsChostOwe (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe chost remainingTab oweAdjusted : UInt256) : Store :=
  (clipperTakeLocalsOweAdjusted evmLoc evmRead I price slice owe0 owe chost remainingTab
    oweAdjusted).insert "owe" (.int (Int.ofNat oweAdjusted.toNat))

abbrev clipperTakeLocalsChostOweSlice (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe chost remainingTab oweAdjusted sliceAdjusted : UInt256) : Store :=
  (clipperTakeLocalsChostOwe evmLoc evmRead I price slice owe0 owe chost remainingTab
    oweAdjusted).insert "slice" (.int (Int.ofNat sliceAdjusted.toNat))

theorem clipperEvalTakeNoChostCond_true (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (price slice owe0 owe : UInt256)
    (hlt : owe.toNat < (clipperTakeSalesTabEVMWord evmRead I).toNat)
    (hsliceLt : slice.toNat < (clipperTakeSalesLotEVMWord evmRead I).toNat) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe }
      evmRead
      (.binary .and (.binary .lt (.var "owe") (.var "tab"))
        (.binary .lt (.var "slice") (.var "lot"))) = .ok (.bool true) := by
  have hleft :=
    clipperEvalTakeOweLtTab_true v evmLoc evmRead I price slice owe0 owe hlt
  have hright :
      evalExpr? (config v)
        { contract := contract v,
          locals := clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe }
        evmRead (.binary .lt (.var "slice") (.var "lot")) = .ok (.bool true) := by
    simp only [evalExpr?, EvalResult.bind, bind,
      clipperEvalTakeVarSliceAtOwe v evmLoc evmRead evmRead I false price slice owe0 owe,
      clipperEvalTakeVarLotAtOwe v evmLoc evmRead evmRead I false price slice owe0 owe]
    simp [evalBinaryOp?]
    exact hsliceLt
  simp [evalExpr?, hleft, hright, EvalResult.bind, bind, pure]

theorem clipperEvalTakeVarTabAtChost (v : ClipperImmutables)
    (evmLoc evmRead evmEval : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe chost : UInt256) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperTakeLocalsChost evmLoc evmRead I price slice owe0 owe chost }
      evmEval (.var "tab") =
      .ok (.int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsChost, store_get_ne _ _ (by decide), clipperTakeLocalsOwe,
    store_get_ne _ _ (by decide), clipperTakeLocalsOwe0, store_get_ne _ _ (by decide),
    clipperTakeLocalsSlice, store_get_ne _ _ (by decide), clipperTakeLocalsTab,
    store_get_self]
  rfl

theorem clipperEvalTakeVarOweAtChost (v : ClipperImmutables)
    (evmLoc evmRead evmEval : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe chost : UInt256) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperTakeLocalsChost evmLoc evmRead I price slice owe0 owe chost }
      evmEval (.var "owe") = .ok (.int (Int.ofNat owe.toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsChost, store_get_ne _ _ (by decide), clipperTakeLocalsOwe,
    store_get_self]
  rfl

theorem clipperEvalTakeTabSubOweAtChost (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe chost : UInt256)
    (howeTab : owe.toNat ≤ (clipperTakeSalesTabEVMWord evmRead I).toNat) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperTakeLocalsChost evmLoc evmRead I price slice owe0 owe chost }
      evmRead (wrap256 (.binary .sub (.var "tab") (.var "owe"))) =
      .ok (.int (Int.ofNat (UInt256.sub (clipperTakeSalesTabEVMWord evmRead I) owe).toNat)) := by
  let tab := clipperTakeSalesTabEVMWord evmRead I
  have hsubNat : (UInt256.sub tab owe).toNat = tab.toNat - owe.toNat := by
    exact usub_toNat howeTab
  have hdiff :
      Int.ofNat tab.toNat - Int.ofNat owe.toNat = Int.ofNat (tab.toNat - owe.toNat) := by
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
      (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat - Int.ofNat owe.toNat) %
          wordModulus =
        Int.ofNat ((clipperTakeSalesTabEVMWord evmRead I).toNat - owe.toNat) := by
    rw [show Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat -
        Int.ofNat owe.toNat = Int.ofNat (tab.toNat - owe.toNat) by
      simpa [tab] using hdiff]
    simpa [tab] using hmod
  simp [wrap256, evalExpr?, EvalResult.bind, bind,
    clipperEvalTakeVarTabAtChost v evmLoc evmRead evmRead I price slice owe0 owe chost,
    clipperEvalTakeVarOweAtChost v evmLoc evmRead evmRead I price slice owe0 owe chost,
    evalBinaryOp?, hsubNat, hwordNonzero, tab]
  exact hmodLoad

theorem clipperEvalTakeRemainingTabLtChost_false (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe chost remainingTab : UInt256)
    (hchostLe : chost.toNat ≤ remainingTab.toNat) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperTakeLocalsRemainingTab evmLoc evmRead I price slice owe0 owe chost
          remainingTab }
      evmRead (.binary .lt (.var "remainingTab") (.var "_chost")) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.bind, bind]
  rw [clipperTakeLocalsRemainingTab, store_get_self, store_get_ne _ _ (by decide),
    clipperTakeLocalsChost, store_get_self]
  change evalBinaryOp? .lt (.int (Int.ofNat remainingTab.toNat))
      (.int (Int.ofNat chost.toNat)) = .ok (.bool false)
  simp [evalBinaryOp?]
  exact hchostLe

theorem clipperEvalTakeRemainingTabLtChost_true (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe chost remainingTab : UInt256)
    (hlt : remainingTab.toNat < chost.toNat) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperTakeLocalsRemainingTab evmLoc evmRead I price slice owe0 owe chost
          remainingTab }
      evmRead (.binary .lt (.var "remainingTab") (.var "_chost")) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.bind, bind]
  rw [clipperTakeLocalsRemainingTab, store_get_self, store_get_ne _ _ (by decide),
    clipperTakeLocalsChost, store_get_self]
  change evalBinaryOp? .lt (.int (Int.ofNat remainingTab.toNat))
      (.int (Int.ofNat chost.toNat)) = .ok (.bool true)
  simp [evalBinaryOp?]
  exact hlt

theorem clipperEvalTakeVarTabAtRemainingTab (v : ClipperImmutables)
    (evmLoc evmRead evmEval : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe chost remainingTab : UInt256) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperTakeLocalsRemainingTab evmLoc evmRead I price slice owe0 owe chost
          remainingTab }
      evmEval (.var "tab") =
      .ok (.int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsRemainingTab, store_get_ne _ _ (by decide),
    clipperTakeLocalsChost, store_get_ne _ _ (by decide), clipperTakeLocalsOwe,
    store_get_ne _ _ (by decide), clipperTakeLocalsOwe0, store_get_ne _ _ (by decide),
    clipperTakeLocalsSlice, store_get_ne _ _ (by decide), clipperTakeLocalsTab,
    store_get_self]
  rfl

theorem clipperEvalTakeVarChostAtRemainingTab (v : ClipperImmutables)
    (evmLoc evmRead evmEval : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe chost remainingTab : UInt256) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperTakeLocalsRemainingTab evmLoc evmRead I price slice owe0 owe chost
          remainingTab }
      evmEval (.var "_chost") = .ok (.int (Int.ofNat chost.toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsRemainingTab, store_get_ne _ _ (by decide),
    clipperTakeLocalsChost, store_get_self]
  rfl

theorem clipperEvalTakeTabGtChost_true (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe chost remainingTab : UInt256)
    (hlt : chost.toNat < (clipperTakeSalesTabEVMWord evmRead I).toNat) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperTakeLocalsRemainingTab evmLoc evmRead I price slice owe0 owe chost
          remainingTab }
      evmRead (.binary .gt (.var "tab") (.var "_chost")) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind,
    clipperEvalTakeVarTabAtRemainingTab v evmLoc evmRead evmRead I price slice owe0 owe
      chost remainingTab,
    clipperEvalTakeVarChostAtRemainingTab v evmLoc evmRead evmRead I price slice owe0 owe
      chost remainingTab,
    evalBinaryOp?]
  exact hlt

theorem clipperEvalTakeTabSubChostAtRemainingTab (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe chost remainingTab : UInt256)
    (hchostTab : chost.toNat ≤ (clipperTakeSalesTabEVMWord evmRead I).toNat) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperTakeLocalsRemainingTab evmLoc evmRead I price slice owe0 owe chost
          remainingTab }
      evmRead (wrap256 (.binary .sub (.var "tab") (.var "_chost"))) =
      .ok (.int
        (Int.ofNat (UInt256.sub (clipperTakeSalesTabEVMWord evmRead I) chost).toNat)) := by
  let tab := clipperTakeSalesTabEVMWord evmRead I
  have hsubNat : (UInt256.sub tab chost).toNat = tab.toNat - chost.toNat := by
    exact usub_toNat hchostTab
  have hdiff :
      Int.ofNat tab.toNat - Int.ofNat chost.toNat =
        Int.ofNat (tab.toNat - chost.toNat) := by
    exact (Int.ofNat_sub hchostTab).symm
  have hltNat : tab.toNat - chost.toNat < UInt256.size := by
    exact lt_of_le_of_lt (Nat.sub_le tab.toNat chost.toNat) tab.val.isLt
  have hlt : Int.ofNat (tab.toNat - chost.toNat) < wordModulus := by
    norm_num [wordModulus, UInt256.size] at hltNat ⊢
    exact_mod_cast hltNat
  have hmod :
      Int.ofNat (tab.toNat - chost.toNat) % wordModulus =
        Int.ofNat (tab.toNat - chost.toNat) := by
    rw [Int.emod_eq_of_lt]
    · exact Int.natCast_nonneg _
    · exact hlt
  have hwordNonzero : ¬wordModulus = 0 := by
    norm_num [wordModulus]
  have hmodLoad :
      (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat - Int.ofNat chost.toNat) %
          wordModulus =
        Int.ofNat ((clipperTakeSalesTabEVMWord evmRead I).toNat - chost.toNat) := by
    rw [show Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat -
        Int.ofNat chost.toNat = Int.ofNat (tab.toNat - chost.toNat) by
      simpa [tab] using hdiff]
    simpa [tab] using hmod
  simp [wrap256, evalExpr?, EvalResult.bind, bind,
    clipperEvalTakeVarTabAtRemainingTab v evmLoc evmRead evmRead I price slice owe0 owe
      chost remainingTab,
    clipperEvalTakeVarChostAtRemainingTab v evmLoc evmRead evmRead I price slice owe0 owe
      chost remainingTab,
    evalBinaryOp?, hsubNat, hwordNonzero, tab]
  exact hmodLoad

theorem clipperEvalTakeVarOweAdjusted (v : ClipperImmutables)
    (evmLoc evmRead evmEval : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe chost remainingTab oweAdjusted : UInt256) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperTakeLocalsOweAdjusted evmLoc evmRead I price slice owe0 owe chost
          remainingTab oweAdjusted }
      evmEval (.var "oweAdjusted") = .ok (.int (Int.ofNat oweAdjusted.toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsOweAdjusted, store_get_self]
  rfl

theorem clipperTakeAssignOweFromAdjusted (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe chost remainingTab oweAdjusted : UInt256) :
    ExecStmt (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsOweAdjusted evmLoc evmRead I price slice owe0 owe chost
          remainingTab oweAdjusted))
      evmRead (.assign .localVar (varRef "owe") (.var "oweAdjusted"))
      (.ok
        (Frame.mk (contract v)
          (clipperTakeLocalsChostOwe evmLoc evmRead I price slice owe0 owe chost
            remainingTab oweAdjusted))
        evmRead) := by
  let adjustedFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsOweAdjusted evmLoc evmRead I price slice owe0 owe chost remainingTab
        oweAdjusted)
  let oweFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsChostOwe evmLoc evmRead I price slice owe0 owe chost remainingTab
        oweAdjusted)
  have hrhs :
      evalExpr? (config v) adjustedFrame evmRead (.var "oweAdjusted") =
        .ok (.int (Int.ofNat oweAdjusted.toNat)) := by
    simpa [adjustedFrame] using
      clipperEvalTakeVarOweAdjusted v evmLoc evmRead evmRead I price slice owe0 owe chost
        remainingTab oweAdjusted
  have hassign :
      assignStorageRef? (config v) adjustedFrame evmRead .localVar (varRef "owe")
          (.int (Int.ofNat oweAdjusted.toNat)) =
        .ok (oweFrame, evmRead) := by
    simp [assignStorageRef?, updateLocalPath?, varRef, adjustedFrame, oweFrame,
      clipperTakeLocalsChostOwe, pure, bind, EvalResult.bind]
  simpa [adjustedFrame, oweFrame] using ExecStmt.assign hrhs hassign

theorem clipperEvalTakeVarOweAtChostOwe (v : ClipperImmutables)
    (evmLoc evmRead evmEval : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe chost remainingTab oweAdjusted : UInt256) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperTakeLocalsChostOwe evmLoc evmRead I price slice owe0 owe chost
          remainingTab oweAdjusted }
      evmEval (.var "owe") = .ok (.int (Int.ofNat oweAdjusted.toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsChostOwe, store_get_self]
  rfl

theorem clipperEvalTakeVarPriceAtChostOwe (v : ClipperImmutables)
    (evmLoc evmRead evmEval : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe chost remainingTab oweAdjusted : UInt256) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperTakeLocalsChostOwe evmLoc evmRead I price slice owe0 owe chost
          remainingTab oweAdjusted }
      evmEval (.var "price") = .ok (.int (Int.ofNat price.toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsChostOwe, store_get_ne _ _ (by decide),
    clipperTakeLocalsOweAdjusted, store_get_ne _ _ (by decide),
    clipperTakeLocalsRemainingTab, store_get_ne _ _ (by decide),
    clipperTakeLocalsChost, store_get_ne _ _ (by decide), clipperTakeLocalsOwe,
    store_get_ne _ _ (by decide), clipperTakeLocalsOwe0, store_get_ne _ _ (by decide),
    clipperTakeLocalsSlice, store_get_ne _ _ (by decide), clipperTakeLocalsTab,
    store_get_ne _ _ (by decide), clipperTakeLocalsLot, store_get_ne _ _ (by decide),
    clipperTakeLocalsPrice, store_get_self]
  rfl

theorem clipperEvalTakeOweDivPriceAtChostOwe (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe chost remainingTab oweAdjusted : UInt256)
    (hprice : price ≠ ⟨0⟩) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperTakeLocalsChostOwe evmLoc evmRead I price slice owe0 owe chost
          remainingTab oweAdjusted }
      evmRead (.binary .div (.var "owe") (.var "price")) =
      .ok (.int (Int.ofNat (UInt256.div oweAdjusted price).toNat)) := by
  have hpriceNat : ¬price.toNat = 0 := by
    intro hzero
    exact hprice (uint256_toNat_eq_zero hzero)
  have hdiv :
      Int.ofNat oweAdjusted.toNat / Int.ofNat price.toNat =
        Int.ofNat (UInt256.div oweAdjusted price).toNat := by
    rw [udiv_toNat]
    exact Int.ofNat_ediv_ofNat
  simp [evalExpr?, EvalResult.bind, bind, evalBinaryOp?,
    clipperEvalTakeVarOweAtChostOwe v evmLoc evmRead evmRead I price slice owe0 owe chost
      remainingTab oweAdjusted,
    clipperEvalTakeVarPriceAtChostOwe v evmLoc evmRead evmRead I price slice owe0 owe chost
      remainingTab oweAdjusted,
    hpriceNat]
  exact hdiv

theorem clipperTakeAssignSliceFromChostOwe (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe chost remainingTab oweAdjusted : UInt256)
    (hprice : price ≠ ⟨0⟩) :
    let sliceAdjusted := UInt256.div oweAdjusted price
    ExecStmt (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsChostOwe evmLoc evmRead I price slice owe0 owe chost remainingTab
          oweAdjusted))
      evmRead (.assign .localVar (varRef "slice") (.binary .div (.var "owe") (.var "price")))
      (.ok
        (Frame.mk (contract v)
          (clipperTakeLocalsChostOweSlice evmLoc evmRead I price slice owe0 owe chost
            remainingTab oweAdjusted sliceAdjusted))
        evmRead) := by
  intro sliceAdjusted
  let oweFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsChostOwe evmLoc evmRead I price slice owe0 owe chost remainingTab
        oweAdjusted)
  let sliceFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsChostOweSlice evmLoc evmRead I price slice owe0 owe chost
        remainingTab oweAdjusted sliceAdjusted)
  have hrhs :
      evalExpr? (config v) oweFrame evmRead
          (.binary .div (.var "owe") (.var "price")) =
        .ok (.int (Int.ofNat sliceAdjusted.toNat)) := by
    simpa [oweFrame, sliceAdjusted] using
      clipperEvalTakeOweDivPriceAtChostOwe v evmLoc evmRead I price slice owe0 owe chost
        remainingTab oweAdjusted hprice
  have hassign :
      assignStorageRef? (config v) oweFrame evmRead .localVar (varRef "slice")
          (.int (Int.ofNat sliceAdjusted.toNat)) =
        .ok (sliceFrame, evmRead) := by
    simp [assignStorageRef?, updateLocalPath?, varRef, oweFrame, sliceFrame,
      clipperTakeLocalsChostOweSlice, pure, bind, EvalResult.bind]
  simpa [oweFrame, sliceFrame] using ExecStmt.assign hrhs hassign

theorem clipperTakeOweLtTabSliceLtLotChostNoAdjustIte (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (price slice : UInt256)
    (hle : (UInt256.mul slice price).toNat ≤ (clipperTakeSalesTabEVMWord evmRead I).toNat)
    (hlt : (UInt256.mul slice price).toNat < (clipperTakeSalesTabEVMWord evmRead I).toNat)
    (hsliceLt : slice.toNat < (clipperTakeSalesLotEVMWord evmRead I).toNat)
    (hchostLe :
      (Solm.EVM.storageLoad evmRead evmRead.executionEnv.codeOwner ⟨9⟩).toNat ≤
        (UInt256.sub (clipperTakeSalesTabEVMWord evmRead I)
          (UInt256.mul slice price)).toNat) :
    let owe0 := UInt256.mul slice price
    let chost := Solm.EVM.storageLoad evmRead evmRead.executionEnv.codeOwner ⟨9⟩
    let remainingTab := UInt256.sub (clipperTakeSalesTabEVMWord evmRead I) owe0
    ExecStmt (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0))
      evmRead clipperTakeOweAdjustmentStmt
      (.ok
        (Frame.mk (contract v)
          (clipperTakeLocalsRemainingTab evmLoc evmRead I price slice owe0 owe0 chost
            remainingTab))
        evmRead) := by
  intro owe0 chost remainingTab
  let oweFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0)
  let chostFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsChost evmLoc evmRead I price slice owe0 owe0 chost)
  let remainingFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsRemainingTab evmLoc evmRead I price slice owe0 owe0 chost remainingTab)
  have houter :
      evalExpr? (config v) oweFrame evmRead
        (.binary .gt (.var "owe") (.var "tab")) = .ok (.bool false) := by
    simpa [oweFrame, owe0] using
      clipperEvalTakeOweGtTab_false v evmLoc evmRead I price slice owe0 owe0 hle
  have hinnerCond :
      evalExpr? (config v) oweFrame evmRead
        (.binary .and (.binary .lt (.var "owe") (.var "tab"))
          (.binary .lt (.var "slice") (.var "lot"))) = .ok (.bool true) := by
    simpa [oweFrame, owe0] using
      clipperEvalTakeNoChostCond_true v evmLoc evmRead I price slice owe0 owe0 hlt hsliceLt
  have hbase :
      (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0).get? "chost" =
        none := by
    simp [clipperTakeLocalsOwe, clipperTakeLocalsOwe0, clipperTakeLocalsSlice,
      clipperTakeLocalsTab, clipperTakeLocalsLot, clipperTakeLocalsPrice,
      clipperTakeLocalsDone, clipperTakeLocalsSt, clipperTakeLocalsTic,
      clipperTakeLocalsUsr, clipperTakeStore]
  have hletChost :
      ExecStmt (config v) oweFrame evmRead
        (.letDecl "_chost" (some uint256) (.storage chostRef))
        (.ok chostFrame evmRead) := by
    simpa [oweFrame, chostFrame, chost, clipperTakeLocalsChost] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := oweFrame) (evm := evmRead) (name := "_chost")
        (ty := some uint256) (expr := .storage chostRef)
        (value := .int (Int.ofNat chost.toNat))
        (by simpa [oweFrame, chost] using
          (clipperEvalChost v evmRead
            (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0) hbase)))
  have hletRemaining :
      ExecStmt (config v) chostFrame evmRead
        (.letDecl "remainingTab" (some uint256)
          (wrap256 (.binary .sub (.var "tab") (.var "owe"))))
        (.ok remainingFrame evmRead) := by
    simpa [chostFrame, remainingFrame, remainingTab, clipperTakeLocalsRemainingTab] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := chostFrame) (evm := evmRead) (name := "remainingTab")
        (ty := some uint256) (expr := wrap256 (.binary .sub (.var "tab") (.var "owe")))
        (value := .int (Int.ofNat remainingTab.toNat))
        (by simpa [chostFrame, remainingTab, owe0] using
          (clipperEvalTakeTabSubOweAtChost v evmLoc evmRead I price slice owe0 owe0 chost
            hle)))
  have hadjustCond :
      evalExpr? (config v) remainingFrame evmRead
        (.binary .lt (.var "remainingTab") (.var "_chost")) = .ok (.bool false) := by
    simpa [remainingFrame, chost, remainingTab] using
      clipperEvalTakeRemainingTabLtChost_false v evmLoc evmRead I price slice owe0 owe0
        chost remainingTab hchostLe
  have hadjust :
      ExecStmt (config v) remainingFrame evmRead
        (.ite (.binary .lt (.var "remainingTab") (.var "_chost"))
          ([ .require (.binary .gt (.var "tab") (.var "_chost")) ] ++
            wrappingSubInto "oweAdjusted" (.var "tab") (.var "_chost") ++
            [ .assign .localVar (varRef "owe") (.var "oweAdjusted"),
              .assign .localVar (varRef "slice") (.binary .div (.var "owe") (.var "price")) ])
          [])
        (.ok remainingFrame evmRead) :=
    ExecStmt.iteFalse hadjustCond ExecBlock.nil
  have hinnerBlock :
      ExecBlock (config v) oweFrame evmRead
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
        (.ok remainingFrame evmRead) := by
    simpa [wrappingSubInto, remainingFrame] using
      (ExecBlock.consNormal hletChost
        (ExecBlock.consNormal hletRemaining
          (ExecBlock.consNormal hadjust ExecBlock.nil)))
  have hinner :
      ExecStmt (config v) oweFrame evmRead
        (.ite
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
          [])
        (.ok remainingFrame evmRead) :=
    ExecStmt.iteTrue hinnerCond hinnerBlock
  have helse :
      ExecBlock (config v) oweFrame evmRead
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
        (.ok remainingFrame evmRead) :=
    ExecBlock.consNormal hinner ExecBlock.nil
  simpa [clipperTakeOweAdjustmentStmt, oweFrame, remainingFrame] using
    ExecStmt.iteFalse houter helse

theorem clipperTakeOweLtTabSliceLtLotChostAdjustIte (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (price slice : UInt256)
    (hle : (UInt256.mul slice price).toNat ≤ (clipperTakeSalesTabEVMWord evmRead I).toNat)
    (hlt : (UInt256.mul slice price).toNat < (clipperTakeSalesTabEVMWord evmRead I).toNat)
    (hsliceLt : slice.toNat < (clipperTakeSalesLotEVMWord evmRead I).toNat)
    (hremainingLt :
      (UInt256.sub (clipperTakeSalesTabEVMWord evmRead I)
          (UInt256.mul slice price)).toNat <
        (Solm.EVM.storageLoad evmRead evmRead.executionEnv.codeOwner ⟨9⟩).toNat)
    (hchostTab :
      (Solm.EVM.storageLoad evmRead evmRead.executionEnv.codeOwner ⟨9⟩).toNat <
        (clipperTakeSalesTabEVMWord evmRead I).toNat)
    (hprice : price ≠ ⟨0⟩) :
    let owe0 := UInt256.mul slice price
    let chost := Solm.EVM.storageLoad evmRead evmRead.executionEnv.codeOwner ⟨9⟩
    let remainingTab := UInt256.sub (clipperTakeSalesTabEVMWord evmRead I) owe0
    let oweAdjusted := UInt256.sub (clipperTakeSalesTabEVMWord evmRead I) chost
    let sliceAdjusted := UInt256.div oweAdjusted price
    ExecStmt (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0))
      evmRead clipperTakeOweAdjustmentStmt
      (.ok
        (Frame.mk (contract v)
          (clipperTakeLocalsChostOweSlice evmLoc evmRead I price slice owe0 owe0 chost
            remainingTab oweAdjusted sliceAdjusted))
        evmRead) := by
  intro owe0 chost remainingTab oweAdjusted sliceAdjusted
  let oweFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0)
  let chostFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsChost evmLoc evmRead I price slice owe0 owe0 chost)
  let remainingFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsRemainingTab evmLoc evmRead I price slice owe0 owe0 chost remainingTab)
  let adjustedFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsOweAdjusted evmLoc evmRead I price slice owe0 owe0 chost remainingTab
        oweAdjusted)
  let chostOweFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsChostOwe evmLoc evmRead I price slice owe0 owe0 chost remainingTab
        oweAdjusted)
  let sliceFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsChostOweSlice evmLoc evmRead I price slice owe0 owe0 chost
        remainingTab oweAdjusted sliceAdjusted)
  have houter :
      evalExpr? (config v) oweFrame evmRead
        (.binary .gt (.var "owe") (.var "tab")) = .ok (.bool false) := by
    simpa [oweFrame, owe0] using
      clipperEvalTakeOweGtTab_false v evmLoc evmRead I price slice owe0 owe0 hle
  have hinnerCond :
      evalExpr? (config v) oweFrame evmRead
        (.binary .and (.binary .lt (.var "owe") (.var "tab"))
          (.binary .lt (.var "slice") (.var "lot"))) = .ok (.bool true) := by
    simpa [oweFrame, owe0] using
      clipperEvalTakeNoChostCond_true v evmLoc evmRead I price slice owe0 owe0 hlt hsliceLt
  have hbase :
      (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0).get? "chost" =
        none := by
    simp [clipperTakeLocalsOwe, clipperTakeLocalsOwe0, clipperTakeLocalsSlice,
      clipperTakeLocalsTab, clipperTakeLocalsLot, clipperTakeLocalsPrice,
      clipperTakeLocalsDone, clipperTakeLocalsSt, clipperTakeLocalsTic,
      clipperTakeLocalsUsr, clipperTakeStore]
  have hletChost :
      ExecStmt (config v) oweFrame evmRead
        (.letDecl "_chost" (some uint256) (.storage chostRef))
        (.ok chostFrame evmRead) := by
    simpa [oweFrame, chostFrame, chost, clipperTakeLocalsChost] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := oweFrame) (evm := evmRead) (name := "_chost")
        (ty := some uint256) (expr := .storage chostRef)
        (value := .int (Int.ofNat chost.toNat))
        (by simpa [oweFrame, chost] using
          (clipperEvalChost v evmRead
            (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0) hbase)))
  have hletRemaining :
      ExecStmt (config v) chostFrame evmRead
        (.letDecl "remainingTab" (some uint256)
          (wrap256 (.binary .sub (.var "tab") (.var "owe"))))
        (.ok remainingFrame evmRead) := by
    simpa [chostFrame, remainingFrame, remainingTab, clipperTakeLocalsRemainingTab] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := chostFrame) (evm := evmRead) (name := "remainingTab")
        (ty := some uint256) (expr := wrap256 (.binary .sub (.var "tab") (.var "owe")))
        (value := .int (Int.ofNat remainingTab.toNat))
        (by simpa [chostFrame, remainingTab, owe0] using
          (clipperEvalTakeTabSubOweAtChost v evmLoc evmRead I price slice owe0 owe0 chost
            hle)))
  have hadjustCond :
      evalExpr? (config v) remainingFrame evmRead
        (.binary .lt (.var "remainingTab") (.var "_chost")) = .ok (.bool true) := by
    simpa [remainingFrame, chost, remainingTab] using
      clipperEvalTakeRemainingTabLtChost_true v evmLoc evmRead I price slice owe0 owe0 chost
        remainingTab hremainingLt
  have hrequireCond :
      evalExpr? (config v) remainingFrame evmRead
        (.binary .gt (.var "tab") (.var "_chost")) = .ok (.bool true) := by
    simpa [remainingFrame, chost] using
      clipperEvalTakeTabGtChost_true v evmLoc evmRead I price slice owe0 owe0 chost
        remainingTab hchostTab
  have hletAdjusted :
      ExecStmt (config v) remainingFrame evmRead
        (.letDecl "oweAdjusted" (some uint256)
          (wrap256 (.binary .sub (.var "tab") (.var "_chost"))))
        (.ok adjustedFrame evmRead) := by
    have hleChost : chost.toNat ≤ (clipperTakeSalesTabEVMWord evmRead I).toNat :=
      Nat.le_of_lt hchostTab
    simpa [remainingFrame, adjustedFrame, oweAdjusted, clipperTakeLocalsOweAdjusted] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := remainingFrame) (evm := evmRead) (name := "oweAdjusted")
        (ty := some uint256)
        (expr := wrap256 (.binary .sub (.var "tab") (.var "_chost")))
        (value := .int (Int.ofNat oweAdjusted.toNat))
        (by simpa [remainingFrame, oweAdjusted, chost] using
          (clipperEvalTakeTabSubChostAtRemainingTab v evmLoc evmRead I price slice owe0
            owe0 chost remainingTab hleChost)))
  have hassignOwe :
      ExecStmt (config v) adjustedFrame evmRead
        (.assign .localVar (varRef "owe") (.var "oweAdjusted"))
        (.ok chostOweFrame evmRead) := by
    simpa [adjustedFrame, chostOweFrame] using
      clipperTakeAssignOweFromAdjusted v evmLoc evmRead I price slice owe0 owe0 chost
        remainingTab oweAdjusted
  have hassignSlice :
      ExecStmt (config v) chostOweFrame evmRead
        (.assign .localVar (varRef "slice") (.binary .div (.var "owe") (.var "price")))
        (.ok sliceFrame evmRead) := by
    simpa [chostOweFrame, sliceFrame, sliceAdjusted] using
      clipperTakeAssignSliceFromChostOwe v evmLoc evmRead I price slice owe0 owe0 chost
        remainingTab oweAdjusted hprice
  have hadjustBlock :
      ExecBlock (config v) remainingFrame evmRead
        ([ .require (.binary .gt (.var "tab") (.var "_chost")) ] ++
          wrappingSubInto "oweAdjusted" (.var "tab") (.var "_chost") ++
          [ .assign .localVar (varRef "owe") (.var "oweAdjusted"),
            .assign .localVar (varRef "slice") (.binary .div (.var "owe") (.var "price")) ])
        (.ok sliceFrame evmRead) := by
    simpa [wrappingSubInto, sliceFrame] using
      (ExecBlock.consNormal (ExecStmt.requireTrue hrequireCond)
        (ExecBlock.consNormal hletAdjusted
          (ExecBlock.consNormal hassignOwe
            (ExecBlock.consNormal hassignSlice ExecBlock.nil))))
  have hadjust :
      ExecStmt (config v) remainingFrame evmRead
        (.ite (.binary .lt (.var "remainingTab") (.var "_chost"))
          ([ .require (.binary .gt (.var "tab") (.var "_chost")) ] ++
            wrappingSubInto "oweAdjusted" (.var "tab") (.var "_chost") ++
            [ .assign .localVar (varRef "owe") (.var "oweAdjusted"),
              .assign .localVar (varRef "slice") (.binary .div (.var "owe") (.var "price")) ])
          [])
        (.ok sliceFrame evmRead) :=
    ExecStmt.iteTrue hadjustCond hadjustBlock
  have hinnerBlock :
      ExecBlock (config v) oweFrame evmRead
        ([ .letDecl "_chost" (some uint256) (.storage chostRef) ] ++
          wrappingSubInto "remainingTab" (.var "tab") (.var "owe") ++
          [ .ite (.binary .lt (.var "remainingTab") (.var "_chost"))
            ([ .require (.binary .gt (.var "tab") (.var "_chost")) ] ++
              wrappingSubInto "oweAdjusted" (.var "tab") (.var "_chost") ++
              [ .assign .localVar (varRef "owe") (.var "oweAdjusted"),
                .assign .localVar (varRef "slice") (.binary .div (.var "owe") (.var "price")) ])
            [] ])
        (.ok sliceFrame evmRead) := by
    simpa [wrappingSubInto, sliceFrame] using
      (ExecBlock.consNormal hletChost
        (ExecBlock.consNormal hletRemaining
          (ExecBlock.consNormal hadjust ExecBlock.nil)))
  have hinner :
      ExecStmt (config v) oweFrame evmRead
        (.ite (.binary .and (.binary .lt (.var "owe") (.var "tab"))
            (.binary .lt (.var "slice") (.var "lot")))
          ([ .letDecl "_chost" (some uint256) (.storage chostRef) ] ++
            wrappingSubInto "remainingTab" (.var "tab") (.var "owe") ++
            [ .ite (.binary .lt (.var "remainingTab") (.var "_chost"))
              ([ .require (.binary .gt (.var "tab") (.var "_chost")) ] ++
                wrappingSubInto "oweAdjusted" (.var "tab") (.var "_chost") ++
                [ .assign .localVar (varRef "owe") (.var "oweAdjusted"),
                  .assign .localVar (varRef "slice")
                    (.binary .div (.var "owe") (.var "price")) ])
              [] ])
          [])
        (.ok sliceFrame evmRead) :=
    ExecStmt.iteTrue hinnerCond hinnerBlock
  have helse :
      ExecBlock (config v) oweFrame evmRead
        [ .ite (.binary .and (.binary .lt (.var "owe") (.var "tab"))
            (.binary .lt (.var "slice") (.var "lot")))
          ([ .letDecl "_chost" (some uint256) (.storage chostRef) ] ++
            wrappingSubInto "remainingTab" (.var "tab") (.var "owe") ++
            [ .ite (.binary .lt (.var "remainingTab") (.var "_chost"))
              ([ .require (.binary .gt (.var "tab") (.var "_chost")) ] ++
                wrappingSubInto "oweAdjusted" (.var "tab") (.var "_chost") ++
                [ .assign .localVar (varRef "owe") (.var "oweAdjusted"),
                  .assign .localVar (varRef "slice")
                    (.binary .div (.var "owe") (.var "price")) ])
              [] ])
          [] ]
        (.ok sliceFrame evmRead) :=
    ExecBlock.consNormal hinner ExecBlock.nil
  simpa [clipperTakeOweAdjustmentStmt, oweFrame, sliceFrame] using
    ExecStmt.iteFalse houter helse

end Benchmarks.Dss.Clipper
