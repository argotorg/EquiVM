import Examples.StringStore.Clear

/-!
# StringStore — `dropLast()` empty-history branch

This module discharges the `dropLast()` case where the history array is empty.  The non-empty case
still contains the dynamic string read/pop/return path and remains as the exposed branch hypothesis.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace StringStore

theorem stringStoreDispatch_dropLast {cd : ByteArray}
    (hsel : ((⟨#[0x4e, 0x30, 0x50, 0x6f]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg stringStoreContract cd = some dropLastTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x4e, 0x30, 0x50, 0x6f]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [setTransition, appendToHistoryTransition, replaceFromHistoryTransition])
    (post := [clearCurrentTransition, clearAllTransition, storeRawTransition, currentLengthGetter,
      historyLengthGetter, rawLengthGetter]) rfl ?_
    (by rw [selectorOf, dropLastSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · rw [selectorOf, setSelectorBytes, hcd]; decide
  · rw [selectorOf, appendToHistorySelectorBytes, hcd]; decide
  · rw [selectorOf, replaceFromHistorySelectorBytes, hcd]; decide

theorem stringStoreReachDropLast {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stringStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x4e, 0x30, 0x50, 0x6f]⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨208⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  have hmatches := stringStoreLowMatches 1 (by omega) hsz hsel
  exact stringStoreReachLowBody 1 (by omega) ⟨208⟩ hcode hwv hsz hsize
    (stringStorePivotTaken 1 (by omega) hsz hsel)
    hmatches.1 hmatches.2 (by jump_dest) (by decide)

theorem dropLastBodyRevertsEmptyHistory {evm : EVM.State}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩) :
    ExecTransitionBody stringStoreConfig stringStoreContract evm ∅ dropLastTransition.body
      .reverted := by
  have hresolve : resolveStorageRef? stringStoreConfig
      { contract := stringStoreContract, locals := ∅ } evm historyRef =
        .ok ({ base := "history", steps := [] }, .dynamicArray .string) := by
    simp [resolveStorageRef?, evalStorageRef, evalStorageRefSteps, historyRef,
      storageTypeAt?, stringStoreContract, storageDecls, stringSt, EvalResult.ofOption,
      EvalResult.bind, pure, bind]
  have hlen :
      storageLocLoad evm (uint256Loc ⟨1⟩) = .int 0 :=
    storageLocLoad_uint256_zero hload
  have hlengthEval :
      evalExpr? stringStoreConfig { contract := stringStoreContract, locals := ∅ } evm
        (.arrayLength .storage historyRef) = .ok (.int 0) := by
    simp only [evalExpr?, hresolve, readStorageArrayLength?, EvalResult.bind, bind]
    simp [stringStoreConfig_storage_history_length, hlen, pure]
  have hgtEval :
      evalExpr? stringStoreConfig
        { contract := stringStoreContract, locals := (∅ : Store).insert "length" (.int 0) } evm
        (.binary .gt (.var "length") (.intLit 0)) = .ok (.bool false) := by
    simp [evalExpr?, evalBinaryOp?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  exact ExecFuncBody.execBlockRevert <|
    ((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep hlengthEval).requireRevert
      hgtEval

theorem stringStoreX_dropLastEmptyHistory {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨208⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hhistory : historyLengthWord σ I = ⟨0⟩) :
    RDrev stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd208⟩ := hreach
  have rd725 := evm_run rd208 with [
    jumpdest, push2 ⟨216⟩, push2 ⟨725⟩, jump (by jump_dest)]
  have rd732pre := evm_run rd725 with [
    jumpdest, push1 ⟨96⟩, push0, push1 ⟨1⟩, dup1]
  obtain ⟨_, _, rd733₀⟩ := rd732pre.sload (by native_decide) (by evm_ov)
  have hhistoryLoad :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) = ⟨0⟩ := by
    simpa [historyLengthWord] using hhistory
  obtain ⟨_, _, rd733⟩ :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨733⟩
        [⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨96⟩, ⟨216⟩, stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    have hpc :
        (⟨725⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ :
          UInt256) = ⟨733⟩ := by
      native_decide
    exact ⟨_, _, by simpa [initState, hhistoryLoad, hpc] using rd733₀⟩
  have rd744 := evm_run rd733 with [
    swap1, pop, swap1, pop, push0, dup2, gt, push2 ⟨747⟩, jumpiNT (by decide)]
  exact rd744.revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

theorem stringStoreDropLastEmptyHistoryRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x4e, 0x30, 0x50, 0x6f]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hhistory : historyLengthWord σ_evm I = ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0x4e, 0x30, 0x50, 0x6f]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := dropLastSelector_size hsel
  have hd := stringStoreDispatch_dropLast (cd := I.calldata) hsel'
  have hdec := stringStoreDecode_dropLast (I := I) hsz
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
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
  have hbody :
      ExecTransitionBody stringStoreConfig stringStoreContract evmSolm0 ∅ dropLastTransition.body
        .reverted :=
    dropLastBodyRevertsEmptyHistory (evm := evmSolm0)
      (by simp [evmSolm0, initState]; exact hwv) hhistorySolm
  have hreach := stringStoreReachDropLast (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv (dropLastSelector_size hsel) hsize hsel
  have hrev := stringStoreX_dropLastEmptyHistory
    (g := Sat256.ofUInt256 g) hreach hhistory
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

axiom stringStoreDropLastNonzeroHistoryRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x4e, 0x30, 0x50, 0x6f]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hhistory : historyLengthWord σ_evm I ≠ ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I

theorem stringStoreDropLastRuntime_of_nonzeroHistory
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x4e, 0x30, 0x50, 0x6f]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hhistory : historyLengthWord σ_evm I = ⟨0⟩
  · exact stringStoreDropLastEmptyHistoryRuntime
      hcode hsize hperm hwv hsel hAccounts hhistory
  · exact stringStoreDropLastNonzeroHistoryRuntime
      hcode hsize hperm hwv hsel hAccounts hhistory

end StringStore
