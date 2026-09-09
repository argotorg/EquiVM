import Benchmarks.Dss.Cure.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Cure

/-! ## `tCount()` -/

def tCountWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  cureSlotWord ⟨2⟩ σ I

theorem cureDispatchTCount {I : ExecutionEnv}
    (hsel : selIs I (cureSelBytes 15)) :
    dispatchMsg contract I.calldata = some tCountTransition := by
  have hcd : I.calldata.extract 0 4 = cureSelBytes 15 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some tCountTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, cureSelBytes,
    cureAmtSelectorBytes, cureCageSelectorBytes, cureDenySelectorBytes,
    cureDropSelectorBytes, cureFileSelectorBytes, cureLCountSelectorBytes,
    cureLiftSelectorBytes, cureListSelectorBytes, cureLiveSelectorBytes,
    cureLoadSelectorBytes, cureLoadedSelectorBytes, curePosSelectorBytes,
    cureRelySelectorBytes, cureSaySelectorBytes, cureSrcsSelectorBytes,
    cureTCountSelectorBytes]
  decide +native

theorem cureDecode_tCount {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (tCountTransition.params.map Param.name)
      (transitionSignature tCountTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem cureTCountBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = cureBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (cureSelBytes 15))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (cureSelBytes 15) rfl hsel
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ tCountTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (tCountWord σ_solm I).toNat))])) := by
    apply nonpayableReturnExprBodyReturns
    · simp only [initState]
      exact hwv
    · simp [evalExpr?, tCountWord, cureSlotWord, initState, config, contract,
        srcsRef, storageDecls, storageLayout, solidityStorageLayout, storageLayoutRaw,
        readStorageArrayLength?, resolveStorageRef?, storageTypeAt?, evalStorageRef, evalStorageRefSteps,
        wordLoc, EvalResult.ofOption, EvalResult.bind, pure, bind]
      change
        (match storageLocLoad
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (wordLoc ⟨2⟩) with
        | Value.int n => EvalResult.ok (Value.int n)
        | _ => EvalResult.error EvalError.storageError) =
          EvalResult.ok (Value.int ↑(cureSlotWord ⟨2⟩ σ_solm I).toNat)
      rw [cureStorageLocLoad_uint256]
      simp [cureSlotWord, solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage]
  have hreach := cureReachTCountBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hentry : solcGetterEntryWf cureBytecode ⟨578⟩ ⟨343⟩ ⟨2333⟩ := by
    unfold solcGetterEntryWf
    repeat' first | apply And.intro | decide +native
  have hgetter : solcWordSlotGetterSwapJumpWf cureBytecode ⟨2333⟩ ⟨2⟩ := by
    unfold solcWordSlotGetterSwapJumpWf
    repeat' first | apply And.intro | decide +native
  have hretmem : solcReturnWordFromMemWf cureBytecode ⟨343⟩ := by
    unfold solcReturnWordFromMemWf
    repeat' first | apply And.intro | decide +native
  obtain ⟨_, _, hroutine⟩ := RD.solcGetterThunk hreach hentry (by jump_dest)
  obtain ⟨_, _, hretPc⟩ := RD.solcWordSlotGetterSwapJump
    (slot := ⟨2⟩) (R := [cureSelWord I]) hroutine hgetter (by jump_dest)
    (by simp)
  have hret :
      RDret cureBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray (tCountWord σ_evm I)) := by
    have hret' := RD.solcReturnWordFromMem
      (pc := ⟨343⟩) (val := tCountWord σ_evm I) (ret := cureSelWord I) (R := [])
      (memout := solcReturnMem (tCountWord σ_evm I))
      (by simpa [tCountWord, cureSlotWord] using hretPc)
      hretmem
      solcFreePtrMem_mload64
      (by rfl)
      (solcReturnMem_mload64 (tCountWord σ_evm I))
      (solcReturnMem_read128 (tCountWord σ_evm I))
      (by simp)
    simpa using hret'
  have hword : tCountWord σ_evm I = tCountWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
  have hval :
      some [Value.int (Int.ofNat (tCountWord σ_solm I).toNat)] =
        some [Value.int (Int.ofNat (tCountWord σ_evm I).toNat)] := by
    rw [hword]
  have henc :
      returnEquiv (UInt256.toByteArray (tCountWord σ_evm I))
        (some [(.int (Int.ofNat (tCountWord σ_evm I).toNat))])
        tCountTransition.returnType := by
    rw [show tCountTransition.returnType = [uint256] by rfl]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (tCountWord σ_evm I))
  exact hret.reEquivExecutionTransport hcode (cureDispatchTCount hsel)
    (cureDecode_tCount hsz) hbody hval hAccounts henc

end Benchmarks.Dss.Cure
