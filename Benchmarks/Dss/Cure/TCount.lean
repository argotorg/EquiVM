import Benchmarks.Dss.Cure.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Cure

/-! ## `tCount()` -/

def tCountWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWordAt ⟨2⟩ σ I

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
  native_decide

theorem cureDecode_tCount {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (tCountTransition.params.map Param.name)
      (transitionSignature tCountTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem cureTCountBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = cureBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (cureSelBytes 15)) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (cureSelBytes 15) rfl hsel
  have hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ tCountTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (tCountWord σ I).toNat))])) := by
    apply nonpayableReturnExprBodyReturns
    · simp only [initState]
      exact hwv
    · simp [evalExpr?, tCountWord, solcSlotWordAt, initState, config, contract,
        srcsRef, storageDecls, storageLayout, solidityStorageLayout, storageLayoutRaw,
        readStorageArrayLength?, resolveStorageRef?, storageTypeAt?, evalStorageRef, evalStorageRefSteps,
        wordLoc, EvalResult.ofOption, EvalResult.bind, pure, bind]
      change
        (match storageLocLoad
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) (wordLoc ⟨2⟩) with
        | Value.int n => EvalResult.ok (Value.int n)
        | _ => EvalResult.error EvalError.storageError) =
          EvalResult.ok (Value.int ↑(solcSlotWordAt ⟨2⟩ σ I).toNat)
      erw [storageLocLoad_uint256]
      simp [solcSlotWordAt, solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage]
  have hreach := cureReachTCountBody (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hentry : solcGetterEntryWf cureBytecode ⟨578⟩ ⟨343⟩ ⟨2333⟩ := by
    unfold solcGetterEntryWf
    repeat' first | apply And.intro | native_decide
  have hgetter : solcWordSlotGetterSwapJumpWf cureBytecode ⟨2333⟩ ⟨2⟩ := by
    unfold solcWordSlotGetterSwapJumpWf
    repeat' first | apply And.intro | native_decide
  have hretmem : solcReturnWordFromMemWf cureBytecode ⟨343⟩ := by
    unfold solcReturnWordFromMemWf
    repeat' first | apply And.intro | native_decide
  obtain ⟨_, _, hroutine⟩ := RD.solcGetterThunk hreach hentry (by jump_dest)
  obtain ⟨_, _, hretPc⟩ := RD.solcWordSlotGetterSwapJump
    (slot := ⟨2⟩) (R := [cureSelWord I]) hroutine hgetter (by jump_dest)
    (by simp)
  have hret :
      RDret cureBytecode (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ
        (UInt256.toByteArray (tCountWord σ I)) := by
    have hret' := RD.solcReturnWordFromMem
      (pc := ⟨343⟩) (val := tCountWord σ I) (ret := cureSelWord I) (R := [])
      (memout := solcReturnMem (tCountWord σ I))
      (by simpa [tCountWord, solcSlotWordAt] using hretPc)
      hretmem
      solcFreePtrMem_mload64
      (by rfl)
      (solcReturnMem_mload64 (tCountWord σ I))
      (solcReturnMem_read128 (tCountWord σ I))
      (by simp)
    simpa using hret'
  have henc :
      returnEquiv (UInt256.toByteArray (tCountWord σ I))
        (some [(.int (Int.ofNat (tCountWord σ I).toNat))])
        tCountTransition.returnType := by
    rw [show tCountTransition.returnType = [uint256] by rfl]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (tCountWord σ I))
  exact hret.reEquivExecutionGen hcode (cureDispatchTCount hsel)
    (cureDecode_tCount hsz) hbody rfl henc

end Benchmarks.Dss.Cure
