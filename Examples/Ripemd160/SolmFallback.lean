import Examples.Ripemd160.SolmHash
import Examples.Ripemd160.Fallback
import Examples.Precompiles.Ripemd160.HashWideTrace

/-!
# RIPEMD-160 Solm fallback

Execution of the raw-calldata fallback and connection of its packed return to the mathematical
32-byte RIPEMD-160 output.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Ripemd160

abbrev uint96ABI : ABIType := .elem (.int (.uint ⟨96, by decide⟩))
abbrev bytes20ABI : ABIType := .elem (.bytes bytes20Width)

def fallbackValueGuard : Stmt :=
  .require (.binary .eq (.env .callvalue) (.intLit 0))

def fallbackSizeGuard : Stmt :=
  .require (.binary .le
    (.arrayLength .localVar { base := "data" })
    (.intLit maxFallbackCalldataSize))

def fallbackHashCall : Stmt := .internalCall "hash" [.var "data"] "digest"

def fallbackReturnExpr : Expr :=
  .abiEncodePacked [(uint96ABI, .intLit 0), (bytes20ABI, .var "digest")]

def fallbackReturnStmt : Stmt := .return [fallbackReturnExpr]

def fallbackBody : List Stmt :=
  [fallbackValueGuard, fallbackSizeGuard, fallbackHashCall, fallbackReturnStmt]

theorem fallbackTransition_body : fallbackTransition.body = fallbackBody := by
  rfl

def fallbackPackedOutput (h : RuntimeChain) : ByteArray :=
  ⟨(List.replicate 12 0 ++ (EVM.Word.toBytesBE (runtimeDigestPacked h)).drop 12).toArray⟩

theorem runtimeDigestPacked_eq_value {runtime : RuntimeChain} {model : Model.ChainState}
    (hrep : RuntimeChainRep runtime model) (hbound : Model.ChainBound model) :
    runtimeDigestPacked runtime = runtimeDigestValue runtime := by
  apply u256_inj
  rw [runtimeDigestPacked_toNat hrep hbound, runtimeDigestValue_toNat hrep hbound]

theorem fallbackPackedOutput_final (data : ByteArray) :
    let final := sourceChainRun data (Model.paddedLength data.size / 64) runtimeInitialChain
    fallbackPackedOutput final = Model.rawOutput data := by
  dsimp only
  let final := sourceChainRun data (Model.paddedLength data.size / 64) runtimeInitialChain
  change fallbackPackedOutput final = Model.rawOutput data
  have hrep : RuntimeChainRep final (Model.finalState data) := sourceChainRun_final_rep data
  have hbound : Model.ChainBound (Model.finalState data) := Model.chainBound_finalState data
  have hpv : runtimeDigestPacked final = runtimeDigestValue final :=
    runtimeDigestPacked_eq_value hrep hbound
  have hfull : (runtimeDigestValue final).toByteArray = Model.rawOutput data :=
    runtimeDigestValue_final data hrep
  rw [toByteArray_eq_toBytesBE] at hfull
  have hlist : EVM.Word.toBytesBE (runtimeDigestValue final) =
      (Model.rawOutput data).toList := by
    have htolist := congrArg ByteArray.toList hfull
    simpa [byteArray_toList_eq] using htolist
  have hrawTake : (Model.rawOutput data).toList.take 12 = List.replicate 12 0 := by
    rw [Model.rawOutput_eq]
    unfold Model.rawOutputOfChain
    rw [byteArray_toList_eq, ByteArray.data_append, Array.toList_append]
    simp
  have htake : (EVM.Word.toBytesBE (runtimeDigestValue final)).take 12 =
      List.replicate 12 0 := by
    rw [hlist, hrawTake]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp only [fallbackPackedOutput]
  rw [hpv]
  calc
    List.replicate 12 0 ++ (EVM.Word.toBytesBE (runtimeDigestValue final)).drop 12 =
        (EVM.Word.toBytesBE (runtimeDigestValue final)).take 12 ++
          (EVM.Word.toBytesBE (runtimeDigestValue final)).drop 12 := by rw [htake]
    _ = EVM.Word.toBytesBE (runtimeDigestValue final) := List.take_append_drop _ _
    _ = (Model.rawOutput data).toList := hlist
    _ = (Model.rawOutput data).data.toList := byteArray_toList_eq _

theorem evalFallbackSizeGuard_true (evm : EVM.State) (data : ByteArray)
    (hdata : (fallbackLocals evm.executionEnv).get? "data" = some (.bytes data))
    (hsmall : data.size ≤ maxFallbackCalldataSize) :
    evalExpr? config { contract := contract, locals := fallbackLocals evm.executionEnv } evm
      (.binary .le
        (.arrayLength .localVar { base := "data" })
        (.intLit maxFallbackCalldataSize)) = .ok (.bool true) := by
  simp only [evalExpr?, hdata, readLocalPath?, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hi : Int.ofNat data.size ≤ Int.ofNat maxFallbackCalldataSize :=
    Int.ofNat_le.mpr hsmall
  change EvalResult.ok (Value.bool
      (decide (Int.ofNat data.size ≤ Int.ofNat maxFallbackCalldataSize))) =
    EvalResult.ok (Value.bool true)
  rw [decide_eq_true hi]

theorem word_toBytesBE_length (w : UInt256) : (EVM.Word.toBytesBE w).length = 32 := by
  rw [word_toBytesBE_reverse, List.length_reverse]
  unfold EVM.Word.toBytesLE
  have hb := Ethereum.toBytes'_le (k := 32) w.val.isLt
  simp
  omega

theorem encodePacked_uint96_zero :
    encodePackedValue? uint96ABI (.int 0) = some (List.replicate 12 0) := by
  native_decide

theorem encodePacked_digestBytes20 (h : RuntimeChain) :
    encodePackedValue? bytes20ABI (digestBytes20 h) =
      some ((EVM.Word.toBytesBE (runtimeDigestPacked h)).drop 12) := by
  simp only [bytes20ABI, digestBytes20, encodePackedValue?, fixedBytesSize]
  rw [if_pos (by
    constructor
    · trivial
    · rw [List.length_drop, word_toBytesBE_length])]

theorem evalFallbackReturnExpr {L : Store} (evm : EVM.State) (h : RuntimeChain)
    (hdigest : L.get? "digest" = some (digestBytes20 h)) :
    evalExpr? config { contract := contract, locals := L } evm fallbackReturnExpr =
      .ok (.bytes (fallbackPackedOutput h)) := by
  simp only [fallbackReturnExpr, evalExpr?, evalPackedArgs?, EvalResult.bind, bind, pure,
    encodePacked_uint96_zero, EvalResult.ofOption, hdigest, encodePacked_digestBytes20]
  simp only [List.append_nil, fallbackPackedOutput]

theorem hashCall {L : Store} (evm : EVM.State) (data : ByteArray)
    (hsmall : data.size ≤ maxFallbackCalldataSize)
    (hdata : L.get? "data" = some (.bytes data)) :
    let final := sourceChainRun data (Model.paddedLength data.size / 64) runtimeInitialChain
    ExecStmt config { contract := contract, locals := L } evm fallbackHashCall
      (.ok { contract := contract, locals := L.insert "digest" (digestBytes20 final) } evm) := by
  dsimp only
  let final := sourceChainRun data (Model.paddedLength data.size / 64) runtimeInitialChain
  have hargs : evalExprs? config { contract := contract, locals := L } evm [.var "data"] =
      .ok [.bytes data] := by
    simp only [evalExprs?, evalExpr?, EvalResult.ofOption, hdata, EvalResult.bind, bind, pure]
  have hlookup : lookupCallable? contract "hash" = some hashFunction.toCallable := by
    rfl
  have hbind := hashFunction_bindParams data
  obtain ⟨L', hbody⟩ := hashFunctionBodyReturns evm data hsmall
  have hcall := internalCallFunctionReturn
    (cfg := config) (caller := { contract := contract, locals := L })
    (evm := evm) (calleeEvm := evm) (name := "hash") (retVar := "digest")
    (args := [.var "data"]) (argVals := [.bytes data]) (callee := hashFunction)
    (locals := hashLocals data) (calleeSolm := { contract := contract, locals := L' })
    (value := some [digestBytes20 final]) hargs hlookup hbind hbody
  simpa only [fallbackHashCall, resumeAfterInternalCall, collapseReturns] using hcall

theorem fallbackBodyReturns (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsmall : evm.executionEnv.calldata.size ≤ maxFallbackCalldataSize) :
    let data := evm.executionEnv.calldata
    let final := sourceChainRun data (Model.paddedLength data.size / 64) runtimeInitialChain
    ExecTransitionBody config contract evm (fallbackLocals evm.executionEnv)
      fallbackTransition.body
      (.returned { contract := contract, locals :=
          (fallbackLocals evm.executionEnv).insert "digest" (digestBytes20 final) }
        evm (some [.bytes (Model.rawOutput data)])) := by
  dsimp only
  let data := evm.executionEnv.calldata
  let final := sourceChainRun data (Model.paddedLength data.size / 64) runtimeInitialChain
  let L := fallbackLocals evm.executionEnv
  let L' := L.insert "digest" (digestBytes20 final)
  have hdata : L.get? "data" = some (.bytes data) := by
    simp [L, data, fallbackLocals]
  have e0 : ExecStmt config { contract := contract, locals := L } evm fallbackValueGuard
      (.ok { contract := contract, locals := L } evm) := by
    exact ExecStmt.requireTrue (by
      simpa only [fallbackValueGuard] using
        (evalCallvalueEq_true (cfg := config)
          (solm := { contract := contract, locals := L }) hwv))
  have e1 : ExecStmt config { contract := contract, locals := L } evm fallbackSizeGuard
      (.ok { contract := contract, locals := L } evm) := by
    exact ExecStmt.requireTrue (by
      simpa only [fallbackSizeGuard] using evalFallbackSizeGuard_true evm data (by
        simpa only [L] using hdata) (by simpa only [data] using hsmall))
  have e2 : ExecStmt config { contract := contract, locals := L } evm fallbackHashCall
      (.ok { contract := contract, locals := L' } evm) := by
    simpa only [L', final] using hashCall evm data (by simpa only [data] using hsmall) hdata
  have hdigest : L'.get? "digest" = some (digestBytes20 final) := by
    simp [L']
  have hreturnEval : evalExpr? config { contract := contract, locals := L' } evm
      fallbackReturnExpr = .ok (.bytes (Model.rawOutput data)) := by
    rw [← fallbackPackedOutput_final data]
    exact evalFallbackReturnExpr evm final hdigest
  have e3 : ExecStmt config { contract := contract, locals := L' } evm fallbackReturnStmt
      (.returned { contract := contract, locals := L' } evm
        (some [.bytes (Model.rawOutput data)])) := by
    apply ExecStmt.return
    simp only [fallbackReturnStmt, evalExprs?, hreturnEval, EvalResult.bind, bind, pure]
  apply ExecFuncBody.execBlockRet
  rw [fallbackTransition_body]
  exact ExecBlock.consNormal e0 <| ExecBlock.consNormal e1 <|
    ExecBlock.consNormal e2 <| ExecBlock.consReturn e3

/-- Fixed-input equivalence for the successful zero-value, allocator-safe fallback branch. -/
theorem fallbackSuccess {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = ripemd160RuntimeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrun := ripemd160X_success
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) hcode hwv hsize hsmall
  have hequiv :
      runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀
        (Sat256.ofUInt256 g).toUInt256 A I :=
    hrun.reEquivElim hcode fun g' A' hxi => by
      let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let final := sourceChainRun I.calldata
        (Model.paddedLength I.calldata.size / 64) runtimeInitialChain
      let resultLocals := (fallbackLocals I).insert "digest" (digestBytes20 final)
      have hbody : ExecTransitionBody config contract evmSolm (fallbackLocals I)
          fallbackTransition.body
          (.returned { contract := contract, locals := resultLocals } evmSolm
            (some [.bytes (Model.rawOutput I.calldata)])) := by
        simpa only [evmSolm, final, resultLocals, initState] using
          fallbackBodyReturns evmSolm
            (by simpa [evmSolm, initState] using hwv)
            (by simpa [evmSolm, initState] using hsmall)
      have hsolm : solmExec config contract cA gh bl σ_solm σ₀
          (Sat256.ofUInt256 g).toUInt256 A I
          (.returned { contract := contract, locals := resultLocals } evmSolm
            (some [.bytes (Model.rawOutput I.calldata)])) .rawBytes := by
        exact solmExec.fallback
          (selectorDispatch_none I.calldata)
          (receiveDispatch_none I.calldata)
          rfl
          (fallback_callargs I.calldata)
          fallback_returnConvention
          (by simp [evmSolm, initState])
          hbody
      refine runtimeEquivalenceFor.execution hxi hsolm ?_
      exact execResultsEquiv.success rfl rfl
        (by simp [evmSolm, initState])
        (by simpa [evmSolm, initState] using hAccounts)
        (.rawBytes rfl)
  simpa using hequiv

end Ripemd160
