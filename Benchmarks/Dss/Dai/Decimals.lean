import Benchmarks.Dss.Dai.Dispatch
import Benchmarks.Dss.Dai.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Dai

/-! ## ABI decode and source-level body for `decimals()` -/

abbrev decimalsStore : Store :=
  ∅

abbrev decimalsWord : UInt256 :=
  ⟨18⟩

theorem daiDecode_decimals_ok {I : ExecutionEnv} (hsz4 : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (decimalsTransition.params.map Param.name)
      (transitionSignature decimalsTransition).paramTypes I.calldata =
        some decimalsStore := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata =
    some (∅ : Store)
  exact decodeCalldataWithMode_empty_ok hsz4

/-- The Solm `decimals()` body returns the constant `18`. -/
theorem daiDecimalsBodyReturns (evm : EVM.State)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm decimalsStore decimalsTransition.body
      (.returned { contract := contract, locals := decimalsStore } evm
        (some [(.int (Int.ofNat decimalsWord.toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      change evalExpr? config { contract := contract, locals := decimalsStore } evm
        (.intLit 18) = EvalResult.ok (.int 18)
      simp [evalExpr?, pure])

/-! ## EVM trace -/

theorem daiX_decimals_ok {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD daiBytecode I g
      (initState σ σ₀ g A I) ⟨604⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDret daiBytecode g (initState σ σ₀ g A I) σ
      (UInt256.toByteArray decimalsWord) := by
  have hmask : UInt256.land (⟨18⟩ : UInt256) ⟨255⟩ = decimalsWord := by
    native_decide
  simpa [decimalsWord, hmask] using
    RD.daiUint8ConstGetterExternal
      (entry := ⟨604⟩) (returnPc := ⟨612⟩) (routine := ⟨2000⟩)
      (val := (⟨18⟩ : UInt256)) (width := 1) (op := .PUSH1)
      hreach
      dai_getter_entry_wf
      dai_const_getter_wf
      (by jump_dest)
      (by jump_dest)
      dai_return_uint8_from_mem_wf

theorem daiDecimalsBodyCoreOk
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = daiBytecode) (_hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some decimalsTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (decimalsTransition.params.map Param.name)
        (transitionSignature decimalsTransition).paramTypes I.calldata =
          some decimalsStore)
    (hreach : ∃ k C, RD daiBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨604⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        decimalsStore
        decimalsTransition.body
        (.returned { contract := contract, locals := decimalsStore }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat decimalsWord.toNat))])) := by
    exact daiDecimalsBodyReturns
      (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (by simp only [initState]; exact hwv)
  exact (daiX_decimals_ok (g := Sat256.ofUInt256 g) hreach)
    |>.reEquivExecution hcode hdispatch hdecode hbody
      (returnEquiv_of_encode
        (by
          simpa [uint8, decimalsWord] using
            uint8ReturnEncoding decimalsWord (by native_decide)))

/-- `decimals()` body refines its Solm transition. -/
theorem daiDecimalsBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (daiSelBytes 4)) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (daiSelBytes 4) (by native_decide) hsel
  have hdispatch : dispatchMsg contract I.calldata = some decimalsTransition :=
    daiDispatchDecimals hsel
  have hreach := daiReachDecimalsBody
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  exact daiDecimalsBodyCoreOk hcode hsize hwv hdispatch
    (daiDecode_decimals_ok hsz4) hreach

end Benchmarks.Dss.Dai
