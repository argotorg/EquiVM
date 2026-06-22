import Examples.CtorTruth.Bytecode
import Examples.Truth.Correct
import Reasoning.Memory
import Reasoning.Solc
import Reasoning.Theory
import Reasoning.Dispatch
import Reasoning.SolmBody
import Reasoning.Reach

/-!
# CtorTruth — whole-contract equivalence smoke test

The runtime proof reuses the existing `Truth` symbolic trace because the deployed runtime bytecode is
the same metadata-free code.  The constructor proof exercises the new constructor-equivalence API and
the Solidity `selfDeployment` hook; the initcode proof is a direct `CODECOPY`/`RETURN` trace for the
empty payable constructor.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 10000

theorem ctorTruthRuntime_eq_truthBytecode :
    ctorTruthRuntimeBytecode = truthBytecode := rfl

/-! ## Runtime side -/

/-- Single-selector dispatch bundle for the `truth()` selector. -/
theorem ctorTruthDispatch :
    SingleSelectorDispatch CtorTruth.contract CtorTruth.truthTransition ⟨#[0x9e, 0x9f, 0x51, 0xd2]⟩ :=
  singleSelectorDispatch rfl ctorTruthSelectorBytes rfl

/-- `CtorTruth` has exactly one transition, so any successful dispatch yields it. -/
theorem ctorTruthDispatch_unique {cd : ByteArray} {t : TransitionDecl}
    (h : dispatchMsg CtorTruth.contract cd = some t) : t = CtorTruth.truthTransition :=
  dispatch_unique rfl h


/-- With zero call value, the Solm body returns `true`. -/
theorem ctorTruthBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody ctorTruthConfig CtorTruth.contract evm locals
      CtorTruth.truthTransition.body
      (.returned { contract := CtorTruth.contract, locals := locals } evm (some (.bool true))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by simp only [evalExpr?]; rfl)

theorem ctorTruthReturnEncoding :
    encodeReturnValue? (.elem .bool) (.bool true) = some (UInt256.toByteArray ⟨1⟩) :=
  boolTrueReturnEncoding

/-- The EVM selector test agrees with the dispatcher comparison. -/
theorem ctorTruthEvmSelector {cd : ByteArray} (hsz : 4 ≤ cd.size) :
    UInt256.eq ⟨2661241298⟩
        (UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩)
      = if ((⟨#[0x9e, 0x9f, 0x51, 0xd2]⟩ : ByteArray) == cd.extract 0 4) then ⟨1⟩ else ⟨0⟩ :=
  truthEvmSelector hsz

/-- Decoding `truth()`'s empty argument list succeeds with the empty store. -/
theorem ctorTruthDecode_empty {I : Ethereum.ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (CtorTruth.truthTransition.params.map Param.name)
      (transitionSignature CtorTruth.truthTransition).paramTypes I.calldata = some ∅ := by
  simpa [CtorTruth.truthTransition] using truthDecode_empty (I := I) hsz

theorem ctorTruthReEquiv_callvalueZero
    {cA gh bl σ_evm σ₀_evm σ_solm σ₀_solm A I} {g : Sat256}
    (hcode : I.code = ctorTruthRuntimeBytecode) (hsize : I.calldata.size < Ethereum.UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor ctorTruthConfig CtorTruth.contract cA gh bl
      σ_evm σ₀_evm σ_solm σ₀_solm g.toUInt256 A I := by
  have hcode' : I.code = truthBytecode := by
    rw [← ctorTruthRuntime_eq_truthBytecode]
    exact hcode
  by_cases hsz : I.calldata.size < 4
  · exact (truthX_cvz_short hcode' hwv hsz).reEquivNoDispatch hcode'
      (ctorTruthDispatch.none_short hsz)
  · rw [not_lt] at hsz
    by_cases hmatch : ((⟨#[0x9e, 0x9f, 0x51, 0xd2]⟩ : ByteArray) == I.calldata.extract 0 4) = true
    · have hd : dispatchMsg CtorTruth.contract I.calldata = some CtorTruth.truthTransition := by
        rw [ctorTruthDispatch.eq, if_pos hmatch]
      exact (truthX_cvz_success hcode' hwv hsz hsize hmatch).reEquivExecution hcode' hd
        (ctorTruthDecode_empty hsz)
        (ctorTruthBodyReturns (initState cA gh bl σ_solm σ₀_solm g A I) ∅
          (by simp only [initState]; exact hwv))
        hAccounts
        (returnEquiv_of_encode ctorTruthReturnEncoding)
    · rw [Bool.not_eq_true] at hmatch
      exact (truthX_cvz_revertB hcode' hwv hsz hsize hmatch).reEquivNoDispatch hcode'
        (ctorTruthDispatch.none_nomatch hmatch)

/-- Runtime bytecode refines the Solm runtime specification. -/
theorem ctorTruthRuntimeCorrect :
    runtimeEquivalence!?! ctorTruthConfig ctorTruthRuntimeBytecode CtorTruth.contract := by
  refine ⟨fun cA gh bl σ_evm σ₀_evm σ_solm σ₀_solm g A I hcode hsize _hperm hσ _hσ₀ => ?_⟩
  by_cases hwv : I.weiValue = ⟨0⟩
  · exact ctorTruthReEquiv_callvalueZero (g := Sat256.ofUInt256 g) hcode hsize hwv hσ
  · have hcode' : I.code = truthBytecode := by
      rw [← ctorTruthRuntime_eq_truthBytecode]
      exact hcode
    exact (truthX_callvalue_ne (g := Sat256.ofUInt256 g) hcode' hwv).reEquivNonPayable hcode' rfl
      fun _ca => bodyReverts_nonPayable (by simp only [initState]; exact hwv)

/-! ## Constructor side -/

noncomputable def ctorTruthInitReturnMem : ByteArray :=
  ctorTruthRuntimeBytecode.write 0 solcFreePtrMem 0 123

theorem ctorTruthRuntime_size : ctorTruthRuntimeBytecode.size = 123 := by
  native_decide

theorem ctorTruthRuntime_extract_all :
    ctorTruthRuntimeBytecode.extract 0 123 = ctorTruthRuntimeBytecode := by
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by native_decide)

theorem ctorTruthInitcode_runtime_window :
    ctorTruthInitcode.extract 15 (15 + 123) = ctorTruthRuntimeBytecode := by
  native_decide

theorem ctorTruthInitcode_codecopy_mem :
    ctorTruthInitcode.write 15 solcFreePtrMem 0 123 = ctorTruthInitReturnMem := by
  unfold ctorTruthInitReturnMem
  apply ByteArray.ext
  rw [write0_data_from ctorTruthInitcode solcFreePtrMem 15 123 (by decide) (by native_decide)]
  rw [write0_data ctorTruthRuntimeBytecode solcFreePtrMem 123 (by decide)
    (by rw [ctorTruthRuntime_size])]
  have hwindow :
      ctorTruthInitcode.data.extract 15 (15 + 123)
        = ctorTruthRuntimeBytecode.data.extract 0 123 := by
    have h1 := congrArg ByteArray.data ctorTruthInitcode_runtime_window
    have h2 := congrArg ByteArray.data ctorTruthRuntime_extract_all
    simpa [ByteArray.data_extract] using h1.trans h2.symm
  rw [hwindow]

theorem ctorTruthFinal_read :
    ctorTruthInitReturnMem.readWithPadding 0 123 = ctorTruthRuntimeBytecode := by
  unfold ctorTruthInitReturnMem
  rw [write0_read_back_gen ctorTruthRuntimeBytecode solcFreePtrMem 123
    (by decide) (by rw [ctorTruthRuntime_size]) (by decide)]
  exact ctorTruthRuntime_extract_all

/-- Solidity deployment accepts only an argument list of the constructor parameter length. -/
theorem ctorTruthDeployment_args_length {args : List Value} {deployedInitcode : ByteArray} :
    ctorTruthConfig.selfDeployment ctorTruthInitcode args = some deployedInitcode →
    args.length = CtorTruth.contract.ctor.params.length := by
  intro h
  cases args with
  | nil => rfl
  | cons arg rest =>
      simp [ctorTruthConfig, genSolidityConstructorDeployment, CtorTruth.contract, CtorTruth.ctor,
        encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?] at h

theorem ctorTruthDeployment_eq_initcode {args : List Value} {deployedInitcode : ByteArray} :
    ctorTruthConfig.selfDeployment ctorTruthInitcode args = some deployedInitcode →
    deployedInitcode = ctorTruthInitcode := by
  intro h
  cases args with
  | nil =>
      simp [ctorTruthConfig, genSolidityConstructorDeployment, CtorTruth.contract, CtorTruth.ctor,
        encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, ByteArray.append_empty] at h
      exact h.symm
  | cons arg rest =>
      simp [ctorTruthConfig, genSolidityConstructorDeployment, CtorTruth.contract, CtorTruth.ctor,
        encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?] at h

set_option maxHeartbeats 400000 in
theorem ctorTruthInitcodeRun {createdAccounts genesisBlockHeader blocks σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ctorTruthInitcode) :
    RDret ctorTruthInitcode g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) (createdAccounts, σ)
      ctorTruthRuntimeBytecode := by
  set s0 := initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I with hs0
  have rd0 :
      RD ctorTruthInitcode I g s0 ⟨0⟩ [] ByteArray.empty (UInt256.ofNat 0) ByteArray.empty
        (createdAccounts, σ) 0 0 := by
    rw [hs0]; exact RD.initState hcode
  exact evm_run rd0 with [
    raw push1 ⟨128⟩ ctorTruthDecode0 (by evm_ov),
    raw push1 ⟨64⟩ ctorTruthDecode2 (by evm_ov),
    raw mstore 9 solcFreePtrMem (UInt256.ofNat 3) ctorTruthDecode4
      mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨123⟩ ctorTruthDecode5 (by evm_ov),
    raw dup1 ctorTruthDecode7 (by evm_ov),
    raw push1 ⟨15⟩ ctorTruthDecode8 (by evm_ov),
    raw push0 ctorTruthDecode10 (by evm_ov),
    raw codecopy 3 ctorTruthInitReturnMem (UInt256.ofNat 4) ctorTruthDecode11
      mem_cost
      ctorTruthInitcode_codecopy_mem
      (by decide) (by evm_ov),
    raw push0 ctorTruthDecode12 (by evm_ov),
    raw ret 0 ctorTruthRuntimeBytecode ctorTruthDecode13
      mem_cost
      ctorTruthFinal_read
      (by evm_ov)]

theorem ctorTruthInitcodeXiResult
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ : Ethereum.AccountMap)
    (σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (args : List Value)
    (deployedInitcode : ByteArray) :
    ctorTruthConfig.selfDeployment ctorTruthInitcode args = some deployedInitcode →
    I.code = deployedInitcode →
    I.calldata = .empty →
    I.perm = true →
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .error .OutOfGass
      ∨ ∃ (g' : UInt256) (A' : Substate),
          Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I
            = .ok (.success (createdAccounts, σ, g', A') ctorTruthRuntimeBytecode) := by
  intro hdeploy hcode _hcalldata _hperm
  have hdeployed := ctorTruthDeployment_eq_initcode hdeploy
  rw [hdeployed] at hcode
  rcases (ctorTruthInitcodeRun (createdAccounts := createdAccounts)
      (genesisBlockHeader := genesisBlockHeader) (blocks := blocks) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode).xiResult hcode with
    hoog | ⟨g', A', hsuccess⟩
  · left
    simpa using hoog
  · right
    exact ⟨g', A', hsuccess⟩

theorem ctorTruthCtorBodyReturns
    (evm : EVM.State) (locals : Store) :
    ExecTransitionBody ctorTruthConfig CtorTruth.contract evm locals CtorTruth.contract.ctor.body
      (.returned { contract := CtorTruth.contract, locals := locals } evm none) := by
  exact ExecFuncBody.execBlockOK ExecBlock.nil

theorem ctorTruthSolmCtorExec
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ : Ethereum.AccountMap}
    {σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {args : List Value}
    {deployedInitcode : ByteArray}
    (hdeploy : ctorTruthConfig.selfDeployment ctorTruthInitcode args = some deployedInitcode) :
    solmCtorExec ctorTruthConfig CtorTruth.contract args createdAccounts genesisBlockHeader blocks
      σ σ₀ g A I
      (.returned
        { contract := CtorTruth.contract
          locals := Std.HashMap.ofList (List.zip (CtorTruth.contract.ctor.params.map Param.name) args) }
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
        none) := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
    (argsStore := Std.HashMap.ofList (List.zip (CtorTruth.contract.ctor.params.map Param.name) args))
    ?_ (ctorTruthDeployment_args_length hdeploy) rfl ?_
  · rfl
  · exact ctorTruthCtorBodyReturns _ _

/-- The creation/initcode bytecode refines the Solm constructor specification. -/
theorem ctorTruthConstructorCorrect :
    constructorEquivalence ctorTruthConfig ctorTruthInitcode CtorTruth.contract
      ctorTruthRuntimeBytecode := by
  refine constructorEquivalence.intro ?_
  intro createdAccounts genesisBlockHeader blocks σ_evm σ₀_evm σ_solm σ₀_solm g A I
      args deployedInitcode hdeploy hcode hcalldata hperm hσ _hσ₀
  rcases ctorTruthInitcodeXiResult createdAccounts genesisBlockHeader blocks σ_evm σ₀_evm g A I args
      deployedInitcode hdeploy hcode hcalldata hperm with hoog | ⟨g', A', hsuccess⟩
  · exact constructorEquivalenceFor.outOfGas hoog
  · refine constructorEquivalenceFor.execution hsuccess
      (ctorTruthSolmCtorExec (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀_solm) (g := g) (A := A) (I := I)
        (args := args) hdeploy) ?_
    exact ctorResultEquiv.success rfl rfl rfl hσ rfl

/-- The full contract equivalence combines constructor/initcode and runtime equivalence. -/
theorem ctorTruthCorrect :
    contractEquivalence ctorTruthConfig ctorTruthInitcode ctorTruthRuntimeBytecode
      CtorTruth.contract :=
  contractEquivalence.intro ctorTruthConstructorCorrect ctorTruthRuntimeCorrect
