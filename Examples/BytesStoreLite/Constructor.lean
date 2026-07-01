import Examples.BytesStoreLite.Bytecode
import Reasoning.Memory
import Reasoning.Solc
import Reasoning.Theory
import Reasoning.SolmBody
import Reasoning.Reach

/-!
# BytesStoreLite — optimized constructor/initcode proof

The full `BytesStoreLite.sol` contract has no user-written constructor, but Solidity still emits
the standard non-payable creation-code guard.  This file proves that the optimized initcode either
reverts on non-zero call value or returns the optimized deployed runtime bytecode.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 10000

namespace BytesStoreLite

noncomputable def bytesStoreLiteInitReturnMem : ByteArray :=
  bytesStoreLiteBytecode.write 0 solcFreePtrMem 0 2839

theorem bytesStoreLiteBytecode_extract_all :
    bytesStoreLiteBytecode.extract 0 2839 = bytesStoreLiteBytecode := by
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by native_decide)

theorem bytesStoreLiteInitcode_codecopy_mem :
    bytesStoreLiteInitcode.write 28 solcFreePtrMem 0 2839 = bytesStoreLiteInitReturnMem := by
  unfold bytesStoreLiteInitReturnMem
  apply ByteArray.ext
  rw [write0_data_from bytesStoreLiteInitcode solcFreePtrMem 28 2839
      (by decide) (by native_decide)]
  rw [write0_data bytesStoreLiteBytecode solcFreePtrMem 2839 (by decide)
      (by rw [bytesStoreLiteBytecode_size])]
  have hwindow :
      bytesStoreLiteInitcode.data.extract 28 (28 + 2839)
        = bytesStoreLiteBytecode.data.extract 0 2839 := by
    have h1 := congrArg ByteArray.data bytesStoreLiteInitcode_runtime_window
    have h2 := congrArg ByteArray.data bytesStoreLiteBytecode_extract_all
    simpa [ByteArray.data_extract] using h1.trans h2.symm
  rw [hwindow]

theorem bytesStoreLiteFinal_read :
    bytesStoreLiteInitReturnMem.readWithPadding 0 2839 = bytesStoreLiteBytecode := by
  unfold bytesStoreLiteInitReturnMem
  rw [write0_read_back_gen bytesStoreLiteBytecode solcFreePtrMem 2839
    (by decide) (by rw [bytesStoreLiteBytecode_size]) (by decide)]
  exact bytesStoreLiteBytecode_extract_all

theorem bytesStoreLiteConstructorGuard {createdAccounts genesisBlockHeader blocks σ σ₀ A I}
    {g : Sat256}
    (hcode : I.code = bytesStoreLiteInitcode) :
    RD bytesStoreLiteInitcode I g (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨8⟩ [UInt256.isZero I.weiValue, I.weiValue] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (createdAccounts, σ) 6 26 := by
  exact solcGuardPrologueRD (cA := createdAccounts) (gh := genesisBlockHeader)
    (bl := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (code := bytesStoreLiteInitcode) hcode
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)

theorem bytesStoreLiteInitcodeRevert {createdAccounts genesisBlockHeader blocks σ σ₀ A I}
    {g : Sat256}
    (hcode : I.code = bytesStoreLiteInitcode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev bytesStoreLiteInitcode g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  exact solcGuardCallvalueNonzeroRevert
    (ctgt := ⟨14⟩) (wC := 1) (opC := .PUSH1)
    (bytesStoreLiteConstructorGuard (createdAccounts := createdAccounts)
      (genesisBlockHeader := genesisBlockHeader) (blocks := blocks) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode)
    hwv (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)

theorem bytesStoreLiteInitcodeRun {createdAccounts genesisBlockHeader blocks σ σ₀ A I}
    {g : Sat256}
    (hcode : I.code = bytesStoreLiteInitcode) (hwv : I.weiValue = ⟨0⟩) :
    RDret bytesStoreLiteInitcode g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) (createdAccounts, σ)
      bytesStoreLiteBytecode := by
  obtain ⟨_, _, rd16⟩ := solcGuardCallvalueZero
    (ctgt := ⟨14⟩) (wC := 1) (opC := .PUSH1)
    (bytesStoreLiteConstructorGuard (createdAccounts := createdAccounts)
      (genesisBlockHeader := genesisBlockHeader) (blocks := blocks) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode)
    hwv (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  exact evm_run rd16 with [
    raw push2 ⟨2839⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨28⟩ (by native_decide) (by evm_ov),
    raw push0 (by native_decide) (by evm_ov),
    raw codecopy 273 bytesStoreLiteInitReturnMem (UInt256.ofNat 89)
      (by native_decide)
      mem_cost
      bytesStoreLiteInitcode_codecopy_mem
      (by decide) (by evm_ov),
    raw push0 (by native_decide) (by evm_ov),
    raw ret 0 bytesStoreLiteBytecode (by native_decide)
      mem_cost
      bytesStoreLiteFinal_read
      (by evm_ov)]

/-! ## Constructor equivalence -/

/-- Solidity deployment accepts only the zero-argument constructor shape. -/
theorem bytesStoreLiteDeployment_args_length {args : List Value} {deployedInitcode : ByteArray} :
    bytesStoreLiteConfig.selfDeployment bytesStoreLiteInitcode args = some deployedInitcode →
    args.length = bytesStoreLiteContract.ctor.params.length := by
  intro h
  cases args with
  | nil => rfl
  | cons arg rest =>
      simp [bytesStoreLiteConfig, genSolidityConstructorDeployment, bytesStoreLiteContract,
        encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?] at h

theorem bytesStoreLiteDeployment_eq_initcode {args : List Value} {deployedInitcode : ByteArray} :
    bytesStoreLiteConfig.selfDeployment bytesStoreLiteInitcode args = some deployedInitcode →
    deployedInitcode = bytesStoreLiteInitcode := by
  intro h
  cases args with
  | nil =>
      simp [bytesStoreLiteConfig, genSolidityConstructorDeployment, bytesStoreLiteContract,
        encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, ByteArray.append_empty] at h
      exact h.symm
  | cons arg rest =>
      simp [bytesStoreLiteConfig, genSolidityConstructorDeployment, bytesStoreLiteContract,
        encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?] at h

theorem bytesStoreLiteCtorBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm locals
      bytesStoreLiteContract.ctor.body
      (.returned { contract := bytesStoreLiteContract, locals := locals } evm none) := by
  unfold bytesStoreLiteContract
  exact ExecFuncBody.execBlockOK
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true h)) ExecBlock.nil)

theorem bytesStoreLiteCtorBodyReverts (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm locals
      bytesStoreLiteContract.ctor.body .reverted := by
  simpa [bytesStoreLiteContract] using
    (bodyReverts_nonPayable (cfg := bytesStoreLiteConfig) (contract := bytesStoreLiteContract)
      (evm := evm) (locals := locals) (rest := []) h)

theorem bytesStoreLiteSolmCtorExecReturns
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
    (hdeploy : bytesStoreLiteConfig.selfDeployment bytesStoreLiteInitcode args = some deployedInitcode)
    (hwv : I.weiValue = ⟨0⟩) :
    solmCtorExec bytesStoreLiteConfig bytesStoreLiteContract args createdAccounts genesisBlockHeader
      blocks σ σ₀ g A I
      (.returned
        { contract := bytesStoreLiteContract
          locals := Std.HashMap.ofList
            (List.zip (bytesStoreLiteContract.ctor.params.map Param.name) args) }
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
        none) := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
    (argsStore := Std.HashMap.ofList (List.zip (bytesStoreLiteContract.ctor.params.map Param.name) args))
    ?_ (bytesStoreLiteDeployment_args_length hdeploy) rfl ?_
  · rfl
  · exact bytesStoreLiteCtorBodyReturns _ _ (by simp only [initState]; exact hwv)

theorem bytesStoreLiteSolmCtorExecReverts
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
    (hdeploy : bytesStoreLiteConfig.selfDeployment bytesStoreLiteInitcode args = some deployedInitcode)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    solmCtorExec bytesStoreLiteConfig bytesStoreLiteContract args createdAccounts genesisBlockHeader
      blocks σ σ₀ g A I .reverted := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
    (argsStore := Std.HashMap.ofList (List.zip (bytesStoreLiteContract.ctor.params.map Param.name) args))
    ?_ (bytesStoreLiteDeployment_args_length hdeploy) rfl ?_
  · rfl
  · exact bytesStoreLiteCtorBodyReverts _ _ (by simp only [initState]; exact hwv)

/-- The optimized creation/initcode refines the Solm constructor specification. -/
theorem bytesStoreLiteConstructorCorrect :
    constructorEquivalence bytesStoreLiteConfig bytesStoreLiteInitcode bytesStoreLiteContract
      bytesStoreLiteBytecode := by
  refine constructorEquivalence.intro ?_
  intro createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I
      args deployedInitcode hdeploy hcode _hcalldata _hperm hσ
  have hdeployed := bytesStoreLiteDeployment_eq_initcode hdeploy
  rw [hdeployed] at hcode
  by_cases hwv : I.weiValue = ⟨0⟩
  · rcases (bytesStoreLiteInitcodeRun (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader) (blocks := blocks) (σ := σ_evm)
        (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hwv).xiResult
        hcode with
      hoog | ⟨g', A', hsuccess⟩
    · exact constructorEquivalenceFor.outOfGas hoog
    · refine constructorEquivalenceFor.execution hsuccess
        (bytesStoreLiteSolmCtorExecReturns (createdAccounts := createdAccounts)
          (genesisBlockHeader := genesisBlockHeader) (blocks := blocks) (σ := σ_solm)
          (σ₀ := σ₀) (g := g) (A := A) (I := I) (args := args) hdeploy hwv) ?_
      exact ctorResultEquiv.success rfl rfl rfl hσ rfl
  · rcases (bytesStoreLiteInitcodeRevert (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader) (blocks := blocks) (σ := σ_evm)
        (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hwv).xiResult
        hcode with
      hoog | ⟨g', o, hrevert⟩
    · exact constructorEquivalenceFor.outOfGas hoog
    · refine constructorEquivalenceFor.execution hrevert
        (bytesStoreLiteSolmCtorExecReverts (createdAccounts := createdAccounts)
          (genesisBlockHeader := genesisBlockHeader) (blocks := blocks) (σ := σ_solm)
          (σ₀ := σ₀) (g := g) (A := A) (I := I) (args := args) hdeploy hwv) ?_
      exact ctorResultEquiv.revert rfl rfl

end BytesStoreLite
