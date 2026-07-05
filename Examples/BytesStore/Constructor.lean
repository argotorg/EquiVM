import Examples.BytesStore.Bytecode
import Reasoning.Memory
import Reasoning.Solc
import Reasoning.Theory
import Reasoning.SolmBody
import Reasoning.Reach

/-!
# BytesStore — optimized constructor/initcode proof

The full `BytesStore.sol` contract has no user-written constructor, but Solidity still emits
the standard non-payable creation-code guard.  This file proves that the optimized initcode either
reverts on non-zero call value or returns the optimized deployed runtime bytecode.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 10000

namespace BytesStore

noncomputable def bytesStoreInitReturnMem : ByteArray :=
  bytesStoreBytecode.write 0 solcFreePtrMem 0 2839

theorem bytesStoreBytecode_extract_all :
    bytesStoreBytecode.extract 0 2839 = bytesStoreBytecode := by
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by native_decide)

theorem bytesStoreInitcode_codecopy_mem :
    bytesStoreInitcode.write 28 solcFreePtrMem 0 2839 = bytesStoreInitReturnMem := by
  unfold bytesStoreInitReturnMem
  apply ByteArray.ext
  rw [write0_data_from bytesStoreInitcode solcFreePtrMem 28 2839
      (by decide) (by native_decide)]
  rw [write0_data bytesStoreBytecode solcFreePtrMem 2839 (by decide)
      (by rw [bytesStoreBytecode_size])]
  have hwindow :
      bytesStoreInitcode.data.extract 28 (28 + 2839)
        = bytesStoreBytecode.data.extract 0 2839 := by
    have h1 := congrArg ByteArray.data bytesStoreInitcode_runtime_window
    have h2 := congrArg ByteArray.data bytesStoreBytecode_extract_all
    simpa [ByteArray.data_extract] using h1.trans h2.symm
  rw [hwindow]

theorem bytesStoreFinal_read :
    bytesStoreInitReturnMem.readWithPadding 0 2839 = bytesStoreBytecode := by
  unfold bytesStoreInitReturnMem
  rw [write0_read_back_gen bytesStoreBytecode solcFreePtrMem 2839
    (by decide) (by rw [bytesStoreBytecode_size]) (by decide)]
  exact bytesStoreBytecode_extract_all

theorem bytesStoreConstructorGuard {createdAccounts genesisBlockHeader blocks σ σ₀ A I}
    {g : Sat256}
    (hcode : I.code = bytesStoreInitcode) :
    RD bytesStoreInitcode I g (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨8⟩ [UInt256.isZero I.weiValue, I.weiValue] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (createdAccounts, σ) 6 26 := by
  exact solcGuardPrologueRD (cA := createdAccounts) (gh := genesisBlockHeader)
    (bl := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (code := bytesStoreInitcode) hcode
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)

theorem bytesStoreInitcodeRevert {createdAccounts genesisBlockHeader blocks σ σ₀ A I}
    {g : Sat256}
    (hcode : I.code = bytesStoreInitcode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev bytesStoreInitcode g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  exact solcGuardCallvalueNonzeroRevert
    (ctgt := ⟨14⟩) (wC := 1) (opC := .PUSH1)
    (bytesStoreConstructorGuard (createdAccounts := createdAccounts)
      (genesisBlockHeader := genesisBlockHeader) (blocks := blocks) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode)
    hwv (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)

theorem bytesStoreInitcodeRun {createdAccounts genesisBlockHeader blocks σ σ₀ A I}
    {g : Sat256}
    (hcode : I.code = bytesStoreInitcode) (hwv : I.weiValue = ⟨0⟩) :
    RDret bytesStoreInitcode g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) (createdAccounts, σ)
      bytesStoreBytecode := by
  obtain ⟨_, _, rd16⟩ := solcGuardCallvalueZero
    (ctgt := ⟨14⟩) (wC := 1) (opC := .PUSH1)
    (bytesStoreConstructorGuard (createdAccounts := createdAccounts)
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
    raw codecopy 273 bytesStoreInitReturnMem (UInt256.ofNat 89)
      (by native_decide)
      mem_cost
      bytesStoreInitcode_codecopy_mem
      (by decide) (by evm_ov),
    raw push0 (by native_decide) (by evm_ov),
    raw ret 0 bytesStoreBytecode (by native_decide)
      mem_cost
      bytesStoreFinal_read
      (by evm_ov)]

/-! ## Constructor equivalence -/

/-- Solidity deployment accepts only the zero-argument constructor shape. -/
theorem bytesStoreDeployment_args_length {args : List Value} {deployedInitcode : ByteArray} :
    bytesStoreConfig.selfDeployment bytesStoreInitcode args = some deployedInitcode →
    args.length = bytesStoreContract.ctor.params.length := by
  intro h
  cases args with
  | nil => rfl
  | cons arg rest =>
      simp [bytesStoreConfig, genSolidityConstructorDeployment, bytesStoreContract,
        encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?] at h

theorem bytesStoreDeployment_eq_initcode {args : List Value} {deployedInitcode : ByteArray} :
    bytesStoreConfig.selfDeployment bytesStoreInitcode args = some deployedInitcode →
    deployedInitcode = bytesStoreInitcode := by
  intro h
  cases args with
  | nil =>
      simp [bytesStoreConfig, genSolidityConstructorDeployment, bytesStoreContract,
        encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, ByteArray.append_empty] at h
      exact h.symm
  | cons arg rest =>
      simp [bytesStoreConfig, genSolidityConstructorDeployment, bytesStoreContract,
        encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?] at h

theorem bytesStoreCtorBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm locals
      bytesStoreContract.ctor.body
      (.returned { contract := bytesStoreContract, locals := locals } evm none) := by
  unfold bytesStoreContract
  exact ExecFuncBody.execBlockOK
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true h)) ExecBlock.nil)

theorem bytesStoreCtorBodyReverts (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm locals
      bytesStoreContract.ctor.body .reverted := by
  simpa [bytesStoreContract] using
    (bodyReverts_nonPayable (cfg := bytesStoreConfig) (contract := bytesStoreContract)
      (evm := evm) (locals := locals) (rest := []) h)

theorem bytesStoreSolmCtorExecReturns
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
    (hdeploy : bytesStoreConfig.selfDeployment bytesStoreInitcode args = some deployedInitcode)
    (hwv : I.weiValue = ⟨0⟩) :
    solmCtorExec bytesStoreConfig bytesStoreContract args createdAccounts genesisBlockHeader
      blocks σ σ₀ g A I
      (.returned
        { contract := bytesStoreContract
          locals := Std.HashMap.ofList
            (List.zip (bytesStoreContract.ctor.params.map Param.name) args) }
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
        none) := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
    (argsStore := Std.HashMap.ofList (List.zip (bytesStoreContract.ctor.params.map Param.name) args))
    ?_ (bytesStoreDeployment_args_length hdeploy) rfl ?_
  · rfl
  · exact bytesStoreCtorBodyReturns _ _ (by simp only [initState]; exact hwv)

theorem bytesStoreSolmCtorExecReverts
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
    (hdeploy : bytesStoreConfig.selfDeployment bytesStoreInitcode args = some deployedInitcode)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    solmCtorExec bytesStoreConfig bytesStoreContract args createdAccounts genesisBlockHeader
      blocks σ σ₀ g A I .reverted := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
    (argsStore := Std.HashMap.ofList (List.zip (bytesStoreContract.ctor.params.map Param.name) args))
    ?_ (bytesStoreDeployment_args_length hdeploy) rfl ?_
  · rfl
  · exact bytesStoreCtorBodyReverts _ _ (by simp only [initState]; exact hwv)

/-- The optimized creation/initcode refines the Solm constructor specification. -/
theorem bytesStoreConstructorCorrect :
    constructorEquivalence bytesStoreConfig bytesStoreInitcode bytesStoreContract
      bytesStoreBytecode := by
  refine constructorEquivalence.intro ?_
  intro createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I
      args deployedInitcode hdeploy hcode _hcalldata _hperm hσ
  have hdeployed := bytesStoreDeployment_eq_initcode hdeploy
  rw [hdeployed] at hcode
  by_cases hwv : I.weiValue = ⟨0⟩
  · rcases (bytesStoreInitcodeRun (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader) (blocks := blocks) (σ := σ_evm)
        (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hwv).xiResult
        hcode with
      hoog | ⟨g', A', hsuccess⟩
    · exact constructorEquivalenceFor.outOfGas hoog
    · refine constructorEquivalenceFor.execution hsuccess
        (bytesStoreSolmCtorExecReturns (createdAccounts := createdAccounts)
          (genesisBlockHeader := genesisBlockHeader) (blocks := blocks) (σ := σ_solm)
          (σ₀ := σ₀) (g := g) (A := A) (I := I) (args := args) hdeploy hwv) ?_
      exact ctorResultEquiv.success rfl rfl rfl hσ rfl
  · rcases (bytesStoreInitcodeRevert (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader) (blocks := blocks) (σ := σ_evm)
        (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hwv).xiResult
        hcode with
      hoog | ⟨g', o, hrevert⟩
    · exact constructorEquivalenceFor.outOfGas hoog
    · refine constructorEquivalenceFor.execution hrevert
        (bytesStoreSolmCtorExecReverts (createdAccounts := createdAccounts)
          (genesisBlockHeader := genesisBlockHeader) (blocks := blocks) (σ := σ_solm)
          (σ₀ := σ₀) (g := g) (A := A) (I := I) (args := args) hdeploy hwv) ?_
      exact ctorResultEquiv.revert rfl rfl

end BytesStore
