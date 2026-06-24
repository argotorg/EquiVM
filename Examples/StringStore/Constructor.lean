import Examples.StringStore.Runtime

/-!
# StringStore — constructor and final composition

The heavier runtime proof facts live in `Examples.StringStore.Runtime`; this module contains the
constructor-side proof and the final `contractEquivalence` combiner.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace StringStore

/-! ## Constructor side -/

noncomputable def stringStoreInitReturnMem : ByteArray :=
  stringStoreInitcode.write 10 ByteArray.empty 0 4435

theorem stringStoreInitcodePrefix_size : stringStoreInitcodePrefix.size = 10 := by
  native_decide

theorem stringStoreRuntime_size : stringStoreBytecode.size = 4435 := by
  native_decide

theorem stringStoreInitcode_size : stringStoreInitcode.size = 4445 := by
  native_decide

theorem stringStoreRuntime_extract_all :
    stringStoreBytecode.extract 0 4435 = stringStoreBytecode := by
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by native_decide)

theorem stringStoreInitcode_runtime_window :
    stringStoreInitcode.extract 10 (10 + 4435) = stringStoreBytecode := by
  unfold stringStoreInitcode
  exact extract_append_right' stringStoreInitcodePrefix stringStoreBytecode 10 (10 + 4435)
    stringStoreInitcodePrefix_size.symm
    (by rw [stringStoreInitcodePrefix_size, stringStoreRuntime_size])

theorem stringStoreInitcode_codecopy_mem :
    stringStoreInitcode.write 10 ByteArray.empty 0 4435 = stringStoreInitReturnMem := by
  rfl

theorem stringStoreFinal_read :
    stringStoreInitReturnMem.readWithPadding 0 4435 = stringStoreBytecode := by
  unfold stringStoreInitReturnMem
  rw [write0_read_back_from_gen stringStoreInitcode ByteArray.empty 10 4435
    (by decide) (by rw [stringStoreInitcode_size]) (by decide)]
  exact stringStoreInitcode_runtime_window

/-- Solidity deployment accepts only an argument list of the constructor parameter length. -/
theorem stringStoreDeployment_args_length {args : List Value} {deployedInitcode : ByteArray} :
    stringStoreConfig.selfDeployment stringStoreInitcode args = some deployedInitcode →
    args.length = stringStoreContract.ctor.params.length := by
  intro h
  cases args with
  | nil => rfl
  | cons arg rest =>
      simp [stringStoreConfig, genSolidityConstructorDeployment, stringStoreContract,
        encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?] at h

theorem stringStoreDeployment_eq_initcode {args : List Value} {deployedInitcode : ByteArray} :
    stringStoreConfig.selfDeployment stringStoreInitcode args = some deployedInitcode →
    deployedInitcode = stringStoreInitcode := by
  intro h
  cases args with
  | nil =>
      simp [stringStoreConfig, genSolidityConstructorDeployment, stringStoreContract,
        encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, ByteArray.append_empty] at h
      exact h.symm
  | cons arg rest =>
      simp [stringStoreConfig, genSolidityConstructorDeployment, stringStoreContract,
        encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?] at h

set_option maxHeartbeats 400000 in
theorem stringStoreInitcodeRun {createdAccounts genesisBlockHeader blocks σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stringStoreInitcode) :
    RDret stringStoreInitcode g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) (createdAccounts, σ)
      stringStoreBytecode := by
  set s0 := initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I with hs0
  have rd0 :
      RD stringStoreInitcode I g s0 ⟨0⟩ [] ByteArray.empty (UInt256.ofNat 0) ByteArray.empty
        (createdAccounts, σ) 0 0 := by
    rw [hs0]; exact RD.initState hcode
  exact evm_run rd0 with [
    raw push2 ⟨4435⟩ stringStoreDecode0 (by evm_ov),
    raw dup1 stringStoreDecode3 (by evm_ov),
    raw push1 ⟨10⟩ stringStoreDecode4 (by evm_ov),
    raw push0 stringStoreDecode6 (by evm_ov),
    raw codecopy 454 stringStoreInitReturnMem (UInt256.ofNat 139) stringStoreDecode7
      mem_cost
      stringStoreInitcode_codecopy_mem
      (by decide) (by evm_ov),
    raw push0 stringStoreDecode8 (by evm_ov),
    raw ret 0 stringStoreBytecode stringStoreDecode9
      mem_cost
      stringStoreFinal_read
      (by evm_ov)]

theorem stringStoreInitcodeXiResult
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
    stringStoreConfig.selfDeployment stringStoreInitcode args = some deployedInitcode →
    I.code = deployedInitcode →
    I.calldata = .empty →
    I.perm = true →
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .error .OutOfGass
      ∨ ∃ (g' : UInt256) (A' : Substate),
          Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I
            = .ok (.success (createdAccounts, σ, g', A') stringStoreBytecode) := by
  intro hdeploy hcode _hcalldata _hperm
  have hdeployed := stringStoreDeployment_eq_initcode hdeploy
  rw [hdeployed] at hcode
  rcases (stringStoreInitcodeRun (createdAccounts := createdAccounts)
      (genesisBlockHeader := genesisBlockHeader) (blocks := blocks) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode).xiResult hcode with
    hoog | ⟨g', A', hsuccess⟩
  · left
    simpa using hoog
  · right
    exact ⟨g', A', hsuccess⟩

theorem stringStoreCtorBodyReturns
    (evm : EVM.State) (locals : Store) :
    ExecTransitionBody stringStoreConfig stringStoreContract evm locals stringStoreContract.ctor.body
      (.returned { contract := stringStoreContract, locals := locals } evm none) := by
  exact ExecFuncBody.execBlockOK ExecBlock.nil

theorem stringStoreSolmCtorExec
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
    (hdeploy : stringStoreConfig.selfDeployment stringStoreInitcode args = some deployedInitcode) :
    solmCtorExec stringStoreConfig stringStoreContract args createdAccounts genesisBlockHeader blocks
      σ σ₀ g A I
      (.returned
        { contract := stringStoreContract
          locals := Std.HashMap.ofList (List.zip (stringStoreContract.ctor.params.map Param.name) args) }
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
        none) := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
    (argsStore := Std.HashMap.ofList (List.zip (stringStoreContract.ctor.params.map Param.name) args))
    ?_ (stringStoreDeployment_args_length hdeploy) rfl ?_
  · rfl
  · exact stringStoreCtorBodyReturns _ _

/-- The creation/initcode bytecode refines the Solm constructor specification. -/
theorem stringStoreConstructorCorrect :
    constructorEquivalence stringStoreConfig stringStoreInitcode stringStoreContract
      stringStoreBytecode := by
  refine constructorEquivalence.intro ?_
  intro createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I
      args deployedInitcode hdeploy hcode hcalldata hperm hσ
  rcases stringStoreInitcodeXiResult createdAccounts genesisBlockHeader blocks σ_evm σ₀ g A I args
      deployedInitcode hdeploy hcode hcalldata hperm with hoog | ⟨g', A', hsuccess⟩
  · exact constructorEquivalenceFor.outOfGas hoog
  · refine constructorEquivalenceFor.execution hsuccess
      (stringStoreSolmCtorExec (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader) (blocks := blocks) (σ := σ_solm)
        (σ₀ := σ₀) (g := g) (A := A) (I := I) (args := args) hdeploy) ?_
    exact ctorResultEquiv.success rfl rfl rfl hσ rfl

/-- Combines the completed constructor side with a future runtime proof. -/
theorem stringStoreCorrect_of_runtime
    (hruntime : runtimeEquivalence!?! stringStoreConfig stringStoreBytecode stringStoreContract) :
    contractEquivalence stringStoreConfig stringStoreInitcode stringStoreBytecode stringStoreContract :=
  contractEquivalence.intro stringStoreConstructorCorrect hruntime

end StringStore
