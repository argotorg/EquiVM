import EVMReasoning.Reach
import Solm.Reasoning.Reach
import Solm.Reasoning.SolmBody
import Solm.SolidityLayout

/-!
# Constructor — reusable constructor-equivalence proof skeletons

This module contains contract-agnostic glue for constructors whose Solidity/Solm constructor has no
parameters and no body.  Callers still prove their concrete initcode trace, but the deployment,
Solm-side empty-constructor execution, and final constructor-equivalence wrapper are shared.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Reach

namespace Reasoning.Theory

theorem toABIList?_length {vs : List Value} {avs : List ABIValue}
    (h : Value.toABIList? vs = some avs) : avs.length = vs.length := by
  induction vs generalizing avs with
  | nil => simp at h; subst h; rfl
  | cons v vs ih =>
      simp only [Value.toABIList?, bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨_, _, as, has, rfl⟩ := h
      simp [ih has]

theorem encodeABIValuesFrom?_length :
    ∀ {tys : List ABIType} {vs : List ABIValue} {hs : Nat} {head tail bs : List UInt8},
      encodeABIValuesFrom? tys vs hs head tail = some bs → vs.length = tys.length
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, _, _, _, _, h => by simp [encodeABIValuesFrom?] at h
  | _ :: _, [], _, _, _, _, h => by simp [encodeABIValuesFrom?] at h
  | ty :: tys, v :: vs, hs, head, tail, bs, h => by
      simp only [encodeABIValuesFrom?, bind, Option.bind_eq_some_iff] at h
      obtain ⟨_, _, hrest⟩ := h
      split at hrest <;> simp [encodeABIValuesFrom?_length hrest]

/-- A Solidity deployment encodes only an argument list of the parameter length. -/
theorem genSolidityConstructorDeployment_length {params : List Param} {init : EVM.Bytes}
    {args : List Value} {d : EVM.Bytes}
    (h : genSolidityConstructorDeployment params init args = some d) :
    args.length = params.length := by
  simp only [genSolidityConstructorDeployment, encodeABIValues?, bind, Option.bind_eq_some_iff]
    at h
  obtain ⟨avs, havs, _, ⟨_, _, hfrom⟩, _⟩ := h
  rw [← toABIList?_length havs, encodeABIValuesFrom?_length hfrom, List.length_map]

/-- Successful Solidity deployment of an empty-parameter constructor implies the argument list has
    the constructor parameter length. -/
theorem emptyCtorDeployment_args_length
    {cfg : Config} {contract : ContractDecl} {initcode deployedInitcode : ByteArray}
    {args : List Value}
    (hself : cfg.selfDeployment = genSolidityConstructorDeployment contract.ctor.params)
    (hparams : contract.ctor.params = [])
    (hdeploy : cfg.selfDeployment initcode args = some deployedInitcode) :
    args.length = contract.ctor.params.length := by
  rw [hself, hparams] at hdeploy
  rw [hparams]
  cases args with
  | nil => rfl
  | cons arg rest =>
      simp [genSolidityConstructorDeployment, encodeABIValues?, abiTupleHeadSize?] at hdeploy
      cases harg : arg.toABI? <;> simp [harg] at hdeploy
      cases hrest : Value.toABIList? rest <;> simp [hrest, encodeABIValuesFrom?] at hdeploy

/-- Successful Solidity deployment of an empty-parameter constructor appends no ABI tail. -/
theorem emptyCtorDeployment_eq_initcode
    {cfg : Config} {contract : ContractDecl} {initcode deployedInitcode : ByteArray}
    {args : List Value}
    (hself : cfg.selfDeployment = genSolidityConstructorDeployment contract.ctor.params)
    (hparams : contract.ctor.params = [])
    (hdeploy : cfg.selfDeployment initcode args = some deployedInitcode) :
    deployedInitcode = initcode := by
  rw [hself, hparams] at hdeploy
  cases args with
  | nil =>
      simp [genSolidityConstructorDeployment, encodeABIValues?, encodeABIValuesFrom?,
        abiTupleHeadSize?, ByteArray.append_empty] at hdeploy
      exact hdeploy.symm
  | cons arg rest =>
      simp [genSolidityConstructorDeployment, encodeABIValues?, abiTupleHeadSize?] at hdeploy
      cases harg : arg.toABI? <;> simp [harg] at hdeploy
      cases hrest : Value.toABIList? rest <;> simp [hrest, encodeABIValuesFrom?] at hdeploy

theorem emptyCtorBodyReturns
    {cfg : Config} {contract : ContractDecl} (evm : EVM.State) (locals : Store)
    (hbody : contract.ctor.body = []) :
    ExecTransitionBody cfg contract evm locals contract.ctor.body
      (.returned { contract := contract, locals := locals } evm none) := by
  rw [hbody]
  exact ExecFuncBody.execBlockOK ExecBlock.nil

theorem emptySolmCtorExec
    {cfg : Config} {contract : ContractDecl}
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ : Ethereum.AccountMap}
    {σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {args : List Value}
    {initcode deployedInitcode : ByteArray}
    (hself : cfg.selfDeployment = genSolidityConstructorDeployment contract.ctor.params)
    (hparams : contract.ctor.params = [])
    (hbody : contract.ctor.body = [])
    (hdeploy : cfg.selfDeployment initcode args = some deployedInitcode) :
    solmCtorExec cfg contract args createdAccounts genesisBlockHeader blocks
      σ σ₀ g A I
      (.returned
        { contract := contract
          locals := Std.HashMap.ofList (List.zip (contract.ctor.params.map Param.name) args) }
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
        none) := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
    (argsStore := Std.HashMap.ofList (List.zip (contract.ctor.params.map Param.name) args))
    ?_ (emptyCtorDeployment_args_length hself hparams hdeploy) rfl ?_
  · rfl
  · exact emptyCtorBodyReturns _ _ hbody

/-- Generic constructor-equivalence wrapper for empty constructors.

The caller supplies only the concrete `RDret` trace proving that the initcode returns the runtime
bytecode while preserving created accounts and account map.
-/
theorem emptyConstructorCorrect_of_RDret
    {cfg : Config} {contract : ContractDecl} {initcode runtimeCode : ByteArray}
    (hself : cfg.selfDeployment = genSolidityConstructorDeployment contract.ctor.params)
    (hparams : contract.ctor.params = [])
    (hbody : contract.ctor.body = [])
    (hrun : ∀ {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
        {genesisBlockHeader : Ethereum.BlockHeader}
        {blocks : Ethereum.ProcessedBlocks}
        {σ : Ethereum.AccountMap}
        {σ₀ : Ethereum.AccountMap}
        {A : Ethereum.Substate}
        {I : Ethereum.ExecutionEnv}
        {g : Sat256},
      I.code = initcode →
      RDret initcode g (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
        (createdAccounts, σ) runtimeCode) :
    constructorEquivalence cfg initcode contract runtimeCode := by
  refine constructorEquivalence.intro ?_
  intro createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I
      args deployedInitcode hdeploy hcode _hcalldata _hperm hσ
  have hdeployed := emptyCtorDeployment_eq_initcode hself hparams hdeploy
  rw [hdeployed] at hcode
  have hrd := hrun (createdAccounts := createdAccounts)
      (genesisBlockHeader := genesisBlockHeader) (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode
  rcases hrd.xiResult hcode with hoog | ⟨g', A', hsuccess⟩
  · exact constructorEquivalenceFor.outOfGas (by simpa using hoog)
  · refine constructorEquivalenceFor.execution hsuccess
      (emptySolmCtorExec (cfg := cfg) (contract := contract)
        (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (g := g) (A := A) (I := I)
        (args := args) (initcode := initcode) (deployedInitcode := deployedInitcode)
        hself hparams hbody hdeploy) ?_
    exact ctorResultEquiv.success rfl rfl rfl hσ rfl

theorem emptyContractCorrect_of_RDret
    {cfg : Config} {contract : ContractDecl} {initcode runtimeCode : ByteArray}
    (hself : cfg.selfDeployment = genSolidityConstructorDeployment contract.ctor.params)
    (hparams : contract.ctor.params = [])
    (hbody : contract.ctor.body = [])
    (hrun : ∀ {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
        {genesisBlockHeader : Ethereum.BlockHeader}
        {blocks : Ethereum.ProcessedBlocks}
        {σ : Ethereum.AccountMap}
        {σ₀ : Ethereum.AccountMap}
        {A : Ethereum.Substate}
        {I : Ethereum.ExecutionEnv}
        {g : Sat256},
      I.code = initcode →
      RDret initcode g (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
        (createdAccounts, σ) runtimeCode)
    (hruntime : runtimeEquivalence cfg runtimeCode contract) :
    contractEquivalence cfg initcode runtimeCode contract :=
  contractEquivalence.intro
    (emptyConstructorCorrect_of_RDret hself hparams hbody hrun)
    hruntime

end Reasoning.Theory
