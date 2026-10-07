import Reasoning.Reach
import Reasoning.SolmBody
import Solm.SolidityLayout
import Solm.Refine

/-!
# Constructor — reusable constructor-equivalence proof skeletons

This module contains contract-agnostic glue for constructors whose Solidity/Solm constructor has no
parameters and no body.  Callers still prove their concrete initcode trace, but the deployment,
Solm-side empty-constructor execution, and final constructor-equivalence wrapper are shared.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Reach

namespace Reasoning.Theory

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
      simp [genSolidityConstructorDeployment, encodeABIValues?, encodeABIValuesFrom?,
        abiTupleHeadSize?] at hdeploy

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
      simp [genSolidityConstructorDeployment, encodeABIValues?, encodeABIValuesFrom?,
        abiTupleHeadSize?] at hdeploy

theorem emptyCtorBodyReturns
    {cfg : Config} {contract : ContractDecl} (evm : EVM.State) (locals : Store)
    (hbody : contract.ctor.body = []) :
    ExecTransitionBody cfg contract evm locals contract.ctor.body
      (.returned { contract := contract, locals := locals } evm none) := by
  rw [hbody]
  exact ExecFuncBody.execBlockOK ExecBlock.nil

theorem emptySolmCtorExec
    {cfg : Config} {contract : ContractDecl}
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
    (hdeploy : cfg.selfDeployment initcode args = some deployedInitcode)
    (himm : contract.immutables = [] := by rfl) :
    solmCtorExec cfg contract args σ σ₀ g A I
      (.returned
        { contract := contract
          locals := Std.HashMap.ofList (List.zip (contract.ctor.params.map Param.name) args) }
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        none) := by
  refine solmCtorExec.intro
    (evmState := initState σ σ₀ (Sat256.ofUInt256 g) A I)
    (argsStore := Std.HashMap.ofList (List.zip (contract.ctor.params.map Param.name) args))
    ?_ (emptyCtorDeployment_args_length hself hparams hdeploy) rfl ?_
  · rfl
  · rw [initialImmutables_noImmutables himm]
    exact emptyCtorBodyReturns _ _ hbody

/-- Generic constructor-equivalence wrapper for empty constructors.

The caller supplies only the concrete `RDret` trace proving that the initcode returns the runtime
bytecode while preserving the account map.
-/
theorem emptyConstructorCorrect_of_RDret
    {cfg : Config} {contract : ContractDecl} {initcode runtimeCode : ByteArray}
    (hself : cfg.selfDeployment = genSolidityConstructorDeployment contract.ctor.params)
    (hparams : contract.ctor.params = [])
    (hbody : contract.ctor.body = [])
    (hrun : ∀ {σ : Ethereum.AccountMap}
        {σ₀ : Ethereum.AccountMap}
        {A : Ethereum.Substate}
        {I : Ethereum.ExecutionEnv}
        {g : Sat256},
      I.code = initcode →
      RDret initcode g (initState σ σ₀ g A I) σ runtimeCode)
    (himm : contract.immutables = [] := by rfl) :
    typedConstructorRefinement cfg initcode contract (fun _ => runtimeCode) := by
  intro σ σ₀ g A I
      args deployedInitcode hdeploy hcode _hcalldata _hperm
  have hdeployed := emptyCtorDeployment_eq_initcode hself hparams hdeploy
  rw [hdeployed] at hcode
  have hrd := hrun (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode
  rcases hrd.xiResult hcode with hoog | ⟨g', A', hsuccess⟩
  · exact typedConstructorRefinementFor.outOfGas (by simpa using hoog)
  · refine typedConstructorRefinementFor.execution hsuccess
      (emptySolmCtorExec (cfg := cfg) (contract := contract)
        (σ := σ) (σ₀ := σ₀) (g := g) (A := A) (I := I)
        (args := args) (initcode := initcode) (deployedInitcode := deployedInitcode)
        hself hparams hbody hdeploy himm) ?_ (ctorImmutablesFit_noImmutables himm)
    exact ctorResultEquiv.success rfl rfl rfl rfl

theorem emptyContractCorrect_of_RDret
    {cfg : Config} {contract : ContractDecl} {initcode runtimeCode : ByteArray}
    (hself : cfg.selfDeployment = genSolidityConstructorDeployment contract.ctor.params)
    (hparams : contract.ctor.params = [])
    (hbody : contract.ctor.body = [])
    (hrun : ∀ {σ : Ethereum.AccountMap}
        {σ₀ : Ethereum.AccountMap}
        {A : Ethereum.Substate}
        {I : Ethereum.ExecutionEnv}
        {g : Sat256},
      I.code = initcode →
      RDret initcode g (initState σ σ₀ g A I) σ runtimeCode)
    (hruntime : runtimeRefinement cfg runtimeCode contract)
    (himm : contract.immutables = [] := by rfl) :
    contractRefinement cfg initcode contract :=
  contractRefinement.of_constant
    (emptyConstructorCorrect_of_RDret hself hparams hbody hrun himm)
    hruntime himm

end Reasoning.Theory
