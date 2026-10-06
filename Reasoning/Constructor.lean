import Reasoning.Reach
import Reasoning.SolmBody
import Solm.SolidityLayout

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
    (hdeploy : cfg.selfDeployment initcode args = some deployedInitcode) :
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
  · exact emptyCtorBodyReturns _ _ hbody

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
      RDret initcode g (initState σ σ₀ g A I) σ runtimeCode) :
    constructorEquivalence cfg initcode contract runtimeCode := by
  refine constructorEquivalence.intro ?_
  intro σ σ₀ g A I
      args deployedInitcode hdeploy hcode _hcalldata _hperm
  have hdeployed := emptyCtorDeployment_eq_initcode hself hparams hdeploy
  rw [hdeployed] at hcode
  have hrd := hrun (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode
  rcases hrd.xiResult hcode with hoog | ⟨g', A', hsuccess⟩
  · exact constructorEquivalenceFor.outOfGas (by simpa using hoog)
  · refine constructorEquivalenceFor.execution hsuccess
      (emptySolmCtorExec (cfg := cfg) (contract := contract)
        (σ := σ) (σ₀ := σ₀) (g := g) (A := A) (I := I)
        (args := args) (initcode := initcode) (deployedInitcode := deployedInitcode)
        hself hparams hbody hdeploy) ?_
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
    (hruntime : runtimeEquivalence cfg runtimeCode contract) :
    contractEquivalence cfg initcode runtimeCode contract :=
  contractEquivalence.intro
    (emptyConstructorCorrect_of_RDret hself hparams hbody hrun)
    hruntime

theorem solmEmptyParamsCtorExec_of_body {cfg : Config} {decl : ContractDecl}
    {σ σ₀ A I} {g : UInt256} {res : ExecResult}
    (hparams : decl.ctor.params = [])
    (hbody : ExecTransitionBody cfg decl (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      ∅ decl.ctor.body res) :
    solmCtorExec cfg decl [] σ σ₀ g A I res := by
  refine solmCtorExec.intro rfl ?_ ?_ hbody
  · rw [hparams]; rfl
  · rw [hparams]; rfl

end Reasoning.Theory

namespace Reasoning.Reach

open Reasoning.Theory

theorem RDret.constructorEquivalenceEmptyParams {cfg : Config} {decl : ContractDecl}
    {σ σ₀ A I} {g : UInt256} {code runtime : ByteArray}
    {acc : AccountMap} {final : EVM.State} {frame : Frame}
    (rd : RDret code (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) acc runtime)
    (hcode : I.code = code) (hparams : decl.ctor.params = [])
    (hbody : ExecTransitionBody cfg decl (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      ∅ decl.ctor.body (.returned frame final none))
    (ha : acc = final.accountMap) :
    constructorEquivalenceFor cfg decl [] σ σ₀ g A I runtime := by
  rcases rd with hoog | ⟨s, hX, hacc⟩
  · exact constructorEquivalenceFor.outOfGas
      (by simpa using Xi_error_of_X (by rw [← hcode] at hoog; exact hoog))
  · have hxi := Xi_success_of_X (by rw [← hcode] at hX; exact hX)
    rw [hacc] at hxi
    exact constructorEquivalenceFor.execution (by simpa using hxi)
      (solmEmptyParamsCtorExec_of_body hparams hbody)
      (ctorResultEquiv.success rfl rfl ha rfl)

theorem RDrev.constructorEquivalenceEmptyParams {cfg : Config} {decl : ContractDecl}
    {σ σ₀ A I} {g : UInt256} {code runtime : ByteArray}
    (rd : RDrev code (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I))
    (hcode : I.code = code) (hparams : decl.ctor.params = [])
    (hbody : ExecTransitionBody cfg decl (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      ∅ decl.ctor.body .reverted) :
    constructorEquivalenceFor cfg decl [] σ σ₀ g A I runtime := by
  rcases rd.xiResult hcode with hoog | ⟨g', o, hxi⟩
  · exact constructorEquivalenceFor.outOfGas (by simpa using hoog)
  · exact constructorEquivalenceFor.execution (by simpa using hxi)
      (solmEmptyParamsCtorExec_of_body hparams hbody) (ctorResultEquiv.revert rfl rfl)

end Reasoning.Reach
