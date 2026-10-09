import Solm.Refine

namespace Solm

/-- A copy of `typedConstructorRefinement` restricted to deployments whose complete initcode
    (including encoded constructor arguments) fits in an EVM size word without wrapping.
    The deployment encoder and the execution/result relation are unchanged. -/
def typedConstructorRefinementWithCodeBound (cfg : Config) (initcode : ByteArray)
    (contract : ContractDecl) (runtimeCodeOf : Store → ByteArray) : Prop :=
  ∀ (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) (args : List Value) (deployedInitcode : ByteArray),
    cfg.selfDeployment initcode args = .some deployedInitcode →
    I.code = deployedInitcode →
    I.calldata = .empty →
    I.perm = true →
    I.code.size < Ethereum.UInt256.size →
    typedConstructorRefinementFor cfg contract args σ σ₀ g A I runtimeCodeOf

/-- `contractRefinementWF` with the deployment domain of
    `typedConstructorRefinementWithCodeBound`. The runtime storage and gas conditions are
    unchanged; the additional bound applies only to complete initcode at deployment. -/
inductive contractRefinementWFWithCodeBound (wf : StorageWF) (gasBound : GasBound)
    (cfg : Config) (initcode : ByteArray) (contract : ContractDecl) : Prop where
  | intro (runtimeCodeOf : Store → ByteArray) :
    (∀ (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
      (I : Ethereum.ExecutionEnv) (args : List Value) (deployedInitcode : ByteArray),
      cfg.selfDeployment initcode args = .some deployedInitcode →
      I.code = deployedInitcode →
      I.calldata = .empty →
      I.perm = true →
      I.code.size < Ethereum.UInt256.size →
      deploymentRefinement wf gasBound cfg contract args σ σ₀ g A I runtimeCodeOf) →
    contractRefinementWFWithCodeBound wf gasBound cfg initcode contract

/-- An existing constructor proof also applies on the smaller deployment domain. -/
theorem typedConstructorRefinement.withCodeBound {cfg : Config} {initcode : ByteArray}
    {contract : ContractDecl} {runtimeCodeOf : Store → ByteArray}
    (h : typedConstructorRefinement cfg initcode contract runtimeCodeOf) :
    typedConstructorRefinementWithCodeBound cfg initcode contract runtimeCodeOf :=
  fun σ σ₀ g A I args d hdeploy hcode hcalldata hperm _ =>
    h σ σ₀ g A I args d hdeploy hcode hcalldata hperm

/-- An existing whole-contract proof also applies on the smaller deployment domain. -/
theorem contractRefinementWF.withCodeBound {wf : StorageWF} {gasBound : GasBound}
    {cfg : Config} {initcode : ByteArray} {contract : ContractDecl}
    (h : contractRefinementWF wf gasBound cfg initcode contract) :
    contractRefinementWFWithCodeBound wf gasBound cfg initcode contract := by
  cases h with
  | intro runtimeCodeOf h =>
    exact .intro runtimeCodeOf fun σ σ₀ g A I args d hdeploy hcode hcalldata hperm _ =>
      h σ σ₀ g A I args d hdeploy hcode hcalldata hperm

/-- Assemble a constructor proof under the initcode-size bound and the usual runtime proof. -/
theorem contractRefinementWFWithCodeBound.of_runtime {wf : StorageWF} {gasBound : GasBound}
    {cfg : Config} {initcode : ByteArray} {contract : ContractDecl}
    {runtimeCodeOf : Store → ByteArray}
    (hctor : typedConstructorRefinementWithCodeBound cfg initcode contract runtimeCodeOf)
    (hrt : ∀ imms, immutablesFit contract imms →
      runtimeRefinementWithWF wf gasBound cfg (runtimeCodeOf imms) contract
        (restrictImmutables contract imms)) :
    contractRefinementWFWithCodeBound wf gasBound cfg initcode contract :=
  .intro runtimeCodeOf fun σ σ₀ g A I args d hdeploy hcode hcalldata hperm hsize =>
    (hctor σ σ₀ g A I args d hdeploy hcode hcalldata hperm hsize).toDeployment hrt

end Solm
