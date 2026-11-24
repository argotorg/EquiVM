import Stele.Refine

namespace Stele

/-- A copy of `typedConstructorRefinementOn` restricted to deployments whose complete initcode
    (including encoded constructor arguments) fits in an EVM size word without wrapping.
    The deployment encoder and the execution/result relation are unchanged. -/
def typedConstructorRefinementWithCodeBoundOn (forks : ForkSet) (cfg : Config)
    (initcode : ByteArray) (contract : ContractDecl) (runtimeCodeOf : Store → ByteArray) : Prop :=
  ∀ (fork : Ethereum.Fork), forks fork → ∀ (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256)
    (A : Ethereum.Substate) (I : Ethereum.ExecutionEnv) (args : List Value) (deployedInitcode : ByteArray),
    cfg.selfDeployment initcode args = .some deployedInitcode →
    I.code = deployedInitcode →
    I.calldata = .empty →
    I.perm = true →
    I.code.size < Ethereum.UInt256.size →
    typedConstructorRefinementFor fork cfg contract args σ σ₀ g A I runtimeCodeOf

/-- `typedConstructorRefinementWithCodeBoundOn` at every supported fork. -/
abbrev typedConstructorRefinementWithCodeBound (cfg : Config) (initcode : ByteArray)
    (contract : ContractDecl) (runtimeCodeOf : Store → ByteArray) : Prop :=
  typedConstructorRefinementWithCodeBoundOn supportedForks cfg initcode contract runtimeCodeOf

/-- `contractRefinementWFOn` with the deployment domain of
    `typedConstructorRefinementWithCodeBoundOn`. The runtime storage and gas conditions are
    unchanged; the additional bound applies only to complete initcode at deployment. -/
inductive contractRefinementWFWithCodeBoundOn (forks : ForkSet) (wf : StorageWF)
    (gasBound : GasBound) (cfg : Config) (initcode : ByteArray) (contract : ContractDecl) :
    Prop where
  | intro (runtimeCodeOf : Store → ByteArray) :
    (∀ (fork : Ethereum.Fork), forks fork → ∀ (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256)
      (A : Ethereum.Substate) (I : Ethereum.ExecutionEnv) (args : List Value) (deployedInitcode : ByteArray),
      cfg.selfDeployment initcode args = .some deployedInitcode →
      I.code = deployedInitcode →
      I.calldata = .empty →
      I.perm = true →
      I.code.size < Ethereum.UInt256.size →
      deploymentRefinement forks fork wf gasBound cfg contract args σ σ₀ g A I runtimeCodeOf) →
    contractRefinementWFWithCodeBoundOn forks wf gasBound cfg initcode contract

/-- `contractRefinementWFWithCodeBoundOn` at every supported fork. -/
abbrev contractRefinementWFWithCodeBound (wf : StorageWF) (gasBound : GasBound) (cfg : Config)
    (initcode : ByteArray) (contract : ContractDecl) : Prop :=
  contractRefinementWFWithCodeBoundOn supportedForks wf gasBound cfg initcode contract

/-- An existing constructor proof also applies on the smaller deployment domain. -/
theorem typedConstructorRefinement.withCodeBound {forks : ForkSet} {cfg : Config}
    {initcode : ByteArray} {contract : ContractDecl} {runtimeCodeOf : Store → ByteArray}
    (h : typedConstructorRefinementOn forks cfg initcode contract runtimeCodeOf) :
    typedConstructorRefinementWithCodeBoundOn forks cfg initcode contract runtimeCodeOf :=
  fun fork hfork σ σ₀ g A I args d hdeploy hcode hcalldata hperm _ =>
    h fork hfork σ σ₀ g A I args d hdeploy hcode hcalldata hperm

/-- An existing whole-contract proof also applies on the smaller deployment domain. -/
theorem contractRefinementWF.withCodeBound {forks : ForkSet} {wf : StorageWF}
    {gasBound : GasBound} {cfg : Config} {initcode : ByteArray} {contract : ContractDecl}
    (h : contractRefinementWFOn forks wf gasBound cfg initcode contract) :
    contractRefinementWFWithCodeBoundOn forks wf gasBound cfg initcode contract := by
  cases h with
  | intro runtimeCodeOf h =>
    exact .intro runtimeCodeOf fun fork hfork σ σ₀ g A I args d hdeploy hcode hcalldata hperm _ =>
      h fork hfork σ σ₀ g A I args d hdeploy hcode hcalldata hperm

/-- Assemble a constructor proof under the initcode-size bound and the usual runtime proof. -/
theorem contractRefinementWFWithCodeBound.of_runtime {forks : ForkSet} {wf : StorageWF}
    {gasBound : GasBound} {cfg : Config} {initcode : ByteArray} {contract : ContractDecl}
    {runtimeCodeOf : Store → ByteArray}
    (hctor : typedConstructorRefinementWithCodeBoundOn forks cfg initcode contract runtimeCodeOf)
    (hrt : ∀ imms, immutablesFit contract imms →
      runtimeRefinementWithWFOn forks wf gasBound cfg (runtimeCodeOf imms) contract
        (restrictImmutables contract imms)) :
    contractRefinementWFWithCodeBoundOn forks wf gasBound cfg initcode contract :=
  .intro runtimeCodeOf fun fork hfork σ σ₀ g A I args d hdeploy hcode hcalldata hperm hsize =>
    (hctor fork hfork σ σ₀ g A I args d hdeploy hcode hcalldata hperm hsize).toDeployment hrt

end Stele
