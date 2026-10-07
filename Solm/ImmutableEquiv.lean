import Solm.Equiv

/-!
# Immutable-aware contract refinement

A contract with immutables is deployed by running its constructor, and the code that constructor
returns depends on the immutables it set: the EVM runs that code from then on, and the spec's
runtime must run with those same immutables.  `contractEquivalence` cannot say this: it fixes one
runtime code and runs the runtime spec with no immutables.

`contractRefinement` says it per deployment (`deploymentRefinement`): the EVM deployment run is
matched by a Solm constructor run (`constructorRefinementFor`), which exposes the immutables it
deployed, or `none` if it did not succeed; the deployed immutables then refine at runtime
(`runtimeRefinement`).  One `runtimeCodeOf` is shared by all deployments, so the constructor
affects the runtime only through its immutables, and the deployed code is a function of them.
The constructor's final storage does not reach the runtime half: `runtimeEquivalence` quantifies
over every runtime state, so constructor-established storage facts can only enter through the
storage well-formedness precondition `wf`.

Proofs rarely go through that per deployment.  `contractRefinement.of_runtime` splits it: a
constructor proof (`typedConstructorRefinement`) that the EVM returns `runtimeCodeOf` of the final
immutables, which are well-typed, and a runtime proof for every well-typed immutables store.
-/

namespace Solm

/-- The immutables a deployed contract runs with: the declared ones of the constructor's final
    frame. -/
def restrictImmutables (contract : ContractDecl) (immutables : Store) : Store :=
  contract.immutables.foldl (fun acc d =>
    match immutables.get? d.name with
    | some v => acc.insert d.name v
    | none => acc) ∅

theorem restrictImmutables_noImmutables {contract : ContractDecl} {immutables : Store}
    (h : contract.immutables = []) : restrictImmutables contract immutables = ∅ := by
  simp [restrictImmutables, h]

/-- Whether `immutables` gives every declared immutable a value of its declared type. -/
def immutablesFit (contract : ContractDecl) (immutables : Store) : Prop :=
  ∀ d ∈ contract.immutables, ∃ v, immutables.get? d.name = some v ∧ elemValueFits d.ty v = true

/-! ## The relation -/

/-- The immutables a constructor run deploys: those of its final frame on success, none
    otherwise. -/
def deployedImmutables : ExecResult → Option Store
  | .returned frame _ _ => some frame.immutables
  | _ => none

/-- Constructor refinement at fixed deployment inputs: the EVM deployment run is matched by a Solm
    constructor run, which deployed `imms?` (`none` if it did not succeed).  On success the EVM
    returns `runtimeCodeOf` of those immutables. -/
inductive constructorRefinementFor (cfg : Config) (contract : ContractDecl) (args : List Value)
    (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) (runtimeCodeOf : Store → ByteArray) : Option Store → Prop where
  | execution {Ξ_res solmRes} :
    Ethereum.EVM.Ξ σ σ₀ g A I = Ξ_res →
    solmCtorExec cfg contract args σ σ₀ g A I solmRes →
    ctorResultEquiv Ξ_res solmRes runtimeCodeOf →
    constructorRefinementFor cfg contract args σ σ₀ g A I runtimeCodeOf
      (deployedImmutables solmRes)
  | outOfGas :
    /- TODO: non-terminating EVM programs are currently equivalent to any spec -/
    Ethereum.EVM.Ξ σ σ₀ g A I = .error .OutOfGass →
    constructorRefinementFor cfg contract args σ σ₀ g A I runtimeCodeOf none

/-- Runtime refinement of the code deployed for `imms`: every call to it
    (`runtimeEquivalenceFor`) refines the spec run with its declared immutables. -/
def runtimeRefinement (wf : StorageWF) (cfg : Config) (contract : ContractDecl)
    (runtimeCodeOf : Store → ByteArray) (imms : Store) : Prop :=
  runtimeEquivalenceWithWF wf cfg (runtimeCodeOf imms) contract (restrictImmutables contract imms)

/-- Deployment refinement at fixed deployment inputs: the constructor refines, and whatever it
    deployed refines at runtime. -/
def deploymentRefinement (wf : StorageWF) (cfg : Config) (contract : ContractDecl)
    (args : List Value) (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256)
    (A : Ethereum.Substate) (I : Ethereum.ExecutionEnv) (runtimeCodeOf : Store → ByteArray) :
    Prop :=
  ∃ imms?, constructorRefinementFor cfg contract args σ σ₀ g A I runtimeCodeOf imms? ∧
    ∀ imms, imms? = some imms → runtimeRefinement wf cfg contract runtimeCodeOf imms

/-- Top-level refinement of a contract with immutables, under a storage well-formedness
    precondition for runtime calls: `deploymentRefinement` at every deployment of `initcode` (the
    inputs of `constructorEquivalence`), for one `runtimeCodeOf` shared by all of them. -/
inductive contractRefinementWF (wf : StorageWF) (cfg : Config) (initcode : ByteArray)
    (contract : ContractDecl) : Prop where
  | intro (runtimeCodeOf : Store → ByteArray) :
    (∀ (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
      (I : Ethereum.ExecutionEnv) (args : List Value) (deployedInitcode : ByteArray),
      cfg.selfDeployment initcode args = .some deployedInitcode →
      I.code = deployedInitcode →
      I.calldata = .empty →
      I.perm = true →
      deploymentRefinement wf cfg contract args σ σ₀ g A I runtimeCodeOf) →
    contractRefinementWF wf cfg initcode contract

/-- Top-level refinement of a contract with immutables. -/
abbrev contractRefinement (cfg : Config) (initcode : ByteArray) (contract : ContractDecl) : Prop :=
  contractRefinementWF trivialStorageWF cfg initcode contract

/-! ## Proving it: constructor and runtime separately -/

/-- The final immutables of a successful constructor run are well-typed (other results carry
    none). -/
def ctorImmutablesFit (contract : ContractDecl) (solmRes : ExecResult) : Prop :=
  match solmRes with
  | .returned frame _ _ => immutablesFit contract frame.immutables
  | _ => True

/-- The constructor half as proved: `constructorRefinementFor`, plus that the deployed immutables
    are well-typed. -/
inductive typedConstructorRefinementFor (cfg : Config) (contract : ContractDecl)
    (args : List Value) (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256)
    (A : Ethereum.Substate) (I : Ethereum.ExecutionEnv) (runtimeCodeOf : Store → ByteArray) :
    Prop where
  | execution {Ξ_res solmRes} :
    Ethereum.EVM.Ξ σ σ₀ g A I = Ξ_res →
    solmCtorExec cfg contract args σ σ₀ g A I solmRes →
    ctorResultEquiv Ξ_res solmRes runtimeCodeOf →
    ctorImmutablesFit contract solmRes →
    typedConstructorRefinementFor cfg contract args σ σ₀ g A I runtimeCodeOf
  | outOfGas :
    Ethereum.EVM.Ξ σ σ₀ g A I = .error .OutOfGass →
    typedConstructorRefinementFor cfg contract args σ σ₀ g A I runtimeCodeOf

/-- `typedConstructorRefinementFor` at every deployment of `initcode`. -/
def typedConstructorRefinement (cfg : Config) (initcode : ByteArray) (contract : ContractDecl)
    (runtimeCodeOf : Store → ByteArray) : Prop :=
  ∀ (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) (args : List Value) (deployedInitcode : ByteArray),
    cfg.selfDeployment initcode args = .some deployedInitcode →
    I.code = deployedInitcode →
    I.calldata = .empty →
    I.perm = true →
    typedConstructorRefinementFor cfg contract args σ σ₀ g A I runtimeCodeOf

theorem typedConstructorRefinementFor.toDeployment {wf : StorageWF} {cfg : Config}
    {contract : ContractDecl} {args : List Value} {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256} {A : Ethereum.Substate} {I : Ethereum.ExecutionEnv}
    {runtimeCodeOf : Store → ByteArray}
    (h : typedConstructorRefinementFor cfg contract args σ σ₀ g A I runtimeCodeOf)
    (hrt : ∀ imms, immutablesFit contract imms → runtimeRefinement wf cfg contract runtimeCodeOf imms) :
    deploymentRefinement wf cfg contract args σ σ₀ g A I runtimeCodeOf := by
  cases h with
  | outOfGas hoog => exact ⟨none, .outOfGas hoog, fun _ h => by cases h⟩
  | @execution _ solmRes hΞ hsolm hres hfit =>
      refine ⟨_, .execution hΞ hsolm hres, fun imms himms => ?_⟩
      cases solmRes with
      | returned frame _ _ =>
          cases himms
          exact hrt _ hfit
      | _ => cases himms

/-- **The usual proof route**: a constructor proof for some `runtimeCodeOf`, and a runtime proof
    of `runtimeCodeOf imms` for every well-typed immutables store `imms`. -/
theorem contractRefinementWF.of_runtime {wf : StorageWF} {cfg : Config} {initcode : ByteArray}
    {contract : ContractDecl} {runtimeCodeOf : Store → ByteArray}
    (hctor : typedConstructorRefinement cfg initcode contract runtimeCodeOf)
    (hrt : ∀ imms, immutablesFit contract imms →
      runtimeEquivalenceWithWF wf cfg (runtimeCodeOf imms) contract
        (restrictImmutables contract imms)) :
    contractRefinementWF wf cfg initcode contract :=
  .intro runtimeCodeOf fun σ σ₀ g A I args d hdeploy hcode hcalldata hperm =>
    (hctor σ σ₀ g A I args d hdeploy hcode hcalldata hperm).toDeployment hrt

/-- `contractRefinementWF.of_runtime` without a storage precondition. -/
theorem contractRefinement.of_runtime {cfg : Config} {initcode : ByteArray}
    {contract : ContractDecl} {runtimeCodeOf : Store → ByteArray}
    (hctor : typedConstructorRefinement cfg initcode contract runtimeCodeOf)
    (hrt : ∀ imms, immutablesFit contract imms →
      runtimeEquivalence cfg (runtimeCodeOf imms) contract (restrictImmutables contract imms)) :
    contractRefinement cfg initcode contract :=
  contractRefinementWF.of_runtime hctor fun imms hfit =>
    runtimeEquivalenceWithWF_trivial_iff.mpr (hrt imms hfit)

/-! ## Relation to `contractEquivalence` -/

/-- Without immutables, `contractEquivalence` is the special case of a constant runtime code. -/
theorem contractEquivalence.toRefinement {cfg : Config} {initcode runtimeCode : EVM.Bytes}
    {contract : ContractDecl} (h : contractEquivalence cfg initcode runtimeCode contract) :
    contractRefinement cfg initcode contract := by
  obtain ⟨⟨hctor⟩, hrt, himm⟩ := h
  refine contractRefinement.of_runtime (runtimeCodeOf := fun _ => runtimeCode) ?_ ?_
  · intro σ σ₀ g A I args deployedInitcode hdeploy hcode hcalldata hperm
    cases hctor σ σ₀ g A I args deployedInitcode hdeploy hcode hcalldata hperm with
    | outOfGas hoog => exact .outOfGas hoog
    | execution hΞ hsolm hres =>
        refine .execution hΞ hsolm hres ?_
        unfold ctorImmutablesFit; split
        · intro d hd; simp [himm] at hd
        · trivial
  · intro imms _
    rw [restrictImmutables_noImmutables himm]
    exact hrt

end Solm
