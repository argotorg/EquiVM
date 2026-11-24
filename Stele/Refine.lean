import ABI.Encode
import ABI.Decode
import Stele.Semantics

variable {fork : Ethereum.Fork}

/-!
The statement of Stele/EVM refinement, layered bottom-up:

* **Result equivalence** — `returnEquiv`/`returnDataEquiv` couple returned bytes with spec
  return values; `execResultsEquiv` / `ctorResultEquiv` couple whole execution outcomes
  (equality of final account maps, plus the return data — for constructors, the
  returned bytes must be the deployed runtime code for the constructor's final immutables).
* **Fixed-input relation** — `runtimeRefinementFor` couples one EVM execution
  (`Ethereum.EVM.Ξ`) with one Stele execution (`steleExec`) at fixed transaction inputs, under
  one fork.
* **∀-closure** — `runtimeRefinementOn forks` (and `runtimeRefinementWithWFOn forks`, which
  carries a storage precondition and a bound on the starting gas) quantify over all inputs and
  over the forks in the set `forks`.
* **Top level** — the contract refinement (`contractRefinementOn forks`) composes the
  constructor (`typedConstructorRefinementOn forks`) and runtime relations through the
  immutables the constructor deploys.

Each closure is stated for a set of forks (`ForkSet`). The names without `On` (`runtimeRefinement`,
`contractRefinement`, …) are the closures at `supportedForks`, every fork the model supports:
Cancun onward.  `….mono` restricts a closure to fewer forks, so the general closure yields every
fork-specific one.
-/

namespace Stele

open ABI

/-- Default (zero-initialized) value for an ABI return type. Used when a function
    with a declared return type falls through without an explicit `return`: the EVM
    then returns the ABI encoding of this value (e.g. 32 zero bytes for `uint`), not
    empty output. Only the elementary types the model supports are covered. -/
def defaultAbiValue : ABIType -> Option Value
  | .elem .bool    => some (.bool false)
  | .elem .address => some (.address (.ofNat 0))
  | .elem (.int _) => some (.int 0)
  | .elem (.bytes n) => some (.fixedBytes n (List.replicate (n.val + 1) 0))
  | _              => none

/-- Equivalence of ABI-returned data. -/
inductive returnEquiv (o : ByteArray) (r : Option (List Value)) (t : List ABIType) : Prop where
  | returned :
    /- Explicit `return`: the returned values encode flat to the output.  `vs = []`, `t = []`
       subsumes an explicit void return (`encodeReturnValues? [] [] = some ∅`). -/
    r = .some vs →
    encodeReturnValues? t vs = .some o →
    returnEquiv o r t
  | fallthrough :
    /- No explicit `return`: the EVM returns the ABI encoding of each return type's default
       (zero-initialized) value.  `t = []` gives empty output. -/
    r = .none →
    t.mapM defaultAbiValue = .some dvs →
    encodeReturnValues? t dvs = .some o →
    returnEquiv o r t

-- Flat multi-return: `(uint256[], address)` with an empty array and zero address is 96 bytes —
-- `0x40` offset word, then the address word, then the array-length word — with no leading `0x20`.
#guard
  (encodeReturnValues?
      [.dynamicArray (.elem (.int (.uint ⟨256, by decide⟩))), .elem .address]
      [.array [], .address (.ofNat 0)]).map (·.toList)
    = some (List.replicate 31 0 ++ [0x40] ++ List.replicate 64 0)

-- Void is the empty flat encoding: `return;` / a fell-through void encodes to empty output.
#guard (encodeReturnValues? [] []).map (·.toList) = some []

/-- Bridge for migrating single-return proofs: the old one-value encoder is the list encoder at
    a singleton.  Definitional, so it rewrites either way. -/
@[simp] theorem encodeReturnValue_eq_singleton (t : ABIType) (v : Value) :
    encodeReturnValue? t v = encodeReturnValues? [t] [v] := rfl

/-- Equivalence of return data, per the transition's return convention. -/
inductive returnDataEquiv (o : ByteArray) (r : Option (List Value)) : ReturnConvention → Prop where
  | abi {t} :
    returnEquiv o r t →
    returnDataEquiv o r (.abi t)
  | rawBytes :
    r = some [.bytes o] →
    returnDataEquiv o r .rawBytes
  | rawBytesVoid :
    r = none →
    o = null →
    returnDataEquiv o r .rawBytes


inductive execResultsEquiv
  (evmRes: Except Ethereum.EVM.ExecutionException (Ethereum.ExecutionResult (Ethereum.AccountMap × Ethereum.UInt256 × Ethereum.Substate)))
  (steleRes : ExecResult) (returnConvention : ReturnConvention) : Prop where
  | success :
    evmRes = .ok (.success (σ', g', A') o) →
    steleRes = .returned _ steleState retVal →
    σ' = steleState.accountMap →
    returnDataEquiv o retVal returnConvention →
    execResultsEquiv evmRes steleRes returnConvention
  | revert :
    evmRes = .ok (.revert g o) →
    steleRes = .reverted →
    execResultsEquiv evmRes steleRes returnConvention
  /-- A missing entry point is matched only by an EVM revert. Its payload is unconstrained. -/
  | noMatch :
    evmRes = .ok (.revert g o) →
    steleRes = .noMatch →
    execResultsEquiv evmRes steleRes returnConvention
  /-- Rejected calldata is matched only by an EVM revert. Its payload is unconstrained. -/
  | decodingFailed :
    evmRes = .ok (.revert g o) →
    steleRes = .decodingFailed →
    execResultsEquiv evmRes steleRes returnConvention
  -- `INVALID` (`0xFE`) refines a Stele `.reverted`; legacy solc uses it as the assert/panic failure
  -- path.  Static-mode violations have their own case below; no other EVM exception is matched.
  | invalidHalt :
    evmRes = .error .InvalidInstruction →
    steleRes = .reverted →
    execResultsEquiv evmRes steleRes returnConvention
  -- Static mode (`I.perm = false`, the contract was entered through `STATICCALL`): the EVM's
  -- `StaticModeViolation` at a forbidden opcode refines a Stele `.staticViolation`, which only a
  -- state-changing statement can produce.  A body without one (a view function) can never match
  -- an EVM static halt.
  | staticHalt :
    evmRes = .error .StaticModeViolation →
    steleRes = .staticViolation →
    execResultsEquiv evmRes steleRes returnConvention

/-- Constructor result equivalence.  On success the final account maps agree and the returned
    bytes are `runtimeCodeOf` of the immutables in the constructor's final frame. -/
inductive ctorResultEquiv
  (evmRes: Except Ethereum.EVM.ExecutionException (Ethereum.ExecutionResult (Ethereum.AccountMap × Ethereum.UInt256 × Ethereum.Substate)))
  (steleRes : ExecResult) (runtimeCodeOf : Store → ByteArray) : Prop where
  | success :
    evmRes = .ok (.success (σ', g', A') o) →
    steleRes = .returned steleFrame steleState .none →
    σ' = steleState.accountMap →
    o = runtimeCodeOf steleFrame.immutables →
    ctorResultEquiv evmRes steleRes runtimeCodeOf
  -- Twin of `success` for a ctor body ending in a bare `return` (explicit void return `some []`);
  -- kept separate so existing `.success` (fall-through `.none`) proofs are unchanged.
  | successVoidReturn :
    evmRes = .ok (.success (σ', g', A') o) →
    steleRes = .returned steleFrame steleState (some []) →
    σ' = steleState.accountMap →
    o = runtimeCodeOf steleFrame.immutables →
    ctorResultEquiv evmRes steleRes runtimeCodeOf
  | revert :
    evmRes = .ok (.revert g o) →
    steleRes = .reverted →
    ctorResultEquiv evmRes steleRes runtimeCodeOf
  -- `INVALID` (`0xFE`) refines a Stele `.reverted`, as in `execResultsEquiv.invalidHalt`.
  | invalidHalt :
    evmRes = .error .InvalidInstruction →
    steleRes = .reverted →
    ctorResultEquiv evmRes steleRes runtimeCodeOf

/-- Runtime refinement of a single message call at fixed transaction inputs: couples the EVM
    execution of the bytecode (`Ethereum.EVM.Ξ`) with the Stele execution of the spec (`steleExec`),
    both run under `fork` from the given accounts, gas, substate, and environment `I` (which
    carries the code and calldata).

    Holds in exactly one of two ways:
    * `execution`: `steleExec` produces `steleRes`; the EVM result is `execResultsEquiv`-related
      to it under the message's return convention. This includes `.noMatch` and `.decodingFailed`,
      each matched only by an EVM revert, and the static-mode case (`I.perm = false`): an EVM
      `StaticModeViolation` pairs with a Stele `.staticViolation`.
    * `outOfGas`: the EVM exhausts its gas; the spec side is unconstrained.  (TODO: because
      termination is not forced, a non-terminating EVM program is equivalent to any spec.)

    `immutables` are the values the contract was deployed with (`∅` without immutables). -/
inductive runtimeRefinementFor (fork : Ethereum.Fork) (cfg : Config)
    (contract : ContractDecl) /- Spec -/
    (σ : Ethereum.AccountMap)
    (σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) /- contains the EVM bytecode -/
    (immutables : Store := ∅)
: Prop where
  | execution {Ξ_res steleRes returnConvention} : /- Both executions produce related outcomes -/
    /- Execute EVM transaction-/
    Ethereum.EVM.Ξ fork σ σ₀ g A I = Ξ_res →
    /- Stele message execution, including dispatch and calldata-decoding failures -/
    steleExec fork cfg contract immutables σ σ₀ g A I steleRes returnConvention →
    /- The outcomes must be related by result equivalence -/
    execResultsEquiv Ξ_res steleRes returnConvention →
    runtimeRefinementFor fork cfg contract σ σ₀ g A I immutables
  | outOfGas : /- EVM runs out of gas -/
    /- TODO: non-terminating EVM programs are currently equivalent to any spec -/
    Ethereum.EVM.Ξ fork σ σ₀ g A I = .error .OutOfGass →
    runtimeRefinementFor fork cfg contract σ σ₀ g A I immutables

/-! ## Fork sets -/

/-- A set of forks a refinement is stated for. -/
abbrev ForkSet := Ethereum.Fork → Prop

/-- The forks from `f` onward, in activation order: what bytecode compiled for `f` runs under. -/
def forksFrom (f : Ethereum.Fork) : ForkSet := fun fork => f ≤ fork

/-- The single fork `f`. -/
def onlyFork (f : Ethereum.Fork) : ForkSet := fun fork => fork = f

/-- Every fork the model supports: Cancun onward. -/
abbrev supportedForks : ForkSet := forksFrom .cancun

/-- Every fork is a supported fork. -/
theorem supportedForks_mem (fork : Ethereum.Fork) : supportedForks fork := Ethereum.Fork.cancun_le fork

theorem forksFrom_mono {f f' : Ethereum.Fork} (h : f ≤ f') {fork : Ethereum.Fork}
    (hf : forksFrom f' fork) : forksFrom f fork :=
  Nat.le_trans h hf

theorem onlyFork_sub_forksFrom {f fork : Ethereum.Fork} (h : onlyFork f fork) :
    forksFrom f fork := by
  cases h; exact Nat.le_refl _

/-- The forks of `forks` from `f` onward: the forks a contract deployed under `f` can be called
    under, within `forks`. -/
def forksAfter (forks : ForkSet) (f : Ethereum.Fork) : ForkSet := fun fork => forks fork ∧ f ≤ fork

abbrev StorageWF := Ethereum.AccountMap → Ethereum.ExecutionEnv → Prop

/-- Trivial storage well-formedness predicate for contracts whose correctness is unconditional. -/
def trivialStorageWF : StorageWF := fun _ _ => True

/-- A bound on the gas a runtime call starts with (e.g. `fun g => g.toNat < 2^64`). -/
abbrev GasBound := Ethereum.UInt256 → Prop

/-- No gas bound: refinement holds for every amount of gas. -/
def noGasBound : GasBound := fun _ => True

/-- Runtime refinement under the forks `forks`, a contract-specific storage well-formedness
precondition and a gas bound.

This is the same runtime relation as `runtimeRefinementOn`, except it only covers calls where
`wf σ I` holds for the EVM-side initial storage and execution environment, and `gasBound g`
holds for the starting gas.  Both relations cover either permission mode. -/
inductive runtimeRefinementWithWFOn (forks : ForkSet) (wf : StorageWF) (gasBound : GasBound)
    (cfg : Config) (bytecode : ByteArray) (contract : ContractDecl) (immutables : Store := ∅) :
    Prop where
  | intro :
    (∀ (fork : Ethereum.Fork), forks fork → ∀
      (σ : Ethereum.AccountMap)
      (σ₀ : Ethereum.AccountMap)
      (g : Ethereum.UInt256)
      (A : Ethereum.Substate)
      (I : Ethereum.ExecutionEnv),
    I.code = bytecode →
    I.calldata.size < Ethereum.UInt256.size →
    wf σ I →
    gasBound g →
    runtimeRefinementFor fork cfg contract σ σ₀ g A I immutables
    ) →
    runtimeRefinementWithWFOn forks wf gasBound cfg bytecode contract immutables

/-- `runtimeRefinementWithWFOn` at every supported fork. -/
abbrev runtimeRefinementWithWF (wf : StorageWF) (gasBound : GasBound) (cfg : Config)
    (bytecode : ByteArray) (contract : ContractDecl) (immutables : Store := ∅) : Prop :=
  runtimeRefinementWithWFOn supportedForks wf gasBound cfg bytecode contract immutables

/-- Runtime refinement of `bytecode` under the forks `forks`, with the spec run with the deployed
    `immutables`, in either permission mode.  When entered through `STATICCALL`, the EVM halts at
    the first forbidden opcode and Stele halts at a state-changing statement, paired by
    `execResultsEquiv.staticHalt`. -/
inductive runtimeRefinementOn (forks : ForkSet) (cfg : Config) (bytecode : ByteArray)
    (contract : ContractDecl) (immutables : Store := ∅) : Prop where
  | intro :
    (∀ (fork : Ethereum.Fork), forks fork → ∀
      (σ : Ethereum.AccountMap)
      (σ₀ : Ethereum.AccountMap)
      (g : Ethereum.UInt256)
      (A : Ethereum.Substate)
      (I : Ethereum.ExecutionEnv),
    I.code = bytecode →
    I.calldata.size < Ethereum.UInt256.size →
    runtimeRefinementFor fork cfg contract σ σ₀ g A I immutables
    ) →
    runtimeRefinementOn forks cfg bytecode contract immutables

/-- Runtime refinement at every supported fork (Cancun onward). -/
abbrev runtimeRefinement (cfg : Config) (bytecode : ByteArray) (contract : ContractDecl)
    (immutables : Store := ∅) : Prop :=
  runtimeRefinementOn supportedForks cfg bytecode contract immutables

/-- Runtime refinement from the fork `f` onward. -/
abbrev runtimeRefinementFrom (f : Ethereum.Fork) (cfg : Config) (bytecode : ByteArray)
    (contract : ContractDecl) (immutables : Store := ∅) : Prop :=
  runtimeRefinementOn (forksFrom f) cfg bytecode contract immutables

/-- Runtime refinement at the single fork `f`. -/
abbrev runtimeRefinementAt (f : Ethereum.Fork) (cfg : Config) (bytecode : ByteArray)
    (contract : ContractDecl) (immutables : Store := ∅) : Prop :=
  runtimeRefinementOn (onlyFork f) cfg bytecode contract immutables

/-- Sanity check: the two definitions agree for the trivial storage predicate and no gas bound. -/
theorem runtimeRefinementWithWF_trivial_iff {forks : ForkSet} {cfg : Config}
    {bytecode : ByteArray} {contract : ContractDecl} {immutables : Store} :
    runtimeRefinementWithWFOn forks trivialStorageWF noGasBound cfg bytecode contract immutables ↔
      runtimeRefinementOn forks cfg bytecode contract immutables := by
  constructor
  · intro h
    cases h with
    | intro hrun =>
        refine runtimeRefinementOn.intro ?_
        intro fork hfork σ σ₀ g A I hcode hsize
        exact hrun fork hfork σ σ₀ g A I hcode hsize trivial trivial
  · intro h
    cases h with
    | intro hrun =>
        refine runtimeRefinementWithWFOn.intro ?_
        intro fork hfork σ σ₀ g A I hcode hsize _hwf _hgas
        exact hrun fork hfork σ σ₀ g A I hcode hsize

/-- A runtime refinement holds on every smaller set of forks. -/
theorem runtimeRefinementWithWFOn.mono {forks forks' : ForkSet} {wf : StorageWF}
    {gasBound : GasBound} {cfg : Config} {bytecode : ByteArray} {contract : ContractDecl}
    {immutables : Store} (hsub : ∀ fork, forks' fork → forks fork)
    (h : runtimeRefinementWithWFOn forks wf gasBound cfg bytecode contract immutables) :
    runtimeRefinementWithWFOn forks' wf gasBound cfg bytecode contract immutables := by
  cases h with
  | intro hrun => exact .intro fun fork hfork => hrun fork (hsub fork hfork)

/-- A runtime refinement holds on every smaller set of forks. -/
theorem runtimeRefinementOn.mono {forks forks' : ForkSet} {cfg : Config} {bytecode : ByteArray}
    {contract : ContractDecl} {immutables : Store} (hsub : ∀ fork, forks' fork → forks fork)
    (h : runtimeRefinementOn forks cfg bytecode contract immutables) :
    runtimeRefinementOn forks' cfg bytecode contract immutables := by
  cases h with
  | intro hrun => exact .intro fun fork hfork => hrun fork (hsub fork hfork)

/-- The general runtime refinement gives the refinement on any set of forks. -/
theorem runtimeRefinement.on {forks : ForkSet} {cfg : Config} {bytecode : ByteArray}
    {contract : ContractDecl} {immutables : Store}
    (h : runtimeRefinement cfg bytecode contract immutables) :
    runtimeRefinementOn forks cfg bytecode contract immutables :=
  h.mono fun fork _ => supportedForks_mem fork

/-! ## Contract refinement

A contract with immutables is deployed by running its constructor, and the code that constructor
returns depends on the immutables it set: the EVM runs that code from then on, and the spec's
runtime must run with those same immutables.

`contractRefinement` says it per deployment (`deploymentRefinement`): the EVM deployment run is
matched by a Stele constructor run (`constructorRefinementFor`), which exposes the immutables it
deployed, or `none` if it did not succeed; the code deployed for those immutables then refines the
spec run with them (`runtimeRefinementWithWFOn`).  The runtime half covers every fork of the set
from the deployment's onward (`forksAfter`): a contract deployed under one fork is called under
that fork and later ones, never earlier ones.  One `runtimeCodeOf` is shared by all deployments,
so the constructor affects the runtime only through its immutables, and the deployed code is a
function of them.
The constructor's final storage does not reach the runtime half: `runtimeRefinement` quantifies
over every runtime state, so constructor-established storage facts can only enter through the
storage well-formedness precondition `wf`.  The runtime half can likewise be restricted to calls
whose starting gas satisfies `gasBound`; the constructor half is unaffected.

Proofs rarely go through that per deployment.  `contractRefinement.of_runtime` splits it: a
constructor proof (`typedConstructorRefinement`) that the EVM returns `runtimeCodeOf` of the final
immutables, which are well-typed, and a runtime proof for every well-typed immutables store.  A
contract without immutables uses `contractRefinement.of_constant`: a constructor proof returning
one `runtimeCode` (`runtimeCodeOf := fun _ => runtimeCode`, well-typedness discharged
automatically), and a `runtimeRefinement` of that code.
-/

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

/-! ### The relation -/

/-- The immutables a constructor run deploys: those of its final frame on success, none
    otherwise. -/
def deployedImmutables : ExecResult → Option Store
  | .returned frame _ _ => some frame.immutables
  | _ => none

/-- Constructor refinement at fixed deployment inputs: the EVM deployment run is matched by a Stele
    constructor run, which deployed `imms?` (`none` if it did not succeed).  On success the EVM
    returns `runtimeCodeOf` of those immutables. -/
inductive constructorRefinementFor (fork : Ethereum.Fork) (cfg : Config) (contract : ContractDecl) (args : List Value)
    (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) (runtimeCodeOf : Store → ByteArray) : Option Store → Prop where
  | execution {Ξ_res steleRes} :
    Ethereum.EVM.Ξ fork σ σ₀ g A I = Ξ_res →
    steleCtorExec fork cfg contract args σ σ₀ g A I steleRes →
    ctorResultEquiv Ξ_res steleRes runtimeCodeOf →
    constructorRefinementFor fork cfg contract args σ σ₀ g A I runtimeCodeOf
      (deployedImmutables steleRes)
  | outOfGas :
    /- TODO: non-terminating EVM programs are currently equivalent to any spec -/
    Ethereum.EVM.Ξ fork σ σ₀ g A I = .error .OutOfGass →
    constructorRefinementFor fork cfg contract args σ σ₀ g A I runtimeCodeOf none

/-- Deployment refinement at fixed deployment inputs: the constructor refines under `fork`, and
    whatever it deployed refines at runtime under every fork of `forks` from `fork` onward. -/
def deploymentRefinement (forks : ForkSet) (fork : Ethereum.Fork) (wf : StorageWF)
    (gasBound : GasBound) (cfg : Config) (contract : ContractDecl)
    (args : List Value) (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256)
    (A : Ethereum.Substate) (I : Ethereum.ExecutionEnv) (runtimeCodeOf : Store → ByteArray) :
    Prop :=
  ∃ imms?, constructorRefinementFor fork cfg contract args σ σ₀ g A I runtimeCodeOf imms? ∧
    ∀ imms, imms? = some imms →
      runtimeRefinementWithWFOn (forksAfter forks fork) wf gasBound cfg (runtimeCodeOf imms)
        contract (restrictImmutables contract imms)

/-- Top-level refinement of a contract with immutables under the forks `forks`, a storage
    well-formedness precondition and a gas bound for runtime calls: `deploymentRefinement` at
    every deployment of `initcode` under a fork of `forks` (the deployment inputs of
    `typedConstructorRefinementOn`), for one `runtimeCodeOf` shared by all of them. -/
inductive contractRefinementWFOn (forks : ForkSet) (wf : StorageWF) (gasBound : GasBound)
    (cfg : Config) (initcode : ByteArray) (contract : ContractDecl) : Prop where
  | intro (runtimeCodeOf : Store → ByteArray) :
    (∀ (fork : Ethereum.Fork), forks fork → ∀ (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256)
      (A : Ethereum.Substate) (I : Ethereum.ExecutionEnv) (args : List Value) (deployedInitcode : ByteArray),
      cfg.selfDeployment initcode args = .some deployedInitcode →
      I.code = deployedInitcode →
      I.calldata = .empty →
      -- Init code never runs in static mode: the transaction entry `Υ` passes `true` to `Λ`, and
      -- `CREATE`/`CREATE2` are themselves forbidden under `perm = false`, so `Λ` is never reached
      -- with it.  The hypothesis excludes nothing reachable.
      I.perm = true →
      deploymentRefinement forks fork wf gasBound cfg contract args σ σ₀ g A I runtimeCodeOf) →
    contractRefinementWFOn forks wf gasBound cfg initcode contract

/-- `contractRefinementWFOn` at every supported fork. -/
abbrev contractRefinementWF (wf : StorageWF) (gasBound : GasBound) (cfg : Config)
    (initcode : ByteArray) (contract : ContractDecl) : Prop :=
  contractRefinementWFOn supportedForks wf gasBound cfg initcode contract

/-- Top-level refinement of a contract with immutables under the forks `forks`. -/
abbrev contractRefinementOn (forks : ForkSet) (cfg : Config) (initcode : ByteArray)
    (contract : ContractDecl) : Prop :=
  contractRefinementWFOn forks trivialStorageWF noGasBound cfg initcode contract

/-- Top-level refinement of a contract with immutables, at every supported fork (Cancun
    onward). -/
abbrev contractRefinement (cfg : Config) (initcode : ByteArray) (contract : ContractDecl) : Prop :=
  contractRefinementOn supportedForks cfg initcode contract

/-- Top-level refinement of a contract with immutables, from the fork `f` onward. -/
abbrev contractRefinementFrom (f : Ethereum.Fork) (cfg : Config) (initcode : ByteArray)
    (contract : ContractDecl) : Prop :=
  contractRefinementOn (forksFrom f) cfg initcode contract

/-- Top-level refinement of a contract with immutables, at the single fork `f`. -/
abbrev contractRefinementAt (f : Ethereum.Fork) (cfg : Config) (initcode : ByteArray)
    (contract : ContractDecl) : Prop :=
  contractRefinementOn (onlyFork f) cfg initcode contract

/-- A contract refinement holds on every smaller set of forks. -/
theorem contractRefinementWFOn.mono {forks forks' : ForkSet} {wf : StorageWF}
    {gasBound : GasBound} {cfg : Config} {initcode : ByteArray} {contract : ContractDecl}
    (hsub : ∀ fork, forks' fork → forks fork)
    (h : contractRefinementWFOn forks wf gasBound cfg initcode contract) :
    contractRefinementWFOn forks' wf gasBound cfg initcode contract := by
  cases h with
  | intro runtimeCodeOf h =>
    refine .intro runtimeCodeOf fun fork hfork σ σ₀ g A I args d hdeploy hcode hcalldata hperm => ?_
    obtain ⟨imms?, hctor, hrt⟩ := h fork (hsub fork hfork) σ σ₀ g A I args d hdeploy hcode hcalldata hperm
    exact ⟨imms?, hctor, fun imms himms =>
      (hrt imms himms).mono fun f hf => ⟨hsub f hf.1, hf.2⟩⟩

/-- The general contract refinement gives the refinement on any set of forks. -/
theorem contractRefinementWF.on {forks : ForkSet} {wf : StorageWF} {gasBound : GasBound}
    {cfg : Config} {initcode : ByteArray} {contract : ContractDecl}
    (h : contractRefinementWF wf gasBound cfg initcode contract) :
    contractRefinementWFOn forks wf gasBound cfg initcode contract :=
  h.mono fun fork _ => supportedForks_mem fork

/-! ### Proving it: constructor and runtime separately -/

/-- The final immutables of a successful constructor run are well-typed (other results carry
    none). -/
def ctorImmutablesFit (contract : ContractDecl) (steleRes : ExecResult) : Prop :=
  match steleRes with
  | .returned frame _ _ => immutablesFit contract frame.immutables
  | _ => True

/-- A contract without immutables deploys well-typed immutables trivially. -/
theorem ctorImmutablesFit_noImmutables {contract : ContractDecl} {steleRes : ExecResult}
    (h : contract.immutables = []) : ctorImmutablesFit contract steleRes := by
  unfold ctorImmutablesFit; split
  · intro d hd; simp [h] at hd
  · trivial

/-- The constructor half as proved: `constructorRefinementFor`, plus that the deployed immutables
    are well-typed (discharged automatically for a contract without immutables). -/
inductive typedConstructorRefinementFor (fork : Ethereum.Fork) (cfg : Config) (contract : ContractDecl)
    (args : List Value) (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256)
    (A : Ethereum.Substate) (I : Ethereum.ExecutionEnv) (runtimeCodeOf : Store → ByteArray) :
    Prop where
  | execution {Ξ_res steleRes} :
    Ethereum.EVM.Ξ fork σ σ₀ g A I = Ξ_res →
    steleCtorExec fork cfg contract args σ σ₀ g A I steleRes →
    ctorResultEquiv Ξ_res steleRes runtimeCodeOf →
    (hfit : ctorImmutablesFit contract steleRes :=
      by exact ctorImmutablesFit_noImmutables (by rfl)) →
    typedConstructorRefinementFor fork cfg contract args σ σ₀ g A I runtimeCodeOf
  | outOfGas :
    Ethereum.EVM.Ξ fork σ σ₀ g A I = .error .OutOfGass →
    typedConstructorRefinementFor fork cfg contract args σ σ₀ g A I runtimeCodeOf

/-- `typedConstructorRefinementFor` at every deployment of `initcode` under a fork of `forks`. -/
def typedConstructorRefinementOn (forks : ForkSet) (cfg : Config) (initcode : ByteArray)
    (contract : ContractDecl) (runtimeCodeOf : Store → ByteArray) : Prop :=
  ∀ (fork : Ethereum.Fork), forks fork → ∀ (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256)
    (A : Ethereum.Substate) (I : Ethereum.ExecutionEnv) (args : List Value) (deployedInitcode : ByteArray),
    cfg.selfDeployment initcode args = .some deployedInitcode →
    I.code = deployedInitcode →
    I.calldata = .empty →
    I.perm = true →  -- unreachable otherwise, see `contractRefinementWF`
    typedConstructorRefinementFor fork cfg contract args σ σ₀ g A I runtimeCodeOf

/-- `typedConstructorRefinementOn` at every supported fork. -/
abbrev typedConstructorRefinement (cfg : Config) (initcode : ByteArray) (contract : ContractDecl)
    (runtimeCodeOf : Store → ByteArray) : Prop :=
  typedConstructorRefinementOn supportedForks cfg initcode contract runtimeCodeOf

/-- A constructor refinement holds on every smaller set of forks. -/
theorem typedConstructorRefinementOn.mono {forks forks' : ForkSet} {cfg : Config}
    {initcode : ByteArray} {contract : ContractDecl} {runtimeCodeOf : Store → ByteArray}
    (hsub : ∀ fork, forks' fork → forks fork)
    (h : typedConstructorRefinementOn forks cfg initcode contract runtimeCodeOf) :
    typedConstructorRefinementOn forks' cfg initcode contract runtimeCodeOf :=
  fun fork hfork => h fork (hsub fork hfork)

theorem typedConstructorRefinementFor.toDeployment {forks : ForkSet} {wf : StorageWF}
    {gasBound : GasBound} {cfg : Config}
    {contract : ContractDecl} {args : List Value} {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256} {A : Ethereum.Substate} {I : Ethereum.ExecutionEnv}
    {runtimeCodeOf : Store → ByteArray}
    (h : typedConstructorRefinementFor fork cfg contract args σ σ₀ g A I runtimeCodeOf)
    (hrt : ∀ imms, immutablesFit contract imms →
      runtimeRefinementWithWFOn forks wf gasBound cfg (runtimeCodeOf imms) contract
        (restrictImmutables contract imms)) :
    deploymentRefinement forks fork wf gasBound cfg contract args σ σ₀ g A I runtimeCodeOf := by
  cases h with
  | outOfGas hoog => exact ⟨none, .outOfGas hoog, fun _ h => by cases h⟩
  | @execution _ steleRes hΞ hstele hres hfit =>
      refine ⟨_, .execution hΞ hstele hres, fun imms himms => ?_⟩
      cases steleRes with
      | returned frame _ _ =>
          cases himms
          exact (hrt _ hfit).mono fun _ hf => hf.1
      | _ => cases himms

/-- **The usual proof route**: a constructor proof for some `runtimeCodeOf`, and a runtime proof
    of `runtimeCodeOf imms` for every well-typed immutables store `imms`. -/
theorem contractRefinementWF.of_runtime {forks : ForkSet} {wf : StorageWF} {gasBound : GasBound}
    {cfg : Config} {initcode : ByteArray} {contract : ContractDecl}
    {runtimeCodeOf : Store → ByteArray}
    (hctor : typedConstructorRefinementOn forks cfg initcode contract runtimeCodeOf)
    (hrt : ∀ imms, immutablesFit contract imms →
      runtimeRefinementWithWFOn forks wf gasBound cfg (runtimeCodeOf imms) contract
        (restrictImmutables contract imms)) :
    contractRefinementWFOn forks wf gasBound cfg initcode contract :=
  .intro runtimeCodeOf fun fork hfork σ σ₀ g A I args d hdeploy hcode hcalldata hperm =>
    (hctor fork hfork σ σ₀ g A I args d hdeploy hcode hcalldata hperm).toDeployment hrt

/-- `contractRefinementWF.of_runtime` without a storage precondition or gas bound. -/
theorem contractRefinement.of_runtime {forks : ForkSet} {cfg : Config} {initcode : ByteArray}
    {contract : ContractDecl} {runtimeCodeOf : Store → ByteArray}
    (hctor : typedConstructorRefinementOn forks cfg initcode contract runtimeCodeOf)
    (hrt : ∀ imms, immutablesFit contract imms →
      runtimeRefinementOn forks cfg (runtimeCodeOf imms) contract
        (restrictImmutables contract imms)) :
    contractRefinementOn forks cfg initcode contract :=
  contractRefinementWF.of_runtime hctor fun imms hfit =>
    runtimeRefinementWithWF_trivial_iff.mpr (hrt imms hfit)

/-! ### Contracts without immutables -/

/-- **Contracts without immutables**: the constructor returns `runtimeCode`, which refines the spec
    under the storage precondition `wf` and gas bound `gasBound`. -/
theorem contractRefinementWF.of_constant {forks : ForkSet} {wf : StorageWF}
    {gasBound : GasBound} {cfg : Config} {initcode runtimeCode : ByteArray}
    {contract : ContractDecl}
    (hctor : typedConstructorRefinementOn forks cfg initcode contract (fun _ => runtimeCode))
    (hrt : runtimeRefinementWithWFOn forks wf gasBound cfg runtimeCode contract)
    (himm : contract.immutables = [] := by rfl) :
    contractRefinementWFOn forks wf gasBound cfg initcode contract :=
  contractRefinementWF.of_runtime hctor fun imms _ => by
    rw [restrictImmutables_noImmutables himm]
    exact hrt

/-- **Contracts without immutables**: the constructor returns `runtimeCode`, which refines the
    spec. -/
theorem contractRefinement.of_constant {forks : ForkSet} {cfg : Config}
    {initcode runtimeCode : ByteArray} {contract : ContractDecl}
    (hctor : typedConstructorRefinementOn forks cfg initcode contract (fun _ => runtimeCode))
    (hrt : runtimeRefinementOn forks cfg runtimeCode contract)
    (himm : contract.immutables = [] := by rfl) :
    contractRefinementOn forks cfg initcode contract :=
  contractRefinementWF.of_constant hctor (runtimeRefinementWithWF_trivial_iff.mpr hrt) himm

end Stele
