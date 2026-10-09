import ABI.Encode
import ABI.Decode
import Solm.Semantics

/-!
The statement of Solm/EVM refinement, layered bottom-up:

* **Result equivalence** — `returnEquiv`/`returnDataEquiv` couple returned bytes with spec
  return values; `execResultsEquiv` / `ctorResultEquiv` couple whole execution outcomes
  (equality of final account maps, plus the return data — for constructors, the
  returned bytes must be the deployed runtime code for the constructor's final immutables).
* **Fixed-input relation** — `runtimeRefinementFor` couples one EVM execution
  (`Ethereum.EVM.Ξ`) with one Solm execution (`solmExec`) at fixed transaction inputs.
* **∀-closure** — `runtimeRefinement` (and `runtimeRefinementWithWF`, which carries a storage
  precondition and a bound on the starting gas) quantify over all inputs.
* **Top level** — the contract refinement (`contractRefinement`) composes the constructor
  (`typedConstructorRefinement`) and runtime relations through the immutables the constructor
  deploys.
-/

namespace Solm

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
  (solmRes : ExecResult) (returnConvention : ReturnConvention) : Prop where
  | success :
    evmRes = .ok (.success (σ', g', A') o) →
    solmRes = .returned _ solmState retVal →
    σ' = solmState.accountMap →
    returnDataEquiv o retVal returnConvention →
    execResultsEquiv evmRes solmRes returnConvention
  | revert :
    evmRes = .ok (.revert g o) →
    solmRes = .reverted →
    execResultsEquiv evmRes solmRes returnConvention
  -- `INVALID` (`0xFE`) refines a Solm `.reverted`; legacy solc uses it as the assert/panic failure
  -- path.  Static-mode violations have their own case below; no other EVM exception is matched.
  | invalidHalt :
    evmRes = .error .InvalidInstruction →
    solmRes = .reverted →
    execResultsEquiv evmRes solmRes returnConvention
  -- Static mode (`I.perm = false`, the contract was entered through `STATICCALL`): the EVM's
  -- `StaticModeViolation` at a forbidden opcode refines a Solm `.staticViolation`, which only a
  -- state-changing statement can produce.  A body without one (a view function) can never match
  -- an EVM static halt.
  | staticHalt :
    evmRes = .error .StaticModeViolation →
    solmRes = .staticViolation →
    execResultsEquiv evmRes solmRes returnConvention

/-- Constructor result equivalence.  On success the final account maps agree and the returned
    bytes are `runtimeCodeOf` of the immutables in the constructor's final frame. -/
inductive ctorResultEquiv
  (evmRes: Except Ethereum.EVM.ExecutionException (Ethereum.ExecutionResult (Ethereum.AccountMap × Ethereum.UInt256 × Ethereum.Substate)))
  (solmRes : ExecResult) (runtimeCodeOf : Store → ByteArray) : Prop where
  | success :
    evmRes = .ok (.success (σ', g', A') o) →
    solmRes = .returned solmFrame solmState .none →
    σ' = solmState.accountMap →
    o = runtimeCodeOf solmFrame.immutables →
    ctorResultEquiv evmRes solmRes runtimeCodeOf
  -- Twin of `success` for a ctor body ending in a bare `return` (explicit void return `some []`);
  -- kept separate so existing `.success` (fall-through `.none`) proofs are unchanged.
  | successVoidReturn :
    evmRes = .ok (.success (σ', g', A') o) →
    solmRes = .returned solmFrame solmState (some []) →
    σ' = solmState.accountMap →
    o = runtimeCodeOf solmFrame.immutables →
    ctorResultEquiv evmRes solmRes runtimeCodeOf
  | revert :
    evmRes = .ok (.revert g o) →
    solmRes = .reverted →
    ctorResultEquiv evmRes solmRes runtimeCodeOf
  -- `INVALID` (`0xFE`) refines a Solm `.reverted`, as in `execResultsEquiv.invalidHalt`.
  | invalidHalt :
    evmRes = .error .InvalidInstruction →
    solmRes = .reverted →
    ctorResultEquiv evmRes solmRes runtimeCodeOf

/-- Runtime refinement of a single message call at fixed transaction inputs: couples the EVM
    execution of the bytecode (`Ethereum.EVM.Ξ`) with the Solm execution of the spec (`solmExec`),
    both run from the given accounts, gas, substate, and environment `I` (which carries the code
    and calldata).

    Holds in exactly one of four ways:
    * `execution`: Solm dispatches and runs a transition to `solmRes`; the EVM result is
      `execResultsEquiv`-related to it under the transition's return convention.  This includes
      the static-mode case (`I.perm = false`): an EVM `StaticModeViolation` pairs with a Solm
      `.staticViolation`.
    * `noDispatch`: no Solm transition accepts the calldata, and the EVM reverts.
    * `decodingFailed`: the selector matches a transition but calldata decoding fails,
      and the EVM reverts.
    * `outOfGas`: the EVM exhausts its gas; the spec side is unconstrained.  (TODO: because
      termination is not forced, a non-terminating EVM program is equivalent to any spec.)

    `immutables` are the values the contract was deployed with (`∅` without immutables). -/
inductive runtimeRefinementFor (cfg : Config)
    (contract : ContractDecl) /- Spec -/
    (σ : Ethereum.AccountMap)
    (σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) /- contains the EVM bytecode -/
    (immutables : Store := ∅)
: Prop where
  | execution {Ξ_res solmRes returnConvention} : /- Both executions return -/
    /- Execute EVM transaction-/
    Ethereum.EVM.Ξ σ σ₀ g A I = Ξ_res →
    /- Solm transition dispatch + execution -/
    solmExec cfg contract immutables σ σ₀ g A I solmRes returnConvention →
    /- Resulting states and return must be equivalent equivalence -/
    execResultsEquiv Ξ_res solmRes returnConvention →
    runtimeRefinementFor cfg contract σ σ₀ g A I immutables
  | noDispatch : /- Dispatch fails in Solm, EVM reverts -/
    dispatchMsg contract I.calldata = .none →
    Ethereum.EVM.Ξ σ σ₀ g A I = .ok (.revert g' o) →
    runtimeRefinementFor cfg contract σ σ₀ g A I immutables
  | decodingFailed {transition transitionSig g' o} : /- Decoding fails in Solm, EVM reverts -/
    selectorDispatchMsg contract I.calldata = .some transition →
    transitionSig = transitionSignature transition →
    decodeCalldataWithMode cfg.abiDecodeMode (transition.params.map Param.name)
      transitionSig.paramTypes I.calldata = .none →
    Ethereum.EVM.Ξ σ σ₀ g A I = .ok (.revert g' o) →
    runtimeRefinementFor cfg contract σ σ₀ g A I immutables
  | outOfGas : /- EVM runs out of gas -/
    /- TODO: non-terminating EVM programs are currently equivalent to any spec -/
    Ethereum.EVM.Ξ σ σ₀ g A I = .error .OutOfGass →
    runtimeRefinementFor cfg contract σ σ₀ g A I immutables

abbrev StorageWF := Ethereum.AccountMap → Ethereum.ExecutionEnv → Prop

/-- Trivial storage well-formedness predicate for contracts whose correctness is unconditional. -/
def trivialStorageWF : StorageWF := fun _ _ => True

/-- A bound on the gas a runtime call starts with (e.g. `fun g => g.toNat < 2^64`). -/
abbrev GasBound := Ethereum.UInt256 → Prop

/-- No gas bound: refinement holds for every amount of gas. -/
def noGasBound : GasBound := fun _ => True

/-- Runtime refinement under a contract-specific storage well-formedness precondition and a gas
bound.

This is the same runtime relation as `runtimeRefinement`, except it only covers calls where
`wf σ I` holds for the EVM-side initial storage and execution environment, and `gasBound g`
holds for the starting gas.  Both relations cover either permission mode. -/
inductive runtimeRefinementWithWF (wf : StorageWF) (gasBound : GasBound) (cfg : Config)
    (bytecode : ByteArray) (contract : ContractDecl) (immutables : Store := ∅) : Prop where
  | intro :
    (∀ (σ : Ethereum.AccountMap)
      (σ₀ : Ethereum.AccountMap)
      (g : Ethereum.UInt256)
      (A : Ethereum.Substate)
      (I : Ethereum.ExecutionEnv),
    I.code = bytecode →
    I.calldata.size < Ethereum.UInt256.size →
    wf σ I →
    gasBound g →
    runtimeRefinementFor cfg contract σ σ₀ g A I immutables
    ) →
    runtimeRefinementWithWF wf gasBound cfg bytecode contract immutables

/-- Runtime refinement of `bytecode` with the spec run with the deployed `immutables`, in either
    permission mode.  When entered through `STATICCALL`, the EVM halts at the first forbidden
    opcode and Solm halts at a state-changing statement, paired by `execResultsEquiv.staticHalt`. -/
inductive runtimeRefinement (cfg : Config) (bytecode : ByteArray) (contract : ContractDecl)
    (immutables : Store := ∅) : Prop where
  | intro :
    (∀ (σ : Ethereum.AccountMap)
      (σ₀ : Ethereum.AccountMap)
      (g : Ethereum.UInt256)
      (A : Ethereum.Substate)
      (I : Ethereum.ExecutionEnv),
    I.code = bytecode →
    I.calldata.size < Ethereum.UInt256.size →
    runtimeRefinementFor cfg contract σ σ₀ g A I immutables
    ) →
    runtimeRefinement cfg bytecode contract immutables

/-- Sanity check: the two definitions agree for the trivial storage predicate and no gas bound. -/
theorem runtimeRefinementWithWF_trivial_iff {cfg : Config} {bytecode : ByteArray}
    {contract : ContractDecl} {immutables : Store} :
    runtimeRefinementWithWF trivialStorageWF noGasBound cfg bytecode contract immutables ↔
      runtimeRefinement cfg bytecode contract immutables := by
  constructor
  · intro h
    cases h with
    | intro hrun =>
        refine runtimeRefinement.intro ?_
        intro σ σ₀ g A I hcode hsize
        exact hrun σ σ₀ g A I hcode hsize trivial trivial
  · intro h
    cases h with
    | intro hrun =>
        refine runtimeRefinementWithWF.intro ?_
        intro σ σ₀ g A I hcode hsize _hwf _hgas
        exact hrun σ σ₀ g A I hcode hsize

/-! ## Contract refinement

A contract with immutables is deployed by running its constructor, and the code that constructor
returns depends on the immutables it set: the EVM runs that code from then on, and the spec's
runtime must run with those same immutables.

`contractRefinement` says it per deployment (`deploymentRefinement`): the EVM deployment run is
matched by a Solm constructor run (`constructorRefinementFor`), which exposes the immutables it
deployed, or `none` if it did not succeed; the code deployed for those immutables then refines the
spec run with them (`runtimeRefinementWithWF`).  One `runtimeCodeOf` is shared by all deployments,
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

/-- Deployment refinement at fixed deployment inputs: the constructor refines, and whatever it
    deployed refines at runtime. -/
def deploymentRefinement (wf : StorageWF) (gasBound : GasBound) (cfg : Config)
    (contract : ContractDecl)
    (args : List Value) (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256)
    (A : Ethereum.Substate) (I : Ethereum.ExecutionEnv) (runtimeCodeOf : Store → ByteArray) :
    Prop :=
  ∃ imms?, constructorRefinementFor cfg contract args σ σ₀ g A I runtimeCodeOf imms? ∧
    ∀ imms, imms? = some imms →
      runtimeRefinementWithWF wf gasBound cfg (runtimeCodeOf imms) contract
        (restrictImmutables contract imms)

/-- Top-level refinement of a contract with immutables, under a storage well-formedness
    precondition and a gas bound for runtime calls: `deploymentRefinement` at every deployment of
    `initcode` (the deployment inputs of `typedConstructorRefinement`), for one `runtimeCodeOf`
    shared by all of them. -/
inductive contractRefinementWF (wf : StorageWF) (gasBound : GasBound) (cfg : Config)
    (initcode : ByteArray) (contract : ContractDecl) : Prop where
  | intro (runtimeCodeOf : Store → ByteArray) :
    (∀ (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
      (I : Ethereum.ExecutionEnv) (args : List Value) (deployedInitcode : ByteArray),
      cfg.selfDeployment initcode args = .some deployedInitcode →
      I.code = deployedInitcode →
      I.calldata = .empty →
      -- Init code never runs in static mode: the transaction entry `Υ` passes `true` to `Λ`, and
      -- `CREATE`/`CREATE2` are themselves forbidden under `perm = false`, so `Λ` is never reached
      -- with it.  The hypothesis excludes nothing reachable.
      I.perm = true →
      deploymentRefinement wf gasBound cfg contract args σ σ₀ g A I runtimeCodeOf) →
    contractRefinementWF wf gasBound cfg initcode contract

/-- Top-level refinement of a contract with immutables. -/
abbrev contractRefinement (cfg : Config) (initcode : ByteArray) (contract : ContractDecl) : Prop :=
  contractRefinementWF trivialStorageWF noGasBound cfg initcode contract

/-! ### Proving it: constructor and runtime separately -/

/-- The final immutables of a successful constructor run are well-typed (other results carry
    none). -/
def ctorImmutablesFit (contract : ContractDecl) (solmRes : ExecResult) : Prop :=
  match solmRes with
  | .returned frame _ _ => immutablesFit contract frame.immutables
  | _ => True

/-- A contract without immutables deploys well-typed immutables trivially. -/
theorem ctorImmutablesFit_noImmutables {contract : ContractDecl} {solmRes : ExecResult}
    (h : contract.immutables = []) : ctorImmutablesFit contract solmRes := by
  unfold ctorImmutablesFit; split
  · intro d hd; simp [h] at hd
  · trivial

/-- The constructor half as proved: `constructorRefinementFor`, plus that the deployed immutables
    are well-typed (discharged automatically for a contract without immutables). -/
inductive typedConstructorRefinementFor (cfg : Config) (contract : ContractDecl)
    (args : List Value) (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256)
    (A : Ethereum.Substate) (I : Ethereum.ExecutionEnv) (runtimeCodeOf : Store → ByteArray) :
    Prop where
  | execution {Ξ_res solmRes} :
    Ethereum.EVM.Ξ σ σ₀ g A I = Ξ_res →
    solmCtorExec cfg contract args σ σ₀ g A I solmRes →
    ctorResultEquiv Ξ_res solmRes runtimeCodeOf →
    (hfit : ctorImmutablesFit contract solmRes :=
      by exact ctorImmutablesFit_noImmutables (by rfl)) →
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
    I.perm = true →  -- unreachable otherwise, see `contractRefinementWF`
    typedConstructorRefinementFor cfg contract args σ σ₀ g A I runtimeCodeOf

theorem typedConstructorRefinementFor.toDeployment {wf : StorageWF} {gasBound : GasBound}
    {cfg : Config}
    {contract : ContractDecl} {args : List Value} {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256} {A : Ethereum.Substate} {I : Ethereum.ExecutionEnv}
    {runtimeCodeOf : Store → ByteArray}
    (h : typedConstructorRefinementFor cfg contract args σ σ₀ g A I runtimeCodeOf)
    (hrt : ∀ imms, immutablesFit contract imms →
      runtimeRefinementWithWF wf gasBound cfg (runtimeCodeOf imms) contract
        (restrictImmutables contract imms)) :
    deploymentRefinement wf gasBound cfg contract args σ σ₀ g A I runtimeCodeOf := by
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
theorem contractRefinementWF.of_runtime {wf : StorageWF} {gasBound : GasBound} {cfg : Config}
    {initcode : ByteArray} {contract : ContractDecl} {runtimeCodeOf : Store → ByteArray}
    (hctor : typedConstructorRefinement cfg initcode contract runtimeCodeOf)
    (hrt : ∀ imms, immutablesFit contract imms →
      runtimeRefinementWithWF wf gasBound cfg (runtimeCodeOf imms) contract
        (restrictImmutables contract imms)) :
    contractRefinementWF wf gasBound cfg initcode contract :=
  .intro runtimeCodeOf fun σ σ₀ g A I args d hdeploy hcode hcalldata hperm =>
    (hctor σ σ₀ g A I args d hdeploy hcode hcalldata hperm).toDeployment hrt

/-- `contractRefinementWF.of_runtime` without a storage precondition or gas bound. -/
theorem contractRefinement.of_runtime {cfg : Config} {initcode : ByteArray}
    {contract : ContractDecl} {runtimeCodeOf : Store → ByteArray}
    (hctor : typedConstructorRefinement cfg initcode contract runtimeCodeOf)
    (hrt : ∀ imms, immutablesFit contract imms →
      runtimeRefinement cfg (runtimeCodeOf imms) contract (restrictImmutables contract imms)) :
    contractRefinement cfg initcode contract :=
  contractRefinementWF.of_runtime hctor fun imms hfit =>
    runtimeRefinementWithWF_trivial_iff.mpr (hrt imms hfit)

/-! ### Contracts without immutables -/

/-- **Contracts without immutables**: the constructor returns `runtimeCode`, which refines the spec
    under the storage precondition `wf` and gas bound `gasBound`. -/
theorem contractRefinementWF.of_constant {wf : StorageWF} {gasBound : GasBound} {cfg : Config}
    {initcode runtimeCode : ByteArray} {contract : ContractDecl}
    (hctor : typedConstructorRefinement cfg initcode contract (fun _ => runtimeCode))
    (hrt : runtimeRefinementWithWF wf gasBound cfg runtimeCode contract)
    (himm : contract.immutables = [] := by rfl) :
    contractRefinementWF wf gasBound cfg initcode contract :=
  contractRefinementWF.of_runtime hctor fun imms _ => by
    rw [restrictImmutables_noImmutables himm]
    exact hrt

/-- **Contracts without immutables**: the constructor returns `runtimeCode`, which refines the
    spec. -/
theorem contractRefinement.of_constant {cfg : Config} {initcode runtimeCode : ByteArray}
    {contract : ContractDecl}
    (hctor : typedConstructorRefinement cfg initcode contract (fun _ => runtimeCode))
    (hrt : runtimeRefinement cfg runtimeCode contract)
    (himm : contract.immutables = [] := by rfl) :
    contractRefinement cfg initcode contract :=
  contractRefinementWF.of_constant hctor (runtimeRefinementWithWF_trivial_iff.mpr hrt) himm

end Solm
