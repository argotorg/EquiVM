import ABI.Encode
import ABI.Decode
import Solm.Semantics

/-!
The statement of Solm/EVM refinement, layered bottom-up:

* **Result equivalence** — `returnEquiv`/`returnDataEquiv` couple returned bytes with spec
  return values; `execResultsEquiv` / `ctorResultEquiv` couple whole execution outcomes
  (equality of final account maps, plus the return data — for constructors, the
  returned bytes must be the deployed runtime code for the constructor's final immutables).
* **Fixed-input relations** — `runtimeEquivalenceFor` / `constructorEquivalenceFor` couple one
  EVM execution (`Ethereum.EVM.Ξ`) with one Solm execution (`solmExec` / `solmCtorExec`) at
  fixed transaction inputs.
* **∀-closures** — `runtimeEquivalence` (and the precondition-carrying
  `runtimeEquivalenceWithWF`) and `constructorEquivalence` quantify over all inputs.
* **Top level** — `contractEquivalence` = constructor + runtime, for some map from immutable
  values to deployed code; `contractEquivalence.deployed_refines` states the consequence:
  whatever runtime a successful deployment returns refines the spec run with the immutables that
  constructor run produced.

Immutables are part of the Solm semantics (`Frame.immutables`), so the spec is one
`ContractDecl`.  How the compiler embeds them in the code is not: the relation quantifies over
`runtimeCodeOf : Store → ByteArray` and only ties it to the compiler's `runtimeCode`, the code for
the zero immutables.

The `*With` family at the bottom of the file is the legacy encoding of immutables as constructor
locals, kept until the benchmarks using it migrate.
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
  -- path.  It is the ONLY EVM exception matched here — any other error leaves `execResultsEquiv`
  -- unmatchable, so a real crash never equates with a revert.
  | invalidHalt :
    evmRes = .error .InvalidInstruction →
    solmRes = .reverted →
    execResultsEquiv evmRes solmRes returnConvention

/-- Whether `immutables` gives every declared immutable a value of its declared type. -/
def immutablesFit (contract : ContractDecl) (immutables : Store) : Bool :=
  contract.immutables.all fun d =>
    match immutables.get? d.name with
    | some v => elemValueFits d.ty v
    | none => false

/-- The immutables a deployed contract runs with: the declared ones only. -/
def restrictImmutables (contract : ContractDecl) (immutables : Store) : Store :=
  contract.immutables.foldl (fun acc d =>
    match immutables.get? d.name with
    | some v => acc.insert d.name v
    | none => acc) ∅

/-- The runtime code deployed for the immutables a constructor run leaves, under the compiler's
    `runtimeCodeOf`; `none` if they are not well typed. -/
def deployedRuntime? (contract : ContractDecl) (runtimeCodeOf : Store → ByteArray)
    (immutables : Store) : Option ByteArray :=
  if immutablesFit contract immutables then some (runtimeCodeOf immutables) else none

theorem deployedRuntime?_noImmutables {contract : ContractDecl} {runtimeCode : ByteArray}
    {immutables : Store} (h : contract.immutables = []) :
    deployedRuntime? contract (fun _ => runtimeCode) immutables = some runtimeCode := by
  simp [deployedRuntime?, immutablesFit, h]

theorem restrictImmutables_noImmutables {contract : ContractDecl} {immutables : Store}
    (h : contract.immutables = []) : restrictImmutables contract immutables = ∅ := by
  simp [restrictImmutables, h]

/-- Constructor result equivalence.  `deployed imms` is the runtime code deployed for the
    immutables `imms` (`deployedRuntime?`); on success the EVM must return exactly the code for the
    immutables in the constructor's final frame. -/
inductive ctorResultEquiv
  (evmRes: Except Ethereum.EVM.ExecutionException (Ethereum.ExecutionResult (Ethereum.AccountMap × Ethereum.UInt256 × Ethereum.Substate)))
  (solmRes : ExecResult) (deployed : Store → Option ByteArray) : Prop where
  | success :
    evmRes = .ok (.success (σ', g', A') o) →
    solmRes = .returned solmFrame solmState .none →
    σ' = solmState.accountMap →
    deployed solmFrame.immutables = some o →
    ctorResultEquiv evmRes solmRes deployed
  -- Twin of `success` for a ctor body ending in a bare `return` (explicit void return `some []`);
  -- kept separate so existing `.success` (fall-through `.none`) proofs are unchanged.
  | successVoidReturn :
    evmRes = .ok (.success (σ', g', A') o) →
    solmRes = .returned solmFrame solmState (some []) →
    σ' = solmState.accountMap →
    deployed solmFrame.immutables = some o →
    ctorResultEquiv evmRes solmRes deployed
  | revert :
    evmRes = .ok (.revert g o) →
    solmRes = .reverted →
    ctorResultEquiv evmRes solmRes deployed
  -- `INVALID` (`0xFE`) refines a Solm `.reverted`, as in `execResultsEquiv.invalidHalt`.
  | invalidHalt :
    evmRes = .error .InvalidInstruction →
    solmRes = .reverted →
    ctorResultEquiv evmRes solmRes deployed

/-- Runtime equivalence of a single message call at fixed transaction inputs: couples the EVM
    execution of the bytecode (`Ethereum.EVM.Ξ`) with the Solm execution of the spec (`solmExec`),
    both run from the given accounts, gas, substate, and environment `I` (which carries the code
    and calldata).

    Holds in exactly one of four ways:
    * `execution`: Solm dispatches and runs a transition to `solmRes`; the EVM result is
      `execResultsEquiv`-related to it under the transition's return convention.
    * `noDispatch`: no Solm transition accepts the calldata, and the EVM reverts.
    * `decodingFailed`: the selector matches a transition but calldata decoding fails,
      and the EVM reverts.
    * `outOfGas`: the EVM exhausts its gas; the spec side is unconstrained.  (TODO: because
      termination is not forced, a non-terminating EVM program is equivalent to any spec.)

    `immutables` are the values the contract was deployed with (`∅` without immutables). -/
inductive runtimeEquivalenceFor (cfg : Config)
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
    runtimeEquivalenceFor cfg contract σ σ₀ g A I immutables
  | noDispatch : /- Dispatch fails in Solm, EVM reverts -/
    dispatchMsg contract I.calldata = .none →
    Ethereum.EVM.Ξ σ σ₀ g A I = .ok (.revert g' o) →
    runtimeEquivalenceFor cfg contract σ σ₀ g A I immutables
  | decodingFailed {transition transitionSig g' o} : /- Decoding fails in Solm, EVM reverts -/
    selectorDispatchMsg contract I.calldata = .some transition →
    transitionSig = transitionSignature transition →
    decodeCalldataWithMode cfg.abiDecodeMode (transition.params.map Param.name)
      transitionSig.paramTypes I.calldata = .none →
    Ethereum.EVM.Ξ σ σ₀ g A I = .ok (.revert g' o) →
    runtimeEquivalenceFor cfg contract σ σ₀ g A I immutables
  | outOfGas : /- EVM runs out of gas -/
    /- TODO: non-terminating EVM programs are currently equivalent to any spec -/
    Ethereum.EVM.Ξ σ σ₀ g A I = .error .OutOfGass →
    runtimeEquivalenceFor cfg contract σ σ₀ g A I immutables

abbrev StorageWF := Ethereum.AccountMap → Ethereum.ExecutionEnv → Prop

/-- Trivial storage well-formedness predicate for contracts whose correctness is unconditional. -/
def trivialStorageWF : StorageWF := fun _ _ => True

/-- Runtime equivalence under a contract-specific storage well-formedness precondition.

This is the same runtime relation as `runtimeEquivalence`, except the caller must additionally
prove `wf σ I` for the EVM-side initial storage and execution environment.  The old
unconditional relation remains available as before; new contracts that need reachable-state or
layout invariants can use this parameterized entry point. -/
inductive runtimeEquivalenceWithWF (wf : StorageWF) (cfg : Config) (bytecode : ByteArray)
    (contract : ContractDecl) (immutables : Store := ∅) : Prop where
  | intro :
    (∀ (σ : Ethereum.AccountMap)
      (σ₀ : Ethereum.AccountMap)
      (g : Ethereum.UInt256)
      (A : Ethereum.Substate)
      (I : Ethereum.ExecutionEnv),
    I.code = bytecode →
    I.calldata.size < Ethereum.UInt256.size →
    I.perm = true →
    wf σ I →
    runtimeEquivalenceFor cfg contract σ σ₀ g A I immutables
    ) →
    runtimeEquivalenceWithWF wf cfg bytecode contract immutables

/-- Runtime equivalence of `bytecode` with the spec run with the deployed `immutables`. -/
inductive runtimeEquivalence (cfg : Config) (bytecode : ByteArray) (contract : ContractDecl)
    (immutables : Store := ∅) : Prop where
  | intro :
    (∀ (σ : Ethereum.AccountMap)
      (σ₀ : Ethereum.AccountMap)
      (g : Ethereum.UInt256)
      (A : Ethereum.Substate)
      (I : Ethereum.ExecutionEnv),
    I.code = bytecode →
    I.calldata.size < Ethereum.UInt256.size →
    -- A top-level message call is never executed in static (read-only) mode: the EVM's
    -- transaction entry `Υ` sets the permission flag, and Solm's external-call rule likewise
    -- hardcodes a writable sub-call.  Required for contracts that write storage (`SSTORE` aborts
    -- under `perm = false`, whereas Solm's `.assign` is permission-free); benign for pure ones.
    I.perm = true →
    runtimeEquivalenceFor cfg contract σ σ₀ g A I immutables
    ) →
    runtimeEquivalence cfg bytecode contract immutables

/-- Sanity check: the two definitions agree for the trivial storage well-formedness predicate. -/
theorem runtimeEquivalenceWithWF_trivial_iff {cfg : Config} {bytecode : ByteArray}
    {contract : ContractDecl} {immutables : Store} :
    runtimeEquivalenceWithWF trivialStorageWF cfg bytecode contract immutables ↔
      runtimeEquivalence cfg bytecode contract immutables := by
  constructor
  · intro h
    cases h with
    | intro hrun =>
        refine runtimeEquivalence.intro ?_
        intro σ σ₀ g A I hcode hsize hperm
        exact hrun σ σ₀ g A I hcode hsize hperm trivial
  · intro h
    cases h with
    | intro hrun =>
        refine runtimeEquivalenceWithWF.intro ?_
        intro σ σ₀ g A I hcode hsize hperm _hwf
        exact hrun σ σ₀ g A I hcode hsize hperm


/-- Constructor (deployment) equivalence at fixed transaction inputs: couples the EVM
    execution of the init code (`Ethereum.EVM.Ξ`, with `I.code` the deployed initcode and empty
    calldata) with the Solm execution of the constructor body (`solmCtorExec`) on the argument
    values `args`.  Unlike the runtime relation there is no dispatch or calldata-decoding case:
    creation calls are compiler-generated and trusted, so the *spec side* fixes `args`, and the
    ∀-closure (`constructorEquivalence`) ties them to the deployed initcode via
    `cfg.selfDeployment`.

    Holds in one of two ways:
    * `execution` — the Solm constructor runs to `solmRes`; the EVM result is
      `ctorResultEquiv`-related: on success the final account maps are equal
      **and the EVM's returned bytes are exactly `runtimeCodeOf` of the constructor's final
      immutables** (`deployedRuntime?`; by default the constant `runtimeCode`, as for a contract
      without immutables); reverts and `INVALID` halts pair with a Solm revert.
    * `outOfGas` — the EVM exhausts its gas; the spec side is unconstrained. (same
      termination caveat as `runtimeEquivalenceFor`) -/

inductive constructorEquivalenceFor (cfg : Config)
    (contract : ContractDecl) /- Spec -/
    (args : List Value)
    (σ : Ethereum.AccountMap)
    (σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) /- contains the EVM bytecode -/
    (runtimeCode : ByteArray)
    (runtimeCodeOf : Store → ByteArray := fun _ => runtimeCode)
: Prop where
  | execution {Ξ_res solmRes} : /- Both executions return -/
    /- Execute EVM transaction-/
    Ethereum.EVM.Ξ σ σ₀ g A I = Ξ_res →
    /- Solm constructor + execution -/
    solmCtorExec cfg contract args σ σ₀ g A I solmRes →
    /- Resulting states must be equivalent, and the EVM return bytes should equal the runtime code -/
    ctorResultEquiv Ξ_res solmRes (deployedRuntime? contract runtimeCodeOf) →
    constructorEquivalenceFor cfg contract args σ σ₀ g A I runtimeCode runtimeCodeOf
  | outOfGas : /- EVM runs out of gas -/
    /- TODO: non-terminating EVM programs are currently equivalent to any spec -/
    Ethereum.EVM.Ξ σ σ₀ g A I = .error .OutOfGass →
    constructorEquivalenceFor cfg contract args σ σ₀ g A I runtimeCode runtimeCodeOf


inductive constructorEquivalence (cfg : Config) (initcode : ByteArray) (contract : ContractDecl)
    (runtimeCode : ByteArray) (runtimeCodeOf : Store → ByteArray := fun _ => runtimeCode) :
    Prop where
  | intro :
    (∀ (σ : Ethereum.AccountMap)
      (σ₀ : Ethereum.AccountMap)
      (g : Ethereum.UInt256)
      (A : Ethereum.Substate)
      (I : Ethereum.ExecutionEnv)
      (args : List Value)
      (deployedInitcode : ByteArray),
    -- This should handle creating the initcode ++ arguments,
    -- and also enforce that we are only checking equivalence for valid argument values.
    -- We do not need to check for arbitraty given values, because the Solidity compiler
    -- does not perform the same ABI decoding checks as for message calldata. The reason behind
    -- this is that create calls are generated by the compiler itself, and so they are trusted.
    -- Thus, we have the opposite situation from runtime messages, where the Solm spec
    -- defines the arguments to check, instead of checking for arbitrary bytearray inputs.
    cfg.selfDeployment initcode args = .some deployedInitcode →
    I.code = deployedInitcode →
    I.calldata = .empty →
    -- A top-level message call is never executed in static (read-only) mode: the EVM's
    -- transaction entry `Υ` sets the permission flag, and Solm's external-call rule likewise
    -- hardcodes a writable sub-call.  Required for contracts that write storage (`SSTORE` aborts
    -- under `perm = false`, whereas Solm's `.assign` is permission-free); benign for pure ones.
    I.perm = true →
    -- Every successful execution path returns the runtime code for its final immutables
    constructorEquivalenceFor cfg contract args σ σ₀ g A I runtimeCode runtimeCodeOf
    ) →
    constructorEquivalence cfg initcode contract runtimeCode runtimeCodeOf

/-- Runtime equivalence of every runtime the constructor could deploy: for each well-typed
    assignment of the immutables, `runtimeCodeOf` of it refines the spec run with it. -/
def deployedRuntimeEquivalence (cfg : Config) (contract : ContractDecl)
    (runtimeCodeOf : Store → ByteArray) : Prop :=
  ∀ immutables, immutablesFit contract immutables = true →
    runtimeEquivalence cfg (runtimeCodeOf immutables) contract
      (restrictImmutables contract immutables)

/-- `deployedRuntimeEquivalence` under a storage well-formedness precondition. -/
def deployedRuntimeEquivalenceWithWF (wf : StorageWF) (cfg : Config) (contract : ContractDecl)
    (runtimeCodeOf : Store → ByteArray) : Prop :=
  ∀ immutables, immutablesFit contract immutables = true →
    runtimeEquivalenceWithWF wf cfg (runtimeCodeOf immutables) contract
      (restrictImmutables contract immutables)

/-- Without immutables the deployed runtime is `runtimeCode`, run with no immutables. -/
theorem deployedRuntimeEquivalence.ofNoImmutables {cfg : Config} {runtimeCode : ByteArray}
    {contract : ContractDecl} (himm : contract.immutables = [])
    (h : runtimeEquivalence cfg runtimeCode contract) :
    deployedRuntimeEquivalence cfg contract (fun _ => runtimeCode) := by
  intro immutables _
  rw [restrictImmutables_noImmutables himm]
  exact h

theorem deployedRuntimeEquivalenceWithWF.ofNoImmutables {wf : StorageWF} {cfg : Config}
    {runtimeCode : ByteArray} {contract : ContractDecl} (himm : contract.immutables = [])
    (h : runtimeEquivalenceWithWF wf cfg runtimeCode contract) :
    deployedRuntimeEquivalenceWithWF wf cfg contract (fun _ => runtimeCode) := by
  intro immutables _
  rw [restrictImmutables_noImmutables himm]
  exact h

-- Technically could give only initcode and derive runtime code from it, but lets be explicit.
-- Note: right now we are only comparing code execution i.e. EVM.Ξ with solmExec.
-- We do not have a model of message calls (Θ) for the spec (which would handle balance transfer for example)
-- If it were implemented however it would likely exactly mirror the EVM version except for calling solmExec
-- instead of EVM.Ξ, so on the equivalence checking level it is uninteresting

/-- Top-level contract equivalence.  The map `runtimeCodeOf` from immutable values to deployed
    code is existentially quantified, so the spec is not tied to one encoding of immutables; it
    must give the compiler's `runtimeCode` for the zero immutables (solc's runtime template has
    zeros where the immutables go).  Contracts without immutables use `contractEquivalence.intro`. -/
inductive contractEquivalence (cfg : Config) (initcode : EVM.Bytes) (runtimeCode : EVM.Bytes)
    (contract : ContractDecl) : Prop where
  | mk (runtimeCodeOf : Store → ByteArray) :
    runtimeCodeOf (initialImmutables contract) = runtimeCode →
    constructorEquivalence cfg initcode contract runtimeCode runtimeCodeOf →
    deployedRuntimeEquivalence cfg contract runtimeCodeOf →
    contractEquivalence cfg initcode runtimeCode contract

inductive contractEquivalenceWF (wf : StorageWF) (cfg : Config) (initcode : EVM.Bytes)
    (runtimeCode : EVM.Bytes) (contract : ContractDecl) : Prop where
  | mk (runtimeCodeOf : Store → ByteArray) :
    runtimeCodeOf (initialImmutables contract) = runtimeCode →
    constructorEquivalence cfg initcode contract runtimeCode runtimeCodeOf →
    deployedRuntimeEquivalenceWithWF wf cfg contract runtimeCodeOf →
    contractEquivalenceWF wf cfg initcode runtimeCode contract

/-- Contract equivalence for a contract without immutables: the constructor returns exactly
    `runtimeCode`, which refines the spec. -/
theorem contractEquivalence.intro {cfg : Config} {initcode runtimeCode : EVM.Bytes}
    {contract : ContractDecl}
    (hctor : constructorEquivalence cfg initcode contract runtimeCode)
    (hrt : runtimeEquivalence cfg runtimeCode contract)
    (himm : contract.immutables = [] := by rfl) :
    contractEquivalence cfg initcode runtimeCode contract :=
  .mk (fun _ => runtimeCode) rfl hctor (.ofNoImmutables himm hrt)

theorem contractEquivalenceWF.intro {wf : StorageWF} {cfg : Config}
    {initcode runtimeCode : EVM.Bytes} {contract : ContractDecl}
    (hctor : constructorEquivalence cfg initcode contract runtimeCode)
    (hrt : runtimeEquivalenceWithWF wf cfg runtimeCode contract)
    (himm : contract.immutables = [] := by rfl) :
    contractEquivalenceWF wf cfg initcode runtimeCode contract :=
  .mk (fun _ => runtimeCode) rfl hctor (.ofNoImmutables himm hrt)

/-- A successful EVM deployment at fixed inputs, returning runtime code `o` with final accounts
    `σ'`, is matched by a successful Solm constructor run with the same final accounts, and `o`
    satisfies `runtimeOk` for the immutables that run left. -/
def deploymentRefines (cfg : Config) (contract : ContractDecl) (args : List Value)
    (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) (σ' : Ethereum.AccountMap) (o : ByteArray)
    (runtimeOk : ByteArray → Store → Prop) : Prop :=
  ∃ solmFrame solmState ret,
    solmCtorExec cfg contract args σ σ₀ g A I (.returned solmFrame solmState ret) ∧
    σ' = solmState.accountMap ∧
    runtimeOk o (restrictImmutables contract solmFrame.immutables)

private theorem deployedRuntime?_runtimeOk {contract : ContractDecl}
    {runtimeCodeOf : Store → ByteArray} {runtimeOk : ByteArray → Store → Prop}
    (hrt : ∀ immutables, immutablesFit contract immutables = true →
      runtimeOk (runtimeCodeOf immutables) (restrictImmutables contract immutables))
    {immutables : Store} {o : ByteArray}
    (h : deployedRuntime? contract runtimeCodeOf immutables = some o) :
    runtimeOk o (restrictImmutables contract immutables) := by
  unfold deployedRuntime? at h
  split at h
  · cases h; exact hrt _ (by assumption)
  · cases h

private theorem deploymentRefines_of_ctor {cfg : Config} {contract : ContractDecl}
    {args : List Value} {σ σ₀ : Ethereum.AccountMap} {g : Ethereum.UInt256}
    {A : Ethereum.Substate} {I : Ethereum.ExecutionEnv} {runtimeCode : ByteArray}
    {runtimeCodeOf : Store → ByteArray} {runtimeOk : ByteArray → Store → Prop}
    (hrt : ∀ immutables, immutablesFit contract immutables = true →
      runtimeOk (runtimeCodeOf immutables) (restrictImmutables contract immutables))
    (hctor : constructorEquivalenceFor cfg contract args σ σ₀ g A I runtimeCode runtimeCodeOf)
    {σ' : Ethereum.AccountMap} {g' : Ethereum.UInt256} {A' : Ethereum.Substate} {o : ByteArray}
    (hΞ : Ethereum.EVM.Ξ σ σ₀ g A I = .ok (.success (σ', g', A') o)) :
    deploymentRefines cfg contract args σ σ₀ g A I σ' o runtimeOk := by
  cases hctor with
  | outOfGas hoog => rw [hΞ] at hoog; cases hoog
  | execution hres hsolm hequiv =>
      subst hres
      cases hequiv with
      | success hevm hsolmRes hσ hcode =>
          rw [hΞ] at hevm; cases hevm; subst hsolmRes
          exact ⟨_, _, _, hsolm, hσ, deployedRuntime?_runtimeOk hrt hcode⟩
      | successVoidReturn hevm hsolmRes hσ hcode =>
          rw [hΞ] at hevm; cases hevm; subst hsolmRes
          exact ⟨_, _, _, hsolm, hσ, deployedRuntime?_runtimeOk hrt hcode⟩
      | revert hevm _ => rw [hΞ] at hevm; cases hevm
      | invalidHalt hevm _ => rw [hΞ] at hevm; cases hevm

/-- **Deployment refinement.**  Whatever runtime code a successful deployment returns refines the
    spec run with the immutables its constructor produced. -/
theorem contractEquivalence.deployed_refines {cfg : Config} {initcode runtimeCode : EVM.Bytes}
    {contract : ContractDecl} (h : contractEquivalence cfg initcode runtimeCode contract)
    {σ σ₀ : Ethereum.AccountMap} {g : Ethereum.UInt256} {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv} {args : List Value} {deployedInitcode : ByteArray}
    (hdeploy : cfg.selfDeployment initcode args = .some deployedInitcode)
    (hcode : I.code = deployedInitcode) (hcalldata : I.calldata = .empty) (hperm : I.perm = true)
    {σ' : Ethereum.AccountMap} {g' : Ethereum.UInt256} {A' : Ethereum.Substate} {o : ByteArray}
    (hΞ : Ethereum.EVM.Ξ σ σ₀ g A I = .ok (.success (σ', g', A') o)) :
    deploymentRefines cfg contract args σ σ₀ g A I σ' o
      (runtimeEquivalence cfg · contract ·) := by
  obtain ⟨_, _, ⟨hctor⟩, hrt⟩ := h
  exact deploymentRefines_of_ctor (runtimeOk := (runtimeEquivalence cfg · contract ·)) hrt
    (hctor σ σ₀ g A I args deployedInitcode hdeploy hcode hcalldata hperm) hΞ

theorem contractEquivalenceWF.deployed_refines {wf : StorageWF} {cfg : Config}
    {initcode runtimeCode : EVM.Bytes} {contract : ContractDecl}
    (h : contractEquivalenceWF wf cfg initcode runtimeCode contract)
    {σ σ₀ : Ethereum.AccountMap} {g : Ethereum.UInt256} {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv} {args : List Value} {deployedInitcode : ByteArray}
    (hdeploy : cfg.selfDeployment initcode args = .some deployedInitcode)
    (hcode : I.code = deployedInitcode) (hcalldata : I.calldata = .empty) (hperm : I.perm = true)
    {σ' : Ethereum.AccountMap} {g' : Ethereum.UInt256} {A' : Ethereum.Substate} {o : ByteArray}
    (hΞ : Ethereum.EVM.Ξ σ σ₀ g A I = .ok (.success (σ', g', A') o)) :
    deploymentRefines cfg contract args σ σ₀ g A I σ' o
      (runtimeEquivalenceWithWF wf cfg · contract ·) := by
  obtain ⟨_, _, ⟨hctor⟩, hrt⟩ := h
  exact deploymentRefines_of_ctor (runtimeOk := (runtimeEquivalenceWithWF wf cfg · contract ·))
    hrt
    (hctor σ σ₀ g A I args deployedInitcode hdeploy hcode hcalldata hperm) hΞ

/-! ## Legacy: immutables as constructor locals

Superseded by `Frame.immutables` and `contractEquivalence`; kept until the benchmarks that encode
immutables this way migrate.

The runtime code a constructor returns may depend on the immutable values the spec constructor binds
as locals (convention: `letDecl "imm_<name>" …`).  These siblings replace the constant
`runtimeCode : ByteArray` with `runtimeCodeOf : Store → Option ByteArray`, read against the final
frame's locals — a per-benchmark function that reads those names, `valueToWord`s each, and calls
`patchRuntime template offsetTable`.  The `∀`-over-immutable-values composition lives at the
per-benchmark theorem site, so no value type is baked in here. -/

inductive ctorResultEquivWith
  (evmRes: Except Ethereum.EVM.ExecutionException (Ethereum.ExecutionResult (Ethereum.AccountMap × Ethereum.UInt256 × Ethereum.Substate)))
  (solmRes : ExecResult) (runtimeCodeOf : Store → Option ByteArray) : Prop where
  | success :
    evmRes = .ok (.success (σ', g', A') o) →
    solmRes = .returned solmFrame solmState .none →
    σ' = solmState.accountMap →
    runtimeCodeOf solmFrame.locals = some o →
    ctorResultEquivWith evmRes solmRes runtimeCodeOf
  | successVoidReturn :
    evmRes = .ok (.success (σ', g', A') o) →
    solmRes = .returned solmFrame solmState (some []) →
    σ' = solmState.accountMap →
    runtimeCodeOf solmFrame.locals = some o →
    ctorResultEquivWith evmRes solmRes runtimeCodeOf
  | revert :
    evmRes = .ok (.revert g o) →
    solmRes = .reverted →
    ctorResultEquivWith evmRes solmRes runtimeCodeOf
  | invalidHalt :
    evmRes = .error .InvalidInstruction →
    solmRes = .reverted →
    ctorResultEquivWith evmRes solmRes runtimeCodeOf

inductive constructorEquivalenceForWith (cfg : Config)
    (contract : ContractDecl) (args : List Value)
    (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256)
    (A : Ethereum.Substate) (I : Ethereum.ExecutionEnv)
    (runtimeCodeOf : Store → Option ByteArray) : Prop where
  | execution {Ξ_res solmRes} :
    Ethereum.EVM.Ξ σ σ₀ g A I = Ξ_res →
    solmCtorExec cfg contract args σ σ₀ g A I solmRes →
    ctorResultEquivWith Ξ_res solmRes runtimeCodeOf →
    constructorEquivalenceForWith cfg contract args σ σ₀ g A I runtimeCodeOf
  | outOfGas :
    Ethereum.EVM.Ξ σ σ₀ g A I = .error .OutOfGass →
    constructorEquivalenceForWith cfg contract args σ σ₀ g A I runtimeCodeOf

inductive constructorEquivalenceWith (cfg : Config) (initcode : ByteArray) (contract : ContractDecl)
    (runtimeCodeOf : Store → Option ByteArray) : Prop where
  | intro :
    (∀ (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
      (I : Ethereum.ExecutionEnv) (args : List Value) (deployedInitcode : ByteArray),
    cfg.selfDeployment initcode args = .some deployedInitcode →
    I.code = deployedInitcode →
    I.calldata = .empty →
    I.perm = true →
    constructorEquivalenceForWith cfg contract args σ σ₀ g A I runtimeCodeOf
    ) →
    constructorEquivalenceWith cfg initcode contract runtimeCodeOf

-- Runtime side stays keyed on a concrete `runtimeCode`; the per-benchmark theorem instantiates
-- `runtimeCodeOf` and `runtimeCode` together for each immutable-value assignment.
inductive contractEquivalenceWith (cfg : Config) (initcode : EVM.Bytes) (runtimeCode : EVM.Bytes)
    (contract : ContractDecl) (runtimeCodeOf : Store → Option ByteArray) : Prop where
  | intro :
    constructorEquivalenceWith cfg initcode contract runtimeCodeOf →
    runtimeEquivalence cfg runtimeCode contract →
    contractEquivalenceWith cfg initcode runtimeCode contract runtimeCodeOf

inductive contractEquivalenceWithWF (wf : StorageWF) (cfg : Config) (initcode : EVM.Bytes)
    (runtimeCode : EVM.Bytes) (contract : ContractDecl)
    (runtimeCodeOf : Store → Option ByteArray) : Prop where
  | intro :
    constructorEquivalenceWith cfg initcode contract runtimeCodeOf →
    runtimeEquivalenceWithWF wf cfg runtimeCode contract →
    contractEquivalenceWithWF wf cfg initcode runtimeCode contract runtimeCodeOf

end Solm
