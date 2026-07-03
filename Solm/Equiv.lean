import ABI.Encode
import ABI.Decode
import Solm.Dispatch

open Solm
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

/-- Account equality up to storage-map representation.  The non-storage account fields must match
    structurally, while persistent storage is compared by `find?` at every slot.  This abstracts
    over `RBMap` tree shape without equating absent storage slots with explicitly stored zeroes. -/
def accountEquiv (a b : Ethereum.Account) : Prop :=
  a.nonce = b.nonce ∧
  a.balance = b.balance ∧
  a.code = b.code ∧
  (∀ slot : Ethereum.UInt256,
    a.storage.find? slot = b.storage.find? slot) ∧
      (∀ slot : Ethereum.UInt256,
        a.tstorage.find? slot = b.tstorage.find? slot)

/-- Account-map equality up to the internal representation of each account's persistent storage
    map.  Account presence is still exact. -/
def accountMapEquiv (σ τ : Ethereum.AccountMap) : Prop :=
  ∀ addr : Ethereum.AccountAddress,
    match σ.find? addr, τ.find? addr with
    | none, none => True
    | some a, some b => accountEquiv a b
    | _, _ => False

theorem accountEquiv.refl (a : Ethereum.Account) : accountEquiv a a := by
  exact ⟨rfl, rfl, rfl, fun _ => rfl, fun _ => rfl⟩

theorem accountMapEquiv.refl (σ : Ethereum.AccountMap) : accountMapEquiv σ σ := by
  intro addr
  cases σ.find? addr <;> simp [accountEquiv.refl]

theorem accountEquiv.symm {a b : Ethereum.Account}
    (hab : accountEquiv a b) : accountEquiv b a := by
  rcases hab with ⟨hn, hb, hc, hs, ht⟩
  exact ⟨hn.symm, hb.symm, hc.symm, fun slot => (hs slot).symm,
    fun slot => (ht slot).symm⟩

theorem accountMapEquiv.symm {σ τ : Ethereum.AccountMap}
    (hστ : accountMapEquiv σ τ) : accountMapEquiv τ σ := by
  intro addr
  specialize hστ addr
  cases hσ : σ.find? addr <;> cases hτ : τ.find? addr <;>
    simp [hσ, hτ] at hστ ⊢
  exact accountEquiv.symm hστ

theorem accountMapEquiv.of_eq {σ τ : Ethereum.AccountMap} (h : σ = τ) :
    accountMapEquiv σ τ := by
  subst h
  exact accountMapEquiv.refl σ

theorem accountEquiv.trans {a b c : Ethereum.Account}
    (hab : accountEquiv a b) (hbc : accountEquiv b c) : accountEquiv a c := by
  rcases hab with ⟨hn₁, hb₁, hc₁, hs₁, ht₁⟩
  rcases hbc with ⟨hn₂, hb₂, hc₂, hs₂, ht₂⟩
  exact ⟨hn₁.trans hn₂, hb₁.trans hb₂, hc₁.trans hc₂,
    fun slot => (hs₁ slot).trans (hs₂ slot), fun slot => (ht₁ slot).trans (ht₂ slot)⟩

theorem accountMapEquiv.trans {σ τ υ : Ethereum.AccountMap}
    (hστ : accountMapEquiv σ τ) (hτυ : accountMapEquiv τ υ) : accountMapEquiv σ υ := by
  intro addr
  specialize hστ addr
  specialize hτυ addr
  cases hσ : σ.find? addr <;> cases hτ : τ.find? addr <;> cases hυ : υ.find? addr <;>
    simp [hσ, hτ, hυ] at hστ hτυ ⊢
  exact accountEquiv.trans hστ hτυ


inductive execResultsEquiv
  (evmRes: Except Ethereum.EVM.ExecutionException (Ethereum.ExecutionResult (Batteries.RBSet Ethereum.AccountAddress compare × Ethereum.AccountMap × Ethereum.UInt256 × Ethereum.Substate)))
  (solmRes : ExecResult) (returnConvention : ReturnConvention) : Prop where
  | success :
    -- Resulting states are compared up to storage-map representation (`accountMapEquiv`), the
    -- sound notion given `SSTORE` zero-canonicalization / `RBMap` non-extensionality. Syntactic
    -- equality is a special case, so this single constructor subsumes it.
    evmRes = .ok (.success (createdAccounts', σ', g', A') o) →
    solmRes = .returned _ solmState retVal →
    createdAccounts' = solmState.createdAccounts →
    accountMapEquiv σ' solmState.accountMap →
    -- A' = solmState.substate → /- We ignore the substate -/
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

inductive ctorResultEquiv
  (evmRes: Except Ethereum.EVM.ExecutionException (Ethereum.ExecutionResult (Batteries.RBSet Ethereum.AccountAddress compare × Ethereum.AccountMap × Ethereum.UInt256 × Ethereum.Substate)))
  (solmRes : ExecResult) (runtimeCode : ByteArray) : Prop where
  | success :
    -- Resulting states compared up to storage-map representation (`accountMapEquiv`); syntactic
    -- equality is a special case, so this single constructor subsumes it.
    evmRes = .ok (.success (createdAccounts', σ', g', A') o) →
    solmRes = .returned _ solmState .none →
    createdAccounts' = solmState.createdAccounts →
    accountMapEquiv σ' solmState.accountMap →
    -- A' = solmState.substate → /- We ignore the substate -/
    o = runtimeCode →
    ctorResultEquiv evmRes solmRes runtimeCode
  -- Twin of `success` for a ctor body ending in a bare `return` (explicit void return `some []`);
  -- kept separate so existing `.success` (fall-through `.none`) proofs are unchanged.
  | successVoidReturn :
    evmRes = .ok (.success (createdAccounts', σ', g', A') o) →
    solmRes = .returned _ solmState (some []) →
    createdAccounts' = solmState.createdAccounts →
    accountMapEquiv σ' solmState.accountMap →
    o = runtimeCode →
    ctorResultEquiv evmRes solmRes runtimeCode
  | revert :
    evmRes = .ok (.revert g o) →
    solmRes = .reverted →
    ctorResultEquiv evmRes solmRes runtimeCode
  -- `INVALID` (`0xFE`) refines a Solm `.reverted`, as in `execResultsEquiv.invalidHalt`.
  | invalidHalt :
    evmRes = .error .InvalidInstruction →
    solmRes = .reverted →
    ctorResultEquiv evmRes solmRes runtimeCode
  -- Zoe: commenting out so that it matches execResultsEquiv
  -- | error :
  --   -- TODO: is this what needs to happen?
  --   -- Zoe: Do we model all errors in Solm? AFAICT right now, some may cause the evaluation relation to be uninhabited (undef behavior)
  --   evmRes = .error e →
  --   solmRes = .reverted →
  --   ctorResultEquiv evmRes solmRes runtimeCode

inductive runtimeEquivalenceFor (cfg : Config)
    (contract : ContractDecl) /- Spec -/
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    -- EVM-side initial maps (fed to `Ξ`).
    (σ_evm : Ethereum.AccountMap)
    -- Solm-side initial maps (fed to `solmExec`).  They need only be `accountMapEquiv` to the
    -- EVM-side `σ_evm`/`σ₀` (not syntactically equal); the storage-observational semantics make
    -- the two executions agree.  The coupling is imposed as a precondition at `runtimeEquivalence!?!`.
    (σ_solm : Ethereum.AccountMap)
    (σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) /- contains the EVM bytecode -/
: Prop where
  | execution {Ξ_res solmRes returnConvention} : /- Both executions return -/
    /- Execute EVM transaction-/
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ_evm σ₀ g A I = Ξ_res →
    /- Solm transition dispatch + execution -/
    solmExec cfg contract createdAccounts genesisBlockHeader blocks σ_solm σ₀ g A I solmRes returnConvention →
    /- Resulting states and return must be equivalent equivalence -/
    execResultsEquiv Ξ_res solmRes returnConvention →
    runtimeEquivalenceFor cfg contract createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I
  | noDispatch : /- Dispatch fails in Solm, EVM reverts -/
    dispatchMsg contract I.calldata = .none →
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ_evm σ₀ g A I = .ok (.revert g' o) →
    runtimeEquivalenceFor cfg contract createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I
  | decodingFailed {transition transitionSig g' o} : /- Decoding fails in Solm, EVM reverts -/
    selectorDispatchMsg contract I.calldata = .some transition →
    transitionSig = transitionSignature transition →
    decodeCalldataWithMode cfg.abiDecodeMode (transition.params.map Param.name)
      transitionSig.paramTypes I.calldata = .none →
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ_evm σ₀ g A I = .ok (.revert g' o) →
    runtimeEquivalenceFor cfg contract createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I
  | outOfGas : /- EVM runs out of gas -/
    /- TODO: non-terminating EVM programs are currently equivalent to any spec -/
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ_evm σ₀ g A I = .error .OutOfGass →
    runtimeEquivalenceFor cfg contract createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I

-- a Solm contract corresponds to what?
inductive runtimeEquivalence!?! (cfg : Config) (bytecode : ByteArray) (contract : ContractDecl) : Prop where
  | intro :
    (∀ (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
      (genesisBlockHeader : Ethereum.BlockHeader)
      (blocks : Ethereum.ProcessedBlocks)
      (σ_evm : Ethereum.AccountMap)
      (σ_solm : Ethereum.AccountMap)
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
    -- The Solm-side initial maps need only be observationally (`accountMapEquiv`) equal to the
    -- EVM-side maps, not syntactically equal — see `runtimeEquivalenceFor`.
    accountMapEquiv σ_evm σ_solm →
    runtimeEquivalenceFor cfg contract createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I
    ) →
    runtimeEquivalence!?! cfg bytecode contract

inductive constructorEquivalenceFor (cfg : Config)
    (contract : ContractDecl) /- Spec -/
    (args : List Value)
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    -- EVM-side initial maps (fed to `Ξ`).
    (σ_evm : Ethereum.AccountMap)
    -- Solm-side initial maps (fed to `solmCtorExec`); coupled by `accountMapEquiv` at
    -- `constructorEquivalence` (need only be observationally, not syntactically, equal).
    (σ_solm : Ethereum.AccountMap)
    (σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) /- contains the EVM bytecode -/
    (runtimeCode : ByteArray)
: Prop where
  | execution {Ξ_res solmRes} : /- Both executions return -/
    /- Execute EVM transaction-/
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ_evm σ₀ g A I = Ξ_res →
    /- Solm constructor + execution -/
    solmCtorExec cfg contract args createdAccounts genesisBlockHeader blocks σ_solm σ₀ g A I solmRes →
    /- Resulting states must be equivalent, and the EVM return bytes should equal the runtime code -/
    ctorResultEquiv Ξ_res solmRes runtimeCode →
    constructorEquivalenceFor cfg contract args createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I runtimeCode
  | outOfGas : /- EVM runs out of gas -/
    /- TODO: non-terminating EVM programs are currently equivalent to any spec -/
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ_evm σ₀ g A I = .error .OutOfGass →
    constructorEquivalenceFor cfg contract args createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I runtimeCode


inductive constructorEquivalence (cfg : Config) (initcode : ByteArray) (contract : ContractDecl) (runtimeCode : ByteArray) : Prop where
  | intro :
    (∀ (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
      (genesisBlockHeader : Ethereum.BlockHeader)
      (blocks : Ethereum.ProcessedBlocks)
      (σ_evm : Ethereum.AccountMap)
      (σ_solm : Ethereum.AccountMap)
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
    -- The Solm-side initial maps need only be observationally (`accountMapEquiv`) equal to the
    -- EVM-side maps, not syntactically equal — see `constructorEquivalenceFor`.
    accountMapEquiv σ_evm σ_solm →
    -- We need to enforce that all successful execution paths return the same runtime code
    constructorEquivalenceFor cfg contract args createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I runtimeCode
    ) →
    constructorEquivalence cfg initcode contract runtimeCode

-- Technically could give only initcode and derive runtime code from it, but lets be explicit.
-- Note: right now we are only comparing code execution i.e. EVM.Ξ with solmExec.
-- We do not have a model of message calls (Θ) for the spec (which would handle balance transfer for example)
-- If it were implemented however it would likely exactly mirror the EVM version except for calling solmExec
-- instead of EVM.Ξ, so on the equivalence checking level it is uninteresting
inductive contractEquivalence (cfg : Config) (initcode : EVM.Bytes) (runtimeCode : EVM.Bytes) (contract : ContractDecl) : Prop where
  | intro :
    constructorEquivalence cfg initcode contract runtimeCode →
    runtimeEquivalence!?! cfg runtimeCode contract →
    contractEquivalence cfg initcode runtimeCode contract

/-! ## Parameterized (immutable-aware) constructor equivalence

The runtime code a constructor returns may depend on the immutable values the spec constructor binds
as locals (convention: `letDecl "imm_<name>" …`).  These siblings replace the constant
`runtimeCode : ByteArray` with `runtimeCodeOf : Store → Option ByteArray`, read against the final
frame's locals — a per-benchmark function that reads those names, `valueToWord`s each, and calls
`patchRuntime template offsetTable`.  The constant case `fun _ => some runtimeCode` recovers the
originals exactly (`ctorResultEquiv_const`).  The `∀`-over-immutable-values composition lives at the
per-benchmark theorem site, so no value type is baked in here. -/

inductive ctorResultEquivWith
  (evmRes: Except Ethereum.EVM.ExecutionException (Ethereum.ExecutionResult (Batteries.RBSet Ethereum.AccountAddress compare × Ethereum.AccountMap × Ethereum.UInt256 × Ethereum.Substate)))
  (solmRes : ExecResult) (runtimeCodeOf : Store → Option ByteArray) : Prop where
  | success :
    evmRes = .ok (.success (createdAccounts', σ', g', A') o) →
    solmRes = .returned solmFrame solmState .none →
    createdAccounts' = solmState.createdAccounts →
    accountMapEquiv σ' solmState.accountMap →
    runtimeCodeOf solmFrame.locals = some o →
    ctorResultEquivWith evmRes solmRes runtimeCodeOf
  | successVoidReturn :
    evmRes = .ok (.success (createdAccounts', σ', g', A') o) →
    solmRes = .returned solmFrame solmState (some []) →
    createdAccounts' = solmState.createdAccounts →
    accountMapEquiv σ' solmState.accountMap →
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

/-- The constant-runtime constructor relation is exactly the parameterized one at
    `runtimeCodeOf := fun _ => some runtimeCode`. -/
theorem ctorResultEquiv_const {evmRes solmRes} {rc : ByteArray} :
    ctorResultEquiv evmRes solmRes rc ↔ ctorResultEquivWith evmRes solmRes (fun _ => some rc) := by
  constructor
  · intro h; cases h with
    | success e1 e2 e3 e4 e5 => exact .success e1 e2 e3 e4 (by simp_all)
    | successVoidReturn e1 e2 e3 e4 e5 => exact .successVoidReturn e1 e2 e3 e4 (by simp_all)
    | revert e1 e2 => exact .revert e1 e2
    | invalidHalt e1 e2 => exact .invalidHalt e1 e2
  · intro h; cases h with
    | success e1 e2 e3 e4 e5 => exact .success e1 e2 e3 e4 (by simp_all)
    | successVoidReturn e1 e2 e3 e4 e5 => exact .successVoidReturn e1 e2 e3 e4 (by simp_all)
    | revert e1 e2 => exact .revert e1 e2
    | invalidHalt e1 e2 => exact .invalidHalt e1 e2

inductive constructorEquivalenceForWith (cfg : Config)
    (contract : ContractDecl) (args : List Value)
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader) (blocks : Ethereum.ProcessedBlocks)
    (σ_evm σ_solm σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256)
    (A : Ethereum.Substate) (I : Ethereum.ExecutionEnv)
    (runtimeCodeOf : Store → Option ByteArray) : Prop where
  | execution {Ξ_res solmRes} :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ_evm σ₀ g A I = Ξ_res →
    solmCtorExec cfg contract args createdAccounts genesisBlockHeader blocks σ_solm σ₀ g A I solmRes →
    ctorResultEquivWith Ξ_res solmRes runtimeCodeOf →
    constructorEquivalenceForWith cfg contract args createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I runtimeCodeOf
  | outOfGas :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ_evm σ₀ g A I = .error .OutOfGass →
    constructorEquivalenceForWith cfg contract args createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I runtimeCodeOf

inductive constructorEquivalenceWith (cfg : Config) (initcode : ByteArray) (contract : ContractDecl)
    (runtimeCodeOf : Store → Option ByteArray) : Prop where
  | intro :
    (∀ (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
      (genesisBlockHeader : Ethereum.BlockHeader) (blocks : Ethereum.ProcessedBlocks)
      (σ_evm σ_solm σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
      (I : Ethereum.ExecutionEnv) (args : List Value) (deployedInitcode : ByteArray),
    cfg.selfDeployment initcode args = .some deployedInitcode →
    I.code = deployedInitcode →
    I.calldata = .empty →
    I.perm = true →
    accountMapEquiv σ_evm σ_solm →
    constructorEquivalenceForWith cfg contract args createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I runtimeCodeOf
    ) →
    constructorEquivalenceWith cfg initcode contract runtimeCodeOf

-- Runtime side stays keyed on a concrete `runtimeCode`; the per-benchmark theorem instantiates
-- `runtimeCodeOf` and `runtimeCode` together for each immutable-value assignment.
inductive contractEquivalenceWith (cfg : Config) (initcode : EVM.Bytes) (runtimeCode : EVM.Bytes)
    (contract : ContractDecl) (runtimeCodeOf : Store → Option ByteArray) : Prop where
  | intro :
    constructorEquivalenceWith cfg initcode contract runtimeCodeOf →
    runtimeEquivalence!?! cfg runtimeCode contract →
    contractEquivalenceWith cfg initcode runtimeCode contract runtimeCodeOf
