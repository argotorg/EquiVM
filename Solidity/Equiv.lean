import Solidity.Semantics
import Refinement.AccountEquiv
import Refinement.Result

/-!
# Refinement of EVM bytecode by a Solidity spec

Same layering as `Solm/Equiv.lean` (result equivalence → fixed-input relations → ∀-closures →
contract level), with two additions the Solidity semantics makes possible:
* revert data is compared exactly (`Error(string)`, `Panic(uint256)`, custom errors, empty);
* the final log series must coincide (both sides start from the same substate `A`).
`INVALID` is not a spec revert: solc 0.8 reverts with `Panic` data, so a stray `INVALID` is a
genuine crash.  The `Core` variants keep only Sol⁻'s observables (accounts + return data).

Nondeterminism (`gasleft()`, gas and non-log substate handed to sub-calls) is quantified once,
existentially over an `Oracle`: the bytecode's behaviour must be one the spec can exhibit.
-/

namespace Solidity

open ABI

abbrev EVMResult := Except Ethereum.EVM.ExecutionException
  (Ethereum.ExecutionResult
    (Batteries.RBSet Ethereum.AccountAddress compare × Ethereum.AccountMap × Ethereum.UInt256 × Ethereum.Substate))

/-- Equivalence of returned data; return slots always exist, so there is no fall-through case. -/
inductive returnDataEquiv (o : ByteArray) (vs : List ABIValue) : Refinement.ReturnConvention → Prop where
  | abi {tys} : encodeReturnValues? tys vs = some o → returnDataEquiv o vs (.abi tys)
  | rawBytes : vs = [.bytes o] → returnDataEquiv o vs .rawBytes

/-- Accounts and return data only (Sol⁻'s observables). -/
inductive execResultsEquivCore (evmRes : EVMResult) (res : TopResult) (conv : Refinement.ReturnConvention) : Prop where
  | success :
    evmRes = .ok (.success (cA', σ', g', A') out) →
    res = .returned m vs →
    cA' = m.evm.createdAccounts →
    Refinement.accountMapEquiv σ' m.evm.accountMap →
    returnDataEquiv out vs conv →
    execResultsEquivCore evmRes res conv
  | revert :
    evmRes = .ok (.revert g out) →
    res = .reverted d →
    execResultsEquivCore evmRes res conv

/-- Accounts, return data, revert data and logs. -/
inductive execResultsEquiv (evmRes : EVMResult) (res : TopResult) (conv : Refinement.ReturnConvention) : Prop where
  | success :
    evmRes = .ok (.success (cA', σ', g', A') out) →
    res = .returned m vs →
    cA' = m.evm.createdAccounts →
    Refinement.accountMapEquiv σ' m.evm.accountMap →
    A'.logSeries = m.evm.substate.logSeries →
    returnDataEquiv out vs conv →
    execResultsEquiv evmRes res conv
  | revert :
    evmRes = .ok (.revert g out) →
    res = .reverted out →
    execResultsEquiv evmRes res conv

theorem execResultsEquiv.core {evmRes res conv} (h : execResultsEquiv evmRes res conv) :
    execResultsEquivCore evmRes res conv := by
  cases h with
  | success h1 h2 h3 h4 _ h6 => exact .success h1 h2 h3 h4 h6
  | revert h1 h2 => exact .revert h1 h2

/-- Runtime equivalence of one message call at fixed inputs (full observables). -/
inductive runtimeEquivalenceFor (cfg : Config) (fc : FlatContract)
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader) (blocks : Ethereum.ProcessedBlocks)
    (σ_evm σ_spec σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) : Prop where
  | execution {Ξ_res res conv} :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ_evm σ₀ g A I = Ξ_res →
    (∃ o : Oracle, solidityExec cfg o fc createdAccounts genesisBlockHeader blocks σ_spec σ₀ g A I res conv ∧
      execResultsEquiv Ξ_res res conv) →
    runtimeEquivalenceFor cfg fc createdAccounts genesisBlockHeader blocks σ_evm σ_spec σ₀ g A I
  | noDispatch :
    dispatches fc I.calldata = false →
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ_evm σ₀ g A I = .ok (.revert g' ByteArray.empty) →
    runtimeEquivalenceFor cfg fc createdAccounts genesisBlockHeader blocks σ_evm σ_spec σ₀ g A I
  | decodingFailed {e fn g'} :
    selectorDispatch fc I.calldata = some e → fc.fns[e.fn]? = some fn →
    payableOrNoValue fn.decl I →
    decodeArgs cfg fc.types fn.decl I.calldata = none →
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ_evm σ₀ g A I = .ok (.revert g' ByteArray.empty) →
    runtimeEquivalenceFor cfg fc createdAccounts genesisBlockHeader blocks σ_evm σ_spec σ₀ g A I
  | outOfGas :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ_evm σ₀ g A I = .error .OutOfGass →
    runtimeEquivalenceFor cfg fc createdAccounts genesisBlockHeader blocks σ_evm σ_spec σ₀ g A I

/-- As `runtimeEquivalenceFor`, with Sol⁻'s observables only. -/
inductive runtimeEquivalenceForCore (cfg : Config) (fc : FlatContract)
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader) (blocks : Ethereum.ProcessedBlocks)
    (σ_evm σ_spec σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) : Prop where
  | execution {Ξ_res res conv} :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ_evm σ₀ g A I = Ξ_res →
    (∃ o : Oracle, solidityExec cfg o fc createdAccounts genesisBlockHeader blocks σ_spec σ₀ g A I res conv ∧
      execResultsEquivCore Ξ_res res conv) →
    runtimeEquivalenceForCore cfg fc createdAccounts genesisBlockHeader blocks σ_evm σ_spec σ₀ g A I
  | noDispatch :
    dispatches fc I.calldata = false →
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ_evm σ₀ g A I = .ok (.revert g' o) →
    runtimeEquivalenceForCore cfg fc createdAccounts genesisBlockHeader blocks σ_evm σ_spec σ₀ g A I
  | decodingFailed {e fn g' o} :
    selectorDispatch fc I.calldata = some e → fc.fns[e.fn]? = some fn →
    payableOrNoValue fn.decl I →
    decodeArgs cfg fc.types fn.decl I.calldata = none →
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ_evm σ₀ g A I = .ok (.revert g' o) →
    runtimeEquivalenceForCore cfg fc createdAccounts genesisBlockHeader blocks σ_evm σ_spec σ₀ g A I
  | outOfGas :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ_evm σ₀ g A I = .error .OutOfGass →
    runtimeEquivalenceForCore cfg fc createdAccounts genesisBlockHeader blocks σ_evm σ_spec σ₀ g A I

theorem runtimeEquivalenceFor.core {cfg fc cA gh bl σ_evm σ_spec σ₀ g A I}
    (h : runtimeEquivalenceFor cfg fc cA gh bl σ_evm σ_spec σ₀ g A I) :
    runtimeEquivalenceForCore cfg fc cA gh bl σ_evm σ_spec σ₀ g A I := by
  cases h with
  | execution h1 h2 =>
    obtain ⟨o, hexec, hequiv⟩ := h2
    exact .execution h1 ⟨o, hexec, hequiv.core⟩
  | noDispatch h1 h2 => exact .noDispatch h1 h2
  | decodingFailed h1 h2 h3 h4 h5 => exact .decodingFailed h1 h2 h3 h4 h5
  | outOfGas h1 => exact .outOfGas h1

abbrev StorageWF := Refinement.StorageWF

/-- Runtime equivalence over all admissible inputs, under a storage precondition. -/
inductive runtimeEquivalenceWithWF (wf : StorageWF) (cfg : Config) (bytecode : ByteArray)
    (fc : FlatContract) : Prop where
  | intro :
    (∀ (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
      (genesisBlockHeader : Ethereum.BlockHeader) (blocks : Ethereum.ProcessedBlocks)
      (σ_evm σ_spec σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
      (I : Ethereum.ExecutionEnv),
    I.code = bytecode →
    I.calldata.size < Ethereum.UInt256.size →
    I.perm = true →
    Refinement.accountMapEquiv σ_evm σ_spec →
    wf σ_evm I →
    runtimeEquivalenceFor cfg fc createdAccounts genesisBlockHeader blocks σ_evm σ_spec σ₀ g A I) →
    runtimeEquivalenceWithWF wf cfg bytecode fc

inductive runtimeEquivalence (cfg : Config) (bytecode : ByteArray) (fc : FlatContract) : Prop where
  | intro :
    (∀ (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
      (genesisBlockHeader : Ethereum.BlockHeader) (blocks : Ethereum.ProcessedBlocks)
      (σ_evm σ_spec σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
      (I : Ethereum.ExecutionEnv),
    I.code = bytecode →
    I.calldata.size < Ethereum.UInt256.size →
    I.perm = true →
    Refinement.accountMapEquiv σ_evm σ_spec →
    runtimeEquivalenceFor cfg fc createdAccounts genesisBlockHeader blocks σ_evm σ_spec σ₀ g A I) →
    runtimeEquivalence cfg bytecode fc

inductive runtimeEquivalenceCore (cfg : Config) (bytecode : ByteArray) (fc : FlatContract) : Prop where
  | intro :
    (∀ (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
      (genesisBlockHeader : Ethereum.BlockHeader) (blocks : Ethereum.ProcessedBlocks)
      (σ_evm σ_spec σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
      (I : Ethereum.ExecutionEnv),
    I.code = bytecode →
    I.calldata.size < Ethereum.UInt256.size →
    I.perm = true →
    Refinement.accountMapEquiv σ_evm σ_spec →
    runtimeEquivalenceForCore cfg fc createdAccounts genesisBlockHeader blocks σ_evm σ_spec σ₀ g A I) →
    runtimeEquivalenceCore cfg bytecode fc

theorem runtimeEquivalence.core {cfg bytecode fc} (h : runtimeEquivalence cfg bytecode fc) :
    runtimeEquivalenceCore cfg bytecode fc := by
  cases h with
  | intro hrun =>
    exact .intro fun cA gh bl σe σs σ₀ g A I h1 h2 h3 h4 => (hrun cA gh bl σe σs σ₀ g A I h1 h2 h3 h4).core

/-! ## Constructors -/

/-- The EVM's deployment returns the runtime code, which may depend on the immutables. -/
inductive ctorResultEquiv (evmRes : EVMResult) (res : CtorResult)
    (runtimeCodeOf : Store → Option ByteArray) : Prop where
  | success :
    evmRes = .ok (.success (cA', σ', g', A') out) →
    res = .ok m imms →
    cA' = m.evm.createdAccounts →
    Refinement.accountMapEquiv σ' m.evm.accountMap →
    A'.logSeries = m.evm.substate.logSeries →
    runtimeCodeOf imms = some out →
    ctorResultEquiv evmRes res runtimeCodeOf
  | revert :
    evmRes = .ok (.revert g out) →
    res = .reverted out →
    ctorResultEquiv evmRes res runtimeCodeOf

inductive constructorEquivalenceFor (cfg : Config) (fc : FlatContract) (args : List ABIValue)
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader) (blocks : Ethereum.ProcessedBlocks)
    (σ_evm σ_spec σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) (runtimeCodeOf : Store → Option ByteArray) : Prop where
  | execution {Ξ_res res} :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ_evm σ₀ g A I = Ξ_res →
    (∃ o : Oracle, solidityCtorExec cfg o fc args createdAccounts genesisBlockHeader blocks σ_spec σ₀ g A I res ∧
      ctorResultEquiv Ξ_res res runtimeCodeOf) →
    constructorEquivalenceFor cfg fc args createdAccounts genesisBlockHeader blocks σ_evm σ_spec σ₀ g A I runtimeCodeOf
  | outOfGas :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ_evm σ₀ g A I = .error .OutOfGass →
    constructorEquivalenceFor cfg fc args createdAccounts genesisBlockHeader blocks σ_evm σ_spec σ₀ g A I runtimeCodeOf

/-- Deployment equivalence over all constructor arguments admitted by `cfg.selfDeployment`. -/
inductive constructorEquivalence (cfg : Config) (initcode : ByteArray) (fc : FlatContract)
    (runtimeCodeOf : Store → Option ByteArray) : Prop where
  | intro :
    (∀ (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
      (genesisBlockHeader : Ethereum.BlockHeader) (blocks : Ethereum.ProcessedBlocks)
      (σ_evm σ_spec σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
      (I : Ethereum.ExecutionEnv) (args : List ABIValue) (deployedInitcode : ByteArray),
    cfg.selfDeployment initcode args = .some deployedInitcode →
    I.code = deployedInitcode →
    I.calldata = .empty →
    I.perm = true →
    Refinement.accountMapEquiv σ_evm σ_spec →
    constructorEquivalenceFor cfg fc args createdAccounts genesisBlockHeader blocks σ_evm σ_spec σ₀ g A I runtimeCodeOf) →
    constructorEquivalence cfg initcode fc runtimeCodeOf

/-- Constant runtime code (no immutables). -/
def constCode (runtimeCode : ByteArray) : Store → Option ByteArray := fun _ => some runtimeCode

/-- Top-level contract equivalence: deployment + every message call. -/
inductive contractEquivalence (cfg : Config) (initcode runtimeCode : EVM.Bytes) (fc : FlatContract) : Prop where
  | intro :
    constructorEquivalence cfg initcode fc (constCode runtimeCode) →
    runtimeEquivalence cfg runtimeCode fc →
    contractEquivalence cfg initcode runtimeCode fc

/-- Immutable-aware variant: the runtime relation is stated for one instantiation of the
    immutables (`runtimeCode`), the deployment relation for the code patched from the
    constructor's immutables. -/
inductive contractEquivalenceWith (cfg : Config) (initcode runtimeCode : EVM.Bytes) (fc : FlatContract)
    (runtimeCodeOf : Store → Option ByteArray) : Prop where
  | intro :
    constructorEquivalence cfg initcode fc runtimeCodeOf →
    runtimeEquivalence cfg runtimeCode fc →
    contractEquivalenceWith cfg initcode runtimeCode fc runtimeCodeOf

inductive contractEquivalenceWF (wf : StorageWF) (cfg : Config) (initcode runtimeCode : EVM.Bytes)
    (fc : FlatContract) : Prop where
  | intro :
    constructorEquivalence cfg initcode fc (constCode runtimeCode) →
    runtimeEquivalenceWithWF wf cfg runtimeCode fc →
    contractEquivalenceWF wf cfg initcode runtimeCode fc

/-! ## Core constructor relations (accounts and returned code only) -/

inductive ctorResultEquivCore (evmRes : EVMResult) (res : CtorResult)
    (runtimeCodeOf : Store → Option ByteArray) : Prop where
  | success :
    evmRes = .ok (.success (cA', σ', g', A') out) →
    res = .ok m imms →
    cA' = m.evm.createdAccounts →
    Refinement.accountMapEquiv σ' m.evm.accountMap →
    runtimeCodeOf imms = some out →
    ctorResultEquivCore evmRes res runtimeCodeOf
  | revert :
    evmRes = .ok (.revert g out) →
    res = .reverted d →
    ctorResultEquivCore evmRes res runtimeCodeOf

theorem ctorResultEquiv.core {evmRes res runtimeCodeOf} (h : ctorResultEquiv evmRes res runtimeCodeOf) :
    ctorResultEquivCore evmRes res runtimeCodeOf := by
  cases h with
  | success h1 h2 h3 h4 _ h6 => exact .success h1 h2 h3 h4 h6
  | revert h1 h2 => exact .revert h1 h2

inductive constructorEquivalenceForCore (cfg : Config) (fc : FlatContract) (args : List ABIValue)
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader) (blocks : Ethereum.ProcessedBlocks)
    (σ_evm σ_spec σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) (runtimeCodeOf : Store → Option ByteArray) : Prop where
  | execution {Ξ_res res} :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ_evm σ₀ g A I = Ξ_res →
    (∃ o : Oracle, solidityCtorExec cfg o fc args createdAccounts genesisBlockHeader blocks σ_spec σ₀ g A I res ∧
      ctorResultEquivCore Ξ_res res runtimeCodeOf) →
    constructorEquivalenceForCore cfg fc args createdAccounts genesisBlockHeader blocks σ_evm σ_spec σ₀ g A I runtimeCodeOf
  | outOfGas :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ_evm σ₀ g A I = .error .OutOfGass →
    constructorEquivalenceForCore cfg fc args createdAccounts genesisBlockHeader blocks σ_evm σ_spec σ₀ g A I runtimeCodeOf

theorem constructorEquivalenceFor.core {cfg fc args cA gh bl σ_evm σ_spec σ₀ g A I runtimeCodeOf}
    (h : constructorEquivalenceFor cfg fc args cA gh bl σ_evm σ_spec σ₀ g A I runtimeCodeOf) :
    constructorEquivalenceForCore cfg fc args cA gh bl σ_evm σ_spec σ₀ g A I runtimeCodeOf := by
  cases h with
  | execution h1 h2 =>
    obtain ⟨o, hexec, hequiv⟩ := h2
    exact .execution h1 ⟨o, hexec, hequiv.core⟩
  | outOfGas h1 => exact .outOfGas h1

inductive constructorEquivalenceCore (cfg : Config) (initcode : ByteArray) (fc : FlatContract)
    (runtimeCodeOf : Store → Option ByteArray) : Prop where
  | intro :
    (∀ (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
      (genesisBlockHeader : Ethereum.BlockHeader) (blocks : Ethereum.ProcessedBlocks)
      (σ_evm σ_spec σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
      (I : Ethereum.ExecutionEnv) (args : List ABIValue) (deployedInitcode : ByteArray),
    cfg.selfDeployment initcode args = .some deployedInitcode →
    I.code = deployedInitcode →
    I.calldata = .empty →
    I.perm = true →
    Refinement.accountMapEquiv σ_evm σ_spec →
    constructorEquivalenceForCore cfg fc args createdAccounts genesisBlockHeader blocks σ_evm σ_spec σ₀ g A I runtimeCodeOf) →
    constructorEquivalenceCore cfg initcode fc runtimeCodeOf

theorem constructorEquivalence.core {cfg initcode fc runtimeCodeOf}
    (h : constructorEquivalence cfg initcode fc runtimeCodeOf) :
    constructorEquivalenceCore cfg initcode fc runtimeCodeOf := by
  cases h with
  | intro hrun =>
    exact .intro fun cA gh bl σe σs σ₀ g A I args dep h1 h2 h3 h4 h5 =>
      (hrun cA gh bl σe σs σ₀ g A I args dep h1 h2 h3 h4 h5).core

/-- Deployment + every message call, with Sol⁻'s observables only. -/
inductive contractEquivalenceCore (cfg : Config) (initcode runtimeCode : EVM.Bytes) (fc : FlatContract) : Prop where
  | intro :
    constructorEquivalenceCore cfg initcode fc (constCode runtimeCode) →
    runtimeEquivalenceCore cfg runtimeCode fc →
    contractEquivalenceCore cfg initcode runtimeCode fc

theorem contractEquivalence.core {cfg initcode runtimeCode fc}
    (h : contractEquivalence cfg initcode runtimeCode fc) :
    contractEquivalenceCore cfg initcode runtimeCode fc := by
  cases h with
  | intro hc hr => exact .intro hc.core hr.core

end Solidity
