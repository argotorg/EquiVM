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
genuine crash.  Calldata the spec cannot decode must revert: with empty data, or with
`Panic(0x41)` when the argument decoder allocates memory for a dynamic argument.

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

/-- Revert data of a call whose arguments cannot be decoded: empty, or `Panic(0x41)` when the
    decoder allocates memory for a dynamic argument (`hasDynamicMemoryParam`). -/
def decodeFailureData (env : TypeEnv) (d : FnDecl) (out : ByteArray) : Prop :=
  out = ByteArray.empty ∨ (hasDynamicMemoryParam env d = true ∧ out = panicData 0x41)

/-- Runtime equivalence of one message call at fixed inputs. -/
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
  | decodingFailed {e fn g' out} :
    selectorDispatch fc I.calldata = some e → fc.fns[e.fn]? = some fn →
    payableOrNoValue fn.decl I →
    decodeArgs cfg fc.types fn.decl I.calldata = none →
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ_evm σ₀ g A I = .ok (.revert g' out) →
    decodeFailureData fc.types fn.decl out →
    runtimeEquivalenceFor cfg fc createdAccounts genesisBlockHeader blocks σ_evm σ_spec σ₀ g A I
  | outOfGas :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ_evm σ₀ g A I = .error .OutOfGass →
    runtimeEquivalenceFor cfg fc createdAccounts genesisBlockHeader blocks σ_evm σ_spec σ₀ g A I

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

end Solidity
