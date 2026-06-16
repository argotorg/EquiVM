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
  | _              => none

inductive returnEquiv (o : ByteArray) (r : Option Value) (t : Option ABIType) : Prop where
  | returned :
    r = .some rv →
    t = .some abit →
    encodeReturnValue? abit rv = .some o →
    returnEquiv o r t
  | void :
    /- No declared return type and no value: the EVM returns empty output. -/
    r = .none →
    t = .none →
    o = null →
    returnEquiv o r t
  | fallthrough :
    /- Declared return type but no explicit `return`: the EVM returns the ABI
       encoding of the type's default (zero-initialized) value. -/
    r = .none →
    t = .some abit →
    defaultAbiValue abit = .some dv →
    encodeReturnValue? abit dv = .some o →
    returnEquiv o r t


inductive execResultsEquiv
  (evmRes: Except Ethereum.EVM.ExecutionException (Ethereum.ExecutionResult (Batteries.RBSet Ethereum.AccountAddress compare × Ethereum.AccountMap × Ethereum.UInt256 × Ethereum.Substate)))
  (actRes : ExecResult) (t : Option ABIType) : Prop where
  | success :
    evmRes = .ok (.success (createdAccounts', σ', g', A') o) →
    actRes = .returned _ actState retVal →
    createdAccounts' = actState.createdAccounts →
    σ' = actState.accountMap →
    -- A' = actState.substate → /- We ignore the substate -/
    returnEquiv o retVal t →
    execResultsEquiv evmRes actRes t
  | revert :
    evmRes = .ok (.revert g o) →
    actRes = .reverted →
    -- TODO: something like: decode o = retVal
    execResultsEquiv evmRes actRes t
  | error :
    -- TODO: is this what needs to happen?
    -- Zoe: Do we model all errors in Solm? AFAICT right now, some may cause the evaluation relation to be uninhabited (undef behavior)
    evmRes = .error e →
    actRes = .reverted →
    execResultsEquiv evmRes actRes t


-- Solm transaction dispatch and execution.
inductive actExec
    (conf : Config)
    (contract : ContractDecl) /- Spec -/
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ : Ethereum.AccountMap)
    (σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (actRes : ExecResult)
: Option ABIType -> Prop where
  | intro :
    /- Solm transition dispatch -/
    dispatchMsg contract I.calldata = .some transition →
    transitionSig = transitionSignature transition →
    decodeCalldata (transition.params.map Param.name) transitionSig.paramTypes I.calldata = .some callargs →
    evmState =
      { (default : EVM.State) with
          accountMap := σ
          σ₀ := σ₀
          executionEnv := I
          substate := A
          createdAccounts := createdAccounts
          machineState.gasAvailable := .ofUInt256 g
          blocks := blocks
          genesisBlockHeader := genesisBlockHeader
      } →
    ExecContractBody conf contract evmState callargs transition.body actRes →
    actExec conf contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I actRes transition.returnType

inductive runtimeEquivalenceFor (cfg : Config)
    (contract : ContractDecl) /- Spec -/
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ : Ethereum.AccountMap)
    (σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) /- contains the EVM bytecode -/
: Prop where
  | execution {Ξ_res actRes returnType} : /- Both executions return -/
    /- Execute EVM transaction-/
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = Ξ_res →
    /- Solm transition dispatch + execution -/
    actExec cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I actRes returnType →
    /- Resulting states and return must be equivalent equivalence -/
    execResultsEquiv Ξ_res actRes returnType →
    runtimeEquivalenceFor cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  | noDispatch : /- Dispatch fails in Solm, EVM reverts -/
    dispatchMsg contract I.calldata = .none →
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .ok (.revert g' o) →
    runtimeEquivalenceFor cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  | decodingFailed {transition transitionSig g' o} : /- Decoding fails in Solm, EVM reverts -/
    dispatchMsg contract I.calldata = .some transition →
    transitionSig = transitionSignature transition →
    decodeCalldata (transition.params.map Param.name) transitionSig.paramTypes I.calldata = .none →
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .ok (.revert g' o) →
    runtimeEquivalenceFor cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  | outOfGas : /- EVM runs out of gas -/
    /- TODO: non-terminating EVM programs are currently equivalent to any spec -/
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .error .OutOfGass →
    runtimeEquivalenceFor cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I

-- a Solm contract corresponds to what?
inductive runtimeEquivalence!?! (cfg : Config) (bytecode : ByteArray) (contract : ContractDecl) : Prop where
  | intro :
    (∀ (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
      (genesisBlockHeader : Ethereum.BlockHeader)
      (blocks : Ethereum.ProcessedBlocks)
      (σ : Ethereum.AccountMap)
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
    runtimeEquivalenceFor cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    ) →
    runtimeEquivalence!?! cfg bytecode contract
