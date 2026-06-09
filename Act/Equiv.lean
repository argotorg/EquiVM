import ABI.Encode
import ABI.Decode
import Act.Dispatch

open Act
open ABI

inductive returnEquiv (o : ByteArray) (r : Option Value) (t : Option ABIType) : Prop where
  | returned :
    r = .some rv →
    t = .some abit →
    encodeReturnValue? abit rv = .some o →
    returnEquiv o r t
  | null :
    r = .none →
    o = null →
    returnEquiv o r t

/- Zoe: do we really need the type here? Can decode figure out the type from the return value constructor? -/

inductive execResultsEquiv
  (evmRes: Except Ethereum.EVM.ExecutionException (Ethereum.ExecutionResult (Batteries.RBSet Ethereum.AccountAddress compare × Ethereum.AccountMap × Ethereum.UInt256 × Ethereum.Substate)))
  (actRes : ExecResult) (t : Option ABIType) : Prop where
  | success :
    evmRes = .ok (.success (createdAccounts', σ', g', A') o) →
    actRes = .returned _ actState retVal →
    createdAccounts' = actState.createdAccounts →
    σ' = actState.accountMap →
    A' = actState.substate →
    returnEquiv o retVal t →
    execResultsEquiv evmRes actRes t
  | revert :
    evmRes = .ok (.revert g o) →
    actRes = .reverted →
    -- TODO: something like: decode o = retVal
    execResultsEquiv evmRes actRes t
  | error :
    -- TODO: is this what needs to happen?
    -- Zoe: Do we model all errors in Act? AFAICT right now, some may cause the evaluation relation to be uninhabited (undef behavior)
    evmRes = .error e →
    actRes = .reverted →
    execResultsEquiv evmRes actRes t


-- Act transaction dispatch and execution.
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
    /- Act transition dispatch -/
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
          machineState.gasAvailable := g
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
    /- Act transition dispatch + execution -/
    actExec cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I actRes returnType →
    /- Resulting states and return must be equivalent equivalence -/
    execResultsEquiv Ξ_res actRes returnType →
    runtimeEquivalenceFor cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  | noDispatch : /- Dispatch fails in Act, EVM reverts -/
    dispatchMsg contract I.calldata = .none →
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .ok (.revert g' o) →
    runtimeEquivalenceFor cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  | decodingFailed {transition transitionSig g' o} : /- Decoding fails in Act, EVM reverts -/
    dispatchMsg contract I.calldata = .some transition →
    transitionSig = transitionSignature transition →
    decodeCalldata (transition.params.map Param.name) transitionSig.paramTypes I.calldata = .none →
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .ok (.revert g' o) →
    runtimeEquivalenceFor cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  | outOfGas : /- EVM runs out of gas -/
    /- TODO: non-terminating EVM programs are currently equivalent to any spec -/
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .error .OutOfGass →
    runtimeEquivalenceFor cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I

-- an act contract corresponds to what?
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
    runtimeEquivalenceFor cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    ) →
    runtimeEquivalence!?! cfg bytecode contract
