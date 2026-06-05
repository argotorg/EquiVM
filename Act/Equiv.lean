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

inductive execResultsEquiv (evmRes: Except Ethereum.EVM.ExecutionException (Ethereum.ExecutionResult (Batteries.RBSet Ethereum.AccountAddress compare × Ethereum.AccountMap × Ethereum.UInt256 × Ethereum.Substate))) (actRes : ExecResult) (t : Option ABIType) : Prop where
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
    evmRes = .error e →
    actRes = .reverted →
    execResultsEquiv evmRes actRes t

inductive runtimeEquivalenceFor (cfg : Config) (bytecode : ByteArray) (contract : ContractDecl)
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
      (genesisBlockHeader : Ethereum.BlockHeader)
      (blocks : Ethereum.ProcessedBlocks)
      (σ : Ethereum.AccountMap)
      (σ₀ : Ethereum.AccountMap)
      (g : Ethereum.UInt256)
      (A : Ethereum.Substate)
      (I : Ethereum.ExecutionEnv)
: Prop where
  | execution :
    I.code = bytecode →
    dispatchMsg contract I.calldata = .some transition →
    transitionSig = transitionSignature transition →
    decodeCalldata (transition.params.map Param.name) transitionSig.paramTypes I.calldata = .some callargs →
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = Ξ_res →
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
    ExecContractBody cfg contract evmState callargs transition.body actRes →
    execResultsEquiv Ξ_res actRes transition.returnType →
    runtimeEquivalenceFor cfg bytecode contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  | noDispatch :
    I.code = bytecode →
    dispatchMsg contract I.calldata = .none →
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .ok (.revert g' o) →
    runtimeEquivalenceFor cfg bytecode contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  | decodingFailed :
    I.code = bytecode →
    dispatchMsg contract I.calldata = .some transition →
    transitionSig = transitionSignature transition →
    decodeCalldata (transition.params.map Param.name) transitionSig.paramTypes I.calldata = .none →
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .ok (.revert g' o) →
    runtimeEquivalenceFor cfg bytecode contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  | outOfGas :
    I.code = bytecode →
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .error .OutOfGass →
    runtimeEquivalenceFor cfg bytecode contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I

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
    runtimeEquivalenceFor cfg bytecode contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    ) →
    runtimeEquivalence!?! cfg bytecode contract


