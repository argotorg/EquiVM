import Benchmarks.Morpho.MetaMorphoV1_1.PermitHashSource

/-! Typed permit arguments and the source frames surrounding signature recovery. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

structure PermitData where
  owner : AccountAddress
  spender : AccountAddress
  value : UInt256
  deadline : UInt256
  sigV : UInt256
  sigR : UInt256
  sigS : UInt256

namespace PermitData

def locals (p : PermitData) : Store :=
  (((((((∅ : Store).insert "owner" (.address p.owner)).insert "spender" (.address p.spender)).insert
    "value" (uint256Value p.value)).insert "deadline" (uint256Value p.deadline)).insert
    "v" (uint256Value p.sigV)).insert "r" (wordBytes32Value p.sigR)).insert
    "s" (wordBytes32Value p.sigS)

def structHash (p : PermitData) (evm : State) : UInt256 :=
  permitStructHash p.owner p.spender p.value (nonceWord evm p.owner) p.deadline

def digest (p : PermitData) (v : MetaMorphoV1_1Immutables) (evm : State) : UInt256 :=
  typedDataHash (domainSeparatorWord v evm.executionEnv) (p.structHash evm)

def entryFrame (p : PermitData) (evm : State) (v : MetaMorphoV1_1Immutables) : Frame :=
  ⟨contract, p.locals.insert "__calldata" (.bytes evm.executionEnv.calldata), immStore v⟩

def nonceFrame (p : PermitData) (evm : State) (v : MetaMorphoV1_1Immutables) : Frame :=
  { p.entryFrame evm v with
    locals := (p.entryFrame evm v).locals.insert "__c0" (uint256Value (nonceWord evm p.owner)) }

def hashFrame (p : PermitData) (evm : State) (v : MetaMorphoV1_1Immutables) : Frame :=
  { p.nonceFrame evm v with
    locals := ((p.nonceFrame evm v).locals.insert "structHash"
      (wordBytes32Value (p.structHash evm))).insert "hash" (wordBytes32Value (p.digest v evm)) }

def signerFrame (p : PermitData) (evm : State) (v : MetaMorphoV1_1Immutables)
    (signer : AccountAddress) : Frame :=
  { p.hashFrame evm v with
    locals := (p.hashFrame evm v).locals.insert "signer" (.address signer) }

end PermitData

end Benchmarks.Morpho.MetaMorphoV1_1
