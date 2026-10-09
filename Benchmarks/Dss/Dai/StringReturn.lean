import Reasoning.Solc
import Benchmarks.Dss.Dai.Dispatch
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Dai

/-! ## Shared dynamic string getter facts -/

def daiNameBytes : ByteArray :=
  String.toByteArray "Dai Stablecoin"

def daiSymbolBytes : ByteArray :=
  String.toByteArray "DAI"

def daiVersionBytes : ByteArray :=
  String.toByteArray "1"

/-- The Solm body pattern for Dai's constant dynamic string getters. -/
theorem daiBytesLiteralBodyReturns (evm : EVM.State) (locals : Store) (bytes : ByteArray)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm locals
      (nonpayable ++ [.return [.bytesLit bytes]])
      (.returned { contract := contract, locals := locals } evm (some [.bytes bytes])) := by
  simpa [nonpayable] using
    nonpayableBytesLiteralBodyReturns (cfg := config) (contract := contract) evm locals bytes h


end Benchmarks.Dss.Dai
