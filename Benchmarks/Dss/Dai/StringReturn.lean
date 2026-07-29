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

-- LIBRARY CANDIDATE: short dynamic bytes/string return memory shape for solc constant getters.
def daiStringObjectMem0 : ByteArray :=
  (UInt256.toByteArray (⟨192⟩ : UInt256)).write 0 solcFreePtrMem
    (⟨64⟩ : UInt256).toNat 32

-- LIBRARY CANDIDATE: short dynamic bytes/string return memory shape for solc constant getters.
def daiStringObjectMem1 (len : UInt256) : ByteArray :=
  (UInt256.toByteArray len).write 0 daiStringObjectMem0 (⟨128⟩ : UInt256).toNat 32

-- LIBRARY CANDIDATE: short dynamic bytes/string return memory shape for solc constant getters.
def daiStringObjectMem (len payloadWord : UInt256) : ByteArray :=
  (UInt256.toByteArray payloadWord).write 0 (daiStringObjectMem1 len)
    (⟨160⟩ : UInt256).toNat 32

-- LIBRARY CANDIDATE: short dynamic bytes/string return memory shape for solc constant getters.
def daiStringAbiMem0 (len payloadWord : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0
    (daiStringObjectMem len payloadWord) (⟨192⟩ : UInt256).toNat 32

-- LIBRARY CANDIDATE: short dynamic bytes/string return memory shape for solc constant getters.
def daiStringAbiMem1 (len payloadWord : UInt256) : ByteArray :=
  (UInt256.toByteArray len).write 0 (daiStringAbiMem0 len payloadWord)
    (⟨224⟩ : UInt256).toNat 32

-- LIBRARY CANDIDATE: short dynamic bytes/string return memory shape for solc constant getters.
def daiStringAbiMem2 (len payloadWord : UInt256) : ByteArray :=
  (UInt256.toByteArray payloadWord).write 0 (daiStringAbiMem1 len payloadWord)
    (⟨256⟩ : UInt256).toNat 32

-- LIBRARY CANDIDATE: short dynamic bytes/string return tail mask used by solc's ABI encoder.
def daiStringTailMask (len : UInt256) : UInt256 :=
  UInt256.lnot (UInt256.sub (UInt256.exp ⟨256⟩ (UInt256.sub ⟨32⟩ len)) ⟨1⟩)

-- LIBRARY CANDIDATE: short dynamic bytes/string return tail cleanup used by solc's ABI encoder.
def daiStringCleanWord (len payloadWord : UInt256) : UInt256 :=
  UInt256.land (daiStringTailMask len) payloadWord

-- LIBRARY CANDIDATE: short dynamic bytes/string return memory shape for solc constant getters.
def daiStringAbiMem3 (len payloadWord : UInt256) : ByteArray :=
  (UInt256.toByteArray (daiStringCleanWord len payloadWord)).write 0
    (daiStringAbiMem2 len payloadWord) (⟨256⟩ : UInt256).toNat 32

end Benchmarks.Dss.Dai
