import Examples.Ripemd160.Bytecode
import Examples.Ripemd160.HashModel
import Examples.Ripemd160.ProofSupport
import Reasoning.ABI
import Reasoning.Constructor
import Reasoning.Dispatch
import Reasoning.Memory
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.SolmBody
import Reasoning.Stepping

/-!
# Ripemd160Deployed shared equivalence setup

The runtime has no selector dispatcher: every call enters the nonpayable fallback. This module
collects the raw-calldata store and byte-level return shape used by the symbolic trace.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Ripemd160

def maxFallbackCalldataSize : Nat := 18446744073709551424

abbrev calldataSizeWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.calldata.size

def roundedCalldataSizeWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land (UInt256.lnot ⟨31⟩) (calldataSizeWord I + ⟨31⟩)

def fallbackAllocationSize (I : ExecutionEnv) : UInt256 :=
  roundedCalldataSizeWord I + ⟨32⟩

def fallbackFreePtr (I : ExecutionEnv) : UInt256 :=
  ⟨128⟩ + fallbackAllocationSize I

noncomputable def fallbackAllocMem (I : ExecutionEnv) : ByteArray :=
  (fallbackFreePtr I).toByteArray.write 0 solcFreePtrMem 64 32

noncomputable def fallbackLengthMem (I : ExecutionEnv) : ByteArray :=
  (calldataSizeWord I).toByteArray.write 0 (fallbackAllocMem I) 128 32

noncomputable def fallbackCalldataMem (I : ExecutionEnv) : ByteArray :=
  I.calldata.write 0 (fallbackLengthMem I) 160 I.calldata.size

noncomputable def fallbackPaddedMem (I : ExecutionEnv) : ByteArray :=
  (⟨0⟩ : UInt256).toByteArray.write 0
    (fallbackCalldataMem I) (160 + I.calldata.size) 32

def fallbackCopyAw (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (MachineState.M (UInt256.ofNat 5).toNat 160 I.calldata.size)

def fallbackPaddedAw (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (fallbackCopyAw I).toNat (160 + I.calldata.size) 32)

def panicSelectorWord : UInt256 :=
  ⟨35408467139433450592217433187231851964531694900788300625387963629091585785856⟩

noncomputable def panic41Mem1 : ByteArray :=
  panicSelectorWord.toByteArray.write 0 solcFreePtrMem 0 32

noncomputable def panic41Mem : ByteArray :=
  (⟨65⟩ : UInt256).toByteArray.write 0 panic41Mem1 4 32

abbrev fallbackLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "data" (.bytes I.calldata)

/-- The deployed adapter returns a single right-aligned RIPEMD-160 word. -/
def rawDigestWord (digest : List UInt8) : ByteArray :=
  ⟨(List.replicate 12 0 ++ digest).toArray⟩

end Ripemd160
