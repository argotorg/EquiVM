import Examples.Precompiles.Blake2f.Spec
import Reasoning.Solc

/-!
# BLAKE2F fallback bytecode memory terms: base parser state

These bytecode terms are computable; the bytearray writes used here have Lean implementations.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

abbrev calldataSizeWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.calldata.size

/- Source note: the parser memory terms below are intentionally computable.  They use
`ByteArray.write` and `readWithPadding` through the Solidity dynamic-bytes helpers; despite older
FFI-adjacent names in the bytearray layer, these operations now have computable Lean definitions. -/

/-- Exact gas consumed by the nonpayable prologue and explicit calldata-length guard when the
length is rejected before any `bytes memory` allocation happens. -/
def invalidLengthGas : Nat := 55

/-- Exact gas consumed by the nonpayable prologue, successful length guard, and explicit
final-flag guard when the flag is rejected before any `bytes memory` allocation happens. -/
def invalidFinalFlagGas : Nat := 85

def finalFlagWord (I : ExecutionEnv) : UInt256 :=
  UInt256.byteAt ⟨0⟩ (uInt256OfByteArray (I.calldata.readBytes 212 32))

def hArrayAllocMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.ofNat 640).toByteArray.write 0
    (solcBytesSetPaddedMem I.calldata (UInt256.ofNat 213) ⟨0⟩) 64 32

def hArrayZeroMem (I : ExecutionEnv) : ByteArray :=
  I.calldata.write 213 (hArrayAllocMem I) 384 256

def mArrayAllocMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.ofNat 1152).toByteArray.write 0 (hArrayZeroMem I) 64 32

def mArrayZeroMem (I : ExecutionEnv) : ByteArray :=
  I.calldata.write 213 (mArrayAllocMem I) 640 512

def tArrayAllocMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.ofNat 1216).toByteArray.write 0 (mArrayZeroMem I) 64 32

def tArrayZeroMem (I : ExecutionEnv) : ByteArray :=
  I.calldata.write 213 (tArrayAllocMem I) 1152 64

abbrev inputFirstWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((tArrayZeroMem I).readWithPadding 160 32))

abbrev h0LoadWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((tArrayZeroMem I).readWithPadding 164 32))

def evmSwap64 (x : UInt256) : UInt256 :=
  let x :=
    UInt256.lor
      (UInt256.land (UInt256.shiftLeft x ⟨8⟩) ⟨18374966859414961920⟩)
      (UInt256.land (UInt256.shiftRight x ⟨8⟩) ⟨71777214294589695⟩)
  let x :=
    UInt256.lor
      (UInt256.land (UInt256.shiftLeft x ⟨16⟩) ⟨18446462603027742720⟩)
      (UInt256.land (UInt256.shiftRight x ⟨16⟩) ⟨281470681808895⟩)
  UInt256.lor
    (UInt256.land (UInt256.shiftLeft x ⟨32⟩) ⟨18446744069414584320⟩)
    (UInt256.land (UInt256.shiftRight x ⟨32⟩) ⟨4294967295⟩)

end Blake2f
