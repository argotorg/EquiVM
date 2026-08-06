import Examples.Precompiles.Blake2f.Fallback.Setup.Terms.Defs.Output

/-!
# BLAKE2F fallback bytecode memory terms: Solidity return buffer
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

def returnAllocMem (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (UInt256.ofNat 2080)).write 0 mem 64 32

def returnLengthMem (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (UInt256.ofNat 64)).write 0 (returnAllocMem mem) 1984 32

def returnZeroPadMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  I.calldata.write 213 (returnLengthMem mem) 2016 64

abbrev returnLoopLoadWord0 (I : ExecutionEnv) (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((returnZeroPadMem I mem).readWithPadding 1216 32))

abbrev returnLoopWord0 (I : ExecutionEnv) (mem : ByteArray) : UInt256 :=
  UInt256.shiftLeft (evmSwap64 (returnLoopLoadWord0 I mem)) ⟨192⟩

def returnLoopWord0Mem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (returnLoopWord0 I mem)).write 0 (returnZeroPadMem I mem) 2016 32

abbrev returnLoopLoadWord1 (I : ExecutionEnv) (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((returnLoopWord0Mem I mem).readWithPadding 1248 32))

abbrev returnLoopWord1 (I : ExecutionEnv) (mem : ByteArray) : UInt256 :=
  UInt256.shiftLeft (evmSwap64 (returnLoopLoadWord1 I mem)) ⟨192⟩

def returnLoopWord1Mem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (returnLoopWord1 I mem)).write 0 (returnLoopWord0Mem I mem) 2024 32

abbrev returnLoopLoadWord2 (I : ExecutionEnv) (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((returnLoopWord1Mem I mem).readWithPadding 1280 32))

abbrev returnLoopWord2 (I : ExecutionEnv) (mem : ByteArray) : UInt256 :=
  UInt256.shiftLeft (evmSwap64 (returnLoopLoadWord2 I mem)) ⟨192⟩

def returnLoopWord2Mem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (returnLoopWord2 I mem)).write 0 (returnLoopWord1Mem I mem) 2032 32

abbrev returnLoopLoadWord3 (I : ExecutionEnv) (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((returnLoopWord2Mem I mem).readWithPadding 1312 32))

abbrev returnLoopWord3 (I : ExecutionEnv) (mem : ByteArray) : UInt256 :=
  UInt256.shiftLeft (evmSwap64 (returnLoopLoadWord3 I mem)) ⟨192⟩

def returnLoopWord3Mem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (returnLoopWord3 I mem)).write 0 (returnLoopWord2Mem I mem) 2040 32

abbrev returnLoopLoadWord4 (I : ExecutionEnv) (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((returnLoopWord3Mem I mem).readWithPadding 1344 32))

abbrev returnLoopWord4 (I : ExecutionEnv) (mem : ByteArray) : UInt256 :=
  UInt256.shiftLeft (evmSwap64 (returnLoopLoadWord4 I mem)) ⟨192⟩

def returnLoopWord4Mem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (returnLoopWord4 I mem)).write 0 (returnLoopWord3Mem I mem) 2048 32

abbrev returnLoopLoadWord5 (I : ExecutionEnv) (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((returnLoopWord4Mem I mem).readWithPadding 1376 32))

abbrev returnLoopWord5 (I : ExecutionEnv) (mem : ByteArray) : UInt256 :=
  UInt256.shiftLeft (evmSwap64 (returnLoopLoadWord5 I mem)) ⟨192⟩

def returnLoopWord5Mem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (returnLoopWord5 I mem)).write 0 (returnLoopWord4Mem I mem) 2056 32

abbrev returnLoopLoadWord6 (I : ExecutionEnv) (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((returnLoopWord5Mem I mem).readWithPadding 1408 32))

abbrev returnLoopWord6 (I : ExecutionEnv) (mem : ByteArray) : UInt256 :=
  UInt256.shiftLeft (evmSwap64 (returnLoopLoadWord6 I mem)) ⟨192⟩

def returnLoopWord6Mem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (returnLoopWord6 I mem)).write 0 (returnLoopWord5Mem I mem) 2064 32

abbrev returnLoopLoadWord7 (I : ExecutionEnv) (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((returnLoopWord6Mem I mem).readWithPadding 1440 32))

abbrev returnLoopWord7 (I : ExecutionEnv) (mem : ByteArray) : UInt256 :=
  UInt256.shiftLeft (evmSwap64 (returnLoopLoadWord7 I mem)) ⟨192⟩

def returnLoopWord7Mem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (returnLoopWord7 I mem)).write 0 (returnLoopWord6Mem I mem) 2072 32

end Blake2f
