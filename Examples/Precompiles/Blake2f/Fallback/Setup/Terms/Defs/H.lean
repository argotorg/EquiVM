import Examples.Precompiles.Blake2f.Fallback.Setup.Terms.Defs.Base

/-!
# BLAKE2F fallback bytecode memory terms: parsed `h` words
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

abbrev h0ParsedWord (I : ExecutionEnv) : UInt256 :=
  evmSwap64 (UInt256.shiftRight (h0LoadWord I) ⟨192⟩)

def h0StoredMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (h0ParsedWord I)).write 0 (tArrayZeroMem I) 384 32

abbrev h1LoadWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((h0StoredMem I).readWithPadding 172 32))

abbrev h1ParsedWord (I : ExecutionEnv) : UInt256 :=
  evmSwap64 (UInt256.shiftRight (h1LoadWord I) ⟨192⟩)

def h1StoredMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (h1ParsedWord I)).write 0 (h0StoredMem I) 416 32

abbrev h2LoadWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((h1StoredMem I).readWithPadding 180 32))

abbrev h2ParsedWord (I : ExecutionEnv) : UInt256 :=
  evmSwap64 (UInt256.shiftRight (h2LoadWord I) ⟨192⟩)

def h2StoredMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (h2ParsedWord I)).write 0 (h1StoredMem I) 448 32

abbrev h3LoadWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((h2StoredMem I).readWithPadding 188 32))

abbrev h3ParsedWord (I : ExecutionEnv) : UInt256 :=
  evmSwap64 (UInt256.shiftRight (h3LoadWord I) ⟨192⟩)

def h3StoredMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (h3ParsedWord I)).write 0 (h2StoredMem I) 480 32

abbrev h4LoadWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((h3StoredMem I).readWithPadding 196 32))

abbrev h4ParsedWord (I : ExecutionEnv) : UInt256 :=
  evmSwap64 (UInt256.shiftRight (h4LoadWord I) ⟨192⟩)

def h4StoredMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (h4ParsedWord I)).write 0 (h3StoredMem I) 512 32

abbrev h5LoadWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((h4StoredMem I).readWithPadding 204 32))

abbrev h5ParsedWord (I : ExecutionEnv) : UInt256 :=
  evmSwap64 (UInt256.shiftRight (h5LoadWord I) ⟨192⟩)

def h5StoredMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (h5ParsedWord I)).write 0 (h4StoredMem I) 544 32

abbrev h6LoadWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((h5StoredMem I).readWithPadding 212 32))

abbrev h6ParsedWord (I : ExecutionEnv) : UInt256 :=
  evmSwap64 (UInt256.shiftRight (h6LoadWord I) ⟨192⟩)

def h6StoredMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (h6ParsedWord I)).write 0 (h5StoredMem I) 576 32

abbrev h7LoadWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((h6StoredMem I).readWithPadding 220 32))

abbrev h7ParsedWord (I : ExecutionEnv) : UInt256 :=
  evmSwap64 (UInt256.shiftRight (h7LoadWord I) ⟨192⟩)

def h7StoredMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (h7ParsedWord I)).write 0 (h6StoredMem I) 608 32

end Blake2f
