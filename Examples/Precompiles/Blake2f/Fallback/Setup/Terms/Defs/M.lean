import Examples.Precompiles.Blake2f.Fallback.Setup.Terms.Defs.H

/-!
# BLAKE2F fallback bytecode memory terms: parsed `m` and `t` words
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

abbrev m0LoadWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((h7StoredMem I).readWithPadding 228 32))

abbrev m0ParsedWord (I : ExecutionEnv) : UInt256 :=
  evmSwap64 (UInt256.shiftRight (m0LoadWord I) ⟨192⟩)

def m0StoredMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (m0ParsedWord I)).write 0 (h7StoredMem I) 640 32

abbrev m1LoadWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((m0StoredMem I).readWithPadding 236 32))

abbrev m1ParsedWord (I : ExecutionEnv) : UInt256 :=
  evmSwap64 (UInt256.shiftRight (m1LoadWord I) ⟨192⟩)

def m1StoredMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (m1ParsedWord I)).write 0 (m0StoredMem I) 672 32

abbrev m2LoadWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((m1StoredMem I).readWithPadding 244 32))

abbrev m2ParsedWord (I : ExecutionEnv) : UInt256 :=
  evmSwap64 (UInt256.shiftRight (m2LoadWord I) ⟨192⟩)

def m2StoredMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (m2ParsedWord I)).write 0 (m1StoredMem I) 704 32

abbrev m3LoadWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((m2StoredMem I).readWithPadding 252 32))

abbrev m3ParsedWord (I : ExecutionEnv) : UInt256 :=
  evmSwap64 (UInt256.shiftRight (m3LoadWord I) ⟨192⟩)

def m3StoredMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (m3ParsedWord I)).write 0 (m2StoredMem I) 736 32

abbrev m4LoadWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((m3StoredMem I).readWithPadding 260 32))

abbrev m4ParsedWord (I : ExecutionEnv) : UInt256 :=
  evmSwap64 (UInt256.shiftRight (m4LoadWord I) ⟨192⟩)

def m4StoredMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (m4ParsedWord I)).write 0 (m3StoredMem I) 768 32

abbrev m5LoadWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((m4StoredMem I).readWithPadding 268 32))

abbrev m5ParsedWord (I : ExecutionEnv) : UInt256 :=
  evmSwap64 (UInt256.shiftRight (m5LoadWord I) ⟨192⟩)

def m5StoredMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (m5ParsedWord I)).write 0 (m4StoredMem I) 800 32

abbrev m6LoadWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((m5StoredMem I).readWithPadding 276 32))

abbrev m6ParsedWord (I : ExecutionEnv) : UInt256 :=
  evmSwap64 (UInt256.shiftRight (m6LoadWord I) ⟨192⟩)

def m6StoredMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (m6ParsedWord I)).write 0 (m5StoredMem I) 832 32

abbrev m7LoadWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((m6StoredMem I).readWithPadding 284 32))

abbrev m7ParsedWord (I : ExecutionEnv) : UInt256 :=
  evmSwap64 (UInt256.shiftRight (m7LoadWord I) ⟨192⟩)

def m7StoredMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (m7ParsedWord I)).write 0 (m6StoredMem I) 864 32

abbrev m8LoadWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((m7StoredMem I).readWithPadding 292 32))

abbrev m8ParsedWord (I : ExecutionEnv) : UInt256 :=
  evmSwap64 (UInt256.shiftRight (m8LoadWord I) ⟨192⟩)

def m8StoredMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (m8ParsedWord I)).write 0 (m7StoredMem I) 896 32

abbrev m9LoadWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((m8StoredMem I).readWithPadding 300 32))

abbrev m9ParsedWord (I : ExecutionEnv) : UInt256 :=
  evmSwap64 (UInt256.shiftRight (m9LoadWord I) ⟨192⟩)

def m9StoredMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (m9ParsedWord I)).write 0 (m8StoredMem I) 928 32

abbrev m10LoadWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((m9StoredMem I).readWithPadding 308 32))

abbrev m10ParsedWord (I : ExecutionEnv) : UInt256 :=
  evmSwap64 (UInt256.shiftRight (m10LoadWord I) ⟨192⟩)

def m10StoredMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (m10ParsedWord I)).write 0 (m9StoredMem I) 960 32

abbrev m11LoadWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((m10StoredMem I).readWithPadding 316 32))

abbrev m11ParsedWord (I : ExecutionEnv) : UInt256 :=
  evmSwap64 (UInt256.shiftRight (m11LoadWord I) ⟨192⟩)

def m11StoredMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (m11ParsedWord I)).write 0 (m10StoredMem I) 992 32

abbrev m12LoadWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((m11StoredMem I).readWithPadding 324 32))

abbrev m12ParsedWord (I : ExecutionEnv) : UInt256 :=
  evmSwap64 (UInt256.shiftRight (m12LoadWord I) ⟨192⟩)

def m12StoredMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (m12ParsedWord I)).write 0 (m11StoredMem I) 1024 32

abbrev m13LoadWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((m12StoredMem I).readWithPadding 332 32))

abbrev m13ParsedWord (I : ExecutionEnv) : UInt256 :=
  evmSwap64 (UInt256.shiftRight (m13LoadWord I) ⟨192⟩)

def m13StoredMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (m13ParsedWord I)).write 0 (m12StoredMem I) 1056 32

abbrev m14LoadWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((m13StoredMem I).readWithPadding 340 32))

abbrev m14ParsedWord (I : ExecutionEnv) : UInt256 :=
  evmSwap64 (UInt256.shiftRight (m14LoadWord I) ⟨192⟩)

def m14StoredMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (m14ParsedWord I)).write 0 (m13StoredMem I) 1088 32

abbrev m15LoadWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((m14StoredMem I).readWithPadding 348 32))

abbrev m15ParsedWord (I : ExecutionEnv) : UInt256 :=
  evmSwap64 (UInt256.shiftRight (m15LoadWord I) ⟨192⟩)

def m15StoredMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (m15ParsedWord I)).write 0 (m14StoredMem I) 1120 32

abbrev t0LoadWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((m15StoredMem I).readWithPadding 356 32))

abbrev t0ParsedWord (I : ExecutionEnv) : UInt256 :=
  evmSwap64 (UInt256.shiftRight (t0LoadWord I) ⟨192⟩)

def t0StoredMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (t0ParsedWord I)).write 0 (m15StoredMem I) 1152 32

abbrev t1LoadWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((t0StoredMem I).readWithPadding 364 32))

abbrev t1ParsedWord (I : ExecutionEnv) : UInt256 :=
  evmSwap64 (UInt256.shiftRight (t1LoadWord I) ⟨192⟩)

def t1StoredMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (t1ParsedWord I)).write 0 (t0StoredMem I) 1184 32

end Blake2f
