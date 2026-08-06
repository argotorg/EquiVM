import Examples.Precompiles.Blake2f.Fallback.Setup.Terms.Defs.M

/-!
# BLAKE2F fallback bytecode memory terms: compression vector setup
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

def compressionScratchAllocMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (UInt256.ofNat 1472)).write 0 (t1StoredMem I) 64 32

def compressionScratchZeroMem (I : ExecutionEnv) : ByteArray :=
  I.calldata.write 213 (compressionScratchAllocMem I) 1216 256

def compressionVAllocMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (UInt256.ofNat 1984)).write 0 (compressionScratchZeroMem I) 64 32

abbrev v0LoadWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((compressionVAllocMem I).readWithPadding 384 32))

abbrev v0StoredWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land (v0LoadWord I) ⟨18446744073709551615⟩

def v0InitMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (v0StoredWord I)).write 0 (compressionVAllocMem I) 1472 32

abbrev v1LoadWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((v0InitMem I).readWithPadding 416 32))

abbrev v1StoredWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land (v1LoadWord I) ⟨18446744073709551615⟩

def v1InitMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (v1StoredWord I)).write 0 (v0InitMem I) 1504 32

abbrev v2LoadWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((v1InitMem I).readWithPadding 448 32))

abbrev v2StoredWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land (v2LoadWord I) ⟨18446744073709551615⟩

def v2InitMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (v2StoredWord I)).write 0 (v1InitMem I) 1536 32

abbrev v3LoadWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((v2InitMem I).readWithPadding 480 32))

abbrev v3StoredWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land (v3LoadWord I) ⟨18446744073709551615⟩

def v3InitMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (v3StoredWord I)).write 0 (v2InitMem I) 1568 32

abbrev v4LoadWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((v3InitMem I).readWithPadding 512 32))

abbrev v4StoredWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land (v4LoadWord I) ⟨18446744073709551615⟩

def v4InitMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (v4StoredWord I)).write 0 (v3InitMem I) 1600 32

abbrev v5LoadWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((v4InitMem I).readWithPadding 544 32))

abbrev v5StoredWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land (v5LoadWord I) ⟨18446744073709551615⟩

def v5InitMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (v5StoredWord I)).write 0 (v4InitMem I) 1632 32

abbrev v6LoadWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((v5InitMem I).readWithPadding 576 32))

abbrev v6StoredWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land (v6LoadWord I) ⟨18446744073709551615⟩

def v6InitMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (v6StoredWord I)).write 0 (v5InitMem I) 1664 32

abbrev v7LoadWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((v6InitMem I).readWithPadding 608 32))

abbrev v7StoredWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land (v7LoadWord I) ⟨18446744073709551615⟩

def v7InitMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (v7StoredWord I)).write 0 (v6InitMem I) 1696 32

def v8InitMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (UInt256.ofNat 7640891576956012808)).write 0 (v7InitMem I) 1728 32

def v9InitMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (UInt256.ofNat 13503953896175478587)).write 0 (v8InitMem I) 1760 32

def v10InitMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (UInt256.ofNat 4354685564936845355)).write 0 (v9InitMem I) 1792 32

def v11InitMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (UInt256.ofNat 11912009170470909681)).write 0 (v10InitMem I) 1824 32

def v12InitMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (UInt256.ofNat 5840696475078001361)).write 0 (v11InitMem I) 1856 32

def v13InitMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (UInt256.ofNat 11170449401992604703)).write 0 (v12InitMem I) 1888 32

def v14InitMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (UInt256.ofNat 2270897969802886507)).write 0 (v13InitMem I) 1920 32

def v15InitMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (UInt256.ofNat 6620516959819538809)).write 0 (v14InitMem I) 1952 32

abbrev t0MixLoadWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((v15InitMem I).readWithPadding 1152 32))

abbrev t0MixMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land (t0MixLoadWord I) ⟨18446744073709551615⟩

abbrev t1MixLoadWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((v15InitMem I).readWithPadding 1184 32))

abbrev t1MixMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land (t1MixLoadWord I) ⟨18446744073709551615⟩

abbrev v12MixedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.xor (UInt256.ofNat 5840696475078001361) (t0MixMaskedWord I)

def v12MixedMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (v12MixedWord I)).write 0 (v15InitMem I) 1856 32

abbrev v13MixedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.xor (UInt256.ofNat 11170449401992604703) (t1MixMaskedWord I)

def v13MixedMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (v13MixedWord I)).write 0 (v12MixedMem I) 1888 32

def v14FinalFlagMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (UInt256.ofNat 16175846103906665108)).write 0 (v13MixedMem I) 1920 32

end Blake2f
