import Examples.Precompiles.Blake2f.Fallback.Setup.Terms.Defs.V

/-!
# BLAKE2F fallback bytecode memory terms: output words
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

abbrev outputH0LoadWord (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 384 32))

abbrev outputV0LoadWord (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1472 32))

abbrev outputV8LoadWord (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1728 32))

abbrev outputWord0 (mem : ByteArray) : UInt256 :=
  UInt256.land
    (UInt256.xor
      (UInt256.xor (UInt256.land (outputH0LoadWord mem) ⟨18446744073709551615⟩)
        (outputV0LoadWord mem))
      (outputV8LoadWord mem))
    ⟨18446744073709551615⟩

def outputWord0Mem (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (outputWord0 mem)).write 0 mem 1216 32

abbrev outputH1LoadWord (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 416 32))

abbrev outputV1LoadWord (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1504 32))

abbrev outputV9LoadWord (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1760 32))

abbrev outputWord1 (mem : ByteArray) : UInt256 :=
  UInt256.land
    (UInt256.xor
      (UInt256.xor (UInt256.land (outputH1LoadWord mem) ⟨18446744073709551615⟩)
        (outputV1LoadWord mem))
      (outputV9LoadWord mem))
    ⟨18446744073709551615⟩

def outputWord1Mem (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (outputWord1 mem)).write 0 mem 1248 32

abbrev outputH2LoadWord (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 448 32))

abbrev outputV2LoadWord (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1536 32))

abbrev outputV10LoadWord (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1792 32))

abbrev outputWord2 (mem : ByteArray) : UInt256 :=
  UInt256.land
    (UInt256.xor
      (UInt256.xor (UInt256.land (outputH2LoadWord mem) ⟨18446744073709551615⟩)
        (outputV2LoadWord mem))
      (outputV10LoadWord mem))
    ⟨18446744073709551615⟩

def outputWord2Mem (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (outputWord2 mem)).write 0 mem 1280 32

abbrev outputH3LoadWord (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 480 32))

abbrev outputV3LoadWord (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1568 32))

abbrev outputV11LoadWord (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1824 32))

abbrev outputWord3 (mem : ByteArray) : UInt256 :=
  UInt256.land
    (UInt256.xor
      (UInt256.xor (UInt256.land (outputH3LoadWord mem) ⟨18446744073709551615⟩)
        (outputV3LoadWord mem))
      (outputV11LoadWord mem))
    ⟨18446744073709551615⟩

def outputWord3Mem (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (outputWord3 mem)).write 0 mem 1312 32

abbrev outputH4LoadWord (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 512 32))

abbrev outputV4LoadWord (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1600 32))

abbrev outputV12LoadWord (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1856 32))

abbrev outputWord4 (mem : ByteArray) : UInt256 :=
  UInt256.land
    (UInt256.xor
      (UInt256.xor (UInt256.land (outputH4LoadWord mem) ⟨18446744073709551615⟩)
        (outputV4LoadWord mem))
      (outputV12LoadWord mem))
    ⟨18446744073709551615⟩

def outputWord4Mem (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (outputWord4 mem)).write 0 mem 1344 32

abbrev outputH5LoadWord (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 544 32))

abbrev outputV5LoadWord (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1632 32))

abbrev outputV13LoadWord (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1888 32))

abbrev outputWord5 (mem : ByteArray) : UInt256 :=
  UInt256.land
    (UInt256.xor
      (UInt256.xor (UInt256.land (outputH5LoadWord mem) ⟨18446744073709551615⟩)
        (outputV5LoadWord mem))
      (outputV13LoadWord mem))
    ⟨18446744073709551615⟩

def outputWord5Mem (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (outputWord5 mem)).write 0 mem 1376 32

abbrev outputH6LoadWord (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 576 32))

abbrev outputV6LoadWord (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1664 32))

abbrev outputV14LoadWord (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1920 32))

abbrev outputWord6 (mem : ByteArray) : UInt256 :=
  UInt256.land
    (UInt256.xor
      (UInt256.xor (UInt256.land (outputH6LoadWord mem) ⟨18446744073709551615⟩)
        (outputV6LoadWord mem))
      (outputV14LoadWord mem))
    ⟨18446744073709551615⟩

def outputWord6Mem (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (outputWord6 mem)).write 0 mem 1408 32

abbrev outputH7LoadWord (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 608 32))

abbrev outputV7LoadWord (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1696 32))

abbrev outputV15LoadWord (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1952 32))

abbrev outputWord7 (mem : ByteArray) : UInt256 :=
  UInt256.land
    (UInt256.xor
      (UInt256.xor (UInt256.land (outputH7LoadWord mem) ⟨18446744073709551615⟩)
        (outputV7LoadWord mem))
      (outputV15LoadWord mem))
    ⟨18446744073709551615⟩

def outputWord7Mem (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (outputWord7 mem)).write 0 mem 1440 32

def outputWordsMem0 (mem : ByteArray) : ByteArray :=
  outputWord0Mem mem

def outputWordsMem1 (mem : ByteArray) : ByteArray :=
  outputWord1Mem (outputWordsMem0 mem)

def outputWordsMem2 (mem : ByteArray) : ByteArray :=
  outputWord2Mem (outputWordsMem1 mem)

def outputWordsMem3 (mem : ByteArray) : ByteArray :=
  outputWord3Mem (outputWordsMem2 mem)

def outputWordsMem4 (mem : ByteArray) : ByteArray :=
  outputWord4Mem (outputWordsMem3 mem)

def outputWordsMem5 (mem : ByteArray) : ByteArray :=
  outputWord5Mem (outputWordsMem4 mem)

def outputWordsMem6 (mem : ByteArray) : ByteArray :=
  outputWord6Mem (outputWordsMem5 mem)

def outputWordsMem7 (mem : ByteArray) : ByteArray :=
  outputWord7Mem (outputWordsMem6 mem)

def outputWordsMem (mem : ByteArray) : ByteArray :=
  outputWordsMem7 mem

end Blake2f
