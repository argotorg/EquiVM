import Examples.Precompiles.Ripemd160.HashWideRound
import Examples.Precompiles.Ripemd160.HashCursorRound

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Ripemd160

theorem runtimeInitLineCursor_line_padded {I : ExecutionEnv}
    {cursor : RuntimeMemCursor} {n baseOffset : Nat}
    {base : UInt256} {s : RuntimeLineState}
    (hpadded : RuntimePaddedCursor I cursor n)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hbase : base.toNat = (hashScratchPtr I).toNat + baseOffset)
    (hoffset : baseOffset + 128 ≤ 832) :
    RuntimeLineAt (runtimeInitLineCursor cursor base s) base s := by
  have addNat (offset : Nat) (hoff : baseOffset + offset ≤ 832) :
      (base + UInt256.ofNat offset).toNat =
        (hashScratchPtr I).toNat + (baseOffset + offset) := by
    rw [uadd_ofNat_toNat offset (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega) (by
        rw [hbase]
        have hu := hashScratchPtr_add_uint I hsmall
        omega)]
    omega
  have h32 : (base + ⟨32⟩).toNat =
      (hashScratchPtr I).toNat + (baseOffset + 32) := addNat 32 (by omega)
  have h64 : (base + ⟨64⟩).toNat =
      (hashScratchPtr I).toNat + (baseOffset + 64) := addNat 64 (by omega)
  have h96 : (base + ⟨96⟩).toNat =
      (hashScratchPtr I).toNat + (baseOffset + 96) := addNat 96 (by omega)
  have h128 : (base + ⟨128⟩).toNat =
      (hashScratchPtr I).toNat + (baseOffset + 128) := addNat 128 (by omega)
  let c1 := runtimeStoreCursor cursor base s.a
  let c2 := runtimeStoreCursor c1 (base + ⟨32⟩) s.b
  let c3 := runtimeStoreCursor c2 (base + ⟨64⟩) s.c
  let c4 := runtimeStoreCursor c3 (base + ⟨96⟩) s.d
  let c5 := runtimeStoreCursor c4 (base + ⟨128⟩) s.e
  have hp1 : RuntimePaddedCursor I c1 n :=
    hpadded.storeAboveScratch hsmall (by omega) hbase
  have hp2 : RuntimePaddedCursor I c2 n :=
    hp1.storeAboveScratch hsmall (by omega) h32
  have hp3 : RuntimePaddedCursor I c3 n :=
    hp2.storeAboveScratch hsmall (by omega) h64
  have hp4 : RuntimePaddedCursor I c4 n :=
    hp3.storeAboveScratch hsmall (by omega) h96
  have ha1 : RuntimeWordAt c1 base s.a := by
    simpa [c1] using hpadded.storeWordAboveScratch
      (value := s.a) hsmall (by omega) hbase
  have ha2 := ha1.storeAboveScratch hp1 hsmall (stored := s.b)
    (by omega) h32 (by omega)
  have ha3 := ha2.storeAboveScratch hp2 hsmall (stored := s.c)
    (by omega) h64 (by omega)
  have ha4 := ha3.storeAboveScratch hp3 hsmall (stored := s.d)
    (by omega) h96 (by omega)
  have ha5 := ha4.storeAboveScratch hp4 hsmall (stored := s.e)
    (by omega) h128 (by omega)
  have hb2 : RuntimeWordAt c2 (base + ⟨32⟩) s.b := by
    simpa [c2] using hp1.storeWordAboveScratch
      (value := s.b) hsmall (by omega) h32
  have hb3 := hb2.storeAboveScratch hp2 hsmall (stored := s.c)
    (by omega) h64 (by omega)
  have hb4 := hb3.storeAboveScratch hp3 hsmall (stored := s.d)
    (by omega) h96 (by omega)
  have hb5 := hb4.storeAboveScratch hp4 hsmall (stored := s.e)
    (by omega) h128 (by omega)
  have hc3 : RuntimeWordAt c3 (base + ⟨64⟩) s.c := by
    simpa [c3] using hp2.storeWordAboveScratch
      (value := s.c) hsmall (by omega) h64
  have hc4 := hc3.storeAboveScratch hp3 hsmall (stored := s.d)
    (by omega) h96 (by omega)
  have hc5 := hc4.storeAboveScratch hp4 hsmall (stored := s.e)
    (by omega) h128 (by omega)
  have hd4 : RuntimeWordAt c4 (base + ⟨96⟩) s.d := by
    simpa [c4] using hp3.storeWordAboveScratch
      (value := s.d) hsmall (by omega) h96
  have hd5 := hd4.storeAboveScratch hp4 hsmall (stored := s.e)
    (by omega) h128 (by omega)
  have he5 : RuntimeWordAt c5 (base + ⟨128⟩) s.e := by
    simpa [c5] using hp4.storeWordAboveScratch
      (value := s.e) hsmall (by omega) h128
  change RuntimeLineAt c5 base s
  exact ⟨ha5, hb5, hc5, hd5, he5⟩

theorem RuntimeWordAt.runtimeInitLineCursor_below_padded {I : ExecutionEnv}
    {cursor : RuntimeMemCursor} {n baseOffset : Nat}
    {read value base : UInt256} {s : RuntimeLineState}
    (hword : RuntimeWordAt cursor read value)
    (hpadded : RuntimePaddedCursor I cursor n)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hbase : base.toNat = (hashScratchPtr I).toNat + baseOffset)
    (hoffset : baseOffset + 128 ≤ 832)
    (hbelow : read.toNat + 32 ≤ base.toNat) :
    RuntimeWordAt (runtimeInitLineCursor cursor base s) read value := by
  have addNat (offset : Nat) (hoff : baseOffset + offset ≤ 832) :
      (base + UInt256.ofNat offset).toNat =
        (hashScratchPtr I).toNat + (baseOffset + offset) := by
    rw [uadd_ofNat_toNat offset (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega) (by
        rw [hbase]
        have hu := hashScratchPtr_add_uint I hsmall
        omega)]
    omega
  have h32 : (base + ⟨32⟩).toNat =
      (hashScratchPtr I).toNat + (baseOffset + 32) := addNat 32 (by omega)
  have h64 : (base + ⟨64⟩).toNat =
      (hashScratchPtr I).toNat + (baseOffset + 64) := addNat 64 (by omega)
  have h96 : (base + ⟨96⟩).toNat =
      (hashScratchPtr I).toNat + (baseOffset + 96) := addNat 96 (by omega)
  have h128 : (base + ⟨128⟩).toNat =
      (hashScratchPtr I).toNat + (baseOffset + 128) := addNat 128 (by omega)
  let c1 := runtimeStoreCursor cursor base s.a
  let c2 := runtimeStoreCursor c1 (base + ⟨32⟩) s.b
  let c3 := runtimeStoreCursor c2 (base + ⟨64⟩) s.c
  let c4 := runtimeStoreCursor c3 (base + ⟨96⟩) s.d
  let c5 := runtimeStoreCursor c4 (base + ⟨128⟩) s.e
  have hp1 : RuntimePaddedCursor I c1 n :=
    hpadded.storeAboveScratch hsmall (by omega) hbase
  have hp2 : RuntimePaddedCursor I c2 n :=
    hp1.storeAboveScratch hsmall (by omega) h32
  have hp3 : RuntimePaddedCursor I c3 n :=
    hp2.storeAboveScratch hsmall (by omega) h64
  have hp4 : RuntimePaddedCursor I c4 n :=
    hp3.storeAboveScratch hsmall (by omega) h96
  have hw1 := hword.storeAboveScratch hpadded hsmall (stored := s.a)
    (by omega) hbase hbelow
  have hw2 := hw1.storeAboveScratch hp1 hsmall (stored := s.b)
    (by omega) h32 (by omega)
  have hw3 := hw2.storeAboveScratch hp2 hsmall (stored := s.c)
    (by omega) h64 (by omega)
  have hw4 := hw3.storeAboveScratch hp3 hsmall (stored := s.d)
    (by omega) h96 (by omega)
  have hw5 := hw4.storeAboveScratch hp4 hsmall (stored := s.e)
    (by omega) h128 (by omega)
  change RuntimeWordAt c5 read value
  exact hw5

end Ripemd160
