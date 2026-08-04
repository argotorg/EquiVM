import Examples.Precompiles.Ripemd160.HashWideInit

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Ripemd160

theorem RuntimeWordAt.afterLoadScratch {I : ExecutionEnv}
    {cursor : RuntimeMemCursor} {n offset : Nat}
    {read value addr : UInt256}
    (hword : RuntimeWordAt cursor read value)
    (hpadded : RuntimePaddedCursor I cursor n)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hoffset : offset ≤ 832)
    (haddr : addr.toNat = (hashScratchPtr I).toNat + offset) :
    RuntimeWordAt (runtimeLoadCursor cursor addr) read value := by
  apply hword.afterLoadWide hpadded.awSmall
  have hwide := hashScratchPtr_add_wide I hsmall
  omega

theorem RuntimeWordAt.runtimeRoundPreludeCursor_padded {I : ExecutionEnv}
    {cursor : RuntimeMemCursor} {n : Nat} {read value : UInt256}
    (hword : RuntimeWordAt cursor read value)
    (hpadded : RuntimePaddedCursor I cursor n)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RuntimeWordAt (runtimeRoundPreludeCursor cursor (hashScratchPtr I)) read value := by
  have h544 := hashScratchAdd_toNat I hsmall (by omega : 544 ≤ 895)
  have h576 := hashScratchAdd_toNat I hsmall (by omega : 576 ≤ 895)
  have h608 := hashScratchAdd_toNat I hsmall (by omega : 608 ≤ 895)
  let c1 := runtimeLoadCursor cursor (hashScratchPtr I + ⟨544⟩)
  let c2 := runtimeLoadCursor c1 (hashScratchPtr I + ⟨576⟩)
  have hp1 : RuntimePaddedCursor I c1 n :=
    hpadded.loadScratch hsmall (by omega) h544
  have hp2 : RuntimePaddedCursor I c2 n :=
    hp1.loadScratch hsmall (by omega) h576
  have hw1 : RuntimeWordAt c1 read value :=
    hword.afterLoadScratch hpadded hsmall (by omega) h544
  have hw2 : RuntimeWordAt c2 read value :=
    hw1.afterLoadScratch hp1 hsmall (by omega) h576
  have hw3 := hw2.afterLoadScratch hp2 hsmall (by omega) h608
  simpa [runtimeRoundPreludeCursor_eq_loads, c1, c2] using hw3

theorem RuntimeWordAt.runtimeRightPreludeCursor_padded {I : ExecutionEnv}
    {cursor : RuntimeMemCursor} {n : Nat} {read value : UInt256}
    (hword : RuntimeWordAt cursor read value)
    (hpadded : RuntimePaddedCursor I cursor n)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RuntimeWordAt (runtimeRightPreludeCursor cursor (hashScratchPtr I)) read value := by
  have h704 := hashScratchAdd_toNat I hsmall (by omega : 704 ≤ 895)
  have h736 := hashScratchAdd_toNat I hsmall (by omega : 736 ≤ 895)
  have h768 := hashScratchAdd_toNat I hsmall (by omega : 768 ≤ 895)
  let c1 := runtimeLoadCursor cursor (hashScratchPtr I + ⟨704⟩)
  let c2 := runtimeLoadCursor c1 (hashScratchPtr I + ⟨736⟩)
  have hp1 : RuntimePaddedCursor I c1 n :=
    hpadded.loadScratch hsmall (by omega) h704
  have hp2 : RuntimePaddedCursor I c2 n :=
    hp1.loadScratch hsmall (by omega) h736
  have hw1 : RuntimeWordAt c1 read value :=
    hword.afterLoadScratch hpadded hsmall (by omega) h704
  have hw2 : RuntimeWordAt c2 read value :=
    hw1.afterLoadScratch hp1 hsmall (by omega) h736
  have hw3 := hw2.afterLoadScratch hp2 hsmall (by omega) h768
  simpa [runtimeRightPreludeCursor_eq_loads, c1, c2] using hw3

theorem RuntimeWordAt.runtimeRoundReadCursor_padded {I : ExecutionEnv}
    {cursor : RuntimeMemCursor} {n lineOffset : Nat}
    {read value lineBase row round : UInt256}
    (hword : RuntimeWordAt cursor read value)
    (hpadded : RuntimePaddedCursor I cursor n)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hline : lineBase.toNat = (hashScratchPtr I).toNat + lineOffset)
    (hoffset : lineOffset + 191 ≤ 895) :
    RuntimeWordAt
      (runtimeRoundReadCursor cursor lineBase (hashScratchPtr I) row round)
      read value := by
  have addNat (offset : Nat) (hoff : lineOffset + offset ≤ 895) :
      (lineBase + UInt256.ofNat offset).toNat =
        (hashScratchPtr I).toNat + (lineOffset + offset) := by
    rw [uadd_ofNat_toNat offset (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega) (by
        rw [hline]
        have hu := hashScratchPtr_add_uint I hsmall
        omega)]
    omega
  have h32 := addNat 32 (by omega)
  have h64 := addNat 64 (by omega)
  have h96 := addNat 96 (by omega)
  have h128 := addNat 128 (by omega)
  have huint : (hashScratchPtr I).toNat + 512 < UInt256.size :=
    lt_of_le_of_lt (Nat.add_le_add_left (by omega : 512 ≤ 895) _)
      (hashScratchPtr_add_uint I hsmall)
  have hmsg :
      (runtimeRoundMessageAddr (hashScratchPtr I) row round).toNat =
        (hashScratchPtr I).toNat + 32 * (runtimeRowEntry row round).toNat :=
    runtimeRoundMessageAddr_toNat huint
  let c1 := runtimeLoadCursor cursor lineBase
  let c2 := runtimeLoadCursor c1 (lineBase + ⟨32⟩)
  let c3 := runtimeLoadCursor c2 (lineBase + ⟨64⟩)
  let c4 := runtimeLoadCursor c3 (lineBase + ⟨96⟩)
  let c5 := runtimeLoadCursor c4 (lineBase + ⟨128⟩)
  have hp1 := hpadded.loadScratch hsmall (by omega) hline
  have hp2 := hp1.loadScratch hsmall (by omega) h32
  have hp3 := hp2.loadScratch hsmall (by omega) h64
  have hp4 := hp3.loadScratch hsmall (by omega) h96
  have hp5 := hp4.loadScratch hsmall (by omega) h128
  have hw1 : RuntimeWordAt c1 read value :=
    hword.afterLoadScratch hpadded hsmall (by omega) hline
  have hw2 : RuntimeWordAt c2 read value :=
    hw1.afterLoadScratch hp1 hsmall (by omega) h32
  have hw3 : RuntimeWordAt c3 read value :=
    hw2.afterLoadScratch hp2 hsmall (by omega) h64
  have hw4 : RuntimeWordAt c4 read value :=
    hw3.afterLoadScratch hp3 hsmall (by omega) h96
  have hw5 : RuntimeWordAt c5 read value :=
    hw4.afterLoadScratch hp4 hsmall (by omega) h128
  have hw6 := hw5.afterLoadScratch hp5 hsmall
    (by have hr := runtimeRowEntry_lt_sixteen row round; omega) hmsg
  simpa [runtimeRoundReadCursor, c1, c2, c3, c4, c5] using hw6

theorem RuntimeWordAt.runtimeRoundCursor_below_padded {I : ExecutionEnv}
    {cursor : RuntimeMemCursor} {n lineOffset : Nat}
    {read value lineBase round row rotationRow boolF constant : UInt256}
    (hword : RuntimeWordAt cursor read value)
    (hpadded : RuntimePaddedCursor I cursor n)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hline : lineBase.toNat = (hashScratchPtr I).toNat + lineOffset)
    (hoffset : lineOffset + 191 ≤ 895)
    (hbelow : read.toNat + 32 ≤ lineBase.toNat) :
    RuntimeWordAt
      (runtimeRoundCursor cursor lineBase (hashScratchPtr I)
        round row rotationRow boolF constant) read value := by
  have addNat (offset : Nat) (hoff : lineOffset + offset ≤ 895) :
      (lineBase + UInt256.ofNat offset).toNat =
        (hashScratchPtr I).toNat + (lineOffset + offset) := by
    rw [uadd_ofNat_toNat offset (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega) (by
        rw [hline]
        have hu := hashScratchPtr_add_uint I hsmall
        omega)]
    omega
  have h32 := addNat 32 (by omega)
  have h64 := addNat 64 (by omega)
  have h96 := addNat 96 (by omega)
  have h128 := addNat 128 (by omega)
  let c0 : RuntimeMemCursor :=
    { mem := cursor.mem,
      aw := runtimeRoundAwX cursor lineBase (hashScratchPtr I) row round }
  let c1 := runtimeStoreCursor c0 lineBase (runtimeRoundE cursor lineBase)
  let c2 := runtimeStoreCursor c1 (lineBase + ⟨128⟩) (runtimeRoundD cursor lineBase)
  let c3 := runtimeStoreCursor c2 (lineBase + ⟨96⟩)
    (runtimeRol32 (runtimeRoundC cursor lineBase) ⟨10⟩)
  let c4 := runtimeStoreCursor c3 (lineBase + ⟨64⟩) (runtimeRoundB cursor lineBase)
  let c5 := runtimeStoreCursor c4 (lineBase + ⟨32⟩)
    (runtimeRoundNext cursor lineBase (hashScratchPtr I)
      round row rotationRow boolF constant)
  have hp0 : RuntimePaddedCursor I c0 n := by
    simpa [c0, runtimeRoundReadCursor_mem, runtimeRoundReadCursor_aw] using
      Ripemd160.runtimeRoundReadCursor_padded hpadded hsmall hline hoffset
        (row := row) (round := round)
  have hp1 : RuntimePaddedCursor I c1 n :=
    hp0.storeAboveScratch (value := runtimeRoundE cursor lineBase)
      hsmall (by omega) hline
  have hp2 : RuntimePaddedCursor I c2 n :=
    hp1.storeAboveScratch (value := runtimeRoundD cursor lineBase)
      hsmall (by omega) h128
  have hp3 : RuntimePaddedCursor I c3 n :=
    hp2.storeAboveScratch
      (value := runtimeRol32 (runtimeRoundC cursor lineBase) ⟨10⟩)
      hsmall (by omega) h96
  have hp4 : RuntimePaddedCursor I c4 n :=
    hp3.storeAboveScratch (value := runtimeRoundB cursor lineBase)
      hsmall (by omega) h64
  have hw0 : RuntimeWordAt c0 read value := by
    simpa [c0, runtimeRoundReadCursor_mem, runtimeRoundReadCursor_aw] using
      hword.runtimeRoundReadCursor_padded hpadded hsmall hline hoffset
        (row := row) (round := round)
  have hw1 := hw0.storeAboveScratch hp0 hsmall
    (stored := runtimeRoundE cursor lineBase) (by omega) hline hbelow
  have hw2 := hw1.storeAboveScratch hp1 hsmall
    (stored := runtimeRoundD cursor lineBase) (by omega) h128 (by omega)
  have hw3 := hw2.storeAboveScratch hp2 hsmall
    (stored := runtimeRol32 (runtimeRoundC cursor lineBase) ⟨10⟩)
    (by omega) h96 (by omega)
  have hw4 := hw3.storeAboveScratch hp3 hsmall
    (stored := runtimeRoundB cursor lineBase) (by omega) h64 (by omega)
  have hw5 := hw4.storeAboveScratch hp4 hsmall
    (stored := runtimeRoundNext cursor lineBase (hashScratchPtr I)
      round row rotationRow boolF constant) (by omega) h32 (by omega)
  change RuntimeWordAt c5 read value
  exact hw5

end Ripemd160
