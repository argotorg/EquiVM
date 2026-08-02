import Examples.Ripemd160.HashWideValues

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Ripemd160

theorem runtimeRoundCursor_line_padded {I : ExecutionEnv}
    {cursor : RuntimeMemCursor} {n lineOffset : Nat}
    {lineBase round row rotationRow boolF constant : UInt256}
    {X : Fin 16 → UInt256} {s : RuntimeLineState}
    (hpadded : RuntimePaddedCursor I cursor n)
    (hmessage : RuntimeMessageAt cursor (hashScratchPtr I) X)
    (hline : RuntimeLineAt cursor lineBase s)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hlineBase : lineBase.toNat = (hashScratchPtr I).toNat + lineOffset)
    (hoffset : lineOffset + 191 ≤ 895) :
    RuntimeLineAt
      (runtimeRoundCursor cursor lineBase (hashScratchPtr I)
        round row rotationRow boolF constant)
      lineBase
      (runtimePureRound s
        (X ⟨(runtimeRowEntry row round).toNat, runtimeRowEntry_lt_sixteen row round⟩)
        round row rotationRow boolF constant) := by
  have addNat (offset : Nat) (hoff : lineOffset + offset ≤ 895) :
      (lineBase + UInt256.ofNat offset).toNat =
        (hashScratchPtr I).toNat + (lineOffset + offset) := by
    rw [uadd_ofNat_toNat offset (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega) (by
        rw [hlineBase]
        have hu := hashScratchPtr_add_uint I hsmall
        omega)]
    omega
  have h32 : (lineBase + ⟨32⟩).toNat =
      (hashScratchPtr I).toNat + (lineOffset + 32) := by
    simpa using addNat 32 (by omega)
  have h64 : (lineBase + ⟨64⟩).toNat =
      (hashScratchPtr I).toNat + (lineOffset + 64) := by
    simpa using addNat 64 (by omega)
  have h96 : (lineBase + ⟨96⟩).toNat =
      (hashScratchPtr I).toNat + (lineOffset + 96) := by
    simpa using addNat 96 (by omega)
  have h128 : (lineBase + ⟨128⟩).toNat =
      (hashScratchPtr I).toNat + (lineOffset + 128) := by
    simpa using addNat 128 (by omega)
  rcases runtimeRoundValues_padded (row := row) (round := round)
      hpadded hmessage hline hsmall hlineBase hoffset with
    ⟨ha, hb, hcv, hd, he, hx⟩
  have hnext :
      runtimeRoundNext cursor lineBase (hashScratchPtr I)
          round row rotationRow boolF constant =
        runtimePureRoundNext s
          (X ⟨(runtimeRowEntry row round).toNat, runtimeRowEntry_lt_sixteen row round⟩)
          round row rotationRow boolF constant := by
    simp [runtimeRoundNext, runtimeRoundSum, runtimePureRoundNext,
      ha, hb, hcv, hd, he, hx]
  have hp0 := runtimeRoundReadCursor_padded hpadded hsmall hlineBase hoffset
    (row := row) (round := round)
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
  have hpc0 : RuntimePaddedCursor I c0 n := by
    simpa [c0, runtimeRoundReadCursor_mem, runtimeRoundReadCursor_aw] using hp0
  have hpc1 : RuntimePaddedCursor I c1 n :=
    hpc0.storeAboveScratch hsmall (by omega) hlineBase
  have hpc2 : RuntimePaddedCursor I c2 n :=
    hpc1.storeAboveScratch hsmall (by omega) h128
  have hpc3 : RuntimePaddedCursor I c3 n :=
    hpc2.storeAboveScratch hsmall (by omega) h96
  have hpc4 : RuntimePaddedCursor I c4 n :=
    hpc3.storeAboveScratch hsmall (by omega) h64
  have ha1 : RuntimeWordAt c1 lineBase s.e := by
    simpa [c1, he] using hpc0.storeWordAboveScratch
      (value := runtimeRoundE cursor lineBase) hsmall (by omega) hlineBase
  have ha2 := ha1.storeAboveScratch hpc1 hsmall
    (stored := runtimeRoundD cursor lineBase) (by omega) h128 (by omega)
  have ha3 := ha2.storeAboveScratch hpc2 hsmall
    (stored := runtimeRol32 (runtimeRoundC cursor lineBase) ⟨10⟩)
    (by omega) h96 (by omega)
  have ha4 := ha3.storeAboveScratch hpc3 hsmall
    (stored := runtimeRoundB cursor lineBase) (by omega) h64 (by omega)
  have ha5 := ha4.storeAboveScratch hpc4 hsmall
    (stored := runtimeRoundNext cursor lineBase (hashScratchPtr I)
      round row rotationRow boolF constant) (by omega) h32 (by omega)
  have he2 : RuntimeWordAt c2 (lineBase + ⟨128⟩) s.d := by
    simpa [c2, hd] using hpc1.storeWordAboveScratch
      (value := runtimeRoundD cursor lineBase) hsmall (by omega) h128
  have he3 := he2.storeBelowScratch hpc2 hsmall
    (stored := runtimeRol32 (runtimeRoundC cursor lineBase) ⟨10⟩)
    (by omega) h96 (by omega)
  have he4 := he3.storeBelowScratch hpc3 hsmall
    (stored := runtimeRoundB cursor lineBase) (by omega) h64 (by omega)
  have he5 := he4.storeBelowScratch hpc4 hsmall
    (stored := runtimeRoundNext cursor lineBase (hashScratchPtr I)
      round row rotationRow boolF constant) (by omega) h32 (by omega)
  have hd3 : RuntimeWordAt c3 (lineBase + ⟨96⟩) (runtimeRol32 s.c ⟨10⟩) := by
    simpa [c3, hcv] using hpc2.storeWordAboveScratch
      (value := runtimeRol32 (runtimeRoundC cursor lineBase) ⟨10⟩)
      hsmall (by omega) h96
  have hd4 := hd3.storeBelowScratch hpc3 hsmall
    (stored := runtimeRoundB cursor lineBase) (by omega) h64 (by omega)
  have hd5 := hd4.storeBelowScratch hpc4 hsmall
    (stored := runtimeRoundNext cursor lineBase (hashScratchPtr I)
      round row rotationRow boolF constant) (by omega) h32 (by omega)
  have hc4 : RuntimeWordAt c4 (lineBase + ⟨64⟩) s.b := by
    simpa [c4, hb] using hpc3.storeWordAboveScratch
      (value := runtimeRoundB cursor lineBase) hsmall (by omega) h64
  have hc5 := hc4.storeBelowScratch hpc4 hsmall
    (stored := runtimeRoundNext cursor lineBase (hashScratchPtr I)
      round row rotationRow boolF constant) (by omega) h32 (by omega)
  have hb5 : RuntimeWordAt c5 (lineBase + ⟨32⟩)
      (runtimePureRoundNext s
        (X ⟨(runtimeRowEntry row round).toNat, runtimeRowEntry_lt_sixteen row round⟩)
        round row rotationRow boolF constant) := by
    simpa [c5, hnext] using hpc4.storeWordAboveScratch
      (value := runtimeRoundNext cursor lineBase (hashScratchPtr I)
        round row rotationRow boolF constant) hsmall (by omega) h32
  have hout :
      runtimeRoundCursor cursor lineBase (hashScratchPtr I)
          round row rotationRow boolF constant = c5 := by
    simp [runtimeRoundCursor, c0, c1, c2, c3, c4, c5,
      ha, hb, hcv, hd, he, hx, hnext]
  rw [hout]
  change RuntimeWordAt c5 lineBase s.e ∧
    RuntimeWordAt c5 (lineBase + ⟨32⟩)
      (runtimePureRoundNext s
        (X ⟨(runtimeRowEntry row round).toNat, runtimeRowEntry_lt_sixteen row round⟩)
        round row rotationRow boolF constant) ∧
    RuntimeWordAt c5 (lineBase + ⟨64⟩) s.b ∧
    RuntimeWordAt c5 (lineBase + ⟨96⟩) (runtimeRol32 s.c ⟨10⟩) ∧
    RuntimeWordAt c5 (lineBase + ⟨128⟩) s.d
  exact ⟨ha5, hb5, hc5, hd5, he5⟩

end Ripemd160
