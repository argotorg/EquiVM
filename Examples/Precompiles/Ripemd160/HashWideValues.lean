import Examples.Precompiles.Ripemd160.ParserMessage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Ripemd160

theorem runtimeRoundValues_padded {I : ExecutionEnv}
    {cursor : RuntimeMemCursor} {n lineOffset : Nat}
    {lineBase row round : UInt256} {X : Fin 16 → UInt256} {s : RuntimeLineState}
    (hpadded : RuntimePaddedCursor I cursor n)
    (hmessage : RuntimeMessageAt cursor (hashScratchPtr I) X)
    (hline : RuntimeLineAt cursor lineBase s)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hlineBase : lineBase.toNat = (hashScratchPtr I).toNat + lineOffset)
    (hoffset : lineOffset + 191 ≤ 895) :
    runtimeRoundA cursor lineBase = s.a ∧
    runtimeRoundB cursor lineBase = s.b ∧
    runtimeRoundC cursor lineBase = s.c ∧
    runtimeRoundD cursor lineBase = s.d ∧
    runtimeRoundE cursor lineBase = s.e ∧
    runtimeRoundX cursor lineBase (hashScratchPtr I) row round =
      X ⟨(runtimeRowEntry row round).toNat, runtimeRowEntry_lt_sixteen row round⟩ := by
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
  have hb0 := hline.2.1.afterLoadWide hpadded.awSmall
    (addr := lineBase) (by
      rw [hlineBase]
      have hw := hashScratchPtr_add_wide I hsmall
      omega)
  have hp1 := hpadded.loadScratch hsmall (by omega) hlineBase
  have hc0 := hline.2.2.1.afterLoadWide hpadded.awSmall
    (addr := lineBase) (by
      rw [hlineBase]
      have hw := hashScratchPtr_add_wide I hsmall
      omega)
  have hc1 := hc0.afterLoadWide hp1.awSmall
    (addr := lineBase + ⟨32⟩) (by
      rw [h32]
      have hw := hashScratchPtr_add_wide I hsmall
      omega)
  have hp2 := hp1.loadScratch hsmall (by omega) (addNat 32 (by omega))
  have hd0 := hline.2.2.2.1.afterLoadWide hpadded.awSmall
    (addr := lineBase) (by
      rw [hlineBase]
      have hw := hashScratchPtr_add_wide I hsmall
      omega)
  have hd1 := hd0.afterLoadWide hp1.awSmall
    (addr := lineBase + ⟨32⟩) (by
      rw [h32]
      have hw := hashScratchPtr_add_wide I hsmall
      omega)
  have hd2 := hd1.afterLoadWide hp2.awSmall
    (addr := lineBase + ⟨64⟩) (by
      rw [h64]
      have hw := hashScratchPtr_add_wide I hsmall
      omega)
  have hp3 := hp2.loadScratch hsmall (by omega) (addNat 64 (by omega))
  have he0 := hline.2.2.2.2.afterLoadWide hpadded.awSmall
    (addr := lineBase) (by
      rw [hlineBase]
      have hw := hashScratchPtr_add_wide I hsmall
      omega)
  have he1 := he0.afterLoadWide hp1.awSmall
    (addr := lineBase + ⟨32⟩) (by
      rw [h32]
      have hw := hashScratchPtr_add_wide I hsmall
      omega)
  have he2 := he1.afterLoadWide hp2.awSmall
    (addr := lineBase + ⟨64⟩) (by
      rw [h64]
      have hw := hashScratchPtr_add_wide I hsmall
      omega)
  have he3 := he2.afterLoadWide hp3.awSmall
    (addr := lineBase + ⟨96⟩) (by
      rw [h96]
      have hw := hashScratchPtr_add_wide I hsmall
      omega)
  have hp4 := hp3.loadScratch hsmall (by omega) (addNat 96 (by omega))
  have huint : (hashScratchPtr I).toNat + 512 < UInt256.size :=
    lt_of_le_of_lt (Nat.add_le_add_left (by omega : 512 ≤ 895) _)
      (hashScratchPtr_add_uint I hsmall)
  have hx := hmessage.selected (row := row) (round := round) huint
  have hx0 := hx.afterLoadWide hpadded.awSmall (addr := lineBase) (by
    rw [hlineBase]
    have hw := hashScratchPtr_add_wide I hsmall
    omega)
  have hx1 := hx0.afterLoadWide hp1.awSmall (addr := lineBase + ⟨32⟩) (by
    rw [h32]
    have hw := hashScratchPtr_add_wide I hsmall
    omega)
  have hx2 := hx1.afterLoadWide hp2.awSmall (addr := lineBase + ⟨64⟩) (by
    rw [h64]
    have hw := hashScratchPtr_add_wide I hsmall
    omega)
  have hx3 := hx2.afterLoadWide hp3.awSmall (addr := lineBase + ⟨96⟩) (by
    rw [h96]
    have hw := hashScratchPtr_add_wide I hsmall
    omega)
  have hx4 := hx3.afterLoadWide hp4.awSmall (addr := lineBase + ⟨128⟩) (by
    rw [h128]
    have hw := hashScratchPtr_add_wide I hsmall
    omega)
  refine ⟨hline.1.load, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [runtimeRoundB, runtimeRoundAwA, runtimeLoadCursor] using hb0.load
  · simpa [runtimeRoundC, runtimeRoundAwB, runtimeRoundAwA, runtimeLoadCursor] using hc1.load
  · simpa [runtimeRoundD, runtimeRoundAwC, runtimeRoundAwB, runtimeRoundAwA,
      runtimeLoadCursor] using hd2.load
  · simpa [runtimeRoundE, runtimeRoundAwD, runtimeRoundAwC, runtimeRoundAwB,
      runtimeRoundAwA, runtimeLoadCursor] using he3.load
  · simpa [runtimeRoundX, runtimeRoundAwE, runtimeRoundAwD, runtimeRoundAwC,
      runtimeRoundAwB, runtimeRoundAwA, runtimeLoadCursor] using hx4.load

end Ripemd160
