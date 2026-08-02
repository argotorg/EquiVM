import Examples.Ripemd160.HashWidePreserve

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Ripemd160

theorem runtimeLeftPrelude_values_padded {I : ExecutionEnv}
    {cursor : RuntimeMemCursor} {n : Nat} {s : RuntimeLineState}
    (hpadded : RuntimePaddedCursor I cursor n)
    (hline : RuntimeLineAt cursor (hashScratchPtr I + ⟨512⟩) s)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    runtimePreludeB cursor (hashScratchPtr I) = s.b ∧
    runtimePreludeC cursor (hashScratchPtr I) = s.c ∧
    runtimePreludeD cursor (hashScratchPtr I) = s.d := by
  have hwB : RuntimeWordAt cursor (hashScratchPtr I + ⟨544⟩) s.b := by
    simpa [u256_add_assoc,
      show (⟨512⟩ : UInt256) + ⟨32⟩ = ⟨544⟩ by native_decide] using hline.2.1
  have hwC : RuntimeWordAt cursor (hashScratchPtr I + ⟨576⟩) s.c := by
    simpa [u256_add_assoc,
      show (⟨512⟩ : UInt256) + ⟨64⟩ = ⟨576⟩ by native_decide] using hline.2.2.1
  have hwD : RuntimeWordAt cursor (hashScratchPtr I + ⟨608⟩) s.d := by
    simpa [u256_add_assoc,
      show (⟨512⟩ : UInt256) + ⟨96⟩ = ⟨608⟩ by native_decide] using hline.2.2.2.1
  have h544 := hashScratchAdd_toNat I hsmall (by omega : 544 ≤ 895)
  have h576 := hashScratchAdd_toNat I hsmall (by omega : 576 ≤ 895)
  let c1 := runtimeLoadCursor cursor (hashScratchPtr I + ⟨544⟩)
  let c2 := runtimeLoadCursor c1 (hashScratchPtr I + ⟨576⟩)
  have hp1 : RuntimePaddedCursor I c1 n :=
    hpadded.loadScratch hsmall (by omega) h544
  have hwC1 : RuntimeWordAt c1 (hashScratchPtr I + ⟨576⟩) s.c :=
    hwC.afterLoadScratch hpadded hsmall (by omega) h544
  have hwD1 : RuntimeWordAt c1 (hashScratchPtr I + ⟨608⟩) s.d :=
    hwD.afterLoadScratch hpadded hsmall (by omega) h544
  have hwD2 : RuntimeWordAt c2 (hashScratchPtr I + ⟨608⟩) s.d :=
    hwD1.afterLoadScratch hp1 hsmall (by omega) h576
  constructor
  · exact hwB.load
  constructor
  · simpa [runtimePreludeC, runtimeLoadCursor, c1] using hwC1.load
  · simpa [runtimePreludeD, runtimeLoadCursor, c1, c2] using hwD2.load

theorem runtimeRightPrelude_values_padded {I : ExecutionEnv}
    {cursor : RuntimeMemCursor} {n : Nat} {s : RuntimeLineState}
    (hpadded : RuntimePaddedCursor I cursor n)
    (hline : RuntimeLineAt cursor (hashScratchPtr I + ⟨672⟩) s)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    runtimeRightPreludeB cursor (hashScratchPtr I) = s.b ∧
    runtimeRightPreludeC cursor (hashScratchPtr I) = s.c ∧
    runtimeRightPreludeD cursor (hashScratchPtr I) = s.d := by
  have hwB : RuntimeWordAt cursor (hashScratchPtr I + ⟨704⟩) s.b := by
    simpa [u256_add_assoc,
      show (⟨672⟩ : UInt256) + ⟨32⟩ = ⟨704⟩ by native_decide] using hline.2.1
  have hwC : RuntimeWordAt cursor (hashScratchPtr I + ⟨736⟩) s.c := by
    simpa [u256_add_assoc,
      show (⟨672⟩ : UInt256) + ⟨64⟩ = ⟨736⟩ by native_decide] using hline.2.2.1
  have hwD : RuntimeWordAt cursor (hashScratchPtr I + ⟨768⟩) s.d := by
    simpa [u256_add_assoc,
      show (⟨672⟩ : UInt256) + ⟨96⟩ = ⟨768⟩ by native_decide] using hline.2.2.2.1
  have h704 := hashScratchAdd_toNat I hsmall (by omega : 704 ≤ 895)
  have h736 := hashScratchAdd_toNat I hsmall (by omega : 736 ≤ 895)
  let c1 := runtimeLoadCursor cursor (hashScratchPtr I + ⟨704⟩)
  let c2 := runtimeLoadCursor c1 (hashScratchPtr I + ⟨736⟩)
  have hp1 : RuntimePaddedCursor I c1 n :=
    hpadded.loadScratch hsmall (by omega) h704
  have hwC1 : RuntimeWordAt c1 (hashScratchPtr I + ⟨736⟩) s.c :=
    hwC.afterLoadScratch hpadded hsmall (by omega) h704
  have hwD1 : RuntimeWordAt c1 (hashScratchPtr I + ⟨768⟩) s.d :=
    hwD.afterLoadScratch hpadded hsmall (by omega) h704
  have hwD2 : RuntimeWordAt c2 (hashScratchPtr I + ⟨768⟩) s.d :=
    hwD1.afterLoadScratch hp1 hsmall (by omega) h736
  constructor
  · exact hwB.load
  constructor
  · simpa [runtimeRightPreludeC, runtimeLoadCursor, c1] using hwC1.load
  · simpa [runtimeRightPreludeD, runtimeLoadCursor, c1, c2] using hwD2.load

theorem runtimeLeftRoundCursor_line_padded {I : ExecutionEnv}
    {cursor : RuntimeMemCursor} {n group round : Nat}
    {X : Fin 16 → UInt256} {s : RuntimeLineState}
    (hpadded : RuntimePaddedCursor I cursor n)
    (hmessage : RuntimeMessageAt cursor (hashScratchPtr I) X)
    (hline : RuntimeLineAt cursor (hashScratchPtr I + ⟨512⟩) s)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RuntimeLineAt
      (runtimeLeftRoundCursor cursor (hashScratchPtr I) group round)
      (hashScratchPtr I + ⟨512⟩)
      (runtimePureLeftRound X group round s) := by
  let pre := runtimeRoundPreludeCursor cursor (hashScratchPtr I)
  have hp : RuntimePaddedCursor I pre n := runtimeRoundPreludeCursor_padded hpadded hsmall
  have hm : RuntimeMessageAt pre (hashScratchPtr I) X := fun i =>
    (hmessage i).runtimeRoundPreludeCursor_padded hpadded hsmall
  have hl : RuntimeLineAt pre (hashScratchPtr I + ⟨512⟩) s :=
    ⟨hline.1.runtimeRoundPreludeCursor_padded hpadded hsmall,
      hline.2.1.runtimeRoundPreludeCursor_padded hpadded hsmall,
      hline.2.2.1.runtimeRoundPreludeCursor_padded hpadded hsmall,
      hline.2.2.2.1.runtimeRoundPreludeCursor_padded hpadded hsmall,
      hline.2.2.2.2.runtimeRoundPreludeCursor_padded hpadded hsmall⟩
  rcases runtimeLeftPrelude_values_padded hpadded hline hsmall with ⟨hB, hC, hD⟩
  have hr := runtimeRoundCursor_line_padded (lineOffset := 512) hp hm hl hsmall
    (hashScratchAdd_toNat I hsmall (by omega : 512 ≤ 895)) (by omega)
    (round := UInt256.ofNat round) (row := leftWordRowWord group)
    (rotationRow := leftRotationRowWord group)
    (boolF := runtimeLeftF group (runtimePreludeB cursor (hashScratchPtr I))
      (runtimePreludeC cursor (hashScratchPtr I))
      (runtimePreludeD cursor (hashScratchPtr I)))
    (constant := leftConstantWord group)
  simpa [runtimeLeftRoundCursor, pre, runtimePureLeftRound, hB, hC, hD] using hr

theorem runtimeRightRoundCursor_line_padded {I : ExecutionEnv}
    {cursor : RuntimeMemCursor} {n group round : Nat}
    {X : Fin 16 → UInt256} {s : RuntimeLineState}
    (hpadded : RuntimePaddedCursor I cursor n)
    (hmessage : RuntimeMessageAt cursor (hashScratchPtr I) X)
    (hline : RuntimeLineAt cursor (hashScratchPtr I + ⟨672⟩) s)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RuntimeLineAt
      (runtimeRightRoundCursor cursor (hashScratchPtr I) group round)
      (hashScratchPtr I + ⟨672⟩)
      (runtimePureRightRound X group round s) := by
  let pre := runtimeRightPreludeCursor cursor (hashScratchPtr I)
  have hp : RuntimePaddedCursor I pre n := runtimeRightPreludeCursor_padded hpadded hsmall
  have hm : RuntimeMessageAt pre (hashScratchPtr I) X := fun i =>
    (hmessage i).runtimeRightPreludeCursor_padded hpadded hsmall
  have hl : RuntimeLineAt pre (hashScratchPtr I + ⟨672⟩) s :=
    ⟨hline.1.runtimeRightPreludeCursor_padded hpadded hsmall,
      hline.2.1.runtimeRightPreludeCursor_padded hpadded hsmall,
      hline.2.2.1.runtimeRightPreludeCursor_padded hpadded hsmall,
      hline.2.2.2.1.runtimeRightPreludeCursor_padded hpadded hsmall,
      hline.2.2.2.2.runtimeRightPreludeCursor_padded hpadded hsmall⟩
  rcases runtimeRightPrelude_values_padded hpadded hline hsmall with ⟨hB, hC, hD⟩
  have hr := runtimeRoundCursor_line_padded (lineOffset := 672) hp hm hl hsmall
    (hashScratchAdd_toNat I hsmall (by omega : 672 ≤ 895)) (by omega)
    (round := UInt256.ofNat round) (row := rightWordRowWord group)
    (rotationRow := rightRotationRowWord group)
    (boolF := runtimeRightF group (runtimeRightPreludeB cursor (hashScratchPtr I))
      (runtimeRightPreludeC cursor (hashScratchPtr I))
      (runtimeRightPreludeD cursor (hashScratchPtr I)))
    (constant := rightConstantWord group)
  simpa [runtimeRightRoundCursor, pre, runtimePureRightRound, hB, hC, hD] using hr

end Ripemd160
