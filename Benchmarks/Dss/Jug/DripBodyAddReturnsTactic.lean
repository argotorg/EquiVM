import Benchmarks.Dss.Jug.DripBodyNZeroTactic
import Mathlib.Util.ParseCommand
import Lean.Elab.Tactic

open Lean Elab Tactic
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Jug

set_option maxHeartbeats 1000000

private def jugDripAddReturnsScript : String := r#"
obtain ⟨_, _, rd1485⟩ := RD.jugDripAddReturns haddOverflow _rd2131
obtain ⟨_, _, _rd2153⟩ := RD.jugDripToRpowRoutine hsz36 hlo hout rd1485
let fee :=
  jugSlotWord ⟨4⟩ σ' I + jugSlotWord (fileDutyDutySlotFor I) σ' I
let age :=
  UInt256.sub (UInt256.ofNat I.header.timestamp)
    (jugSlotWord (fileDutyRhoSlotFor I) σ' I)
have _rpowNZeroProgress :
    age = ⟨0⟩ →
      ∃ k' C', RD jugBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1524⟩
        (jugRay :: ⟨1530⟩ :: dripVatIlksPrevWord out :: ⟨0⟩ ::
          fileDutyIlkWord I :: ⟨357⟩ :: jugSelWord I :: [])
        (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
          (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
            (dripVatIlksPostCallMem I out)))
        (UInt256.ofNat 6) out (cA', σ') k' C' := by
  intro hage0
  have rd2153Zero := by
    simpa [fee, age, hage0] using _rd2153
  exact RD.jugDripRpowNZeroReturns
    (R := [⟨1530⟩, dripVatIlksPrevWord out, ⟨0⟩, fileDutyIlkWord I,
      ⟨357⟩, jugSelWord I])
    (by simp) rd2153Zero
have _rpowRmulNZeroProgress :
    age = ⟨0⟩ →
      jugRay.toNat * (dripVatIlksPrevWord out).toNat < UInt256.size →
        ∃ k' C', RD jugBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1530⟩
          (dripVatIlksPrevWord out :: dripVatIlksPrevWord out :: ⟨0⟩ ::
            fileDutyIlkWord I :: ⟨357⟩ :: jugSelWord I :: [])
          (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
            (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
              (dripVatIlksPostCallMem I out)))
          (UInt256.ofNat 6) out (cA', σ') k' C' := by
  intro hage0 hfitRmul
  obtain ⟨_, _, rd1524⟩ := _rpowNZeroProgress hage0
  exact RD.jugDripRmulRayReturns
    (R := [⟨0⟩, fileDutyIlkWord I, ⟨357⟩, jugSelWord I])
    (by simp) hfitRmul rd1524
have _diffNZeroBoundRevert :
    age = ⟨0⟩ →
      jugRay.toNat * (dripVatIlksPrevWord out).toNat < UInt256.size →
        ¬ ((dripVatIlksPrevWord out).toNat : Int) ≤ maxInt256 →
          RDrev jugBytecode (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
  intro hage0 hfitRmul hprevMaxNot
  obtain ⟨_, _, rd1530⟩ := _rpowRmulNZeroProgress hage0 hfitRmul
  obtain ⟨_, _, rd2397⟩ := RD.jugDripToDiffRoutine rd1530
  exact RD.jugDiffSameRevertXBound
    (R := [dripVowTargetWord σ' I, fileDutyIlkWord I,
      dripVatFoldSelectorWord, dripVatTargetWord σ' I,
      dripVatIlksPrevWord out, dripVatIlksPrevWord out, fileDutyIlkWord I,
      ⟨357⟩, jugSelWord I])
    (by simp) hprevMaxNot (by simpa using rd2397)
have _diffNZeroProgress :
    age = ⟨0⟩ →
      jugRay.toNat * (dripVatIlksPrevWord out).toNat < UInt256.size →
        ((dripVatIlksPrevWord out).toNat : Int) ≤ maxInt256 →
          ∃ k' C', RD jugBytecode I (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1570⟩
            (⟨0⟩ :: dripVowTargetWord σ' I :: fileDutyIlkWord I ::
              dripVatFoldSelectorWord :: dripVatTargetWord σ' I ::
              dripVatIlksPrevWord out :: dripVatIlksPrevWord out ::
              fileDutyIlkWord I :: ⟨357⟩ :: jugSelWord I :: [])
            (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
              (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
                (dripVatIlksPostCallMem I out)))
            (UInt256.ofNat 6) out (cA', σ') k' C' := by
  intro hage0 hfitRmul hprevMax
  obtain ⟨_, _, rd1530⟩ := _rpowRmulNZeroProgress hage0 hfitRmul
  obtain ⟨_, _, rd2397⟩ := RD.jugDripToDiffRoutine rd1530
  exact RD.jugDiffSameReturnsZero
    (R := [dripVowTargetWord σ' I, fileDutyIlkWord I,
      dripVatFoldSelectorWord, dripVatTargetWord σ' I,
      dripVatIlksPrevWord out, dripVatIlksPrevWord out, fileDutyIlkWord I,
      ⟨357⟩, jugSelWord I])
    (by simp) hprevMax (by simpa using rd2397)
have _foldNZeroCallReady :
    age = ⟨0⟩ →
      jugRay.toNat * (dripVatIlksPrevWord out).toNat < UInt256.size →
        ((dripVatIlksPrevWord out).toNat : Int) ≤ maxInt256 →
          Reasoning.Theory.extCodeSizeWord σ'
            (dripVatTargetWord σ' I) ≠ ⟨0⟩ →
            ∃ gasWord k' C', RD jugBytecode I (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1650⟩
              (gasWord :: dripVatTargetWord σ' I :: ⟨0⟩ ::
                dripVatFoldOutPtr :: dripVatFoldInSize :: dripVatFoldOutPtr ::
                ⟨0⟩ :: dripVatFoldEndPtr :: dripVatFoldSelectorWord ::
                dripVatTargetWord σ' I :: dripVatIlksPrevWord out ::
                dripVatIlksPrevWord out :: fileDutyIlkWord I :: ⟨357⟩ ::
                jugSelWord I :: [])
              (dripVatFoldCalldataMem σ' I ⟨0⟩
                (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
                  (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
                    (dripVatIlksPostCallMem I out))))
              (UInt256.ofNat 8) out (cA', σ') k' C' := by
  intro hage0 hfitRmul hprevMax hfoldCode
  let foldBaseMem :=
    twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
      (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
        (dripVatIlksPostCallMem I out))
  have hpostSize : (dripVatIlksPostCallMem I out).size = 192 :=
    dripVatIlksPostCallMem_size_long I out hlo hout
  have hpostRead64 :
      (dripVatIlksPostCallMem I out).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    dripVatIlksPostCallMem_read64_long I out hlo hout
  have hinnerSize :
      (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
        (dripVatIlksPostCallMem I out)).size = 192 := by
    rw [drip_twoWordHashMem_size_of_ge64 (fileDutyIlkWord I)
      (⟨1⟩ : UInt256) (by rw [hpostSize]; omega), hpostSize]
  have hinnerRead64 :
      (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
        (dripVatIlksPostCallMem I out)).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    drip_twoWordHashMem_read64_of_ge96 (fileDutyIlkWord I) (⟨1⟩ : UInt256)
      (by rw [hpostSize]; omega) hpostRead64
  have hfoldBaseSize : foldBaseMem.size = 192 := by
    dsimp [foldBaseMem]
    rw [drip_twoWordHashMem_size_of_ge64 (fileDutyIlkWord I)
      (⟨1⟩ : UInt256) (by rw [hinnerSize]; omega), hinnerSize]
  have hfoldBaseRead64 :
      foldBaseMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [foldBaseMem]
    exact drip_twoWordHashMem_read64_of_ge96 (fileDutyIlkWord I)
      (⟨1⟩ : UInt256) (by rw [hinnerSize]; omega) hinnerRead64
  obtain ⟨_, _, rd1570⟩ :=
    _diffNZeroProgress hage0 hfitRmul hprevMax
  simpa [foldBaseMem] using
    (RD.jugDripVatFoldCallReady hfoldBaseSize hfoldBaseRead64 hfoldCode rd1570)
have _foldNZeroNoCode :
    age = ⟨0⟩ →
      jugRay.toNat * (dripVatIlksPrevWord out).toNat < UInt256.size →
        ((dripVatIlksPrevWord out).toNat : Int) ≤ maxInt256 →
          Reasoning.Theory.extCodeSizeWord σ'
            (dripVatTargetWord σ' I) = ⟨0⟩ →
            RDrev jugBytecode (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
  intro hage0 hfitRmul hprevMax hfoldCode
  let foldBaseMem :=
    twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
      (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
        (dripVatIlksPostCallMem I out))
  have hpostSize : (dripVatIlksPostCallMem I out).size = 192 :=
    dripVatIlksPostCallMem_size_long I out hlo hout
  have hpostRead64 :
      (dripVatIlksPostCallMem I out).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    dripVatIlksPostCallMem_read64_long I out hlo hout
  have hinnerSize :
      (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
        (dripVatIlksPostCallMem I out)).size = 192 := by
    rw [drip_twoWordHashMem_size_of_ge64 (fileDutyIlkWord I)
      (⟨1⟩ : UInt256) (by rw [hpostSize]; omega), hpostSize]
  have hinnerRead64 :
      (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
        (dripVatIlksPostCallMem I out)).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    drip_twoWordHashMem_read64_of_ge96 (fileDutyIlkWord I) (⟨1⟩ : UInt256)
      (by rw [hpostSize]; omega) hpostRead64
  have hfoldBaseSize : foldBaseMem.size = 192 := by
    dsimp [foldBaseMem]
    rw [drip_twoWordHashMem_size_of_ge64 (fileDutyIlkWord I)
      (⟨1⟩ : UInt256) (by rw [hinnerSize]; omega), hinnerSize]
  have hfoldBaseRead64 :
      foldBaseMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [foldBaseMem]
    exact drip_twoWordHashMem_read64_of_ge96 (fileDutyIlkWord I)
      (⟨1⟩ : UInt256) (by rw [hinnerSize]; omega) hinnerRead64
  obtain ⟨_, _, rd1570⟩ :=
    _diffNZeroProgress hage0 hfitRmul hprevMax
  simpa [foldBaseMem] using
    (RD.jugDripVatFoldNoCode hfoldBaseSize hfoldBaseRead64 hfoldCode rd1570)
jug_drip_nzero_and_later_tac
"#

elab "jug_drip_add_returns_tac" : tactic => do
  let tacSeq ← match Mathlib.GuardExceptions.parseAsTacticSeq (← getEnv) jugDripAddReturnsScript with
    | .ok tacSeq => pure tacSeq
    | .error err => throwError "failed to parse jug_drip_add_returns_tac:
{err}"
  evalTactic (← `(tactic| ($tacSeq:tacticSeq)))

end Benchmarks.Dss.Jug
