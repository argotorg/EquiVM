import Benchmarks.Dss.Dog.BarkChunk2

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Dog.Immutables

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

section
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Dog

theorem RD.dogBarkNoLeftoverToDinkEntry {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray}
    {σ : AccountMap}
    {room spot dust rate dart art ink kpr urn ilk : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hnoLeftover : art.toNat ≤ dart.toNat)
    (rd3594 : RD code I g s0 ⟨3594⟩
      (room :: spot :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata σ k C)
    (hov : R.length + 24 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨3700⟩
      (room :: spot :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata σ k' C' := by
  have rd3601 := evm_run rd3594 with [
    raw dup5
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup8
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw gt
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3700⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hgtZero : UInt256.gt art dart = ⟨0⟩ :=
    Reasoning.Theory.ugt_zero hnoLeftover
  have hcond : UInt256.isZero (UInt256.gt art dart) ≠ ⟨0⟩ := by
    rw [hgtZero]
    decide
  have rd3700 := rd3601.jumpiT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hcond (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  exact ⟨_, _, rd3700⟩

theorem RD.dogBarkDustyLeftoverToDinkEntry {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray}
    {σ : AccountMap}
    {room spot dust rate dart art ink kpr urn ilk : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hleftover : dart.toNat < art.toNat)
    (hfitLeftoverDue : (barkLeftoverArtWord art dart).toNat * rate.toNat < UInt256.size)
    (hdusty : (barkLeftoverDueWord art dart rate).toNat < dust.toNat)
    (rd3594 : RD code I g s0 ⟨3594⟩
      (room :: spot :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata σ k C)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨3700⟩
      (room :: spot :: dust :: rate :: art :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata σ k' C' := by
  have rd3601 := evm_run rd3594 with [
    raw dup5
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup8
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw gt
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3700⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hgtOne : UInt256.gt art dart = ⟨1⟩ :=
    Reasoning.Theory.ugt_one hleftover
  have hcondNoJump : UInt256.isZero (UInt256.gt art dart) = ⟨0⟩ := by
    rw [hgtOne]
    decide
  have rd3602 := rd3601.jumpiNT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hcondNoJump (by evm_ov)
  have rd3613 := evm_run rd3602 with [
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3614⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup10
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw sub
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4564⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4564 := rd3613.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  obtain ⟨_, _, rd3614raw⟩ :=
    RD.dogCheckedMulReturns (v := v) hpatch
      (x := barkLeftoverArtWord art dart) (y := rate) (ret := ⟨3614⟩)
      (R := dust :: room :: spot :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink ::
        ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      (by simp only [List.length_cons]; omega)
      (dogPatchedJumpDest hpatch (by native_decide)) hfitLeftoverDue rd4564
  have rd3614 := by
    simpa [barkLeftoverDueWord, barkLeftoverArtWord] using rd3614raw
  have rd3620 := evm_run rd3614 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw lt
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3628⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hltOne : UInt256.lt (barkLeftoverDueWord art dart rate) dust = ⟨1⟩ :=
    Reasoning.Theory.ult_one hdusty
  have hcondDusty : UInt256.isZero (UInt256.lt (barkLeftoverDueWord art dart rate) dust) =
      ⟨0⟩ := by
    rw [hltOne]
    decide
  have rd3621 := rd3620.jumpiNT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hcondDusty (by evm_ov)
  have rd3627 := evm_run rd3621 with [
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap5
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3700⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3700 := rd3627.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  exact ⟨_, _, rd3700⟩

theorem RD.dogBarkPartialLeftoverToDinkEntry {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray}
    {σ : AccountMap}
    {room spot dust rate dart art ink kpr urn ilk : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hleftover : dart.toNat < art.toNat)
    (hfitLeftoverDue : (barkLeftoverArtWord art dart).toNat * rate.toNat < UInt256.size)
    (hnotDusty : dust.toNat ≤ (barkLeftoverDueWord art dart rate).toNat)
    (hfitPartialDue : dart.toNat * rate.toNat < UInt256.size)
    (hpartialDueOk : dust.toNat ≤ (barkPartialDueWord dart rate).toNat)
    (rd3594 : RD code I g s0 ⟨3594⟩
      (room :: spot :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata σ k C)
    (hov : R.length + 36 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨3700⟩
      (room :: spot :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata σ k' C' := by
  have rd3601 := evm_run rd3594 with [
    raw dup5
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup8
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw gt
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3700⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hgtOne : UInt256.gt art dart = ⟨1⟩ :=
    Reasoning.Theory.ugt_one hleftover
  have hcondNoJump : UInt256.isZero (UInt256.gt art dart) = ⟨0⟩ := by
    rw [hgtOne]
    decide
  have rd3602 := rd3601.jumpiNT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hcondNoJump (by evm_ov)
  have rd3613 := evm_run rd3602 with [
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3614⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup10
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw sub
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4564⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4564left := rd3613.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  obtain ⟨_, _, rd3614raw⟩ :=
    RD.dogCheckedMulReturns (v := v) hpatch
      (x := barkLeftoverArtWord art dart) (y := rate) (ret := ⟨3614⟩)
      (R := dust :: room :: spot :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink ::
        ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      (by simp only [List.length_cons]; omega)
      (dogPatchedJumpDest hpatch (by native_decide)) hfitLeftoverDue rd4564left
  have rd3614 := by
    simpa [barkLeftoverDueWord, barkLeftoverArtWord] using rd3614raw
  have rd3620 := evm_run rd3614 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw lt
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3628⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hltZero : UInt256.lt (barkLeftoverDueWord art dart rate) dust = ⟨0⟩ :=
    Reasoning.Theory.ult_zero hnotDusty
  have hcondContinue :
      UInt256.isZero (UInt256.lt (barkLeftoverDueWord art dart rate) dust) ≠ ⟨0⟩ := by
    rw [hltZero]
    decide
  have rd3628 := rd3620.jumpiT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hcondContinue (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  have rd3638 := evm_run rd3628 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3639⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4564⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4564partial := rd3638.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  obtain ⟨_, _, rd3639raw⟩ :=
    RD.dogCheckedMulReturns (v := v) hpatch
      (x := dart) (y := rate) (ret := ⟨3639⟩)
      (R := dust :: room :: spot :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink ::
        ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      (by simp only [List.length_cons]; omega)
      (dogPatchedJumpDest hpatch (by native_decide)) hfitPartialDue rd4564partial
  have rd3639 := by
    simpa [barkPartialDueWord] using rd3639raw
  have rd3645 := evm_run rd3639 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw lt
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3700⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hpartialLtZero : UInt256.lt (barkPartialDueWord dart rate) dust = ⟨0⟩ :=
    Reasoning.Theory.ult_zero hpartialDueOk
  have hpartialCond :
      UInt256.isZero (UInt256.lt (barkPartialDueWord dart rate) dust) ≠ ⟨0⟩ := by
    rw [hpartialLtZero]
    decide
  have rd3700 := rd3645.jumpiT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hpartialCond (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  exact ⟨_, _, rd3700⟩

theorem RD.dogBarkPartialLeftoverDustyReverts {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray}
    {σ : AccountMap}
    {room spot dust rate dart art ink kpr urn ilk : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hleftover : dart.toNat < art.toNat)
    (hfitLeftoverDue : (barkLeftoverArtWord art dart).toNat * rate.toNat < UInt256.size)
    (hnotDusty : dust.toNat ≤ (barkLeftoverDueWord art dart rate).toNat)
    (hfitPartialDue : dart.toNat * rate.toNat < UInt256.size)
    (hpartialDueBad : (barkPartialDueWord dart rate).toNat < dust.toNat)
    (hmem : mem.size = 544)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩)
    (rd3594 : RD code I g s0 ⟨3594⟩
      (room :: spot :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata σ k C)
    (hov : R.length + 36 ≤ 1024) :
    RDrev code g s0 := by
  have rd3601 := evm_run rd3594 with [
    raw dup5
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup8
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw gt
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3700⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hgtOne : UInt256.gt art dart = ⟨1⟩ :=
    Reasoning.Theory.ugt_one hleftover
  have hcondNoJump : UInt256.isZero (UInt256.gt art dart) = ⟨0⟩ := by
    rw [hgtOne]
    decide
  have rd3602 := rd3601.jumpiNT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hcondNoJump (by evm_ov)
  have rd3613 := evm_run rd3602 with [
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3614⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup10
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw sub
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4564⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4564left := rd3613.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  obtain ⟨_, _, rd3614raw⟩ :=
    RD.dogCheckedMulReturns (v := v) hpatch
      (x := barkLeftoverArtWord art dart) (y := rate) (ret := ⟨3614⟩)
      (R := dust :: room :: spot :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink ::
        ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      (by simp only [List.length_cons]; omega)
      (dogPatchedJumpDest hpatch (by native_decide)) hfitLeftoverDue rd4564left
  have rd3614 := by
    simpa [barkLeftoverDueWord, barkLeftoverArtWord] using rd3614raw
  have rd3620 := evm_run rd3614 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw lt
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3628⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hltZero : UInt256.lt (barkLeftoverDueWord art dart rate) dust = ⟨0⟩ :=
    Reasoning.Theory.ult_zero hnotDusty
  have hcondContinue :
      UInt256.isZero (UInt256.lt (barkLeftoverDueWord art dart rate) dust) ≠ ⟨0⟩ := by
    rw [hltZero]
    decide
  have rd3628 := rd3620.jumpiT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hcondContinue (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  have rd3638 := evm_run rd3628 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3639⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4564⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4564partial := rd3638.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  obtain ⟨_, _, rd3639raw⟩ :=
    RD.dogCheckedMulReturns (v := v) hpatch
      (x := dart) (y := rate) (ret := ⟨3639⟩)
      (R := dust :: room :: spot :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink ::
        ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      (by simp only [List.length_cons]; omega)
      (dogPatchedJumpDest hpatch (by native_decide)) hfitPartialDue rd4564partial
  have rd3639 := by
    simpa [barkPartialDueWord] using rd3639raw
  have rd3645 := evm_run rd3639 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw lt
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3700⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hpartialLtOne : UInt256.lt (barkPartialDueWord dart rate) dust = ⟨1⟩ :=
    Reasoning.Theory.ult_one hpartialDueBad
  have hpartialCond :
      UInt256.isZero (UInt256.lt (barkPartialDueWord dart rate) dust) = ⟨0⟩ := by
    rw [hpartialLtOne]
    decide
  have rdFallthrough := rd3645.jumpiNT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hpartialCond (by evm_ov)
  have hpc3646 :
      (⟨3639⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ =
        ⟨3646⟩ := by
    native_decide
  have rd3646 := rdFallthrough
  rw [hpc3646] at rd3646
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨384⟩ :=
    mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256))
      (v := (⟨384⟩ : UInt256))
      (by rw [hmem]; decide)
      (by
        simpa [show (⟨64⟩ : UInt256).toNat = 64 by native_decide] using hread64)
  have rdMload := evm_run rd3646 with [
    raw push1 ⟨64⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mload 0 ⟨384⟩ (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload64 (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw shl
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mstore 0 (barkPostIlksErrorStringMem0 mem) (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨4⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨32⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw sub
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mstore 0 (barkPostIlksErrorStringMem1 mem) (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨42⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mstore 0 (barkPostIlksErrorStringMem2 (⟨42⟩ : UInt256) mem)
      (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hcopy :
      code.write 4691 (barkPostIlksErrorStringMem2 (⟨42⟩ : UInt256) mem) 452 42 =
        barkPostIlksCodecopyErrorMem code mem := by
    rfl
  have hsrcCopy : 4691 + 42 ≤ code.size := by
    rw [dogPatchedSize hpatch]
    native_decide
  have rdCopy := evm_run rdPrefix with [
    raw push2 ⟨4691⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by simp only [List.length_cons]; omega),
    raw push1 ⟨42⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by simp only [List.length_cons]; omega),
    raw swap2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by simp only [List.length_cons]; omega),
    raw codecopy 0 (barkPostIlksCodecopyErrorMem code mem) (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by native_decide)
      hcopy
      (by native_decide)
      (by evm_ov)]
  exact evm_run rdCopy with [
    raw push1 ⟨64⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨64⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mload 0 ⟨384⟩ (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost (barkPostIlksCodecopyErrorMem_mload64 hmem hread64 hsrcCopy)
      (by decide) (by evm_ov),
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw sub
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw rev 0
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost (by evm_ov)]

theorem RD.dogBarkComputeDink {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray}
    {σ : AccountMap}
    {room spot dust rate dart art ink kpr urn ilk : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hfitInkDart : ink.toNat * dart.toNat < UInt256.size)
    (hartNe : art ≠ ⟨0⟩)
    (rd3700 : RD code I g s0 ⟨3700⟩
      (room :: spot :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata σ k C)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨3726⟩
      (barkDinkWord ink dart art :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink ::
        ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata σ k' C' := by
  have rd3714 := evm_run rd3700 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨0⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup6
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3715⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup9
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4564⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4564 := rd3714.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  obtain ⟨_, _, rd3715raw⟩ :=
    RD.dogCheckedMulReturns (v := v) hpatch
      (x := ink) (y := dart) (ret := ⟨3715⟩)
      (R := art :: ⟨0⟩ :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink ::
        ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      (by simp only [List.length_cons]; omega)
      (dogPatchedJumpDest hpatch (by native_decide)) hfitInkDart rd4564
  have rd3715 := by
    simpa [barkInkDartWord] using rd3715raw
  have rd3720 := evm_run rd3715 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3722⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3722 := rd3720.jumpiT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hartNe (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  have rd3726 := evm_run rd3722 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw div
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  exact ⟨_, _, by simpa [barkDinkWord] using rd3726⟩

theorem RD.dogBarkInkDartOverflowReverts {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray}
    {σ : AccountMap}
    {room spot dust rate dart art ink kpr urn ilk : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hoverInkDart : UInt256.size ≤ ink.toNat * dart.toNat)
    (rd3700 : RD code I g s0 ⟨3700⟩
      (room :: spot :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata σ k C)
    (hov : R.length + 32 ≤ 1024) :
    RDrev code g s0 := by
  have rd3714 := evm_run rd3700 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨0⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup6
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3715⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup9
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4564⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4564 := rd3714.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  exact RD.dogCheckedMulOverflowReverts (v := v) hpatch
    (x := ink) (y := dart) (ret := ⟨3715⟩)
    (R := art :: ⟨0⟩ :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink ::
      ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
    (by simp only [List.length_cons]; omega) hoverInkDart rd4564

theorem RD.dogBarkDinkGuardOk {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray}
    {σ : AccountMap}
    {dink dust rate dart art ink kpr urn ilk : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hdinkPos : 0 < dink.toNat)
    (rd3726 : RD code I g s0 ⟨3726⟩
      (dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata σ k C)
    (hov : R.length + 30 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨3797⟩
      (dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata σ k' C' := by
  have rd3730 := evm_run rd3726 with [
    raw push1 ⟨0⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw gt
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3797⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hgtOne : UInt256.gt dink ⟨0⟩ = ⟨1⟩ :=
    Reasoning.Theory.ugt_one (by simpa using hdinkPos)
  have hcond : UInt256.gt dink ⟨0⟩ ≠ ⟨0⟩ := by
    rw [hgtOne]
    decide
  have rd3797 := rd3730.jumpiT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hcond (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  exact ⟨_, _, rd3797⟩

theorem RD.dogBarkDinkGuardReverts {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray}
    {σ : AccountMap}
    {dink dust rate dart art ink kpr urn ilk : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hdinkNotPos : ¬ 0 < dink.toNat)
    (hmem : mem.size = 544)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩)
    (rd3726 : RD code I g s0 ⟨3726⟩
      (dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata σ k C)
    (hov : R.length + 30 ≤ 1024) :
    RDrev code g s0 := by
  have rd3730 := evm_run rd3726 with [
    raw push1 ⟨0⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw gt
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3797⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hdinkZero : dink.toNat = 0 := Nat.eq_zero_of_not_pos hdinkNotPos
  have hgtZero : UInt256.gt dink ⟨0⟩ = ⟨0⟩ := by
    exact Reasoning.Theory.ugt_zero (by simpa [hdinkZero])
  have rd3734prep := rd3730
  rw [hgtZero] at rd3734prep
  have rd3734 := rd3734prep.jumpiNT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by rfl) (by evm_ov)
  have htail : solcErrorStringRevertTailWf code ⟨3734⟩ ⟨16⟩
      dogNullAuctionRawWord ⟨129⟩ .PUSH16 16 := by
    unfold solcErrorStringRevertTailWf
    repeat' first
      | apply And.intro
      | (rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)];
          native_decide)
  exact Benchmarks.Dss.Dog.RD.dogBarkPostIlksErrorStringRevertTail
    (pc := ⟨3734⟩) (len := ⟨16⟩) (rawWord := dogNullAuctionRawWord)
    (shift := ⟨129⟩) (word := UInt256.shiftLeft dogNullAuctionRawWord ⟨129⟩)
    (op := .PUSH16) (width := 16) rd3734 htail (by decide) rfl hmem hread64
    (by simp only [List.length_cons]; omega)

theorem RD.dogBarkInt256GuardOk {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray}
    {σ : AccountMap}
    {dink dust rate dart art ink kpr urn ilk : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hdartBound : dart.toNat ≤ dogInt256LimitWord.toNat)
    (hdinkBound : dink.toNat ≤ dogInt256LimitWord.toNat)
    (rd3797 : RD code I g s0 ⟨3797⟩
      (dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata σ k C)
    (hov : R.length + 34 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨3885⟩
      (dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata σ k' C' := by
  have rd3808 := evm_run rd3797 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨1⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨255⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw shl
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup5
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw gt
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3821⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hgtDartZero :
      UInt256.gt dart (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩) = ⟨0⟩ := by
    simpa [dogInt256LimitWord] using
      (Reasoning.Theory.ugt_zero (a := dart) (b := dogInt256LimitWord) hdartBound)
  have rd3812prep := rd3808
  rw [hgtDartZero,
    show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by decide,
    show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ by decide] at rd3812prep
  have rd3812 := rd3812prep.jumpiNT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by rfl) (by evm_ov)
  have rd3825 := evm_run rd3812 with [
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨1⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨255⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw shl
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw gt
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3885⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hgtDinkZero :
      UInt256.gt dink (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩) = ⟨0⟩ := by
    simpa [dogInt256LimitWord] using
      (Reasoning.Theory.ugt_zero (a := dink) (b := dogInt256LimitWord) hdinkBound)
  have rd3825prep := rd3825
  rw [hgtDinkZero,
    show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by decide] at rd3825prep
  have hcond : (⟨1⟩ : UInt256) ≠ ⟨0⟩ := by decide
  have rd3885 := rd3825prep.jumpiT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hcond (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  exact ⟨_, _, rd3885⟩

theorem RD.dogBarkInt256GuardDartOverflowReverts {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray}
    {σ : AccountMap}
    {dink dust rate dart art ink kpr urn ilk : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hdartOverflow : dogInt256LimitWord.toNat < dart.toNat)
    (hmem : mem.size = 544)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩)
    (rd3797 : RD code I g s0 ⟨3797⟩
      (dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata σ k C)
    (hov : R.length + 34 ≤ 1024) :
    RDrev code g s0 := by
  have rd3808 := evm_run rd3797 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨1⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨255⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw shl
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup5
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw gt
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3821⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hgtDartOne :
      UInt256.gt dart (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩) = ⟨1⟩ := by
    simpa [dogInt256LimitWord] using
      (Reasoning.Theory.ugt_one (a := dart) (b := dogInt256LimitWord) hdartOverflow)
  have rd3821prep := rd3808
  rw [hgtDartOne,
    show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ by decide,
    show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by decide] at rd3821prep
  have rd3821 := rd3821prep.jumpiT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  have rd3825 := evm_run rd3821 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3885⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3826 := rd3825.jumpiNT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by rfl) (by evm_ov)
  have htail : solcErrorStringRevertTailWf code ⟨3826⟩ ⟨12⟩
      dogOverflowRawWord ⟨160⟩ .PUSH12 12 := by
    unfold solcErrorStringRevertTailWf
    repeat' first
      | apply And.intro
      | (rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)];
          native_decide)
  exact Benchmarks.Dss.Dog.RD.dogBarkPostIlksErrorStringRevertTail
    (pc := ⟨3826⟩) (len := ⟨12⟩) (rawWord := dogOverflowRawWord)
    (shift := ⟨160⟩) (word := UInt256.shiftLeft dogOverflowRawWord ⟨160⟩)
    (op := .PUSH12) (width := 12) rd3826 htail (by decide) rfl hmem hread64
    (by simp only [List.length_cons]; omega)

theorem RD.dogBarkInt256GuardDinkOverflowReverts {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray}
    {σ : AccountMap}
    {dink dust rate dart art ink kpr urn ilk : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hdartBound : dart.toNat ≤ dogInt256LimitWord.toNat)
    (hdinkOverflow : dogInt256LimitWord.toNat < dink.toNat)
    (hmem : mem.size = 544)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩)
    (rd3797 : RD code I g s0 ⟨3797⟩
      (dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata σ k C)
    (hov : R.length + 34 ≤ 1024) :
    RDrev code g s0 := by
  have rd3808 := evm_run rd3797 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨1⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨255⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw shl
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup5
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw gt
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3821⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hgtDartZero :
      UInt256.gt dart (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩) = ⟨0⟩ := by
    simpa [dogInt256LimitWord] using
      (Reasoning.Theory.ugt_zero (a := dart) (b := dogInt256LimitWord) hdartBound)
  have rd3812prep := rd3808
  rw [hgtDartZero,
    show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by decide,
    show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ by decide] at rd3812prep
  have rd3812 := rd3812prep.jumpiNT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by rfl) (by evm_ov)
  have rd3825 := evm_run rd3812 with [
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨1⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨255⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw shl
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw gt
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3885⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hgtDinkOne :
      UInt256.gt dink (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩) = ⟨1⟩ := by
    simpa [dogInt256LimitWord] using
      (Reasoning.Theory.ugt_one (a := dink) (b := dogInt256LimitWord) hdinkOverflow)
  have rd3825prep := rd3825
  rw [hgtDinkOne,
    show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ by decide] at rd3825prep
  have rd3826 := rd3825prep.jumpiNT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by rfl) (by evm_ov)
  have htail : solcErrorStringRevertTailWf code ⟨3826⟩ ⟨12⟩
      dogOverflowRawWord ⟨160⟩ .PUSH12 12 := by
    unfold solcErrorStringRevertTailWf
    repeat' first
      | apply And.intro
      | (rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)];
          native_decide)
  exact Benchmarks.Dss.Dog.RD.dogBarkPostIlksErrorStringRevertTail
    (pc := ⟨3826⟩) (len := ⟨12⟩) (rawWord := dogOverflowRawWord)
    (shift := ⟨160⟩) (word := UInt256.shiftLeft dogOverflowRawWord ⟨160⟩)
    (op := .PUSH12) (width := 12) rd3826 htail (by decide) rfl hmem hread64
    (by simp only [List.length_cons]; omega)

theorem RD.dogBarkVatGrabExtcodesizeGuard {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray}
    {σ σMem : AccountMap}
    {dink dust rate dart art ink : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hmem : mem.size = 544)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩)
    (hmload256 :
      (if (⟨256⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨256⟩ : UInt256).toNat 32))) =
        barkIlksClipWord σMem I)
    (rd3885 : RD code I g s0 ⟨3885⟩
      (dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata σ k C)
    (hov : R.length + 48 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨4023⟩
      (barkVatWord v :: barkVatWord v :: ⟨0⟩ :: barkVatGrabOutPtr ::
        barkVatGrabInSize :: barkVatGrabOutPtr :: barkVatGrabOutSize ::
        barkVatGrabEndPtr :: barkVatGrabSelectorWord :: barkVatWord v ::
        dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (barkVatGrabCallMem σ σMem I mem dink dart) (UInt256.ofNat 19) rdata
      σ k' C' := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨384⟩ := by
    exact mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (v := (⟨384⟩ : UInt256))
      (by rw [hmem]; decide)
      (by simpa [show (⟨64⟩ : UInt256).toNat = 64 by native_decide] using hread64)
  have hmload64Call :=
    barkVatGrabCallMem_mload64 (σ := σ) (σMem := σMem) (I := I)
      (mem := mem) (dink := dink) (dart := dart) hmem hread64
  have hvatCleanR :
      UInt256.land (barkVatWord v) solcAddrMask = barkVatWord v :=
    solcAddrMask_clean (barkVatWord_canonical v)
  have hvatCleanL :
      UInt256.land solcAddrMask (barkVatWord v) = barkVatWord v :=
    solcAddrMask_clean_left (barkVatWord_canonical v)
  have hclipCanon : (barkIlksClipWord σMem I).toNat < EVM.addressModulus := by
    simpa [barkIlksClipWord, u256_land_comm] using
      solcAddrMask_result_canonical (solcSlotWord σMem I (barkIlksSlot I))
  have hclipMask :
      UInt256.land solcAddrMask (barkIlksClipWord σMem I) = barkIlksClipWord σMem I :=
    solcAddrMask_clean_left hclipCanon
  have hurnCanon : (barkUrnKey I).toNat < EVM.addressModulus := by
    simpa [barkUrnKey, u256_land_comm] using
      solcAddrMask_result_canonical (barkUrnWord I)
  have hurnMask :
      UInt256.land solcAddrMask (barkUrnKey I) = barkUrnKey I :=
    solcAddrMask_clean_left hurnCanon
  have hvowCanon : (barkVowWord σ I).toNat < EVM.addressModulus := by
    simpa [barkVowWord, u256_land_comm] using
      solcAddrMask_result_canonical (solcSlotWordAt ⟨2⟩ σ I)
  have hvowMask :
      UInt256.land solcAddrMask (barkVowWord σ I) = barkVowWord σ I :=
    solcAddrMask_clean_left hvowCanon
  have haddrMaskWord :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  have hvatCleanLit :
      UInt256.land ({ val := 1461501637330902918203684832716283019655932542975 } :
        UInt256) (barkVatWord v) = barkVatWord v := by
    simpa [solcAddrMask] using hvatCleanL
  have hclipMaskLit :
      UInt256.land ({ val := 1461501637330902918203684832716283019655932542975 } :
        UInt256) (barkIlksClipWord σMem I) = barkIlksClipWord σMem I := by
    simpa [solcAddrMask] using hclipMask
  have hvowWordLit :
      UInt256.land ({ val := 1461501637330902918203684832716283019655932542975 } :
        UInt256) (solcSlotWordAt ⟨2⟩ σ I) = barkVowWord σ I := by
    simp [barkVowWord, solcAddrMask]
  have rd3890pre := evm_run rd3885 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup5
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mload 0 (barkIlksClipWord σMem I) (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload256 (by native_decide) (by simp only [List.length_cons]; omega),
    raw push1 ⟨2⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  obtain ⟨k3891, C3891, rd3891raw⟩ := rd3890pre.sload
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rd3891 : RD code I g s0 ⟨3891⟩
      (solcSlotWordAt ⟨2⟩ σ I :: barkIlksClipWord σMem I :: dink :: dust :: rate ::
        dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ :: barkKprKey I :: barkUrnKey I ::
        barkIlkWord I :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata σ k3891 C3891 := by
    simpa [solcSlotWordAt] using rd3891raw
  have rd3964 := evm_run rd3891 with [
    raw push1 ⟨64⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mload 0 ⟨384⟩ (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload64 (by native_decide) (by simp only [List.length_cons]; omega),
    raw push4 ⟨0x01eeacfd⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨230⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw shl
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mstore 0 (barkVatGrabSelectorMem mem) (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost (by rfl) (by native_decide) (by simp only [List.length_cons]; omega),
    raw push1 ⟨4⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup16
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by simp only [List.length_cons]; omega),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mstore 0 (barkVatGrabIlkMem I mem) (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost
      (by
        rw [show ({ val := 384 } + { val := 4 } : UInt256).toNat = 388
          from by native_decide]
        rfl)
      (by native_decide) (by simp only [List.length_cons]; omega),
    raw push1 ⟨1⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨1⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨160⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw shl
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw sub
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup15
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by simp only [List.length_cons]; omega),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw and
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨36⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup4
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mstore 0 (barkVatGrabUrnMem I mem) (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost
      (by
        rw [show ({ val := 384 } + { val := 36 } : UInt256).toNat = 420
          from by native_decide]
        simp only [barkVatGrabUrnMem, Reasoning.Theory.writeWord]
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
            solcAddrMask from by decide, hurnMask])
      (by native_decide) (by simp only [List.length_cons]; omega),
    raw swap4
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup5
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw and
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨68⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mstore 0 (barkVatGrabClipMem σMem I mem) (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost
      (by
        rw [show ({ val := 384 } + { val := 68 } : UInt256).toNat = 452
          from by native_decide]
        simp only [barkVatGrabClipMem, Reasoning.Theory.writeWord]
        rw [haddrMaskWord, hclipMask])
      (by native_decide) (by simp only [List.length_cons]; omega),
    raw swap2
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup4
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw and
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨100⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup4
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mstore 0 (barkVatGrabVowMem σ σMem I mem) (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost
      (by
        rw [show ({ val := 384 } + { val := 100 } : UInt256).toNat = 484
          from by native_decide]
        simp only [barkVatGrabVowMem, Reasoning.Theory.writeWord, barkVowWord]
        rw [haddrMaskWord])
      (by native_decide) (by simp only [List.length_cons]; omega),
    raw push1 ⟨0⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup5
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw sub
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨132⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup5
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mstore 3 (barkVatGrabDinkMem σ σMem I mem dink) (UInt256.ofNat 18)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost
      (by
        rw [show ({ val := 384 } + { val := 132 } : UInt256).toNat = 516
          from by native_decide]
        rfl)
      (by native_decide) (by simp only [List.length_cons]; omega),
    raw dup8
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw sub
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨164⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup5
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mstore 3 (barkVatGrabCallMem σ σMem I mem dink dart) (UInt256.ofNat 19)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost
      (by
        rw [show ({ val := 384 } + { val := 164 } : UInt256).toNat = 548
          from by native_decide]
        rfl)
      (by native_decide) (by simp only [List.length_cons]; omega),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mload 0 ⟨384⟩ (UInt256.ofNat 19)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload64Call (by native_decide) (by simp only [List.length_cons]; omega)]
  have rd3997 := rd3964.pushConst (barkVatWord v) (width := 32) (op := .PUSH32)
    (hop := by decide)
    (by simpa [barkVatWord] using dogBarkVatConstDecode3964 hpatch)
    (by simp only [List.length_cons]; omega)
  have rd4023 := evm_run rd3997 with [
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap4
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw and
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap3
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push4 barkVatGrabSelectorWord
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap3
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 barkVatGrabInSize
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap4
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap3
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap2
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw sub
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup4
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup8
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  exact ⟨_, _, by
    convert rd4023 using 1 <;>
      simp only [barkVatGrabOutPtr, barkVatGrabInSize, barkVatGrabOutSize,
        barkVatGrabEndPtr, haddrMaskWord, hvatCleanL,
        show UInt256.sub (⟨384⟩ : UInt256) ⟨384⟩ + barkVatGrabInSize =
          barkVatGrabInSize from by native_decide,
        show (⟨384⟩ : UInt256) + barkVatGrabInSize = barkVatGrabEndPtr
          from by native_decide] <;>
      native_decide⟩

theorem RD.dogBarkVatGrabNoCodeRevert {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {R : List UInt256}
    {mem rdata : ByteArray}
    {σ : AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd4023 : RD code I g s0 ⟨4023⟩ (barkVatWord v :: barkVatWord v :: R)
      mem (UInt256.ofNat 19) rdata σ k C)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ (barkVatWord v) = ⟨0⟩)
    (hov : R.length + 4 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨4023⟩) (okPc := ⟨4035⟩)
    rd4023 hcodeSize
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    hov

theorem RD.dogBarkVatGrabToCall {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {R : List UInt256}
    {mem rdata : ByteArray}
    {σ : AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd4023 : RD code I g s0 ⟨4023⟩ (barkVatWord v :: barkVatWord v :: R)
      mem (UInt256.ofNat 19) rdata σ k C)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ (barkVatWord v) ≠ ⟨0⟩)
    (hov : R.length + 4 ≤ 1024) :
    ∃ gasWord k' C', RD code I g s0 ⟨4038⟩ (gasWord :: barkVatWord v :: R)
      mem (UInt256.ofNat 19) rdata σ k' C' := by
  obtain ⟨gasWord, k', C', rd4038⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨4023⟩) (okPc := ⟨4035⟩)
      rd4023 hcodeSize
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (dogPatchedJumpDest hpatch (by native_decide))
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      hov
  exact ⟨gasWord, k', C', by simpa using rd4038⟩

theorem RD.dogBarkVatGrabCallFailure {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {acc : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd4039 : RD code I g s0 ⟨4039⟩ (⟨0⟩ :: R) mem aw rdata acc k C)
    (hrdataSize : rdata.size < UInt256.size)
    (hov : R.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨4039⟩) (okPc := ⟨4055⟩) rd4039
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    hrdataSize hov

theorem RD.dogBarkVatGrabCallSuccess {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {acc : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd4039 : RD code I g s0 ⟨4039⟩ (⟨1⟩ :: R) mem aw rdata acc k C)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨4057⟩ R mem aw rdata acc k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨4039⟩) (okPc := ⟨4055⟩) rd4039
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide))
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    hov

theorem RD.dogBarkVatGrabPostCall {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 evm : EVM.State} {I : ExecutionEnv}
    {σ σMem : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {dink dust rate dart art ink : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd3885 : RD code I g s0 ⟨3885⟩
      (dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata σ k C)
    (hsz100 : 100 ≤ I.calldata.size)
    (hmem : mem.size = 544)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩)
    (hmload256 :
      (if (⟨256⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨256⟩ : UInt256).toNat 32))) =
        barkIlksClipWord σMem I)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (barkVatWord v) ≠ ⟨0⟩)
    (hevmEnv : evm.executionEnv = I)
    (hevmMap : evm.accountMap = σ)
    (hevmOrig : evm.σ₀ = s0.σ₀)
    (hdepth : I.depth.val < 1024)
    (hdinkBound : dink.toNat ≤ dogInt256LimitWord.toNat)
    (hdartBound : dart.toNat ≤ dogInt256LimitWord.toNat)
    (hov : R.length + 48 ≤ 1024) :
    ∃ (σ' : AccountMap) (z : Bool)
      (outGrab : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD code I g s0 ⟨4039⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: barkVatGrabEndPtr ::
          barkVatGrabSelectorWord :: barkVatWord v :: dink :: dust :: rate ::
          dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
          barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
        (barkVatGrabPostCallMem σ σMem I mem outGrab dink dart)
        (UInt256.ofNat 19) outGrab σ' k' C'
      ∧ typedCallViaEVM config evm
          (EVM.address (AccountAddress.ofNat v.vat.toNat)) "grab" 0
          [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I),
            .address (AccountAddress.ofNat (barkIlksClipWord σMem I).toNat),
            .address (AccountAddress.ofNat (barkVowWord σ I).toNat),
            .int (-(Int.ofNat dink.toNat)), .int (-(Int.ofNat dart.toNat))]
          (z, { evm with accountMap := σ', substate := A' },
            outGrab) true
      ∧ outGrab.size < UInt256.size := by
  obtain ⟨_, _, rd4023⟩ :=
    RD.dogBarkVatGrabExtcodesizeGuard (v := v) (code := code) (g := g)
      (s0 := s0) (I := I) (ret := ret) (sel := sel) (R := R)
      (σ := σ) (σMem := σMem) hpatch hmem hread64 hmload256
      rd3885 hov
  obtain ⟨_, _, _, rd4038⟩ :=
    RD.dogBarkVatGrabToCall hpatch rd4023 hcodeSize
      (by simp only [List.length_cons]; omega)
  obtain ⟨σ', z, outGrab, A_in, callGas, k', C', hΘpack, rd4039raw, houtsz⟩ :=
    RD.call rd4038
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      hdepth
      (by simp only [List.length_cons]; omega)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨σ', z, outGrab, A', k', C', ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 19).toNat
          barkVatGrabOutPtr.toNat barkVatGrabInSize.toNat)
          barkVatGrabOutPtr.toNat barkVatGrabOutSize.toNat) = UInt256.ofNat 19 := by
      unfold barkVatGrabOutPtr barkVatGrabInSize barkVatGrabOutSize
      native_decide
    change RD code I g s0 ⟨4039⟩
      ((if z then ⟨1⟩ else ⟨0⟩) :: barkVatGrabEndPtr ::
        barkVatGrabSelectorWord :: barkVatWord v :: dink :: dust :: rate ::
        dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (outGrab.write 0 (barkVatGrabCallMem σ σMem I mem dink dart)
        barkVatGrabOutPtr.toNat
        (min barkVatGrabOutSize (UInt256.ofNat outGrab.size)).toNat)
      (UInt256.ofNat 19) outGrab σ' k' C'
    exact haw ▸ rd4039raw
  · have hdepthNe : evm.executionEnv.depth ≠ 1024 := by
      intro hdepthEq
      exact absurd hdepth (by rw [← hevmEnv, hdepthEq]; decide)
    have htargetNorm :
        EVM.address ↑(AccountAddress.ofNat v.vat.toNat) =
          AccountAddress.ofUInt256 (barkVatWord v) := by
      rw [← barkVat_eq_vatKey v]
      apply Fin.ext
      simp [EVM.address, EVM.uintN]
      exact Nat.mod_eq_of_lt (AccountAddress.ofNat v.vat.toNat).isLt
    have hΘ' :
        (σ', g'', A', z, outGrab) =
          Ethereum.EVM.Θ evm.executionEnv.fork evm.accountMap evm.σ₀ A_in
            (AccountAddress.ofUInt256 (UInt256.ofNat evm.executionEnv.codeOwner))
            evm.executionEnv.sender (AccountAddress.ofUInt256 (barkVatWord v))
            (toExecute evm.executionEnv.fork evm.accountMap (AccountAddress.ofUInt256 (barkVatWord v)))
            callGas (UInt256.ofNat evm.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
            ((barkVatGrabCallMem σ σMem I mem dink dart).readWithPadding
              barkVatGrabOutPtr.toNat barkVatGrabInSize.toNat)
            (evm.executionEnv.depth + 1) evm.executionEnv.header
            evm.executionEnv.blobVersionedHashes evm.executionEnv.blocks
            evm.executionEnv.perm := by
      simpa [hevmEnv, hevmMap, hevmOrig] using hΘ
    exact Reasoning.Theory.callCoincides
      (cfg := config) (evm := evm) (name := "grab")
      (args := [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I),
        .address (AccountAddress.ofNat (barkIlksClipWord σMem I).toNat),
        .address (AccountAddress.ofNat (barkVowWord σ I).toNat),
        .int (-(Int.ofNat dink.toNat)), .int (-(Int.ofNat dart.toNat))])
      (tgt := EVM.address (AccountAddress.ofNat v.vat.toNat))
      (targetWord := barkVatWord v) (σ' := σ') (A' := A')
      (A_in := A_in) (z := z) (o := outGrab) (g'' := g'') (callGas := callGas)
      (mem := barkVatGrabCallMem σ σMem I mem dink dart) (inOff := barkVatGrabOutPtr)
      (inSize := barkVatGrabInSize) (callPerm := true) hdepthNe htargetNorm
      (barkVatGrabEncode_eq (σ := σ) (σMem := σMem) (I := I)
        (mem := mem) (dink := dink) (dart := dart)
        hsz100 hmem hdinkBound hdartBound)
      hΘ'


end Benchmarks.Dss.Dog
