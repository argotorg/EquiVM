import Benchmarks.Dss.Clipper.TakeDynamicPostDog

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option maxHeartbeats 2000000 in
theorem RD.clipperTakePostDogTabZeroContinuationElim
    {P : Prop} {cA0 cA gh bl σ₀ σStart σ I} {g : Sat256} {A : Substate}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id sel :
      UInt256}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd5003 : RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨5003⟩
      (owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen ::
        dataStart :: who :: max :: amt :: id :: [⟨502⟩, sel])
      mem aw rdata (cA, σ) k C)
    (hlotNew : lotNew ≠ ⟨0⟩) (htabNew : tabNew = ⟨0⟩)
    (hmem : clipperTakeMemoryWF mem aw)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true)
    (onNoCode :
      ∀ hcodeVat : extCodeSizeWord σ (clipperTakeVatTarget v) = ⟨0⟩,
        RDrev code g (initState cA0 gh bl σStart σ₀ g A I) → P)
    (onCallFailure :
      ∀ (cAFlux : Batteries.RBSet AccountAddress compare) (σFlux : AccountMap)
        (outFlux : ByteArray) (AFlux : Substate),
        extCodeSizeWord σ (clipperTakeVatTarget v) ≠ ⟨0⟩ →
        typedCallViaEVM (config v)
          { initState cA0 gh bl σStart σ₀ g A I with
            accountMap := σ, createdAccounts := cA }
          (EVM.address v.vat) "flux" 0
          [v.ilk, .address I.codeOwner, .address (AccountAddress.ofNat packed.toNat),
            .int (Int.ofNat lotNew.toNat)]
          (false,
            { initState cA0 gh bl σStart σ₀ g A I with
              accountMap := σFlux, substate := AFlux, createdAccounts := cAFlux },
            outFlux) true →
        RDrev code g (initState cA0 gh bl σStart σ₀ g A I) → P)
    (onCallSuccess :
      ∀ (cAFlux : Batteries.RBSet AccountAddress compare) (σFlux : AccountMap)
        (outFlux : ByteArray) (AFlux : Substate) (kFlux CFlux : ℕ),
        extCodeSizeWord σ (clipperTakeVatTarget v) ≠ ⟨0⟩ →
        typedCallViaEVM (config v)
          { initState cA0 gh bl σStart σ₀ g A I with
            accountMap := σ, createdAccounts := cA }
          (EVM.address v.vat) "flux" 0
          [v.ilk, .address I.codeOwner, .address (AccountAddress.ofNat packed.toNat),
            .int (Int.ofNat lotNew.toNat)]
          (true,
            { initState cA0 gh bl σStart σ₀ g A I with
              accountMap := σFlux, substate := AFlux, createdAccounts := cAFlux },
            outFlux) true →
        clipperTakeMemoryWF (clipperTakeVatFluxCalldataMem v I packed lotNew mem) aw →
        RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨8274⟩
          (id :: ⟨5020⟩ :: owe :: tabNew :: lotNew :: price :: tic :: packed ::
            stopped :: dataLen :: dataStart :: who :: max :: amt :: id ::
            [⟨502⟩, sel])
          (clipperTakeVatFluxCalldataMem v I packed lotNew mem) aw outFlux
          (cAFlux, σFlux) kFlux CFlux → P) : P := by
  obtain ⟨_, _, rd5025⟩ := RD.clipperTakePostDogLotNonzeroToCallbackGuard
    (v := v) (hpatch := hpatch) rd5003 hlotNew
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd5177⟩ := RD.clipperTakePostDogFluxExtcodesizeGuardWF
    v hpatch rd5025 htabNew hmem
  by_cases hcodeVat : extCodeSizeWord σ (clipperTakeVatTarget v) = ⟨0⟩
  · exact onNoCode hcodeVat
      (RD.clipperTakePostDogFluxNoCodeWF v hpatch rd5177 hcodeVat)
  · obtain ⟨cAFlux, σFlux, zFlux, outFlux, AFlux, _, _, rd5193,
        hcallFlux, houtFlux, hmemFlux⟩ :=
      RD.clipperTakePostDogFluxPostCallWF v hpatch rd5177 hmem hcodeVat hdepth hperm
    by_cases hzFlux : zFlux = false
    · exact onCallFailure cAFlux σFlux outFlux AFlux hcodeVat
        (by simpa [hzFlux] using hcallFlux)
        (RD.clipperTakePostDogFluxCallFailure v hpatch
          (by simpa [hzFlux] using rd5193) houtFlux
          (by simp only [List.length_cons, List.length_nil]; omega))
    · have hzFluxTrue : zFlux = true := Bool.eq_true_of_not_eq_false hzFlux
      obtain ⟨k8274, C8274, rd8274⟩ :=
        RD.clipperTakePostDogFluxCallSuccessToRemove v hpatch
          (by simpa [hzFluxTrue] using rd5193)
      exact onCallSuccess cAFlux σFlux outFlux AFlux k8274 C8274 hcodeVat
        (by simpa [hzFluxTrue] using hcallFlux) hmemFlux rd8274

end Benchmarks.Dss.Clipper
