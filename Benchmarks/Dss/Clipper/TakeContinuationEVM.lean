import Benchmarks.Dss.Clipper.TakeDynamicPostDog

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option maxHeartbeats 2000000 in
theorem RD.clipperTakeOweGtTabContinuationElim
    {P : Prop} {cA0 cA gh bl σ₀ σStart σ I} {g : Sat256} {A : Substate}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {dog slice owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id :
      UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd4701 : RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨4701⟩
      (dog :: slice :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped ::
        dataLen :: dataStart :: who :: max :: amt :: id :: R)
      mem aw rdata (cA, σ) k C)
    (hmem : clipperTakeMemoryWF mem aw)
    (hlotNew : lotNew ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true)
    (hov : R.length + 32 ≤ 1024)
    (onMoveNoCode :
      ∀ hcodeVat : extCodeSizeWord σ (clipperTakeVatTarget v) = ⟨0⟩,
        RDrev code g (initState cA0 gh bl σStart σ₀ g A I) → P)
    (onMoveFailure :
      ∀ (cAMove : Batteries.RBSet AccountAddress compare) (σMove : AccountMap)
        (outMove : ByteArray) (AMove : Substate),
        extCodeSizeWord σ (clipperTakeVatTarget v) ≠ ⟨0⟩ →
        typedCallViaEVM (config v)
          { initState cA0 gh bl σStart σ₀ g A I with
            accountMap := σ, createdAccounts := cA }
          (EVM.address v.vat) "move" 0
          [.address I.source,
            .address (AccountAddress.ofNat (clipperTakeVowTarget σ I).toNat),
            .int (Int.ofNat owe.toNat)]
          (false,
            { initState cA0 gh bl σStart σ₀ g A I with
              accountMap := σMove, substate := AMove, createdAccounts := cAMove },
            outMove) true →
        RDrev code g (initState cA0 gh bl σStart σ₀ g A I) → P)
    (onDogNoCode :
      ∀ (cAMove : Batteries.RBSet AccountAddress compare) (σMove : AccountMap)
        (outMove : ByteArray) (AMove : Substate),
        extCodeSizeWord σ (clipperTakeVatTarget v) ≠ ⟨0⟩ →
        typedCallViaEVM (config v)
          { initState cA0 gh bl σStart σ₀ g A I with
            accountMap := σ, createdAccounts := cA }
          (EVM.address v.vat) "move" 0
          [.address I.source,
            .address (AccountAddress.ofNat (clipperTakeVowTarget σ I).toNat),
            .int (Int.ofNat owe.toNat)]
          (true,
            { initState cA0 gh bl σStart σ₀ g A I with
              accountMap := σMove, substate := AMove, createdAccounts := cAMove },
            outMove) true →
        extCodeSizeWord σMove (UInt256.land solcAddrMask dog) = ⟨0⟩ →
        RDrev code g (initState cA0 gh bl σStart σ₀ g A I) → P)
    (onDogFailure :
      ∀ (cAMove : Batteries.RBSet AccountAddress compare) (σMove : AccountMap)
        (outMove : ByteArray) (AMove : Substate)
        (cADog : Batteries.RBSet AccountAddress compare) (σDog : AccountMap)
        (outDog : ByteArray) (ADog : Substate),
        extCodeSizeWord σ (clipperTakeVatTarget v) ≠ ⟨0⟩ →
        typedCallViaEVM (config v)
          { initState cA0 gh bl σStart σ₀ g A I with
            accountMap := σ, createdAccounts := cA }
          (EVM.address v.vat) "move" 0
          [.address I.source,
            .address (AccountAddress.ofNat (clipperTakeVowTarget σ I).toNat),
            .int (Int.ofNat owe.toNat)]
          (true,
            { initState cA0 gh bl σStart σ₀ g A I with
              accountMap := σMove, substate := AMove, createdAccounts := cAMove },
            outMove) true →
        extCodeSizeWord σMove (UInt256.land solcAddrMask dog) ≠ ⟨0⟩ →
        typedCallViaEVM (config v)
          { initState cA0 gh bl σStart σ₀ g A I with
            accountMap := σMove, createdAccounts := cAMove }
          (EVM.address (AccountAddress.ofUInt256 (UInt256.land solcAddrMask dog)))
          "digs" 0 [v.ilk, .int (Int.ofNat owe.toNat)]
          (false,
            { initState cA0 gh bl σStart σ₀ g A I with
              accountMap := σDog, substate := ADog, createdAccounts := cADog },
            outDog) true →
        RDrev code g (initState cA0 gh bl σStart σ₀ g A I) → P)
    (onPostDog :
      ∀ (cAMove : Batteries.RBSet AccountAddress compare) (σMove : AccountMap)
        (outMove : ByteArray) (AMove : Substate)
        (cADog : Batteries.RBSet AccountAddress compare) (σDog : AccountMap)
        (outDog : ByteArray) (ADog : Substate) (kDog CDog : ℕ),
        extCodeSizeWord σ (clipperTakeVatTarget v) ≠ ⟨0⟩ →
        typedCallViaEVM (config v)
          { initState cA0 gh bl σStart σ₀ g A I with
            accountMap := σ, createdAccounts := cA }
          (EVM.address v.vat) "move" 0
          [.address I.source,
            .address (AccountAddress.ofNat (clipperTakeVowTarget σ I).toNat),
            .int (Int.ofNat owe.toNat)]
          (true,
            { initState cA0 gh bl σStart σ₀ g A I with
              accountMap := σMove, substate := AMove, createdAccounts := cAMove },
            outMove) true →
        extCodeSizeWord σMove (UInt256.land solcAddrMask dog) ≠ ⟨0⟩ →
        typedCallViaEVM (config v)
          { initState cA0 gh bl σStart σ₀ g A I with
            accountMap := σMove, createdAccounts := cAMove }
          (EVM.address (AccountAddress.ofUInt256 (UInt256.land solcAddrMask dog)))
          "digs" 0 [v.ilk, .int (Int.ofNat owe.toNat)]
          (true,
            { initState cA0 gh bl σStart σ₀ g A I with
              accountMap := σDog, substate := ADog, createdAccounts := cADog },
            outDog) true →
        clipperTakeMemoryWF (clipperDogDigsCalldataMem v owe
          (clipperTakeVatMoveCalldataMem σ I owe mem)) aw →
        RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨5003⟩
          (owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen ::
            dataStart :: who :: max :: amt :: id :: R)
          (clipperDogDigsCalldataMem v owe
            (clipperTakeVatMoveCalldataMem σ I owe mem))
          aw outDog (cADog, σDog) kDog CDog → P) : P := by
  obtain ⟨_, _, rd4813⟩ := RD.clipperTakeVatMoveExtcodesizeGuardWF
    (v := v) (hpatch := hpatch) rd4701 hmem hov
  by_cases hcodeVat : extCodeSizeWord σ (clipperTakeVatTarget v) = ⟨0⟩
  · exact onMoveNoCode hcodeVat
      (RD.clipperTakeVatMoveNoCodeWF v hpatch rd4701 hmem hcodeVat hov)
  · obtain ⟨cAMove, σMove, zMove, outMove, AMove, kMove, CMove,
        rdMove, hcallMove, houtMove, hmemMove⟩ :=
      RD.clipperTakeVatMovePostCallWF v hpatch rd4813 hmem hcodeVat hdepth hperm hov
    by_cases hzMove : zMove = false
    · exact onMoveFailure cAMove σMove outMove AMove hcodeVat
        (by simpa [hzMove] using hcallMove)
        (RD.clipperTakeVatMoveCallFailure v hpatch
          (by simpa [hzMove] using rdMove) houtMove
          (by simp only [List.length_cons]; omega))
    · have hzMoveTrue : zMove = true := Bool.eq_true_of_not_eq_false hzMove
      obtain ⟨_, _, rd4850⟩ := RD.clipperTakeVatMoveCallSuccessToDogDigs
        v hpatch (by simpa [hzMoveTrue] using rdMove) hov
      obtain ⟨_, _, rd4964⟩ := RD.clipperTakeDogDigsOweCallSetupNonzeroWF
        v hpatch rd4850 hmemMove hlotNew hov
      by_cases hcodeDog :
          extCodeSizeWord σMove (UInt256.land solcAddrMask dog) = ⟨0⟩
      · exact onDogNoCode cAMove σMove outMove AMove hcodeVat
          (by simpa [hzMoveTrue] using hcallMove) hcodeDog
          (RD.clipperTakeDogDigsNoCodeWF v hpatch rd4964 hcodeDog hov)
      · obtain ⟨cADog, σDog, zDog, outDog, ADog, kDogCall, CDogCall,
            rdDog, hcallDog, houtDog, hmemDog⟩ :=
          RD.clipperTakeDogDigsPostCallWF v hpatch rd4964 hmemMove hcodeDog
            hdepth hperm hov
        by_cases hzDog : zDog = false
        · exact onDogFailure cAMove σMove outMove AMove cADog σDog outDog ADog
            hcodeVat (by simpa [hzMoveTrue] using hcallMove) hcodeDog
            (by simpa [hzDog] using hcallDog)
            (RD.clipperTakeDogDigsCallFailure v hpatch
              (by simpa [hzDog] using rdDog) houtDog
              (by simp only [List.length_cons]; omega))
        · have hzDogTrue : zDog = true := Bool.eq_true_of_not_eq_false hzDog
          obtain ⟨kPost, CPost, rd5003⟩ := RD.clipperTakeDogDigsCallSuccessToPostDog
            v hpatch (by simpa [hzDogTrue] using rdDog) hov
          exact onPostDog cAMove σMove outMove AMove cADog σDog outDog ADog
            kPost CPost hcodeVat (by simpa [hzMoveTrue] using hcallMove)
            hcodeDog (by simpa [hzDogTrue] using hcallDog) hmemDog rd5003

end Benchmarks.Dss.Clipper
