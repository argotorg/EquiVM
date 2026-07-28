import Benchmarks.Dss.Vat.FrobBase

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Vat

suppress_compilation

theorem vatFrobSuccessEquivFromFinalState
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {evmFinal : EVM.State} {finalLocals : Store}
    (hcode : I.code = vatBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some frobTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (frobTransition.params.map Param.name)
        (transitionSignature frobTransition).paramTypes I.calldata = some (frobStore I))
    (hret : RDret vatBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      (cA, frobAfterRuntimeFinal σ_evm I) ByteArray.empty)
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (frobStore I) frobTransition.body
        (.returned { contract := contract, locals := finalLocals } evmFinal none))
    (hcreated : (cA, frobAfterRuntimeFinal σ_evm I).1 = evmFinal.createdAccounts)
    (haccounts :
      accountMapEquiv (cA, frobAfterRuntimeFinal σ_evm I).2 evmFinal.accountMap) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have henc : returnEquiv ByteArray.empty none frobTransition.returnType := by
    rw [show frobTransition.returnType = [] by rfl]
    exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    hcreated haccounts henc

set_option maxHeartbeats 0 in
theorem vatFrobSuccessEquivFromSourceFinal
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {finalLocals : Store}
    (hsz196 : 196 ≤ I.calldata.size)
    (hcode : I.code = vatBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some frobTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (frobTransition.params.map Param.name)
        (transitionSignature frobTransition).paramTypes I.calldata = some (frobStore I))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hret : RDret vatBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      (cA, frobAfterRuntimeFinal σ_evm I) ByteArray.empty)
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (frobStore I) frobTransition.body
        (.returned { contract := contract, locals := finalLocals }
          (frobSourceFinalState cA gh bl σ_solm σ₀ A I g
            (frobUrnInkNew σ_solm I) (frobUrnArtNew σ_solm I)
            (frobIlkArtNew σ_solm I) (frobGemNew σ_solm I)
            (frobDaiNew σ_solm I)) none)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hcreated :=
    frobSourceFinalState_createdAccounts (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (frobUrnInkNew σ_solm I) (frobUrnArtNew σ_solm I)
      (frobIlkArtNew σ_solm I) (frobGemNew σ_solm I)
      (frobDaiNew σ_solm I)
  have hsourceAccounts :=
    accountMapEquiv_frobSourceFinalState (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hsz196
      (frobUrnInkNew σ_solm I) (frobUrnArtNew σ_solm I)
      (frobIlkArtNew σ_solm I) (frobGemNew σ_solm I)
      (frobDaiNew σ_solm I) rfl rfl rfl rfl rfl
  exact vatFrobSuccessEquivFromFinalState hcode hdispatch hdecode hret hbody
    (by simpa using hcreated)
    (by exact (accountMapEquiv_frobAfterRuntimeFinal hAccounts).trans hsourceAccounts)

theorem vatFrobLiveOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : vatSlotWord ⟨10⟩ σ I = ⟨1⟩)
    (hdecoded : ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2975⟩
      [frobDartWord I, frobDinkWord I, frobWMaskedWord I, frobVMaskedWord I,
        frobUMaskedWord I, frobIWord I, ⟨524⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3045⟩
      [frobDartWord I, frobDinkWord I, frobWMaskedWord I, frobVMaskedWord I,
        frobUMaskedWord I, frobIWord I, ⟨524⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := hdecoded
  have hliveSolc : solcSlotWord σ I ⟨10⟩ = ⟨1⟩ := by
    simpa [vatSlotWord] using hlive
  exact RD.vatLiveGuardOk
    (code := vatBytecode) (pc := ⟨2975⟩) (okPc := ⟨3045⟩)
    (key := frobDartWord I) (ret := frobDinkWord I)
    (R := [frobWMaskedWord I, frobVMaskedWord I, frobUMaskedWord I, frobIWord I, ⟨524⟩, sel])
    hdecoded
    (by unfold vatLiveGuardWf; repeat' first | apply And.intro | native_decide)
    hliveSolc (by jump_dest) (by simp)

def frobLiveSuccessGuards (σ : AccountMap) (I : ExecutionEnv) : Prop :=
  (UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
    UInt256.gt (frobDinkWord I + solcSlotWord σ I (frobUrnInkSlot I))
      (solcSlotWord σ I (frobUrnInkSlot I)) = ⟨0⟩) ∧
  (UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
    UInt256.lt (frobDinkWord I + solcSlotWord σ I (frobUrnInkSlot I))
      (solcSlotWord σ I (frobUrnInkSlot I)) = ⟨0⟩) ∧
  (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
    UInt256.gt (frobDartWord I + solcSlotWord σ I (frobUrnArtSlot I))
      (solcSlotWord σ I (frobUrnArtSlot I)) = ⟨0⟩) ∧
  (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
    UInt256.lt (frobDartWord I + solcSlotWord σ I (frobUrnArtSlot I))
      (solcSlotWord σ I (frobUrnArtSlot I)) = ⟨0⟩) ∧
  (UInt256.slt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
    UInt256.gt (frobDartWord I + solcSlotWord σ I (frobIlkArtSlot I))
      (solcSlotWord σ I (frobIlkArtSlot I)) = ⟨0⟩) ∧
  (UInt256.sgt (frobDartWord I) ⟨0⟩ = ⟨0⟩ ∨
    UInt256.lt (frobDartWord I + solcSlotWord σ I (frobIlkArtSlot I))
      (solcSlotWord σ I (frobIlkArtSlot I)) = ⟨0⟩) ∧
  UInt256.slt (solcSlotWord σ I (frobIlkRateSlot I)) ⟨0⟩ = ⟨0⟩ ∧
  (frobDartWord I = ⟨0⟩ ∨
    UInt256.eq
      (UInt256.sdiv
        (UInt256.mul (frobDartWord I) (solcSlotWord σ I (frobIlkRateSlot I)))
        (frobDartWord I))
      (solcSlotWord σ I (frobIlkRateSlot I)) ≠ ⟨0⟩) ∧
  ((frobDartWord I + solcSlotWord σ I (frobUrnArtSlot I)) = ⟨0⟩ ∨
    UInt256.eq
      (UInt256.div
        (UInt256.mul (solcSlotWord σ I (frobIlkRateSlot I))
          (frobDartWord I + solcSlotWord σ I (frobUrnArtSlot I)))
        (frobDartWord I + solcSlotWord σ I (frobUrnArtSlot I)))
      (solcSlotWord σ I (frobIlkRateSlot I)) ≠ ⟨0⟩) ∧
  (UInt256.slt
      (UInt256.mul (frobDartWord I) (solcSlotWord σ I (frobIlkRateSlot I)))
      ⟨0⟩ = ⟨0⟩ ∨
    UInt256.gt
      (UInt256.mul (frobDartWord I) (solcSlotWord σ I (frobIlkRateSlot I)) +
        solcSlotWord σ I foldDebtSlot)
      (solcSlotWord σ I foldDebtSlot) = ⟨0⟩) ∧
  (UInt256.sgt
      (UInt256.mul (frobDartWord I) (solcSlotWord σ I (frobIlkRateSlot I)))
      ⟨0⟩ = ⟨0⟩ ∨
    UInt256.lt
      (UInt256.mul (frobDartWord I) (solcSlotWord σ I (frobIlkRateSlot I)) +
        solcSlotWord σ I foldDebtSlot)
      (solcSlotWord σ I foldDebtSlot) = ⟨0⟩) ∧
  (solcSlotWord σ I (frobIlkRateSlot I) = ⟨0⟩ ∨
    UInt256.eq
      (UInt256.div
        (UInt256.mul
          (frobDartWord I + solcSlotWord σ I (frobIlkArtSlot I))
          (solcSlotWord σ I (frobIlkRateSlot I)))
        (solcSlotWord σ I (frobIlkRateSlot I)))
      (frobDartWord I + solcSlotWord σ I (frobIlkArtSlot I)) ≠ ⟨0⟩) ∧
  UInt256.lor
    (UInt256.land
      (UInt256.isZero
        (UInt256.gt
          (UInt256.mul (frobDartWord I) (solcSlotWord σ I (frobIlkRateSlot I)) +
            solcSlotWord σ I foldDebtSlot)
          (solcSlotWord σ I ⟨9⟩)))
      (UInt256.isZero
        (UInt256.gt
          (UInt256.mul
            (frobDartWord I + solcSlotWord σ I (frobIlkArtSlot I))
            (solcSlotWord σ I (frobIlkRateSlot I)))
          (solcSlotWord σ I (frobIlkLineSlot I)))))
    (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩)) ≠ ⟨0⟩ ∧
  (((sstoreAccountMap I.codeOwner σ foldDebtSlot
    (UInt256.mul (frobDartWord I) (solcSlotWord σ I (frobIlkRateSlot I)) +
      solcSlotWord σ I foldDebtSlot)).find? I.codeOwner |>.option ⟨0⟩
      (fun acc => acc.storage.findD (⟨7⟩ : UInt256) ⟨0⟩)) =
    UInt256.mul (frobDartWord I) (solcSlotWord σ I (frobIlkRateSlot I)) +
      solcSlotWord σ I foldDebtSlot) ∧
  (solcSlotWord σ I (frobIlkSpotSlot I) = ⟨0⟩ ∨
    UInt256.eq
      (UInt256.div
        (UInt256.mul
          (frobDinkWord I + solcSlotWord σ I (frobUrnInkSlot I))
          (solcSlotWord σ I (frobIlkSpotSlot I)))
        (solcSlotWord σ I (frobIlkSpotSlot I)))
      (frobDinkWord I + solcSlotWord σ I (frobUrnInkSlot I)) ≠ ⟨0⟩) ∧
  UInt256.lor
    (UInt256.isZero
      (UInt256.gt
        (UInt256.mul (solcSlotWord σ I (frobIlkRateSlot I))
          (frobDartWord I + solcSlotWord σ I (frobUrnArtSlot I)))
        (UInt256.mul
          (frobDinkWord I + solcSlotWord σ I (frobUrnInkSlot I))
          (solcSlotWord σ I (frobIlkSpotSlot I)))))
    (UInt256.land
      (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
      (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩))) ≠ ⟨0⟩ ∧
  UInt256.lor
    (UInt256.lor
      (UInt256.eq (vatSlotWord (frobUWishSlot I)
        (sstoreAccountMap I.codeOwner σ foldDebtSlot
          (UInt256.mul (frobDartWord I) (solcSlotWord σ I (frobIlkRateSlot I)) +
            solcSlotWord σ I foldDebtSlot)) I) ⟨1⟩)
      (UInt256.eq (frobUMaskedWord I) (hopeSourceWord I)))
    (UInt256.land
      (UInt256.isZero (UInt256.slt (frobDinkWord I) ⟨0⟩))
      (UInt256.isZero (UInt256.sgt (frobDartWord I) ⟨0⟩))) ≠ ⟨0⟩ ∧
  UInt256.lor
    (UInt256.lor
      (UInt256.eq (vatSlotWord (frobVWishSlot I)
        (sstoreAccountMap I.codeOwner σ foldDebtSlot
          (UInt256.mul (frobDartWord I) (solcSlotWord σ I (frobIlkRateSlot I)) +
            solcSlotWord σ I foldDebtSlot)) I) ⟨1⟩)
      (UInt256.eq (frobVMaskedWord I) (hopeSourceWord I)))
    (UInt256.isZero (UInt256.sgt (frobDinkWord I) ⟨0⟩)) ≠ ⟨0⟩ ∧
  UInt256.lor
    (UInt256.lor
      (UInt256.eq (vatSlotWord (frobWWishSlot I)
        (sstoreAccountMap I.codeOwner σ foldDebtSlot
          (UInt256.mul (frobDartWord I) (solcSlotWord σ I (frobIlkRateSlot I)) +
            solcSlotWord σ I foldDebtSlot)) I) ⟨1⟩)
      (UInt256.eq (frobWMaskedWord I) (hopeSourceWord I)))
    (UInt256.isZero (UInt256.slt (frobDartWord I) ⟨0⟩)) ≠ ⟨0⟩ ∧
  UInt256.lor
    (UInt256.isZero
      (UInt256.lt
        (UInt256.mul (solcSlotWord σ I (frobIlkRateSlot I))
          (frobDartWord I + solcSlotWord σ I (frobUrnArtSlot I)))
        (solcSlotWord σ I (frobIlkDustSlot I))))
    (UInt256.eq ⟨0⟩
      (frobDartWord I + solcSlotWord σ I (frobUrnArtSlot I))) ≠ ⟨0⟩ ∧
  (UInt256.sgt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
    UInt256.gt (frobGemNew σ I)
      (solcSlotWord (frobAfterDebt σ I) I (frobGemVSlot I)) = ⟨0⟩) ∧
  (UInt256.slt (frobDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
    UInt256.lt (frobGemNew σ I)
      (solcSlotWord (frobAfterDebt σ I) I (frobGemVSlot I)) = ⟨0⟩) ∧
  (UInt256.slt (frobDtabWord σ I) ⟨0⟩ = ⟨0⟩ ∨
    UInt256.gt (frobDaiNew σ I)
      (solcSlotWord (frobAfterGem σ I) I (frobDaiWSlot I)) = ⟨0⟩) ∧
  (UInt256.sgt (frobDtabWord σ I) ⟨0⟩ = ⟨0⟩ ∨
    UInt256.lt (frobDaiNew σ I)
      (solcSlotWord (frobAfterGem σ I) I (frobDaiWSlot I)) = ⟨0⟩)
