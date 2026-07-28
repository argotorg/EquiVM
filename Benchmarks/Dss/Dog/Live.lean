import Benchmarks.Dss.Dog.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Dog.Immutables

namespace Benchmarks.Dss.Dog

theorem dogDecode_live {v : DogImmutables} {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode (liveTransition.params.map Param.name)
      (transitionSignature liveTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem dogReachLiveBody {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (dogSelBytes 12)) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨440⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : solcSelectorWord I = ⟨0x957aa58c⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x95 0x7a 0xa5 0x8c ⟨0x957aa58c⟩
      (by native_decide) (by simpa [dogSelBytes] using hsel)
  obtain ⟨k32, C32, h32⟩ :=
    dogReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize
  have hrootTgt : armTgt code (⟨32⟩ : UInt256) = ⟨162⟩ := by
    dsimp [armTgt]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨32⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  have hlowWidth : armTgtWidth code (⟨163⟩ : UInt256) = 2 := by
    dsimp [armTgtWidth]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨163⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  have hroot :
      UInt256.gt (armSelNat code (⟨32⟩ : UInt256)) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [hword]
    dsimp [armSelNat]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPush4Pc (⟨32⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  have h162 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨162⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [hrootTgt] using
      RD.selectorSplitTakenAuto h32 (dogRootSplitWellFormed hpatch) hroot
        (by
          rw [hrootTgt]
          exact dogPatchedDJumpPrefix1405 ⟨162⟩ hpatch (by native_decide))
        (by simp)
  have h163 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨163⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k32 + 5 + 1) (C32 + 22 + 1) := by
    simpa using
      h162.jumpdest
        (by
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨162⟩) hpatch (by native_decide)]
          native_decide)
        (by simp only [List.length_singleton]; omega)
  have hlow :
      UInt256.gt (armSelNat code (⟨163⟩ : UInt256)) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    dsimp [armSelNat]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPush4Pc (⟨163⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  have h174 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨174⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k32 + 5 + 1 + 5) (C32 + 22 + 1 + 22) := by
    simpa [selArmNextPc, hlowWidth] using
      RD.selectorSplitNotTakenAuto h163 (dogLowSplitWellFormed hpatch) hlow (by simp)
  have hrely : UInt256.eq (dogSelectorWord 13) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hcage : UInt256.eq (dogSelectorWord 3) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlive : UInt256.eq (dogSelectorWord 12) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have h185 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨185⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k32 + 5 + 1 + 5 + 5) (C32 + 22 + 1 + 22 + 22) := by
    simpa [selArmNextPc] using
      h174.selectorArmNotTaken (selNat := dogSelectorWord 13) (tgt := (⟨394⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨174⟩) hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        hrely
        (by simp)
  have h196 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨196⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k32 + 5 + 1 + 5 + 5 + 5) (C32 + 22 + 1 + 22 + 22 + 22) := by
    simpa [selArmNextPc] using
      h185.selectorArmNotTaken (selNat := dogSelectorWord 3) (tgt := (⟨432⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨185⟩) hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        hcage
        (by simp)
  have h440 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨440⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k32 + 5 + 1 + 5 + 5 + 5 + 5)
      (C32 + 22 + 1 + 22 + 22 + 22 + 22) := by
    simpa using
      h196.selectorArmTaken (selNat := dogSelectorWord 12) (tgt := (⟨440⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨196⟩) hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        hlive
        (dogPatchedDJumpPrefix1405 ⟨440⟩ hpatch (by native_decide))
        (by simp)
  exact ⟨_, _, h440⟩

theorem dogLiveBodyCore {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (_hpatch : patchRuntime dogBytecode (patches v) = some code)
    (_hcode : I.code = code)
    (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (_hwv : I.weiValue = ⟨0⟩)
    (_hsel : selIs I (dogSelBytes 12))
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (dogSelBytes 12) rfl _hsel
  have hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ liveTransition.body
        (.returned { contract := contract v, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (dogSlotWord ⟨3⟩ σ_solm I).toNat))])) := by
    simpa [liveTransition, dogSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      dogUint256GetterBodyReturns v
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := liveRef) (er := ({ base := "live", steps := [] } : EvaledStorageRef))
        (slot := ⟨3⟩)
        (by simp only [initState]; exact _hwv) (by simp [liveRef])
        (by simp [evalStorageRef, evalStorageRefSteps, liveRef, EvalResult.bind, pure, bind])
        (by simp [storageTypeAt?, contract, storageDecls, uint256St]) (by rfl)
  exact dogUint256GetterBodyCore (entry := ⟨440⟩) (returnPc := ⟨448⟩)
    (routine := ⟨1749⟩) (slot := ⟨3⟩)
    _hcode (dogDispatchLive _hsel) (dogDecode_live (v := v) hsz)
    (dogReachLiveBody (g := Sat256.ofUInt256 g) _hpatch _hcode _hwv hsz _hsize _hsel)
    _hAccounts
    (by
      unfold solcGetterEntryWf
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplate1405 _hpatch (by native_decide)]
          native_decide)
    (by
      unfold solcWordSlotGetterWf
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplateDisjoint _hpatch (by native_decide) (by
            intro p hp
            have hm := dogPatchOffsetMem v p hp
            simp [dogPatchOffsets] at hm
            rcases hm with h | h | h | h
            · rw [h]
              native_decide
            · rw [h]
              native_decide
            · rw [h]
              native_decide
            · rw [h]
              native_decide)]
          native_decide)
    (dogPatchedJumpDest _hpatch (by native_decide))
    (dogPatchedDJumpPrefix1405 ⟨448⟩ _hpatch (by native_decide))
    (by
      unfold solcReturnWordFromMemWf
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplate1405 _hpatch (by native_decide)]
          native_decide)
    (by rfl) (by simpa [dogSlotWord] using hbody)

end Benchmarks.Dss.Dog
