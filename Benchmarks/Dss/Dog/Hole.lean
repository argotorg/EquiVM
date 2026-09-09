import Benchmarks.Dss.Dog.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Dog.Immutables

namespace Benchmarks.Dss.Dog

theorem dogDecode_Hole {v : DogImmutables} {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode (HoleTransition.params.map Param.name)
      (transitionSignature HoleTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem dogReachHoleBody {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (dogSelBytes 1)) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨504⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : solcSelectorWord I = ⟨0xaf7cfeb1⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xaf 0x7c 0xfe 0xb1 ⟨0xaf7cfeb1⟩
      (by decide +native) (by simpa [dogSelBytes] using hsel)
  obtain ⟨k32, C32, h32⟩ :=
    dogReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize
  have hrootWidth : armTgtWidth code (⟨32⟩ : UInt256) = 2 := by
    dsimp [armTgtWidth]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨32⟩ : UInt256))
      hpatch (by decide +native)]
    decide +native
  have hhighTgt : armTgt code (⟨43⟩ : UInt256) = ⟨113⟩ := by
    dsimp [armTgt]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨43⟩ : UInt256))
      hpatch (by decide +native)]
    decide +native
  have hroot :
      UInt256.gt (armSelNat code (⟨32⟩ : UInt256)) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    dsimp [armSelNat]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPush4Pc (⟨32⟩ : UInt256))
      hpatch (by decide +native)]
    decide +native
  have h43 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨43⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [selArmNextPc, hrootWidth] using
      RD.selectorSplitNotTakenAuto h32 (dogRootSplitWellFormed hpatch) hroot (by simp)
  have hhigh :
      UInt256.gt (armSelNat code (⟨43⟩ : UInt256)) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [hword]
    dsimp [armSelNat]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPush4Pc (⟨43⟩ : UInt256))
      hpatch (by decide +native)]
    decide +native
  have h113 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨113⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k32 + 5 + 5) (C32 + 22 + 22) := by
    simpa [hhighTgt] using
      RD.selectorSplitTakenAuto h43 (dogHighSplitWellFormed hpatch) hhigh
        (by
          rw [hhighTgt]
          exact dogPatchedDJumpPrefix1405 ⟨113⟩ hpatch (by decide +native))
        (by simp)
  have h114 := h113.jumpdest
    (by
      rw [dogDecodePatchedEqTemplate1405 (pc := ⟨113⟩) hpatch (by decide +native)]
      decide +native)
    (by simp only [List.length_singleton]; omega)
  have hhole : UInt256.eq (dogSelectorWord 1) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  have h504 := by
    simpa using
      h114.selectorArmTaken (selNat := dogSelectorWord 1) (tgt := (⟨504⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        hhole
        (dogPatchedDJumpPrefix1405 ⟨504⟩ hpatch (by decide +native))
        (by simp)
  exact ⟨_, _, h504⟩

theorem dogHoleBodyCore {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (_hpatch : patchRuntime dogBytecode (patches v) = some code)
    (_hcode : I.code = code)
    (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (_hwv : I.weiValue = ⟨0⟩)
    (_hsel : selIs I (dogSelBytes 1))
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (dogSelBytes 1) rfl _hsel
  have hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ HoleTransition.body
        (.returned { contract := contract v, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (dogSlotWord ⟨4⟩ σ_solm I).toNat))])) := by
    simpa [HoleTransition, dogSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      dogUint256GetterBodyReturns v
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := HoleRef) (er := ({ base := "Hole", steps := [] } : EvaledStorageRef))
        (slot := ⟨4⟩)
        (by simp only [initState]; exact _hwv) (by simp [HoleRef])
        (by simp [evalStorageRef, evalStorageRefSteps, HoleRef, EvalResult.bind, pure, bind])
        (by simp [storageTypeAt?, contract, storageDecls, uint256St]) (by rfl)
  exact dogUint256GetterBodyCore (entry := ⟨504⟩) (returnPc := ⟨448⟩)
    (routine := ⟨1912⟩) (slot := ⟨4⟩)
    _hcode (dogDispatchHole _hsel) (dogDecode_Hole (v := v) hsz)
    (dogReachHoleBody (g := Sat256.ofUInt256 g) _hpatch _hcode _hwv hsz _hsize _hsel)
    _hAccounts
    (by
      unfold solcGetterEntryWf
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplate1405 _hpatch (by decide +native)]
          decide +native)
    (by
      unfold solcWordSlotGetterWf
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplateAway _hpatch (by decide +native) (by decide +native)]
          decide +native)
    (dogPatchedJumpDest _hpatch (by decide +native))
    (dogPatchedDJumpPrefix1405 ⟨448⟩ _hpatch (by decide +native))
    (by
      unfold solcReturnWordFromMemWf
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplate1405 _hpatch (by decide +native)]
          decide +native)
    (by rfl) (by simpa [dogSlotWord] using hbody)

end Benchmarks.Dss.Dog
