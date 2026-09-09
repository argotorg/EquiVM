import Benchmarks.Dss.Dog.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Dog.Immutables

namespace Benchmarks.Dss.Dog

theorem dogDecode_Dirt {v : DogImmutables} {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode (DirtTransition.params.map Param.name)
      (transitionSignature DirtTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem dogReachDirtBody {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (dogSelBytes 0)) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨837⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : solcSelectorWord I = ⟨0xeda6e121⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xed 0xa6 0xe1 0x21 ⟨0xeda6e121⟩
      (by decide +native) (by simpa [dogSelBytes] using hsel)
  obtain ⟨k32, C32, h32⟩ :=
    dogReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize
  have hrootWidth : armTgtWidth code (⟨32⟩ : UInt256) = 2 := by
    dsimp [armTgtWidth]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨32⟩ : UInt256))
      hpatch (by decide +native)]
    decide +native
  have hhighWidth : armTgtWidth code (⟨43⟩ : UInt256) = 2 := by
    dsimp [armTgtWidth]
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
      UInt256.gt (armSelNat code (⟨43⟩ : UInt256)) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    dsimp [armSelNat]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPush4Pc (⟨43⟩ : UInt256))
      hpatch (by decide +native)]
    decide +native
  have h54 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨54⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k32 + 5 + 5) (C32 + 22 + 22) := by
    simpa [selArmNextPc, hhighWidth] using
      RD.selectorSplitNotTakenAuto h43 (dogHighSplitWellFormed hpatch) hhigh (by simp)
  have hchop : UInt256.eq (dogSelectorWord 4) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    decide +native
  have hilks : UInt256.eq (dogSelectorWord 11) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    decide +native
  have hfileIlkClip : UInt256.eq (dogSelectorWord 10) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    decide +native
  have hbark : UInt256.eq (dogSelectorWord 2) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    decide +native
  have hdirt : UInt256.eq (dogSelectorWord 0) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  have h65 := by
    simpa [selArmNextPc] using
      h54.selectorArmNotTaken (selNat := dogSelectorWord 4) (tgt := (⟨629⟩ : UInt256))
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
        hchop
        (by simp)
  have h76 := by
    simpa [selArmNextPc] using
      h65.selectorArmNotTaken (selNat := dogSelectorWord 11) (tgt := (⟨658⟩ : UInt256))
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
        hilks
        (by simp)
  have h87 := by
    simpa [selArmNextPc] using
      h76.selectorArmNotTaken (selNat := dogSelectorWord 10) (tgt := (⟨735⟩ : UInt256))
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
        hfileIlkClip
        (by simp)
  have h98 := by
    simpa [selArmNextPc] using
      h87.selectorArmNotTaken (selNat := dogSelectorWord 2) (tgt := (⟨785⟩ : UInt256))
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
        hbark
        (by simp)
  have h837 := by
    simpa using
      h98.selectorArmTaken (selNat := dogSelectorWord 0) (tgt := (⟨837⟩ : UInt256))
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
        hdirt
        (dogPatchedDJumpPrefix1405 ⟨837⟩ hpatch (by decide +native))
        (by simp)
  exact ⟨_, _, h837⟩

theorem dogDirtBodyCore {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (_hpatch : patchRuntime dogBytecode (patches v) = some code)
    (_hcode : I.code = code)
    (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (_hwv : I.weiValue = ⟨0⟩)
    (_hsel : selIs I (dogSelBytes 0))
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (dogSelBytes 0) rfl _hsel
  have hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ DirtTransition.body
        (.returned { contract := contract v, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (dogSlotWord ⟨5⟩ σ_solm I).toNat))])) := by
    simpa [DirtTransition, dogSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      dogUint256GetterBodyReturns v
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := DirtRef) (er := ({ base := "Dirt", steps := [] } : EvaledStorageRef))
        (slot := ⟨5⟩)
        (by simp only [initState]; exact _hwv) (by simp [DirtRef])
        (by simp [evalStorageRef, evalStorageRefSteps, DirtRef, EvalResult.bind, pure, bind])
        (by simp [storageTypeAt?, contract, storageDecls, uint256St]) (by rfl)
  exact dogUint256GetterBodyCore (entry := ⟨837⟩) (returnPc := ⟨448⟩)
    (routine := ⟨4536⟩) (slot := ⟨5⟩)
    _hcode (dogDispatchDirt _hsel) (dogDecode_Dirt (v := v) hsz)
    (dogReachDirtBody (g := Sat256.ofUInt256 g) _hpatch _hcode _hwv hsz _hsize _hsel)
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
