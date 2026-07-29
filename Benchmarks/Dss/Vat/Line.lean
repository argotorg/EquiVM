import Benchmarks.Dss.Vat.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Vat

/-! ## `Line()` getter -/

def LineWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  vatSlotWord ⟨9⟩ σ I

theorem vatDecode_Line {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (LineTransition.params.map Param.name)
      (transitionSignature LineTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem vatReachLineBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vatSelBytes 0)) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1295⟩ [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vatSelWord I = ⟨0xbabe8a3f⟩ :=
    vatSelWord_eq_of_beq I hsz 0xba 0xbe 0x8a 0x3f ⟨0xbabe8a3f⟩
      (by native_decide) (by simpa [vatSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhigh : UInt256.gt (armSelNat vatBytecode vatHighSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhighlow :
      UInt256.gt (armSelNat vatBytecode vatHighLowSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms163FirstPc j))
        (vatSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms163FirstPc 3))
        (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vatReachArms163Body 3 (by omega) ⟨1295⟩ hcode hwv hsz hsize
    hroot hhigh hhighlow heq0 htake (by jump_dest) (by native_decide)

theorem vatLineBodyCore : VatBodyTheorem 0 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize _hperm hwv hsel hAccounts
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (vatSelBytes 0) rfl hsel
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ LineTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (LineWord σ_solm I).toNat))])) := by
    simpa [LineTransition, LineWord, vatSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      vatUint256GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := LineRef) (er := ({ base := "Line", steps := [] } : EvaledStorageRef))
        (slot := ⟨9⟩)
        (by simp only [initState]; exact hwv) (by simp [LineRef])
        (by simp [evalStorageRef, evalStorageRefSteps, LineRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact vatUint256GetterBodyCore (entry := ⟨1295⟩) (returnPc := ⟨465⟩)
    (routine := ⟨5868⟩) (slot := ⟨9⟩)
    hcode (vatDispatchLine hsel) (vatDecode_Line hsz)
    (vatReachLineBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)
    hAccounts
    (by
      unfold solcGetterEntryWf
      repeat' first | apply And.intro | native_decide)
    (by
      unfold solcWordSlotGetterWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest)
    (by jump_dest)
    (by
      unfold solcReturnWordFromMemWf
      repeat' first | apply And.intro | native_decide)
    (by rfl) (by simpa [LineWord] using hbody)

end Benchmarks.Dss.Vat
