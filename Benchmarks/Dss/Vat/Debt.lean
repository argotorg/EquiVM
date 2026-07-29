import Benchmarks.Dss.Vat.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Vat

/-! ## `debt()` getter -/

def debtWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  vatSlotWord ⟨7⟩ σ I

theorem vatDecode_debt {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (debtTransition.params.map Param.name)
      (transitionSignature debtTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem vatReachDebtBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vatSelBytes 4)) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨457⟩ [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vatSelWord I = ⟨0x0dca59c1⟩ :=
    vatSelWord_eq_of_beq I hsz 0x0d 0xca 0x59 0xc1 ⟨0x0dca59c1⟩
      (by native_decide) (by simpa [vatSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlow : UInt256.gt (armSelNat vatBytecode vatLowSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlowlow :
      UInt256.gt (armSelNat vatBytecode vatLowLowSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms419FirstPc j))
        (vatSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms419FirstPc 0))
        (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vatReachArms419Body 0 (by omega) ⟨457⟩ hcode hwv hsz hsize
    hroot hlow hlowlow heq0 htake (by jump_dest) (by native_decide)

theorem vatDebtBodyCore : VatBodyTheorem 4 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize _hperm hwv hsel hAccounts
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (vatSelBytes 4) rfl hsel
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ debtTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (debtWord σ_solm I).toNat))])) := by
    simpa [debtTransition, debtWord, vatSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      vatUint256GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := debtRef) (er := ({ base := "debt", steps := [] } : EvaledStorageRef))
        (slot := ⟨7⟩)
        (by simp only [initState]; exact hwv) (by simp [debtRef])
        (by simp [evalStorageRef, evalStorageRefSteps, debtRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact vatUint256GetterBodyCore (entry := ⟨457⟩) (returnPc := ⟨465⟩)
    (routine := ⟨1626⟩) (slot := ⟨7⟩)
    hcode (vatDispatchDebt hsel) (vatDecode_debt hsz)
    (vatReachDebtBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)
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
    (by rfl) (by simpa [debtWord] using hbody)

end Benchmarks.Dss.Vat
