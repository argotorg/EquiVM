import Benchmarks.Dss.Flopper.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Flopper

/-! ## `tau()` getter -/

def tauWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flopperUint48Offset6Word ⟨6⟩ σ I

theorem flopperDecode_tau {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (tauTransition.params.map Param.name)
      (transitionSignature tauTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem flopperReachTauBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flopperSelBytes 13)) :
    ∃ k C, RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨833⟩ [flopperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : flopperSelWord I = ⟨0xcfc4af55⟩ := by
    simpa [flopperSelWord, solcSelectorWord] using
      solcSelectorWord_eq_of_beq I hsz 0xcf 0xc4 0xaf 0x55 ⟨0xcfc4af55⟩
        (by native_decide) (by simpa [flopperSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat flopperBytecode flopperRootSplitPc)
      (flopperSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhigh : UInt256.gt (armSelNat flopperBytecode flopperHighSplitPc)
      (flopperSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  obtain ⟨_, _, hfirst⟩ :=
    flopperReachHighHighFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh
  have heq0 : ∀ j, j < 2 →
      UInt256.eq
        (armSelNat flopperBytecode (nthArmPc flopperBytecode flopperHighHighFirstArmPc j))
        (flopperSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq
        (armSelNat flopperBytecode (nthArmPc flopperBytecode flopperHighHighFirstArmPc 2))
        (flopperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo ⟨833⟩ 2 hfirst
    (fun j hj => flopperHighHighArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem flopperTauBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some tauTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (tauTransition.params.map Param.name)
        (transitionSignature tauTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨833⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ tauTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (tauWord σ_solm I).toNat))])) := by
    simpa [tauTransition, tauWord, flopperUint48Offset6Word, initState,
      Solm.EVM.storageLoad, State.lookupAccount] using
      flopperUint48GetterBodyReturns_offset6
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := tauRef) (er := ({ base := "tau", steps := [] } : EvaledStorageRef))
        (slot := ⟨6⟩)
        (by simp only [initState]; exact hwv) (by simp [tauRef])
        (by simp [evalStorageRef, evalStorageRefSteps, tauRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact flopperUint48Offset6GetterBodyCore (entry := ⟨833⟩) (returnPc := ⟨506⟩)
    (routine := ⟨4265⟩) (slot := ⟨6⟩)
    hcode hdispatch hdecode hreach hAccounts
    (by
      unfold solcGetterEntryWf
      repeat' first | apply And.intro | native_decide)
    (by
      unfold flopperUint48Offset6SlotGetterWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest)
    (by jump_dest)
    (by
      unfold flopperReturnUint48FromMemWf
      repeat' first | apply And.intro | native_decide)
    (by rfl) (by simpa [tauWord] using hbody)

theorem flopperTauBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flopperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flopperSelBytes 13))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flopperSelBytes 13) rfl hsel
  exact flopperTauBodyCore hcode hwv (flopperDispatchTau hsel) (flopperDecode_tau hsz)
    (flopperReachTauBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel) hAccounts

end Benchmarks.Dss.Flopper
