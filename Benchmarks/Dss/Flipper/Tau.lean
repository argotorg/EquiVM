import Benchmarks.Dss.Flipper.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flipper

/-! ## `tau()` getter -/

def tauWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flipperUint48Offset6Word ⟨5⟩ σ I

theorem flipperDecode_tau {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (tauTransition.params.map Param.name)
      (transitionSignature tauTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem flipperReachTauBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flipperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flipperSelBytes 12)) :
    ∃ k C, RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨870⟩ [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : flipperSelWord I = ⟨0xcfc4af55⟩ :=
    flipperSelWord_eq_of_beq I hsz 0xcf 0xc4 0xaf 0x55 ⟨0xcfc4af55⟩
      (by decide +native) (by simpa [flipperSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat flipperBytecode flipperRootSplitPc)
      (flipperSelWord I) = ⟨0⟩ := by
    rw [hword]
    decide +native
  have hlow : UInt256.gt (armSelNat flipperBytecode flipperLowSplitPc)
      (flipperSelWord I) = ⟨0⟩ := by
    rw [hword]
    decide +native
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperLowHighFirstArmPc j))
        (flipperSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperLowHighFirstArmPc 0))
        (flipperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  exact flipperReachLowHighBody 0 (by omega) ⟨870⟩ hcode hwv hsz hsize hroot hlow
    heq0 htake (by jump_dest) (by decide +native)

theorem flipperTauBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flipperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flipperSelBytes 12))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flipperSelBytes 12) rfl hsel
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ tauTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (tauWord σ_solm I).toNat))])) := by
    simpa [tauTransition, tauWord, flipperUint48Offset6Word, flipperSlotWord, initState,
      Solm.EVM.storageLoad, State.lookupAccount] using
      flipperUint48Offset6GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := tauRef) (er := ({ base := "tau", steps := [] } : EvaledStorageRef))
        (slot := ⟨5⟩)
        (by simp only [initState]; exact hwv) (by simp [tauRef])
        (by simp [evalStorageRef, evalStorageRefSteps, tauRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact flipperUint48Offset6GetterBodyCore (entry := ⟨870⟩) (routine := ⟨5794⟩)
    (slot := ⟨5⟩)
    hcode (flipperDispatchTau hsel) (flipperDecode_tau hsz)
    (flipperReachTauBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel) hAccounts
    (by
      unfold solcGetterEntryWf
      repeat' first | apply And.intro | decide +native)
    (by
      unfold solcUint48Offset6SlotGetterWf
      repeat' first | apply And.intro | decide +native)
    (by jump_dest)
    (by jump_dest)
    (by rfl) (by simpa [tauWord] using hbody)

end Benchmarks.Dss.Flipper
