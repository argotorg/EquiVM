import Benchmarks.Dss.Flipper.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flipper

/-! ## `beg()` getter -/

def begWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flipperSlotWord ⟨4⟩ σ I

theorem flipperDecode_beg {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (begTransition.params.map Param.name)
      (transitionSignature begTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem flipperReachBegBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flipperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flipperSelBytes 0)) :
    ∃ k C, RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨749⟩ [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : flipperSelWord I = ⟨0x7d780d82⟩ :=
    flipperSelWord_eq_of_beq I hsz 0x7d 0x78 0x0d 0x82 ⟨0x7d780d82⟩
      (by decide +native) (by simpa [flipperSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat flipperBytecode flipperRootSplitPc)
      (flipperSelWord I) = ⟨0⟩ := by
    rw [hword]
    decide +native
  have hlow : UInt256.gt (armSelNat flipperBytecode flipperLowSplitPc)
      (flipperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperLowLowFirstArmPc j))
        (flipperSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperLowLowFirstArmPc 0))
        (flipperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  exact flipperReachLowLowBody 0 (by omega) ⟨749⟩ hcode hwv hsz hsize hroot hlow
    heq0 htake (by jump_dest) (by decide +native)

theorem flipperBegBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flipperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flipperSelBytes 0))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flipperSelBytes 0) rfl hsel
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ begTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (begWord σ_solm I).toNat))])) := by
    simpa [begTransition, begWord, flipperSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      flipperUint256GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := begRef) (er := ({ base := "beg", steps := [] } : EvaledStorageRef))
        (slot := ⟨4⟩)
        (by simp only [initState]; exact hwv) (by simp [begRef])
        (by simp [evalStorageRef, evalStorageRefSteps, begRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact flipperUint256GetterBodyCore (entry := ⟨749⟩) (returnPc := ⟨426⟩)
    (routine := ⟨5227⟩) (slot := ⟨4⟩)
    hcode (flipperDispatchBeg hsel) (flipperDecode_beg hsz)
    (flipperReachBegBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel) hAccounts
    (by
      unfold solcGetterEntryWf
      repeat' first | apply And.intro | decide +native)
    (by
      unfold solcWordSlotGetterWf
      repeat' first | apply And.intro | decide +native)
    (by jump_dest)
    (by jump_dest)
    (by
      unfold solcReturnWordFromMemWf
      repeat' first | apply And.intro | decide +native)
    (by rfl) (by simpa [begWord] using hbody)

end Benchmarks.Dss.Flipper
