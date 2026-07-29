import Benchmarks.Dss.Jug.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Jug

/-! ## `base()` getter -/

def baseWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  jugSlotWord ⟨4⟩ σ I

theorem jugDecode_base {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (baseTransition.params.map Param.name)
      (transitionSignature baseTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem jugReachBaseBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = jugBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (jugSelBytes 0)) :
    ∃ k C, RD jugBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨375⟩ [jugSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : jugSelWord I = ⟨0x5001f3b5⟩ :=
    jugSelWord_eq_of_beq I hsz 0x50 0x01 0xf3 0xb5 ⟨0x5001f3b5⟩
      (by native_decide) (by simpa [jugSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat jugBytecode jugRootSplitPc) (jugSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 5 →
      UInt256.eq (armSelNat jugBytecode (nthArmPc jugBytecode jugLowFirstArmPc j))
        (jugSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat jugBytecode (nthArmPc jugBytecode jugLowFirstArmPc 5))
        (jugSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact jugReachLowBody 5 (by omega) ⟨375⟩ hcode hwv hsz hsize hroot heq0 htake
    (by jump_dest) (by native_decide)

theorem jugBaseBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = jugBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some baseTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (baseTransition.params.map Param.name)
        (transitionSignature baseTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨375⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ baseTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (baseWord σ_solm I).toNat))])) := by
    simpa [baseTransition, baseWord, jugSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      jugUint256GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := baseRef) (er := ({ base := "base", steps := [] } : EvaledStorageRef))
        (slot := ⟨4⟩)
        (by simp only [initState]; exact hwv) (by simp [baseRef])
        (by simp [evalStorageRef, evalStorageRefSteps, baseRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact jugUint256GetterBodyCore (entry := ⟨375⟩) (returnPc := ⟨357⟩)
    (routine := ⟨1699⟩) (slot := ⟨4⟩)
    hcode hdispatch hdecode hreach hAccounts
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
    (by rfl) (by simpa [baseWord] using hbody)

theorem jugBaseBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = jugBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (jugSelBytes 0))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (jugSelBytes 0) rfl hsel
  exact jugBaseBodyCore hcode hwv (jugDispatchBase hsel) (jugDecode_base hsz)
    (jugReachBaseBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel) hAccounts

end Benchmarks.Dss.Jug
