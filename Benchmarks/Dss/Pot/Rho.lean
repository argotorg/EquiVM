import Benchmarks.Dss.Pot.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Pot

/-! ## `rho()` public getter (time of last drip, slot 7). Group @223 arm 2. -/

def rhoWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 := potSlotWord ⟨7⟩ σ I

theorem potDecode_rho {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (rhoTransition.params.map Param.name)
      (transitionSignature rhoTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem potReachRhoBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = potBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (potSelBytes 13)) :
    ∃ k C, RD potBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨359⟩ [potSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : potSelWord I = ⟨0x20aba08b⟩ :=
    potSelWord_eq_of_beq I hsz 0x20 0xab 0xa0 0x8b ⟨0x20aba08b⟩
      (by decide +native) (by simpa [potSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat potBytecode potRootSplitPc) (potSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; decide +native
  have h163 : UInt256.gt (armSelNat potBytecode potSplit163Pc) (potSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; decide +native
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG223FirstArmPc j))
        (potSelWord I) = ⟨0⟩ := by intro j hj; interval_cases j <;> rw [hword] <;> decide +native
  have htake :
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG223FirstArmPc 2))
        (potSelWord I) ≠ ⟨0⟩ := by rw [hword]; decide +native
  exact potReachG223Body 2 (by omega) ⟨359⟩ hcode hwv hsz hsize hroot h163 heq0 htake
    (by jump_dest) (by decide +native)

theorem potRhoBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = potBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some rhoTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (rhoTransition.params.map Param.name)
        (transitionSignature rhoTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD potBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨359⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ rhoTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (rhoWord σ_solm I).toNat))])) := by
    simpa [rhoTransition, rhoWord, potSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      potUint256GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := rhoRef) (er := ({ base := "rho", steps := [] } : EvaledStorageRef))
        (slot := ⟨7⟩)
        (by simp only [initState]; exact hwv) (by simp [rhoRef])
        (by simp [evalStorageRef, evalStorageRefSteps, rhoRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact potUint256GetterBodyCore (entry := ⟨359⟩) (returnPc := ⟨341⟩)
    (routine := ⟨984⟩) (slot := ⟨7⟩)
    hcode hdispatch hdecode hreach hAccounts
    (by unfold solcGetterEntryWf; repeat' first | apply And.intro | decide +native)
    (by unfold solcWordSlotGetterWf; repeat' first | apply And.intro | decide +native)
    (by jump_dest) (by jump_dest)
    (by unfold solcReturnWordFromMemWf; repeat' first | apply And.intro | decide +native)
    (by rfl) (by simpa [rhoWord] using hbody)

theorem potRhoBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = potBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (potSelBytes 13))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (potSelBytes 13) rfl hsel
  exact potRhoBodyCore hcode hwv (potDispatchRho hsel) (potDecode_rho hsz)
    (potReachRhoBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel) hAccounts

end Benchmarks.Dss.Pot
