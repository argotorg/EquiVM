import Benchmarks.Dss.Pot.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Pot

/-! ## `chi()` public getter (rate accumulator, slot 4). Group @54 arm 3. -/

def chiWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 := potSlotWord ⟨4⟩ σ I

theorem potDecode_chi {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (chiTransition.params.map Param.name)
      (transitionSignature chiTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem potReachChiBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = potBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (potSelBytes 2)) :
    ∃ k C, RD potBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨629⟩ [potSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : potSelWord I = ⟨0xc92aecc4⟩ :=
    potSelWord_eq_of_beq I hsz 0xc9 0x2a 0xec 0xc4 ⟨0xc92aecc4⟩
      (by native_decide) (by simpa [potSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat potBytecode potRootSplitPc) (potSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have h43 : UInt256.gt (armSelNat potBytecode potSplit43Pc) (potSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG54FirstArmPc j))
        (potSelWord I) = ⟨0⟩ := by intro j hj; interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG54FirstArmPc 3))
        (potSelWord I) ≠ ⟨0⟩ := by rw [hword]; native_decide
  exact potReachG54Body 3 (by omega) ⟨629⟩ hcode hwv hsz hsize hroot h43 heq0 htake
    (by jump_dest) (by native_decide)

theorem potChiBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = potBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some chiTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (chiTransition.params.map Param.name)
        (transitionSignature chiTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD potBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨629⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ chiTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (chiWord σ_solm I).toNat))])) := by
    simpa [chiTransition, chiWord, potSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      potUint256GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := chiRef) (er := ({ base := "chi", steps := [] } : EvaledStorageRef))
        (slot := ⟨4⟩)
        (by simp only [initState]; exact hwv) (by simp [chiRef])
        (by simp [evalStorageRef, evalStorageRefSteps, chiRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact potUint256GetterBodyCore (entry := ⟨629⟩) (returnPc := ⟨341⟩)
    (routine := ⟨2137⟩) (slot := ⟨4⟩)
    hcode hdispatch hdecode hreach hAccounts
    (by unfold solcGetterEntryWf; repeat' first | apply And.intro | native_decide)
    (by unfold solcWordSlotGetterWf; repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by jump_dest)
    (by unfold solcReturnWordFromMemWf; repeat' first | apply And.intro | native_decide)
    (by rfl) (by simpa [chiWord] using hbody)

theorem potChiBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = potBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (potSelBytes 2))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (potSelBytes 2) rfl hsel
  exact potChiBodyCore hcode hwv (potDispatchChi hsel) (potDecode_chi hsz)
    (potReachChiBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel) hAccounts

end Benchmarks.Dss.Pot
