import Benchmarks.Dss.Pot.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Pot

/-! ## `dsr()` public getter (dai savings rate, slot 3). Group @174 arm 2. -/

def dsrWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 := potSlotWord ⟨3⟩ σ I

theorem potDecode_dsr {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (dsrTransition.params.map Param.name)
      (transitionSignature dsrTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem potReachDsrBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = potBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (potSelBytes 5)) :
    ∃ k C, RD potBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨446⟩ [potSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : potSelWord I = ⟨0x487bf082⟩ :=
    potSelWord_eq_of_beq I hsz 0x48 0x7b 0xf0 0x82 ⟨0x487bf082⟩
      (by native_decide) (by simpa [potSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat potBytecode potRootSplitPc) (potSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have h163 : UInt256.gt (armSelNat potBytecode potSplit163Pc) (potSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG174FirstArmPc j))
        (potSelWord I) = ⟨0⟩ := by intro j hj; interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG174FirstArmPc 2))
        (potSelWord I) ≠ ⟨0⟩ := by rw [hword]; native_decide
  exact potReachG174Body 2 (by omega) ⟨446⟩ hcode hwv hsz hsize hroot h163 heq0 htake
    (by jump_dest) (by native_decide)

theorem potDsrBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = potBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some dsrTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dsrTransition.params.map Param.name)
        (transitionSignature dsrTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD potBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨446⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ dsrTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (dsrWord σ_solm I).toNat))])) := by
    simpa [dsrTransition, dsrWord, potSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      potUint256GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := dsrRef) (er := ({ base := "dsr", steps := [] } : EvaledStorageRef))
        (slot := ⟨3⟩)
        (by simp only [initState]; exact hwv) (by simp [dsrRef])
        (by simp [evalStorageRef, evalStorageRefSteps, dsrRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact potUint256GetterBodyCore (entry := ⟨446⟩) (returnPc := ⟨341⟩)
    (routine := ⟨1351⟩) (slot := ⟨3⟩)
    hcode hdispatch hdecode hreach hAccounts
    (by unfold solcGetterEntryWf; repeat' first | apply And.intro | native_decide)
    (by unfold solcWordSlotGetterWf; repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by jump_dest)
    (by unfold solcReturnWordFromMemWf; repeat' first | apply And.intro | native_decide)
    (by rfl) (by simpa [dsrWord] using hbody)

theorem potDsrBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = potBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (potSelBytes 5))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (potSelBytes 5) rfl hsel
  exact potDsrBodyCore hcode hwv (potDispatchDsr hsel) (potDecode_dsr hsz)
    (potReachDsrBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel) hAccounts

end Benchmarks.Dss.Pot
