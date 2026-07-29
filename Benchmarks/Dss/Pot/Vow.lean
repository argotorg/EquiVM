import Benchmarks.Dss.Pot.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Pot

/-! ## `vow()` public getter (debt engine address, slot 6). Group @174 arm 3. -/

theorem potDecode_vow {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (vowTransition.params.map Param.name)
      (transitionSignature vowTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem potReachVowBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = potBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (potSelBytes 15)) :
    ∃ k C, RD potBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨454⟩ [potSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : potSelWord I = ⟨0x626cb3c5⟩ :=
    potSelWord_eq_of_beq I hsz 0x62 0x6c 0xb3 0xc5 ⟨0x626cb3c5⟩
      (by native_decide) (by simpa [potSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat potBytecode potRootSplitPc) (potSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have h163 : UInt256.gt (armSelNat potBytecode potSplit163Pc) (potSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG174FirstArmPc j))
        (potSelWord I) = ⟨0⟩ := by intro j hj; interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG174FirstArmPc 3))
        (potSelWord I) ≠ ⟨0⟩ := by rw [hword]; native_decide
  exact potReachG174Body 3 (by omega) ⟨454⟩ hcode hwv hsz hsize hroot h163 heq0 htake
    (by jump_dest) (by native_decide)

theorem potVowBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = potBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some vowTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (vowTransition.params.map Param.name)
        (transitionSignature vowTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD potBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨454⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ vowTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat (potAddressReturnWord ⟨6⟩ σ_solm I).toNat))])) := by
    simpa [vowTransition, potAddressReturnWord, potSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      potAddressGetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := vowRef) (er := ({ base := "vow", steps := [] } : EvaledStorageRef))
        (slot := ⟨6⟩)
        (by simp only [initState]; exact hwv) (by simp [vowRef])
        (by simp [evalStorageRef, evalStorageRefSteps, vowRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact potAddressGetterBodyCore (entry := ⟨454⟩) (returnPc := ⟨418⟩)
    (routine := ⟨1357⟩) (slot := ⟨6⟩)
    hcode hdispatch hdecode hreach hAccounts
    (by unfold solcGetterEntryWf; repeat' first | apply And.intro | native_decide)
    (by unfold solcAddressSlotGetterWf; repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by jump_dest)
    (by unfold solcReturnAddressFromMemWf; repeat' first | apply And.intro | native_decide)
    (by rfl) hbody

theorem potVowBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = potBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (potSelBytes 15))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (potSelBytes 15) rfl hsel
  exact potVowBodyCore hcode hwv (potDispatchVow hsel) (potDecode_vow hsz)
    (potReachVowBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel) hAccounts

end Benchmarks.Dss.Pot
