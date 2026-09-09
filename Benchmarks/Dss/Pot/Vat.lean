import Benchmarks.Dss.Pot.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Pot

/-! ## `vat()` public getter (CDP engine address, slot 5). Group @174 arm 1. -/

theorem potDecode_vat {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (vatTransition.params.map Param.name)
      (transitionSignature vatTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem potReachVatBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = potBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (potSelBytes 14)) :
    ∃ k C, RD potBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨410⟩ [potSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : potSelWord I = ⟨0x36569e77⟩ :=
    potSelWord_eq_of_beq I hsz 0x36 0x56 0x9e 0x77 ⟨0x36569e77⟩
      (by decide +native) (by simpa [potSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat potBytecode potRootSplitPc) (potSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; decide +native
  have h163 : UInt256.gt (armSelNat potBytecode potSplit163Pc) (potSelWord I) = ⟨0⟩ := by
    rw [hword]; decide +native
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG174FirstArmPc j))
        (potSelWord I) = ⟨0⟩ := by intro j hj; interval_cases j <;> rw [hword] <;> decide +native
  have htake :
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG174FirstArmPc 1))
        (potSelWord I) ≠ ⟨0⟩ := by rw [hword]; decide +native
  exact potReachG174Body 1 (by omega) ⟨410⟩ hcode hwv hsz hsize hroot h163 heq0 htake
    (by jump_dest) (by decide +native)

theorem potVatBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = potBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some vatTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (vatTransition.params.map Param.name)
        (transitionSignature vatTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD potBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨410⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ vatTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat (potAddressReturnWord ⟨5⟩ σ_solm I).toNat))])) := by
    simpa [vatTransition, potAddressReturnWord, potSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      potAddressGetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := vatRef) (er := ({ base := "vat", steps := [] } : EvaledStorageRef))
        (slot := ⟨5⟩)
        (by simp only [initState]; exact hwv) (by simp [vatRef])
        (by simp [evalStorageRef, evalStorageRefSteps, vatRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact potAddressGetterBodyCore (entry := ⟨410⟩) (returnPc := ⟨418⟩)
    (routine := ⟨1336⟩) (slot := ⟨5⟩)
    hcode hdispatch hdecode hreach hAccounts
    (by unfold solcGetterEntryWf; repeat' first | apply And.intro | decide +native)
    (by unfold solcAddressSlotGetterWf; repeat' first | apply And.intro | decide +native)
    (by jump_dest) (by jump_dest)
    (by unfold solcReturnAddressFromMemWf; repeat' first | apply And.intro | decide +native)
    (by rfl) hbody

theorem potVatBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = potBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (potSelBytes 14))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (potSelBytes 14) rfl hsel
  exact potVatBodyCore hcode hwv (potDispatchVat hsel) (potDecode_vat hsz)
    (potReachVatBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel) hAccounts

end Benchmarks.Dss.Pot
