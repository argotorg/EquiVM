import Benchmarks.Dss.Pot.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Pot

/-! ## `Pie()` public getter (total normalised savings dai, slot 2). -/

def PieTotalWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 := potSlotWord ⟨2⟩ σ I

theorem potDecode_PieTotal {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (PieTransition.params.map Param.name)
      (transitionSignature PieTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem potReachPieTotalBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = potBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (potSelBytes 0)) :
    ∃ k C, RD potBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨402⟩ [potSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : potSelWord I = ⟨0x2c69ed58⟩ :=
    potSelWord_eq_of_beq I hsz 0x2c 0x69 0xed 0x58 ⟨0x2c69ed58⟩
      (by native_decide) (by simpa [potSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat potBytecode potRootSplitPc) (potSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have h163 : UInt256.gt (armSelNat potBytecode potSplit163Pc) (potSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG174FirstArmPc j))
        (potSelWord I) = ⟨0⟩ := by intro j hj; omega
  have htake :
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG174FirstArmPc 0))
        (potSelWord I) ≠ ⟨0⟩ := by rw [hword]; native_decide
  exact potReachG174Body 0 (by omega) ⟨402⟩ hcode hwv hsz hsize hroot h163 heq0 htake
    (by jump_dest) (by native_decide)

theorem potPieTotalBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = potBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some PieTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (PieTransition.params.map Param.name)
        (transitionSignature PieTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD potBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨402⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ PieTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (PieTotalWord σ_solm I).toNat))])) := by
    simpa [PieTransition, PieTotalWord, potSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      potUint256GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := PieRef) (er := ({ base := "Pie", steps := [] } : EvaledStorageRef))
        (slot := ⟨2⟩)
        (by simp only [initState]; exact hwv) (by simp [PieRef])
        (by simp [evalStorageRef, evalStorageRefSteps, PieRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact potUint256GetterBodyCore (entry := ⟨402⟩) (returnPc := ⟨341⟩)
    (routine := ⟨1330⟩) (slot := ⟨2⟩)
    hcode hdispatch hdecode hreach hAccounts
    (by unfold solcGetterEntryWf; repeat' first | apply And.intro | native_decide)
    (by unfold solcWordSlotGetterWf; repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by jump_dest)
    (by unfold solcReturnWordFromMemWf; repeat' first | apply And.intro | native_decide)
    (by rfl) (by simpa [PieTotalWord] using hbody)

theorem potPieTotalBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = potBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (potSelBytes 0))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (potSelBytes 0) rfl hsel
  exact potPieTotalBodyCore hcode hwv (potDispatchPie hsel) (potDecode_PieTotal hsz)
    (potReachPieTotalBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel) hAccounts

end Benchmarks.Dss.Pot
