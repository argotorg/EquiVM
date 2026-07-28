import Benchmarks.Dss.Jug.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Jug

/-! ## `vow()` getter -/

def vowWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  jugAddressReturnWord ⟨3⟩ σ I

theorem jugDecode_vow {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (vowTransition.params.map Param.name)
      (transitionSignature vowTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem jugReachVowBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = jugBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (jugSelBytes 10)) :
    ∃ k C, RD jugBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨383⟩ [jugSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : jugSelWord I = ⟨0x626cb3c5⟩ :=
    jugSelWord_eq_of_beq I hsz 0x62 0x6c 0xb3 0xc5 ⟨0x626cb3c5⟩
      (by native_decide) (by simpa [jugSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat jugBytecode jugRootSplitPc) (jugSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat jugBytecode (nthArmPc jugBytecode jugHighFirstArmPc j))
        (jugSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq (armSelNat jugBytecode (nthArmPc jugBytecode jugHighFirstArmPc 0))
        (jugSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact jugReachHighBody 0 (by omega) ⟨383⟩ hcode hwv hsz hsize hroot heq0 htake
    (by jump_dest) (by native_decide)

theorem jugVowBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = jugBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some vowTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (vowTransition.params.map Param.name)
        (transitionSignature vowTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨383⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ vowTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat (vowWord σ_solm I).toNat))])) := by
    simpa [vowTransition, vowWord, jugAddressReturnWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      jugAddressGetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := vowRef) (er := ({ base := "vow", steps := [] } : EvaledStorageRef))
        (slot := ⟨3⟩)
        (by simp only [initState]; exact hwv) (by simp [vowRef])
        (by simp [evalStorageRef, evalStorageRefSteps, vowRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact jugAddressGetterBodyCore (entry := ⟨383⟩) (returnPc := ⟨271⟩)
    (routine := ⟨1705⟩) (slot := ⟨3⟩)
    hcode hdispatch hdecode hreach hAccounts
    (by
      unfold solcGetterEntryWf
      repeat' first | apply And.intro | native_decide)
    (by
      unfold solcAddressSlotGetterWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest)
    (by jump_dest)
    (by
      unfold solcReturnAddressFromMemWf
      repeat' first | apply And.intro | native_decide)
    (by rfl) (by simpa [vowWord] using hbody)

theorem jugVowBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = jugBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (jugSelBytes 10))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (jugSelBytes 10) rfl hsel
  exact jugVowBodyCore hcode hwv (jugDispatchVow hsel) (jugDecode_vow hsz)
    (jugReachVowBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel) hAccounts

end Benchmarks.Dss.Jug
