import Benchmarks.Dss.Flipper.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Flipper

/-! ## `ttl()` getter -/

def ttlWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flipperUint48Offset0Word ⟨5⟩ σ I

theorem flipperDecode_ttl {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (ttlTransition.params.map Param.name)
      (transitionSignature ttlTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem flipperReachTtlBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flipperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flipperSelBytes 15)) :
    ∃ k C, RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨635⟩ [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : flipperSelWord I = ⟨0x4e8b1dd5⟩ :=
    flipperSelWord_eq_of_beq I hsz 0x4e 0x8b 0x1d 0xd5 ⟨0x4e8b1dd5⟩
      (by native_decide) (by simpa [flipperSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat flipperBytecode flipperRootSplitPc)
      (flipperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhigh : UInt256.gt (armSelNat flipperBytecode flipperHighSplitPc)
      (flipperSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperHighHighFirstArmPc j))
        (flipperSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperHighHighFirstArmPc 2))
        (flipperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact flipperReachHighHighBody 2 (by omega) ⟨635⟩ hcode hwv hsz hsize hroot hhigh
    heq0 htake (by jump_dest) (by native_decide)

theorem flipperTtlBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flipperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flipperSelBytes 15))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flipperSelBytes 15) rfl hsel
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ ttlTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (ttlWord σ_solm I).toNat))])) := by
    simpa [ttlTransition, ttlWord, flipperUint48Offset0Word, flipperSlotWord, initState,
      Solm.EVM.storageLoad, State.lookupAccount] using
      flipperUint48Offset0GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := ttlRef) (er := ({ base := "ttl", steps := [] } : EvaledStorageRef))
        (slot := ⟨5⟩)
        (by simp only [initState]; exact hwv) (by simp [ttlRef])
        (by simp [evalStorageRef, evalStorageRefSteps, ttlRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact flipperUint48Offset0GetterBodyCore (entry := ⟨635⟩) (routine := ⟨3921⟩)
    (slot := ⟨5⟩)
    hcode (flipperDispatchTtl hsel) (flipperDecode_ttl hsz)
    (flipperReachTtlBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel) hAccounts
    (by
      unfold solcGetterEntryWf
      repeat' first | apply And.intro | native_decide)
    (by
      unfold solcUint48Offset0SlotGetterWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest)
    (by jump_dest)
    (by rfl) (by simpa [ttlWord] using hbody)

end Benchmarks.Dss.Flipper
