import Benchmarks.Dss.Flopper.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flopper

/-! ## `ttl()` getter -/

def ttlWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  uint48Offset0Word ⟨6⟩ σ I

theorem flopperDecode_ttl {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (ttlTransition.params.map Param.name)
      (transitionSignature ttlTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem flopperReachTtlBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flopperSelBytes 15)) :
    ∃ k C, RD flopperBytecode I g (initState σ σ₀ g A I)
        ⟨498⟩ [flopperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        σ k C := by
  have hword : flopperSelWord I = ⟨0x4e8b1dd5⟩ := by
    simpa [flopperSelWord, solcSelectorWord] using
      solcSelectorWord_eq_of_beq I hsz 0x4e 0x8b 0x1d 0xd5 ⟨0x4e8b1dd5⟩
        (by native_decide) (by simpa [flopperSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat flopperBytecode flopperRootSplitPc)
      (flopperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlow : UInt256.gt (armSelNat flopperBytecode flopperLowSplitPc)
      (flopperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  obtain ⟨_, _, hfirst⟩ :=
    flopperReachLowLowFirstArm (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow
  have heq0 : ∀ j, j < 4 →
      UInt256.eq
        (armSelNat flopperBytecode (nthArmPc flopperBytecode flopperLowLowFirstArmPc j))
        (flopperSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq
        (armSelNat flopperBytecode (nthArmPc flopperBytecode flopperLowLowFirstArmPc 4))
        (flopperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo ⟨498⟩ 4 hfirst
    (fun j hj => flopperLowLowArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem flopperTtlBodyCore
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some ttlTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (ttlTransition.params.map Param.name)
        (transitionSignature ttlTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨498⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ ttlTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (ttlWord σ I).toNat))])) := by
    simpa [ttlTransition, ttlWord, uint48Offset0Word, initState,
      Solm.EVM.storageLoad, State.lookupAccount] using
      flopperUint48GetterBodyReturns_offset0
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := ttlRef) (er := ({ base := "ttl", steps := [] } : EvaledStorageRef))
        (slot := ⟨6⟩)
        (by simp only [initState]; exact hwv) (by simp [ttlRef])
        (by simp [evalStorageRef, evalStorageRefSteps, ttlRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact flopperUint48Offset0GetterBodyCore (entry := ⟨498⟩) (returnPc := ⟨506⟩)
    (routine := ⟨1620⟩) (slot := ⟨6⟩)
    hcode hdispatch hdecode hreach
    (by
      unfold solcGetterEntryWf
      repeat' first | apply And.intro | native_decide)
    (by
      unfold solcUint48Offset0SlotGetterWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest)
    (by jump_dest)
    (by
      unfold solcReturnUint48FromMemWf
      repeat' first | apply And.intro | native_decide)
    (by rfl) (by simpa [ttlWord] using hbody)

theorem flopperTtlBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = flopperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flopperSelBytes 15)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flopperSelBytes 15) rfl hsel
  exact flopperTtlBodyCore hcode hwv (flopperDispatchTtl hsel) (flopperDecode_ttl hsz)
    (flopperReachTtlBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)

end Benchmarks.Dss.Flopper
