import Benchmarks.Dss.Flapper.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flapper

/-! ## `ttl()` getter -/

def ttlWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  uint48Offset0Word ⟨5⟩ σ I

theorem flapperDecode_ttl {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (ttlTransition.params.map Param.name)
      (transitionSignature ttlTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem flapperReachTtlBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flapperSelBytes 16)) :
    ∃ k C, RD flapperBytecode I g (initState σ σ₀ g A I)
        ⟨565⟩ [flapperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        σ k C := by
  have hword : flapperSelWord I = ⟨0x4e8b1dd5⟩ := by
    simpa [flapperSelWord, solcSelectorWord] using
      solcSelectorWord_eq_of_beq I hsz 0x4e 0x8b 0x1d 0xd5 ⟨0x4e8b1dd5⟩
        (by native_decide) (by simpa [flapperSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat flapperBytecode flapperRootSplitPc)
      (flapperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlow : UInt256.gt (armSelNat flapperBytecode flapperLowSplitPc)
      (flapperSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  obtain ⟨_, _, hfirst⟩ :=
    flapperReachLowHighFirstArm (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow
  have heq0 : ∀ j, j < 1 →
      UInt256.eq
        (armSelNat flapperBytecode (nthArmPc flapperBytecode flapperLowHighFirstArmPc j))
        (flapperSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    rw [hword]
    native_decide
  have htake :
      UInt256.eq
        (armSelNat flapperBytecode (nthArmPc flapperBytecode flapperLowHighFirstArmPc 1))
        (flapperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo ⟨565⟩ 1 hfirst
    (fun j hj => flapperLowHighArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem flapperTtlBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = flapperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flapperSelBytes 16)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flapperSelBytes 16) rfl hsel
  have hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ ttlTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (ttlWord σ I).toNat))])) := by
    simpa [ttlTransition, ttlWord, uint48Offset0Word, initState,
      Solm.EVM.storageLoad, State.lookupAccount] using
      flapperUint48GetterBodyReturns_offset0
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := ttlRef) (er := ({ base := "ttl", steps := [] } : EvaledStorageRef))
        (slot := ⟨5⟩)
        (by simp only [initState]; exact hwv) (by simp [ttlRef])
        (by simp [evalStorageRef, evalStorageRefSteps, ttlRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact flapperUint48Offset0GetterBodyCore (entry := ⟨565⟩) (returnPc := ⟨573⟩)
    (routine := ⟨2824⟩) (slot := ⟨5⟩)
    hcode (flapperDispatchTtl hsel) (flapperDecode_ttl hsz)
    (flapperReachTtlBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)
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

end Benchmarks.Dss.Flapper
