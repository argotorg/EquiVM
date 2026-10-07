import Benchmarks.Dss.Vow.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vow

/-! ## `dump()` getter -/

def dumpWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWordAt ⟨8⟩ σ I

theorem vowDispatch_dump {I : ExecutionEnv} (hsel : selIs I ⟨#[0xe4, 0x33, 0x05, 0x45]⟩) :
    dispatchMsg contract I.calldata = some dumpTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [AshTransition, SinTransition, bumpTransition, cageTransition, denyTransition])
    (post := [fessTransition, fileUintTransition, fileAddressTransition, flapTransition,
      flapperTransition, flogTransition, flopTransition, flopperTransition, healTransition,
      humpTransition, kissTransition, liveTransition, relyTransition, sinTransition,
      sumpTransition, vatTransition, waitTransition, wardsTransition])
    (ti := dumpTransition)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = (⟨#[0xe4, 0x33, 0x05, 0x45]⟩ : ByteArray) :=
      (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, AshSelectorBytes, SinSelectorBytes, bumpSelectorBytes,
        cageSelectorBytes, denySelectorBytes, hcd]
      native_decide
  · rw [selectorOf, dumpSelectorBytes]
    exact hsel

theorem vowDecode_dump {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (dumpTransition.params.map Param.name)
      (transitionSignature dumpTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem vowReachDumpBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xe4, 0x33, 0x05, 0x45]⟩) :
    ∃ k C, RD vowBytecode I g (initState σ σ₀ g A I)
        ⟨810⟩ [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        σ k C := by
  have hword : vowSelWord I = ⟨3828548933⟩ :=
    vowSelWord_eq_of_beq I hsz 0xe4 0x33 0x05 0x45 ⟨3828548933⟩
      (by native_decide) hsel
  have hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhigh : UInt256.gt (armSelNat vowBytecode vowHighSplitPc) (vowSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowHighHighFirstArmPc j))
        (vowSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowHighHighFirstArmPc 4))
        (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vowReachHighHighBody 4 (by omega) ⟨810⟩ hcode hwv hsz hsize hroot hhigh heq0 htake
    (by jump_dest) (by native_decide)

theorem vowDumpBodyCore
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some dumpTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dumpTransition.params.map Param.name)
        (transitionSignature dumpTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨810⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ dumpTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (dumpWord σ I).toNat))])) := by
    simpa [dumpTransition, dumpWord, solcSlotWordAt, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      vowUint256GetterBodyReturns
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := dumpRef) (er := ({ base := "dump", steps := [] } : EvaledStorageRef))
        (slot := ⟨8⟩)
        (by simp only [initState]; exact hwv) (by simp [dumpRef])
        (by simp [evalStorageRef, evalStorageRefSteps, dumpRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact vowUint256GetterBodyCore (entry := ⟨810⟩) (routine := ⟨4634⟩) (slot := ⟨8⟩)
    hcode hdispatch hdecode hreach
    (by
      unfold solcGetterEntryWf
      repeat' first | apply And.intro | native_decide)
    (by
      unfold solcWordSlotGetterWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by rfl)
    (by simpa [dumpWord] using hbody)

theorem vowDumpBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe4, 0x33, 0x05, 0x45]⟩) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0xe4, 0x33, 0x05, 0x45]⟩ rfl hsel
  exact vowDumpBodyCore hcode hwv (vowDispatch_dump hsel) (vowDecode_dump hsz)
    (vowReachDumpBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)

end Benchmarks.Dss.Vow
