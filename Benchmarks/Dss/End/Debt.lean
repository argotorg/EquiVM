import Benchmarks.Dss.End.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.End

/-! ## `debt()` getter -/

def debtWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWordAt ⟨11⟩ σ I

theorem endDecode_debt {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (debtTransition.params.map Param.name)
      (transitionSignature debtTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem endDebtBodyCore
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some debtTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (debtTransition.params.map Param.name)
        (transitionSignature debtTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) endDebtEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ debtTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (debtWord σ I).toNat))])) := by
    simpa [debtTransition, debtWord, solcSlotWordAt, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      endUint256GetterBodyReturns
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := debtRef) (er := ({ base := "debt", steps := [] } : EvaledStorageRef))
        (slot := ⟨11⟩)
        (by simp only [initState]; exact hwv) (by simp [debtRef])
        (by simp [evalStorageRef, evalStorageRefSteps, debtRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact endUint256GetterBodyCore (entry := endDebtEntryPc)
    (returnPc := endWordReturnPc) (routine := endDebtRoutinePc) (slot := ⟨11⟩)
    hcode hdispatch hdecode hreach
    (by
      unfold solcGetterEntryWf
      repeat' first | apply And.intro | native_decide)
    (by
      unfold solcWordSlotGetterWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest)
    (by jump_dest)
    (by
      unfold solcReturnWordFromMemWf
      repeat' first | apply And.intro | native_decide)
    (by rfl) (by simpa [debtWord] using hbody)

theorem endDebtBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selectorOf debtTransition)) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsel' : selIs I debtSelector := by
    simpa [endDebtSelectorBytes] using hsel
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I debtSelector (by rfl) hsel'
  exact endDebtBodyCore hcode hwv (endDispatchDebt hsel) (endDecode_debt hsz)
    (endReachDebtBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel')

end Benchmarks.Dss.End
