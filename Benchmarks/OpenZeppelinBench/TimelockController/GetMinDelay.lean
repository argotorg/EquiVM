import Benchmarks.OpenZeppelinBench.TimelockController.Return
import Benchmarks.OpenZeppelinBench.TimelockController.SolmDispatch

/-!
# OpenZeppelin TimelockController `getMinDelay()` refinement

`getMinDelay` is a public non-payable `uint256` getter reading storage slot 2 (`_minDelay`).
Selector index 6, dispatch group G51 arm 3, body pc 1443.  Template for fixed-slot word getters.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace OpenZeppelinBench.TimelockController

/-- The stored `_minDelay` value (storage slot 2). -/
def tlcMinDelayWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 := solcSlotWord σ I ⟨2⟩

theorem tlcDecodeGetMinDelay {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (getMinDelayTransition.params.map Param.name)
      (transitionSignature getMinDelayTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some (∅ : Store)
  exact decodeCalldataWithMode_empty_ok hsz

/-- Reach the `getMinDelay` body pc 1443 (G51 arm 3). -/
theorem tlcReachGetMinDelay {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 6)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1443⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : tlcSelWord I = ⟨0xf27a0c92⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xf2 0x7a 0x0c 0x92 ⟨0xf27a0c92⟩ (by native_decide)
      (by simpa [tlcSelBytes] using hsel)
  exact tlcReachG51Body 3 (by omega) ⟨1443⟩ hcode hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
    (by intro j hj; interval_cases j <;> (rw [hsw]; native_decide))
    (by rw [hsw]; native_decide) (by jump_dest) (by native_decide)

/-- EVM: with zero callvalue, `getMinDelay()` returns storage slot 2. -/
theorem tlcGetMinDelayX_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tlcSelBytes 6)) :
    RDret timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (tlcMinDelayWord σ I)) := by
  obtain ⟨_, _, h1443⟩ := tlcReachGetMinDelay (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize hsel
  obtain ⟨_, _, h1456⟩ := tlcGuardPeelOk (gt := ⟨1454⟩) h1443 hwv (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by jump_dest)
    (by native_decide) (by native_decide)
  obtain ⟨_, _, h1459⟩ := (h1456.push1 ⟨2⟩ (by native_decide) (by simp)).sload (by native_decide) (by simp)
  have h581 := h1459.push2 ⟨581⟩ (by native_decide) (by simp)
    |>.jump (by native_decide) (by jump_dest) (by simp)
  exact tlcReturnWord h581 (by simp)

/-- The Solm `getMinDelay()` body returns the slot-2 word. -/
theorem tlcGetMinDelayBodyReturns {cA gh bl σ σ₀ A I} {g : Sat256}
    (h : I.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I) ∅
      getMinDelayTransition.body
      (.returned { contract := contract, locals := ∅ } (initState cA gh bl σ σ₀ g A I)
        (some [(.int (Int.ofNat (tlcMinDelayWord σ I).toNat))])) := by
  refine nonpayableReturnExprBodyReturns (by simp only [initState]; exact h) ?_
  rw [evalExpr_storage_scalar (cfg := config) (solm := { contract := contract, locals := ∅ })
    (slot := minDelayRef) (er := ({ base := "_minDelay", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int) (loc := uint256Loc ⟨2⟩)
    (hbase := by simp [minDelayRef])
    (her := by simp [evalStorageRef, minDelayRef, EvalResult.bind, EvalResult.ofOption, bind, pure])
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St, uint256Int])
    (hloc := by rfl)]
  exact congrArg EvalResult.ok (storageLocLoad_uint256 (initState cA gh bl σ σ₀ g A I) ⟨2⟩)

/-- Refinement of `getMinDelay` (selector index 6). -/
theorem tlcGetMinDelayBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hsel : selIs I (tlcSelBytes 6))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (tlcSelBytes 6) (by native_decide) hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hword : tlcMinDelayWord σ_evm I = tlcMinDelayWord σ_solm I := by
      simp only [tlcMinDelayWord]; exact accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
    exact tlcReEquivExecTransport hcode
      (tlcGetMinDelayX_ok (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)
      (tlcSelectorDispatchGetMinDelay hsel) (tlcDecodeGetMinDelay hsz)
      (tlcGetMinDelayBodyReturns (g := Sat256.ofUInt256 g) hwv) (by rw [← hword]) hAccounts
      (returnEquiv_of_encode (by simpa [uint256] using uint256ReturnEncoding (tlcMinDelayWord σ_evm I)))
  · obtain ⟨_, _, h1443⟩ := tlcReachGetMinDelay (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
    have hrev := tlcGuardPeelRev (gt := ⟨1454⟩) h1443 hwv (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
    exact tlcNonpayableRevert hcode hrev (tlcSelectorDispatchGetMinDelay hsel)
      (fun callargs _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end OpenZeppelinBench.TimelockController
