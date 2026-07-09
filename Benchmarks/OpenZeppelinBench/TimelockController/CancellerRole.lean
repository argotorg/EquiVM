import Benchmarks.OpenZeppelinBench.TimelockController.Return
import Benchmarks.OpenZeppelinBench.TimelockController.SolmDispatch
import Benchmarks.OpenZeppelinBench.TimelockController.Dispatch
import Benchmarks.OpenZeppelinBench.TimelockController.Routines

/-!
# OpenZeppelin TimelockController `CANCELLER_ROLE()` refinement

`CANCELLER_ROLE` is a public non-payable `bytes32` constant getter (selector index 0, dispatch group
G147 arm 2, body pc 1151).  It returns `keccak256("CANCELLER_ROLE")`.  Copied from the
`PROPOSER_ROLE` template.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace OpenZeppelinBench.TimelockController

/-- `keccak256("CANCELLER_ROLE")` as an EVM word (the `PUSH32` constant at pc 1164). -/
def tlcCancellerRoleWord : UInt256 :=
  ⟨0xfd643c72710c63c0180259aba6b2d05451e3591a24e58b62239378085726f783⟩

theorem tlcDecodeCancellerRole {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (cancellerRoleTransition.params.map Param.name)
      (transitionSignature cancellerRoleTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some (∅ : Store)
  exact decodeCalldataWithMode_empty_ok hsz

/-- Reach the `CANCELLER_ROLE` body pc 1151 (G147 arm 2). -/
theorem tlcReachCancellerRole {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 0)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1151⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : tlcSelWord I = ⟨0xb08e51c0⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xb0 0x8e 0x51 0xc0 ⟨0xb08e51c0⟩ (by native_decide)
      (by simpa [tlcSelBytes] using hsel)
  exact tlcReachG147Body 2 (by omega) ⟨1151⟩ hcode hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
    (by intro j hj; interval_cases j <;> (rw [hsw]; native_decide))
    (by rw [hsw]; native_decide) (by jump_dest) (by native_decide)

/-- EVM: with zero callvalue, `CANCELLER_ROLE()` returns the 32-byte role hash. -/
theorem tlcCancellerRoleX_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tlcSelBytes 0)) :
    RDret timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray tlcCancellerRoleWord) := by
  obtain ⟨_, _, h1151⟩ := tlcReachCancellerRole (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize hsel
  obtain ⟨_, _, h1164⟩ := tlcGuardPeelOk (gt := ⟨1162⟩) h1151 hwv (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by jump_dest)
    (by native_decide) (by native_decide)
  have h581 := h1164.push2 ⟨581⟩ (by native_decide) (by simp)
    |>.pushConst tlcCancellerRoleWord (op := .PUSH32) (width := 32) (by decide)
        (by native_decide) (by simp)
    |>.dup2 (by native_decide) (by simp)
    |>.jump (by native_decide) (by jump_dest) (by simp)
  exact tlcReturnWord h581 (by simp)

/-- The Solm `CANCELLER_ROLE()` body returns the constant `bytes32`. -/
theorem tlcCancellerRoleBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm locals cancellerRoleTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some [(.fixedBytes bytes32Width (EVM.Word.toBytesBE tlcCancellerRoleWord))])) := by
  have hbody : cancellerRoleTransition.body =
      [ Stmt.require (.binary .eq (.env .callvalue) (.intLit 0)),
        Stmt.return [Expr.fixedBytesLit bytes32Width (EVM.Word.toBytesBE tlcCancellerRoleWord)] ] := by
    native_decide
  rw [hbody]
  exact nonpayableFixedBytesLiteralBodyReturns (cfg := config) (contract := contract)
    evm locals bytes32Width (EVM.Word.toBytesBE tlcCancellerRoleWord) h

/-- Refinement of `CancellerRole` (selector index 0). -/
theorem tlcCancellerRoleBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hsel : selIs I (tlcSelBytes 0))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (tlcSelBytes 0) (by native_decide) hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · exact tlcReEquivExecTransport hcode
      (tlcCancellerRoleX_ok (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)
      (tlcSelectorDispatchCancellerRole hsel) (tlcDecodeCancellerRole hsz)
      (tlcCancellerRoleBodyReturns (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv))
      rfl hAccounts
      (returnEquiv_of_encode (bytes32ReturnEncoding tlcCancellerRoleWord))
  · obtain ⟨_, _, h1151⟩ := tlcReachCancellerRole (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
    have hrev := tlcGuardPeelRev (gt := ⟨1162⟩) h1151 hwv (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
    exact tlcNonpayableRevert hcode hrev (tlcSelectorDispatchCancellerRole hsel)
      (fun callargs _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end OpenZeppelinBench.TimelockController
