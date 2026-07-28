import Benchmarks.OpenZeppelinBench.TimelockController.Return
import Benchmarks.OpenZeppelinBench.TimelockController.SolmDispatch
import Benchmarks.OpenZeppelinBench.TimelockController.Dispatch
import Benchmarks.OpenZeppelinBench.TimelockController.Routines

/-!
# OpenZeppelin TimelockController `EXECUTOR_ROLE()` refinement

`EXECUTOR_ROLE` is a public non-payable `bytes32` constant getter (selector index 5, dispatch group
G397 arm 2, body pc 530).  It returns `keccak256("EXECUTOR_ROLE")`.  Copied from the `PROPOSER_ROLE`
template.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace OpenZeppelinBench.TimelockController

/-- `keccak256("EXECUTOR_ROLE")` as an EVM word (the `PUSH32` constant at pc 543). -/
def tlcExecutorRoleWord : UInt256 :=
  ⟨0xd8aa0f3194971a2a116679f7c2090f6939c8d4e01a2a8d7e41d55e5351469e63⟩

theorem tlcDecodeExecutorRole {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (executorRoleTransition.params.map Param.name)
      (transitionSignature executorRoleTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some (∅ : Store)
  exact decodeCalldataWithMode_empty_ok hsz

/-- Reach the `EXECUTOR_ROLE` body pc 530 (G397 arm 2). -/
theorem tlcReachExecutorRole {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 5)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨530⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : tlcSelWord I = ⟨0x07bd0265⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x07 0xbd 0x02 0x65 ⟨0x07bd0265⟩ (by native_decide)
      (by simpa [tlcSelBytes] using hsel)
  exact tlcReachG397Body 2 (by omega) ⟨530⟩ hcode hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
    (by intro j hj; interval_cases j <;> (rw [hsw]; native_decide))
    (by rw [hsw]; native_decide) (by jump_dest) (by native_decide)

/-- EVM: with zero callvalue, `EXECUTOR_ROLE()` returns the 32-byte role hash. -/
theorem tlcExecutorRoleX_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tlcSelBytes 5)) :
    RDret timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray tlcExecutorRoleWord) := by
  obtain ⟨_, _, h530⟩ := tlcReachExecutorRole (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize hsel
  obtain ⟨_, _, h543⟩ := tlcGuardPeelOk (gt := ⟨541⟩) h530 hwv (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by jump_dest)
    (by native_decide) (by native_decide)
  have h581 := h543.push2 ⟨581⟩ (by native_decide) (by simp)
    |>.pushConst tlcExecutorRoleWord (op := .PUSH32) (width := 32) (by decide)
        (by native_decide) (by simp)
    |>.dup2 (by native_decide) (by simp)
    |>.jump (by native_decide) (by jump_dest) (by simp)
  exact tlcReturnWord h581 (by simp)

/-- The Solm `EXECUTOR_ROLE()` body returns the constant `bytes32`. -/
theorem tlcExecutorRoleBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm locals executorRoleTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some [(.fixedBytes bytes32Width (EVM.Word.toBytesBE tlcExecutorRoleWord))])) := by
  have hbody : executorRoleTransition.body =
      [ Stmt.require (.binary .eq (.env .callvalue) (.intLit 0)),
        Stmt.return [Expr.fixedBytesLit bytes32Width (EVM.Word.toBytesBE tlcExecutorRoleWord)] ] := by
    native_decide
  rw [hbody]
  exact nonpayableFixedBytesLiteralBodyReturns (cfg := config) (contract := contract)
    evm locals bytes32Width (EVM.Word.toBytesBE tlcExecutorRoleWord) h

/-- Refinement of `ExecutorRole` (selector index 5). -/
theorem tlcExecutorRoleBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hsel : selIs I (tlcSelBytes 5))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (tlcSelBytes 5) (by native_decide) hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · exact tlcReEquivExecTransport hcode
      (tlcExecutorRoleX_ok (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)
      (tlcSelectorDispatchExecutorRole hsel) (tlcDecodeExecutorRole hsz)
      (tlcExecutorRoleBodyReturns (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv))
      rfl hAccounts
      (returnEquiv_of_encode (bytes32ReturnEncoding tlcExecutorRoleWord))
  · obtain ⟨_, _, h530⟩ := tlcReachExecutorRole (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
    have hrev := tlcGuardPeelRev (gt := ⟨541⟩) h530 hwv (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
    exact tlcNonpayableRevert hcode hrev (tlcSelectorDispatchExecutorRole hsel)
      (fun callargs _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end OpenZeppelinBench.TimelockController
