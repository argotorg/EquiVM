import Benchmarks.OpenZeppelinBench.TimelockController.Return
import Benchmarks.OpenZeppelinBench.TimelockController.SolmDispatch
import Benchmarks.OpenZeppelinBench.TimelockController.Dispatch
import Benchmarks.OpenZeppelinBench.TimelockController.Routines

/-!
# OpenZeppelin TimelockController `DEFAULT_ADMIN_ROLE()` refinement

`DEFAULT_ADMIN_ROLE` is a public non-payable `bytes32` constant getter (selector index 2, dispatch
group G147 arm 1, body pc 1132).  It returns `bytes32(0)`, which the optimized runtime pushes with
`PUSH0` (not `PUSH32`).  Copied from the `PROPOSER_ROLE` template.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000
-- arm index 1 ⇒ `interval_cases j` yields a single goal, so the `<;>` combinator (kept for
-- template parity) is flagged as an unnecessary seq-focus; the warning is purely cosmetic.
set_option linter.unnecessarySeqFocus false

namespace OpenZeppelinBench.TimelockController

/-- `DEFAULT_ADMIN_ROLE` is `bytes32(0)` (the `PUSH0` constant at pc 1145). -/
def tlcDefaultAdminRoleWord : UInt256 := ⟨0⟩

theorem tlcDecodeDefaultAdminRole {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (defaultAdminRoleTransition.params.map Param.name)
      (transitionSignature defaultAdminRoleTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some (∅ : Store)
  exact decodeCalldataWithMode_empty_ok hsz

/-- Reach the `DEFAULT_ADMIN_ROLE` body pc 1132 (G147 arm 1). -/
theorem tlcReachDefaultAdminRole {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 2)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1132⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : tlcSelWord I = ⟨0xa217fddf⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xa2 0x17 0xfd 0xdf ⟨0xa217fddf⟩ (by native_decide)
      (by simpa [tlcSelBytes] using hsel)
  exact tlcReachG147Body 1 (by omega) ⟨1132⟩ hcode hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
    (by intro j hj; interval_cases j <;> (rw [hsw]; native_decide))
    (by rw [hsw]; native_decide) (by jump_dest) (by native_decide)

/-- EVM: with zero callvalue, `DEFAULT_ADMIN_ROLE()` returns the 32-byte zero constant. -/
theorem tlcDefaultAdminRoleX_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tlcSelBytes 2)) :
    RDret timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray tlcDefaultAdminRoleWord) := by
  obtain ⟨_, _, h1132⟩ := tlcReachDefaultAdminRole (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize hsel
  obtain ⟨_, _, h1145⟩ := tlcGuardPeelOk (gt := ⟨1143⟩) h1132 hwv (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by jump_dest)
    (by native_decide) (by native_decide)
  have h581 := h1145.push2 ⟨581⟩ (by native_decide) (by simp)
    |>.push0 (by native_decide) (by simp)
    |>.dup2 (by native_decide) (by simp)
    |>.jump (by native_decide) (by jump_dest) (by simp)
  exact tlcReturnWord h581 (by simp)

/-- The Solm `DEFAULT_ADMIN_ROLE()` body returns the constant `bytes32(0)`. -/
theorem tlcDefaultAdminRoleBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm locals defaultAdminRoleTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some [(.fixedBytes bytes32Width (EVM.Word.toBytesBE tlcDefaultAdminRoleWord))])) := by
  have hbody : defaultAdminRoleTransition.body =
      [ Stmt.require (.binary .eq (.env .callvalue) (.intLit 0)),
        Stmt.return [Expr.fixedBytesLit bytes32Width (EVM.Word.toBytesBE tlcDefaultAdminRoleWord)] ] := by
    native_decide
  rw [hbody]
  exact nonpayableFixedBytesLiteralBodyReturns (cfg := config) (contract := contract)
    evm locals bytes32Width (EVM.Word.toBytesBE tlcDefaultAdminRoleWord) h

/-- Refinement of `DefaultAdminRole` (selector index 2). -/
theorem tlcDefaultAdminRoleBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hsel : selIs I (tlcSelBytes 2))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (tlcSelBytes 2) (by native_decide) hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · exact tlcReEquivExecTransport hcode
      (tlcDefaultAdminRoleX_ok (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)
      (tlcSelectorDispatchDefaultAdminRole hsel) (tlcDecodeDefaultAdminRole hsz)
      (tlcDefaultAdminRoleBodyReturns (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv))
      rfl hAccounts
      (returnEquiv_of_encode (bytes32ReturnEncoding tlcDefaultAdminRoleWord))
  · obtain ⟨_, _, h1132⟩ := tlcReachDefaultAdminRole (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
    have hrev := tlcGuardPeelRev (gt := ⟨1143⟩) h1132 hwv (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
    exact tlcNonpayableRevert hcode hrev (tlcSelectorDispatchDefaultAdminRole hsel)
      (fun callargs _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end OpenZeppelinBench.TimelockController
