import Benchmarks.OpenZeppelinBench.TimelockController.Return
import Benchmarks.OpenZeppelinBench.TimelockController.SolmDispatch

/-!
# OpenZeppelin TimelockController `PROPOSER_ROLE()` refinement

`PROPOSER_ROLE` is a public non-payable `bytes32` constant getter (selector index 21, dispatch group
G194 arm 2, body pc 1050).  It returns `keccak256("PROPOSER_ROLE")`.  Template for the other three
role-constant getters.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace OpenZeppelinBench.TimelockController

/-- `keccak256("PROPOSER_ROLE")` as an EVM word (the `PUSH32` constant at pc 1066). -/
def tlcProposerRoleWord : UInt256 :=
  ⟨0xb09aa5aeb3702cfd50b6b62bc4532604938f21248a27a1d5ca736082b6819cc1⟩

theorem tlcDecodeProposerRole {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (proposerRoleTransition.params.map Param.name)
      (transitionSignature proposerRoleTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some (∅ : Store)
  exact decodeCalldataWithMode_empty_ok hsz

/-- Reach the `PROPOSER_ROLE` body pc 1050 (G194 arm 2). -/
theorem tlcReachProposerRole {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 21)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1050⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : tlcSelWord I = ⟨0x8f61f4f5⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x8f 0x61 0xf4 0xf5 ⟨0x8f61f4f5⟩ (by native_decide)
      (by simpa [tlcSelBytes] using hsel)
  exact tlcReachG194Body 2 (by omega) ⟨1050⟩ hcode hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
    (by intro j hj; interval_cases j <;> (rw [hsw]; native_decide))
    (by rw [hsw]; native_decide) (by jump_dest) (by native_decide)

/-- EVM: with zero callvalue, `PROPOSER_ROLE()` returns the 32-byte role hash. -/
theorem tlcProposerRoleX_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tlcSelBytes 21)) :
    RDret timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray tlcProposerRoleWord) := by
  obtain ⟨_, _, h1050⟩ := tlcReachProposerRole (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize hsel
  obtain ⟨_, _, h1063⟩ := tlcGuardPeelOk (gt := ⟨1061⟩) h1050 hwv (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by jump_dest)
    (by native_decide) (by native_decide)
  have h581 := h1063.push2 ⟨581⟩ (by native_decide) (by simp)
    |>.pushConst tlcProposerRoleWord (op := .PUSH32) (width := 32) (by decide)
        (by native_decide) (by simp)
    |>.dup2 (by native_decide) (by simp)
    |>.jump (by native_decide) (by jump_dest) (by simp)
  exact tlcReturnWord h581 (by simp)

/-- The Solm `PROPOSER_ROLE()` body returns the constant `bytes32`. -/
theorem tlcProposerRoleBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm locals proposerRoleTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some [(.fixedBytes bytes32Width (EVM.Word.toBytesBE tlcProposerRoleWord))])) := by
  have hbody : proposerRoleTransition.body =
      [ Stmt.require (.binary .eq (.env .callvalue) (.intLit 0)),
        Stmt.return [Expr.fixedBytesLit bytes32Width (EVM.Word.toBytesBE tlcProposerRoleWord)] ] := by
    native_decide
  rw [hbody]
  exact nonpayableFixedBytesLiteralBodyReturns (cfg := config) (contract := contract)
    evm locals bytes32Width (EVM.Word.toBytesBE tlcProposerRoleWord) h

/-- Refinement of `PROPOSER_ROLE` (selector index 21). -/
theorem tlcProposerRoleBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hsel : selIs I (tlcSelBytes 21))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (tlcSelBytes 21) (by native_decide) hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · exact tlcReEquivExecTransport hcode
      (tlcProposerRoleX_ok (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)
      (tlcSelectorDispatchProposerRole hsel) (tlcDecodeProposerRole hsz)
      (tlcProposerRoleBodyReturns (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv))
      rfl hAccounts
      (returnEquiv_of_encode (bytes32ReturnEncoding tlcProposerRoleWord))
  · obtain ⟨_, _, h1050⟩ := tlcReachProposerRole (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
    have hrev := tlcGuardPeelRev (gt := ⟨1061⟩) h1050 hwv (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
    exact tlcNonpayableRevert hcode hrev (tlcSelectorDispatchProposerRole hsel)
      (fun callargs _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end OpenZeppelinBench.TimelockController
