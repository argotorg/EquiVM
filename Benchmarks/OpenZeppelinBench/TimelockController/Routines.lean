import Benchmarks.OpenZeppelinBench.TimelockController.Common

/-!
# OpenZeppelin TimelockController shared routine lemmas

Contract-wide `RD` combinators and refinement bridges not covered directly by the library because
TimelockController (solc 0.8.35, payable `receive`) emits a **per-function** non-payable callvalue
guard rather than a shared-prologue one, and has `contract.receive = some …` (so the library
`reEquiv*` bridges, which require `receive = none`, do not apply on the selector-match path).

The guard-peel lemmas are the per-function analogues of the library's `solcGuardCallvalueZero` /
`solcGuardCallvalueNonzeroRevert`.  The `tlcReEquiv*` bridges consume a direct
`selectorDispatchMsg contract I.calldata = some t` fact, mirroring
`RDret.reEquivExecutionGenAccountMapEquiv` / `RDrev.reEquivExecutionRevert`.

Adapted from the fully-proved sibling `Benchmarks/WETH9/Routines.lean` (same payable-dispatch shape).
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace OpenZeppelinBench.TimelockController

/-- Non-payable callvalue guard, `callvalue == 0` branch: peel
    `JUMPDEST; CALLVALUE; DUP1; ISZERO; PUSH2 gt; JUMPI; …; JUMPDEST gt; POP`, reaching `gt + 2`
    with the selector word still on the stack.
    LIBRARY CANDIDATE: `Reasoning.Solc` — per-function analogue of `solcGuardCallvalueZero`. -/
theorem tlcGuardPeelOk {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {entry gt sel : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 entry [sel] mem aw rdata acc k C)
    (hcv : ee.weiValue = ⟨0⟩)
    (hd0 : decode code entry = some (.JUMPDEST, .none))
    (hd1 : decode code (entry + ⟨1⟩) = some (.CALLVALUE, .none))
    (hd2 : decode code (entry + ⟨1⟩ + ⟨1⟩) = some (.DUP1, .none))
    (hd3 : decode code (entry + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.ISZERO, .none))
    (hd4 : decode code (entry + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.Push .PUSH2, some (gt, 2)))
    (hd7 : decode code (entry + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3) = some (.JUMPI, .none))
    (hgtjd : (D_J code 0).contains gt = true)
    (hdgt : decode code gt = some (.JUMPDEST, .none))
    (hdpop : decode code (gt + ⟨1⟩) = some (.POP, .none)) :
    ∃ k' C', RD code ee g s0 (gt + ⟨1⟩ + ⟨1⟩) [sel] mem aw rdata acc k' C' := by
  have hcond : UInt256.isZero ee.weiValue ≠ ⟨0⟩ := by rw [hcv]; decide
  exact ⟨_, _, h.jumpdest hd0 (by simp)
    |>.callvalue hd1 (by simp)
    |>.dup1 hd2 (by simp)
    |>.iszero hd3 (by simp)
    |>.pushConst gt (op := .PUSH2) (width := 2) (by simp) hd4 (by simp)
    |>.jumpiT hd7 hcond hgtjd (by simp)
    |>.jumpdest hdgt (by simp)
    |>.pop hdpop (by simp)⟩

/-- Non-payable callvalue guard, `callvalue != 0` branch: the `JUMPI` is not taken and control falls
    into the `PUSH0; PUSH0; REVERT` stub (solc ≥ 0.8.20 Shanghai emits `PUSH0 PUSH0` not `PUSH1 0 DUP1`).
    LIBRARY CANDIDATE: `Reasoning.Solc` — per-function analogue of `solcGuardCallvalueNonzeroRevert`. -/
theorem tlcGuardPeelRev {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {entry gt sel : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 entry [sel] mem aw rdata acc k C)
    (hcv : ee.weiValue ≠ ⟨0⟩)
    (hd0 : decode code entry = some (.JUMPDEST, .none))
    (hd1 : decode code (entry + ⟨1⟩) = some (.CALLVALUE, .none))
    (hd2 : decode code (entry + ⟨1⟩ + ⟨1⟩) = some (.DUP1, .none))
    (hd3 : decode code (entry + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.ISZERO, .none))
    (hd4 : decode code (entry + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.Push .PUSH2, some (gt, 2)))
    (hd7 : decode code (entry + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3) = some (.JUMPI, .none))
    (hd8 : decode code (entry + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩)
        = some (.PUSH0, .none))
    (hd9 : decode code (entry + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ + ⟨1⟩)
        = some (.PUSH0, .none))
    (hd10 : decode code (entry + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩)
        = some (.REVERT, .none)) :
    RDrev code g s0 := by
  have hcond : UInt256.isZero ee.weiValue = ⟨0⟩ := isZero_eq_zero_of_ne hcv
  exact (h.jumpdest hd0 (by simp)
    |>.callvalue hd1 (by simp)
    |>.dup1 hd2 (by simp)
    |>.iszero hd3 (by simp)
    |>.pushConst gt (op := .PUSH2) (width := 2) (by simp) hd4 (by simp)
    |>.jumpiNT hd7 hcond (by simp)).revertStub hd8 hd9 hd10 (by simp)

/-! ## Connect lemmas taking a direct selector dispatch

TimelockController has `contract.receive = some receiveTransition`, so the library `reEquiv*`
bridges — which require `contract.receive = none` to convert a `dispatchMsg` fact into a
`selectorDispatchMsg` one — do not apply on the selector-match path.  When a named selector matches,
`selectorDispatchMsg contract I.calldata = some t` holds directly; these lemmas consume that,
mirroring `RDret.reEquivExecutionGenAccountMapEquiv` / `RDrev.reEquivExecutionRevert`. -/

/-- `RDret ⇒ execution` for a directly-matched selector (accounts up to `accountMapEquiv`). -/
theorem tlcReEquivExecGen {cfg : Config} {t : TransitionDecl}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {o : ByteArray} {callargs cs retVal}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {evm'' : EVM.State}
    (hcode : I.code = timelockControllerBenchBytecode)
    (h : RDret timelockControllerBenchBytecode g (initState cA gh bl σ_evm σ₀ g A I) acc o)
    (hsel : selectorDispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
              (transitionSignature t).paramTypes I.calldata = some callargs)
    (hbody : ExecTransitionBody cfg contract
              (initState cA gh bl σ_solm σ₀ g A I) callargs t.body
              (.returned cs evm'' retVal))
    (hCreated : acc.1 = evm''.createdAccounts)
    (hAccounts : accountMapEquiv acc.2 evm''.accountMap)
    (henc : returnEquiv o retVal t.returnType) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀ g.toUInt256 A I := by
  rcases h with hoog | ⟨s, hX, hsacc⟩
  · exact reEquiv_outOfGas (Xi_error_of_X (g := g.toUInt256) (by
      rw [← hcode] at hoog
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hoog))
  · have hxi := Xi_success_of_X (g := g.toUInt256) (by
      rw [← hcode] at hX
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hX)
    have hbody' :
        ExecTransitionBody cfg contract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g.toUInt256) A I)
          callargs t.body (.returned cs evm'' retVal) := by
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hbody
    refine runtimeEquivalenceFor.execution rfl
      (solmExec.intro hsel rfl hdec rfl hbody') ?_
    rw [hxi]
    have hcreated : s.createdAccounts = evm''.createdAccounts :=
      (congrArg Prod.fst hsacc).trans hCreated
    have haccounts : accountMapEquiv s.accountMap evm''.accountMap := by
      change accountMapEquiv (s.createdAccounts, s.accountMap).2 evm''.accountMap
      rw [congrArg Prod.snd hsacc]; exact hAccounts
    exact execResultsEquiv.success rfl rfl hcreated haccounts (.abi henc)

/-- Getter form: the Solm body returns `rvSolm` (read from `σ_solm`) leaving state at `initState`,
    the EVM output encodes `rvEvm` (read from `σ_evm`), coupled by `hval : rvSolm = rvEvm`. -/
theorem tlcReEquivExecTransport {cfg : Config} {t : TransitionDecl}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {o : ByteArray} {callargs cs rvSolm rvEvm}
    (hcode : I.code = timelockControllerBenchBytecode)
    (h : RDret timelockControllerBenchBytecode g (initState cA gh bl σ_evm σ₀ g A I) (cA, σ_evm) o)
    (hsel : selectorDispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
              (transitionSignature t).paramTypes I.calldata = some callargs)
    (hbody : ExecTransitionBody cfg contract
              (initState cA gh bl σ_solm σ₀ g A I) callargs t.body
              (.returned cs (initState cA gh bl σ_solm σ₀ g A I) rvSolm))
    (hval : rvSolm = rvEvm)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (henc : returnEquiv o rvEvm t.returnType) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀ g.toUInt256 A I := by
  subst hval
  exact tlcReEquivExecGen hcode h hsel hdec hbody (by simp [initState])
    (by simpa [initState] using hAccounts) henc

/-- `RDrev ⇒ execution` (revert) for a directly-matched selector. -/
theorem tlcReEquivExecRev {cfg : Config} {t : TransitionDecl}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256} {callargs}
    (hcode : I.code = timelockControllerBenchBytecode)
    (h : RDrev timelockControllerBenchBytecode g (initState cA gh bl σ_evm σ₀ g A I))
    (hsel : selectorDispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
              (transitionSignature t).paramTypes I.calldata = some callargs)
    (hbody : ExecTransitionBody cfg contract
              (initState cA gh bl σ_solm σ₀ g A I) callargs t.body .reverted) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀ g.toUInt256 A I := by
  rcases h with hoog | ⟨g', o, hrev⟩
  · exact reEquiv_outOfGas (Xi_error_of_X (g := g.toUInt256) (by
      rw [← hcode] at hoog
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hoog))
  · have hxi := Xi_revert_of_X (g := g.toUInt256) (by
      rw [← hcode] at hrev
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hrev)
    have hbody' :
        ExecTransitionBody cfg contract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g.toUInt256) A I)
          callargs t.body .reverted := by
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hbody
    refine runtimeEquivalenceFor.execution rfl
      (solmExec.intro hsel rfl hdec rfl hbody') ?_
    rw [hxi]; exact execResultsEquiv.revert rfl rfl

/-- `RDrev ⇒ decodingFailed` for a directly-matched selector whose ABI decode fails. -/
theorem tlcReEquivDecodeFailed {cfg : Config} {t : TransitionDecl}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode)
    (h : RDrev timelockControllerBenchBytecode g (initState cA gh bl σ_evm σ₀ g A I))
    (hsel : selectorDispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
              (transitionSignature t).paramTypes I.calldata = none) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀ g.toUInt256 A I := by
  rcases h with hoog | ⟨g', o, hrev⟩
  · exact reEquiv_outOfGas (Xi_error_of_X (g := g.toUInt256) (by
      rw [← hcode] at hoog
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hoog))
  · have hxi := Xi_revert_of_X (g := g.toUInt256) (by
      rw [← hcode] at hrev
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hrev)
    exact runtimeEquivalenceFor.decodingFailed hsel rfl hdec hxi

/-- Non-payable function, `callvalue != 0` branch: the EVM reverts at the function's own callvalue
    guard.  On the Solm side the body reverts at its `require(msg.value == 0)` (when the calldata
    decodes) or decoding fails first — both revert, matching the EVM revert.  `hbodyRev` supplies the
    Solm body revert for the decode-success case (typically `bodyReverts_nonPayable`). -/
theorem tlcNonpayableRevert {cfg : Config} {t : TransitionDecl}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode)
    (h : RDrev timelockControllerBenchBytecode g (initState cA gh bl σ_evm σ₀ g A I))
    (hsel : selectorDispatchMsg contract I.calldata = some t)
    (hbodyRev : ∀ callargs,
      decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
        (transitionSignature t).paramTypes I.calldata = some callargs →
      ExecTransitionBody cfg contract (initState cA gh bl σ_solm σ₀ g A I) callargs t.body
        .reverted) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀ g.toUInt256 A I := by
  by_cases hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata = none
  · exact tlcReEquivDecodeFailed hcode h hsel hdec
  · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
    exact tlcReEquivExecRev hcode h hsel hca (hbodyRev callargs hca)

end OpenZeppelinBench.TimelockController
