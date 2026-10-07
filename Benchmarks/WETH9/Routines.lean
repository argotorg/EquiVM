import Benchmarks.WETH9.Dispatch

/-!
# WETH9 shared routine lemmas

Contract-wide `RD` combinators not covered by the library because WETH9 (solc 0.5.16, payable
`deposit`) emits a **per-function** non-payable callvalue guard rather than a shared-prologue one.
The guard shape is `JUMPDEST; CALLVALUE; DUP1; ISZERO; PUSH2 gt; JUMPI; PUSH1 0; DUP1; REVERT;
JUMPDEST gt; POP` — the peel lemmas below are the per-function analogues of the library's
`solcGuardCallvalueZero` / `solcGuardCallvalueNonzeroRevert`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.WETH9

/-- Non-payable callvalue guard, `callvalue == 0` branch: peel
    `JUMPDEST; CALLVALUE; DUP1; ISZERO; PUSH2 gt; JUMPI; …; JUMPDEST gt; POP`, reaching `gt + 2`
    with the selector word still on the stack.
    LIBRARY CANDIDATE: `Reasoning.Solc` — per-function analogue of `solcGuardCallvalueZero`. -/
theorem weth9GuardPeelOk {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {entry gt sel : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : AccountMap} {k C : ℕ}
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
    into the `PUSH1 0; DUP1; REVERT` stub.
    LIBRARY CANDIDATE: `Reasoning.Solc` — per-function analogue of `solcGuardCallvalueNonzeroRevert`. -/
theorem weth9GuardPeelRev {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {entry gt sel : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : AccountMap} {k C : ℕ}
    (h : RD code ee g s0 entry [sel] mem aw rdata acc k C)
    (hcv : ee.weiValue ≠ ⟨0⟩)
    (hd0 : decode code entry = some (.JUMPDEST, .none))
    (hd1 : decode code (entry + ⟨1⟩) = some (.CALLVALUE, .none))
    (hd2 : decode code (entry + ⟨1⟩ + ⟨1⟩) = some (.DUP1, .none))
    (hd3 : decode code (entry + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.ISZERO, .none))
    (hd4 : decode code (entry + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.Push .PUSH2, some (gt, 2)))
    (hd7 : decode code (entry + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3) = some (.JUMPI, .none))
    (hd8 : decode code (entry + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩)
        = some (.Push .PUSH1, some (⟨0⟩, 1)))
    (hd10 : decode code (entry + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ + UInt256.ofNat 2)
        = some (.DUP1, .none))
    (hd11 : decode code (entry + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩)
        = some (.REVERT, .none)) :
    RDrev code g s0 := by
  have hcond : UInt256.isZero ee.weiValue = ⟨0⟩ := isZero_eq_zero_of_ne hcv
  exact h.jumpdest hd0 (by simp)
    |>.callvalue hd1 (by simp)
    |>.dup1 hd2 (by simp)
    |>.iszero hd3 (by simp)
    |>.pushConst gt (op := .PUSH2) (width := 2) (by simp) hd4 (by simp)
    |>.jumpiNT hd7 hcond (by simp)
    |>.solcPush1Dup1Revert0 hd8 hd10 hd11 (by simp)

/-- Combined nested-mapping getter (chains the library inner-hash / outer-hash / load-and-jump).
    LIBRARY CANDIDATE: `Reasoning.Solc` — the nested analogue of `RD.solcSingleMappingGetter`. -/
theorem weth9NestedMappingGetter {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {k C : ℕ} {pc baseSlot owner spender ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {σ : AccountMap}
    (h : RD code ee g s0 pc (spender :: owner :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata σ k C)
    (hwf : solcNestedMappingGetterWf code pc baseSlot)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (solcSlotWord σ ee (solcMappingSlot (solcMappingSlot baseSlot owner) spender) :: ret :: R)
      (solcNestedMappingHashMem baseSlot owner spender) (UInt256.ofNat 3) rdata σ k' C' := by
  obtain ⟨_, _, hinner⟩ := RD.solcNestedMappingInnerHash h hwf hov
  obtain ⟨_, _, houter⟩ := RD.solcNestedMappingOuterHash hinner hwf hov
  exact RD.solcNestedMappingLoadAndJump houter hwf hret (by omega)

/-! ## Connect lemmas taking a direct selector dispatch

WETH9 has a payable fallback (`contract.fallback = some fallbackTransition`), so the library
`reEquiv*` bridges — which require `contract.fallback = none` to convert a `dispatchMsg` fact into a
`selectorDispatchMsg` one — do not apply on the selector-match path.  When a named selector matches,
`selectorDispatchMsg contract I.calldata = some t` holds directly; these lemmas consume that,
mirroring `RDret.reEquivExecutionGen` / `RDrev.reEquivExecutionRevert`. -/

/-- `RDret ⇒ execution` for a directly-matched selector. -/
theorem weth9ReEquivExecGen {cfg : Config} {contract : ContractDecl} {t : TransitionDecl}
    {σ σ₀ A I} {g : Sat256}
    {o : ByteArray} {callargs cs retVal}
    {acc : AccountMap} {evm'' : EVM.State}
    (hcode : I.code = weth9Bytecode)
    (h : RDret weth9Bytecode g (initState σ σ₀ g A I) acc o)
    (hsel : selectorDispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
              (transitionSignature t).paramTypes I.calldata = some callargs)
    (hbody : ExecTransitionBody cfg contract
              (initState σ σ₀ g A I) callargs t.body
              (.returned cs evm'' retVal))
    (hAccountMap : acc = evm''.accountMap)
    (henc : returnEquiv o retVal t.returnType) :
    runtimeRefinementFor cfg contract σ σ₀ g.toUInt256 A I := by
  rcases h with hoog | ⟨s, hX, hsacc⟩
  · exact reEquiv_outOfGas (Xi_error_of_X (g := g.toUInt256) (by
      rw [← hcode] at hoog
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hoog))
  · have hxi := Xi_success_of_X (g := g.toUInt256) (by
      rw [← hcode] at hX
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hX)
    have hbody' :
        ExecTransitionBody cfg contract
          (initState σ σ₀ (Sat256.ofUInt256 g.toUInt256) A I)
          callargs t.body (.returned cs evm'' retVal) := by
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hbody
    refine runtimeRefinementFor.execution rfl
      (solmExec.intro hsel rfl hdec rfl hbody') ?_
    rw [hxi]
    have haccounts : s.accountMap = evm''.accountMap := hsacc.trans hAccountMap
    exact execResultsEquiv.success rfl rfl haccounts (.abi henc)

/-- `RDrev ⇒ execution` (revert) for a directly-matched selector. -/
theorem weth9ReEquivExecRev {cfg : Config} {contract : ContractDecl} {t : TransitionDecl}
    {σ σ₀ A I} {g : Sat256} {callargs}
    (hcode : I.code = weth9Bytecode)
    (h : RDrev weth9Bytecode g (initState σ σ₀ g A I))
    (hsel : selectorDispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
              (transitionSignature t).paramTypes I.calldata = some callargs)
    (hbody : ExecTransitionBody cfg contract
              (initState σ σ₀ g A I) callargs t.body .reverted) :
    runtimeRefinementFor cfg contract σ σ₀ g.toUInt256 A I := by
  rcases h with hoog | ⟨g', o, hrev⟩
  · exact reEquiv_outOfGas (Xi_error_of_X (g := g.toUInt256) (by
      rw [← hcode] at hoog
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hoog))
  · have hxi := Xi_revert_of_X (g := g.toUInt256) (by
      rw [← hcode] at hrev
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hrev)
    have hbody' :
        ExecTransitionBody cfg contract
          (initState σ σ₀ (Sat256.ofUInt256 g.toUInt256) A I)
          callargs t.body .reverted := by
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hbody
    refine runtimeRefinementFor.execution rfl
      (solmExec.intro hsel rfl hdec rfl hbody') ?_
    rw [hxi]; exact execResultsEquiv.revert rfl rfl

/-- `RDrev ⇒ decodingFailed` for a directly-matched selector whose ABI decode fails. -/
theorem weth9ReEquivDecodeFailed {cfg : Config} {contract : ContractDecl} {t : TransitionDecl}
    {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode)
    (h : RDrev weth9Bytecode g (initState σ σ₀ g A I))
    (hsel : selectorDispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
              (transitionSignature t).paramTypes I.calldata = none) :
    runtimeRefinementFor cfg contract σ σ₀ g.toUInt256 A I := by
  rcases h with hoog | ⟨g', o, hrev⟩
  · exact reEquiv_outOfGas (Xi_error_of_X (g := g.toUInt256) (by
      rw [← hcode] at hoog
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hoog))
  · have hxi := Xi_revert_of_X (g := g.toUInt256) (by
      rw [← hcode] at hrev
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hrev)
    exact runtimeRefinementFor.decodingFailed hsel rfl hdec hxi

/-- Non-payable function, `callvalue != 0` branch: the EVM reverts at the function's own callvalue
    guard.  On the Solm side the body reverts at its `require(msg.value == 0)` (when the calldata
    decodes) or decoding fails first — both revert, matching the EVM revert.  `hbodyRev` supplies the
    Solm body revert for the decode-success case (typically `bodyReverts_nonPayable`). -/
theorem weth9NonpayableRevert {cfg : Config} {contract : ContractDecl} {t : TransitionDecl}
    {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode)
    (h : RDrev weth9Bytecode g (initState σ σ₀ g A I))
    (hsel : selectorDispatchMsg contract I.calldata = some t)
    (hbodyRev : ∀ callargs,
      decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
        (transitionSignature t).paramTypes I.calldata = some callargs →
      ExecTransitionBody cfg contract (initState σ σ₀ g A I) callargs t.body
        .reverted) :
    runtimeRefinementFor cfg contract σ σ₀ g.toUInt256 A I := by
  by_cases hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata = none
  · exact weth9ReEquivDecodeFailed hcode h hsel hdec
  · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
    exact weth9ReEquivExecRev hcode h hsel hca (hbodyRev callargs hca)

end Benchmarks.WETH9
