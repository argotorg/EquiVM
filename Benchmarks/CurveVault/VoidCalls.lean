import Benchmarks.CurveVault.Calls

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault

-- LIBRARY CANDIDATE: an EXTCODESIZE-guarded, zero-value typed call with no decoded results.
theorem checkedVoidCallBridge {cfg : Config} {decl : ContractDecl} {code : ByteArray}
    {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {σ : AccountMap} {locals : Store}
    {mem rdata : ByteArray} {pc next target inOffset inSize outOffset : UInt256}
    {R nextStack : List UInt256} {receiver : Expr} {args : List Expr} {argVals : List Value}
    {name retVar : Ident}
    (hs : SourceState s0 I σ evm)
    (hr : evalExpr? cfg {contract := decl, locals := locals} evm receiver =
      .ok (.address (AccountAddress.ofUInt256 target)))
    (ha : evalExprs? cfg {contract := decl, locals := locals} evm args = .ok argVals)
    (hencode : cfg.externalABI.encode? name argVals = some (mem.readWithPadding inOffset.toNat inSize.toNat))
    (hdecode : ∀ out, cfg.externalABI.decode? name out = some [])
    (hpc : decode code pc = some (.CALL, .none)) (hsmall : inSize.toNat ≤ 2 ^ 64)
    (hstack : R.length + 1 ≤ 1024)
    (hprepare : extCodeSizeWord σ target ≠ ⟨0⟩ → ∃ gasArg aw k C,
      RD fork code I g s0 pc (gasArg :: target :: ⟨0⟩ :: inOffset :: inSize :: outOffset :: ⟨0⟩ :: R)
        mem aw rdata σ k C)
    (hnoCode : extCodeSizeWord σ target = ⟨0⟩ → RDrev fork code g s0)
    (hpass : ∀ {aw out σ' k C},
      RD fork code I g s0 (pc + ⟨1⟩) (⟨1⟩ :: R) mem aw out σ' k C →
      ∃ aw' k' C', RD fork code I g s0 next nextStack mem aw' out σ' k' C')
    (hfail : ∀ {aw out σ' k C},
      RD fork code I g s0 (pc + ⟨1⟩) (⟨0⟩ :: R) mem aw out σ' k C → RDrev fork code g s0) :
    (∃ (evm' : State) (σ' : AccountMap) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      ExecBlock fork cfg {contract := decl, locals := locals} evm
        [.require (.binary .gt (.extCodeSize receiver) (.intLit 0)),
          .externalCall receiver name (.intLit 0) args retVar]
        (.ok {contract := decl, locals := locals.insert retVar (collapseReturns [])} evm') ∧
      SourceState s0 I σ' evm' ∧ RD fork code I g s0 next nextStack mem aw' out σ' k' C') ∨
    (ExecBlock fork cfg {contract := decl, locals := locals} evm
      [.require (.binary .gt (.extCodeSize receiver) (.intLit 0)),
        .externalCall receiver name (.intLit 0) args retVar] .reverted ∧ RDrev fork code g s0) := by
  have hguard := evalExpr_codeGuard_of_accounts_eq hs.accounts rfl hr
  by_cases hzero : extCodeSizeWord σ target = ⟨0⟩
  · have hg : evalExpr? cfg {contract := decl, locals := locals} evm
        (.binary .gt (.extCodeSize receiver) (.intLit 0)) = .ok (.bool false) := by
      simpa only [hzero] using hguard
    exact Or.inr ⟨checkedExternalCallNoCode hg, hnoCode hzero⟩
  have hpos : 0 < (extCodeSizeWord σ target).toNat := by
    by_contra hn
    exact hzero (uint256_toNat_eq_zero (by omega))
  have hg : evalExpr? cfg {contract := decl, locals := locals} evm
      (.binary .gt (.extCodeSize receiver) (.intLit 0)) = .ok (.bool true) := by
    simpa only [hpos, decide_true] using hguard
  obtain ⟨gasArg, aw, k, C, rdCall⟩ := hprepare hzero
  obtain ⟨evm', σ', z, out, k', C', hcall, hs', rd, _, _⟩ :=
    typedCallBridge rdCall hs hpc hencode hsmall hstack
  change RD fork code I g s0 (pc + ⟨1⟩) ((if z then ⟨1⟩ else ⟨0⟩) :: R)
    (callOutputMem mem out outOffset ⟨0⟩) _ out σ' k' C' at rd
  rw [callOutputMem_zero] at rd
  have hcall' := hcall
  rw [← address_of_addressOfUInt256 target] at hcall'
  cases z with
  | false => exact Or.inr ⟨checkedExternalCallFailure (hperm := Or.inl rfl) hg hr ha hcall', hfail rd⟩
  | true =>
    obtain ⟨aw', k'', C'', rdNext⟩ := hpass rd
    exact Or.inl ⟨evm', σ', out, aw', k'', C'',
      checkedExternalCallSuccess (hperm := Or.inl rfl) hg hr ha hcall' (hdecode out), hs', rdNext⟩

end Benchmarks.CurveVault
