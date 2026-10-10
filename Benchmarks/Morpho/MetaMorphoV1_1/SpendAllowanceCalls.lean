import Benchmarks.Morpho.MetaMorphoV1_1.SpendAllowanceSource

/-! State and internal-call interfaces for allowance spending. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def spendAllowanceAllowed (evm : State) (owner spender : AccountAddress) (value : UInt256) : Prop :=
  allowanceWord evm owner spender = unlimitedAllowance ∨
    (value.toNat ≤ (allowanceWord evm owner spender).toNat ∧
      owner ≠ ⟨0, by decide⟩ ∧ spender ≠ ⟨0, by decide⟩)

def spendAllowanceState (evm : State) (owner spender : AccountAddress) (value : UInt256) : State :=
  if allowanceWord evm owner spender = unlimitedAllowance then evm
  else approvalState evm owner spender (UInt256.sub (allowanceWord evm owner spender) value)

theorem spendAllowanceBody (imms : Store) (evm : State)
    (owner spender : AccountAddress) (value : UInt256)
    (hgood : spendAllowanceAllowed evm owner spender value) :
    ∃ final, ExecFuncBody config (spendAllowanceFrame imms owner spender value) evm
      spendAllowanceFunction.body
      (.returned final (spendAllowanceState evm owner spender value) none) := by
  by_cases hmax : allowanceWord evm owner spender = unlimitedAllowance
  · simp only [spendAllowanceState, hmax, if_true]
    exact ⟨_, spendAllowanceUnlimitedBody imms evm owner spender value hmax⟩
  · simp only [spendAllowanceState, hmax, if_false]
    have hg := hgood.resolve_left hmax
    exact ⟨_, spendAllowanceFiniteBodyReturns imms evm owner spender value hmax
      hg.1 hg.2.1 hg.2.2⟩

theorem spendAllowanceCall {locals imms : Store} {evm : State} {owner spender : AccountAddress}
    {value : UInt256} {args : List Expr} {ret : Ident}
    (hargs : evalExprs? config ⟨contract, locals, imms⟩ evm args =
      .ok [.address owner, .address spender, uint256Value value])
    (hgood : spendAllowanceAllowed evm owner spender value) :
    ExecStmt config ⟨contract, locals, imms⟩ evm (.internalCall "_spendAllowance" args ret)
      (.ok ⟨contract, locals.insert ret .unit, imms⟩
        (spendAllowanceState evm owner spender value)) := by
  obtain ⟨final, hbody⟩ := spendAllowanceBody imms evm owner spender value hgood
  exact internalCallFunctionReturn (callee := spendAllowanceFunction) hargs rfl rfl hbody

theorem spendAllowanceCallReverts {locals imms : Store} {evm : State}
    {owner spender : AccountAddress} {value : UInt256} {args : List Expr} {ret : Ident}
    (hargs : evalExprs? config ⟨contract, locals, imms⟩ evm args =
      .ok [.address owner, .address spender, uint256Value value])
    (hbad : ¬ spendAllowanceAllowed evm owner spender value) :
    ExecStmt config ⟨contract, locals, imms⟩ evm (.internalCall "_spendAllowance" args ret)
      .reverted :=
  internalCallFunctionRevert (callee := spendAllowanceFunction) hargs rfl rfl
    (spendAllowanceFiniteBodyReverts imms evm owner spender value
      (fun h ↦ hbad (.inl h)) (fun h ↦ hbad (.inr h)))

theorem spendAllowanceCallStatic {locals imms : Store} {evm : State}
    {owner spender : AccountAddress} {value : UInt256} {args : List Expr} {ret : Ident}
    (hargs : evalExprs? config ⟨contract, locals, imms⟩ evm args =
      .ok [.address owner, .address spender, uint256Value value])
    (hfinite : allowanceWord evm owner spender ≠ unlimitedAllowance)
    (hgood : spendAllowanceAllowed evm owner spender value)
    (hperm : evm.executionEnv.perm = false) :
    ExecStmt config ⟨contract, locals, imms⟩ evm (.internalCall "_spendAllowance" args ret)
      .staticViolation := by
  have hg := hgood.resolve_left hfinite
  exact ExecStmt.internalCallStatic (callee := spendAllowanceFunction.toCallable) hargs rfl rfl
    (spendAllowanceFiniteBodyStatic imms evm owner spender value hfinite
      hg.1 hg.2.1 hg.2.2 hperm)

theorem spendAllowanceState_executionEnv (evm : State)
    (owner spender : AccountAddress) (value : UInt256) :
    (spendAllowanceState evm owner spender value).executionEnv = evm.executionEnv := by
  unfold spendAllowanceState
  split
  · rfl
  · exact storageStore_executionEnv _ _ _ _

end Benchmarks.Morpho.MetaMorphoV1_1
