import Proofs.ERC20.API

/-!
# ERC20 — the supply invariant on the bytecode

`Proofs.ERC20.API` proves `Inv` for every run of the Stele spec.  The refinement proofs of
`Examples/ERC20` (`erc20Correct`, `erc20ConstructorCorrect`) match every EVM execution of the
compiled code with such a run ending in the same account map, so the invariant transfers to the
bytecode:

* `erc20_bytecode_preserves_inv`: a call to the runtime bytecode (`Ethereum.EVM.Ξ`) that succeeds
  returns an account map satisfying `Inv` at the contract's address if the initial one did and the
  slots the call writes are unshared (`CallClean`);
* `erc20_initcode_establishes_inv`: a deployment that succeeds, from a state without balances,
  returns an account map satisfying `Inv` and deploys `erc20Bytecode`, assuming `SupplyClean`
  and `BalClean` for the deployer.

A call that reverts or runs out of gas returns no account map, so there is nothing to show.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace ERC20

/-! ## The invariant on an account map

`Ξ` returns an account map, not an `EVM.State`; `Inv` reads only the account map and the
contract's address, so it is restated on those. -/

/-- `Inv` for the account map `σ`: `totalSupply = Σ balances` in the storage of `owner`. -/
def InvAt (σ : AccountMap) (owner : AccountAddress) : Prop :=
  Inv { (default : EVM.State) with accountMap := σ, executionEnv.codeOwner := owner }

/-- `balanceOf[a]` in the storage of `owner`, for the account map `σ`. -/
def balOfAt (σ : AccountMap) (owner a : AccountAddress) : ℕ :=
  balOf { (default : EVM.State) with accountMap := σ, executionEnv.codeOwner := owner } a

theorem inv_iff_invAt (evm : EVM.State) :
    Inv evm ↔ InvAt evm.accountMap evm.executionEnv.codeOwner :=
  Iff.rfl

/-- The state `Ξ` starts from satisfies `Inv` iff its account map does. -/
theorem inv_initState (σ σ₀ : AccountMap) (g : Sat256) (A : Substate) (I : ExecutionEnv) :
    Inv (initState σ σ₀ g A I) ↔ InvAt σ I.codeOwner :=
  Iff.rfl

theorem balOf_initState (σ σ₀ : AccountMap) (g : Sat256) (A : Substate) (I : ExecutionEnv)
    (a : AccountAddress) : balOf (initState σ σ₀ g A I) a = balOfAt σ I.codeOwner a :=
  rfl

/-! ## Runtime -/

/-- **Every call to the ERC20 bytecode preserves the supply invariant.**  If the EVM runs
    `erc20Bytecode` — any accounts, gas, substate, caller, value and calldata whose written slots
    are unshared (`CallClean`) — and succeeds, the account map it returns satisfies `Inv` at the
    contract's address if the initial one did. -/
theorem erc20_bytecode_preserves_inv
    {σ σ₀ σ' : AccountMap} {g g' : UInt256} {A A' : Substate} {I : ExecutionEnv} {o : ByteArray}
    (hclean : CallClean I)
    (hcode : I.code = erc20Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hInv : InvAt σ I.codeOwner)
    (hΞ : Ξ σ σ₀ g A I = .ok (.success (σ', g', A') o)) :
    InvAt σ' I.codeOwner := by
  obtain ⟨hrun⟩ := erc20Correct
  cases hrun σ σ₀ g A I hcode hsize with
  | execution hΞ' hstele hequiv =>
    obtain rfl := hΞ'.symm.trans hΞ
    cases hequiv with
    | success h1 h2 h3 _ =>
      cases h1
      subst h2 h3
      obtain ⟨henv, hInv'⟩ :=
        erc20_steleExec_preserves_inv hclean ((inv_initState σ σ₀ _ A I).mpr hInv) hstele
      rw [inv_iff_invAt, henv] at hInv'
      exact hInv'
    | revert h1 _ => cases h1
    | noMatch h1 _ => cases h1
    | decodingFailed h1 _ => cases h1
    | invalidHalt h1 _ => cases h1
    | staticHalt h1 _ => cases h1
  | outOfGas hΞ' => cases hΞ'.symm.trans hΞ

/-! ## Deployment -/

/-- **Deploying the ERC20 establishes the supply invariant.**  If the EVM runs the initcode of a
    deployment (`erc20Initcode` followed by the encoded constructor argument, as
    `erc20Config.selfDeployment` produces it) from a state in which the contract has no balances
    and succeeds, the account map it returns satisfies `Inv` at the contract's address, and the
    code it deploys is `erc20Bytecode`.  Assumes no balance slot is the `totalSupply` slot
    (`SupplyClean`) and the deployer's balance slot is unshared (`BalClean I.source`). -/
theorem erc20_initcode_establishes_inv (hsup : SupplyClean)
    {σ σ₀ σ' : AccountMap} {g g' : UInt256} {A A' : Substate} {I : ExecutionEnv}
    {args : List Value} {deployedInitcode o : ByteArray}
    (hcd : BalClean I.source)
    (hdeploy : erc20Config.selfDeployment erc20Initcode args = some deployedInitcode)
    (hcode : I.code = deployedInitcode) (hcalldata : I.calldata = .empty) (hperm : I.perm = true)
    (hzero : ∀ a, balOfAt σ I.codeOwner a = 0)
    (hΞ : Ξ σ σ₀ g A I = .ok (.success (σ', g', A') o)) :
    InvAt σ' I.codeOwner ∧ o = erc20Bytecode := by
  cases erc20ConstructorCorrect σ σ₀ g A I args deployedInitcode hdeploy hcode hcalldata hperm with
  | execution hΞ' hstele hequiv _ =>
    obtain rfl := hΞ'.symm.trans hΞ
    cases hequiv with
    | success h1 h2 h3 h4 | successVoidReturn h1 h2 h3 h4 =>
      cases h1
      subst h2 h3
      obtain ⟨henv, hInv⟩ := erc20_deployment_establishes_inv hsup hcd hdeploy
        (fun a => (balOf_initState σ σ₀ _ A I a).trans (hzero a)) hstele
      rw [inv_iff_invAt, henv] at hInv
      exact ⟨hInv, h4⟩
    | revert h1 _ => cases h1
    | invalidHalt h1 _ => cases h1
  | outOfGas hΞ' => cases hΞ'.symm.trans hΞ

end ERC20
