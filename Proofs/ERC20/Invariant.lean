import Proofs.ERC20.Balances
import Examples.ERC20.Correct
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# ERC20 contract invariant — `totalSupply = Σ balances`

The classic ERC20 supply invariant `totalSupply = Σ_a balanceOf[a]`, stated on the Stele spec's
storage, and its preservation by the post-states the spec's mutating bodies produce:
`transferPostState`, `transferFromPostState`, `approvePostState`, and the constructor's
`erc20CtorPostState` (all from `Examples/ERC20`).  `Proofs.ERC20.API` lifts these to every
execution of every ABI entry point.

The sum `Σ_a balanceOf[a]` ranges over *all* addresses.  Because `AccountAddress` is a finite type
(`Fin _`), `∑ a : AccountAddress, balOf evm a` is a genuine `Finset.univ` sum — finitely supported
automatically, with no auxiliary "set of holders" and no new axioms.  Each theorem assumes only
that the slots its call writes are not shared (`BalClean`, `AllowClean`; the constructor also
`SupplyClean`; see `Proofs.ERC20.Balances`).

The preservation theorems need no hypothesis on the contract's account: if it is missing every
storage write is a no-op, and a self-transfer (`from = to`) writes the sender's balance back.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory
open scoped BigOperators

set_option maxHeartbeats 1000000

namespace ERC20

/-! ## The invariant -/

/-- The sum of every account's `balanceOf` (a `Finset.univ` sum over the finite address type). -/
noncomputable def totalBalances (evm : EVM.State) : ℕ :=
  ∑ a : AccountAddress, balOf evm a

/-- The ERC20 supply invariant: stored `totalSupply` equals the sum of all balances. -/
def Inv (evm : EVM.State) : Prop :=
  totalSupplyVal evm = totalBalances evm

/-- A missing contract account stores nothing: `totalSupply` reads as `0`. -/
theorem totalSupplyVal_of_missing (evm : EVM.State)
    (hmiss : evm.accountMap.get? evm.executionEnv.codeOwner = none) : totalSupplyVal evm = 0 := by
  rw [totalSupplyVal, Stele.EVM.storageLoad, Ethereum.State.lookupAccount, hmiss]; rfl

/-! ## Generic two-point "transfer" sum lemma

Moving `v` units from `x` to `y` (`x ≠ y`, `v ≤ f x`) leaves the total unchanged.  This is the
combinatorial heart of every balance-conserving transition. -/

theorem sum_transfer_eq {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℕ) {x y : α} (hxy : x ≠ y)
    (v : ℕ) (hv : v ≤ f x) :
    (∑ a, Function.update (Function.update f x (f x - v)) y (f y + v) a) = ∑ a, f a := by
  have hx' : x ∈ (Finset.univ : Finset α) \ {y} :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, by simp [hxy]⟩
  rw [Finset.sum_update_of_mem (Finset.mem_univ y),
      Finset.sum_update_of_mem hx']
  have hRy : (∑ a, f a) = f y + ∑ a ∈ (Finset.univ : Finset α) \ {y}, f a := by
    rw [← Finset.sum_update_of_mem (Finset.mem_univ y) f (f y), Function.update_eq_self]
  have hRx : (∑ a ∈ (Finset.univ : Finset α) \ {y}, f a)
      = f x + ∑ a ∈ ((Finset.univ : Finset α) \ {y}) \ {x}, f a := by
    rw [← Finset.sum_update_of_mem hx' f (f x), Function.update_eq_self]
  rw [hRy, hRx]
  omega

/-! ## `transfer` preserves the invariant -/

section Transfer

variable (evm : EVM.State) (I : ExecutionEnv)

/-- Storage writes leave the execution environment untouched. -/
theorem transferPostState_executionEnv :
    (transferPostState evm I).executionEnv = evm.executionEnv := by
  simp only [transferPostState, transferAfterDebitState, storageStore_codeOwner]

/-- `codeOwner` is unchanged by the transfer post-state (storage writes don't touch the env). -/
theorem transferPostState_codeOwner :
    (transferPostState evm I).executionEnv.codeOwner = evm.executionEnv.codeOwner := by
  simp only [transferPostState, transferAfterDebitState, storageStore_codeOwner]

/-- The sender's pre-balance, as named by the spec, *is* `balOf` at the caller. -/
theorem balOf_source_eq :
    balOf evm evm.executionEnv.source = (transferFromBalanceWord evm).toNat := rfl

/-- `transfer` leaves `totalSupply` untouched: both balance writes hit `balanceOf` slots, distinct
    from the `totalSupply` slot. -/
theorem totalSupplyVal_transferPostState (hcs : BalClean evm.executionEnv.source)
    (hct : BalClean (AccountAddress.ofNat (transferToWord I).toNat)) :
    totalSupplyVal (transferPostState evm I) = totalSupplyVal evm := by
  simp only [totalSupplyVal, transferPostState, transferAfterDebitState, storageStore_codeOwner]
  rw [storageLoad_storageStore_ne _ _ _ _ _
        (by simpa [transferToSlot] using hct.ne_supply.symm),
      storageLoad_storageStore_ne _ _ _ _ _
        (by simpa [transferSenderSlot] using hcs.ne_supply.symm)]

/-- The debit word's value is the sender's balance minus the transferred amount (no underflow). -/
theorem transferDebitWord_toNat :
    (transferDebitWord evm I).toNat =
      balOf evm evm.executionEnv.source - (transferValueWord I).toNat := by
  rw [balOf_source_eq]
  simp only [transferDebitWord]
  exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _) (transferFromBalanceWord evm).val.isLt)

/-- The recipient's pre-balance, as named by the spec, *is* `balOf` at the recipient. -/
theorem transferToBalanceWord_toNat (hcs : BalClean evm.executionEnv.source)
    (hne : evm.executionEnv.source ≠ AccountAddress.ofNat (transferToWord I).toNat) :
    (transferToBalanceWord evm I).toNat =
      balOf evm (AccountAddress.ofNat (transferToWord I).toNat) := by
  simp only [transferToBalanceWord, transferAfterDebitState, balOf]
  rw [storageLoad_storageStore_ne _ _ _ _ _
        (by simpa [transferToSlot, transferSenderSlot] using
          hcs.unshared _ (Ne.symm hne))]
  rfl

/-- Recipient's post-balance: `balOf evm to + value`. -/
theorem balOf_transferPostState_to (hcs : BalClean evm.executionEnv.source)
    {acc : Account} (hco : evm.accountMap.get? evm.executionEnv.codeOwner = some acc)
    (hne : evm.executionEnv.source ≠ AccountAddress.ofNat (transferToWord I).toNat)
    (hfit : transferNewToNat evm I < UInt256.size) :
    balOf (transferPostState evm I) (AccountAddress.ofNat (transferToWord I).toNat) =
      balOf evm (AccountAddress.ofNat (transferToWord I).toNat) + (transferValueWord I).toNat := by
  obtain ⟨acc', hX⟩ := storageStore_find_codeOwner evm evm.executionEnv.codeOwner
    (transferSenderSlot evm) (transferDebitWord evm I) hco
  rw [balOf]
  simp only [transferPostState, transferAfterDebitState, storageStore_codeOwner]
  rw [show erc20BalanceOfSlot (KeyValue.address (AccountAddress.ofNat (transferToWord I).toNat))
        = transferToSlot I from rfl]
  rw [storageLoad_storageStore_self _ _ _ _ hX, transferNewToWord_toNat evm I hfit,
    transferNewToNat, transferToBalanceWord_toNat evm I hcs hne]

/-- Caller's post-balance: `balOf evm from - value`. -/
theorem balOf_transferPostState_from
    (hct : BalClean (AccountAddress.ofNat (transferToWord I).toNat))
    {acc : Account} (hco : evm.accountMap.get? evm.executionEnv.codeOwner = some acc)
    (hne : evm.executionEnv.source ≠ AccountAddress.ofNat (transferToWord I).toNat) :
    balOf (transferPostState evm I) evm.executionEnv.source =
      balOf evm evm.executionEnv.source - (transferValueWord I).toNat := by
  rw [balOf]
  simp only [transferPostState, transferAfterDebitState, storageStore_codeOwner]
  rw [storageLoad_storageStore_ne _ _ _ _ _
        (by simpa [transferToSlot, transferSenderSlot] using hct.unshared _ hne)]
  rw [show erc20BalanceOfSlot (KeyValue.address evm.executionEnv.source) = transferSenderSlot evm
        from rfl]
  rw [storageLoad_storageStore_self _ _ _ _ hco, transferDebitWord_toNat evm I]

/-- Any third party's balance is untouched by `transfer`. -/
theorem balOf_transferPostState_other (hcs : BalClean evm.executionEnv.source)
    (hct : BalClean (AccountAddress.ofNat (transferToWord I).toNat)) (a : AccountAddress)
    (hat : a ≠ AccountAddress.ofNat (transferToWord I).toNat) (has : a ≠ evm.executionEnv.source) :
    balOf (transferPostState evm I) a = balOf evm a := by
  rw [balOf, balOf]
  simp only [transferPostState, transferAfterDebitState, storageStore_codeOwner]
  rw [storageLoad_storageStore_ne _ _ _ _ _
        (by simpa [transferToSlot] using hct.unshared a hat)]
  rw [storageLoad_storageStore_ne _ _ _ _ _
        (by simpa [transferSenderSlot] using hcs.unshared a has)]

/-- **Pointwise balance effect of `transfer`** between distinct accounts: the post-state balances
    are exactly the pre-state balances with `value` moved from the caller to the recipient. -/
theorem balOf_transferPostState (hcs : BalClean evm.executionEnv.source)
    (hct : BalClean (AccountAddress.ofNat (transferToWord I).toNat))
    {acc : Account} (hco : evm.accountMap.get? evm.executionEnv.codeOwner = some acc)
    (hne : evm.executionEnv.source ≠ AccountAddress.ofNat (transferToWord I).toNat)
    (hfit : transferNewToNat evm I < UInt256.size) :
    balOf (transferPostState evm I) =
      Function.update
        (Function.update (balOf evm) evm.executionEnv.source
          (balOf evm evm.executionEnv.source - (transferValueWord I).toNat))
        (AccountAddress.ofNat (transferToWord I).toNat)
        (balOf evm (AccountAddress.ofNat (transferToWord I).toNat) +
          (transferValueWord I).toNat) := by
  funext a
  by_cases hat : a = AccountAddress.ofNat (transferToWord I).toNat
  · subst hat
    rw [Function.update_self, balOf_transferPostState_to evm I hcs hco hne hfit]
  · by_cases has : a = evm.executionEnv.source
    · subst has
      rw [Function.update_of_ne hat, Function.update_self,
        balOf_transferPostState_from evm I hct hco hne]
    · rw [Function.update_of_ne hat, Function.update_of_ne has,
        balOf_transferPostState_other evm I hcs hct a hat has]

/-! ### Self-transfer (`to = msg.sender`) -/

theorem transferToSlot_eq_of_self
    (hself : evm.executionEnv.source = AccountAddress.ofNat (transferToWord I).toNat) :
    transferToSlot I = transferSenderSlot evm := by
  simp only [transferToSlot, transferSenderSlot, hself]

/-- A self-transfer credits back exactly what it debited. -/
theorem transferNewToNat_of_self {acc : Account}
    (hco : evm.accountMap.get? evm.executionEnv.codeOwner = some acc)
    (hself : evm.executionEnv.source = AccountAddress.ofNat (transferToWord I).toNat)
    (henough : (transferValueWord I).toNat ≤ balOf evm evm.executionEnv.source) :
    transferNewToNat evm I = balOf evm evm.executionEnv.source := by
  rw [transferNewToNat, transferToBalanceWord, transferToSlot_eq_of_self evm I hself,
    transferAfterDebitState, storageLoad_storageStore_self _ _ _ _ hco, transferDebitWord_toNat]
  omega

/-- **Pointwise balance effect of a self-transfer**: no balance changes. -/
theorem balOf_transferPostState_self (hcs : BalClean evm.executionEnv.source)
    {acc : Account} (hco : evm.accountMap.get? evm.executionEnv.codeOwner = some acc)
    (hself : evm.executionEnv.source = AccountAddress.ofNat (transferToWord I).toNat)
    (henough : (transferValueWord I).toNat ≤ balOf evm evm.executionEnv.source) :
    balOf (transferPostState evm I) = balOf evm := by
  funext a
  by_cases ha : a = evm.executionEnv.source
  · subst ha
    obtain ⟨acc', hX⟩ := storageStore_find_codeOwner evm evm.executionEnv.codeOwner
      (transferSenderSlot evm) (transferDebitWord evm I) hco
    have hfit : transferNewToNat evm I < UInt256.size := by
      rw [transferNewToNat_of_self evm I hco hself henough]
      exact Fin.isLt _
    rw [balOf]
    simp only [transferPostState, transferAfterDebitState, storageStore_codeOwner]
    rw [show erc20BalanceOfSlot (KeyValue.address evm.executionEnv.source) = transferToSlot I from
      (transferToSlot_eq_of_self evm I hself).symm]
    rw [storageLoad_storageStore_self _ _ _ _ hX, transferNewToWord_toNat evm I hfit,
      transferNewToNat_of_self evm I hco hself henough]
  · rw [balOf, balOf]
    simp only [transferPostState, transferAfterDebitState, storageStore_codeOwner]
    rw [transferToSlot_eq_of_self evm I hself]
    rw [storageLoad_storageStore_ne _ _ _ _ _
          (by simpa [transferSenderSlot] using hcs.unshared a ha),
        storageLoad_storageStore_ne _ _ _ _ _
          (by simpa [transferSenderSlot] using hcs.unshared a ha)]

/-! ### Missing contract account -/

/-- Without a contract account every storage write is a no-op. -/
theorem transferPostState_of_missing
    (hmiss : evm.accountMap.get? evm.executionEnv.codeOwner = none) :
    transferPostState evm I = evm := by
  simp only [transferPostState, transferAfterDebitState]
  rw [storageStore_noop_of_missing _ _ _ _ hmiss, storageStore_noop_of_missing _ _ _ _ hmiss]

/-- **`transfer` preserves the supply invariant**, for any sender and recipient (including
    `to = msg.sender`), whenever its two `require`/range checks pass. -/
theorem transfer_preserves_inv (hcs : BalClean evm.executionEnv.source)
    (hct : BalClean (AccountAddress.ofNat (transferToWord I).toNat))
    (henough : (transferValueWord I).toNat ≤ balOf evm evm.executionEnv.source)
    (hfit : transferNewToNat evm I < UInt256.size)
    (hInv : Inv evm) : Inv (transferPostState evm I) := by
  rcases hacc : evm.accountMap.get? evm.executionEnv.codeOwner with _ | acc
  · rw [transferPostState_of_missing evm I hacc]; exact hInv
  · unfold Inv totalBalances at *
    rw [totalSupplyVal_transferPostState evm I hcs hct, hInv]
    by_cases hself : evm.executionEnv.source = AccountAddress.ofNat (transferToWord I).toNat
    · rw [balOf_transferPostState_self evm I hcs hacc hself henough]
    · rw [balOf_transferPostState evm I hcs hct hacc hself hfit]
      exact (sum_transfer_eq (balOf evm) hself (transferValueWord I).toNat henough).symm

end Transfer

/-! ## `approve` preserves the invariant

`approve` writes only an `allowance` slot — by `AllowClean`, disjoint from every `balanceOf` slot
and from `totalSupply` — so it perturbs neither side of the invariant. -/

section Approve

variable (evm : EVM.State) (I : ExecutionEnv)

theorem approvePostState_executionEnv :
    (approvePostState evm I).executionEnv = evm.executionEnv := by
  simp only [approvePostState, storageStore_codeOwner]

theorem balOf_approvePostState
    (hca : AllowClean evm.executionEnv.source (AccountAddress.ofNat (approveSpenderWord I).toNat))
    (a : AccountAddress) :
    balOf (approvePostState evm I) a = balOf evm a := by
  rw [balOf, balOf]
  simp only [approvePostState, storageStore_codeOwner]
  rw [storageLoad_storageStore_ne _ _ _ _ _
        (by simpa [approveSlot] using (hca.ne_balanceOf a).symm)]

theorem totalSupplyVal_approvePostState
    (hca : AllowClean evm.executionEnv.source (AccountAddress.ofNat (approveSpenderWord I).toNat)) :
    totalSupplyVal (approvePostState evm I) = totalSupplyVal evm := by
  simp only [totalSupplyVal, approvePostState, storageStore_codeOwner]
  rw [storageLoad_storageStore_ne _ _ _ _ _
        (by simpa [approveSlot] using hca.ne_supply.symm)]

/-- **`approve` preserves the supply invariant** (it touches no balance and not `totalSupply`). -/
theorem approve_preserves_inv
    (hca : AllowClean evm.executionEnv.source (AccountAddress.ofNat (approveSpenderWord I).toNat))
    (hInv : Inv evm) : Inv (approvePostState evm I) := by
  unfold Inv totalBalances at *
  rw [totalSupplyVal_approvePostState evm I hca, hInv]
  exact Finset.sum_congr rfl (fun a _ => (balOf_approvePostState evm I hca a).symm)

end Approve

/-! ## `transferFrom` preserves the invariant

`transferFrom` does everything `transfer` does — move `value` from `from` to `to` — plus a write to
the `allowance[from][msg.sender]` slot, which `AllowClean` makes disjoint from all balance slots
and from `totalSupply`.  So the balance-conservation argument is identical, with one extra
disjoint write to frame past. -/

section TransferFrom

variable (evm : EVM.State) (I : ExecutionEnv)

theorem transferFromPostState_executionEnv :
    (transferFromPostState evm I).executionEnv = evm.executionEnv := by
  simp only [transferFromPostState, transferFromAfterBalanceState,
    transferFromAfterAllowanceState, storageStore_codeOwner]

theorem transferFromPostState_codeOwner :
    (transferFromPostState evm I).executionEnv.codeOwner = evm.executionEnv.codeOwner := by
  simp only [transferFromPostState, transferFromAfterBalanceState,
    transferFromAfterAllowanceState, storageStore_codeOwner]

/-- The recipient's pre-balance under `transferFrom`, read through the allowance and `from` writes. -/
theorem transferFromToBalanceWord_toNat
    (hca : AllowClean (AccountAddress.ofNat (transferFromFromWord I).toNat)
      evm.executionEnv.source)
    (hcf : BalClean (AccountAddress.ofNat (transferFromFromWord I).toNat))
    (hft : AccountAddress.ofNat (transferFromFromWord I).toNat ≠
      AccountAddress.ofNat (transferFromToWord I).toNat) :
    (transferFromToBalanceWord evm I).toNat =
      balOf evm (AccountAddress.ofNat (transferFromToWord I).toNat) := by
  simp only [transferFromToBalanceWord, transferFromAfterBalanceState,
    transferFromAfterAllowanceState, balOf]
  rw [storageLoad_storageStore_ne _ _ _ _ _
        (by simpa [transferFromToSlot, transferFromFromSlot] using hcf.unshared _ hft.symm)]
  rw [storageLoad_storageStore_ne _ _ _ _ _
        (by simpa [transferFromToSlot, transferFromAllowanceSlot] using
          (hca.ne_balanceOf (AccountAddress.ofNat (transferFromToWord I).toNat)).symm)]
  rfl

/-- The `from`-balance debit value: `balOf evm from - value` (read past the allowance write). -/
theorem transferFromBalanceDebitWord_toNat
    (hca : AllowClean (AccountAddress.ofNat (transferFromFromWord I).toNat)
      evm.executionEnv.source) :
    (transferFromBalanceDebitWord (transferFromAfterAllowanceState evm I) I).toNat =
      balOf evm (AccountAddress.ofNat (transferFromFromWord I).toNat) -
        (transferFromValueWord I).toNat := by
  have hval : (transferFromFromBalanceWord (transferFromAfterAllowanceState evm I) I) =
      transferFromFromBalanceWord evm I := by
    simp only [transferFromFromBalanceWord, transferFromAfterAllowanceState,
      storageStore_codeOwner]
    rw [storageLoad_storageStore_ne _ _ _ _ _
          (by simpa [transferFromFromSlot, transferFromAllowanceSlot] using
            (hca.ne_balanceOf (AccountAddress.ofNat (transferFromFromWord I).toNat)).symm)]
  simp only [transferFromBalanceDebitWord, hval]
  exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _) (transferFromFromBalanceWord evm I).val.isLt)

/-- Recipient's post-balance under `transferFrom`: `balOf evm to + value`. -/
theorem balOf_transferFromPostState_to
    (hca : AllowClean (AccountAddress.ofNat (transferFromFromWord I).toNat)
      evm.executionEnv.source)
    (hcf : BalClean (AccountAddress.ofNat (transferFromFromWord I).toNat))
    {acc : Account} (hco : evm.accountMap.get? evm.executionEnv.codeOwner = some acc)
    (hft : AccountAddress.ofNat (transferFromFromWord I).toNat ≠
      AccountAddress.ofNat (transferFromToWord I).toNat)
    (hfit : transferFromNewToNat evm I < UInt256.size) :
    balOf (transferFromPostState evm I) (AccountAddress.ofNat (transferFromToWord I).toNat) =
      balOf evm (AccountAddress.ofNat (transferFromToWord I).toNat) +
        (transferFromValueWord I).toNat := by
  obtain ⟨_, hcoA⟩ := storageStore_find_codeOwner evm evm.executionEnv.codeOwner
    (transferFromAllowanceSlot evm I) (transferFromAllowanceDebitWord evm I) hco
  obtain ⟨_, hcoB⟩ := storageStore_find_codeOwner (transferFromAfterAllowanceState evm I)
    evm.executionEnv.codeOwner (transferFromFromSlot I)
    (transferFromBalanceDebitWord (transferFromAfterAllowanceState evm I) I) hcoA
  rw [balOf, transferFromPostState_codeOwner, transferFromPostState]
  rw [show erc20BalanceOfSlot (KeyValue.address (AccountAddress.ofNat (transferFromToWord I).toNat))
        = transferFromToSlot I from rfl]
  rw [storageLoad_storageStore_self (transferFromAfterBalanceState evm I)
        evm.executionEnv.codeOwner (transferFromToSlot I) (transferFromNewToWord evm I) hcoB]
  rw [transferFromNewToWord_toNat evm I hfit, transferFromNewToNat,
    transferFromToBalanceWord_toNat evm I hca hcf hft]

/-- Sender's (`from`) post-balance under `transferFrom`: `balOf evm from - value`. -/
theorem balOf_transferFromPostState_from
    (hca : AllowClean (AccountAddress.ofNat (transferFromFromWord I).toNat)
      evm.executionEnv.source)
    (hct : BalClean (AccountAddress.ofNat (transferFromToWord I).toNat))
    {acc : Account} (hco : evm.accountMap.get? evm.executionEnv.codeOwner = some acc)
    (hft : AccountAddress.ofNat (transferFromFromWord I).toNat ≠
      AccountAddress.ofNat (transferFromToWord I).toNat) :
    balOf (transferFromPostState evm I) (AccountAddress.ofNat (transferFromFromWord I).toNat) =
      balOf evm (AccountAddress.ofNat (transferFromFromWord I).toNat) -
        (transferFromValueWord I).toNat := by
  obtain ⟨_, hcoA⟩ := storageStore_find_codeOwner evm evm.executionEnv.codeOwner
    (transferFromAllowanceSlot evm I) (transferFromAllowanceDebitWord evm I) hco
  rw [balOf, transferFromPostState_codeOwner, transferFromPostState]
  rw [storageLoad_storageStore_ne _ _ _ _ _
        (by simpa [transferFromToSlot, transferFromFromSlot] using hct.unshared _ hft)]
  rw [transferFromAfterBalanceState]
  rw [show erc20BalanceOfSlot (KeyValue.address (AccountAddress.ofNat (transferFromFromWord I).toNat))
        = transferFromFromSlot I from rfl]
  rw [storageLoad_storageStore_self (transferFromAfterAllowanceState evm I)
        evm.executionEnv.codeOwner (transferFromFromSlot I)
        (transferFromBalanceDebitWord (transferFromAfterAllowanceState evm I) I) hcoA]
  rw [transferFromBalanceDebitWord_toNat evm I hca]

/-- Any third party's balance is untouched by `transferFrom`. -/
theorem balOf_transferFromPostState_other
    (hca : AllowClean (AccountAddress.ofNat (transferFromFromWord I).toNat)
      evm.executionEnv.source)
    (hcf : BalClean (AccountAddress.ofNat (transferFromFromWord I).toNat))
    (hct : BalClean (AccountAddress.ofNat (transferFromToWord I).toNat)) (a : AccountAddress)
    (hfrom : a ≠ AccountAddress.ofNat (transferFromFromWord I).toNat)
    (hto : a ≠ AccountAddress.ofNat (transferFromToWord I).toNat) :
    balOf (transferFromPostState evm I) a = balOf evm a := by
  rw [balOf, balOf, transferFromPostState_codeOwner, transferFromPostState,
    transferFromAfterBalanceState, transferFromAfterAllowanceState]
  rw [storageLoad_storageStore_ne _ _ _ _ _
        (by simpa [transferFromToSlot] using hct.unshared a hto)]
  rw [storageLoad_storageStore_ne _ _ _ _ _
        (by simpa [transferFromFromSlot] using hcf.unshared a hfrom)]
  rw [storageLoad_storageStore_ne _ _ _ _ _
        (by simpa [transferFromAllowanceSlot] using (hca.ne_balanceOf a).symm)]

/-- **Pointwise balance effect of `transferFrom`** between distinct accounts. -/
theorem balOf_transferFromPostState
    (hca : AllowClean (AccountAddress.ofNat (transferFromFromWord I).toNat)
      evm.executionEnv.source)
    (hcf : BalClean (AccountAddress.ofNat (transferFromFromWord I).toNat))
    (hct : BalClean (AccountAddress.ofNat (transferFromToWord I).toNat))
    {acc : Account} (hco : evm.accountMap.get? evm.executionEnv.codeOwner = some acc)
    (hft : AccountAddress.ofNat (transferFromFromWord I).toNat ≠
      AccountAddress.ofNat (transferFromToWord I).toNat)
    (hfit : transferFromNewToNat evm I < UInt256.size) :
    balOf (transferFromPostState evm I) =
      Function.update
        (Function.update (balOf evm) (AccountAddress.ofNat (transferFromFromWord I).toNat)
          (balOf evm (AccountAddress.ofNat (transferFromFromWord I).toNat) -
            (transferFromValueWord I).toNat))
        (AccountAddress.ofNat (transferFromToWord I).toNat)
        (balOf evm (AccountAddress.ofNat (transferFromToWord I).toNat) +
          (transferFromValueWord I).toNat) := by
  funext a
  by_cases hat : a = AccountAddress.ofNat (transferFromToWord I).toNat
  · subst hat
    rw [Function.update_self, balOf_transferFromPostState_to evm I hca hcf hco hft hfit]
  · by_cases haf : a = AccountAddress.ofNat (transferFromFromWord I).toNat
    · subst haf
      rw [Function.update_of_ne hat, Function.update_self,
        balOf_transferFromPostState_from evm I hca hct hco hft]
    · rw [Function.update_of_ne hat, Function.update_of_ne haf,
        balOf_transferFromPostState_other evm I hca hcf hct a haf hat]

theorem totalSupplyVal_transferFromPostState
    (hca : AllowClean (AccountAddress.ofNat (transferFromFromWord I).toNat)
      evm.executionEnv.source)
    (hcf : BalClean (AccountAddress.ofNat (transferFromFromWord I).toNat))
    (hct : BalClean (AccountAddress.ofNat (transferFromToWord I).toNat)) :
    totalSupplyVal (transferFromPostState evm I) = totalSupplyVal evm := by
  simp only [totalSupplyVal, transferFromPostState, transferFromAfterBalanceState,
    transferFromAfterAllowanceState, storageStore_codeOwner]
  rw [storageLoad_storageStore_ne _ _ _ _ _
        (by simpa [transferFromToSlot] using hct.ne_supply.symm)]
  rw [storageLoad_storageStore_ne _ _ _ _ _
        (by simpa [transferFromFromSlot] using hcf.ne_supply.symm)]
  rw [storageLoad_storageStore_ne _ _ _ _ _
        (by simpa [transferFromAllowanceSlot] using hca.ne_supply.symm)]

/-! ### Self-transfer (`from = to`) -/

theorem transferFromToSlot_eq_of_self
    (hself : AccountAddress.ofNat (transferFromFromWord I).toNat =
      AccountAddress.ofNat (transferFromToWord I).toNat) :
    transferFromToSlot I = transferFromFromSlot I := by
  simp only [transferFromToSlot, transferFromFromSlot, hself]

/-- A self-`transferFrom` credits back exactly what it debited. -/
theorem transferFromNewToNat_of_self
    (hca : AllowClean (AccountAddress.ofNat (transferFromFromWord I).toNat)
      evm.executionEnv.source) {acc : Account}
    (hco : evm.accountMap.get? evm.executionEnv.codeOwner = some acc)
    (hself : AccountAddress.ofNat (transferFromFromWord I).toNat =
      AccountAddress.ofNat (transferFromToWord I).toNat)
    (henough : (transferFromValueWord I).toNat ≤
      balOf evm (AccountAddress.ofNat (transferFromFromWord I).toNat)) :
    transferFromNewToNat evm I = balOf evm (AccountAddress.ofNat (transferFromFromWord I).toNat) := by
  obtain ⟨_, hcoA⟩ := storageStore_find_codeOwner evm evm.executionEnv.codeOwner
    (transferFromAllowanceSlot evm I) (transferFromAllowanceDebitWord evm I) hco
  rw [transferFromNewToNat, transferFromToBalanceWord, transferFromToSlot_eq_of_self I hself,
    transferFromAfterBalanceState,
    storageLoad_storageStore_self (transferFromAfterAllowanceState evm I) evm.executionEnv.codeOwner
      (transferFromFromSlot I) (transferFromBalanceDebitWord (transferFromAfterAllowanceState evm I) I)
      hcoA,
    transferFromBalanceDebitWord_toNat evm I hca]
  omega

/-- **Pointwise balance effect of a self-`transferFrom`**: no balance changes. -/
theorem balOf_transferFromPostState_self
    (hca : AllowClean (AccountAddress.ofNat (transferFromFromWord I).toNat)
      evm.executionEnv.source)
    (hcf : BalClean (AccountAddress.ofNat (transferFromFromWord I).toNat)) {acc : Account}
    (hco : evm.accountMap.get? evm.executionEnv.codeOwner = some acc)
    (hself : AccountAddress.ofNat (transferFromFromWord I).toNat =
      AccountAddress.ofNat (transferFromToWord I).toNat)
    (henough : (transferFromValueWord I).toNat ≤
      balOf evm (AccountAddress.ofNat (transferFromFromWord I).toNat)) :
    balOf (transferFromPostState evm I) = balOf evm := by
  funext a
  by_cases ha : a = AccountAddress.ofNat (transferFromFromWord I).toNat
  · subst ha
    obtain ⟨_, hcoA⟩ := storageStore_find_codeOwner evm evm.executionEnv.codeOwner
      (transferFromAllowanceSlot evm I) (transferFromAllowanceDebitWord evm I) hco
    obtain ⟨_, hcoB⟩ := storageStore_find_codeOwner (transferFromAfterAllowanceState evm I)
      evm.executionEnv.codeOwner (transferFromFromSlot I)
      (transferFromBalanceDebitWord (transferFromAfterAllowanceState evm I) I) hcoA
    have hfit : transferFromNewToNat evm I < UInt256.size := by
      rw [transferFromNewToNat_of_self evm I hca hco hself henough]
      exact Fin.isLt _
    rw [balOf, transferFromPostState_codeOwner, transferFromPostState]
    rw [show erc20BalanceOfSlot
          (KeyValue.address (AccountAddress.ofNat (transferFromFromWord I).toNat))
        = transferFromToSlot I from (transferFromToSlot_eq_of_self I hself).symm]
    rw [storageLoad_storageStore_self (transferFromAfterBalanceState evm I)
          evm.executionEnv.codeOwner (transferFromToSlot I) (transferFromNewToWord evm I) hcoB]
    rw [transferFromNewToWord_toNat evm I hfit,
      transferFromNewToNat_of_self evm I hca hco hself henough]
  · rw [balOf, balOf, transferFromPostState_codeOwner, transferFromPostState,
      transferFromAfterBalanceState, transferFromAfterAllowanceState]
    rw [transferFromToSlot_eq_of_self I hself]
    rw [storageLoad_storageStore_ne _ _ _ _ _
          (by simpa [transferFromFromSlot] using hcf.unshared a ha)]
    rw [storageLoad_storageStore_ne _ _ _ _ _
          (by simpa [transferFromFromSlot] using hcf.unshared a ha)]
    rw [storageLoad_storageStore_ne _ _ _ _ _
          (by simpa [transferFromAllowanceSlot] using
            (hca.ne_balanceOf a).symm)]

/-! ### Missing contract account -/

theorem transferFromPostState_of_missing
    (hmiss : evm.accountMap.get? evm.executionEnv.codeOwner = none) :
    transferFromPostState evm I = evm := by
  simp only [transferFromPostState, transferFromAfterBalanceState, transferFromAfterAllowanceState]
  rw [storageStore_noop_of_missing _ _ _ _ hmiss, storageStore_noop_of_missing _ _ _ _ hmiss,
    storageStore_noop_of_missing _ _ _ _ hmiss]

/-- **`transferFrom` preserves the supply invariant**, for any `from` and `to` (including
    `from = to`), whenever its checks pass. -/
theorem transferFrom_preserves_inv
    (hca : AllowClean (AccountAddress.ofNat (transferFromFromWord I).toNat)
      evm.executionEnv.source)
    (hcf : BalClean (AccountAddress.ofNat (transferFromFromWord I).toNat))
    (hct : BalClean (AccountAddress.ofNat (transferFromToWord I).toNat))
    (henough : (transferFromValueWord I).toNat ≤
      balOf evm (AccountAddress.ofNat (transferFromFromWord I).toNat))
    (hfit : transferFromNewToNat evm I < UInt256.size)
    (hInv : Inv evm) : Inv (transferFromPostState evm I) := by
  rcases hacc : evm.accountMap.get? evm.executionEnv.codeOwner with _ | acc
  · rw [transferFromPostState_of_missing evm I hacc]; exact hInv
  · unfold Inv totalBalances at *
    rw [totalSupplyVal_transferFromPostState evm I hca hcf hct, hInv]
    by_cases hself : AccountAddress.ofNat (transferFromFromWord I).toNat =
        AccountAddress.ofNat (transferFromToWord I).toNat
    · rw [balOf_transferFromPostState_self evm I hca hcf hacc hself henough]
    · rw [balOf_transferFromPostState evm I hca hcf hct hacc hself hfit]
      exact (sum_transfer_eq (balOf evm) hself (transferFromValueWord I).toNat henough).symm

end TransferFrom

/-! ## The constructor establishes the invariant (base case)

`constructor(initialSupply)` mints `initialSupply` to the deployer and sets `totalSupply`
(`erc20CtorPostState`, from `Examples/ERC20/Correct`).  From a fresh deploy state (all balances
zero) the result satisfies `Inv`: the only non-zero balance is the deployer's, equal to
`totalSupply`. -/

section Constructor

variable (evm : EVM.State)

/-- A single mint to `x` of a state with otherwise-zero balances sums to that mint. -/
theorem totalBalances_update_zero {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℕ) (x : α)
    (v : ℕ) (hz : ∀ a, a ≠ x → f a = 0) :
    (∑ a, Function.update f x v a) = v := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ x),
    Finset.sum_eq_zero (fun a ha => hz a (by simpa using (Finset.mem_sdiff.mp ha).2)), Nat.add_zero]

theorem erc20CtorPostState_executionEnv (s : UInt256) :
    (erc20CtorPostState evm s).executionEnv = evm.executionEnv := by
  simp only [erc20CtorPostState, erc20CtorBalancePostState, storageStore_codeOwner]

theorem balOf_erc20CtorPostState (s : UInt256) (hsup : SupplyClean)
    (hcd : BalClean evm.executionEnv.source)
    {acc : Account} (hco : evm.accountMap.get? evm.executionEnv.codeOwner = some acc) :
    balOf (erc20CtorPostState evm s) =
      Function.update (balOf evm) evm.executionEnv.source s.toNat := by
  funext a
  by_cases ha : a = evm.executionEnv.source
  · subst ha
    rw [balOf]
    simp only [erc20CtorPostState, erc20CtorBalancePostState, storageStore_codeOwner]
    rw [storageLoad_storageStore_ne _ _ _ _ _ hcd.ne_supply]
    rw [storageLoad_storageStore_self _ _ _ _ hco, Function.update_self]
  · rw [Function.update_of_ne ha, balOf, balOf]
    simp only [erc20CtorPostState, erc20CtorBalancePostState, storageStore_codeOwner]
    rw [storageLoad_storageStore_ne _ _ _ _ _ (hsup a)]
    rw [storageLoad_storageStore_ne _ _ _ _ _ (hcd.unshared a ha)]

theorem totalSupplyVal_erc20CtorPostState (s : UInt256)
    {acc : Account} (hco : evm.accountMap.get? evm.executionEnv.codeOwner = some acc) :
    totalSupplyVal (erc20CtorPostState evm s) = s.toNat := by
  obtain ⟨_, h2⟩ := storageStore_find_codeOwner evm evm.executionEnv.codeOwner
    (erc20BalanceOfSlot (.address evm.executionEnv.source)) s hco
  simp only [totalSupplyVal, erc20CtorPostState, erc20CtorBalancePostState, storageStore_codeOwner]
  rw [storageLoad_storageStore_self _ _ _ _ h2]

theorem erc20CtorPostState_of_missing (s : UInt256)
    (hmiss : evm.accountMap.get? evm.executionEnv.codeOwner = none) :
    erc20CtorPostState evm s = evm := by
  simp only [erc20CtorPostState, erc20CtorBalancePostState]
  rw [storageStore_noop_of_missing _ _ _ _ hmiss]
  exact storageStore_noop_of_missing _ _ _ _ hmiss

/-- **The constructor establishes `Inv`** from a fresh (all-balances-zero) deploy state. -/
theorem constructor_establishes_inv (s : UInt256) (hsup : SupplyClean)
    (hcd : BalClean evm.executionEnv.source)
    (hzero : ∀ a, balOf evm a = 0) : Inv (erc20CtorPostState evm s) := by
  rcases hacc : evm.accountMap.get? evm.executionEnv.codeOwner with _ | acc
  · rw [erc20CtorPostState_of_missing evm s hacc]
    unfold Inv totalBalances
    rw [totalSupplyVal_of_missing evm hacc]
    exact (Finset.sum_eq_zero (fun a _ => hzero a)).symm
  · unfold Inv totalBalances
    rw [totalSupplyVal_erc20CtorPostState evm s hacc,
      balOf_erc20CtorPostState evm s hsup hcd hacc,
      totalBalances_update_zero (balOf evm) evm.executionEnv.source s.toNat (fun a _ => hzero a)]

end Constructor

end ERC20
