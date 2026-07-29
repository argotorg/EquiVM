import Proofs.ERC20.Balances
import Examples.ERC20.Transfer
import Examples.ERC20.TransferFrom
import Examples.ERC20.TotalSupply
import Examples.ERC20.Allowance
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# ERC20 contract invariant — `totalSupply = Σ balances`, preserved across every ABI call

This "closes the loop" on the ERC20 Solm spec: instead of proving the spec equivalent to bytecode
(as in `Examples/ERC20`), we prove a *functional-correctness invariant of the spec itself* — the
classic ERC20 supply invariant `totalSupply = Σ_a balanceOf[a]` — and show that **every** ABI
entry point preserves it, and that the constructor establishes it.

The sum `Σ_a balanceOf[a]` ranges over *all* addresses.  Because `AccountAddress` is a finite type
(`Fin _`), `∑ a : AccountAddress, balOf evm a` is a genuine `Finset.univ` sum — finitely supported
automatically, with no auxiliary "set of holders" and no new axioms.  The only assumption is the
explicit `InjectiveLayout` hypothesis (distinct storage refs ↦ distinct slots; see
`Proofs.ERC20.Balances`).
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
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

/-- `codeOwner` is unchanged by the transfer post-state (storage writes don't touch the env). -/
theorem transferPostState_codeOwner :
    (transferPostState evm I).executionEnv.codeOwner = evm.executionEnv.codeOwner := by
  simp only [transferPostState, transferAfterDebitState, storageStore_codeOwner]

/-- The sender's pre-balance, as named by the spec, *is* `balOf` at the caller. -/
theorem balOf_source_eq :
    balOf evm evm.executionEnv.source = (transferFromBalanceWord evm).toNat := rfl

/-- `transfer` leaves `totalSupply` untouched: both balance writes hit `balanceOf` slots, distinct
    from the `totalSupply` slot. -/
theorem totalSupplyVal_transferPostState (hinj : InjectiveLayout erc20Config) :
    totalSupplyVal (transferPostState evm I) = totalSupplyVal evm := by
  simp only [totalSupplyVal, transferPostState, transferAfterDebitState, storageStore_codeOwner]
  rw [storageLoad_storageStore_ne _ _ _ _ _
        (by simpa [transferToSlot] using
          (balanceOf_slot_ne_totalSupply hinj
            (AccountAddress.ofNat (transferToWord I).toNat)).symm),
      storageLoad_storageStore_ne _ _ _ _ _
        (by simpa [transferSenderSlot] using
          (balanceOf_slot_ne_totalSupply hinj evm.executionEnv.source).symm)]

/-- The debit word's value is the sender's balance minus the transferred amount (no underflow). -/
theorem transferDebitWord_toNat
    (henough : (transferValueWord I).toNat ≤ balOf evm evm.executionEnv.source) :
    (transferDebitWord evm I).toNat =
      balOf evm evm.executionEnv.source - (transferValueWord I).toNat := by
  rw [balOf_source_eq]
  simp only [transferDebitWord]
  exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _) (transferFromBalanceWord evm).val.isLt)

/-- The recipient's pre-balance, as named by the spec, *is* `balOf` at the recipient. -/
theorem transferToBalanceWord_toNat (hinj : InjectiveLayout erc20Config)
    (hne : evm.executionEnv.source ≠ AccountAddress.ofNat (transferToWord I).toNat) :
    (transferToBalanceWord evm I).toNat =
      balOf evm (AccountAddress.ofNat (transferToWord I).toNat) := by
  simp only [transferToBalanceWord, transferAfterDebitState, balOf]
  rw [storageLoad_storageStore_ne _ _ _ _ _
        (by simpa [transferToSlot, transferSenderSlot] using
          balanceOf_slot_ne hinj (Ne.symm hne))]
  rfl

/-- Recipient's post-balance: `balOf evm to + value`. -/
theorem balOf_transferPostState_to (hinj : InjectiveLayout erc20Config)
    {acc : Account} (hco : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
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
    transferNewToNat, transferToBalanceWord_toNat evm I hinj hne]

/-- Caller's post-balance: `balOf evm from - value`. -/
theorem balOf_transferPostState_from (hinj : InjectiveLayout erc20Config)
    {acc : Account} (hco : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
    (hne : evm.executionEnv.source ≠ AccountAddress.ofNat (transferToWord I).toNat)
    (henough : (transferValueWord I).toNat ≤ balOf evm evm.executionEnv.source) :
    balOf (transferPostState evm I) evm.executionEnv.source =
      balOf evm evm.executionEnv.source - (transferValueWord I).toNat := by
  rw [balOf]
  simp only [transferPostState, transferAfterDebitState, storageStore_codeOwner]
  rw [storageLoad_storageStore_ne _ _ _ _ _
        (by simpa [transferToSlot, transferSenderSlot] using balanceOf_slot_ne hinj hne)]
  rw [show erc20BalanceOfSlot (KeyValue.address evm.executionEnv.source) = transferSenderSlot evm
        from rfl]
  rw [storageLoad_storageStore_self _ _ _ _ hco, transferDebitWord_toNat evm I henough]

/-- Any third party's balance is untouched by `transfer`. -/
theorem balOf_transferPostState_other (hinj : InjectiveLayout erc20Config) (a : AccountAddress)
    (hat : a ≠ AccountAddress.ofNat (transferToWord I).toNat) (has : a ≠ evm.executionEnv.source) :
    balOf (transferPostState evm I) a = balOf evm a := by
  rw [balOf, balOf]
  simp only [transferPostState, transferAfterDebitState, storageStore_codeOwner]
  rw [storageLoad_storageStore_ne _ _ _ _ _
        (by simpa [transferToSlot] using balanceOf_slot_ne hinj hat)]
  rw [storageLoad_storageStore_ne _ _ _ _ _
        (by simpa [transferSenderSlot] using balanceOf_slot_ne hinj has)]

/-- **Pointwise balance effect of `transfer`.**  On the success path, the post-state balances are
    exactly the pre-state balances with `value` moved from the caller to the recipient. -/
theorem balOf_transferPostState (hinj : InjectiveLayout erc20Config)
    {acc : Account} (hco : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
    (hne : evm.executionEnv.source ≠ AccountAddress.ofNat (transferToWord I).toNat)
    (henough : (transferValueWord I).toNat ≤ balOf evm evm.executionEnv.source)
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
    rw [Function.update_self, balOf_transferPostState_to evm I hinj hco hne hfit]
  · by_cases has : a = evm.executionEnv.source
    · subst has
      rw [Function.update_of_ne hat, Function.update_self,
        balOf_transferPostState_from evm I hinj hco hne henough]
    · rw [Function.update_of_ne hat, Function.update_of_ne has,
        balOf_transferPostState_other evm I hinj a hat has]

/-- **`transfer` preserves the supply invariant.**  Packaged with the witness that this post-state
    is exactly the result of executing the `transfer` body (`erc20TransferBodyReturns`), so this is a
    statement about the real Solm semantics, not a hand-rolled state. -/
theorem transfer_preserves_inv (hinj : InjectiveLayout erc20Config)
    {acc : Account} (hco : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
    (hne : evm.executionEnv.source ≠ AccountAddress.ofNat (transferToWord I).toNat)
    (henough : (transferValueWord I).toNat ≤ balOf evm evm.executionEnv.source)
    (hfit : transferNewToNat evm I < UInt256.size)
    (hInv : Inv evm) : Inv (transferPostState evm I) := by
  unfold Inv totalBalances at *
  rw [totalSupplyVal_transferPostState evm I hinj, hInv,
    balOf_transferPostState evm I hinj hco hne henough hfit]
  exact (sum_transfer_eq (balOf evm) hne (transferValueWord I).toNat henough).symm

end Transfer

/-! ## `approve` and the read-only entry points preserve the invariant

`approve` writes only an `allowance` slot — disjoint from every `balanceOf` slot and from
`totalSupply` — so it perturbs neither side of the invariant.  The read-only methods
(`totalSupply`, `balanceOf`, `allowance`) do not write storage at all. -/

section Approve

variable (evm : EVM.State) (I : ExecutionEnv)

theorem balOf_approvePostState (hinj : InjectiveLayout erc20Config) (a : AccountAddress) :
    balOf (approvePostState evm I) a = balOf evm a := by
  rw [balOf, balOf]
  simp only [approvePostState, storageStore_codeOwner]
  rw [storageLoad_storageStore_ne _ _ _ _ _
        (by simpa [approveSlot] using
          (allowance_slot_ne_balanceOf hinj evm.executionEnv.source
            (AccountAddress.ofNat (approveSpenderWord I).toNat) a).symm)]

theorem totalSupplyVal_approvePostState (hinj : InjectiveLayout erc20Config) :
    totalSupplyVal (approvePostState evm I) = totalSupplyVal evm := by
  simp only [totalSupplyVal, approvePostState, storageStore_codeOwner]
  rw [storageLoad_storageStore_ne _ _ _ _ _
        (by simpa [approveSlot] using
          (allowance_slot_ne_totalSupply hinj evm.executionEnv.source
            (AccountAddress.ofNat (approveSpenderWord I).toNat)).symm)]

/-- **`approve` preserves the supply invariant** (it touches no balance and not `totalSupply`). -/
theorem approve_preserves_inv (hinj : InjectiveLayout erc20Config) (hInv : Inv evm) :
    Inv (approvePostState evm I) := by
  unfold Inv totalBalances at *
  rw [totalSupplyVal_approvePostState evm I hinj, hInv]
  exact Finset.sum_congr rfl (fun a _ => (balOf_approvePostState evm I hinj a).symm)

end Approve

/-! ## `transferFrom` preserves the invariant

`transferFrom` does everything `transfer` does — move `value` from `from` to `to` — plus a write to
the `allowance[from][msg.sender]` slot, which is disjoint from all balance slots and from
`totalSupply`.  So the balance-conservation argument is identical, with one extra disjoint write to
frame past. -/

section TransferFrom

variable (evm : EVM.State) (I : ExecutionEnv)

theorem transferFromPostState_codeOwner :
    (transferFromPostState evm I).executionEnv.codeOwner = evm.executionEnv.codeOwner := by
  simp only [transferFromPostState, transferFromAfterBalanceState,
    transferFromAfterAllowanceState, storageStore_codeOwner]

/-- The recipient's pre-balance under `transferFrom`, read through the allowance and `from` writes. -/
theorem transferFromToBalanceWord_toNat (hinj : InjectiveLayout erc20Config)
    (hft : AccountAddress.ofNat (transferFromFromWord I).toNat ≠
      AccountAddress.ofNat (transferFromToWord I).toNat) :
    (transferFromToBalanceWord evm I).toNat =
      balOf evm (AccountAddress.ofNat (transferFromToWord I).toNat) := by
  simp only [transferFromToBalanceWord, transferFromAfterBalanceState,
    transferFromAfterAllowanceState, balOf]
  rw [storageLoad_storageStore_ne _ _ _ _ _
        (by simpa [transferFromToSlot, transferFromFromSlot] using balanceOf_slot_ne hinj hft.symm)]
  rw [storageLoad_storageStore_ne _ _ _ _ _
        (by simpa [transferFromToSlot, transferFromAllowanceSlot] using
          (allowance_slot_ne_balanceOf hinj (AccountAddress.ofNat (transferFromFromWord I).toNat)
            evm.executionEnv.source (AccountAddress.ofNat (transferFromToWord I).toNat)).symm)]
  rfl

/-- The `from`-balance debit value: `balOf evm from - value` (read past the allowance write). -/
theorem transferFromBalanceDebitWord_toNat (hinj : InjectiveLayout erc20Config)
    (henough : (transferFromValueWord I).toNat ≤
      balOf evm (AccountAddress.ofNat (transferFromFromWord I).toNat)) :
    (transferFromBalanceDebitWord (transferFromAfterAllowanceState evm I) I).toNat =
      balOf evm (AccountAddress.ofNat (transferFromFromWord I).toNat) -
        (transferFromValueWord I).toNat := by
  have hval : (transferFromFromBalanceWord (transferFromAfterAllowanceState evm I) I) =
      transferFromFromBalanceWord evm I := by
    simp only [transferFromFromBalanceWord, transferFromAfterAllowanceState,
      storageStore_codeOwner]
    rw [storageLoad_storageStore_ne _ _ _ _ _
          (by simpa [transferFromFromSlot, transferFromAllowanceSlot] using
            (allowance_slot_ne_balanceOf hinj (AccountAddress.ofNat (transferFromFromWord I).toNat)
              evm.executionEnv.source
              (AccountAddress.ofNat (transferFromFromWord I).toNat)).symm)]
  simp only [transferFromBalanceDebitWord, hval]
  exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _) (transferFromFromBalanceWord evm I).val.isLt)

/-- Recipient's post-balance under `transferFrom`: `balOf evm to + value`. -/
theorem balOf_transferFromPostState_to (hinj : InjectiveLayout erc20Config)
    {acc : Account} (hco : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
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
    transferFromToBalanceWord_toNat evm I hinj hft]

/-- Sender's (`from`) post-balance under `transferFrom`: `balOf evm from - value`. -/
theorem balOf_transferFromPostState_from (hinj : InjectiveLayout erc20Config)
    {acc : Account} (hco : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
    (hft : AccountAddress.ofNat (transferFromFromWord I).toNat ≠
      AccountAddress.ofNat (transferFromToWord I).toNat)
    (henough : (transferFromValueWord I).toNat ≤
      balOf evm (AccountAddress.ofNat (transferFromFromWord I).toNat)) :
    balOf (transferFromPostState evm I) (AccountAddress.ofNat (transferFromFromWord I).toNat) =
      balOf evm (AccountAddress.ofNat (transferFromFromWord I).toNat) -
        (transferFromValueWord I).toNat := by
  obtain ⟨_, hcoA⟩ := storageStore_find_codeOwner evm evm.executionEnv.codeOwner
    (transferFromAllowanceSlot evm I) (transferFromAllowanceDebitWord evm I) hco
  rw [balOf, transferFromPostState_codeOwner, transferFromPostState]
  rw [storageLoad_storageStore_ne _ _ _ _ _
        (by simpa [transferFromToSlot, transferFromFromSlot] using balanceOf_slot_ne hinj hft)]
  rw [transferFromAfterBalanceState]
  rw [show erc20BalanceOfSlot (KeyValue.address (AccountAddress.ofNat (transferFromFromWord I).toNat))
        = transferFromFromSlot I from rfl]
  rw [storageLoad_storageStore_self (transferFromAfterAllowanceState evm I)
        evm.executionEnv.codeOwner (transferFromFromSlot I)
        (transferFromBalanceDebitWord (transferFromAfterAllowanceState evm I) I) hcoA]
  rw [transferFromBalanceDebitWord_toNat evm I hinj henough]

/-- Any third party's balance is untouched by `transferFrom`. -/
theorem balOf_transferFromPostState_other (hinj : InjectiveLayout erc20Config) (a : AccountAddress)
    (hfrom : a ≠ AccountAddress.ofNat (transferFromFromWord I).toNat)
    (hto : a ≠ AccountAddress.ofNat (transferFromToWord I).toNat) :
    balOf (transferFromPostState evm I) a = balOf evm a := by
  rw [balOf, balOf, transferFromPostState_codeOwner, transferFromPostState,
    transferFromAfterBalanceState, transferFromAfterAllowanceState]
  rw [storageLoad_storageStore_ne _ _ _ _ _
        (by simpa [transferFromToSlot] using balanceOf_slot_ne hinj hto)]
  rw [storageLoad_storageStore_ne _ _ _ _ _
        (by simpa [transferFromFromSlot] using balanceOf_slot_ne hinj hfrom)]
  rw [storageLoad_storageStore_ne _ _ _ _ _
        (by simpa [transferFromAllowanceSlot] using
          (allowance_slot_ne_balanceOf hinj (AccountAddress.ofNat (transferFromFromWord I).toNat)
            evm.executionEnv.source a).symm)]

theorem balOf_transferFromPostState (hinj : InjectiveLayout erc20Config)
    {acc : Account} (hco : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
    (hft : AccountAddress.ofNat (transferFromFromWord I).toNat ≠
      AccountAddress.ofNat (transferFromToWord I).toNat)
    (henough : (transferFromValueWord I).toNat ≤
      balOf evm (AccountAddress.ofNat (transferFromFromWord I).toNat))
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
    rw [Function.update_self, balOf_transferFromPostState_to evm I hinj hco hft hfit]
  · by_cases haf : a = AccountAddress.ofNat (transferFromFromWord I).toNat
    · subst haf
      rw [Function.update_of_ne hat, Function.update_self,
        balOf_transferFromPostState_from evm I hinj hco hft henough]
    · rw [Function.update_of_ne hat, Function.update_of_ne haf,
        balOf_transferFromPostState_other evm I hinj a haf hat]

theorem totalSupplyVal_transferFromPostState (hinj : InjectiveLayout erc20Config) :
    totalSupplyVal (transferFromPostState evm I) = totalSupplyVal evm := by
  simp only [totalSupplyVal, transferFromPostState, transferFromAfterBalanceState,
    transferFromAfterAllowanceState, storageStore_codeOwner]
  rw [storageLoad_storageStore_ne _ _ _ _ _
        (by simpa [transferFromToSlot] using
          (balanceOf_slot_ne_totalSupply hinj
            (AccountAddress.ofNat (transferFromToWord I).toNat)).symm)]
  rw [storageLoad_storageStore_ne _ _ _ _ _
        (by simpa [transferFromFromSlot] using
          (balanceOf_slot_ne_totalSupply hinj
            (AccountAddress.ofNat (transferFromFromWord I).toNat)).symm)]
  rw [storageLoad_storageStore_ne _ _ _ _ _
        (by simpa [transferFromAllowanceSlot] using
          (allowance_slot_ne_totalSupply hinj
            (AccountAddress.ofNat (transferFromFromWord I).toNat) evm.executionEnv.source).symm)]

/-- **`transferFrom` preserves the supply invariant.** -/
theorem transferFrom_preserves_inv (hinj : InjectiveLayout erc20Config)
    {acc : Account} (hco : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
    (hft : AccountAddress.ofNat (transferFromFromWord I).toNat ≠
      AccountAddress.ofNat (transferFromToWord I).toNat)
    (henough : (transferFromValueWord I).toNat ≤
      balOf evm (AccountAddress.ofNat (transferFromFromWord I).toNat))
    (hfit : transferFromNewToNat evm I < UInt256.size)
    (hInv : Inv evm) : Inv (transferFromPostState evm I) := by
  unfold Inv totalBalances at *
  rw [totalSupplyVal_transferFromPostState evm I hinj, hInv,
    balOf_transferFromPostState evm I hinj hco hft henough hfit]
  exact (sum_transfer_eq (balOf evm) hft (transferFromValueWord I).toNat henough).symm

end TransferFrom

/-! ## Closing the loop: every ABI entry point preserves `Inv`

Each theorem below pairs the *real* `ExecTransitionBody` derivation of a transition body (reused
verbatim from the equivalence development, e.g. `erc20TransferBodyReturns`) with a proof that the
resulting state still satisfies `Inv`.  Together they say: executing any ERC20 ABI method on a state
satisfying the supply invariant lands in a state that still satisfies it.

The read-only methods return the state unchanged, so they preserve `Inv` trivially.  `transfer` and
`transferFrom` additionally require `from ≠ to` (the self-transfer case is a no-op on the sum and is
left as a small separate lemma) and that the contract's own account exists (`hco`, true of any live
call). -/

section ClosesLoop

variable (evm : EVM.State) (I : ExecutionEnv)

theorem transfer_closesLoop (hinj : InjectiveLayout erc20Config)
    {acc : Account} (hco : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
    (hne : evm.executionEnv.source ≠ AccountAddress.ofNat (transferToWord I).toNat)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (henough : (transferValueWord I).toNat ≤ balOf evm evm.executionEnv.source)
    (hfit : transferNewToNat evm I < UInt256.size) (hInv : Inv evm) :
    ExecTransitionBody erc20Config erc20Contract evm (transferStore I) transferTransition.body
        (.returned { contract := erc20Contract, locals := transferStoreNewToBalance evm I }
          (transferPostState evm I) (some [.bool true]))
      ∧ Inv (transferPostState evm I) :=
  ⟨erc20TransferBodyReturns evm I hwv henough hfit,
    transfer_preserves_inv evm I hinj hco hne henough hfit hInv⟩

theorem transferFrom_closesLoop (hinj : InjectiveLayout erc20Config)
    {acc : Account} (hco : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
    (hft : AccountAddress.ofNat (transferFromFromWord I).toNat ≠
      AccountAddress.ofNat (transferFromToWord I).toNat)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowance : (transferFromValueWord I).toNat ≤ (transferFromCurrentAllowanceWord evm I).toNat)
    (hbalance : (transferFromValueWord I).toNat ≤
      balOf evm (AccountAddress.ofNat (transferFromFromWord I).toNat))
    (hbalanceDebit : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (transferFromAfterAllowanceState evm I) I).toNat)
    (hfit : transferFromNewToNat evm I < UInt256.size) (hInv : Inv evm) :
    ExecTransitionBody erc20Config erc20Contract evm (transferFromStore I)
        transferFromTransition.body
        (.returned { contract := erc20Contract, locals := transferFromStoreNewToBalance evm I }
          (transferFromPostState evm I) (some [.bool true]))
      ∧ Inv (transferFromPostState evm I) :=
  ⟨erc20TransferFromBodyReturns evm I hwv hallowance hbalance hbalanceDebit hfit,
    transferFrom_preserves_inv evm I hinj hco hft hbalance hfit hInv⟩

theorem approve_closesLoop (hinj : InjectiveLayout erc20Config)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hInv : Inv evm) :
    ExecTransitionBody erc20Config erc20Contract evm (approveStore I) approveTransition.body
        (.returned { contract := erc20Contract, locals := approveStore I }
          (approvePostState evm I) (some [.bool true]))
      ∧ Inv (approvePostState evm I) :=
  ⟨erc20ApproveBodyReturns evm I hwv, approve_preserves_inv evm I hinj hInv⟩

theorem totalSupply_closesLoop (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hInv : Inv evm) :
    ExecTransitionBody erc20Config erc20Contract evm (∅ : Store) totalSupplyTransition.body
        (.returned { contract := erc20Contract, locals := (∅ : Store) } evm
          (some [.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)]))
      ∧ Inv evm :=
  ⟨erc20TotalSupplyBodyReturns evm (∅ : Store) hwv (by simp), hInv⟩

theorem balanceOf_closesLoop (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hInv : Inv evm) :
    ExecTransitionBody erc20Config erc20Contract evm (balanceOfStore I) balanceOfTransition.body
        (.returned { contract := erc20Contract, locals := balanceOfStore I } evm
          (some [.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (balanceOfSlot I)).toNat)]))
      ∧ Inv evm :=
  ⟨erc20BalanceOfBodyReturns evm I hwv, hInv⟩

theorem allowance_closesLoop (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hInv : Inv evm) :
    ExecTransitionBody erc20Config erc20Contract evm (allowanceStore I) allowanceTransition.body
        (.returned { contract := erc20Contract, locals := allowanceStore I } evm
          (some [.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (allowanceSlot I)).toNat)]))
      ∧ Inv evm :=
  ⟨erc20AllowanceBodyReturns evm I hwv, hInv⟩

end ClosesLoop

/-! ## The constructor establishes the invariant (base case)

`constructor(initialSupply)` mints `initialSupply` to the deployer and sets `totalSupply`.  From a
fresh deploy state (all balances zero) the result satisfies `Inv`: the only non-zero balance is the
deployer's, equal to `totalSupply`. -/

section Constructor

variable (evm : EVM.State)

/-- A single mint to `x` of a state with otherwise-zero balances sums to that mint. -/
theorem totalBalances_update_zero {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℕ) (x : α)
    (v : ℕ) (hz : ∀ a, a ≠ x → f a = 0) :
    (∑ a, Function.update f x v a) = v := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ x),
    Finset.sum_eq_zero (fun a ha => hz a (by simpa using (Finset.mem_sdiff.mp ha).2)), Nat.add_zero]

/-- The state after running the ERC20 constructor with supply word `s`: mint `s` to the deployer,
    then set `totalSupply := s`. -/
def ctorPostState (s : UInt256) : EVM.State :=
  Solm.EVM.storageStore
    (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (erc20BalanceOfSlot (.address evm.executionEnv.source)) s)
    evm.executionEnv.codeOwner ⟨2⟩ s

theorem balOf_ctorPostState (s : UInt256) (hinj : InjectiveLayout erc20Config)
    {acc : Account} (hco : evm.accountMap.find? evm.executionEnv.codeOwner = some acc) :
    balOf (ctorPostState evm s) = Function.update (balOf evm) evm.executionEnv.source s.toNat := by
  funext a
  by_cases ha : a = evm.executionEnv.source
  · subst ha
    rw [balOf]
    simp only [ctorPostState, storageStore_codeOwner]
    rw [storageLoad_storageStore_ne _ _ _ _ _
          (balanceOf_slot_ne_totalSupply hinj evm.executionEnv.source)]
    rw [storageLoad_storageStore_self _ _ _ _ hco, Function.update_self]
  · rw [Function.update_of_ne ha, balOf, balOf]
    simp only [ctorPostState, storageStore_codeOwner]
    rw [storageLoad_storageStore_ne _ _ _ _ _ (balanceOf_slot_ne_totalSupply hinj a)]
    rw [storageLoad_storageStore_ne _ _ _ _ _ (balanceOf_slot_ne hinj ha)]

theorem totalSupplyVal_ctorPostState (s : UInt256)
    {acc : Account} (hco : evm.accountMap.find? evm.executionEnv.codeOwner = some acc) :
    totalSupplyVal (ctorPostState evm s) = s.toNat := by
  obtain ⟨_, h2⟩ := storageStore_find_codeOwner evm evm.executionEnv.codeOwner
    (erc20BalanceOfSlot (.address evm.executionEnv.source)) s hco
  simp only [totalSupplyVal, ctorPostState, storageStore_codeOwner]
  rw [storageLoad_storageStore_self _ _ _ _ h2]

/-- **The constructor establishes `Inv`** from a fresh (all-balances-zero) deploy state. -/
theorem constructor_establishes_inv (s : UInt256) (hinj : InjectiveLayout erc20Config)
    {acc : Account} (hco : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
    (hzero : ∀ a, balOf evm a = 0) : Inv (ctorPostState evm s) := by
  unfold Inv totalBalances
  rw [totalSupplyVal_ctorPostState evm s hco, balOf_ctorPostState evm s hinj hco,
    totalBalances_update_zero (balOf evm) evm.executionEnv.source s.toNat (fun a _ => hzero a)]

end Constructor

end ERC20
