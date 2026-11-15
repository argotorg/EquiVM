import Examples.ERC20.Spec
import Reasoning.Storage

/-!
# ERC20 invariant — balance / totalSupply readers, storage frame, slot assumptions

This is the foundation for the *spec-level* ERC20 contract invariant
`totalSupply = Σ balances` (see `Proofs.ERC20.Invariant`).  Unlike the equivalence proofs in
`Examples/ERC20`, nothing here talks about bytecode: we reason purely about the trusted Stele
spec's effect on EVM storage.

It provides:

* `balOf evm a` / `totalSupplyVal evm` — the contract's own-account storage read of `balanceOf[a]`
  and `totalSupply`, as `ℕ`.
* Raw load-after-store frame lemmas for `Stele.EVM.storageStore` (same slot / different slot).
* `BalClean a`, `AllowClean o s`, `SupplyClean` — the slot assumptions.  Keccak collision-freedom
  is not axiomatized; instead each invariant theorem assumes that the slots its call writes are not
  shared with another balance or with `totalSupply`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace ERC20

/-! ## Balance / totalSupply readers -/

/-- `balanceOf[a]` read from the contract's own account, as a `ℕ`. -/
def balOf (evm : EVM.State) (a : AccountAddress) : ℕ :=
  (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
    (erc20BalanceOfSlot (.address a))).toNat

/-- `totalSupply` (storage slot `2`) read from the contract's own account, as a `ℕ`. -/
def totalSupplyVal (evm : EVM.State) : ℕ :=
  (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat

/-! ## Raw `storageStore` frame lemmas

These characterise reading one slot after writing another, directly on the raw
`Stele.EVM.storageStore`/`storageLoad` pair (the form the ERC20 post-states are built from).  They
hold unconditionally for the *different-slot* case; the *same-slot* read-back needs the account to
exist (a `storageStore` to a missing account is a no-op). -/

/-- `storageStore` preserves the execution environment, hence the `codeOwner`. -/
@[simp] theorem storageStore_codeOwner (evm : EVM.State) (a : AccountAddress) (k v : UInt256) :
    (Stele.EVM.storageStore evm a k v).executionEnv = evm.executionEnv := by
  exact Reasoning.Theory.storageStore_executionEnv evm a k v

/-- Reading a *different* slot is unaffected by a store. -/
theorem storageLoad_storageStore_ne (evm : EVM.State) (a : AccountAddress)
    (rs ws v : UInt256) (h : rs ≠ ws) :
    Stele.EVM.storageLoad (Stele.EVM.storageStore evm a ws v) a rs =
      Stele.EVM.storageLoad evm a rs := by
  exact Reasoning.Theory.storageLoad_storageStore_ne evm a h

/-- Reading the *same* slot after a store returns the stored value (account must exist). -/
theorem storageLoad_storageStore_self (evm : EVM.State) (a : AccountAddress)
    (ws v : UInt256) {acc : Account} (hex : evm.accountMap.get? a = some acc) :
    Stele.EVM.storageLoad (Stele.EVM.storageStore evm a ws v) a ws = v := by
  exact Reasoning.Theory.storageLoad_storageStore_same_present evm a hex ws v

/-- A store to a *missing* account is a no-op. -/
theorem storageStore_noop_of_missing (evm : EVM.State) (a : AccountAddress) (k v : UInt256)
    (hmiss : evm.accountMap.get? a = none) :
    Stele.EVM.storageStore evm a k v = evm := by
  exact Reasoning.Theory.storageStore_absent evm a hmiss k v

/-- `storageStore` to an *existing* account leaves it existing (used to thread read-backs through
    several writes). -/
theorem storageStore_find_codeOwner (evm : EVM.State) (a : AccountAddress) (k v : UInt256)
    {acc : Account} (hex : evm.accountMap.get? a = some acc) :
    ∃ acc', (Stele.EVM.storageStore evm a k v).accountMap.get? a = some acc' := by
  refine ⟨acc.updateStorage k v, ?_⟩
  simp only [Stele.EVM.storageStore, State.lookupAccount, State.setAccount, hex, Option.option]
  simp [Std.ExtTreeMap.get?_eq_getElem?]

/-! ## Slot assumptions

The invariant reads the `totalSupply` slot (`2`) and the `balanceOf` slot of every address.  A call
can only break it through the slots it writes, so each call assumes only that those slots are not
shared.  No global injectivity is assumed: over all keys it is false (`allowance` alone has `2^320`
address pairs and only `2^256` slots). -/

/-- `balanceOf[a]`'s slot is used by `a` alone and is not the `totalSupply` slot. -/
structure BalClean (a : AccountAddress) : Prop where
  ne_supply : erc20BalanceOfSlot (.address a) ≠ (⟨2⟩ : UInt256)
  unshared : ∀ b : AccountAddress, b ≠ a →
    erc20BalanceOfSlot (.address b) ≠ erc20BalanceOfSlot (.address a)

/-- `allowance[o][s]`'s slot is neither the `totalSupply` slot nor any `balanceOf` slot. -/
structure AllowClean (o s : AccountAddress) : Prop where
  ne_supply : erc20AllowanceSlot (.address o) (.address s) ≠ (⟨2⟩ : UInt256)
  ne_balanceOf : ∀ a : AccountAddress,
    erc20AllowanceSlot (.address o) (.address s) ≠ erc20BalanceOfSlot (.address a)

/-- No `balanceOf` slot is the `totalSupply` slot.  The one global assumption; only the
    constructor needs it. -/
def SupplyClean : Prop :=
  ∀ a : AccountAddress, erc20BalanceOfSlot (.address a) ≠ (⟨2⟩ : UInt256)

end ERC20
