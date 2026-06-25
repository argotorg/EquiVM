import Examples.ERC20.Spec
import Reasoning.Storage

/-!
# ERC20 invariant — balance / totalSupply readers, storage frame, layout injectivity

This is the foundation for the *spec-level* ERC20 contract invariant
`totalSupply = Σ balances` (see `Proofs.ERC20.Invariant`).  Unlike the equivalence proofs in
`Examples/ERC20`, nothing here talks about bytecode: we reason purely about the trusted Solm
spec's effect on EVM storage.

It provides:

* `balOf evm a` / `totalSupplyVal evm` — the contract's own-account storage read of `balanceOf[a]`
  and `totalSupply`, as `ℕ`.
* Raw load-after-store frame lemmas for `Solm.EVM.storageStore` (same slot / different slot).
* `InjectiveLayout cfg` — the *explicit* hypothesis that the storage layout maps distinct storage
  references to distinct slots.  This is the one assumption a `Σ balances` argument cannot avoid
  (distinct mapping keys must land in distinct slots); for Solidity's layout it is discharged by
  Keccak collision-freedom, which this repo deliberately does **not** axiomatize.  Keeping it a
  named hypothesis on the theorems makes the dependency visible rather than trusted.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace ERC20

/-! ## Balance / totalSupply readers -/

/-- `balanceOf[a]` read from the contract's own account, as a `ℕ`. -/
def balOf (evm : EVM.State) (a : AccountAddress) : ℕ :=
  (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
    (erc20BalanceOfSlot (.address a))).toNat

/-- `totalSupply` (storage slot `2`) read from the contract's own account, as a `ℕ`. -/
def totalSupplyVal (evm : EVM.State) : ℕ :=
  (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat

/-! ## Raw `storageStore` frame lemmas

These characterise reading one slot after writing another, directly on the raw
`Solm.EVM.storageStore`/`storageLoad` pair (the form the ERC20 post-states are built from).  They
hold unconditionally for the *different-slot* case; the *same-slot* read-back needs the account to
exist (a `storageStore` to a missing account is a no-op). -/

/-- `storageStore` preserves the execution environment, hence the `codeOwner`. -/
@[simp] theorem storageStore_codeOwner (evm : EVM.State) (a : AccountAddress) (k v : UInt256) :
    (Solm.EVM.storageStore evm a k v).executionEnv = evm.executionEnv := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? a with
  | none => rfl
  | some acc => rfl

/-- Reading a *different* slot is unaffected by a store. -/
theorem storageLoad_storageStore_ne (evm : EVM.State) (a : AccountAddress)
    (rs ws v : UInt256) (h : rs ≠ ws) :
    Solm.EVM.storageLoad (Solm.EVM.storageStore evm a ws v) a rs =
      Solm.EVM.storageLoad evm a rs := by
  simp only [Solm.EVM.storageStore, Solm.EVM.storageLoad, State.lookupAccount, State.setAccount]
  cases hfind : evm.accountMap.find? a with
  | none => simp [Option.option, State.lookupAccount, hfind]
  | some acc =>
      simp only [Option.option]
      rw [show (({ evm with accountMap := evm.accountMap.insert a (acc.updateStorage ws v) }
            : EVM.State).accountMap.find? a) = some (acc.updateStorage ws v) from by
        simpa using accountMap_find_insert_self evm.accountMap a (acc.updateStorage ws v)]
      simp only [Option.option, Account.lookupStorage, Account.updateStorage]
      split
      · exact storage_findD_erase_ne acc.storage rs ws _ h
      · exact storage_findD_insert_ne acc.storage rs ws v _ h

/-- Reading the *same* slot after a store returns the stored value (account must exist). -/
theorem storageLoad_storageStore_self (evm : EVM.State) (a : AccountAddress)
    (ws v : UInt256) {acc : Account} (hex : evm.accountMap.find? a = some acc) :
    Solm.EVM.storageLoad (Solm.EVM.storageStore evm a ws v) a ws = v := by
  simp only [Solm.EVM.storageStore, Solm.EVM.storageLoad, State.lookupAccount, State.setAccount,
    hex, Option.option]
  rw [show (({ evm with accountMap := evm.accountMap.insert a (acc.updateStorage ws v) }
        : EVM.State).accountMap.find? a) = some (acc.updateStorage ws v) from by
    simpa using accountMap_find_insert_self evm.accountMap a (acc.updateStorage ws v)]
  simp only [Account.lookupStorage, Account.updateStorage]
  split
  · rename_i heq
    rw [show v = (default : UInt256) from eq_of_beq heq]
    have hnone : (acc.storage.erase ws).find? ws = none := storage_find?_erase_self acc.storage ws
    simp only [Batteries.RBMap.findD, hnone, Option.getD_none]; rfl
  · have hsome : (acc.storage.insert ws v).find? ws = some v := by
      rw [Batteries.RBMap.find?_insert_of_eq]; exact Std.ReflCmp.compare_self
    simp only [Batteries.RBMap.findD, hsome, Option.getD_some]

/-- A store to a *missing* account is a no-op. -/
theorem storageStore_noop_of_missing (evm : EVM.State) (a : AccountAddress) (k v : UInt256)
    (hmiss : evm.accountMap.find? a = none) :
    Solm.EVM.storageStore evm a k v = evm := by
  simp [Solm.EVM.storageStore, State.lookupAccount, hmiss, Option.option]

/-- `storageStore` to an *existing* account leaves it existing (used to thread read-backs through
    several writes). -/
theorem storageStore_find_codeOwner (evm : EVM.State) (a : AccountAddress) (k v : UInt256)
    {acc : Account} (hex : evm.accountMap.find? a = some acc) :
    ∃ acc', (Solm.EVM.storageStore evm a k v).accountMap.find? a = some acc' := by
  refine ⟨acc.updateStorage k v, ?_⟩
  simp only [Solm.EVM.storageStore, State.lookupAccount, State.setAccount, hex, Option.option]
  simpa using accountMap_find_insert_self evm.accountMap a (acc.updateStorage k v)

/-! ## Layout injectivity (explicit hypothesis) -/

/-- The storage layout sends distinct storage references to distinct slots.  For Solidity's layout
    this is exactly Keccak collision-freedom on the mapping-slot derivation; we keep it as a named
    hypothesis on the invariant theorems instead of axiomatizing it. -/
def InjectiveLayout (cfg : Config) : Prop :=
  ∀ (r₁ r₂ : EvaledStorageRef) (evm : EVM.State) (l₁ l₂ : StorageLoc),
    cfg.storage.layout r₁ evm = some l₁ → cfg.storage.layout r₂ evm = some l₂ →
    r₁ ≠ r₂ → l₁.slot ≠ l₂.slot

variable {cfg : Config}

/-- Helper: the ERC20 layout's slot for a resolved reference, when injectivity holds, is determined
    by the reference. -/
theorem InjectiveLayout.slot_ne (hinj : InjectiveLayout erc20Config)
    {r₁ r₂ : EvaledStorageRef} {l₁ l₂ : StorageLoc} (evm : EVM.State)
    (h₁ : erc20Config.storage.layout r₁ evm = some l₁)
    (h₂ : erc20Config.storage.layout r₂ evm = some l₂)
    (hr : r₁ ≠ r₂) : l₁.slot ≠ l₂.slot :=
  hinj r₁ r₂ evm l₁ l₂ h₁ h₂ hr

/-- Distinct holders ⇒ distinct `balanceOf` slots. -/
theorem balanceOf_slot_ne (hinj : InjectiveLayout erc20Config) {a b : AccountAddress} (h : a ≠ b) :
    erc20BalanceOfSlot (.address a) ≠ erc20BalanceOfSlot (.address b) := by
  have hL₁ : erc20Config.storage.layout
      { base := "balanceOf", steps := [.mindex (.address a)] } (default : EVM.State) =
        some (erc20Uint256Loc (erc20BalanceOfSlot (.address a))) := by
    rw [erc20Config_storage_balanceOf]
  have hL₂ : erc20Config.storage.layout
      { base := "balanceOf", steps := [.mindex (.address b)] } (default : EVM.State) =
        some (erc20Uint256Loc (erc20BalanceOfSlot (.address b))) := by
    rw [erc20Config_storage_balanceOf]
  have hr : ({ base := "balanceOf", steps := [.mindex (.address a)] } : EvaledStorageRef) ≠
      { base := "balanceOf", steps := [.mindex (.address b)] } := by
    intro he
    have hsteps := congrArg EvaledStorageRef.steps he
    simp only [List.cons.injEq, EvaledStorageRefStep.mindex.injEq, KeyValue.address.injEq,
      and_true] at hsteps
    exact h hsteps
  simpa [erc20Uint256Loc] using hinj.slot_ne (default : EVM.State) hL₁ hL₂ hr

/-- A `balanceOf` slot is never the `totalSupply` slot. -/
theorem balanceOf_slot_ne_totalSupply (hinj : InjectiveLayout erc20Config) (a : AccountAddress) :
    erc20BalanceOfSlot (.address a) ≠ (⟨2⟩ : UInt256) := by
  have hL₁ : erc20Config.storage.layout
      { base := "balanceOf", steps := [.mindex (.address a)] } (default : EVM.State) =
        some (erc20Uint256Loc (erc20BalanceOfSlot (.address a))) := by
    rw [erc20Config_storage_balanceOf]
  have hL₂ : erc20Config.storage.layout
      { base := "totalSupply", steps := [] } (default : EVM.State) =
        some (erc20Uint256Loc ⟨2⟩) := by rw [erc20Config_storage_totalSupply]
  have hr : ({ base := "balanceOf", steps := [.mindex (.address a)] } : EvaledStorageRef) ≠
      { base := "totalSupply", steps := [] } := by
    intro he; simp at he
  simpa [erc20Uint256Loc] using hinj.slot_ne (default : EVM.State) hL₁ hL₂ hr

/-- An `allowance` slot is never a `balanceOf` slot. -/
theorem allowance_slot_ne_balanceOf (hinj : InjectiveLayout erc20Config)
    (o s a : AccountAddress) :
    erc20AllowanceSlot (.address o) (.address s) ≠ erc20BalanceOfSlot (.address a) := by
  have hL₁ : erc20Config.storage.layout
      { base := "allowance", steps := [.mindex (.address o), .mindex (.address s)] }
        (default : EVM.State) =
        some (erc20Uint256Loc (erc20AllowanceSlot (.address o) (.address s))) := by
    rw [erc20Config_storage_allowance]
  have hL₂ : erc20Config.storage.layout
      { base := "balanceOf", steps := [.mindex (.address a)] } (default : EVM.State) =
        some (erc20Uint256Loc (erc20BalanceOfSlot (.address a))) := by
    rw [erc20Config_storage_balanceOf]
  have hr : ({ base := "allowance", steps := [.mindex (.address o), .mindex (.address s)] } : EvaledStorageRef) ≠ { base := "balanceOf", steps := [.mindex (.address a)] } := by
    intro he; simp at he
  simpa [erc20Uint256Loc] using hinj.slot_ne (default : EVM.State) hL₁ hL₂ hr

/-- An `allowance` slot is never the `totalSupply` slot. -/
theorem allowance_slot_ne_totalSupply (hinj : InjectiveLayout erc20Config) (o s : AccountAddress) :
    erc20AllowanceSlot (.address o) (.address s) ≠ (⟨2⟩ : UInt256) := by
  have hL₁ : erc20Config.storage.layout
      { base := "allowance", steps := [.mindex (.address o), .mindex (.address s)] }
        (default : EVM.State) =
        some (erc20Uint256Loc (erc20AllowanceSlot (.address o) (.address s))) := by
    rw [erc20Config_storage_allowance]
  have hL₂ : erc20Config.storage.layout
      { base := "totalSupply", steps := [] } (default : EVM.State) =
        some (erc20Uint256Loc ⟨2⟩) := by rw [erc20Config_storage_totalSupply]
  have hr : ({ base := "allowance", steps := [.mindex (.address o), .mindex (.address s)] } : EvaledStorageRef) ≠ { base := "totalSupply", steps := [] } := by
    intro he; simp at he
  simpa [erc20Uint256Loc] using hinj.slot_ne (default : EVM.State) hL₁ hL₂ hr

end ERC20
