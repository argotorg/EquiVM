import EVM.Types

/-! # Equality of EVM account maps up to storage representation -/

namespace Refinement

/-- Account equality up to storage-map representation.  The non-storage account fields must match
    structurally, while persistent storage is compared by `find?` at every slot.  This abstracts
    over `RBMap` tree shape without equating absent storage slots with explicitly stored zeroes. -/
def accountEquiv (a b : Ethereum.Account) : Prop :=
  a.nonce = b.nonce ∧
  a.balance = b.balance ∧
  a.code = b.code ∧
  (∀ slot : Ethereum.UInt256,
    a.storage.find? slot = b.storage.find? slot) ∧
      (∀ slot : Ethereum.UInt256,
        a.tstorage.find? slot = b.tstorage.find? slot)

/-- Account-map equality up to the internal representation of each account's persistent storage
    map.  Account presence is still exact. -/
def accountMapEquiv (σ τ : Ethereum.AccountMap) : Prop :=
  ∀ addr : Ethereum.AccountAddress,
    match σ.find? addr, τ.find? addr with
    | none, none => True
    | some a, some b => accountEquiv a b
    | _, _ => False

theorem accountEquiv.refl (a : Ethereum.Account) : accountEquiv a a := by
  exact ⟨rfl, rfl, rfl, fun _ => rfl, fun _ => rfl⟩

theorem accountMapEquiv.refl (σ : Ethereum.AccountMap) : accountMapEquiv σ σ := by
  intro addr
  cases σ.find? addr <;> simp [accountEquiv.refl]

theorem accountEquiv.symm {a b : Ethereum.Account}
    (hab : accountEquiv a b) : accountEquiv b a := by
  rcases hab with ⟨hn, hb, hc, hs, ht⟩
  exact ⟨hn.symm, hb.symm, hc.symm, fun slot => (hs slot).symm,
    fun slot => (ht slot).symm⟩

theorem accountMapEquiv.symm {σ τ : Ethereum.AccountMap}
    (hστ : accountMapEquiv σ τ) : accountMapEquiv τ σ := by
  intro addr
  specialize hστ addr
  cases hσ : σ.find? addr <;> cases hτ : τ.find? addr <;>
    simp [hσ, hτ] at hστ ⊢
  exact accountEquiv.symm hστ

theorem accountMapEquiv.of_eq {σ τ : Ethereum.AccountMap} (h : σ = τ) :
    accountMapEquiv σ τ := by
  subst h
  exact accountMapEquiv.refl σ

theorem accountEquiv.trans {a b c : Ethereum.Account}
    (hab : accountEquiv a b) (hbc : accountEquiv b c) : accountEquiv a c := by
  rcases hab with ⟨hn₁, hb₁, hc₁, hs₁, ht₁⟩
  rcases hbc with ⟨hn₂, hb₂, hc₂, hs₂, ht₂⟩
  exact ⟨hn₁.trans hn₂, hb₁.trans hb₂, hc₁.trans hc₂,
    fun slot => (hs₁ slot).trans (hs₂ slot), fun slot => (ht₁ slot).trans (ht₂ slot)⟩

theorem accountMapEquiv.trans {σ τ υ : Ethereum.AccountMap}
    (hστ : accountMapEquiv σ τ) (hτυ : accountMapEquiv τ υ) : accountMapEquiv σ υ := by
  intro addr
  specialize hστ addr
  specialize hτυ addr
  cases hσ : σ.find? addr <;> cases hτ : τ.find? addr <;> cases hυ : υ.find? addr <;>
    simp [hσ, hτ, hυ] at hστ hτυ ⊢
  exact accountEquiv.trans hστ hτυ

end Refinement
