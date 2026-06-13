import TruthClaude.PowCorrect
open Ethereum Ethereum.EVM TruthClaude.Theory

theorem ult_one {a b : UInt256} (h : a.toNat < b.toNat) : UInt256.lt a b = ⟨1⟩ := by
  show UInt256.fromBool (decide (a < b)) = ⟨1⟩
  rw [decide_eq_true (show a < b from h)]; rfl
theorem ult_zero {a b : UInt256} (h : b.toNat ≤ a.toNat) : UInt256.lt a b = ⟨0⟩ := by
  show UInt256.fromBool (decide (a < b)) = ⟨0⟩
  rw [decide_eq_false (show ¬ (a < b) from by show ¬ (a.toNat < b.toNat); omega)]; rfl
theorem mul2_toNat {r : UInt256} (h : 2 * r.toNat < UInt256.size) :
    (UInt256.mul r ⟨2⟩).toNat = 2 * r.toNat := by
  show (r.val * (⟨2⟩ : UInt256).val).val = 2 * r.toNat
  rw [Fin.val_mul]
  show (r.toNat * 2) % UInt256.size = 2 * r.toNat
  rw [Nat.mul_comm]; exact Nat.mod_eq_of_lt h
theorem add1_toNat {i : UInt256} (h : i.toNat + 1 < UInt256.size) :
    (i + ⟨1⟩).toNat = i.toNat + 1 := by
  show (i.val + (⟨1⟩ : UInt256).val).val = i.toNat + 1
  rw [Fin.val_add]
  show (i.toNat + 1) % UInt256.size = i.toNat + 1
  exact Nat.mod_eq_of_lt h
#print axioms add1_toNat

example : UInt256.isZero ⟨0⟩ = ⟨1⟩ := by decide
example : UInt256.isZero ⟨1⟩ = ⟨0⟩ := by decide
example : (D_J powBytecode ⟨0⟩).contains ⟨142⟩ = true := by
  rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp)
example (i r slot n ret : UInt256) : ([i,r,slot,n,ret] : List UInt256).length ≤ 1024 := by simp
