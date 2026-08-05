import Examples.Precompiles.Modexp.Bridge
import Examples.Precompiles.Modexp.WordLoopSteps

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

theorem shiftRightOne_toNat (e : UInt256) :
    (UInt256.shiftRight e ⟨1⟩).toNat = e.toNat / 2 := by
  simpa using shiftRight_toNat_of_lt256 e ⟨1⟩ (by decide)

/-- Word-level square-and-multiply, matching the deployed loop instruction-for-instruction. -/
def wordPowAux (base acc modulus e : UInt256) : UInt256 :=
  if _h : e = ⟨0⟩ then acc
  else
    let acc' := if e.toNat % 2 = 1 then UInt256.mulMod acc base modulus else acc
    wordPowAux (UInt256.mulMod base base modulus) acc' modulus (UInt256.shiftRight e ⟨1⟩)
termination_by e.toNat
decreasing_by
  rw [shiftRightOne_toNat]
  apply Nat.div_lt_self
  · by_contra hz
    have : e.toNat = 0 := Nat.eq_zero_of_not_pos hz
    exact _h (uint256_toNat_eq_zero this)
  · decide

/-- Gas from a word-loop header through the successful return.  It is executable and exact:
29 gas for the zero test/return, 83 for every zero bit, and 126 for every one bit. -/
def wordLoopGas (e : Nat) : Nat :=
  if h : e = 0 then 29
  else (if e % 2 = 1 then 126 else 83) + wordLoopGas (e / 2)
termination_by e
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

/-- Exact recursive loop theorem, preserving both the final word value and the OOG threshold. -/
theorem wordLoopExact {cA gh bl σ σ₀ A I} {g : Sat256}
    {e b m acc : UInt256} {k C : Nat}
    (hm : (modulusSizeWord I).toNat ≤ 32)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨0x173⟩
      [e, b, m, e, acc, UInt256.sub ⟨32⟩ (modulusSizeWord I), modulusSizeWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ) (wordResult (wordPowAux b acc m e) I) (C + wordLoopGas e.toNat) := by
  by_cases hzero : e = ⟨0⟩
  · subst e
    simpa [wordPowAux, wordLoopGas] using wordLoopExit hm rd0
  · have hnat : e.toNat ≠ 0 := by
      intro hz
      exact hzero (uint256_toNat_eq_zero hz)
    rcases Nat.mod_two_eq_zero_or_one e.toNat with heven | hodd
    · obtain ⟨k', rd1⟩ := wordLoopIterationEven rd0 hzero heven
      have ih := wordLoopExact hm rd1
      rw [wordPowAux, dif_neg hzero, if_neg (by omega : ¬ e.toNat % 2 = 1)]
      rw [wordLoopGas, dif_neg hnat, if_neg (by omega : ¬ e.toNat % 2 = 1)]
      rw [shiftRightOne_toNat] at ih
      exact ih.withCost (by omega)
    · obtain ⟨k', rd1⟩ := wordLoopIterationOdd rd0 hzero hodd
      have ih := wordLoopExact hm rd1
      rw [wordPowAux, dif_neg hzero, if_pos hodd]
      rw [wordLoopGas, dif_neg hnat, if_pos hodd]
      rw [shiftRightOne_toNat] at ih
      exact ih.withCost (by omega)
termination_by e.toNat
decreasing_by
  all_goals
    rw [shiftRightOne_toNat]
    exact Nat.div_lt_self (Nat.pos_of_ne_zero hnat) (by decide)

end Modexp
