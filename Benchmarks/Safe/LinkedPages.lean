import Benchmarks.Safe.Common

open Ethereum Ethereum.EVM

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: a finite prefix of a sentinel-terminated linked list.
inductive LinkedPage (next : UInt256 → UInt256) : Nat → UInt256 → List UInt256 → UInt256 → Prop
  | stop {fuel current} (h : fuel = 0 ∨ current = ⟨0⟩ ∨ current = ⟨1⟩) :
      LinkedPage next fuel current [] current
  | step {fuel current words last} (hz : current ≠ ⟨0⟩) (hs : current ≠ ⟨1⟩)
      (tail : LinkedPage next fuel (next current) words last) :
      LinkedPage next (fuel + 1) current (current :: words) last

theorem LinkedPage.exists (next : UInt256 → UInt256) (fuel : Nat) (current : UInt256) :
    ∃ words last, LinkedPage next fuel current words last := by
  induction fuel generalizing current with
  | zero => exact ⟨[], current, .stop (.inl rfl)⟩
  | succ fuel ih =>
      by_cases hz : current = ⟨0⟩
      · exact ⟨[], current, .stop (.inr (.inl hz))⟩
      by_cases hs : current = ⟨1⟩
      · exact ⟨[], current, .stop (.inr (.inr hs))⟩
      obtain ⟨words, last, h⟩ := ih (next current)
      exact ⟨current :: words, last, .step hz hs h⟩

theorem LinkedPage.length_le {next fuel current words last}
    (h : LinkedPage next fuel current words last) : words.length ≤ fuel := by
  induction h with
  | stop => simp
  | step hz hs ht ih => simp only [List.length_cons]; omega

theorem LinkedPage.canonical {next fuel current words last}
    (h : LinkedPage next fuel current words last)
    (hc : current.toNat < EVM.addressModulus)
    (hn : ∀ w, (next w).toNat < EVM.addressModulus) :
    (∀ w ∈ words, w.toNat < EVM.addressModulus) ∧
      last.toNat < EVM.addressModulus := by
  induction h with
  | stop => exact ⟨by simp, hc⟩
  | step hz hs ht ih =>
      obtain ⟨hw, hl⟩ := ih (hn _)
      exact ⟨by simpa only [List.mem_cons, forall_eq_or_imp] using And.intro hc hw, hl⟩

end Benchmarks.Safe
