import Benchmarks.Safe.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: a failed dispatch means every transition's selector misses.
theorem dispatchList_none_miss {ts : List TransitionDecl} {cd : ByteArray}
    (hd : dispatchList ts cd = none) {t : TransitionDecl} (ht : t ∈ ts) :
    (selectorOf t == cd.extract 0 4) = false := by
  induction ts with
  | nil => simp at ht
  | cons head tail ih =>
      rw [dispatchList_cons] at hd
      split at hd
      · cases hd
      · rename_i hm
        rcases List.mem_cons.mp ht with heq | ht
        · rw [heq]
          simpa only [Bool.not_eq_true] using hm
        · exact ih hd ht

-- LIBRARY CANDIDATE: source dispatch failure rules out a concrete EVM selector arm.
theorem selectorMissWord {c : ContractDecl} {t : TransitionDecl} {I : ExecutionEnv}
    (c0 c1 c2 c3 : UInt8) (w : UInt256)
    (hd : selectorDispatchMsg c I.calldata = none) (ht : t ∈ c.transitions)
    (hlong : 4 ≤ I.calldata.size)
    (hbytes : (KEC (String.toByteArray (transitionSigStr t))).extract 0 4 =
      ⟨#[c0, c1, c2, c3]⟩)
    (hnat : (fromBytesBigEndian [c0, c1, c2, c3] : Nat) = w.toNat) :
    UInt256.eq w (solcSelectorWord I) = ⟨0⟩ := by
  have hm := dispatchList_none_miss
    ((selectorDispatchMsg_eq_dispatchList c I.calldata).symm.trans hd) ht
  change ((KEC (String.toByteArray (transitionSigStr t))).extract 0 4 ==
    I.calldata.extract 0 4) = false at hm
  rw [hbytes] at hm
  rw [evmSelectorDecode hlong c0 c1 c2 c3 w hnat, hm]
  rfl

-- GENERALIZES RD.dispatchTo: skip all arms without requiring a final matching arm.
theorem skipSelectorArms {code : ByteArray} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {word : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap} {R : List UInt256} (n : Nat) {start : UInt256} {k C : Nat}
    (h : RD code I g s0 start (word :: R) mem aw rdata σ k C)
    (hwf : ∀ j, j < n → armWellFormed code (nthArmPc code start j))
    (hmiss : ∀ j, j < n → UInt256.eq (armSelNat code (nthArmPc code start j)) word = ⟨0⟩)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD code I g s0 (nthArmPc code start n) (word :: R) mem aw rdata σ k' C' := by
  induction n generalizing start k C with
  | zero => exact ⟨k, C, h⟩
  | succ n ih =>
      exact ih (RD.selectorArmNotTakenAuto h (hwf 0 (by omega)) (hmiss 0 (by omega)) hov)
        (fun j hj ↦ hwf (j + 1) (by omega)) (fun j hj ↦ hmiss (j + 1) (by omega))

end Benchmarks.Safe
