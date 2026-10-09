import Benchmarks.Safe.GetOwnersSource
import Benchmarks.Safe.GetOwnersLoopTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

theorem safeGetOwnersLoop (evm : EVM.State) {g s0 k C aw mem rdata n words i current locals}
    {ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode evm.executionEnv g s0 ⟨4419⟩
      (current :: UInt256.ofNat i :: ⟨128⟩ :: ⟨96⟩ :: ret :: R)
      mem aw rdata evm.accountMap k C)
    (hov : R.length + 11 ≤ 1024)
    (hm : AddressArrayMemory mem n words) (hl : GetOwnersLocals locals words i current)
    (hn : n ≤ 2 ^ 64 - 1) (hi : i ≤ n)
    (hc : current.toNat < EVM.addressModulus)
    (hw : ∀ w ∈ words, w.toNat < EVM.addressModulus)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    (ExecStmt config { contract := contract, locals := locals } evm getOwnersLoop .reverted ∧
      RDrev safeBytecode g s0) ∨
    ∃ words' locals' mem' aw' k' C' j,
      ExecStmt config { contract := contract, locals := locals } evm getOwnersLoop
        (.ok { contract := contract, locals := locals' } evm) ∧
      GetOwnersLocals locals' words' j ⟨1⟩ ∧
      AddressArrayMemory mem' n words' ∧
      (∀ w ∈ words', w.toNat < EVM.addressModulus) ∧
      RD safeBytecode evm.executionEnv g s0 ret (⟨128⟩ :: R)
        mem' aw' rdata evm.accountMap k' C' := by
  induction hfuel : n - i using Nat.strong_induction_on generalizing i words current locals
      mem aw k C with
  | h fuel ih =>
    by_cases hs : current = ⟨1⟩
    · subst current
      obtain ⟨k', C', h'⟩ := safeGetOwnersLoopExit h (by omega) hret
      refine .inr ⟨words, locals, mem, aw, k', C', i, ?_, ?_, hm, hw, h'⟩
      · exact .whileFalse (by simpa only [ne_eq, not_true_eq_false, decide_false] using
          safeGetOwnersCondition evm hl hc)
      · exact hl
    · have hcond := safeGetOwnersCondition evm hl hc
      simp only [hs, ne_eq, not_false_eq_true, decide_true] at hcond
      by_cases hib : i < n
      · have hfit : i + 1 < UInt256.size := by change i + 1 < 2 ^ 256; omega
        have hsbody := safeGetOwnersLoopStep evm hl hc (by rw [hm.length]; exact hib) hfit
        obtain ⟨aw', k', C', h'⟩ := safeGetOwnersLoopNext h (by simp; omega) hm hn hib hc hs
        rw [← ownerLink_eq_at] at h'
        have hw' : ∀ w ∈ words.set i current, w.toNat < EVM.addressModulus := by
          intro w hmem
          rcases List.mem_or_eq_of_mem_set hmem with hm | rfl
          · exact hw w hm
          · exact hc
        have hrec := ih (n - (i + 1)) (by omega) h' (hm.step i current hib)
          (safeGetOwnersNextLocals evm hl) (by omega) (solcAddrMask_result_canonical _) hw' rfl
        rcases hrec with ⟨hsrc, hrev⟩ | ⟨ws, ls, ms, a, k'', C'', j, hsrc, hls, hms, hws, hrd⟩
        · exact .inl ⟨.whileTrue hcond hsbody hsrc, hrev⟩
        · exact .inr ⟨ws, ls, ms, a, k'', C'', j, .whileTrue hcond hsbody hsrc,
            hls, hms, hws, hrd⟩
      · exact .inl ⟨.whileRevert hcond (safeGetOwnersLoopBounds evm hl
          (by rw [hm.length]; omega)),
          safeGetOwnersLoopOutOfBounds h (by simp; omega) hm (by omega) hc hs⟩

end Benchmarks.Safe
