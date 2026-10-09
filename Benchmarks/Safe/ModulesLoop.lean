import Benchmarks.Safe.ModulesLoopTrace
import Benchmarks.Safe.LinkedPages

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

theorem safeModulesLoop {I g s0 σ k C aw mem rdata capacity doneWords fuel current words last}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨4995⟩
      (UInt256.ofNat doneWords.length :: current :: ⟨128⟩ :: UInt256.ofNat capacity :: R)
      mem aw rdata σ k C)
    (hov : R.length + 12 ≤ 1024)
    (hm : AddressArrayMemory mem capacity (doneWords ++ List.replicate fuel ⟨0⟩))
    (hn : capacity ≤ 2 ^ 64 - 1) (hf : doneWords.length + fuel = capacity)
    (hc : current.toNat < EVM.addressModulus)
    (hp : LinkedPage (moduleLinkAt σ I) fuel current words last) :
    ∃ mem' aw' k' C',
      RD safeBytecode I g s0 ⟨5128⟩
        (UInt256.ofNat (doneWords ++ words).length :: last :: ⟨128⟩ ::
          UInt256.ofNat capacity :: R) mem' aw' rdata σ k' C' ∧
      AddressArrayMemory mem' capacity
        ((doneWords ++ words) ++ List.replicate (fuel - words.length) ⟨0⟩) := by
  induction hp generalizing mem doneWords aw k C with
  | @stop fuel current hstop =>
      obtain ⟨k', C', hout⟩ := safeModulesLoopExit h (by omega) hc (by
        rcases hstop with hzero | hz | hs
        · right; right
          have hlen : doneWords.length = capacity := by omega
          simp only [hlen, Nat.le_refl]
        · exact .inl hz
        · exact .inr (.inl hs))
      exact ⟨mem, aw, k', C', by simpa using hout, by simpa using hm⟩
  | @step fuel current words last hz hs hp ih =>
      have hi : doneWords.length < capacity := by omega
      obtain ⟨aw₁, k₁, C₁, h₁⟩ := safeModulesLoopStep h hov hm hn hi hc hz hs
      have hm₁ := (hm.write doneWords.length current hi).scratch current ⟨1⟩
      have hset : (doneWords ++ List.replicate (fuel + 1) (⟨0⟩ : UInt256)).set
          doneWords.length current = (doneWords ++ [current]) ++ List.replicate fuel ⟨0⟩ := by
        simp [List.set_append_right, List.replicate_succ, List.append_assoc]
      rw [hset] at hm₁
      obtain ⟨mem', aw', k', C', hout, hm'⟩ := ih
        (doneWords := doneWords ++ [current]) (by simpa using h₁) hm₁
        (by simp only [List.length_append, List.length_singleton]; omega)
        (solcAddrMask_result_canonical _)
      exact ⟨mem', aw', k', C', by simpa [List.append_assoc] using hout,
        by simpa [List.append_assoc] using hm'⟩

end Benchmarks.Safe
