import Examples.Precompiles.Modexp.WordEdge

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Completion of the single-word operand parser through the modulus word. -/
theorem reachModulusOperand {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode) (hvalue : I.weiValue = ⟨0⟩)
    (hb : (baseSizeWord I).toNat ≤ 32)
    (he : (exponentSizeWord I).toNat ≤ 32)
    (hm : (modulusSizeWord I).toNat ≤ 32) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨0x157⟩
      [exponentWord I, baseWord I, modulusWord I,
        UInt256.sub ⟨32⟩ (modulusSizeWord I), modulusSizeWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k 310 := by
  obtain ⟨k, rd0⟩ := reachModulusOffset
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hvalue hb he hm
  have hd :
      decode runtimeBytecode ⟨0x150⟩ = some (.CALLDATALOAD, .none) ∧
      decode runtimeBytecode ⟨0x151⟩ = some (.DUP4, .none) ∧
      decode runtimeBytecode ⟨0x152⟩ = some (.Push .PUSH1, some (⟨3⟩, 1)) ∧
      decode runtimeBytecode ⟨0x154⟩ = some (.SHL, .none) ∧
      decode runtimeBytecode ⟨0x155⟩ = some (.SHR, .none) ∧
      decode runtimeBytecode ⟨0x156⟩ = some (.SWAP2, .none) := by
    simpa only [List.cons.injEq, and_true] using modulusOperandTailDecodes
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩
  have rdA := evm_run rd0 with [
    known calldataload hd0,
    known dup4 hd1,
    known push1 hd2 ⟨3⟩ ]
  have rdB := rdA.shl hd3 (by simp)
  have rdC := rdB.shr hd4 (by simp)
  have rd := rdC.swap2 hd5 (by simp)
  exact ⟨_, (rd.withPC (by native_decide)).withIndices rfl (by omega)⟩

end Modexp
