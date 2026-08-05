import Examples.Precompiles.Modexp.WordSmall

/-!
# Exact single-word modular-exponentiation loop
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Select the stack-only modular exponentiation path when the decoded modulus exceeds one. -/
theorem reachLargeModulusBranch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode) (hvalue : I.weiValue = ⟨0⟩)
    (hb : (baseSizeWord I).toNat ≤ 32)
    (he : (exponentSizeWord I).toNat ≤ 32)
    (hm : (modulusSizeWord I).toNat ≤ 32)
    (hmod : 1 < (modulusWord I).toNat) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨0x168⟩
      [modulusWord I, exponentWord I, baseWord I, ⟨0⟩,
        UInt256.sub ⟨32⟩ (modulusSizeWord I), modulusSizeWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k 337 := by
  obtain ⟨k, rd0⟩ := reachModulusOperand
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hvalue hb he hm
  have hd :
      decode runtimeBytecode ⟨0x157⟩ = some (.PUSH0, .none) ∧
      decode runtimeBytecode ⟨0x158⟩ = some (.SWAP3, .none) ∧
      decode runtimeBytecode ⟨0x159⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) ∧
      decode runtimeBytecode ⟨0x15b⟩ = some (.DUP2, .none) ∧
      decode runtimeBytecode ⟨0x15c⟩ = some (.GT, .none) ∧
      decode runtimeBytecode ⟨0x15d⟩ = some (.Push .PUSH2, some (⟨0x168⟩, 2)) ∧
      decode runtimeBytecode ⟨0x160⟩ = some (.JUMPI, .none) := by
    simpa only [List.cons.injEq, and_true] using edgeBranchDecodes
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6⟩
  have hgt : UInt256.gt (modulusWord I) ⟨1⟩ = ⟨1⟩ := by
    apply ugt_one
    simpa using hmod
  have rd := evm_run rd0 with [
    known push0 hd0,
    known swap3 hd1,
    known push1 hd2 ⟨1⟩,
    known dup2 hd3,
    known gt hd4,
    known push2 hd5 ⟨0x168⟩,
    known jumpiT hd6 (by rw [hgt]; native_decide) jumpDest_168 ]
  exact ⟨_, rd⟩

/-- Initialize square-and-multiply: accumulator `1`, base reduced modulo `m`, and a duplicated
loop exponent at the loop header. -/
theorem reachWordLoopHeader {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode) (hvalue : I.weiValue = ⟨0⟩)
    (hb : (baseSizeWord I).toNat ≤ 32)
    (he : (exponentSizeWord I).toNat ≤ 32)
    (hm : (modulusSizeWord I).toNat ≤ 32)
    (hmod : 1 < (modulusWord I).toNat) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨0x173⟩
      [exponentWord I, UInt256.mod (baseWord I) (modulusWord I), modulusWord I,
        exponentWord I, ⟨1⟩, UInt256.sub ⟨32⟩ (modulusSizeWord I),
        modulusSizeWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k 366 := by
  obtain ⟨k, rd0⟩ := reachLargeModulusBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hvalue hb he hm hmod
  have hd :
      decode runtimeBytecode ⟨0x168⟩ = some (.JUMPDEST, .none) ∧
      decode runtimeBytecode ⟨0x169⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) ∧
      decode runtimeBytecode ⟨0x16b⟩ = some (.SWAP4, .none) ∧
      decode runtimeBytecode ⟨0x16c⟩ = some (.POP, .none) ∧
      decode runtimeBytecode ⟨0x16d⟩ = some (.SWAP1, .none) ∧
      decode runtimeBytecode ⟨0x16e⟩ = some (.SWAP2, .none) ∧
      decode runtimeBytecode ⟨0x16f⟩ = some (.DUP2, .none) ∧
      decode runtimeBytecode ⟨0x170⟩ = some (.SWAP1, .none) ∧
      decode runtimeBytecode ⟨0x171⟩ = some (.MOD, .none) ∧
      decode runtimeBytecode ⟨0x172⟩ = some (.DUP3, .none) := by
    simpa only [List.cons.injEq, and_true] using wordLoopSetupDecodes
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9⟩
  have rd := evm_run rd0 with [
    known jumpdest hd0,
    known push1 hd1 ⟨1⟩,
    known swap4 hd2,
    known pop hd3,
    known swap1 hd4,
    known swap2 hd5,
    known dup2 hd6,
    known swap1 hd7,
    known mod hd8,
    known dup3 hd9 ]
  exact ⟨_, (rd.withPC (by native_decide)).withIndices rfl (by omega)⟩

end Modexp
