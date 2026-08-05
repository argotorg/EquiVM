import Examples.Precompiles.Modexp.Word

/-!
# ModExp single-word edge path

This file parses the three operands on the stack-only path and proves the exact branch selected
when the decoded modulus is zero or one.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem reachBaseOperand {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode) (hvalue : I.weiValue = ⟨0⟩)
    (hb : (baseSizeWord I).toNat ≤ 32)
    (he : (exponentSizeWord I).toNat ≤ 32)
    (hm : (modulusSizeWord I).toNat ≤ 32) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨0x13a⟩
      [baseWord I, exponentSizeWord I, baseSizeWord I, modulusSizeWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k 238 := by
  obtain ⟨k, rd0⟩ := reachWordPath
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hvalue hb he hm
  have hd :
      decode runtimeBytecode ⟨0x12e⟩ = some (.JUMPDEST, .none) ∧
      decode runtimeBytecode ⟨0x12f⟩ = some (.Push .PUSH1, some (⟨96⟩, 1)) ∧
      decode runtimeBytecode ⟨0x131⟩ = some (.CALLDATALOAD, .none) ∧
      decode runtimeBytecode ⟨0x132⟩ = some (.DUP3, .none) ∧
      decode runtimeBytecode ⟨0x133⟩ = some (.Push .PUSH1, some (⟨32⟩, 1)) ∧
      decode runtimeBytecode ⟨0x135⟩ = some (.SUB, .none) ∧
      decode runtimeBytecode ⟨0x136⟩ = some (.Push .PUSH1, some (⟨3⟩, 1)) ∧
      decode runtimeBytecode ⟨0x138⟩ = some (.SHL, .none) ∧
      decode runtimeBytecode ⟨0x139⟩ = some (.SHR, .none) := by
    simpa only [List.cons.injEq, and_true] using baseOperandDecodes
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8⟩
  have rd := evm_run rd0 with [
    known jumpdest hd0,
    known push1 hd1 ⟨96⟩,
    known calldataload hd2,
    known dup3 hd3,
    known push1 hd4 ⟨32⟩,
    known sub hd5,
    known push1 hd6 ⟨3⟩,
    known shl hd7,
    known shr hd8 ]
  exact ⟨_, rd⟩

private theorem reachExponentOperand {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode) (hvalue : I.weiValue = ⟨0⟩)
    (hb : (baseSizeWord I).toNat ≤ 32)
    (he : (exponentSizeWord I).toNat ≤ 32)
    (hm : (modulusSizeWord I).toNat ≤ 32) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨0x148⟩
      [exponentWord I, ⟨96⟩, baseWord I, exponentSizeWord I, baseSizeWord I,
        modulusSizeWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k 271 := by
  obtain ⟨k, rd0⟩ := reachBaseOperand
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hvalue hb he hm
  have hd :
      decode runtimeBytecode ⟨0x13a⟩ = some (.Push .PUSH1, some (⟨96⟩, 1)) ∧
      decode runtimeBytecode ⟨0x13c⟩ = some (.DUP4, .none) ∧
      decode runtimeBytecode ⟨0x13d⟩ = some (.DUP2, .none) ∧
      decode runtimeBytecode ⟨0x13e⟩ = some (.ADD, .none) ∧
      decode runtimeBytecode ⟨0x13f⟩ = some (.CALLDATALOAD, .none) ∧
      decode runtimeBytecode ⟨0x140⟩ = some (.DUP4, .none) ∧
      decode runtimeBytecode ⟨0x141⟩ = some (.Push .PUSH1, some (⟨32⟩, 1)) ∧
      decode runtimeBytecode ⟨0x143⟩ = some (.SUB, .none) ∧
      decode runtimeBytecode ⟨0x144⟩ = some (.Push .PUSH1, some (⟨3⟩, 1)) ∧
      decode runtimeBytecode ⟨0x146⟩ = some (.SHL, .none) ∧
      decode runtimeBytecode ⟨0x147⟩ = some (.SHR, .none) := by
    simpa only [List.cons.injEq, and_true] using exponentOperandDecodes
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10⟩
  have rd := evm_run rd0 with [
    known push1 hd0 ⟨96⟩,
    known dup4 hd1,
    known dup2 hd2,
    known add hd3,
    known calldataload hd4,
    known dup4 hd5,
    known push1 hd6 ⟨32⟩,
    known sub hd7,
    known push1 hd8 ⟨3⟩,
    known shl hd9,
    known shr hd10 ]
  exact ⟨_, rd⟩

theorem reachModulusOffset {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode) (hvalue : I.weiValue = ⟨0⟩)
    (hb : (baseSizeWord I).toNat ≤ 32)
    (he : (exponentSizeWord I).toNat ≤ 32)
    (hm : (modulusSizeWord I).toNat ≤ 32) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨0x150⟩
      [(baseSizeWord I + exponentSizeWord I) + ⟨96⟩, baseWord I, exponentWord I,
        UInt256.sub ⟨32⟩ (modulusSizeWord I), modulusSizeWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k 292 := by
  obtain ⟨k, rd0⟩ := reachExponentOperand
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hvalue hb he hm
  have hd :
      decode runtimeBytecode ⟨0x148⟩ = some (.SWAP3, .none) ∧
      decode runtimeBytecode ⟨0x149⟩ = some (.DUP6, .none) ∧
      decode runtimeBytecode ⟨0x14a⟩ = some (.Push .PUSH1, some (⟨32⟩, 1)) ∧
      decode runtimeBytecode ⟨0x14c⟩ = some (.SUB, .none) ∧
      decode runtimeBytecode ⟨0x14d⟩ = some (.SWAP5, .none) ∧
      decode runtimeBytecode ⟨0x14e⟩ = some (.ADD, .none) ∧
      decode runtimeBytecode ⟨0x14f⟩ = some (.ADD, .none) := by
    have h := modulusOperandDecodes
    simp only [List.cons.injEq, and_true] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
      h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6⟩
  have rdA := evm_run rd0 with [
    known swap3 hd0,
    known dup6 hd1,
    known push1 hd2 ⟨32⟩,
    known sub hd3 ]
  have atSwap : ∃ k', RDx runtimeBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨0x14d⟩
      [UInt256.sub ⟨32⟩ (modulusSizeWord I), exponentSizeWord I, ⟨96⟩,
        baseWord I, exponentWord I, baseSizeWord I, modulusSizeWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' 283 :=
    ⟨_, (rdA.withPC (by native_decide)).withIndices rfl (by omega)⟩
  obtain ⟨k', rd1⟩ := atSwap
  have rd := evm_run rd1 with [
    known swap5 hd4,
    known add hd5,
    known add hd6 ]
  exact ⟨_, (rd.withPC (by native_decide)).withIndices rfl (by omega)⟩

/- BISECT
private theorem reachModulusOperand {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode) (hvalue : I.weiValue = ⟨0⟩)
    (hb : (baseSizeWord I).toNat ≤ 32)
    (he : (exponentSizeWord I).toNat ≤ 32)
    (hm : (modulusSizeWord I).toNat ≤ 32) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨0x157⟩
      [exponentWord I, baseWord I, modulusWord I,
        UInt256.shiftLeft (⟨32⟩ - modulusSizeWord I) ⟨3⟩, modulusSizeWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k 310 := by
  obtain ⟨k, rd0⟩ := reachModulusOffset
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hvalue hb he hm
  have hd :
      decode runtimeBytecode ⟨0x148⟩ = some (.SWAP3, .none) ∧
      decode runtimeBytecode ⟨0x149⟩ = some (.DUP6, .none) ∧
      decode runtimeBytecode ⟨0x14a⟩ = some (.Push .PUSH1, some (⟨32⟩, 1)) ∧
      decode runtimeBytecode ⟨0x14c⟩ = some (.SUB, .none) ∧
      decode runtimeBytecode ⟨0x14d⟩ = some (.SWAP5, .none) ∧
      decode runtimeBytecode ⟨0x14e⟩ = some (.ADD, .none) ∧
      decode runtimeBytecode ⟨0x14f⟩ = some (.ADD, .none) ∧
      decode runtimeBytecode ⟨0x150⟩ = some (.CALLDATALOAD, .none) ∧
      decode runtimeBytecode ⟨0x151⟩ = some (.DUP4, .none) ∧
      decode runtimeBytecode ⟨0x152⟩ = some (.Push .PUSH1, some (⟨3⟩, 1)) ∧
      decode runtimeBytecode ⟨0x154⟩ = some (.SHL, .none) ∧
      decode runtimeBytecode ⟨0x155⟩ = some (.SHR, .none) ∧
      decode runtimeBytecode ⟨0x156⟩ = some (.SWAP2, .none) := by
    simpa only [List.cons.injEq, and_true] using modulusOperandDecodes
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10,
    hd11, hd12⟩
  have rd := evm_run rd0 with [
    known calldataload hd7,
    known dup4 hd8,
    known push1 hd9 ⟨3⟩,
    known shl hd10,
    known shr hd11,
    known swap2 hd12 ]
  exact ⟨_, (rd.withPC (by native_decide)).withIndices rfl (by omega)⟩

/-- Exact parsing of the three single-word operands and selection of the `modulus ≤ 1` edge
branch. -/
theorem reachSmallModulusBranch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode) (hvalue : I.weiValue = ⟨0⟩)
    (hb : (baseSizeWord I).toNat ≤ 32)
    (he : (exponentSizeWord I).toNat ≤ 32)
    (hm : (modulusSizeWord I).toNat ≤ 32)
    (hmod : (modulusWord I).toNat ≤ 1) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨0x161⟩
      [modulusWord I, exponentWord I, baseWord I, ⟨0⟩,
        UInt256.shiftLeft (⟨32⟩ - modulusSizeWord I) ⟨3⟩, modulusSizeWord I]
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
  have hgt : UInt256.gt (modulusWord I) ⟨1⟩ = ⟨0⟩ := by
    apply ugt_zero
    simpa using hmod
  have rd := evm_run rd0 with [
    known push0 hd0,
    known swap3 hd1,
    known push1 hd2 ⟨1⟩,
    known dup2 hd3,
    known gt hd4,
    known push2 hd5 ⟨0x168⟩,
    known jumpiNT hd6 hgt ]
  exact ⟨_, rd⟩

-/
end Modexp
