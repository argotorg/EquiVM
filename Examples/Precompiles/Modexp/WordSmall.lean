import Examples.Precompiles.Modexp.WordModulus

/-!
# ModExp single-word modulus-zero/one path

This file closes the loop-free edge path with an exact `RDxRet` fact.  The returned bytes are
kept as the literal memory projection here; `Bridge.lean` identifies that projection with the
trusted pure ModExp model.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false

def wordResultMemory (value : UInt256) : ByteArray :=
  value.toByteArray.write 0 solcFreePtrMem 0 32

def wordResult (value : UInt256) (I : ExecutionEnv) : ByteArray :=
  (wordResultMemory value).readWithPadding
    (UInt256.sub ⟨32⟩ (modulusSizeWord I)).toNat
    (modulusSizeWord I).toNat

def smallResultMemory : ByteArray := wordResultMemory ⟨0⟩

def smallResult (I : ExecutionEnv) : ByteArray :=
  wordResult ⟨0⟩ I

/-- Exact parser/dispatch trace to the loop-free `modulus ≤ 1` return block. -/
theorem reachSmallModulusBranch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode) (hvalue : I.weiValue = ⟨0⟩)
    (hb : (baseSizeWord I).toNat ≤ 32)
    (he : (exponentSizeWord I).toNat ≤ 32)
    (hm : (modulusSizeWord I).toNat ≤ 32)
    (hmod : (modulusWord I).toNat ≤ 1) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨0x161⟩
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

/-- Shared exact return block for a one-word modular exponentiation result. -/
theorem returnWordExact {cA gh bl σ σ₀ A I} {g : Sat256}
    {x y z value : UInt256} {k C : Nat}
    (hm : (modulusSizeWord I).toNat ≤ 32)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨0x161⟩
      [x, y, z, value, UInt256.sub ⟨32⟩ (modulusSizeWord I), modulusSizeWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ) (wordResult value I) (C + 12) := by
  have hd :
      decode runtimeBytecode ⟨0x161⟩ = some (.JUMPDEST, .none) ∧
      decode runtimeBytecode ⟨0x162⟩ = some (.POP, .none) ∧
      decode runtimeBytecode ⟨0x163⟩ = some (.POP, .none) ∧
      decode runtimeBytecode ⟨0x164⟩ = some (.POP, .none) ∧
      decode runtimeBytecode ⟨0x165⟩ = some (.PUSH0, .none) ∧
      decode runtimeBytecode ⟨0x166⟩ = some (.MSTORE, .none) ∧
      decode runtimeBytecode ⟨0x167⟩ = some (.RETURN, .none) := by
    simpa only [List.cons.injEq, and_true] using smallModulusReturnDecodes
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6⟩
  have rd := evm_run rd0 with [
    known jumpdest hd0,
    known pop hd1,
    known pop hd2,
    known pop hd3,
    known push0 hd4,
    raw mstore 0 (wordResultMemory value) (UInt256.ofNat 3) hd5
      mem_cost
      (by rfl)
      (by native_decide)
      (by simp) ]
  have hpad : (UInt256.sub ⟨32⟩ (modulusSizeWord I)).toNat =
      32 - (modulusSizeWord I).toNat := by
    exact usub_ofNat_word_toNat hm (by decide)
  have rdret := RDx.ret 0 (wordResult value I) rd hd6
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      rw [show (UInt256.ofNat 3).toNat = 3 from rfl]
      rw [hpad]
      have hM : MachineState.M 3 (32 - (modulusSizeWord I).toNat)
          (modulusSizeWord I).toNat = 3 := by
        generalize (modulusSizeWord I).toNat = n at hm ⊢
        cases n with
        | zero => simp [MachineState.M]
        | succ n =>
            simp only [MachineState.M]
            rw [show 32 - (n + 1) + (n + 1) = 32 by omega]
            decide
      rw [hM]
      simp)
    (by rfl)
    (by simp)
  simpa using rdret

/-- Exact successful halt and gas threshold for the modulus-zero/one word path. -/
theorem smallModulusExactGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode) (hvalue : I.weiValue = ⟨0⟩)
    (hb : (baseSizeWord I).toNat ≤ 32)
    (he : (exponentSizeWord I).toNat ≤ 32)
    (hm : (modulusSizeWord I).toNat ≤ 32)
    (hmod : (modulusWord I).toNat ≤ 1) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ) (smallResult I) 349 := by
  obtain ⟨k, rd0⟩ := reachSmallModulusBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hvalue hb he hm hmod
  simpa [smallResult] using returnWordExact hm rd0

end Modexp
