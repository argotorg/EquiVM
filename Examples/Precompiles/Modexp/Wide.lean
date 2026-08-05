import Examples.Precompiles.Modexp.WordBridge

/-!
# ModExp arbitrary-width dispatch

The deployed runtime short-circuits the three `≤ 32` tests.  These exact traces characterize each
way execution can fall through to the arbitrary-width implementation at PC `0x3e`.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem gt32_zero {w : UInt256} (h : w.toNat ≤ 32) :
    UInt256.gt w ⟨32⟩ = ⟨0⟩ := by
  apply ugt_zero
  simpa using h

private theorem gt32_one {w : UInt256} (h : 32 < w.toNat) :
    UInt256.gt w ⟨32⟩ = ⟨1⟩ := by
  apply ugt_one
  simpa using h

/-- The base length is the first failing word-size check. -/
theorem reachWideBase {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode) (hvalue : I.weiValue = ⟨0⟩)
    (hb1024 : (baseSizeWord I).toNat ≤ 1024)
    (he1024 : (exponentSizeWord I).toNat ≤ 1024)
    (hm1024 : (modulusSizeWord I).toNat ≤ 1024)
    (hb : 32 < (baseSizeWord I).toNat) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨0x3e⟩
      [exponentSizeWord I, baseSizeWord I, modulusSizeWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k 161 := by
  obtain ⟨k, rd0⟩ := reachBoundsPassed
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hvalue hb1024 he1024 hm1024
  rcases wordDispatchFacts with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, _, _, _, _, _, _,
    _, _, hd15, hd16, hd17, hd18, _, _, _, _, _, _, _, _, hd27, hd28, hd29⟩
  have hbgt := gt32_one hb
  have rd := evm_run rd0 with [
    known push1 hd0 ⟨32⟩,
    known dup3 hd1,
    known gt hd2,
    known iszero hd3,
    known dup1 hd4,
    known push2 hd5 ⟨0x1a9⟩,
    known jumpiNT hd6 (by rw [hbgt]; native_decide),
    known jumpdest hd15,
    known dup1 hd16,
    known push2 hd17 ⟨0x19e⟩,
    known jumpiNT hd18 (by rw [hbgt]; native_decide),
    known jumpdest hd27,
    known push2 hd28 ⟨0x12e⟩,
    known jumpiNT hd29 (by rw [hbgt]; native_decide) ]
  exact ⟨_, (rd.withPC (by native_decide)).withIndices rfl (by omega)⟩

/-- The base fits one word but the exponent length does not. -/
theorem reachWideExponent {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode) (hvalue : I.weiValue = ⟨0⟩)
    (hb1024 : (baseSizeWord I).toNat ≤ 1024)
    (he1024 : (exponentSizeWord I).toNat ≤ 1024)
    (hm1024 : (modulusSizeWord I).toNat ≤ 1024)
    (hb : (baseSizeWord I).toNat ≤ 32)
    (he : 32 < (exponentSizeWord I).toNat) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨0x3e⟩
      [exponentSizeWord I, baseSizeWord I, modulusSizeWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k 187 := by
  obtain ⟨k, rd0⟩ := reachBoundsPassed
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hvalue hb1024 he1024 hm1024
  rcases wordDispatchFacts with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8,
    hd9, hd10, hd11, hd12, hd13, hd14, hd15, hd16, hd17, hd18, _, _, _, _, _, _, _,
    _, hd27, hd28, hd29⟩
  have hbgt := gt32_zero hb
  have hegt := gt32_one he
  have rd := evm_run rd0 with [
    known push1 hd0 ⟨32⟩,
    known dup3 hd1,
    known gt hd2,
    known iszero hd3,
    known dup1 hd4,
    known push2 hd5 ⟨0x1a9⟩,
    known jumpiT hd6 (by rw [hbgt]; native_decide) jumpDest_1a9,
    known jumpdest hd7,
    known pop hd8,
    known push1 hd9 ⟨32⟩,
    known dup2 hd10,
    known gt hd11,
    known iszero hd12,
    known push2 hd13 ⟨0x33⟩,
    known jump hd14 jumpDest_33,
    known jumpdest hd15,
    known dup1 hd16,
    known push2 hd17 ⟨0x19e⟩,
    known jumpiNT hd18 (by rw [hegt]; native_decide),
    known jumpdest hd27,
    known push2 hd28 ⟨0x12e⟩,
    known jumpiNT hd29 (by rw [hegt]; native_decide) ]
  exact ⟨_, (rd.withPC (by native_decide)).withIndices rfl (by omega)⟩

/-- Base and exponent lengths fit one word, but the modulus length does not. -/
theorem reachWideModulus {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode) (hvalue : I.weiValue = ⟨0⟩)
    (hb1024 : (baseSizeWord I).toNat ≤ 1024)
    (he1024 : (exponentSizeWord I).toNat ≤ 1024)
    (hm1024 : (modulusSizeWord I).toNat ≤ 1024)
    (hb : (baseSizeWord I).toNat ≤ 32)
    (he : (exponentSizeWord I).toNat ≤ 32)
    (hm : 32 < (modulusSizeWord I).toNat) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨0x3e⟩
      [exponentSizeWord I, baseSizeWord I, modulusSizeWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k 213 := by
  obtain ⟨k, rd0⟩ := reachBoundsPassed
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hvalue hb1024 he1024 hm1024
  rcases wordDispatchFacts with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8,
    hd9, hd10, hd11, hd12, hd13, hd14, hd15, hd16, hd17, hd18, hd19, hd20,
    hd21, hd22, hd23, hd24, hd25, hd26, hd27, hd28, hd29⟩
  have hbgt := gt32_zero hb
  have hegt := gt32_zero he
  have hmgt := gt32_one hm
  have rd := evm_run rd0 with [
    known push1 hd0 ⟨32⟩,
    known dup3 hd1,
    known gt hd2,
    known iszero hd3,
    known dup1 hd4,
    known push2 hd5 ⟨0x1a9⟩,
    known jumpiT hd6 (by rw [hbgt]; native_decide) jumpDest_1a9,
    known jumpdest hd7,
    known pop hd8,
    known push1 hd9 ⟨32⟩,
    known dup2 hd10,
    known gt hd11,
    known iszero hd12,
    known push2 hd13 ⟨0x33⟩,
    known jump hd14 jumpDest_33,
    known jumpdest hd15,
    known dup1 hd16,
    known push2 hd17 ⟨0x19e⟩,
    known jumpiT hd18 (by rw [hegt]; native_decide) jumpDest_19e,
    known jumpdest hd19,
    known pop hd20,
    known push1 hd21 ⟨32⟩,
    known dup4 hd22,
    known gt hd23,
    known iszero hd24,
    known push2 hd25 ⟨0x39⟩,
    known jump hd26 jumpDest_39,
    known jumpdest hd27,
    known push2 hd28 ⟨0x12e⟩,
    known jumpiNT hd29 (by rw [hmgt]; native_decide) ]
  exact ⟨_, (rd.withPC (by native_decide)).withIndices rfl (by omega)⟩

end Modexp
