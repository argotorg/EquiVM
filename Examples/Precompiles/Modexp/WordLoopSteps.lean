import Examples.Precompiles.Modexp.WordLoop

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem isZero_eq_zero {e : UInt256} (he : e ≠ ⟨0⟩) :
    UInt256.isZero e = ⟨0⟩ := by
  simp [UInt256.isZero, UInt256.eq0, he, UInt256.fromBool, Bool.toUInt256]
  native_decide

private theorem isZero_zero_eq_one : UInt256.isZero ⟨0⟩ = ⟨1⟩ := by
  native_decide

private theorem land_one_eq_zero {e : UInt256} (heven : e.toNat % 2 = 0) :
    UInt256.land e ⟨1⟩ = ⟨0⟩ := by
  apply u256_inj
  rw [uInt256_land_one_toNat, heven]
  rfl

private theorem land_one_eq_one {e : UInt256} (hodd : e.toNat % 2 = 1) :
    UInt256.land e ⟨1⟩ = ⟨1⟩ := by
  apply u256_inj
  rw [uInt256_land_one_toNat, hodd]
  rfl

private theorem wordHeaderDecodes :
    decode runtimeBytecode ⟨0x173⟩ = some (.JUMPDEST, .none) ∧
    decode runtimeBytecode ⟨0x174⟩ = some (.ISZERO, .none) ∧
    decode runtimeBytecode ⟨0x175⟩ = some (.Push .PUSH2, some (⟨0x161⟩, 2)) ∧
    decode runtimeBytecode ⟨0x178⟩ = some (.JUMPI, .none) ∧
    decode runtimeBytecode ⟨0x179⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) ∧
    decode runtimeBytecode ⟨0x17b⟩ = some (.DUP4, .none) ∧
    decode runtimeBytecode ⟨0x17c⟩ = some (.AND, .none) ∧
    decode runtimeBytecode ⟨0x17d⟩ = some (.Push .PUSH2, some (⟨0x190⟩, 2)) ∧
    decode runtimeBytecode ⟨0x180⟩ = some (.JUMPI, .none) := by
  simpa only [List.cons.injEq, and_true] using wordLoopHeaderDecodes

/-- A nonzero even exponent reaches the shared square/shift block in exactly 39 gas. -/
theorem wordLoopDispatchEven {cA gh bl σ σ₀ A I} {g : Sat256}
    {e b m acc : UInt256} {k C : Nat}
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨0x173⟩
      [e, b, m, e, acc, UInt256.sub ⟨32⟩ (modulusSizeWord I), modulusSizeWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hne : e ≠ ⟨0⟩) (heven : e.toNat % 2 = 0) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨0x181⟩
      [b, m, e, acc, UInt256.sub ⟨32⟩ (modulusSizeWord I), modulusSizeWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' (C + 39) := by
  rcases wordHeaderDecodes with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8⟩
  have hz := isZero_eq_zero hne
  have hbit := land_one_eq_zero heven
  have rd := evm_run rd0 with [
    known jumpdest hd0,
    known iszero hd1,
    known push2 hd2 ⟨0x161⟩,
    known jumpiNT hd3 hz,
    known push1 hd4 ⟨1⟩,
    known dup4 hd5,
    known and hd6,
    known push2 hd7 ⟨0x190⟩,
    known jumpiNT hd8 hbit ]
  exact ⟨_, (rd.withPC (by native_decide)).withIndices rfl (by omega)⟩

/-- A nonzero odd exponent reaches its accumulator-update block in exactly 39 gas. -/
theorem wordLoopDispatchOdd {cA gh bl σ σ₀ A I} {g : Sat256}
    {e b m acc : UInt256} {k C : Nat}
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨0x173⟩
      [e, b, m, e, acc, UInt256.sub ⟨32⟩ (modulusSizeWord I), modulusSizeWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hne : e ≠ ⟨0⟩) (hodd : e.toNat % 2 = 1) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨0x190⟩
      [b, m, e, acc, UInt256.sub ⟨32⟩ (modulusSizeWord I), modulusSizeWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' (C + 39) := by
  rcases wordHeaderDecodes with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8⟩
  have hz := isZero_eq_zero hne
  have hbit := land_one_eq_one hodd
  have rd := evm_run rd0 with [
    known jumpdest hd0,
    known iszero hd1,
    known push2 hd2 ⟨0x161⟩,
    known jumpiNT hd3 hz,
    known push1 hd4 ⟨1⟩,
    known dup4 hd5,
    known and hd6,
    known push2 hd7 ⟨0x190⟩,
    known jumpiT hd8 (by rw [hbit]; native_decide) jumpDest_190 ]
  exact ⟨_, (rd.withIndices rfl (by omega))⟩

/-- Square the base, shift the exponent, and return to the loop header (44 gas). -/
theorem wordLoopEvenStep {cA gh bl σ σ₀ A I} {g : Sat256}
    {e b m acc : UInt256} {k C : Nat}
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨0x181⟩
      [b, m, e, acc, UInt256.sub ⟨32⟩ (modulusSizeWord I), modulusSizeWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨0x173⟩
      [UInt256.shiftRight e ⟨1⟩, UInt256.mulMod b b m, m,
        UInt256.shiftRight e ⟨1⟩, acc,
        UInt256.sub ⟨32⟩ (modulusSizeWord I), modulusSizeWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' (C + 44) := by
  have hd :
      decode runtimeBytecode ⟨0x181⟩ = some (.JUMPDEST, .none) ∧
      decode runtimeBytecode ⟨0x182⟩ = some (.DUP1, .none) ∧
      decode runtimeBytecode ⟨0x183⟩ = some (.DUP3, .none) ∧
      decode runtimeBytecode ⟨0x184⟩ = some (.SWAP2, .none) ∧
      decode runtimeBytecode ⟨0x185⟩ = some (.MULMOD, .none) ∧
      decode runtimeBytecode ⟨0x186⟩ = some (.SWAP2, .none) ∧
      decode runtimeBytecode ⟨0x187⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) ∧
      decode runtimeBytecode ⟨0x189⟩ = some (.SHR, .none) ∧
      decode runtimeBytecode ⟨0x18a⟩ = some (.SWAP2, .none) ∧
      decode runtimeBytecode ⟨0x18b⟩ = some (.DUP3, .none) ∧
      decode runtimeBytecode ⟨0x18c⟩ = some (.Push .PUSH2, some (⟨0x173⟩, 2)) ∧
      decode runtimeBytecode ⟨0x18f⟩ = some (.JUMP, .none) := by
    simpa only [List.cons.injEq, and_true] using wordLoopEvenDecodes
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11⟩
  have rd := evm_run rd0 with [
    known jumpdest hd0,
    known dup1 hd1,
    known dup3 hd2,
    known swap2 hd3,
    known mulmod hd4,
    known swap2 hd5,
    known push1 hd6 ⟨1⟩,
    known shr hd7,
    known swap2 hd8,
    known dup3 hd9,
    known push2 hd10 ⟨0x173⟩,
    known jump hd11 jumpDest_173 ]
  exact ⟨_, (rd.withIndices rfl (by omega))⟩

/-- Update the accumulator on an odd bit and enter the shared square/shift block (43 gas). -/
theorem wordLoopOddPrefix {cA gh bl σ σ₀ A I} {g : Sat256}
    {e b m acc : UInt256} {k C : Nat}
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨0x190⟩
      [b, m, e, acc, UInt256.sub ⟨32⟩ (modulusSizeWord I), modulusSizeWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨0x181⟩
      [b, m, e, UInt256.mulMod acc b m,
        UInt256.sub ⟨32⟩ (modulusSizeWord I), modulusSizeWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' (C + 43) := by
  have hd :
      decode runtimeBytecode ⟨0x190⟩ = some (.JUMPDEST, .none) ∧
      decode runtimeBytecode ⟨0x191⟩ = some (.SWAP3, .none) ∧
      decode runtimeBytecode ⟨0x192⟩ = some (.DUP2, .none) ∧
      decode runtimeBytecode ⟨0x193⟩ = some (.DUP5, .none) ∧
      decode runtimeBytecode ⟨0x194⟩ = some (.DUP2, .none) ∧
      decode runtimeBytecode ⟨0x195⟩ = some (.SWAP3, .none) ∧
      decode runtimeBytecode ⟨0x196⟩ = some (.MULMOD, .none) ∧
      decode runtimeBytecode ⟨0x197⟩ = some (.SWAP4, .none) ∧
      decode runtimeBytecode ⟨0x198⟩ = some (.SWAP1, .none) ∧
      decode runtimeBytecode ⟨0x199⟩ = some (.POP, .none) ∧
      decode runtimeBytecode ⟨0x19a⟩ = some (.Push .PUSH2, some (⟨0x181⟩, 2)) ∧
      decode runtimeBytecode ⟨0x19d⟩ = some (.JUMP, .none) := by
    simpa only [List.cons.injEq, and_true] using wordLoopOddDecodes
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11⟩
  have rd := evm_run rd0 with [
    known jumpdest hd0,
    known swap3 hd1,
    known dup2 hd2,
    known dup5 hd3,
    known dup2 hd4,
    known swap3 hd5,
    known mulmod hd6,
    known swap4 hd7,
    known swap1 hd8,
    known pop hd9,
    known push2 hd10 ⟨0x181⟩,
    known jump hd11 jumpDest_181 ]
  exact ⟨_, (rd.withIndices rfl (by omega))⟩

/-- The zero-exponent header check and shared return block consume exactly 29 gas. -/
theorem wordLoopExit {cA gh bl σ σ₀ A I} {g : Sat256}
    {b m acc : UInt256} {k C : Nat}
    (hm : (modulusSizeWord I).toNat ≤ 32)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨0x173⟩
      [⟨0⟩, b, m, ⟨0⟩, acc,
        UInt256.sub ⟨32⟩ (modulusSizeWord I), modulusSizeWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ) (wordResult acc I) (C + 29) := by
  rcases wordHeaderDecodes with ⟨hd0, hd1, hd2, hd3, _, _, _, _, _⟩
  have rd := evm_run rd0 with [
    known jumpdest hd0,
    known iszero hd1,
    known push2 hd2 ⟨0x161⟩,
    known jumpiT hd3 (by rw [isZero_zero_eq_one]; native_decide) jumpDest_161 ]
  have hret := returnWordExact hm rd
  simpa only [Nat.add_assoc] using hret

/-- One nonzero even exponent bit costs exactly 83 gas. -/
theorem wordLoopIterationEven {cA gh bl σ σ₀ A I} {g : Sat256}
    {e b m acc : UInt256} {k C : Nat}
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨0x173⟩
      [e, b, m, e, acc, UInt256.sub ⟨32⟩ (modulusSizeWord I), modulusSizeWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hne : e ≠ ⟨0⟩) (heven : e.toNat % 2 = 0) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨0x173⟩
      [UInt256.shiftRight e ⟨1⟩, UInt256.mulMod b b m, m,
        UInt256.shiftRight e ⟨1⟩, acc,
        UInt256.sub ⟨32⟩ (modulusSizeWord I), modulusSizeWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' (C + 83) := by
  obtain ⟨k', rd1⟩ := wordLoopDispatchEven rd0 hne heven
  obtain ⟨k'', rd2⟩ := wordLoopEvenStep rd1
  exact ⟨k'', rd2.withIndices rfl (by omega)⟩

/-- One nonzero odd exponent bit costs exactly 126 gas. -/
theorem wordLoopIterationOdd {cA gh bl σ σ₀ A I} {g : Sat256}
    {e b m acc : UInt256} {k C : Nat}
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨0x173⟩
      [e, b, m, e, acc, UInt256.sub ⟨32⟩ (modulusSizeWord I), modulusSizeWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hne : e ≠ ⟨0⟩) (hodd : e.toNat % 2 = 1) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨0x173⟩
      [UInt256.shiftRight e ⟨1⟩, UInt256.mulMod b b m, m,
        UInt256.shiftRight e ⟨1⟩, UInt256.mulMod acc b m,
        UInt256.sub ⟨32⟩ (modulusSizeWord I), modulusSizeWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' (C + 126) := by
  obtain ⟨k', rd1⟩ := wordLoopDispatchOdd rd0 hne hodd
  obtain ⟨k'', rd2⟩ := wordLoopOddPrefix rd1
  obtain ⟨k''', rd3⟩ := wordLoopEvenStep rd2
  exact ⟨k''', rd3.withIndices rfl (by omega)⟩

end Modexp
