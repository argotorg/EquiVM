import Benchmarks.UniswapV3Pool.IncreaseObservationCardinalityNextGrow

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

private theorem uniswapV3PoolIncreaseObservationCardinalityNextGrowTailPatchDisjoint
    {v : PoolImmutables} {pc : UInt256} (hlo : 5404 ≤ pc.toNat)
    (hhi : pc.toNat + 33 ≤ 6603) :
    ∀ p ∈ patches v, pc.toNat + 33 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;>
    omega

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolIncreaseObservationCardinalityNextGrowChangedTailReturn
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {R : List UInt256} {rdata : ByteArray} {obsNext : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨5521⟩
      (obsNext :: ⟨0⟩ :: increaseObservationCardinalityNextOldWord σ ee ::
        increaseObservationCardinalityNextArgWord ee :: ⟨857⟩ :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hperm : ee.perm = true)
    (hchanged :
      UInt256.land (increaseObservationCardinalityNextOldWord σ ee) (⟨65535⟩ : UInt256) ≠
        UInt256.land obsNext (⟨65535⟩ : UInt256))
    (hov : R.length + 12 ≤ 1024) :
    RDret code g s0
      (cA, sstoreAccountMap ee.codeOwner
        (sstoreAccountMap ee.codeOwner σ ⟨0⟩
          (increaseObservationCardinalityNextEvmObsNextSlotWord σ ee obsNext))
        ⟨0⟩
        (increaseObservationCardinalityNextEvmUnlockedTrueSlotWord
          (sstoreAccountMap ee.codeOwner σ ⟨0⟩
            (increaseObservationCardinalityNextEvmObsNextSlotWord σ ee obsNext)) ee))
      ByteArray.empty := by
  have hdecodeBody {pc : UInt256} (hlo : 5404 ≤ pc.toNat)
      (hhi : pc.toNat + 33 ≤ 6603) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 6603 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolIncreaseObservationCardinalityNextGrowTailPatchDisjoint hlo hhi)]
  have hd5521 : decode code ⟨5521⟩ = some (.JUMPDEST, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5522 : decode code ⟨5522⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5524 : decode code ⟨5524⟩ = some (.DUP1, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5525 : decode code ⟨5525⟩ = some (.SLOAD, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5526 : decode code ⟨5526⟩ = some (.Push .PUSH2, some (⟨65535⟩, 2)) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5529 : decode code ⟨5529⟩ = some (.DUP1, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5530 : decode code ⟨5530⟩ = some (.DUP5, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5531 : decode code ⟨5531⟩ = some (.AND, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5532 : decode code ⟨5532⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5534 : decode code ⟨5534⟩ = some (.Push .PUSH1, some (⟨216⟩, 1)) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5536 : decode code ⟨5536⟩ = some (.SHL, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5537 : decode code ⟨5537⟩ = some (.DUP2, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5538 : decode code ⟨5538⟩ = some (.MUL, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5539 : decode code ⟨5539⟩ = some (.Push .PUSH2, some (⟨65535⟩, 2)) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5542 : decode code ⟨5542⟩ = some (.Push .PUSH1, some (⟨216⟩, 1)) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5544 : decode code ⟨5544⟩ = some (.SHL, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5545 : decode code ⟨5545⟩ = some (.NOT, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5546 : decode code ⟨5546⟩ = some (.SWAP1, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5547 : decode code ⟨5547⟩ = some (.SWAP4, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5548 : decode code ⟨5548⟩ = some (.AND, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5549 : decode code ⟨5549⟩ = some (.SWAP3, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5550 : decode code ⟨5550⟩ = some (.SWAP1, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5551 : decode code ⟨5551⟩ = some (.SWAP3, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5552 : decode code ⟨5552⟩ = some (.OR, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5553 : decode code ⟨5553⟩ = some (.SWAP1, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5554 : decode code ⟨5554⟩ = some (.SWAP3, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5555 : decode code ⟨5555⟩ = some (.SSTORE, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5556 : decode code ⟨5556⟩ = some (.SWAP2, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5557 : decode code ⟨5557⟩ = some (.SWAP3, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5558 : decode code ⟨5558⟩ = some (.POP, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5559 : decode code ⟨5559⟩ = some (.DUP4, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5560 : decode code ⟨5560⟩ = some (.AND, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5561 : decode code ⟨5561⟩ = some (.EQ, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5562 : decode code ⟨5562⟩ = some (.Push .PUSH2, some (⟨5630⟩, 2)) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5565 : decode code ⟨5565⟩ = some (.JUMPI, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have rd5525 := evm_run h with [
    raw jumpdest hd5521 (by evm_ov),
    raw push1 ⟨0⟩ hd5522 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw dup1 hd5524 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega)]
  obtain ⟨_, _, rd5526₀⟩ := rd5525.sload hd5525 (by
    have h := hov
    simp only [List.length_cons] at h ⊢
    omega)
  have rd5555 := evm_run rd5526₀ with [
    raw push2 ⟨65535⟩ hd5526 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw dup1 hd5529 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw dup5 hd5530 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw and hd5531 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw push1 ⟨1⟩ hd5532 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw push1 ⟨216⟩ hd5534 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw shl hd5536 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw dup2 hd5537 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw mul hd5538 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw push2 ⟨65535⟩ hd5539 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw push1 ⟨216⟩ hd5542 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw shl hd5544 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw not hd5545 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw swap1 hd5546 (by evm_ov),
    raw swap4 hd5547 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw and hd5548 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw swap3 hd5549 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw swap1 hd5550 (by evm_ov),
    raw swap3 hd5551 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw lor hd5552 (by evm_ov),
    raw swap1 hd5553 (by evm_ov),
    raw swap3 hd5554 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega)]
  obtain ⟨_, _, rd5556₀⟩ := rd5555.sstore hperm hd5555 (by evm_ov)
  have rd5556 := by
    simpa [increaseObservationCardinalityNextEvmObsNextSlotWord,
      codeOwnerStorageWord] using rd5556₀
  have rd5565 := evm_run rd5556 with [
    raw swap2 hd5556 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw swap3 hd5557 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw pop hd5558 (by evm_ov),
    raw dup4 hd5559 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw and hd5560 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw eq hd5561 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw push2 ⟨5630⟩ hd5562 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega)]
  exact uniswapV3PoolIncreaseObservationCardinalityNextGrowEventTailReturn
    (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
    (R := R) (rdata := rdata) (obsNext := obsNext)
    (old := increaseObservationCardinalityNextOldWord σ ee)
    (arg := increaseObservationCardinalityNextArgWord ee) (cA := cA)
    (σ := sstoreAccountMap ee.codeOwner σ ⟨0⟩
      (increaseObservationCardinalityNextEvmObsNextSlotWord σ ee obsNext))
    hpatch rd5565 hperm hchanged hov

end Benchmarks.UniswapV3Pool
