import Benchmarks.Midnight.LiquidateBadDebtSubtract
import Benchmarks.Midnight.PositionUpdateStorage
import Benchmarks.Midnight.CollateralBlocksGas

variable {fork : Ethereum.Fork}

/-! The packed debt write preserves paid gas and detects a static-context violation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

local macro "liquidate_stack" : tactic =>
  `(tactic| (simp only [List.append, List.length_append, List.length_cons, List.length_nil]; omega))

-- GENERALIZES the generated block at 7454 with static failure and cost monotonicity.
theorem midnightLiquidateBadDebtWrite {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw value reverseRep rep maxDebt price pos dp dl borrower badDebt : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 21 ≤ 1024)
    (h : RD fork midnightBytecode I g s0 ⟨7454⟩
      ([value, uint128Mask, reverseRep, rep, maxDebt, price, pos, dp, dl, borrower, badDebt] ++ R)
      mem aw rdata σ k C) :
    let σ' := storeLow128Accounts σ I (pos + ⟨2⟩) value
    let marketWord := solcSlotWordAt (memLoad (UInt256.ofNat 672) mem) σ' I
    (I.perm = false ∧ RDstatic fork midnightBytecode g s0) ∨
    (I.perm = true ∧ ∃ k' C', C + memExpansionCost aw (UInt256.ofNat 672) ⟨32⟩ ≤ C' ∧
      RD fork midnightBytecode I g s0 ⟨19421⟩
        ([UInt256.shiftRight marketWord ⟨128⟩, ⟨7523⟩, ⟨7530⟩, badDebt, ⟨6721⟩,
          low128 marketWord, ⟨7536⟩, ⟨4204⟩, ⟨7541⟩, ⟨7571⟩, marketWord,
          reverseRep, rep, maxDebt, price, pos, dp, dl, borrower, badDebt] ++ R)
        mem (M aw (UInt256.ofNat 672) ⟨32⟩) rdata σ' k' C') := by
  dsimp only
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by liquidate_stack)
  have r2 := r1.and (by native_decide) (by liquidate_stack)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by liquidate_stack)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by liquidate_stack)
  have r5 := r4.push1 (UInt256.ofNat 128) (by native_decide) (by liquidate_stack)
  have r6 := r5.shl (by native_decide) (by liquidate_stack)
  have r7 := r6.sub (by native_decide) (by liquidate_stack)
  have r8 := r7.not (by native_decide) (by liquidate_stack)
  have r9 := r8.push1 (UInt256.ofNat 2) (by native_decide) (by liquidate_stack)
  have r10 := r9.dup8 (by native_decide) (by liquidate_stack)
  have r11 := r10.add (by native_decide) (by liquidate_stack)
  obtain ⟨_, _, hc12, r12⟩ := RD.sloadMono r11 (by native_decide) (by liquidate_stack)
  have r13 := r12.and (by native_decide) (by liquidate_stack)
  have r14 := r13.or (by native_decide) (by liquidate_stack)
  have r15 := r14.push1 (UInt256.ofNat 2) (by native_decide) (by liquidate_stack)
  have r16 := r15.dup7 (by native_decide) (by liquidate_stack)
  have r17 := r16.add (by native_decide) (by liquidate_stack)
  by_cases hp : I.perm = true
  · obtain ⟨_, _, hc18, r18⟩ := sstoreMono r17 hp (by native_decide) (by liquidate_stack)
    have r19 := r18.push2 (UInt256.ofNat 672) (by native_decide) (by liquidate_stack)
    have r20 := RD.genMload r19 (by native_decide) (by liquidate_stack)
    obtain ⟨_, _, hc21, r21⟩ := RD.sloadMono r20 (by native_decide) (by liquidate_stack)
    have r22 := r21.push2 (UInt256.ofNat 7571) (by native_decide) (by liquidate_stack)
    have r23 := r22.push2 (UInt256.ofNat 7541) (by native_decide) (by liquidate_stack)
    have r24 := r23.push2 (UInt256.ofNat 4204) (by native_decide) (by liquidate_stack)
    have r25 := r24.push2 (UInt256.ofNat 7536) (by native_decide) (by liquidate_stack)
    have r26 := r25.dup14 (by native_decide) (by liquidate_stack)
    have r27 := r26.push2 (UInt256.ofNat 6721) (by native_decide) (by liquidate_stack)
    have r28 := r27.push1 (UInt256.ofNat 1) (by native_decide) (by liquidate_stack)
    have r29 := r28.push1 (UInt256.ofNat 1) (by native_decide) (by liquidate_stack)
    have r30 := r29.push1 (UInt256.ofNat 128) (by native_decide) (by liquidate_stack)
    have r31 := r30.shl (by native_decide) (by liquidate_stack)
    have r32 := r31.sub (by native_decide) (by liquidate_stack)
    have r33 := r32.dup8 (by native_decide) (by liquidate_stack)
    have r34 := r33.and (by native_decide) (by liquidate_stack)
    have r35 := r34.swap2 (by native_decide) (by liquidate_stack)
    have r36 := r35.push2 (UInt256.ofNat 7530) (by native_decide) (by liquidate_stack)
    have r37 := r36.push2 (UInt256.ofNat 7523) (by native_decide) (by liquidate_stack)
    have r38 := r37.dup10 (by native_decide) (by liquidate_stack)
    have r39 := r38.push1 (UInt256.ofNat 128) (by native_decide) (by liquidate_stack)
    have r40 := r39.shr (by native_decide) (by liquidate_stack)
    have r41 := r40.push2 (UInt256.ofNat 19421) (by native_decide) (by liquidate_stack)
    have r42 := r41.jump (by native_decide) (by jump_dest) (by liquidate_stack)
    have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19421)) r42 (by native_decide)
    refine Or.inr ⟨hp, _, _, ?_, by
      simpa only [uint128Mask_computed, storeLow128Accounts, setUint128LowWord, low128]
        using rFinal⟩
    omega
  · exact Or.inl ⟨Bool.eq_false_of_not_eq_true hp,
      r17.sstoreStatic (Bool.eq_false_of_not_eq_true hp) (by native_decide) (by liquidate_stack)⟩

end Benchmarks.Midnight
