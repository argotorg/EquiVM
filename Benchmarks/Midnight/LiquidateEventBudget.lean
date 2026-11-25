import Benchmarks.Midnight.RuntimeBlocks_024
import Benchmarks.Midnight.TransferBudget
import Benchmarks.Midnight.StorageWriteGas

variable {fork : Ethereum.Fork}

/-! The liquidation event's memory writes retain the transfer budget. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight
open midnightBlocks

set_option maxRecDepth 10000

-- GENERALIZES the generated block at 5548 with memory funding across storage reads.
theorem liquidate_block_5548_funded {root : UInt256} {credit : Nat} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hb : TransferBudget root credit mem aw C)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5548) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), TransferBudget root credit (midnight_block_5548_memory (ee := ee) (mem := mem) (x1 := x1) (x6 := x6) (x7 := x7)) (M (M (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 608) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) C' ∧
      RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5636) (midnight_block_5548_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) (midnight_block_5548_memory (ee := ee) (mem := mem) (x1 := x1) (x6 := x6) (x7 := x7)) (M (M (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 608) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 672) (by native_decide) (by evm_ov)
  have r4 := RD.genMload r3 (by native_decide) (by evm_ov)
  have b4 := transferBudgetAt (root := root) (credit := credit) r4
    (by transfer_budget hb)
  obtain ⟨_, _, hc5, r5⟩ := RD.sloadMono r4 (by native_decide) (by evm_ov)
  have b5 := transferBudgetAt (root := root) (credit := credit) r5 (b4.mono hc5)
  have r6 := r5.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r7 := r6.shr (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 672) (by native_decide) (by evm_ov)
  have r10 := RD.genMload r9 (by native_decide) (by evm_ov)
  have r11 := r10.add (by native_decide) (by evm_ov)
  have b11 := transferBudgetAt (root := root) (credit := credit) r11
    (by transfer_budget b5)
  obtain ⟨_, _, hc12, r12⟩ := RD.sloadMono r11 (by native_decide) (by evm_ov)
  have b12 := transferBudgetAt (root := root) (credit := credit) r12 (b11.mono hc12)
  have r13 := r12.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r14 := r13.shr (by native_decide) (by evm_ov)
  have r15 := r14.swap1 (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r17 := RD.genMload r16 (by native_decide) (by evm_ov)
  have r18 := r17.swap3 (by native_decide) (by evm_ov)
  have r19 := r18.caller (by native_decide) (by evm_ov)
  have r20 := r19.dup5 (by native_decide) (by evm_ov)
  have r21 := RD.genMstore r20 (by native_decide) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 640) (by native_decide) (by evm_ov)
  have r23 := RD.genMload r22 (by native_decide) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r25 := r24.dup6 (by native_decide) (by evm_ov)
  have r26 := r25.add (by native_decide) (by evm_ov)
  have r27 := RD.genMstore r26 (by native_decide) (by evm_ov)
  have r28 := r27.push2 (UInt256.ofNat 608) (by native_decide) (by evm_ov)
  have r29 := RD.genMload r28 (by native_decide) (by evm_ov)
  have r30 := r29.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r31 := r30.dup6 (by native_decide) (by evm_ov)
  have r32 := r31.add (by native_decide) (by evm_ov)
  have r33 := RD.genMstore r32 (by native_decide) (by evm_ov)
  have b33 := transferBudgetAt (root := root) (credit := credit) r33
    (by transfer_budget b12)
  have r34 := r33.iszero (by native_decide) (by evm_ov)
  have r35 := r34.iszero (by native_decide) (by evm_ov)
  have r36 := r35.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r37 := r36.dup5 (by native_decide) (by evm_ov)
  have r38 := r37.add (by native_decide) (by evm_ov)
  have r39 := RD.genMstore r38 (by native_decide) (by evm_ov)
  have r40 := r39.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r41 := r40.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r42 := r41.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r43 := r42.shl (by native_decide) (by evm_ov)
  have r44 := r43.sub (by native_decide) (by evm_ov)
  have r45 := r44.dup10 (by native_decide) (by evm_ov)
  have r46 := r45.and (by native_decide) (by evm_ov)
  have r47 := r46.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r48 := r47.dup5 (by native_decide) (by evm_ov)
  have r49 := r48.add (by native_decide) (by evm_ov)
  have r50 := RD.genMstore r49 (by native_decide) (by evm_ov)
  have b50 := transferBudgetAt (root := root) (credit := credit) r50
    (by transfer_budget b33)
  have r51 := r50.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r52 := r51.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r53 := r52.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r54 := r53.shl (by native_decide) (by evm_ov)
  have r55 := r54.sub (by native_decide) (by evm_ov)
  have r56 := r55.dup11 (by native_decide) (by evm_ov)
  have r57 := r56.and (by native_decide) (by evm_ov)
  have r58 := r57.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r59 := r58.dup5 (by native_decide) (by evm_ov)
  have r60 := r59.add (by native_decide) (by evm_ov)
  have r61 := RD.genMstore r60 (by native_decide) (by evm_ov)
  have r62 := r61.dup8 (by native_decide) (by evm_ov)
  have r63 := r62.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r64 := r63.dup5 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5636)) r64 (by native_decide)
  have bFinal := transferBudgetAt (root := root) (credit := credit) rFinal
    (by transfer_budget b50)
  exact ⟨_, _, bFinal, rFinal⟩

end Benchmarks.Midnight
