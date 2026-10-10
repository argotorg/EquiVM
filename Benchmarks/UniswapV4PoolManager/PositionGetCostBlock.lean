import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_018

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

def positionGetActiveWords (aw params free : UInt256) : UInt256 :=
  (M (M (M (M (M (M (M (M (M (M (M (M (M (M (M aw params (⟨32⟩ : UInt256)) (params + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (free + (UInt256.ofNat 38)) (⟨32⟩ : UInt256)) (free + (UInt256.ofNat 6)) (⟨32⟩ : UInt256)) (free + (UInt256.ofNat 3)) (⟨32⟩ : UInt256)) free (⟨32⟩ : UInt256)) (free + (UInt256.ofNat 12)) (UInt256.ofNat 58)) (free + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (free + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) free (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64))

private theorem positionGetCostStep (a b : Nat) : a ≤ b+(a-b) := by omega

private theorem positionGetMemoryCostSum {C Cr c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 : Nat}
    (h : C+1+3+3+3+(c1-c0+3)+3+3+3+(c2-c1+3)+3+3+(c3-c2+3)+3+3+3+3+(c4-c3+3)+3+3+3+3+(c5-c4+3)+3+3+3+3+(c6-c5+3)+3+(c7-c6+3)+2+3+3+3+3+(c8-c7+42)+3+3+3+3+3+(c9-c8+3)+3+3+3+3+(c10-c9+3)+(c11-c10+3)+2+(c12-c11+3)+3+3+(c13-c12+3)+3+3+(c14-c13+3)+3+2+(c15-c14+42)+3+3+3 ≤ Cr) : c15+C ≤ Cr+3+3+c0 := by
  have hs1 := positionGetCostStep c1 c0
  have hs2 := positionGetCostStep c2 c1
  have hs3 := positionGetCostStep c3 c2
  have hs4 := positionGetCostStep c4 c3
  have hs5 := positionGetCostStep c5 c4
  have hs6 := positionGetCostStep c6 c5
  have hs7 := positionGetCostStep c7 c6
  have hs8 := positionGetCostStep c8 c7
  have hs9 := positionGetCostStep c9 c8
  have hs10 := positionGetCostStep c10 c9
  have hs11 := positionGetCostStep c11 c10
  have hs12 := positionGetCostStep c12 c11
  have hs13 := positionGetCostStep c13 c12
  have hs14 := positionGetCostStep c14 c13
  have hs15 := positionGetCostStep c15 c14
  omega (config := { splitNatSub := false })

/-- Retain the memory cost through the final SLOAD, whose generated summary hides its counter.
The prefix uses the decoded instructions of block 5802; its memory and stack are the supplied summaries. -/
theorem positionGetCostBlock {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (h : RD (immutableLayout.runtime poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5802) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), Cₘ (positionGetActiveWords aw x0 (memLoad (UInt256.ofNat 64) mem))+C ≤ C'+Cₘ aw ∧ RD (immutableLayout.runtime poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5915) (poolManager_block_5802_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) (poolManager_block_5802_memory (mem := mem) (x0 := x0) (x8 := x8) (x10 := x10)) (positionGetActiveWords aw x0 (memLoad (UInt256.ofNat 64) mem)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5802⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 160) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5803⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5805⟩ : UInt256), UInt8.ofNat 115, .Push .PUSH20, some ((UInt256.ofNat 1461501637330902918203684832716283019655932542975), 20), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup3 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5826⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMload r4 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5827⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.and (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5828⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap2 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5829⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.add (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5830⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := RD.genMload r8 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5831⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.swap1 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5832⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 64) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5833⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := RD.genMload r11 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5835⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.swap2 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5836⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 38) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5837⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 38), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.dup4 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5839⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.add (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5840⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := RD.genMstore r16 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5841⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.dup10 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5842⟩ : UInt256), UInt8.ofNat 137, .DUP10, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 6) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5843⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 6), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.dup4 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5845⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.add (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5846⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := RD.genMstore r21 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5847⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.dup12 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5848⟩ : UInt256), UInt8.ofNat 139, .DUP12, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 3) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5849⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 3), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.dup4 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5851⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.add (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5852⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := RD.genMstore r26 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5853⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.dup2 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5854⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r29 := RD.genMstore r28 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5855⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r30 := r29.push0 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5856⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r31 := r30.push1 (UInt256.ofNat 58) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5857⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 58), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r32 := r31.push1 (UInt256.ofNat 12) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5859⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 12), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r33 := r32.dup4 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5861⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r34 := r33.add (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5862⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r35 := RD.genKeccak256 r34 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5863⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r36 := r35.swap2 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5864⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r37 := r36.dup2 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5865⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r38 := r37.push1 (UInt256.ofNat 64) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5866⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r39 := r38.dup3 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5868⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r40 := r39.add (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5869⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r41 := RD.genMstore r40 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5870⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r42 := r41.dup2 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5871⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r43 := r42.push1 (UInt256.ofNat 32) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5872⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r44 := r43.dup3 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5874⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r45 := r44.add (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5875⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r46 := RD.genMstore r45 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5876⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r47 := RD.genMstore r46 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5877⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r48 := r47.push0 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5878⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r49 := RD.genMstore r48 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5879⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r50 := r49.push1 (UInt256.ofNat 6) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5880⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 6), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r51 := r50.push1 (UInt256.ofNat 128) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5882⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r52 := RD.genMload r51 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5884⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r53 := r52.add (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5885⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r54 := r53.push1 (UInt256.ofNat 32) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5886⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r55 := RD.genMstore r54 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5888⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r56 := r55.push1 (UInt256.ofNat 64) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5889⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r57 := r56.push0 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5891⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r58 := RD.genKeccak256 r57 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5892⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r59 := r58.swap8 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5893⟩ : UInt256), UInt8.ofNat 151, .SWAP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r60 := r59.pushConst (UInt256.ofNat 340282366920938463463374607431768211455) (width := 16) (op := .PUSH16) (by decide) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5894⟩ : UInt256), UInt8.ofNat 111, .Push .PUSH16, some ((UInt256.ofNat 340282366920938463463374607431768211455), 16), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r61 := r60.dup10 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5911⟩ : UInt256), UInt8.ofNat 137, .DUP10, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, hcost, r62⟩ := RD.sloadMono r61 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5912⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r63 := r62.and (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5913⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r64 := r63.swap10 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨5914⟩ : UInt256), UInt8.ofNat 153, .SWAP10, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5915)) r64 (by native_decide)
  refine ⟨_, _, ?_, rFinal⟩
  clear * - hcost
  dsimp only [positionGetActiveWords, memExpansionCost] at hcost ⊢
  exact positionGetMemoryCostSum hcost

end Benchmarks.UniswapV4PoolManager
