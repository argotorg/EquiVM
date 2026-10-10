import Benchmarks.UniswapV3.Pool.Balance
import Benchmarks.UniswapV3.Pool.BalanceCaller
import Benchmarks.UniswapV3.Pool.FlashPrefix
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_023
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_024

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def flashBalance0Return (after : Bool) : UInt256 := if after then ⟨6991⟩ else ⟨6715⟩
def flashBalance1Return (after : Bool) : UInt256 := if after then ⟨7003⟩ else ⟨6727⟩
def flashBalanceName (after second : Bool) : Ident :=
  if after then (if second then "balance1After" else "balance0After")
  else (if second then "balance1Before" else "balance0Before")

def flashBalanceStmts (after : Bool) : List Stmt :=
  [.internalCall "balance0" [] (flashBalanceName after false),
    .internalCall "balance1" [] (flashBalanceName after true)]

theorem flashBalanceStmts_eq (after : Bool) :
    flashBalanceStmts after = (flashTransition.body.drop (if after then 15 else 8)).take 2 := by
  cases after <;> rfl

def flashBalancesFrame (v : UniswapV3PoolImmutables) (locals : Store)
    (after : Bool) (bal0 bal1 : UInt256) : Frame :=
  {contract := contract, immutables := immStore v,
    locals := (locals.insert (flashBalanceName after false) (.int (Int.ofNat bal0.toNat))).insert
      (flashBalanceName after true) (.int (Int.ofNat bal1.toNat))}

theorem flashBalanceNextX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw bal0 junk : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (after : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (flashBalance0Return after) (bal0 :: junk :: R)
      mem aw rdata σ k C) (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨15901⟩
      (flashBalance1Return after :: ⟨0⟩ :: bal0 :: R) mem aw rdata σ k' C' := by
  cases after
  · exact ⟨_, _, uniswapV3Pool_block_6715 (immWords := wordsOf (immStore v)) hov
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd⟩
  · exact ⟨_, _, uniswapV3Pool_block_6991 (immWords := wordsOf (immStore v)) hov
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd⟩

set_option maxHeartbeats 1000000 in
theorem flashBalancesX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat} {aw p : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (locals : Store) (after : Bool)
    (rd : RD (deployedRuntime v) ee g s0 ⟨15572⟩ (flashBalance0Return after :: ⟨0⟩ :: R)
      mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hm : HeapMemory mem aw p)
    (hzero : memLoad (UInt256.ofNat 96) (balanceInputMem mem p ee.codeOwner) = ⟨0⟩)
    (hb : p.toNat + 2 ^ 140 ≤ 2 ^ 200) (hov : R.length + 20 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ExecBlock config {contract := contract, locals := locals, immutables := immStore v}
        evm (flashBalanceStmts after) .reverted) ∨
    ∃ evm' σ' out mem' aw' next bal0 bal1 k' C', SourceState s0 ee σ' evm' ∧
      ExecBlock config {contract := contract, locals := locals, immutables := immStore v}
        evm (flashBalanceStmts after) (.ok (flashBalancesFrame v locals after bal0 bal1) evm') ∧
      RD (deployedRuntime v) ee g s0 (flashBalance1Return after)
        (bal1 :: ⟨0⟩ :: bal0 :: R) mem' aw' out σ' k' C' ∧
      HeapMemory mem' aw' next ∧ 128 ≤ mem'.size ∧ memLoad (UInt256.ofNat 96) mem' = ⟨0⟩ ∧
      next.toNat ≤ p.toNat + 2 ^ 139 + 262 := by
  have hret0 : (D_J (deployedRuntime v) 0).contains (flashBalance0Return after) = true := by
    rw [uniswapV3PoolPatchedValidJumps v]; cases after <;> native_decide
  rcases balanceEntryCallX (v := v) false rd hs hm hzero (by omega) hret0 (by evm_ov) with
    ⟨rdBad, hbad⟩ | ⟨evm1, σ1, out1, mem1, aw1, p1, k1, C1, hs1, hgood0, rd1, hm1, hpref1, hp1⟩
  · exact Or.inl ⟨rdBad, ExecBlock.consRevert
      (poolBalanceReverts v locals (flashBalanceName after false) evm false hbad)⟩
  · have hp68 : (p + (⟨68⟩ : UInt256)).toNat = p.toNat + 68 :=
      uadd_word_ofNat_toNat p 68 (by change _ < 2 ^ 256; omega)
    have hmem1 : 128 ≤ mem1.size := by
      have hh := hpref1.size
      rw [balanceInputMem_size _ _ _ hm.lower] at hh
      have hlo := hm.lower
      omega
    have hz1 : memLoad (UInt256.ofNat 96) mem1 = ⟨0⟩ := by
      rw [MemoryPrefix.memLoad hpref1 (UInt256.ofNat 96) (by decide) (by change 128 ≤ _; rw [hp68]; have hlo := hm.lower; omega)
        (by change 128 ≤ _; rw [balanceInputMem_size _ _ _ hm.lower]; have hlo := hm.lower; omega)]
      exact hzero
    have hstmt0 := poolBalanceReturns v locals (flashBalanceName after false) evm evm1 false
      (balanceValue out1) (balanceCallFrame v false true out1) hgood0
    obtain ⟨kNext, CNext, rdNext⟩ := flashBalanceNextX (v := v) after rd1 (by evm_ov)
    have hret1 : (D_J (deployedRuntime v) 0).contains (flashBalance1Return after) = true := by
      rw [uniswapV3PoolPatchedValidJumps v]; cases after <;> native_decide
    rcases balanceX (v := v) true rdNext hs1 hm1 hmem1 hz1
        (by rw [hp68] at hp1; omega) hret1 (by evm_ov) with
      ⟨rdBad, hbad⟩ | ⟨evm2, σ2, out2, mem2, aw2, p2, k2, C2, hs2, hgood1, rd2, hm2, hpref2, hp2⟩
    · exact Or.inl ⟨rdBad, ExecBlock.consNormal hstmt0 (ExecBlock.consRevert
        (poolBalanceReverts v _ (flashBalanceName after true) evm1 true hbad))⟩
    · refine Or.inr ⟨evm2, σ2, out2, mem2, aw2, p2, balanceValue out1, balanceValue out2,
        k2, C2, hs2, ?_, rd2, hm2, le_trans hmem1 hpref2.size, ?_, ?_⟩
      · exact ExecBlock.consNormal hstmt0 (ExecBlock.consNormal
          (poolBalanceReturns v _ (flashBalanceName after true) evm1 evm2 true (balanceValue out2)
            (balanceCallFrame v true true out2) hgood1) ExecBlock.nil)
      · rw [MemoryPrefix.memLoad hpref2 (UInt256.ofNat 96) (by decide) (by exact hm1.lower) hmem1, hz1]
      · rw [hp68] at hp1
        omega

end Benchmarks.UniswapV3.Pool
