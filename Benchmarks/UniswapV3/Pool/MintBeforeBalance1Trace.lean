import Benchmarks.UniswapV3.Pool.MintBeforeBalanceSource
import Benchmarks.UniswapV3.Pool.Balance
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_021

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem mintBeforeBalance1X {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat} {aw p amount0 amount1 balance0 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (locals : Store)
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 ⟨5949⟩
      (⟨0⟩ :: balance0 :: amount1 :: amount0 :: amount1 :: amount0 :: R) mem aw rdata σ k C)
    (ha : locals.get? "amount1" = some (.int (Int.ofNat amount1.toNat)))
    (hz : locals.get? "balance1Before" = some (.int 0))
    (hm : HeapMemory mem aw p) (hsize : 128 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hb : p.toNat + 2 ^ 138 + 163 ≤ 2 ^ 200) (hov : R.length + 24 ≤ 1024) :
    (ExecStmt config {contract := contract, locals := locals, immutables := immStore v} evm
        (mintBeforeBalanceStmt true) .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    (∃ evm' σ' out mem' aw' free balance1 k' C', SourceState s0 ee σ' evm' ∧
      ExecStmt config {contract := contract, locals := locals, immutables := immStore v} evm
        (mintBeforeBalanceStmt true)
        (.ok (mintBeforeBalanceFrame v locals true amount1 balance1) evm') ∧
      RD (deployedRuntime v) ee g s0 ⟨5966⟩
        (balance1 :: balance0 :: amount1 :: amount0 :: amount1 :: amount0 :: R)
        mem' aw' out σ' k' C' ∧ HeapMemory mem' aw' free ∧ MemoryPrefix mem mem' p.toNat ∧
      free.toNat ≤ p.toNat + 2 ^ 138 + 131 ∧ (amount1 = ⟨0⟩ → balance1 = ⟨0⟩)) := by
  by_cases h0 : amount1 = ⟨0⟩
  · subst amount1
    have r1 := uniswapV3Pool_block_5949_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    exact Or.inr ⟨evm, σ, rdata, mem, aw, p, ⟨0⟩, _, _, hs,
      mintBeforeBalanceSkip v locals evm true ha, r1, hm, MemoryPrefix.refl _ _, by omega, fun _ ↦ rfl⟩
  · have hp : 0 < amount1.toNat := Nat.pos_of_ne_zero (fun h ↦ h0 (uint256_toNat_eq_zero h))
    have r1 := uniswapV3Pool_block_5949_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (isZero_eq_zero_of_ne h0) rd
    have r2 := uniswapV3Pool_block_5956 (immWords := wordsOf (immStore v)) (by evm_ov)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
    rcases balanceX (v := v) true r2 hs hm hsize hzero hb
        (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest)
        (by change R.length + 6 + 18 ≤ 1024; omega) with
      ⟨rr, hc⟩ | ⟨evm', σ', out, mem', aw', free, k', C', hs', hc, rr, hm', hmem, hfree⟩
    · exact Or.inl ⟨mintBeforeBalanceReverts v locals evm true amount1 ha hp hc, rr⟩
    · have r3 := uniswapV3Pool_block_5963 (immWords := wordsOf (immStore v))
        (by change R.length + 5 + 2 ≤ 1024; omega) rr
      exact Or.inr ⟨evm', σ', out, mem', aw', free, balanceValue out, _, _, hs',
        mintBeforeBalanceReturns v locals evm evm' true amount1 (balanceValue out)
          (balanceCallFrame v true true out) ha hz hp hc, r3, hm', hmem, hfree, fun h ↦ False.elim (h0 h)⟩

end Benchmarks.UniswapV3.Pool
