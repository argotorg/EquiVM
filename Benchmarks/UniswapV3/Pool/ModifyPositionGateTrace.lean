import Benchmarks.UniswapV3.Pool.ModifyPositionMemory
import Benchmarks.UniswapV3.Pool.ModifyPositionPrefix
import Benchmarks.UniswapV3.Pool.CheckTicks

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem modifyPositionGateX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : ModifyPositionArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 ⟨16233⟩ (q :: ret :: R) mem aw rdata σ k C)
    (ha : a.Fits) (hm : HeapMemory mem aw p) (hq : ModifyPositionParamsMemory mem q a)
    (hqp : q.toNat + 128 ≤ p.toNat) (hp : p.toNat ≤ 2 ^ 200) (hov : R.length + 13 ≤ 1024) :
    (ExecFuncBody config (modifyPositionFrame (immStore v) a) evm modifyPositionFunction.body .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    (evm.executionEnv.codeOwner = v.original ∧ validTicks a.lower a.upper ∧ ∃ aw' k' C',
      RD (deployedRuntime v) ee g s0 ⟨16264⟩ (⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: q :: ret :: R)
        mem aw' rdata σ k' C' ∧ HeapMemory mem aw' p) := by
  have r0 := uniswapV3Pool_block_16233 (immWords := wordsOf (immStore v)) (by evm_ov)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [uniswapV3Pool_block_16233_stack] at r0
  rcases noDelegateCallX (v := v) r0
    (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by evm_ov) with
    ⟨hr, he⟩ | ⟨he, k1, C1, r1⟩
  · exact Or.inl ⟨modifyPositionDelegateReverts v evm a (by rw [hs.env]; exact he), hr⟩
  · have hself : evm.executionEnv.codeOwner = v.original := by rw [hs.env]; exact he
    have hqw : q.toNat + 128 < UInt256.size := by change _ < 2 ^ 256; omega
    have hq32 := uadd_word_ofNat_toNat q 32 (show q.toNat + 32 < UInt256.size by omega)
    have hq64 := uadd_word_ofNat_toNat q 64 (show q.toNat + 64 < UInt256.size by omega)
    have r2 := uniswapV3Pool_block_16246 (immWords := wordsOf (immStore v)) (by evm_ov)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
    simp only [uniswapV3Pool_block_16246_stack, u256_add_comm (UInt256.ofNat 32) q,
      u256_add_comm (UInt256.ofNat 64) q, hq.load_lower hqw, hq.load_upper hqw] at r2
    have hm2 := (hm.expand32 (q + UInt256.ofNat 32) (by rw [hq32]; omega)).expand32
      (q + UInt256.ofNat 64) (by rw [hq64]; omega)
    have hlo : normalizeInt (.sint ⟨24, by decide⟩) (Int.ofNat (EVM.wordOfInt a.lower).toNat) =
        a.lower := by
      rw [normalizeInt_wordOfInt, normalizeSint_eq_self ⟨24, by decide⟩ _ ha.1.1 ha.1.2]
    have hup : normalizeInt (.sint ⟨24, by decide⟩) (Int.ofNat (EVM.wordOfInt a.upper).toNat) =
        a.upper := by
      rw [normalizeInt_wordOfInt, normalizeSint_eq_self ⟨24, by decide⟩ _ ha.2.1.1 ha.2.1.2]
    have hc := checkTicksX (v := v) r2
      (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by evm_ov)
    dsimp only at hc
    rw [hlo, hup] at hc
    rcases hc with ⟨hr, ht⟩ | ⟨ht, k3, C3, r3⟩
    · exact Or.inl ⟨modifyPositionTicksReverts v evm a hself ht, hr⟩
    · exact Or.inr ⟨hself, ht, _, k3, C3, r3, hm2⟩

end Benchmarks.UniswapV3.Pool
