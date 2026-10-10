import Benchmarks.UniswapV3.Pool.ModifyPositionMiddleFinalSource
import Benchmarks.UniswapV3.Pool.ModifyPositionMiddleAmountTrace
import Benchmarks.UniswapV3.Pool.LiquidityDeltaInternal
import Benchmarks.UniswapV3.Pool.PoolLiquidityStoreTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000
attribute [local irreducible] modifyPositionUpdatedState modifyPositionMiddleStoresState

theorem modifyPositionMiddleFinalX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q key free : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : ModifyPositionArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ (modifyPositionMiddleStoresState v a evm))
    (rd : RD (deployedRuntime v) ee g s0 ⟨16705⟩
      (EVM.wordOfInt (signedAmountDeltaResult true (modifyPositionMiddleAmountArgs a evm true)) ::
        modifyPositionMiddleLiquidity v a evm :: p :: ⟨0⟩ ::
        EVM.wordOfInt (signedAmountDeltaResult false (modifyPositionMiddleAmountArgs a evm false)) ::
        key :: q :: R) mem aw rdata σ k C)
    (ha : a.Fits) (hm : HeapMemory mem aw free) (hq : ModifyPositionParamsMemory mem q a)
    (hb : q.toNat + 128 ≤ 2 ^ 200) (hperm : ee.perm = true) (hov : R.length + 15 ≤ 1024) :
    (ExecBlock config (modifyPositionMiddleAssigned1Frame v a evm) (modifyPositionMiddleStoresState v a evm)
      (modifyPositionMiddleBody.drop 11) .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    (ExecBlock config (modifyPositionMiddleAssigned1Frame v a evm) (modifyPositionMiddleStoresState v a evm)
      (modifyPositionMiddleBody.drop 11)
      (.ok (modifyPositionMiddleFinalFrame v a evm) (modifyPositionMiddleFinalState v a evm)) ∧
      ∃ σ' aw' k' C', SourceState s0 ee σ' (modifyPositionMiddleFinalState v a evm) ∧
      RD (deployedRuntime v) ee g s0 ⟨16801⟩
        (p :: EVM.wordOfInt (signedAmountDeltaResult true (modifyPositionMiddleAmountArgs a evm true)) ::
          EVM.wordOfInt (signedAmountDeltaResult false (modifyPositionMiddleAmountArgs a evm false)) ::
          key :: q :: R) mem aw' rdata σ' k' C' ∧ HeapMemory mem aw' free) := by
  obtain ⟨aw1, k1, C1, r1, hm1⟩ := modifyPositionMiddleDeltaEntryX (v := v) a rd hm hq hb (by omega)
  have hx : Int.ofNat (modifyPositionMiddleLiquidity v a evm).toNat < 2 ^ 128 := by
    have h := poolLiquidityWord_lt (modifyPositionUpdatedState v a evm).accountMap
      (modifyPositionUpdatedState v a evm).executionEnv
    change (Int.ofNat (modifyPositionMiddleLiquidity v a evm).toNat) < Int.ofNat (2 ^ 128)
    exact Int.ofNat_lt.mpr h
  have r1' : RD (deployedRuntime v) ee g s0 ⟨13807⟩
      (EVM.wordOfInt a.delta :: EVM.wordOfInt (Int.ofNat (modifyPositionMiddleLiquidity v a evm).toNat) ::
        ⟨16721⟩ :: modifyPositionMiddleLiquidity v a evm :: p ::
        EVM.wordOfInt (signedAmountDeltaResult true (modifyPositionMiddleAmountArgs a evm true)) ::
        EVM.wordOfInt (signedAmountDeltaResult false (modifyPositionMiddleAmountArgs a evm false)) ::
        key :: q :: R) mem aw1 rdata σ k1 C1 := by
    simpa only [wordOfInt_ofNat_toNat] using r1
  rcases liquidityDeltaInternalX (v := v) (Int.ofNat (modifyPositionMiddleLiquidity v a evm).toNat)
    a.delta (modifyPositionMiddleAssigned1Frame v a evm) (modifyPositionMiddleStoresState v a evm)
    modifyPositionMiddleDeltaExprs "__c12" rfl (evalModifyPositionMiddleDeltaExprs v a evm _)
    r1' (Int.ofNat_nonneg _) hx ha.2.2.1 ha.2.2.2
    (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by evm_ov) with
      ⟨hcall, rr⟩ | ⟨hcall, _, kr, Cr, rr⟩
  · exact Or.inl ⟨ExecBlock.consRevert hcall, rr⟩
  · obtain ⟨σ', ks, Cs, hs', rs⟩ := poolLiquidityStoreX (v := v)
      (modifyPositionMiddleStoresState v a evm) hs rr hperm (by evm_ov)
    exact Or.inr ⟨ExecBlock.consNormal hcall (ExecBlock.consNormal
      (modifyPositionMiddleLiquidityStoreSource v a evm _) ExecBlock.nil),
      σ', aw1, ks, Cs, hs', rs, hm1⟩

end Benchmarks.UniswapV3.Pool
