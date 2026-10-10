import Benchmarks.UniswapV3.Pool.SwapLiquidityLoad
import Benchmarks.UniswapV3.Pool.SwapLiquidityStore
import Benchmarks.UniswapV3.Pool.LiquidityDeltaRawCost

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapLiquidityX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat}
    {aw p q free exactWord cache snap dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapArgs) (s : SwapStateData) (d : SwapIterationData) (net : Int)
    (frame : Frame) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3851⟩
      ([EVM.wordOfInt net, ⟨0⟩, q] ++
        swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
      mem aw rdata σ k C)
    (hf : frame.contract = contract)
    (hz : frame.locals.get? "zeroForOne" = some (.bool a.zeroForOne))
    (hstate : frame.locals.get? "state" = some s.value)
    (hnet : frame.locals.get? "liquidityNet" = some (.int net))
    (hm : HeapMemory mem aw free) (hs : SwapStateMemory mem p s)
    (hd : SwapIterationMemory mem q d) (hfit : s.Fits)
    (hnetfit : -(2 ^ 127 : Int) ≤ net ∧ net < 2 ^ 127)
    (hp : 96 ≤ p.toNat) (hdisj : p.toNat + 224 ≤ q.toNat)
    (hb : p.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 24 ≤ 1024) :
    (ExecBlock config frame evm (swapInitializedBody.drop 2) .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecBlock config frame evm (swapInitializedBody.drop 2)
        (.ok (swapLiquidityFrame frame s a.zeroForOne net) evm) ∧
      ∃ mem' aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
        RD (deployedRuntime v) ee g s0 ⟨3893⟩
          (q :: swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
          mem' aw' rdata σ k' C' ∧ HeapMemory mem' aw' free ∧
        SwapStateMemory mem' p (swapLiquidityState s a.zeroForOne net) ∧
        SwapIterationMemory mem' q d ∧ MemoryPrefix mem mem' p.toNat ∧
        aw.toNat ≤ aw'.toNat) := by
  have hex1 := swapLiquidityNegSource (evm := evm) a.zeroForOne net hz hnet
  have hsget := (swapLiquidityNegFrame_get frame a.zeroForOne net "state" (by decide)).trans
    hstate
  have hnget := swapLiquidityNegFrame_net frame a.zeroForOne net hnet
  have hfc : (swapLiquidityNegFrame frame a.zeroForOne net).contract = contract := by
    cases a.zeroForOne <;> exact hf
  have he := evalSwapLiquidityArgs (evm := evm) s (swapLiquidityNet a.zeroForOne net) hsget hnget
  obtain ⟨aw1, k1, C1, hC1, r1, hm1, hmono1⟩ :=
    swapLiquidityLoadX (v := v) a s net rd hm hs hb (by omega)
  have hx : normalizeInt (.uint ⟨128, by decide⟩) (Int.ofNat s.liquidity.toNat) =
      Int.ofNat s.liquidity.toNat := by
    apply normalizeInt_uint_eq_self ⟨128, by decide⟩ (Int.ofNat s.liquidity.toNat)
    · rw [Int.ofNat_eq_natCast]; omega
    · exact Int.ofNat_lt.mpr hfit.2.2.2.2.2
  have hy := swapLiquidityRaw_normalize a.zeroForOne net hnetfit
  rcases liquidityDeltaRawInternalMonoX (v := v) s.liquidity (swapLiquidityRaw a.zeroForOne net)
      (Int.ofNat s.liquidity.toNat) (swapLiquidityNet a.zeroForOne net)
      (swapLiquidityNegFrame frame a.zeroForOne net) evm swapLiquidityArgs "__c14" hfc he r1 hx hy
      (by rw [uniswapV3PoolPatchedValidJumps v]; native_decide)
      (by change R.length + 15 + 9 ≤ 1024; omega) with
    ⟨hex2, hr⟩ | ⟨hex2, k2, C2, hC2, r2⟩
  · exact Or.inl ⟨ExecBlock.consNormal hex1 (ExecBlock.consRevert hex2), hr⟩
  · obtain ⟨aw3, k3, C3, hC3, r3, hm3, hs3, hd3, hp3, hmono3⟩ :=
      swapLiquidityStoreX (v := v) s d (EVM.wordOfInt (swapLiquidityValue s a.zeroForOne net))
        (s.liquidity + swapLiquidityRaw a.zeroForOne net) (swapLiquidityRaw a.zeroForOne net)
        r2 hm1 hs hd (liquidityDeltaRawOutput _ _ _ _ hx hy) hp hdisj hb
        (by change R.length + 12 + 7 ≤ 1024; omega)
    exact Or.inr ⟨ExecBlock.consNormal hex1 (ExecBlock.consNormal hex2
      (ExecBlock.consNormal (swapLiquidityAssignSource s a.zeroForOne net hstate) .nil)),
      _, aw3, k3, C3, by omega, r3, hm3, hs3, hd3, hp3, hmono1.trans hmono3⟩

end Benchmarks.UniswapV3.Pool
