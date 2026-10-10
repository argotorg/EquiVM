import Benchmarks.UniswapV3.Pool.PositionUpdateLiquidityTrace
import Benchmarks.UniswapV3.Pool.PositionUpdateFeeTrace
import Benchmarks.UniswapV3.Pool.PositionUpdateFinishTrace
import Benchmarks.UniswapV3.Pool.PositionUpdateSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem positionUpdateX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : PositionUpdateArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 ⟨21559⟩
      (a.growth1 :: a.growth0 :: EVM.wordOfInt a.delta :: solcMappingSlot ⟨7⟩ a.key :: ret :: R)
      mem aw rdata σ k C)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 160 ≤ 2 ^ 200)
    (hdlo : -(2 ^ 127 : Int) ≤ a.delta) (hdhi : a.delta < 2 ^ 127)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 25 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧ ¬ positionUpdateLiquidityValid a evm) ∨
      (positionUpdateLiquidityValid a evm ∧
        ((RDstatic (deployedRuntime v) g s0 ∧ ee.perm = false) ∨
          (ee.perm = true ∧ ∃ σ' k' C' aw', SourceState s0 ee σ' (positionUpdateFinalState a evm) ∧
            RD (deployedRuntime v) ee g s0 ret R
              (wordArrayAllocMem mem p (positionSnapshotWords a.key σ ee)) aw' rdata σ' k' C' ∧
            HeapMemory (wordArrayAllocMem mem p (positionSnapshotWords a.key σ ee)) aw' (p + ⟨160⟩)))) := by
  obtain ⟨aw1, k1, C1, r1, heap1, region1⟩ := positionSnapshotX (v := v) rd hm hb (by omega)
  have region : WordArrayMemory (wordArrayAllocMem mem p (positionSnapshotWords a.key σ ee)) p
      (positionSnapshotWords a.key evm.accountMap evm.executionEnv) := by
    simpa only [hs.accounts, hs.env] using region1
  rcases positionUpdateLiquidityX (v := v) a evm r1 region heap1.active hb hdlo hdhi (by omega) with
    hrev | ⟨hv, aw2, k2, C2, r2, ha2⟩
  · exact Or.inl hrev
  · refine Or.inr ⟨hv, ?_⟩
    obtain ⟨aw3, k3, C3, r3, ha3⟩ := positionUpdateFeeX (v := v) a evm r2 region ha2 hb hov
    obtain ⟨k4, C4, r4⟩ := positionUpdateFirstWriteX (v := v) a evm r3 hdlo hdhi (by omega)
    cases hp : ee.perm
    · exact Or.inl ⟨positionUpdateFirstWriteStaticX (v := v) a evm r4 hp (by omega), rfl⟩
    · apply Or.inr
      refine ⟨rfl, ?_⟩
      obtain ⟨σ5, k5, C5, hs5, r5⟩ := positionUpdateLiquidityStoreX (v := v) a evm hs r4 hp (by omega)
      obtain ⟨k6, C6, hs6, r6⟩ := positionUpdateGrowthX (v := v) a evm hs5 r5 hp (by omega)
      obtain ⟨σ7, k7, C7, hs7, r7⟩ := positionUpdateFinishX (v := v) a evm hs6 r6 hp hret (by omega)
      exact ⟨σ7, k7, C7, aw3, hs7, r7, heap1.size, heap1.free, heap1.lower, heap1.gap, ha3⟩

end Benchmarks.UniswapV3.Pool
