import Benchmarks.UniswapV3Pool.BurnPositionUpdateTokensOwedBridge

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.UniswapV3Pool

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolBurnZeroDeltaPositionUpdateToMulDiv0StartConcrete
    {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (htickLt :
      tickSpacingSint24Value (burnTickLowerWord ee) <
        tickSpacingSint24Value (burnTickUpperWord ee))
    (hzero : burnAmountCleanWord ee = ⟨0⟩)
    (hliq :
      burnPositionUpdateSlot0Packed
          (solcSlotWord σ ee (burnPositionBaseSlotWord σ ee)) ≠ ⟨0⟩)
    (h : RD code ee g s0 ⟨21387⟩
      (solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        ⟨5⟩ :: ⟨19510⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        burnPositionBaseSlotWord σ ee :: slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee)) ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        UInt256.ofNat ee.source.val :: ⟨16428⟩ :: ⟨256⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        burnAmountCleanWord ee :: burnTickUpperCleanWord ee ::
        burnTickLowerCleanWord ee :: ret :: R)
      (burnPositionKeyMappingMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k C)
    (hov : R.length + 82 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨13017⟩
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩ ::
        burnPositionUpdateSlot0Packed
          (solcSlotWord σ ee (burnPositionBaseSlotWord σ ee)) ::
        UInt256.sub (burnTickGetInside0Word σ ee)
          (solcSlotWord σ ee (burnPositionBaseSlotWord σ ee + (⟨1⟩ : UInt256))) ::
        ⟨21769⟩ :: ⟨0⟩ ::
        burnPositionUpdateSlot0Packed
          (solcSlotWord σ ee (burnPositionBaseSlotWord σ ee)) ::
        burnPositionKeyNewFreePtrWord ::
        burnTickGetInside1Word σ ee :: burnTickGetInside0Word σ ee ::
        UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee)) ::
        burnPositionBaseSlotWord σ ee :: ⟨19527⟩ ::
        burnTickGetInside1Word σ ee :: burnTickGetInside0Word σ ee ::
        ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        burnPositionBaseSlotWord σ ee :: slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee)) ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        UInt256.ofNat ee.source.val :: ⟨16428⟩ :: ⟨256⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        burnAmountCleanWord ee :: burnTickUpperCleanWord ee ::
        burnTickLowerCleanWord ee :: ret :: R)
      (burnPositionUpdateMem5 σ ee
        (solcSlotWord σ ee (burnPositionBaseSlotWord σ ee))
        (burnPositionBaseSlotWord σ ee))
      (UInt256.ofNat 22) rdata (cA, σ) k' C' := by
  let inside1 := burnTickGetInside1Word σ ee
  let inside0 := burnTickGetInside0Word σ ee
  let posBase := burnPositionBaseSlotWord σ ee
  let delta := UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee))
  let postFreeR : List UInt256 :=
    ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
    ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
    burnAmountCleanWord ee :: burnTickUpperCleanWord ee ::
    burnTickLowerCleanWord ee :: ret :: R
  obtain ⟨_, _, hrdReturn⟩ :=
    uniswapV3PoolBurnFeeGrowthInsideEntryReturnConcrete
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (ret := ret) (R := R) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch htickLt h (by omega)
  obtain ⟨_, _, hrdEntry⟩ :=
    uniswapV3PoolBurnFeeGrowthInsideEnterPositionUpdate
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1) (inside0 := inside0)
      (z0 := ⟨0⟩) (z1 := ⟨0⟩) (z2 := ⟨0⟩) (z3 := ⟨0⟩)
      (fee1 := solcSlotWord σ ee ⟨2⟩) (fee0 := solcSlotWord σ ee ⟨1⟩)
      (posBase := posBase) (tick := slot0TickReturnWord σ ee)
      (delta := delta)
      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee))
      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee))
      (owner := UInt256.ofNat ee.source.val) (ret := ⟨16428⟩) (free := ⟨256⟩)
      (R := postFreeR)
      hpatch
      (by simpa [inside1, inside0, posBase, delta] using hrdReturn)
      (by simp [postFreeR] at hov ⊢; omega)
  obtain ⟨_, _, hrdSlot0⟩ :=
    uniswapV3PoolBurnPositionUpdateLoadSlot0
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1) (inside0 := inside0) (delta := delta)
      (posBase := posBase) (retPos := ⟨19527⟩)
      (inside1' := inside1) (inside0' := inside0) (z2 := ⟨0⟩) (z3 := ⟨0⟩)
      (fee1 := solcSlotWord σ ee ⟨2⟩) (fee0 := solcSlotWord σ ee ⟨1⟩)
      (posBase' := posBase) (tick := slot0TickReturnWord σ ee)
      (delta' := delta)
      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee))
      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee))
      (owner := UInt256.ofNat ee.source.val) (ret := ⟨16428⟩) (free := ⟨256⟩)
      (R := postFreeR) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch hrdEntry (by simp [postFreeR] at hov ⊢; omega)
  obtain ⟨_, _, hrdPacked⟩ :=
    uniswapV3PoolBurnPositionUpdateStoreSlot0Packed
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (pos0 := solcSlotWord σ ee posBase)
      (inside1 := inside1) (inside0 := inside0) (delta := delta)
      (posBase := posBase) (retPos := ⟨19527⟩)
      (inside1' := inside1) (inside0' := inside0) (z2 := ⟨0⟩) (z3 := ⟨0⟩)
      (fee1 := solcSlotWord σ ee ⟨2⟩) (fee0 := solcSlotWord σ ee ⟨1⟩)
      (posBase' := posBase) (tick := slot0TickReturnWord σ ee)
      (delta' := delta)
      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee))
      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee))
      (owner := UInt256.ofNat ee.source.val) (ret := ⟨16428⟩) (free := ⟨256⟩)
      (R := postFreeR) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch hrdSlot0 (by simp [postFreeR] at hov ⊢; omega)
  obtain ⟨_, _, hrdFee0⟩ :=
    uniswapV3PoolBurnPositionUpdateStoreFeeGrowthInside0Last
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1) (inside0 := inside0) (delta := delta)
      (posBase := posBase) (retPos := ⟨19527⟩)
      (inside1' := inside1) (inside0' := inside0) (z2 := ⟨0⟩) (z3 := ⟨0⟩)
      (fee1 := solcSlotWord σ ee ⟨2⟩) (fee0 := solcSlotWord σ ee ⟨1⟩)
      (posBase' := posBase) (tick := slot0TickReturnWord σ ee)
      (delta' := delta)
      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee))
      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee))
      (owner := UInt256.ofNat ee.source.val) (ret := ⟨16428⟩) (free := ⟨256⟩)
      (R := postFreeR) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch (by simpa [inside1, inside0, posBase, delta] using hrdPacked)
      (by simp [postFreeR] at hov ⊢; omega)
  obtain ⟨_, _, hrdFee1⟩ :=
    uniswapV3PoolBurnPositionUpdateStoreFeeGrowthInside1Last
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1) (inside0 := inside0) (delta := delta)
      (posBase := posBase) (retPos := ⟨19527⟩)
      (inside1' := inside1) (inside0' := inside0) (z2 := ⟨0⟩) (z3 := ⟨0⟩)
      (fee1 := solcSlotWord σ ee ⟨2⟩) (fee0 := solcSlotWord σ ee ⟨1⟩)
      (posBase' := posBase) (tick := slot0TickReturnWord σ ee)
      (delta' := delta)
      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee))
      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee))
      (owner := UInt256.ofNat ee.source.val) (ret := ⟨16428⟩) (free := ⟨256⟩)
      (R := postFreeR) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch hrdFee0 (by simp [postFreeR] at hov ⊢; omega)
  obtain ⟨_, _, hrdTokens0⟩ :=
    uniswapV3PoolBurnPositionUpdateStoreTokensOwed0
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1) (inside0 := inside0) (delta := delta)
      (posBase := posBase) (retPos := ⟨19527⟩)
      (inside1' := inside1) (inside0' := inside0) (z2 := ⟨0⟩) (z3 := ⟨0⟩)
      (fee1 := solcSlotWord σ ee ⟨2⟩) (fee0 := solcSlotWord σ ee ⟨1⟩)
      (posBase' := posBase) (tick := slot0TickReturnWord σ ee)
      (delta' := delta)
      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee))
      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee))
      (owner := UInt256.ofNat ee.source.val) (ret := ⟨16428⟩) (free := ⟨256⟩)
      (R := postFreeR) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch hrdFee1 (by simp [postFreeR] at hov ⊢; omega)
  obtain ⟨_, _, hrdTokens1⟩ :=
    uniswapV3PoolBurnPositionUpdateStoreTokensOwed1
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1) (inside0 := inside0) (delta := delta)
      (posBase := posBase) (retPos := ⟨19527⟩)
      (inside1' := inside1) (inside0' := inside0) (z2 := ⟨0⟩) (z3 := ⟨0⟩)
      (fee1 := solcSlotWord σ ee ⟨2⟩) (fee0 := solcSlotWord σ ee ⟨1⟩)
      (posBase' := posBase) (tick := slot0TickReturnWord σ ee)
      (delta' := delta)
      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee))
      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee))
      (owner := UInt256.ofNat ee.source.val) (ret := ⟨16428⟩) (free := ⟨256⟩)
      (R := postFreeR) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch hrdTokens0 (by simp [postFreeR] at hov ⊢; omega)
  have hdelta : UInt256.signextend ⟨15⟩ delta = ⟨0⟩ := by
    dsimp [delta]
    rw [hzero]
    native_decide
  obtain ⟨_, _, hrdFallthrough⟩ :=
    uniswapV3PoolBurnPositionUpdateLiquidityDeltaZeroFallthrough
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1) (inside0 := inside0) (delta := delta)
      (posBase := posBase) (retPos := ⟨19527⟩)
      (inside1' := inside1) (inside0' := inside0) (z2 := ⟨0⟩) (z3 := ⟨0⟩)
      (fee1 := solcSlotWord σ ee ⟨2⟩) (fee0 := solcSlotWord σ ee ⟨1⟩)
      (posBase' := posBase) (tick := slot0TickReturnWord σ ee)
      (delta' := delta)
      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee))
      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee))
      (owner := UInt256.ofNat ee.source.val) (ret := ⟨16428⟩) (free := ⟨256⟩)
      (R := postFreeR) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch hdelta hrdTokens1 (by simp [postFreeR] at hov ⊢; omega)
  obtain ⟨_, _, hrdNonzero⟩ :=
    uniswapV3PoolBurnPositionUpdateLiquidityNonzeroJump
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1) (inside0 := inside0) (delta := delta)
      (posBase := posBase) (retPos := ⟨19527⟩)
      (inside1' := inside1) (inside0' := inside0) (z2 := ⟨0⟩) (z3 := ⟨0⟩)
      (fee1 := solcSlotWord σ ee ⟨2⟩) (fee0 := solcSlotWord σ ee ⟨1⟩)
      (posBase' := posBase) (tick := slot0TickReturnWord σ ee)
      (delta' := delta)
      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee))
      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee))
      (owner := UInt256.ofNat ee.source.val) (ret := ⟨16428⟩) (free := ⟨256⟩)
      (R := postFreeR) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch hliq hrdFallthrough (by simp [postFreeR] at hov ⊢; omega)
  obtain ⟨_, _, hrdReload⟩ :=
    uniswapV3PoolBurnPositionUpdateReloadLiquidity
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1) (inside0 := inside0) (delta := delta)
      (posBase := posBase) (retPos := ⟨19527⟩)
      (inside1' := inside1) (inside0' := inside0) (z2 := ⟨0⟩) (z3 := ⟨0⟩)
      (fee1 := solcSlotWord σ ee ⟨2⟩) (fee0 := solcSlotWord σ ee ⟨1⟩)
      (posBase' := posBase) (tick := slot0TickReturnWord σ ee)
      (delta' := delta)
      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee))
      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee))
      (owner := UInt256.ofNat ee.source.val) (ret := ⟨16428⟩) (free := ⟨256⟩)
      (R := postFreeR) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch hrdNonzero (by simp [postFreeR] at hov ⊢; omega)
  obtain ⟨_, _, hrd13017⟩ :=
    uniswapV3PoolBurnPositionUpdateStartMulDiv0
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1) (inside0 := inside0) (delta := delta)
      (posBase := posBase) (retPos := ⟨19527⟩)
      (inside1' := inside1) (inside0' := inside0) (z2 := ⟨0⟩) (z3 := ⟨0⟩)
      (fee1 := solcSlotWord σ ee ⟨2⟩) (fee0 := solcSlotWord σ ee ⟨1⟩)
      (posBase' := posBase) (tick := slot0TickReturnWord σ ee)
      (delta' := delta)
      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee))
      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee))
      (owner := UInt256.ofNat ee.source.val) (ret := ⟨16428⟩) (free := ⟨256⟩)
      (R := postFreeR) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch hrdReload (by simp [postFreeR] at hov ⊢; omega)
  exact ⟨_, _, by simpa [inside1, inside0, posBase, delta, postFreeR] using hrd13017⟩

end Benchmarks.UniswapV3Pool
