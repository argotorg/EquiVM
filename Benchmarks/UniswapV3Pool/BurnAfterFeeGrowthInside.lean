import Benchmarks.UniswapV3Pool.BurnAfterFeeGlobals

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

theorem burnFeeGrowthInsideUpperIsZero_eq_zero_of_lt (σ : AccountMap)
    (I : ExecutionEnv)
    (hlt :
      tickSpacingSint24Value (slot0TickRawWord σ I) <
        tickSpacingSint24Value (burnTickUpperWord I)) :
    UInt256.isZero
        (UInt256.slt (UInt256.signextend ⟨2⟩ (slot0TickReturnWord σ I))
          (burnTickUpperFeeGrowthCompareWord I)) = ⟨0⟩ := by
  exact isZero_eq_zero_of_ne (burnFeeGrowthInsideUpperSlt_ne_zero σ I hlt)

theorem burnFeeGrowthInsideUpperIsZero_ne_zero_of_ge (σ : AccountMap)
    (I : ExecutionEnv)
    (hge :
      ¬ tickSpacingSint24Value (slot0TickRawWord σ I) <
        tickSpacingSint24Value (burnTickUpperWord I)) :
    UInt256.isZero
        (UInt256.slt (UInt256.signextend ⟨2⟩ (slot0TickReturnWord σ I))
          (burnTickUpperFeeGrowthCompareWord I)) ≠ ⟨0⟩ := by
  rw [burnFeeGrowthInsideUpperSlt_eq_zero σ I hge]
  native_decide

theorem uniswapV3PoolBurnFeeGrowthInsideLowerBelowToUpperJoin {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hlt :
      tickSpacingSint24Value (slot0TickRawWord σ ee) <
        tickSpacingSint24Value (burnTickLowerWord ee))
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
        burnAmountCleanWord ee :: burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee ::
        ret :: R)
      (burnPositionKeyMappingMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k C)
    (hov : R.length + 80 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21476⟩
      (UInt256.sub (solcSlotWord σ ee ⟨2⟩)
          (burnTickLowerFeeGrowthOutside1Word σ ee) ::
        UInt256.sub (solcSlotWord σ ee ⟨1⟩)
          (burnTickLowerFeeGrowthOutside0Word σ ee) ::
        burnTickUpperFeeGrowthBaseSlot ee :: burnTickLowerFeeGrowthBaseSlot ee ::
        ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
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
        burnAmountCleanWord ee :: burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee ::
        ret :: R)
      (burnTickUpperFeeGrowthMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, hrdTest⟩ :=
    uniswapV3PoolBurnFeeGrowthInsideLowerBranchTest (v := v) (code := code)
      (ee := ee) (g := g) (s0 := s0) (ret := ret) (R := R) (rdata := rdata)
      (cA := cA) (σ := σ) hpatch h hov
  obtain ⟨_, _, hrdJump⟩ :=
    uniswapV3PoolBurnFeeGrowthInsideLowerBelowJump (v := v) (code := code)
      (ee := ee) (g := g) (s0 := s0) (ret := ret) (R := R) (rdata := rdata)
      (cA := cA) (σ := σ) hpatch (burnFeeGrowthInsideLowerSlt_ne_zero σ ee hlt)
      hrdTest hov
  exact uniswapV3PoolBurnFeeGrowthInsideLowerBelowToJoin (v := v) (code := code)
    (ee := ee) (g := g) (s0 := s0) (ret := ret) (R := R) (rdata := rdata)
    (cA := cA) (σ := σ) hpatch hrdJump hov

theorem uniswapV3PoolBurnFeeGrowthInsideLowerNotBelowToUpperJoin
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hge :
      ¬ tickSpacingSint24Value (slot0TickRawWord σ ee) <
        tickSpacingSint24Value (burnTickLowerWord ee))
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
        burnAmountCleanWord ee :: burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee ::
        ret :: R)
      (burnPositionKeyMappingMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k C)
    (hov : R.length + 80 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21476⟩
      (solcSlotWord σ ee (burnTickLowerFeeGrowthBaseSlot ee + ⟨2⟩) ::
        solcSlotWord σ ee (burnTickLowerFeeGrowthBaseSlot ee + ⟨1⟩) ::
        burnTickUpperFeeGrowthBaseSlot ee :: burnTickLowerFeeGrowthBaseSlot ee ::
        ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
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
        burnAmountCleanWord ee :: burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee ::
        ret :: R)
      (burnTickUpperFeeGrowthMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, hrdTest⟩ :=
    uniswapV3PoolBurnFeeGrowthInsideLowerBranchTest (v := v) (code := code)
      (ee := ee) (g := g) (s0 := s0) (ret := ret) (R := R) (rdata := rdata)
      (cA := cA) (σ := σ) hpatch h hov
  obtain ⟨_, _, hrdFallthrough⟩ :=
    uniswapV3PoolBurnFeeGrowthInsideLowerNotBelowFallthrough (v := v) (code := code)
      (ee := ee) (g := g) (s0 := s0) (ret := ret) (R := R) (rdata := rdata)
      (cA := cA) (σ := σ) hpatch (burnFeeGrowthInsideLowerSlt_eq_zero σ ee hge)
      hrdTest hov
  exact uniswapV3PoolBurnFeeGrowthInsideLowerNotBelowToJoin (v := v) (code := code)
    (ee := ee) (g := g) (s0 := s0) (ret := ret) (R := R) (rdata := rdata)
    (cA := cA) (σ := σ) hpatch hrdFallthrough hov

theorem uniswapV3PoolBurnFeeGrowthInsideUpperInsideFromJoin {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret below1 below0 : UInt256} {R : List UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hlt :
      tickSpacingSint24Value (slot0TickRawWord σ ee) <
        tickSpacingSint24Value (burnTickUpperWord ee))
    (h : RD code ee g s0 ⟨21476⟩
      (below1 :: below0 ::
        burnTickUpperFeeGrowthBaseSlot ee :: burnTickLowerFeeGrowthBaseSlot ee ::
        ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
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
        burnAmountCleanWord ee :: burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee ::
        ret :: R)
      (burnTickUpperFeeGrowthMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k C)
    (hov : R.length + 82 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21529⟩
      (solcSlotWord σ ee (burnTickUpperFeeGrowthBaseSlot ee + ⟨2⟩) ::
        solcSlotWord σ ee (burnTickUpperFeeGrowthBaseSlot ee + ⟨1⟩) ::
        below1 :: below0 ::
        burnTickUpperFeeGrowthBaseSlot ee :: burnTickLowerFeeGrowthBaseSlot ee ::
        ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
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
        burnAmountCleanWord ee :: burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee ::
        ret :: R)
      (burnTickUpperFeeGrowthMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, hrdTest⟩ :=
    uniswapV3PoolBurnFeeGrowthInsideUpperBranchTest (v := v) (code := code)
      (ee := ee) (g := g) (s0 := s0) (ret := ret) (below1 := below1)
      (below0 := below0) (R := R) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch h hov
  obtain ⟨_, _, hrdFallthrough⟩ :=
    uniswapV3PoolBurnFeeGrowthInsideUpperInsideFallthrough (v := v) (code := code)
      (ee := ee) (g := g) (s0 := s0) (ret := ret) (below1 := below1)
      (below0 := below0) (R := R) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch (burnFeeGrowthInsideUpperIsZero_eq_zero_of_lt σ ee hlt) hrdTest hov
  exact uniswapV3PoolBurnFeeGrowthInsideUpperInsideToJoin (v := v) (code := code)
    (ee := ee) (g := g) (s0 := s0) (ret := ret) (below1 := below1)
    (below0 := below0) (R := R) (rdata := rdata) (cA := cA) (σ := σ) hpatch
    hrdFallthrough hov

theorem uniswapV3PoolBurnFeeGrowthInsideUpperNotInsideFromJoin
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {ret below1 below0 : UInt256} {R : List UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hge :
      ¬ tickSpacingSint24Value (slot0TickRawWord σ ee) <
        tickSpacingSint24Value (burnTickUpperWord ee))
    (h : RD code ee g s0 ⟨21476⟩
      (below1 :: below0 ::
        burnTickUpperFeeGrowthBaseSlot ee :: burnTickLowerFeeGrowthBaseSlot ee ::
        ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
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
        burnAmountCleanWord ee :: burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee ::
        ret :: R)
      (burnTickUpperFeeGrowthMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k C)
    (hov : R.length + 82 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21529⟩
      (UInt256.sub (solcSlotWord σ ee ⟨2⟩)
          (burnTickUpperFeeGrowthOutside1Word σ ee) ::
        UInt256.sub (solcSlotWord σ ee ⟨1⟩)
          (burnTickUpperFeeGrowthOutside0Word σ ee) ::
        below1 :: below0 ::
        burnTickUpperFeeGrowthBaseSlot ee :: burnTickLowerFeeGrowthBaseSlot ee ::
        ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
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
        burnAmountCleanWord ee :: burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee ::
        ret :: R)
      (burnTickUpperFeeGrowthMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, hrdTest⟩ :=
    uniswapV3PoolBurnFeeGrowthInsideUpperBranchTest (v := v) (code := code)
      (ee := ee) (g := g) (s0 := s0) (ret := ret) (below1 := below1)
      (below0 := below0) (R := R) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch h hov
  obtain ⟨_, _, hrdJump⟩ :=
    uniswapV3PoolBurnFeeGrowthInsideUpperNotInsideJump (v := v) (code := code)
      (ee := ee) (g := g) (s0 := s0) (ret := ret) (below1 := below1)
      (below0 := below0) (R := R) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch (burnFeeGrowthInsideUpperIsZero_ne_zero_of_ge σ ee hge) hrdTest hov
  exact uniswapV3PoolBurnFeeGrowthInsideUpperNotInsideToJoin (v := v) (code := code)
    (ee := ee) (g := g) (s0 := s0) (ret := ret) (below1 := below1)
    (below0 := below0) (R := R) (rdata := rdata) (cA := cA) (σ := σ) hpatch hrdJump hov

end Benchmarks.UniswapV3Pool
