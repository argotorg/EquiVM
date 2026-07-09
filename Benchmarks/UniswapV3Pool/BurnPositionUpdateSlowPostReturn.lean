import Benchmarks.UniswapV3Pool.BurnPositionUpdatePostReturn

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.UniswapV3Pool

theorem uniswapV3PoolBurnPositionUpdateMulDiv1Prod1NonzeroSkipLiquidityWrite
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State}
    {tokensOwed0 liquidity inside1 inside0 delta posBase retPos inside1' inside0'
      z2 z3 fee1 fee0 posBase' tick delta' upper lower owner ret free : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨13017⟩
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩ :: liquidity ::
        UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256))) ::
        ⟨21807⟩ :: ⟨0⟩ :: tokensOwed0 :: liquidity ::
        burnPositionKeyNewFreePtrWord :: inside1 :: inside0 :: delta :: posBase ::
        retPos :: inside1' :: inside0' :: z2 :: z3 :: fee1 :: fee0 :: posBase' ::
        tick :: delta' :: upper :: lower :: owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata (cA, σ) k C)
    (hprod1 :
      uniswapV3PoolFullMathMulDivProd1
          (UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256))))
          liquidity ≠ ⟨0⟩)
    (hden :
      UInt256.gt (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)
        (uniswapV3PoolFullMathMulDivProd1
          (UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256))))
          liquidity) ≠ ⟨0⟩)
    (hdelta : UInt256.signextend ⟨15⟩ delta = ⟨0⟩)
    (hov : R.length + 60 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21846⟩
      (uniswapV3PoolFullMathMulDivSlowResult
          (uniswapV3PoolFullMathMulDivProd1
            (UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256))))
            liquidity)
          (uniswapV3PoolFullMathMulDivProd0
            (UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256))))
            liquidity)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)
          liquidity
          (UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256)))) ::
        tokensOwed0 :: liquidity :: burnPositionKeyNewFreePtrWord ::
        inside1 :: inside0 :: delta :: posBase :: retPos :: inside1' :: inside0' ::
        z2 :: z3 :: fee1 :: fee0 :: posBase' :: tick :: delta' :: upper :: lower ::
        owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata (cA, σ) k' C' := by
  let den := UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩
  let a := UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256)))
  let prod1 := uniswapV3PoolFullMathMulDivProd1 a liquidity
  let prod0 := uniswapV3PoolFullMathMulDivProd0 a liquidity
  obtain ⟨_, _, hrd13044⟩ :=
    uniswapV3PoolFullMathMulDivStartProduct
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (mem := burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (aw := UInt256.ofNat 22) (rdata := rdata) (acc := (cA, σ))
      (den := den) (b := liquidity) (a := a) (ret := ⟨21807⟩) (z := ⟨0⟩)
      (R := tokensOwed0 :: liquidity :: burnPositionKeyNewFreePtrWord ::
        inside1 :: inside0 :: delta :: posBase :: retPos :: inside1' :: inside0' ::
        z2 :: z3 :: fee1 :: fee0 :: posBase' :: tick :: delta' :: upper :: lower ::
        owner :: ret :: free :: R)
      hpatch (by simpa [den, a] using h) (by simp only [List.length_cons] at hov ⊢; omega)
  obtain ⟨_, _, hrd21807⟩ :=
    uniswapV3PoolFullMathMulDivProd1NonzeroReturnStack
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (mem := burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (aw := UInt256.ofNat 22) (rdata := rdata) (acc := (cA, σ))
      (prod1 := prod1) (prod0 := prod0) (den := den) (b := liquidity) (a := a)
      (ret := ⟨21807⟩) (z := ⟨0⟩)
      (R := tokensOwed0 :: liquidity :: burnPositionKeyNewFreePtrWord ::
        inside1 :: inside0 :: delta :: posBase :: retPos :: inside1' :: inside0' ::
        z2 :: z3 :: fee1 :: fee0 :: posBase' :: tick :: delta' :: upper :: lower ::
        owner :: ret :: free :: R)
      hpatch
      (by simpa [prod1, prod0, den, a] using hrd13044)
      (by simpa [prod1, a] using hprod1)
      (by simpa [prod1, den, a] using hden)
      (uniswapV3PoolJumpDestPatched21807 hpatch)
      (by simp only [List.length_cons] at hov ⊢; omega)
  exact uniswapV3PoolBurnPositionUpdateDeltaZeroSkipLiquidityWrite
    (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
    (tokensOwed1 := uniswapV3PoolFullMathMulDivSlowResult prod1 prod0 den liquidity a)
    (z := ⟨0⟩) (tokensOwed0 := tokensOwed0) (liquidity := liquidity)
    (inside1 := inside1) (inside0 := inside0) (delta := delta) (posBase := posBase)
    (retPos := retPos) (inside1' := inside1') (inside0' := inside0') (z2 := z2)
    (z3 := z3) (fee1 := fee1) (fee0 := fee0) (posBase' := posBase') (tick := tick)
    (delta' := delta') (upper := upper) (lower := lower) (owner := owner) (ret := ret)
    (free := free) (R := R) (rdata := rdata) (cA := cA) (σ := σ)
    hpatch hdelta
    (by
      simpa [prod1, prod0, den, a, uniswapV3PoolFullMathMulDivSlowResult,
        uniswapV3PoolFullMathMulDivSlowReturnStack,
        uniswapV3PoolFullMathMulDivSlowJumpStack,
        uniswapV3PoolFullMathMulDivSlowBodyStack] using hrd21807)
    (by omega)

theorem uniswapV3PoolBurnPositionUpdateMulDiv0Prod1NonzeroStartMulDiv1
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State}
    {inside1 inside0 delta posBase retPos inside1' inside0' z2 z3 fee1 fee0 posBase'
      tick delta' upper lower owner ret free : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨13017⟩
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩ ::
        burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase) ::
        UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))) ::
        ⟨21769⟩ :: ⟨0⟩ ::
        burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase) ::
        burnPositionKeyNewFreePtrWord :: inside1 :: inside0 :: delta :: posBase ::
        retPos :: inside1' :: inside0' :: z2 :: z3 :: fee1 :: fee0 :: posBase' ::
        tick :: delta' :: upper :: lower :: owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata (cA, σ) k C)
    (hprod0 :
      uniswapV3PoolFullMathMulDivProd1
          (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))))
          (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)) ≠ ⟨0⟩)
    (hden0 :
      UInt256.gt (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)
        (uniswapV3PoolFullMathMulDivProd1
          (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))))
          (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase))) ≠ ⟨0⟩)
    (hov : R.length + 60 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨13017⟩
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩ ::
        burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase) ::
        UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256))) ::
        ⟨21807⟩ :: ⟨0⟩ ::
        uniswapV3PoolFullMathMulDivSlowResult
          (uniswapV3PoolFullMathMulDivProd1
            (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))))
            (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)))
          (uniswapV3PoolFullMathMulDivProd0
            (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))))
            (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)))
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)
          (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase))
          (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256)))) ::
        burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase) ::
        burnPositionKeyNewFreePtrWord :: inside1 :: inside0 :: delta :: posBase ::
        retPos :: inside1' :: inside0' :: z2 :: z3 :: fee1 :: fee0 :: posBase' ::
        tick :: delta' :: upper :: lower :: owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata (cA, σ) k' C' := by
  let den := UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩
  let liquidity := burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)
  let a := UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256)))
  let prod1 := uniswapV3PoolFullMathMulDivProd1 a liquidity
  let prod0 := uniswapV3PoolFullMathMulDivProd0 a liquidity
  obtain ⟨_, _, hrd13044⟩ :=
    uniswapV3PoolFullMathMulDivStartProduct
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (mem := burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (aw := UInt256.ofNat 22) (rdata := rdata) (acc := (cA, σ))
      (den := den) (b := liquidity) (a := a) (ret := ⟨21769⟩) (z := ⟨0⟩)
      (R := liquidity :: burnPositionKeyNewFreePtrWord ::
        inside1 :: inside0 :: delta :: posBase :: retPos :: inside1' :: inside0' ::
        z2 :: z3 :: fee1 :: fee0 :: posBase' :: tick :: delta' :: upper :: lower ::
        owner :: ret :: free :: R)
      hpatch (by simpa [den, liquidity, a] using h)
      (by simp only [List.length_cons] at hov ⊢; omega)
  obtain ⟨_, _, hrd21769⟩ :=
    uniswapV3PoolFullMathMulDivProd1NonzeroReturnStack
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (mem := burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (aw := UInt256.ofNat 22) (rdata := rdata) (acc := (cA, σ))
      (prod1 := prod1) (prod0 := prod0) (den := den) (b := liquidity) (a := a)
      (ret := ⟨21769⟩) (z := ⟨0⟩)
      (R := liquidity :: burnPositionKeyNewFreePtrWord ::
        inside1 :: inside0 :: delta :: posBase :: retPos :: inside1' :: inside0' ::
        z2 :: z3 :: fee1 :: fee0 :: posBase' :: tick :: delta' :: upper :: lower ::
        owner :: ret :: free :: R)
      hpatch
      (by simpa [prod1, prod0, den, liquidity, a] using hrd13044)
      (by simpa [prod1, liquidity, a] using hprod0)
      (by simpa [prod1, den, liquidity, a] using hden0)
      (uniswapV3PoolJumpDestPatched21769 hpatch)
      (by simp only [List.length_cons] at hov ⊢; omega)
  exact uniswapV3PoolBurnPositionUpdateStartMulDiv1
    (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
    (tokensOwed0 := uniswapV3PoolFullMathMulDivSlowResult prod1 prod0 den liquidity a)
    (z := ⟨0⟩) (liquidity := liquidity)
    (inside1 := inside1) (inside0 := inside0) (delta := delta) (posBase := posBase)
    (retPos := retPos) (inside1' := inside1') (inside0' := inside0') (z2 := z2)
    (z3 := z3) (fee1 := fee1) (fee0 := fee0) (posBase' := posBase') (tick := tick)
    (delta' := delta') (upper := upper) (lower := lower) (owner := owner) (ret := ret)
    (free := free) (R := R) (rdata := rdata) (cA := cA) (σ := σ)
    hpatch
    (by
      simpa [prod1, prod0, den, liquidity, a, uniswapV3PoolFullMathMulDivSlowResult,
        uniswapV3PoolFullMathMulDivSlowReturnStack,
        uniswapV3PoolFullMathMulDivSlowJumpStack,
        uniswapV3PoolFullMathMulDivSlowBodyStack] using hrd21769)
    (by omega)

theorem uniswapV3PoolBurnPositionUpdateMulDiv0Prod1NonzeroMulDiv1Prod1ZeroStoreFeeGrowthLast
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State}
    {inside1 inside0 delta posBase retPos inside1' inside0' z2 z3 fee1 fee0 posBase'
      tick delta' upper lower owner ret free : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hperm : ee.perm = true)
    (h : RD code ee g s0 ⟨13017⟩
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩ ::
        burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase) ::
        UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))) ::
        ⟨21769⟩ :: ⟨0⟩ ::
        burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase) ::
        burnPositionKeyNewFreePtrWord :: inside1 :: inside0 :: delta :: posBase ::
        retPos :: inside1' :: inside0' :: z2 :: z3 :: fee1 :: fee0 :: posBase' ::
        tick :: delta' :: upper :: lower :: owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata (cA, σ) k C)
    (hprod0 :
      uniswapV3PoolFullMathMulDivProd1
          (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))))
          (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)) ≠ ⟨0⟩)
    (hden0 :
      UInt256.gt (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)
        (uniswapV3PoolFullMathMulDivProd1
          (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))))
          (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase))) ≠ ⟨0⟩)
    (hprod1 :
      uniswapV3PoolFullMathMulDivProd1
          (UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256))))
          (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)) = ⟨0⟩)
    (hdelta : UInt256.signextend ⟨15⟩ delta = ⟨0⟩)
    (hov : R.length + 60 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21861⟩
      (UInt256.div
          (uniswapV3PoolFullMathMulDivProd0
            (UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256))))
            (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)))
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩) ::
        uniswapV3PoolFullMathMulDivSlowResult
          (uniswapV3PoolFullMathMulDivProd1
            (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))))
            (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)))
          (uniswapV3PoolFullMathMulDivProd0
            (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))))
            (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)))
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)
          (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase))
          (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256)))) ::
        burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase) ::
        burnPositionKeyNewFreePtrWord :: inside1 :: inside0 :: delta :: posBase ::
        retPos :: inside1' :: inside0' :: z2 :: z3 :: fee1 :: fee0 :: posBase' ::
        tick :: delta' :: upper :: lower :: owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata
      (cA, sstoreAccountMap ee.codeOwner
        (sstoreAccountMap ee.codeOwner σ (posBase + (⟨1⟩ : UInt256)) inside0)
        (posBase + (⟨2⟩ : UInt256)) inside1) k' C' := by
  obtain ⟨_, _, hrdSecond13017⟩ :=
    uniswapV3PoolBurnPositionUpdateMulDiv0Prod1NonzeroStartMulDiv1
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1) (inside0 := inside0) (delta := delta) (posBase := posBase)
      (retPos := retPos) (inside1' := inside1') (inside0' := inside0') (z2 := z2)
      (z3 := z3) (fee1 := fee1) (fee0 := fee0) (posBase' := posBase') (tick := tick)
      (delta' := delta') (upper := upper) (lower := lower) (owner := owner) (ret := ret)
      (free := free) (R := R) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch h hprod0 hden0 (by omega)
  obtain ⟨_, _, hrd21846⟩ :=
    uniswapV3PoolBurnPositionUpdateMulDiv1Prod1ZeroSkipLiquidityWrite
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (tokensOwed0 := uniswapV3PoolFullMathMulDivSlowResult
        (uniswapV3PoolFullMathMulDivProd1
          (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))))
          (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)))
        (uniswapV3PoolFullMathMulDivProd0
          (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))))
          (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)))
        (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)
        (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase))
        (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256)))))
      (liquidity := burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase))
      (inside1 := inside1) (inside0 := inside0) (delta := delta) (posBase := posBase)
      (retPos := retPos) (inside1' := inside1') (inside0' := inside0') (z2 := z2)
      (z3 := z3) (fee1 := fee1) (fee0 := fee0) (posBase' := posBase') (tick := tick)
      (delta' := delta') (upper := upper) (lower := lower) (owner := owner) (ret := ret)
      (free := free) (R := R) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch hrdSecond13017 hprod1 hdelta (by omega)
  exact uniswapV3PoolBurnPositionUpdateStoreFeeGrowthLastAfterSkip
    (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
    (tokensOwed1 := UInt256.div
      (uniswapV3PoolFullMathMulDivProd0
        (UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256))))
        (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)))
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩))
    (tokensOwed0 := uniswapV3PoolFullMathMulDivSlowResult
      (uniswapV3PoolFullMathMulDivProd1
        (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))))
        (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)))
      (uniswapV3PoolFullMathMulDivProd0
        (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))))
        (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)))
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)
      (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase))
      (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256)))))
    (liquidity := burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase))
    (inside1 := inside1) (inside0 := inside0) (delta := delta) (posBase := posBase)
    (retPos := retPos) (inside1' := inside1') (inside0' := inside0') (z2 := z2)
    (z3 := z3) (fee1 := fee1) (fee0 := fee0) (posBase' := posBase') (tick := tick)
    (delta' := delta') (upper := upper) (lower := lower) (owner := owner) (ret := ret)
    (free := free) (R := R) (rdata := rdata) (cA := cA) (σ := σ)
    hpatch hperm hrd21846 (by omega)

theorem uniswapV3PoolBurnPositionUpdateMulDiv0Prod1NonzeroMulDiv1Prod1NonzeroStoreFeeGrowthLast
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State}
    {inside1 inside0 delta posBase retPos inside1' inside0' z2 z3 fee1 fee0 posBase'
      tick delta' upper lower owner ret free : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hperm : ee.perm = true)
    (h : RD code ee g s0 ⟨13017⟩
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩ ::
        burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase) ::
        UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))) ::
        ⟨21769⟩ :: ⟨0⟩ ::
        burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase) ::
        burnPositionKeyNewFreePtrWord :: inside1 :: inside0 :: delta :: posBase ::
        retPos :: inside1' :: inside0' :: z2 :: z3 :: fee1 :: fee0 :: posBase' ::
        tick :: delta' :: upper :: lower :: owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata (cA, σ) k C)
    (hprod0 :
      uniswapV3PoolFullMathMulDivProd1
          (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))))
          (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)) ≠ ⟨0⟩)
    (hden0 :
      UInt256.gt (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)
        (uniswapV3PoolFullMathMulDivProd1
          (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))))
          (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase))) ≠ ⟨0⟩)
    (hprod1 :
      uniswapV3PoolFullMathMulDivProd1
          (UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256))))
          (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)) ≠ ⟨0⟩)
    (hden1 :
      UInt256.gt (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)
        (uniswapV3PoolFullMathMulDivProd1
          (UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256))))
          (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase))) ≠ ⟨0⟩)
    (hdelta : UInt256.signextend ⟨15⟩ delta = ⟨0⟩)
    (hov : R.length + 60 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21861⟩
      (uniswapV3PoolFullMathMulDivSlowResult
          (uniswapV3PoolFullMathMulDivProd1
            (UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256))))
            (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)))
          (uniswapV3PoolFullMathMulDivProd0
            (UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256))))
            (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)))
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)
          (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase))
          (UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256)))) ::
        uniswapV3PoolFullMathMulDivSlowResult
          (uniswapV3PoolFullMathMulDivProd1
            (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))))
            (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)))
          (uniswapV3PoolFullMathMulDivProd0
            (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))))
            (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)))
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)
          (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase))
          (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256)))) ::
        burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase) ::
        burnPositionKeyNewFreePtrWord :: inside1 :: inside0 :: delta :: posBase ::
        retPos :: inside1' :: inside0' :: z2 :: z3 :: fee1 :: fee0 :: posBase' ::
        tick :: delta' :: upper :: lower :: owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata
      (cA, sstoreAccountMap ee.codeOwner
        (sstoreAccountMap ee.codeOwner σ (posBase + (⟨1⟩ : UInt256)) inside0)
        (posBase + (⟨2⟩ : UInt256)) inside1) k' C' := by
  obtain ⟨_, _, hrdSecond13017⟩ :=
    uniswapV3PoolBurnPositionUpdateMulDiv0Prod1NonzeroStartMulDiv1
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1) (inside0 := inside0) (delta := delta) (posBase := posBase)
      (retPos := retPos) (inside1' := inside1') (inside0' := inside0') (z2 := z2)
      (z3 := z3) (fee1 := fee1) (fee0 := fee0) (posBase' := posBase') (tick := tick)
      (delta' := delta') (upper := upper) (lower := lower) (owner := owner) (ret := ret)
      (free := free) (R := R) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch h hprod0 hden0 (by omega)
  obtain ⟨_, _, hrd21846⟩ :=
    uniswapV3PoolBurnPositionUpdateMulDiv1Prod1NonzeroSkipLiquidityWrite
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (tokensOwed0 := uniswapV3PoolFullMathMulDivSlowResult
        (uniswapV3PoolFullMathMulDivProd1
          (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))))
          (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)))
        (uniswapV3PoolFullMathMulDivProd0
          (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))))
          (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)))
        (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)
        (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase))
        (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256)))))
      (liquidity := burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase))
      (inside1 := inside1) (inside0 := inside0) (delta := delta) (posBase := posBase)
      (retPos := retPos) (inside1' := inside1') (inside0' := inside0') (z2 := z2)
      (z3 := z3) (fee1 := fee1) (fee0 := fee0) (posBase' := posBase') (tick := tick)
      (delta' := delta') (upper := upper) (lower := lower) (owner := owner) (ret := ret)
      (free := free) (R := R) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch hrdSecond13017 hprod1 hden1 hdelta (by omega)
  exact uniswapV3PoolBurnPositionUpdateStoreFeeGrowthLastAfterSkip
    (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
    (tokensOwed1 := uniswapV3PoolFullMathMulDivSlowResult
      (uniswapV3PoolFullMathMulDivProd1
        (UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256))))
        (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)))
      (uniswapV3PoolFullMathMulDivProd0
        (UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256))))
        (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)))
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)
      (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase))
      (UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256)))))
    (tokensOwed0 := uniswapV3PoolFullMathMulDivSlowResult
      (uniswapV3PoolFullMathMulDivProd1
        (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))))
        (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)))
      (uniswapV3PoolFullMathMulDivProd0
        (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))))
        (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)))
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)
      (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase))
      (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256)))))
    (liquidity := burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase))
    (inside1 := inside1) (inside0 := inside0) (delta := delta) (posBase := posBase)
    (retPos := retPos) (inside1' := inside1') (inside0' := inside0') (z2 := z2)
    (z3 := z3) (fee1 := fee1) (fee0 := fee0) (posBase' := posBase') (tick := tick)
    (delta' := delta') (upper := upper) (lower := lower) (owner := owner) (ret := ret)
    (free := free) (R := R) (rdata := rdata) (cA := cA) (σ := σ)
    hpatch hperm hrd21846 (by omega)

theorem uniswapV3PoolBurnPositionUpdateMulDiv0Prod1ZeroMulDiv1Prod1NonzeroStoreFeeGrowthLast
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State}
    {inside1 inside0 delta posBase retPos inside1' inside0' z2 z3 fee1 fee0 posBase'
      tick delta' upper lower owner ret free : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hperm : ee.perm = true)
    (h : RD code ee g s0 ⟨13017⟩
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩ ::
        burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase) ::
        UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))) ::
        ⟨21769⟩ :: ⟨0⟩ ::
        burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase) ::
        burnPositionKeyNewFreePtrWord :: inside1 :: inside0 :: delta :: posBase ::
        retPos :: inside1' :: inside0' :: z2 :: z3 :: fee1 :: fee0 :: posBase' ::
        tick :: delta' :: upper :: lower :: owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata (cA, σ) k C)
    (hprod0 :
      uniswapV3PoolFullMathMulDivProd1
          (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))))
          (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)) = ⟨0⟩)
    (hprod1 :
      uniswapV3PoolFullMathMulDivProd1
          (UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256))))
          (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)) ≠ ⟨0⟩)
    (hden :
      UInt256.gt (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)
        (uniswapV3PoolFullMathMulDivProd1
          (UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256))))
          (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase))) ≠ ⟨0⟩)
    (hdelta : UInt256.signextend ⟨15⟩ delta = ⟨0⟩)
    (hov : R.length + 60 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21861⟩
      (uniswapV3PoolFullMathMulDivSlowResult
          (uniswapV3PoolFullMathMulDivProd1
            (UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256))))
            (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)))
          (uniswapV3PoolFullMathMulDivProd0
            (UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256))))
            (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)))
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)
          (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase))
          (UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256)))) ::
        UInt256.div
          (uniswapV3PoolFullMathMulDivProd0
            (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))))
            (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)))
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩) ::
        burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase) ::
        burnPositionKeyNewFreePtrWord :: inside1 :: inside0 :: delta :: posBase ::
        retPos :: inside1' :: inside0' :: z2 :: z3 :: fee1 :: fee0 :: posBase' ::
        tick :: delta' :: upper :: lower :: owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata
      (cA, sstoreAccountMap ee.codeOwner
        (sstoreAccountMap ee.codeOwner σ (posBase + (⟨1⟩ : UInt256)) inside0)
        (posBase + (⟨2⟩ : UInt256)) inside1) k' C' := by
  obtain ⟨_, _, hrdSecond13017⟩ :=
    uniswapV3PoolBurnPositionUpdateMulDiv0Prod1ZeroStartMulDiv1
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1) (inside0 := inside0) (delta := delta) (posBase := posBase)
      (retPos := retPos) (inside1' := inside1') (inside0' := inside0') (z2 := z2)
      (z3 := z3) (fee1 := fee1) (fee0 := fee0) (posBase' := posBase') (tick := tick)
      (delta' := delta') (upper := upper) (lower := lower) (owner := owner) (ret := ret)
      (free := free) (R := R) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch h hprod0 (by omega)
  obtain ⟨_, _, hrd21846⟩ :=
    uniswapV3PoolBurnPositionUpdateMulDiv1Prod1NonzeroSkipLiquidityWrite
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (tokensOwed0 := UInt256.div
        (uniswapV3PoolFullMathMulDivProd0
          (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))))
          (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)))
        (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩))
      (liquidity := burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase))
      (inside1 := inside1) (inside0 := inside0) (delta := delta) (posBase := posBase)
      (retPos := retPos) (inside1' := inside1') (inside0' := inside0') (z2 := z2)
      (z3 := z3) (fee1 := fee1) (fee0 := fee0) (posBase' := posBase') (tick := tick)
      (delta' := delta') (upper := upper) (lower := lower) (owner := owner) (ret := ret)
      (free := free) (R := R) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch hrdSecond13017 hprod1 hden hdelta (by omega)
  exact uniswapV3PoolBurnPositionUpdateStoreFeeGrowthLastAfterSkip
    (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
    (tokensOwed1 := uniswapV3PoolFullMathMulDivSlowResult
      (uniswapV3PoolFullMathMulDivProd1
        (UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256))))
        (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)))
      (uniswapV3PoolFullMathMulDivProd0
        (UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256))))
        (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)))
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)
      (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase))
      (UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256)))))
    (tokensOwed0 := UInt256.div
      (uniswapV3PoolFullMathMulDivProd0
        (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))))
        (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)))
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩))
    (liquidity := burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase))
    (inside1 := inside1) (inside0 := inside0) (delta := delta) (posBase := posBase)
    (retPos := retPos) (inside1' := inside1') (inside0' := inside0') (z2 := z2)
    (z3 := z3) (fee1 := fee1) (fee0 := fee0) (posBase' := posBase') (tick := tick)
    (delta' := delta') (upper := upper) (lower := lower) (owner := owner) (ret := ret)
    (free := free) (R := R) (rdata := rdata) (cA := cA) (σ := σ)
    hpatch hperm hrd21846 (by omega)

end Benchmarks.UniswapV3Pool
