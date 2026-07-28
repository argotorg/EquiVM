import Benchmarks.UniswapV3Pool.BurnZeroDeltaMulDivStart
import Benchmarks.UniswapV3Pool.BurnZeroDeltaFinish
import Benchmarks.UniswapV3Pool.BurnPositionUpdateSlowPostReturn

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolBurnZeroDeltaPositionUpdateSlowToken0Runtime
    {v : PoolImmutables}
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader}
    {bl : ProcessedBlocks} {σ_evm σ_solm σ₀ lockedEvm lockedSolm : AccountMap}
    {A : Substate} {I : ExecutionEnv} {g : UInt256} {code : ByteArray}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code)
    (hperm : I.perm = true)
    (hdispatch : dispatchMsg (contract v) I.calldata = some burnTransition)
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode
          (List.map Param.name burnTransition.params)
          (transitionSignature burnTransition).paramTypes I.calldata =
        some (burnStore I))
    (hwv : I.weiValue = ⟨0⟩)
    (hunlockedSolm : burnUnlockedByte σ_solm I ≠ ⟨0⟩)
    (hcanon : UInt256.signextend ⟨15⟩ (burnAmountCleanWord I) = burnAmountCleanWord I)
    (hnoDelegate : uniswapV3PoolNoDelegateCallGuard v I ≠ ⟨0⟩)
    (htickLt :
      tickSpacingSint24Value (burnTickLowerWord I) <
        tickSpacingSint24Value (burnTickUpperWord I))
    (hLowerMin : ¬ tickSpacingSint24Value (burnTickLowerWord I) < -887272)
    (hUpperMax : ¬ 887272 < tickSpacingSint24Value (burnTickUpperWord I))
    (hzero : burnAmountCleanWord I = ⟨0⟩)
    (hAccountsLocked : accountMapEquiv lockedEvm lockedSolm)
    (hlockedSolm :
      lockedSolm =
        sstoreAccountMap I.codeOwner σ_solm ⟨0⟩ (burnLockedSlotWord σ_solm I))
    (hliq :
      burnPositionUpdateSlot0Packed
          (solcSlotWord lockedEvm I (burnPositionBaseSlotWord lockedEvm I)) ≠ ⟨0⟩)
    (hprod0 :
      uniswapV3PoolFullMathMulDivProd1
          (UInt256.sub (burnTickGetInside0Word lockedEvm I)
            (solcSlotWord lockedEvm I
              (burnPositionBaseSlotWord lockedEvm I + (⟨1⟩ : UInt256))))
          (burnPositionUpdateSlot0Packed
            (solcSlotWord lockedEvm I (burnPositionBaseSlotWord lockedEvm I))) ≠ ⟨0⟩)
    (hrdFeeGrowthEntry :
      RD code I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨21387⟩
        (solcSlotWord lockedEvm I ⟨2⟩ :: solcSlotWord lockedEvm I ⟨1⟩ ::
          slot0TickReturnWord lockedEvm I ::
          UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I) ::
          UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I) ::
          ⟨5⟩ :: ⟨19510⟩ ::
          ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
          solcSlotWord lockedEvm I ⟨2⟩ :: solcSlotWord lockedEvm I ⟨1⟩ ::
          burnPositionBaseSlotWord lockedEvm I :: slot0TickReturnWord lockedEvm I ::
          UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)) ::
          UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I) ::
          UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I) ::
          UInt256.ofNat I.source.val :: ⟨16428⟩ :: ⟨256⟩ ::
          ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
          ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
          burnAmountCleanWord I :: burnTickUpperCleanWord I ::
          burnTickLowerCleanWord I :: ⟨621⟩ :: [solcSelectorWord I])
        (burnPositionKeyMappingMem lockedEvm I) (UInt256.ofNat 18) ByteArray.empty
        (cA, lockedEvm) k C) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  let positionBase := burnPositionBaseSlotWord lockedEvm I
  let feeGrowthInside1 := burnTickGetInside1Word lockedEvm I
  let feeGrowthInside0 := burnTickGetInside0Word lockedEvm I
  let liquidity := burnPositionUpdateSlot0Packed (solcSlotWord lockedEvm I positionBase)
  let delta := UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I))
  let positionUpdateR : List UInt256 :=
    ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
    ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
    burnAmountCleanWord I :: burnTickUpperCleanWord I ::
    burnTickLowerCleanWord I :: ⟨621⟩ :: [solcSelectorWord I]
  have hPositionBase : positionBase = positionsBase (burnPositionKeyKey I) := by
    simpa [positionBase] using burnPositionBaseSlotWord_eq_positionsBase lockedEvm I
  have hliqBound : liquidity.toNat < 2 ^ (128 : Nat) := by
    dsimp [liquidity, positionBase]
    change
      (UInt256.land burnPositionUpdateSlot0Mask
        (solcSlotWord lockedEvm I (burnPositionBaseSlotWord lockedEvm I))).toNat <
        2 ^ (128 : Nat)
    rw [burnPositionUpdateSlot0Mask_eq_uint128Mask]
    rw [u256_land_comm]
    simpa [EVM.twoPow] using
      uint128Mask_bound (solcSlotWord lockedEvm I (burnPositionBaseSlotWord lockedEvm I))
  have hden0 :
      UInt256.gt (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)
        (uniswapV3PoolFullMathMulDivProd1
          (UInt256.sub feeGrowthInside0
            (solcSlotWord lockedEvm I (positionBase + (⟨1⟩ : UInt256))))
          liquidity) ≠ ⟨0⟩ := by
    exact uniswapV3PoolFullMathMulDivProd1DenGtQ128
      (UInt256.sub feeGrowthInside0
        (solcSlotWord lockedEvm I (positionBase + (⟨1⟩ : UInt256))))
      liquidity hliqBound
  obtain ⟨_, _, hrd13017⟩ :=
    uniswapV3PoolBurnZeroDeltaPositionUpdateToMulDiv0StartConcrete
      (v := v) (code := code) (ee := I) (g := Sat256.ofUInt256 g)
      (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      (ret := ⟨621⟩) (R := [solcSelectorWord I])
      (rdata := ByteArray.empty) (cA := cA) (σ := lockedEvm)
      hpatch htickLt hzero
      (by simpa [positionBase, liquidity] using hliq)
      (by simpa [positionBase] using hrdFeeGrowthEntry)
      (by simp only [List.length_singleton]; omega)
  have hdelta : UInt256.signextend ⟨15⟩ delta = ⟨0⟩ := by
    dsimp [delta]
    rw [hzero]
    native_decide
  by_cases hprod1 :
      uniswapV3PoolFullMathMulDivProd1
          (UInt256.sub feeGrowthInside1
            (solcSlotWord lockedEvm I (positionBase + (⟨2⟩ : UInt256))))
          liquidity = ⟨0⟩
  · let tokensOwed0 : UInt256 :=
      uniswapV3PoolFullMathMulDivSlowResult
        (uniswapV3PoolFullMathMulDivProd1
          (UInt256.sub feeGrowthInside0
            (solcSlotWord lockedEvm I (positionBase + (⟨1⟩ : UInt256))))
          liquidity)
        (uniswapV3PoolFullMathMulDivProd0
          (UInt256.sub feeGrowthInside0
            (solcSlotWord lockedEvm I (positionBase + (⟨1⟩ : UInt256))))
          liquidity)
        (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩) liquidity
        (UInt256.sub feeGrowthInside0
          (solcSlotWord lockedEvm I (positionBase + (⟨1⟩ : UInt256))))
    let tokensOwed1 : UInt256 :=
      UInt256.div
        (uniswapV3PoolFullMathMulDivProd0
          (UInt256.sub feeGrowthInside1
            (solcSlotWord lockedEvm I (positionBase + (⟨2⟩ : UInt256))))
          liquidity)
        (UInt256.shiftLeft ⟨1⟩ ⟨128⟩)
    obtain ⟨_, _, hrd21861⟩ :=
      uniswapV3PoolBurnPositionUpdateMulDiv0Prod1NonzeroMulDiv1Prod1ZeroStoreFeeGrowthLast
        (v := v) (code := code) (ee := I) (g := Sat256.ofUInt256 g)
        (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (inside1 := feeGrowthInside1) (inside0 := feeGrowthInside0)
        (delta := delta) (posBase := positionBase) (retPos := ⟨19527⟩)
        (inside1' := feeGrowthInside1) (inside0' := feeGrowthInside0)
        (z2 := ⟨0⟩) (z3 := ⟨0⟩)
        (fee1 := solcSlotWord lockedEvm I ⟨2⟩)
        (fee0 := solcSlotWord lockedEvm I ⟨1⟩)
        (posBase' := positionBase) (tick := slot0TickReturnWord lockedEvm I)
        (delta' := delta)
        (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I))
        (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I))
        (owner := UInt256.ofNat I.source.val) (ret := ⟨16428⟩) (free := ⟨256⟩)
        (R := positionUpdateR) (rdata := ByteArray.empty) (cA := cA) (σ := lockedEvm)
        hpatch hperm
        (by simpa [feeGrowthInside1, feeGrowthInside0, positionBase, liquidity, delta,
          positionUpdateR] using hrd13017)
        (by simpa [feeGrowthInside0, positionBase, liquidity] using hprod0)
        (by simpa [feeGrowthInside0, positionBase, liquidity] using hden0)
        (by simpa [feeGrowthInside1, positionBase, liquidity] using hprod1)
        hdelta
        (by simp [positionUpdateR])
    have hlow0 :
        UInt256.land burnPositionUpdateSlot0Mask
            (UInt256.div
              (uniswapV3PoolFullMathMulDivProd0
                (UInt256.sub feeGrowthInside0
                  (solcSlotWord lockedEvm I (positionBase + (⟨1⟩ : UInt256))))
                liquidity)
              (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)) =
          UInt256.land burnPositionUpdateSlot0Mask tokensOwed0 := by
      simpa [tokensOwed0] using
        (uniswapV3PoolFullMathMulDivSlowResult_low128_eq_prod0Div128
          (UInt256.sub feeGrowthInside0
            (solcSlotWord lockedEvm I (positionBase + (⟨1⟩ : UInt256))))
          liquidity).symm
    have hlow1 :
        UInt256.land burnPositionUpdateSlot0Mask
            (UInt256.div
              (uniswapV3PoolFullMathMulDivProd0
                (UInt256.sub feeGrowthInside1
                  (solcSlotWord lockedEvm I (positionBase + (⟨2⟩ : UInt256))))
                liquidity)
              (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)) =
          UInt256.land burnPositionUpdateSlot0Mask tokensOwed1 := by
      rfl
    exact
      uniswapV3PoolBurnZeroDeltaMulDivReturnToRuntimeFinish
        (v := v) (cA := cA) (gh := gh) (bl := bl)
        (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀)
        (lockedEvm := lockedEvm) (lockedSolm := lockedSolm)
        (A := A) (I := I) (g := g)
        (tokensOwed0 := tokensOwed0) (tokensOwed1 := tokensOwed1)
        (feeGrowthInside0 := feeGrowthInside0) (feeGrowthInside1 := feeGrowthInside1)
        (positionBase := positionBase) (code := code)
        hpatch hcode hperm hdispatch hdecode hwv hunlockedSolm hcanon hnoDelegate
        htickLt hLowerMin hUpperMax hzero hAccountsLocked hlockedSolm
        (by rfl) (by rfl) hPositionBase (by simpa [liquidity] using hliq)
        (by simpa [tokensOwed0, tokensOwed1, feeGrowthInside1, feeGrowthInside0,
          positionBase, liquidity, delta, positionUpdateR] using hrd21861)
        hlow0 hlow1
  · let tokensOwed0 : UInt256 :=
      uniswapV3PoolFullMathMulDivSlowResult
        (uniswapV3PoolFullMathMulDivProd1
          (UInt256.sub feeGrowthInside0
            (solcSlotWord lockedEvm I (positionBase + (⟨1⟩ : UInt256))))
          liquidity)
        (uniswapV3PoolFullMathMulDivProd0
          (UInt256.sub feeGrowthInside0
            (solcSlotWord lockedEvm I (positionBase + (⟨1⟩ : UInt256))))
          liquidity)
        (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩) liquidity
        (UInt256.sub feeGrowthInside0
          (solcSlotWord lockedEvm I (positionBase + (⟨1⟩ : UInt256))))
    let tokensOwed1 : UInt256 :=
      uniswapV3PoolFullMathMulDivSlowResult
        (uniswapV3PoolFullMathMulDivProd1
          (UInt256.sub feeGrowthInside1
            (solcSlotWord lockedEvm I (positionBase + (⟨2⟩ : UInt256))))
          liquidity)
        (uniswapV3PoolFullMathMulDivProd0
          (UInt256.sub feeGrowthInside1
            (solcSlotWord lockedEvm I (positionBase + (⟨2⟩ : UInt256))))
          liquidity)
        (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩) liquidity
        (UInt256.sub feeGrowthInside1
          (solcSlotWord lockedEvm I (positionBase + (⟨2⟩ : UInt256))))
    have hden1 :
        UInt256.gt (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)
          (uniswapV3PoolFullMathMulDivProd1
            (UInt256.sub feeGrowthInside1
              (solcSlotWord lockedEvm I (positionBase + (⟨2⟩ : UInt256))))
            liquidity) ≠ ⟨0⟩ := by
      exact uniswapV3PoolFullMathMulDivProd1DenGtQ128
        (UInt256.sub feeGrowthInside1
          (solcSlotWord lockedEvm I (positionBase + (⟨2⟩ : UInt256))))
        liquidity hliqBound
    obtain ⟨_, _, hrd21861⟩ :=
      uniswapV3PoolBurnPositionUpdateMulDiv0Prod1NonzeroMulDiv1Prod1NonzeroStoreFeeGrowthLast
        (v := v) (code := code) (ee := I) (g := Sat256.ofUInt256 g)
        (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (inside1 := feeGrowthInside1) (inside0 := feeGrowthInside0)
        (delta := delta) (posBase := positionBase) (retPos := ⟨19527⟩)
        (inside1' := feeGrowthInside1) (inside0' := feeGrowthInside0)
        (z2 := ⟨0⟩) (z3 := ⟨0⟩)
        (fee1 := solcSlotWord lockedEvm I ⟨2⟩)
        (fee0 := solcSlotWord lockedEvm I ⟨1⟩)
        (posBase' := positionBase) (tick := slot0TickReturnWord lockedEvm I)
        (delta' := delta)
        (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I))
        (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I))
        (owner := UInt256.ofNat I.source.val) (ret := ⟨16428⟩) (free := ⟨256⟩)
        (R := positionUpdateR) (rdata := ByteArray.empty) (cA := cA) (σ := lockedEvm)
        hpatch hperm
        (by simpa [feeGrowthInside1, feeGrowthInside0, positionBase, liquidity, delta,
          positionUpdateR] using hrd13017)
        (by simpa [feeGrowthInside0, positionBase, liquidity] using hprod0)
        (by simpa [feeGrowthInside0, positionBase, liquidity] using hden0)
        (by simpa [feeGrowthInside1, positionBase, liquidity] using hprod1)
        (by simpa [feeGrowthInside1, positionBase, liquidity] using hden1)
        hdelta
        (by simp [positionUpdateR])
    have hlow0 :
        UInt256.land burnPositionUpdateSlot0Mask
            (UInt256.div
              (uniswapV3PoolFullMathMulDivProd0
                (UInt256.sub feeGrowthInside0
                  (solcSlotWord lockedEvm I (positionBase + (⟨1⟩ : UInt256))))
                liquidity)
              (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)) =
          UInt256.land burnPositionUpdateSlot0Mask tokensOwed0 := by
      simpa [tokensOwed0] using
        (uniswapV3PoolFullMathMulDivSlowResult_low128_eq_prod0Div128
          (UInt256.sub feeGrowthInside0
            (solcSlotWord lockedEvm I (positionBase + (⟨1⟩ : UInt256))))
          liquidity).symm
    have hlow1 :
        UInt256.land burnPositionUpdateSlot0Mask
            (UInt256.div
              (uniswapV3PoolFullMathMulDivProd0
                (UInt256.sub feeGrowthInside1
                  (solcSlotWord lockedEvm I (positionBase + (⟨2⟩ : UInt256))))
                liquidity)
              (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)) =
          UInt256.land burnPositionUpdateSlot0Mask tokensOwed1 := by
      simpa [tokensOwed1] using
        (uniswapV3PoolFullMathMulDivSlowResult_low128_eq_prod0Div128
          (UInt256.sub feeGrowthInside1
            (solcSlotWord lockedEvm I (positionBase + (⟨2⟩ : UInt256))))
          liquidity).symm
    exact
      uniswapV3PoolBurnZeroDeltaMulDivReturnToRuntimeFinish
        (v := v) (cA := cA) (gh := gh) (bl := bl)
        (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀)
        (lockedEvm := lockedEvm) (lockedSolm := lockedSolm)
        (A := A) (I := I) (g := g)
        (tokensOwed0 := tokensOwed0) (tokensOwed1 := tokensOwed1)
        (feeGrowthInside0 := feeGrowthInside0) (feeGrowthInside1 := feeGrowthInside1)
        (positionBase := positionBase) (code := code)
        hpatch hcode hperm hdispatch hdecode hwv hunlockedSolm hcanon hnoDelegate
        htickLt hLowerMin hUpperMax hzero hAccountsLocked hlockedSolm
        (by rfl) (by rfl) hPositionBase (by simpa [liquidity] using hliq)
        (by simpa [tokensOwed0, tokensOwed1, feeGrowthInside1, feeGrowthInside0,
          positionBase, liquidity, delta, positionUpdateR] using hrd21861)
        hlow0 hlow1

end Benchmarks.UniswapV3Pool
