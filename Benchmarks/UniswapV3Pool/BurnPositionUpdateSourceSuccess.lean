import Benchmarks.UniswapV3Pool.BurnPositionUpdateSource

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.UniswapV3Pool

abbrev burnPositionUpdateSourceLiquidityInt (σ : AccountMap) (I : ExecutionEnv) : Int :=
  Int.ofNat (burnPositionUpdateSlot0Packed
    (solcSlotWord σ I (positionsBase (burnPositionKeyKey I)))).toNat

abbrev burnPositionUpdateSourceFeeGrowthInside0LastInt
    (σ : AccountMap) (I : ExecutionEnv) : Int :=
  Int.ofNat (solcSlotWord σ I (positionsBase (burnPositionKeyKey I) + ⟨1⟩)).toNat

abbrev burnPositionUpdateSourceFeeGrowthInside1LastInt
    (σ : AccountMap) (I : ExecutionEnv) : Int :=
  Int.ofNat (solcSlotWord σ I (positionsBase (burnPositionKeyKey I) + ⟨2⟩)).toNat

abbrev burnPositionUpdateSourceTokensOwed0Int
    (σ : AccountMap) (I : ExecutionEnv) (feeGrowthInside0X128 : Int) : Int :=
  (((burnWordSubInt feeGrowthInside0X128
      (burnPositionUpdateSourceFeeGrowthInside0LastInt σ I)) *
    burnPositionUpdateSourceLiquidityInt σ I) / ((2 : Int) ^ 128)) % ((2 : Int) ^ 128)

abbrev burnPositionUpdateSourceTokensOwed1Int
    (σ : AccountMap) (I : ExecutionEnv) (feeGrowthInside1X128 : Int) : Int :=
  (((burnWordSubInt feeGrowthInside1X128
      (burnPositionUpdateSourceFeeGrowthInside1LastInt σ I)) *
    burnPositionUpdateSourceLiquidityInt σ I) / ((2 : Int) ^ 128)) % ((2 : Int) ^ 128)

abbrev burnPositionUpdateSourceTokensOwedSlot (I : ExecutionEnv) : UInt256 :=
  positionsBase (burnPositionKeyKey I) + ⟨3⟩

abbrev burnPositionUpdateSourceStoredTokensOwed0Int
    (evm : EVM.State) (I : ExecutionEnv) : Int :=
  Int.ofNat (UInt256.land
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (burnPositionUpdateSourceTokensOwedSlot I))
    uint128Mask).toNat

abbrev burnPositionUpdateSourceStoredTokensOwed1Int
    (evm : EVM.State) (I : ExecutionEnv) : Int :=
  Int.ofNat (UInt256.land
    (UInt256.div
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (burnPositionUpdateSourceTokensOwedSlot I))
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)) uint128Mask).toNat

abbrev burnPositionUpdateSourceTokensOwed0WriteInt
    (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv)
    (feeGrowthInside0X128 : UInt256) : Int :=
  burnPositionUpdateSourceStoredTokensOwed0Int evm I +
    burnPositionUpdateSourceTokensOwed0Int σ I (Int.ofNat feeGrowthInside0X128.toNat)

abbrev burnPositionUpdateSourceTokensOwed1WriteInt
    (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv)
    (feeGrowthInside1X128 : UInt256) : Int :=
  burnPositionUpdateSourceStoredTokensOwed1Int evm I +
    burnPositionUpdateSourceTokensOwed1Int σ I (Int.ofNat feeGrowthInside1X128.toNat)

abbrev burnPositionUpdateSourceTokensOwed0StoreWord
    (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv)
    (feeGrowthInside0X128 : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.land
      (EVM.wordOfInt
        (burnPositionUpdateSourceTokensOwed0WriteInt evm σ I feeGrowthInside0X128))
      uint128Mask)
    (UInt256.land (UInt256.lnot uint128Mask)
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (burnPositionUpdateSourceTokensOwedSlot I)))

abbrev burnPositionUpdateSourceTokensOwed1StoreWord
    (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv)
    (feeGrowthInside1X128 : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.mul
      (UInt256.land
        (EVM.wordOfInt
          (burnPositionUpdateSourceTokensOwed1WriteInt evm σ I feeGrowthInside1X128))
        uint128Mask)
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩))
    (UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (burnPositionUpdateSourceTokensOwedSlot I))
      uint128Mask)

abbrev burnPositionUpdateSourceAfterTokensOwed0State
    (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv)
    (feeGrowthInside0X128 : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (burnPositionUpdateSourceTokensOwedSlot I)
    (burnPositionUpdateSourceTokensOwed0StoreWord evm σ I feeGrowthInside0X128)

abbrev burnPositionUpdateSourceAfterTokensOwedState
    (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv)
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256) : EVM.State :=
  let evm1 := burnPositionUpdateSourceAfterTokensOwed0State evm σ I feeGrowthInside0X128
  Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
    (burnPositionUpdateSourceTokensOwedSlot I)
    (burnPositionUpdateSourceTokensOwed1StoreWord evm1 σ I feeGrowthInside1X128)

theorem burnPositionUpdateValueAfterLiquidityNext_feeGrowthInside0X128
    (v : PoolImmutables) (σ : AccountMap) (I : ExecutionEnv)
    (feeGrowthInside0X128 feeGrowthInside1X128 : Value) :
    (burnPositionUpdateValueAfterLiquidityNextFrame v σ I feeGrowthInside0X128
        feeGrowthInside1X128).locals.get? "feeGrowthInside0X128" =
      some feeGrowthInside0X128 := by
  rw [burnPositionUpdateValueAfterLiquidityNextFrame]
  rw [store_get_ne (burnPositionUpdateValueAfterPositionFrame v I feeGrowthInside0X128
    feeGrowthInside1X128).locals (k := "liquidityNext") (a := "feeGrowthInside0X128")
    (.int (Int.ofNat (burnPositionUpdateSlot0Packed
      (solcSlotWord σ I (positionsBase (burnPositionKeyKey I)))).toNat))
    (by native_decide)]
  rw [burnPositionUpdateValueAfterPositionFrame]
  rw [store_get_ne (burnPositionUpdateValueStore I feeGrowthInside0X128 feeGrowthInside1X128)
    (k := "position") (a := "feeGrowthInside0X128")
    (.storageRef (burnPositionUpdateEvaledBaseRef I) positionInfoStructTy)
    (by native_decide)]
  exact burnPositionUpdateValueStore_feeGrowthInside0X128 I feeGrowthInside0X128
    feeGrowthInside1X128

theorem burnPositionUpdateValueAfterLiquidityNext_feeGrowthInside1X128
    (v : PoolImmutables) (σ : AccountMap) (I : ExecutionEnv)
    (feeGrowthInside0X128 feeGrowthInside1X128 : Value) :
    (burnPositionUpdateValueAfterLiquidityNextFrame v σ I feeGrowthInside0X128
        feeGrowthInside1X128).locals.get? "feeGrowthInside1X128" =
      some feeGrowthInside1X128 := by
  rw [burnPositionUpdateValueAfterLiquidityNextFrame]
  rw [store_get_ne (burnPositionUpdateValueAfterPositionFrame v I feeGrowthInside0X128
    feeGrowthInside1X128).locals (k := "liquidityNext") (a := "feeGrowthInside1X128")
    (.int (Int.ofNat (burnPositionUpdateSlot0Packed
      (solcSlotWord σ I (positionsBase (burnPositionKeyKey I)))).toNat))
    (by native_decide)]
  rw [burnPositionUpdateValueAfterPositionFrame]
  rw [store_get_ne (burnPositionUpdateValueStore I feeGrowthInside0X128 feeGrowthInside1X128)
    (k := "position") (a := "feeGrowthInside1X128")
    (.storageRef (burnPositionUpdateEvaledBaseRef I) positionInfoStructTy)
    (by native_decide)]
  exact burnPositionUpdateValueStore_feeGrowthInside1X128 I feeGrowthInside0X128
    feeGrowthInside1X128

theorem burnPositionUpdateValue_evalPositionLiquidityAfterLiquidityNext
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : Value) :
    evalExpr? (config v)
      (burnPositionUpdateValueAfterLiquidityNextFrame v σ I feeGrowthInside0X128
        feeGrowthInside1X128)
      (initState cA gh bl σ σ₀ g A I)
      (.field (.var "position") "liquidity") =
        .ok (.int (burnPositionUpdateSourceLiquidityInt σ I)) := by
  simp only [evalExpr?, EvalResult.bind, bind]
  rw [burnPositionUpdateValueAfterLiquidityNext_position (v := v) (σ := σ)]
  simp only [EvalResult.ofOption]
  rw [show storageTypeStep? positionInfoStructTy (.field "liquidity") = some uint128St by
    simp [storageTypeStep?, positionInfoStructTy, uint128St]]
  change
    readStorage? (config v) (initState cA gh bl σ σ₀ g A I)
      (burnPositionUpdateEvaledRef I "liquidity") uint128St =
        .ok (.int (burnPositionUpdateSourceLiquidityInt σ I))
  rw [show uint128St = .elem (.int uint128Int) by rfl]
  rw [readStorage?_elem
    (er := burnPositionUpdateEvaledRef I "liquidity")
    (t := .int uint128Int)
    (loc := loc (positionsBase (burnPositionKeyKey I)) ⟨0, by decide⟩
      ⟨16, by decide⟩ (by decide) (.int uint128Int))]
  · exact congrArg EvalResult.ok (burnPositionUpdate_sourceLiquidityLoad
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g))
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      burnPositionUpdateEvaledRef, burnPositionKeyKey, loc]

theorem burnPositionUpdateValue_evalFeeGrowthInside0AfterLiquidityNext
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : Int) :
    evalExpr? (config v)
      (burnPositionUpdateValueAfterLiquidityNextFrame v σ I (.int feeGrowthInside0X128)
        (.int feeGrowthInside1X128))
      (initState cA gh bl σ σ₀ g A I) (.var "feeGrowthInside0X128") =
        .ok (.int feeGrowthInside0X128) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [burnPositionUpdateValueAfterLiquidityNext_feeGrowthInside0X128
    (v := v) (σ := σ) (I := I)]

theorem burnPositionUpdateValue_evalFeeGrowthInside1AfterLiquidityNext
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : Int) :
    evalExpr? (config v)
      (burnPositionUpdateValueAfterLiquidityNextFrame v σ I (.int feeGrowthInside0X128)
        (.int feeGrowthInside1X128))
      (initState cA gh bl σ σ₀ g A I) (.var "feeGrowthInside1X128") =
        .ok (.int feeGrowthInside1X128) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [burnPositionUpdateValueAfterLiquidityNext_feeGrowthInside1X128
    (v := v) (σ := σ) (I := I)]

theorem burnPositionUpdateValue_evalTokensOwed0AfterLiquidityNext
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : Int) :
    evalExpr? (config v)
      (burnPositionUpdateValueAfterLiquidityNextFrame v σ I (.int feeGrowthInside0X128)
        (.int feeGrowthInside1X128))
      (initState cA gh bl σ σ₀ g A I)
      (uint128Wrap
        (divE
          (mulE
            (wordSub (.var "feeGrowthInside0X128")
              (.field (.var "position") "feeGrowthInside0LastX128"))
            (.field (.var "position") "liquidity"))
          fixedPoint128Q128)) =
        .ok (.int (burnPositionUpdateSourceTokensOwed0Int σ I feeGrowthInside0X128)) := by
  have hfee :=
    burnPositionUpdateValue_evalFeeGrowthInside0AfterLiquidityNext
      (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) feeGrowthInside0X128 feeGrowthInside1X128
  have hlast :=
    burnPositionUpdateValue_evalFeeGrowthInside0LastAfterLiquidityNext
      (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (.int feeGrowthInside0X128) (.int feeGrowthInside1X128)
  have hliq :=
    burnPositionUpdateValue_evalPositionLiquidityAfterLiquidityNext
      (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (.int feeGrowthInside0X128) (.int feeGrowthInside1X128)
  simp [uint128Wrap, divE, mulE, wordSub, modE, subE, uint128Modulus,
    fixedPoint128Q128, uint256Modulus, evalExpr?, EvalResult.bind, bind, pure,
    hfee, hlast, hliq, evalBinaryOp?,
    burnPositionUpdateSourceTokensOwed0Int, burnPositionUpdateSourceLiquidityInt,
    burnPositionUpdateSourceFeeGrowthInside0LastInt,
    burnWordSubInt]

theorem burnPositionUpdateValue_evalTokensOwed1AfterLiquidityNext
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : Int) :
    evalExpr? (config v)
      (burnPositionUpdateValueAfterLiquidityNextFrame v σ I (.int feeGrowthInside0X128)
        (.int feeGrowthInside1X128))
      (initState cA gh bl σ σ₀ g A I)
      (uint128Wrap
        (divE
          (mulE
            (wordSub (.var "feeGrowthInside1X128")
              (.field (.var "position") "feeGrowthInside1LastX128"))
            (.field (.var "position") "liquidity"))
          fixedPoint128Q128)) =
        .ok (.int (burnPositionUpdateSourceTokensOwed1Int σ I feeGrowthInside1X128)) := by
  have hfee :=
    burnPositionUpdateValue_evalFeeGrowthInside1AfterLiquidityNext
      (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) feeGrowthInside0X128 feeGrowthInside1X128
  have hlast :=
    burnPositionUpdateValue_evalFeeGrowthInside1LastAfterLiquidityNext
      (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (.int feeGrowthInside0X128) (.int feeGrowthInside1X128)
  have hliq :=
    burnPositionUpdateValue_evalPositionLiquidityAfterLiquidityNext
      (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (.int feeGrowthInside0X128) (.int feeGrowthInside1X128)
  simp [uint128Wrap, divE, mulE, wordSub, modE, subE, uint128Modulus,
    fixedPoint128Q128, uint256Modulus, evalExpr?, EvalResult.bind, bind, pure,
    hfee, hlast, hliq, evalBinaryOp?,
    burnPositionUpdateSourceTokensOwed1Int, burnPositionUpdateSourceLiquidityInt,
    burnPositionUpdateSourceFeeGrowthInside1LastInt,
    burnWordSubInt]

abbrev burnPositionUpdateValueAfterTokensOwed0Frame
    (v : PoolImmutables) (σ : AccountMap) (I : ExecutionEnv)
    (feeGrowthInside0X128 feeGrowthInside1X128 : Int) : Frame :=
  { contract := contract v,
    locals := (burnPositionUpdateValueAfterLiquidityNextFrame v σ I
      (.int feeGrowthInside0X128) (.int feeGrowthInside1X128)).locals.insert
        "tokensOwed0"
        (.int (burnPositionUpdateSourceTokensOwed0Int σ I feeGrowthInside0X128)) }

abbrev burnPositionUpdateValueAfterTokensOwed1Frame
    (v : PoolImmutables) (σ : AccountMap) (I : ExecutionEnv)
    (feeGrowthInside0X128 feeGrowthInside1X128 : Int) : Frame :=
  { contract := contract v,
    locals := (burnPositionUpdateValueAfterTokensOwed0Frame v σ I feeGrowthInside0X128
      feeGrowthInside1X128).locals.insert "tokensOwed1"
        (.int (burnPositionUpdateSourceTokensOwed1Int σ I feeGrowthInside1X128)) }

theorem burnPositionUpdateValueAfterTokensOwed0_position
    (v : PoolImmutables) (σ : AccountMap) (I : ExecutionEnv)
    (feeGrowthInside0X128 feeGrowthInside1X128 : Int) :
    (burnPositionUpdateValueAfterTokensOwed0Frame v σ I feeGrowthInside0X128
        feeGrowthInside1X128).locals.get? "position" =
      some (.storageRef (burnPositionUpdateEvaledBaseRef I) positionInfoStructTy) := by
  rw [burnPositionUpdateValueAfterTokensOwed0Frame]
  rw [store_get_ne (burnPositionUpdateValueAfterLiquidityNextFrame v σ I
    (.int feeGrowthInside0X128) (.int feeGrowthInside1X128)).locals
    (k := "tokensOwed0") (a := "position")
    (.int (burnPositionUpdateSourceTokensOwed0Int σ I feeGrowthInside0X128))
    (by native_decide)]
  exact burnPositionUpdateValueAfterLiquidityNext_position v σ I
    (.int feeGrowthInside0X128) (.int feeGrowthInside1X128)

theorem burnPositionUpdateValueAfterTokensOwed0_feeGrowthInside1X128
    (v : PoolImmutables) (σ : AccountMap) (I : ExecutionEnv)
    (feeGrowthInside0X128 feeGrowthInside1X128 : Int) :
    (burnPositionUpdateValueAfterTokensOwed0Frame v σ I feeGrowthInside0X128
        feeGrowthInside1X128).locals.get? "feeGrowthInside1X128" =
      some (.int feeGrowthInside1X128) := by
  rw [burnPositionUpdateValueAfterTokensOwed0Frame]
  rw [store_get_ne (burnPositionUpdateValueAfterLiquidityNextFrame v σ I
    (.int feeGrowthInside0X128) (.int feeGrowthInside1X128)).locals
    (k := "tokensOwed0") (a := "feeGrowthInside1X128")
    (.int (burnPositionUpdateSourceTokensOwed0Int σ I feeGrowthInside0X128))
    (by native_decide)]
  exact burnPositionUpdateValueAfterLiquidityNext_feeGrowthInside1X128 v σ I
    (.int feeGrowthInside0X128) (.int feeGrowthInside1X128)

theorem burnPositionUpdateValue_evalFeeGrowthInside1AfterTokensOwed0
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : Int) :
    evalExpr? (config v)
      (burnPositionUpdateValueAfterTokensOwed0Frame v σ I feeGrowthInside0X128
        feeGrowthInside1X128)
      (initState cA gh bl σ σ₀ g A I) (.var "feeGrowthInside1X128") =
        .ok (.int feeGrowthInside1X128) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [burnPositionUpdateValueAfterTokensOwed0_feeGrowthInside1X128
    (v := v) (σ := σ) (I := I)]

theorem burnPositionUpdateValue_evalPositionLiquidityAfterTokensOwed0
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : Int) :
    evalExpr? (config v)
      (burnPositionUpdateValueAfterTokensOwed0Frame v σ I feeGrowthInside0X128
        feeGrowthInside1X128)
      (initState cA gh bl σ σ₀ g A I)
      (.field (.var "position") "liquidity") =
        .ok (.int (burnPositionUpdateSourceLiquidityInt σ I)) := by
  simp only [evalExpr?, EvalResult.bind, bind]
  rw [burnPositionUpdateValueAfterTokensOwed0_position (v := v) (σ := σ)]
  simp only [EvalResult.ofOption]
  rw [show storageTypeStep? positionInfoStructTy (.field "liquidity") = some uint128St by
    simp [storageTypeStep?, positionInfoStructTy, uint128St]]
  change
    readStorage? (config v) (initState cA gh bl σ σ₀ g A I)
      (burnPositionUpdateEvaledRef I "liquidity") uint128St =
        .ok (.int (burnPositionUpdateSourceLiquidityInt σ I))
  rw [show uint128St = .elem (.int uint128Int) by rfl]
  rw [readStorage?_elem
    (er := burnPositionUpdateEvaledRef I "liquidity")
    (t := .int uint128Int)
    (loc := loc (positionsBase (burnPositionKeyKey I)) ⟨0, by decide⟩
      ⟨16, by decide⟩ (by decide) (.int uint128Int))]
  · exact congrArg EvalResult.ok (burnPositionUpdate_sourceLiquidityLoad
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g))
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      burnPositionUpdateEvaledRef, burnPositionKeyKey, loc]

theorem burnPositionUpdateValue_evalFeeGrowthInside1LastAfterTokensOwed0
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : Int) :
    evalExpr? (config v)
      (burnPositionUpdateValueAfterTokensOwed0Frame v σ I feeGrowthInside0X128
        feeGrowthInside1X128)
      (initState cA gh bl σ σ₀ g A I)
      (.field (.var "position") "feeGrowthInside1LastX128") =
        .ok (.int (burnPositionUpdateSourceFeeGrowthInside1LastInt σ I)) := by
  simp only [evalExpr?, EvalResult.bind, bind]
  rw [burnPositionUpdateValueAfterTokensOwed0_position (v := v) (σ := σ)]
  simp only [EvalResult.ofOption]
  rw [show storageTypeStep? positionInfoStructTy (.field "feeGrowthInside1LastX128") =
      some uint256St by simp [storageTypeStep?, positionInfoStructTy, uint256St]]
  change
    readStorage? (config v) (initState cA gh bl σ σ₀ g A I)
      (burnPositionUpdateEvaledRef I "feeGrowthInside1LastX128") uint256St =
        .ok (.int (burnPositionUpdateSourceFeeGrowthInside1LastInt σ I))
  rw [show uint256St = .elem (.int uint256Int) by rfl]
  rw [readStorage?_elem
    (er := burnPositionUpdateEvaledRef I "feeGrowthInside1LastX128")
    (t := .int uint256Int)
    (loc := loc (positionsBase (burnPositionKeyKey I) + ⟨2⟩) ⟨0, by decide⟩
      ⟨32, by decide⟩ (by decide) (.int uint256Int))]
  · simpa [initState, solcSlotWord, burnPositionUpdateSourceFeeGrowthInside1LastInt]
      using burnPositionUpdateStorageLocLoad_feeGrowthInside1Last
        (initState cA gh bl σ σ₀ g A I) (positionsBase (burnPositionKeyKey I))
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      burnPositionUpdateEvaledRef, burnPositionKeyKey, loc]

theorem burnPositionUpdateValue_evalTokensOwed1AfterTokensOwed0
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : Int) :
    evalExpr? (config v)
      (burnPositionUpdateValueAfterTokensOwed0Frame v σ I feeGrowthInside0X128
        feeGrowthInside1X128)
      (initState cA gh bl σ σ₀ g A I)
      (uint128Wrap
        (divE
          (mulE
            (wordSub (.var "feeGrowthInside1X128")
              (.field (.var "position") "feeGrowthInside1LastX128"))
            (.field (.var "position") "liquidity"))
          fixedPoint128Q128)) =
        .ok (.int (burnPositionUpdateSourceTokensOwed1Int σ I feeGrowthInside1X128)) := by
  have hfee :=
    burnPositionUpdateValue_evalFeeGrowthInside1AfterTokensOwed0
      (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) feeGrowthInside0X128 feeGrowthInside1X128
  have hlast :=
    burnPositionUpdateValue_evalFeeGrowthInside1LastAfterTokensOwed0
      (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) feeGrowthInside0X128 feeGrowthInside1X128
  have hliq :=
    burnPositionUpdateValue_evalPositionLiquidityAfterTokensOwed0
      (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) feeGrowthInside0X128 feeGrowthInside1X128
  simp [uint128Wrap, divE, mulE, wordSub, modE, subE, uint128Modulus,
    fixedPoint128Q128, uint256Modulus, evalExpr?, EvalResult.bind, bind, pure,
    hfee, hlast, hliq, evalBinaryOp?,
    burnPositionUpdateSourceTokensOwed1Int, burnPositionUpdateSourceLiquidityInt,
    burnPositionUpdateSourceFeeGrowthInside1LastInt,
    burnWordSubInt]

theorem burnPositionUpdateValueAfterLiquidityNext_liquidityDelta
    (v : PoolImmutables) (σ : AccountMap) (I : ExecutionEnv)
    (feeGrowthInside0X128 feeGrowthInside1X128 : Value) :
    (burnPositionUpdateValueAfterLiquidityNextFrame v σ I feeGrowthInside0X128
        feeGrowthInside1X128).locals.get? "liquidityDelta" =
      some (burnLiquidityDeltaValue I) := by
  rw [burnPositionUpdateValueAfterLiquidityNextFrame]
  rw [store_get_ne (burnPositionUpdateValueAfterPositionFrame v I feeGrowthInside0X128
    feeGrowthInside1X128).locals (k := "liquidityNext") (a := "liquidityDelta")
    (.int (Int.ofNat (burnPositionUpdateSlot0Packed
      (solcSlotWord σ I (positionsBase (burnPositionKeyKey I)))).toNat))
    (by native_decide)]
  exact burnPositionUpdateValueAfterPosition_liquidityDelta v I feeGrowthInside0X128
    feeGrowthInside1X128

theorem burnPositionUpdateValueAfterTokensOwed1_liquidityDelta
    (v : PoolImmutables) (σ : AccountMap) (I : ExecutionEnv)
    (feeGrowthInside0X128 feeGrowthInside1X128 : Int) :
    (burnPositionUpdateValueAfterTokensOwed1Frame v σ I feeGrowthInside0X128
        feeGrowthInside1X128).locals.get? "liquidityDelta" =
      some (burnLiquidityDeltaValue I) := by
  rw [burnPositionUpdateValueAfterTokensOwed1Frame]
  rw [store_get_ne (burnPositionUpdateValueAfterTokensOwed0Frame v σ I
    feeGrowthInside0X128 feeGrowthInside1X128).locals
    (k := "tokensOwed1") (a := "liquidityDelta")
    (.int (burnPositionUpdateSourceTokensOwed1Int σ I feeGrowthInside1X128))
    (by native_decide)]
  rw [burnPositionUpdateValueAfterTokensOwed0Frame]
  rw [store_get_ne (burnPositionUpdateValueAfterLiquidityNextFrame v σ I
    (.int feeGrowthInside0X128) (.int feeGrowthInside1X128)).locals
    (k := "tokensOwed0") (a := "liquidityDelta")
    (.int (burnPositionUpdateSourceTokensOwed0Int σ I feeGrowthInside0X128))
    (by native_decide)]
  exact burnPositionUpdateValueAfterLiquidityNext_liquidityDelta v σ I
    (.int feeGrowthInside0X128) (.int feeGrowthInside1X128)

theorem burnPositionUpdateValue_evalLiquidityDeltaNeZeroFalseAfterTokensOwed1
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : Int)
    (hzero : burnAmountCleanWord I = ⟨0⟩) :
    evalExpr? (config v)
      (burnPositionUpdateValueAfterTokensOwed1Frame v σ I feeGrowthInside0X128
        feeGrowthInside1X128)
      (initState cA gh bl σ σ₀ g A I)
      (neE (.var "liquidityDelta") (.intLit 0)) = .ok (.bool false) := by
  simp only [neE, evalExpr?, EvalResult.bind, bind, pure]
  rw [burnPositionUpdateValueAfterTokensOwed1_liquidityDelta (v := v) (σ := σ)]
  simp [EvalResult.ofOption, burnLiquidityDeltaValue, hzero, evalBinaryOp?]

theorem uniswapV3PoolPositionUpdateSourceZeroDeltaLiquidityNonzeroTokensOwed0PrefixValue
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : Int)
    (hzero : burnAmountCleanWord I = ⟨0⟩)
    (hliq :
      burnPositionUpdateSlot0Packed
          (solcSlotWord σ I (positionsBase (burnPositionKeyKey I))) ≠ ⟨0⟩) :
    ExecBlock (config v)
      (burnPositionUpdateValueFrame v I (.int feeGrowthInside0X128)
        (.int feeGrowthInside1X128))
      (initState cA gh bl σ σ₀ g A I)
      [ .letStorage "position" (positionsRef (.var "positionKey")),
        Stmt.ite (eqE (.var "liquidityDelta") (.intLit 0))
          [ .require (gtE (.field (.var "position") "liquidity") (.intLit 0)),
            .letDecl "liquidityNext" (some uint128)
              (.field (.var "position") "liquidity") ]
          [ .internalCall "liquidityAddDelta"
              [.field (.var "position") "liquidity", .var "liquidityDelta"]
              "liquidityNext" ],
        .letDecl "tokensOwed0" (some uint128)
          (uint128Wrap
            (divE
              (mulE
                (wordSub (.var "feeGrowthInside0X128")
                  (.field (.var "position") "feeGrowthInside0LastX128"))
                (.field (.var "position") "liquidity"))
              fixedPoint128Q128)) ]
      (ExecResult.ok
        (burnPositionUpdateValueAfterTokensOwed0Frame v σ I feeGrowthInside0X128
          feeGrowthInside1X128)
        (initState cA gh bl σ σ₀ g A I)) := by
  have hprefix :=
    uniswapV3PoolPositionUpdateSourceZeroDeltaLiquidityNonzeroPrefixValue
      (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (.int feeGrowthInside0X128) (.int feeGrowthInside1X128)
      hzero hliq
  have htail :
      ExecBlock (config v)
        (burnPositionUpdateValueAfterLiquidityNextFrame v σ I
          (.int feeGrowthInside0X128) (.int feeGrowthInside1X128))
        (initState cA gh bl σ σ₀ g A I)
        [ .letDecl "tokensOwed0" (some uint128)
          (uint128Wrap
            (divE
              (mulE
                (wordSub (.var "feeGrowthInside0X128")
                  (.field (.var "position") "feeGrowthInside0LastX128"))
                (.field (.var "position") "liquidity"))
              fixedPoint128Q128)) ]
        (ExecResult.ok
          (burnPositionUpdateValueAfterTokensOwed0Frame v σ I feeGrowthInside0X128
            feeGrowthInside1X128)
          (initState cA gh bl σ σ₀ g A I)) := by
    exact ExecBlock.consNormal
      (ExecStmt.letDecl
        (burnPositionUpdateValue_evalTokensOwed0AfterLiquidityNext
          (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) feeGrowthInside0X128 feeGrowthInside1X128))
      ExecBlock.nil
  simpa using execBlock_append hprefix htail

theorem uniswapV3PoolPositionUpdateSourceZeroDeltaLiquidityNonzeroTokensOwedPrefixValue
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : Int)
    (hzero : burnAmountCleanWord I = ⟨0⟩)
    (hliq :
      burnPositionUpdateSlot0Packed
          (solcSlotWord σ I (positionsBase (burnPositionKeyKey I))) ≠ ⟨0⟩) :
    ExecBlock (config v)
      (burnPositionUpdateValueFrame v I (.int feeGrowthInside0X128)
        (.int feeGrowthInside1X128))
      (initState cA gh bl σ σ₀ g A I)
      [ .letStorage "position" (positionsRef (.var "positionKey")),
        Stmt.ite (eqE (.var "liquidityDelta") (.intLit 0))
          [ .require (gtE (.field (.var "position") "liquidity") (.intLit 0)),
            .letDecl "liquidityNext" (some uint128)
              (.field (.var "position") "liquidity") ]
          [ .internalCall "liquidityAddDelta"
              [.field (.var "position") "liquidity", .var "liquidityDelta"]
              "liquidityNext" ],
        .letDecl "tokensOwed0" (some uint128)
          (uint128Wrap
            (divE
              (mulE
                (wordSub (.var "feeGrowthInside0X128")
                  (.field (.var "position") "feeGrowthInside0LastX128"))
                (.field (.var "position") "liquidity"))
              fixedPoint128Q128)),
        .letDecl "tokensOwed1" (some uint128)
          (uint128Wrap
            (divE
              (mulE
                (wordSub (.var "feeGrowthInside1X128")
                  (.field (.var "position") "feeGrowthInside1LastX128"))
                (.field (.var "position") "liquidity"))
              fixedPoint128Q128)) ]
      (ExecResult.ok
        (burnPositionUpdateValueAfterTokensOwed1Frame v σ I feeGrowthInside0X128
          feeGrowthInside1X128)
        (initState cA gh bl σ σ₀ g A I)) := by
  have hprefix :=
    uniswapV3PoolPositionUpdateSourceZeroDeltaLiquidityNonzeroTokensOwed0PrefixValue
      (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) feeGrowthInside0X128 feeGrowthInside1X128 hzero hliq
  have htail :
      ExecBlock (config v)
        (burnPositionUpdateValueAfterTokensOwed0Frame v σ I feeGrowthInside0X128
          feeGrowthInside1X128)
        (initState cA gh bl σ σ₀ g A I)
        [ .letDecl "tokensOwed1" (some uint128)
          (uint128Wrap
            (divE
              (mulE
                (wordSub (.var "feeGrowthInside1X128")
                  (.field (.var "position") "feeGrowthInside1LastX128"))
                (.field (.var "position") "liquidity"))
              fixedPoint128Q128)) ]
        (ExecResult.ok
          (burnPositionUpdateValueAfterTokensOwed1Frame v σ I feeGrowthInside0X128
            feeGrowthInside1X128)
          (initState cA gh bl σ σ₀ g A I)) := by
    exact ExecBlock.consNormal
      (ExecStmt.letDecl
        (burnPositionUpdateValue_evalTokensOwed1AfterTokensOwed0
          (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) feeGrowthInside0X128 feeGrowthInside1X128))
      ExecBlock.nil
  simpa using execBlock_append hprefix htail

theorem uniswapV3PoolPositionUpdateSourceZeroDeltaLiquidityNonzeroLiquiditySkipPrefixValue
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : Int)
    (hzero : burnAmountCleanWord I = ⟨0⟩)
    (hliq :
      burnPositionUpdateSlot0Packed
          (solcSlotWord σ I (positionsBase (burnPositionKeyKey I))) ≠ ⟨0⟩) :
    ExecBlock (config v)
      (burnPositionUpdateValueFrame v I (.int feeGrowthInside0X128)
        (.int feeGrowthInside1X128))
      (initState cA gh bl σ σ₀ g A I)
      [ .letStorage "position" (positionsRef (.var "positionKey")),
        Stmt.ite (eqE (.var "liquidityDelta") (.intLit 0))
          [ .require (gtE (.field (.var "position") "liquidity") (.intLit 0)),
            .letDecl "liquidityNext" (some uint128)
              (.field (.var "position") "liquidity") ]
          [ .internalCall "liquidityAddDelta"
              [.field (.var "position") "liquidity", .var "liquidityDelta"]
              "liquidityNext" ],
        .letDecl "tokensOwed0" (some uint128)
          (uint128Wrap
            (divE
              (mulE
                (wordSub (.var "feeGrowthInside0X128")
                  (.field (.var "position") "feeGrowthInside0LastX128"))
                (.field (.var "position") "liquidity"))
              fixedPoint128Q128)),
        .letDecl "tokensOwed1" (some uint128)
          (uint128Wrap
            (divE
              (mulE
                (wordSub (.var "feeGrowthInside1X128")
                  (.field (.var "position") "feeGrowthInside1LastX128"))
                (.field (.var "position") "liquidity"))
              fixedPoint128Q128)),
        Stmt.ite (neE (.var "liquidityDelta") (.intLit 0))
          [ .assign .storage { base := "position", steps := [.field "liquidity"] }
              (.var "liquidityNext") ]
          [] ]
      (ExecResult.ok
        (burnPositionUpdateValueAfterTokensOwed1Frame v σ I feeGrowthInside0X128
          feeGrowthInside1X128)
        (initState cA gh bl σ σ₀ g A I)) := by
  have hprefix :=
    uniswapV3PoolPositionUpdateSourceZeroDeltaLiquidityNonzeroTokensOwedPrefixValue
      (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) feeGrowthInside0X128 feeGrowthInside1X128 hzero hliq
  have htail :
      ExecBlock (config v)
        (burnPositionUpdateValueAfterTokensOwed1Frame v σ I feeGrowthInside0X128
          feeGrowthInside1X128)
        (initState cA gh bl σ σ₀ g A I)
        [ Stmt.ite (neE (.var "liquidityDelta") (.intLit 0))
          [ .assign .storage { base := "position", steps := [.field "liquidity"] }
              (.var "liquidityNext") ]
          [] ]
        (ExecResult.ok
          (burnPositionUpdateValueAfterTokensOwed1Frame v σ I feeGrowthInside0X128
            feeGrowthInside1X128)
          (initState cA gh bl σ σ₀ g A I)) := by
    refine ExecBlock.consNormal (ExecStmt.iteFalse
      (burnPositionUpdateValue_evalLiquidityDeltaNeZeroFalseAfterTokensOwed1
        (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) feeGrowthInside0X128 feeGrowthInside1X128 hzero)
      ?_) ExecBlock.nil
    exact ExecBlock.nil
  simpa using execBlock_append hprefix htail

theorem burnPositionUpdateValueAfterTokensOwed1_position
    (v : PoolImmutables) (σ : AccountMap) (I : ExecutionEnv)
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256) :
    (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
        (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat)).locals.get?
        "position" =
      some (.storageRef (burnPositionUpdateEvaledBaseRef I) positionInfoStructTy) := by
  rw [burnPositionUpdateValueAfterTokensOwed1Frame]
  rw [store_get_ne (burnPositionUpdateValueAfterTokensOwed0Frame v σ I
    (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat)).locals
    (k := "tokensOwed1") (a := "position")
    (.int (burnPositionUpdateSourceTokensOwed1Int σ I
      (Int.ofNat feeGrowthInside1X128.toNat))) (by native_decide)]
  exact burnPositionUpdateValueAfterTokensOwed0_position v σ I
    (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat)

theorem burnPositionUpdateValueAfterTokensOwed1_feeGrowthInside0X128
    (v : PoolImmutables) (σ : AccountMap) (I : ExecutionEnv)
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256) :
    (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
        (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat)).locals.get?
        "feeGrowthInside0X128" =
      some (.int (Int.ofNat feeGrowthInside0X128.toNat)) := by
  rw [burnPositionUpdateValueAfterTokensOwed1Frame]
  rw [store_get_ne (burnPositionUpdateValueAfterTokensOwed0Frame v σ I
    (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat)).locals
    (k := "tokensOwed1") (a := "feeGrowthInside0X128")
    (.int (burnPositionUpdateSourceTokensOwed1Int σ I
      (Int.ofNat feeGrowthInside1X128.toNat))) (by native_decide)]
  rw [burnPositionUpdateValueAfterTokensOwed0Frame]
  rw [store_get_ne (burnPositionUpdateValueAfterLiquidityNextFrame v σ I
    (.int (Int.ofNat feeGrowthInside0X128.toNat))
    (.int (Int.ofNat feeGrowthInside1X128.toNat))).locals
    (k := "tokensOwed0") (a := "feeGrowthInside0X128")
    (.int (burnPositionUpdateSourceTokensOwed0Int σ I
      (Int.ofNat feeGrowthInside0X128.toNat))) (by native_decide)]
  rw [burnPositionUpdateValueAfterLiquidityNext_feeGrowthInside0X128]

theorem burnPositionUpdateValueAfterTokensOwed1_feeGrowthInside1X128
    (v : PoolImmutables) (σ : AccountMap) (I : ExecutionEnv)
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256) :
    (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
        (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat)).locals.get?
        "feeGrowthInside1X128" =
      some (.int (Int.ofNat feeGrowthInside1X128.toNat)) := by
  rw [burnPositionUpdateValueAfterTokensOwed1Frame]
  rw [store_get_ne (burnPositionUpdateValueAfterTokensOwed0Frame v σ I
    (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat)).locals
    (k := "tokensOwed1") (a := "feeGrowthInside1X128")
    (.int (burnPositionUpdateSourceTokensOwed1Int σ I
      (Int.ofNat feeGrowthInside1X128.toNat))) (by native_decide)]
  exact burnPositionUpdateValueAfterTokensOwed0_feeGrowthInside1X128 v σ I
    (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat)

theorem burnPositionUpdateValue_evalFeeGrowthInside0AfterTokensOwed1
    {v : PoolImmutables} {evm σ I}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256) :
    evalExpr? (config v)
      (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
        (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
      evm (.var "feeGrowthInside0X128") =
        .ok (.int (Int.ofNat feeGrowthInside0X128.toNat)) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [burnPositionUpdateValueAfterTokensOwed1_feeGrowthInside0X128
    (v := v) (σ := σ) (I := I)]

theorem burnPositionUpdateValue_evalFeeGrowthInside1AfterTokensOwed1
    {v : PoolImmutables} {evm σ I}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256) :
    evalExpr? (config v)
      (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
        (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
      evm (.var "feeGrowthInside1X128") =
        .ok (.int (Int.ofNat feeGrowthInside1X128.toNat)) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [burnPositionUpdateValueAfterTokensOwed1_feeGrowthInside1X128
    (v := v) (σ := σ) (I := I)]

theorem burnPositionUpdateValue_resolveFeeGrowthInside0LastAfterTokensOwed1
    {v : PoolImmutables} {evm : EVM.State} {σ I}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256) :
    resolveStorageRef? (config v)
      (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
        (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
      evm { base := "position", steps := [.field "feeGrowthInside0LastX128"] } =
        .ok (burnPositionUpdateEvaledRef I "feeGrowthInside0LastX128", uint256St) := by
  rw [resolveStorageRef?]
  rw [burnPositionUpdateValueAfterTokensOwed1_position]
  simp [evalStorageRefFrom?, evalStorageRefStep, EvalResult.bind, EvalResult.ofOption, bind,
    pure, burnPositionUpdateEvaledRef, burnPositionUpdateEvaledBaseRef, uint256St,
    storageTypeStep?, positionInfoStructTy]

theorem burnPositionUpdateValue_resolveFeeGrowthInside1LastAfterTokensOwed1
    {v : PoolImmutables} {evm : EVM.State} {σ I}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256) :
    resolveStorageRef? (config v)
      (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
        (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
      evm { base := "position", steps := [.field "feeGrowthInside1LastX128"] } =
        .ok (burnPositionUpdateEvaledRef I "feeGrowthInside1LastX128", uint256St) := by
  rw [resolveStorageRef?]
  rw [burnPositionUpdateValueAfterTokensOwed1_position]
  simp [evalStorageRefFrom?, evalStorageRefStep, EvalResult.bind, EvalResult.ofOption, bind,
    pure, burnPositionUpdateEvaledRef, burnPositionUpdateEvaledBaseRef, uint256St,
    storageTypeStep?, positionInfoStructTy]

theorem burnPositionUpdateValue_assignFeeGrowthInside0LastAfterTokensOwed1
    {v : PoolImmutables} {evm : EVM.State} {σ I}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256) :
    assignStorageRef? (config v)
      (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
        (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
      evm .storage { base := "position", steps := [.field "feeGrowthInside0LastX128"] }
      (.int (Int.ofNat feeGrowthInside0X128.toNat)) =
        .ok ((burnPositionUpdateValueAfterTokensOwed1Frame v σ I
          (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat)),
          Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (positionsBase (burnPositionKeyKey I) + ⟨1⟩) feeGrowthInside0X128) := by
  rw [assignStorageRef?]
  rw [burnPositionUpdateValue_resolveFeeGrowthInside0LastAfterTokensOwed1]
  simp only [EvalResult.bind, bind, EvalResult.ofOption, pure]
  rw [show (config v).storage.layout (burnPositionUpdateEvaledRef I
      "feeGrowthInside0LastX128") =
      fun _ => some (loc (positionsBase (burnPositionKeyKey I) + ⟨1⟩) ⟨0, by decide⟩
        ⟨32, by decide⟩ (by decide) (.int uint256Int)) by
    funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      burnPositionUpdateEvaledRef, burnPositionKeyKey, loc]]
  simp only [EvalResult.bind, bind, EvalResult.ofOption, pure]
  have hstore :
      storageLocStore evm
          (loc (positionsBase (burnPositionKeyKey I) + ⟨1⟩) ⟨0, by decide⟩
            ⟨32, by decide⟩ (by decide) (.int uint256Int))
          (.int (Int.ofNat feeGrowthInside0X128.toNat)) =
        some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (positionsBase (burnPositionKeyKey I) + ⟨1⟩) feeGrowthInside0X128) := by
    simpa [loc, uint256Loc] using
      storageLocStore_uint256 evm (positionsBase (burnPositionKeyKey I) + ⟨1⟩)
        feeGrowthInside0X128
  rw [hstore]

theorem burnPositionUpdateValue_assignFeeGrowthInside1LastAfterTokensOwed1
    {v : PoolImmutables} {evm : EVM.State} {σ I}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256) :
    assignStorageRef? (config v)
      (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
        (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
      evm .storage { base := "position", steps := [.field "feeGrowthInside1LastX128"] }
      (.int (Int.ofNat feeGrowthInside1X128.toNat)) =
        .ok ((burnPositionUpdateValueAfterTokensOwed1Frame v σ I
          (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat)),
          Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (positionsBase (burnPositionKeyKey I) + ⟨2⟩) feeGrowthInside1X128) := by
  rw [assignStorageRef?]
  rw [burnPositionUpdateValue_resolveFeeGrowthInside1LastAfterTokensOwed1]
  simp only [EvalResult.bind, bind, EvalResult.ofOption, pure]
  rw [show (config v).storage.layout (burnPositionUpdateEvaledRef I
      "feeGrowthInside1LastX128") =
      fun _ => some (loc (positionsBase (burnPositionKeyKey I) + ⟨2⟩) ⟨0, by decide⟩
        ⟨32, by decide⟩ (by decide) (.int uint256Int)) by
    funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      burnPositionUpdateEvaledRef, burnPositionKeyKey, loc]]
  simp only [EvalResult.bind, bind, EvalResult.ofOption, pure]
  have hstore :
      storageLocStore evm
          (loc (positionsBase (burnPositionKeyKey I) + ⟨2⟩) ⟨0, by decide⟩
            ⟨32, by decide⟩ (by decide) (.int uint256Int))
          (.int (Int.ofNat feeGrowthInside1X128.toNat)) =
        some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (positionsBase (burnPositionKeyKey I) + ⟨2⟩) feeGrowthInside1X128) := by
    simpa [loc, uint256Loc] using
      storageLocStore_uint256 evm (positionsBase (burnPositionKeyKey I) + ⟨2⟩)
        feeGrowthInside1X128
  rw [hstore]

theorem uniswapV3PoolPositionUpdateSourceZeroDeltaLiquidityNonzeroFeeGrowthLastTailValue
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256) :
    ExecBlock (config v)
      (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
        (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
      (initState cA gh bl σ σ₀ g A I)
      [ .assign .storage { base := "position", steps := [.field "feeGrowthInside0LastX128"] }
          (.var "feeGrowthInside0X128"),
        .assign .storage { base := "position", steps := [.field "feeGrowthInside1LastX128"] }
          (.var "feeGrowthInside1X128") ]
      (ExecResult.ok
        (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
          (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner
            (positionsBase (burnPositionKeyKey I) + ⟨1⟩) feeGrowthInside0X128)
          I.codeOwner (positionsBase (burnPositionKeyKey I) + ⟨2⟩)
          feeGrowthInside1X128)) := by
  let frame := burnPositionUpdateValueAfterTokensOwed1Frame v σ I
    (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat)
  let evm0 := initState cA gh bl σ σ₀ g A I
  let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
    (positionsBase (burnPositionKeyKey I) + ⟨1⟩) feeGrowthInside0X128
  let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
    (positionsBase (burnPositionKeyKey I) + ⟨2⟩) feeGrowthInside1X128
  have hassign0 :
      assignStorageRef? (config v) frame evm0 .storage
        { base := "position", steps := [.field "feeGrowthInside0LastX128"] }
        (.int (Int.ofNat feeGrowthInside0X128.toNat)) = .ok (frame, evm1) := by
    simpa [frame, evm0, evm1] using
      burnPositionUpdateValue_assignFeeGrowthInside0LastAfterTokensOwed1
        (v := v) (evm := evm0) (σ := σ) (I := I)
        feeGrowthInside0X128 feeGrowthInside1X128
  have hstep0 :
      ExecStmt (config v) frame evm0
        (.assign .storage { base := "position", steps := [.field "feeGrowthInside0LastX128"] }
          (.var "feeGrowthInside0X128")) (.ok frame evm1) := by
    exact ExecStmt.assign
      (burnPositionUpdateValue_evalFeeGrowthInside0AfterTokensOwed1
        (v := v) (evm := evm0) (σ := σ) (I := I)
        feeGrowthInside0X128 feeGrowthInside1X128)
      hassign0
  have hassign1 :
      assignStorageRef? (config v) frame evm1 .storage
        { base := "position", steps := [.field "feeGrowthInside1LastX128"] }
        (.int (Int.ofNat feeGrowthInside1X128.toNat)) = .ok (frame, evm2) := by
    simpa [frame, evm1, evm2] using
      burnPositionUpdateValue_assignFeeGrowthInside1LastAfterTokensOwed1
        (v := v) (evm := evm1) (σ := σ) (I := I)
        feeGrowthInside0X128 feeGrowthInside1X128
  have hstep1 :
      ExecStmt (config v) frame evm1
        (.assign .storage { base := "position", steps := [.field "feeGrowthInside1LastX128"] }
          (.var "feeGrowthInside1X128")) (.ok frame evm2) := by
    exact ExecStmt.assign
      (burnPositionUpdateValue_evalFeeGrowthInside1AfterTokensOwed1
        (v := v) (evm := evm1) (σ := σ) (I := I)
        feeGrowthInside0X128 feeGrowthInside1X128)
      hassign1
  simpa [frame, evm0, evm1, evm2, initState, storageStore_executionEnv] using
    ExecBlock.consNormal hstep0 (ExecBlock.consNormal hstep1 ExecBlock.nil)

theorem uniswapV3PoolPositionUpdateSourceZeroDeltaLiquidityNonzeroFeeGrowthLastPrefixValue
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256)
    (hzero : burnAmountCleanWord I = ⟨0⟩)
    (hliq :
      burnPositionUpdateSlot0Packed
          (solcSlotWord σ I (positionsBase (burnPositionKeyKey I))) ≠ ⟨0⟩) :
    ExecBlock (config v)
      (burnPositionUpdateValueFrame v I (.int (Int.ofNat feeGrowthInside0X128.toNat))
        (.int (Int.ofNat feeGrowthInside1X128.toNat)))
      (initState cA gh bl σ σ₀ g A I)
      [ .letStorage "position" (positionsRef (.var "positionKey")),
        Stmt.ite (eqE (.var "liquidityDelta") (.intLit 0))
          [ .require (gtE (.field (.var "position") "liquidity") (.intLit 0)),
            .letDecl "liquidityNext" (some uint128)
              (.field (.var "position") "liquidity") ]
          [ .internalCall "liquidityAddDelta"
              [.field (.var "position") "liquidity", .var "liquidityDelta"]
              "liquidityNext" ],
        .letDecl "tokensOwed0" (some uint128)
          (uint128Wrap
            (divE
              (mulE
                (wordSub (.var "feeGrowthInside0X128")
                  (.field (.var "position") "feeGrowthInside0LastX128"))
                (.field (.var "position") "liquidity"))
              fixedPoint128Q128)),
        .letDecl "tokensOwed1" (some uint128)
          (uint128Wrap
            (divE
              (mulE
                (wordSub (.var "feeGrowthInside1X128")
                  (.field (.var "position") "feeGrowthInside1LastX128"))
                (.field (.var "position") "liquidity"))
              fixedPoint128Q128)),
        Stmt.ite (neE (.var "liquidityDelta") (.intLit 0))
          [ .assign .storage { base := "position", steps := [.field "liquidity"] }
              (.var "liquidityNext") ]
          [],
        .assign .storage { base := "position", steps := [.field "feeGrowthInside0LastX128"] }
          (.var "feeGrowthInside0X128"),
        .assign .storage { base := "position", steps := [.field "feeGrowthInside1LastX128"] }
          (.var "feeGrowthInside1X128") ]
      (ExecResult.ok
        (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
          (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner
            (positionsBase (burnPositionKeyKey I) + ⟨1⟩) feeGrowthInside0X128)
          I.codeOwner (positionsBase (burnPositionKeyKey I) + ⟨2⟩)
          feeGrowthInside1X128)) := by
  have hprefix :=
    uniswapV3PoolPositionUpdateSourceZeroDeltaLiquidityNonzeroLiquiditySkipPrefixValue
      (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (Int.ofNat feeGrowthInside0X128.toNat)
      (Int.ofNat feeGrowthInside1X128.toNat) hzero hliq
  have htail :=
    uniswapV3PoolPositionUpdateSourceZeroDeltaLiquidityNonzeroFeeGrowthLastTailValue
      (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) feeGrowthInside0X128 feeGrowthInside1X128
  simpa using execBlock_append hprefix htail

theorem burnPositionUpdateValueAfterTokensOwed1_tokensOwed0
    (v : PoolImmutables) (σ : AccountMap) (I : ExecutionEnv)
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256) :
    (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
        (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat)).locals.get?
        "tokensOwed0" =
      some (.int (burnPositionUpdateSourceTokensOwed0Int σ I
        (Int.ofNat feeGrowthInside0X128.toNat))) := by
  rw [burnPositionUpdateValueAfterTokensOwed1Frame]
  rw [store_get_ne (burnPositionUpdateValueAfterTokensOwed0Frame v σ I
    (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat)).locals
    (k := "tokensOwed1") (a := "tokensOwed0")
    (.int (burnPositionUpdateSourceTokensOwed1Int σ I
      (Int.ofNat feeGrowthInside1X128.toNat))) (by native_decide)]
  rw [burnPositionUpdateValueAfterTokensOwed0Frame]
  exact store_get_self (burnPositionUpdateValueAfterLiquidityNextFrame v σ I
    (.int (Int.ofNat feeGrowthInside0X128.toNat))
    (.int (Int.ofNat feeGrowthInside1X128.toNat))).locals "tokensOwed0"
    (.int (burnPositionUpdateSourceTokensOwed0Int σ I
      (Int.ofNat feeGrowthInside0X128.toNat)))

theorem burnPositionUpdateValueAfterTokensOwed1_tokensOwed1
    (v : PoolImmutables) (σ : AccountMap) (I : ExecutionEnv)
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256) :
    (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
        (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat)).locals.get?
        "tokensOwed1" =
      some (.int (burnPositionUpdateSourceTokensOwed1Int σ I
        (Int.ofNat feeGrowthInside1X128.toNat))) := by
  rw [burnPositionUpdateValueAfterTokensOwed1Frame]
  exact store_get_self (burnPositionUpdateValueAfterTokensOwed0Frame v σ I
    (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat)).locals
    "tokensOwed1"
    (.int (burnPositionUpdateSourceTokensOwed1Int σ I
      (Int.ofNat feeGrowthInside1X128.toNat)))

theorem burnPositionUpdateValue_evalTokensOwedGtFalseAfterTokensOwed1
    {v : PoolImmutables} {evm σ I}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256)
    (htokens0 :
      burnPositionUpdateSourceTokensOwed0Int σ I
          (Int.ofNat feeGrowthInside0X128.toNat) = 0)
    (htokens1 :
      burnPositionUpdateSourceTokensOwed1Int σ I
          (Int.ofNat feeGrowthInside1X128.toNat) = 0) :
    evalExpr? (config v)
      (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
        (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
      evm
      (orE (gtE (.var "tokensOwed0") (.intLit 0))
        (gtE (.var "tokensOwed1") (.intLit 0))) = .ok (.bool false) := by
  have hgt0 :
      evalExpr? (config v)
        (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
          (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
        evm (gtE (.var "tokensOwed0") (.intLit 0)) = .ok (.bool false) := by
    simp only [gtE, evalExpr?, EvalResult.bind, bind, pure]
    rw [burnPositionUpdateValueAfterTokensOwed1_tokensOwed0 (v := v) (σ := σ) (I := I)]
    rw [htokens0]
    native_decide
  have hgt1 :
      evalExpr? (config v)
        (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
          (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
        evm (gtE (.var "tokensOwed1") (.intLit 0)) = .ok (.bool false) := by
    simp only [gtE, evalExpr?, EvalResult.bind, bind, pure]
    rw [burnPositionUpdateValueAfterTokensOwed1_tokensOwed1 (v := v) (σ := σ) (I := I)]
    rw [htokens1]
    native_decide
  simp only [orE, evalExpr?, EvalResult.bind, bind, pure]
  rw [hgt0]
  rw [hgt1]

theorem burnPositionUpdateValue_evalTokensOwedGtTrueAfterTokensOwed1_left
    {v : PoolImmutables} {evm σ I}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256)
    (htokens0 :
      0 < burnPositionUpdateSourceTokensOwed0Int σ I
          (Int.ofNat feeGrowthInside0X128.toNat)) :
    evalExpr? (config v)
      (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
        (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
      evm
      (orE (gtE (.var "tokensOwed0") (.intLit 0))
        (gtE (.var "tokensOwed1") (.intLit 0))) = .ok (.bool true) := by
  have hgt0 :
      evalExpr? (config v)
        (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
          (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
        evm (gtE (.var "tokensOwed0") (.intLit 0)) = .ok (.bool true) := by
    simp only [gtE, evalExpr?, EvalResult.bind, bind, pure]
    rw [burnPositionUpdateValueAfterTokensOwed1_tokensOwed0 (v := v) (σ := σ) (I := I)]
    simp only [evalBinaryOp?]
    exact congrArg (fun b => EvalResult.ok (Value.bool b)) (decide_eq_true htokens0)
  simp only [orE, evalExpr?, EvalResult.bind, bind, pure]
  rw [hgt0]

theorem burnPositionUpdateValue_evalTokensOwedGtTrueAfterTokensOwed1_right
    {v : PoolImmutables} {evm σ I}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256)
    (htokens0 :
      burnPositionUpdateSourceTokensOwed0Int σ I
          (Int.ofNat feeGrowthInside0X128.toNat) = 0)
    (htokens1 :
      0 < burnPositionUpdateSourceTokensOwed1Int σ I
          (Int.ofNat feeGrowthInside1X128.toNat)) :
    evalExpr? (config v)
      (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
        (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
      evm
      (orE (gtE (.var "tokensOwed0") (.intLit 0))
        (gtE (.var "tokensOwed1") (.intLit 0))) = .ok (.bool true) := by
  have hgt0 :
      evalExpr? (config v)
        (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
          (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
        evm (gtE (.var "tokensOwed0") (.intLit 0)) = .ok (.bool false) := by
    simp only [gtE, evalExpr?, EvalResult.bind, bind, pure]
    rw [burnPositionUpdateValueAfterTokensOwed1_tokensOwed0 (v := v) (σ := σ) (I := I)]
    rw [htokens0]
    native_decide
  have hgt1 :
      evalExpr? (config v)
        (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
          (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
        evm (gtE (.var "tokensOwed1") (.intLit 0)) = .ok (.bool true) := by
    simp only [gtE, evalExpr?, EvalResult.bind, bind, pure]
    rw [burnPositionUpdateValueAfterTokensOwed1_tokensOwed1 (v := v) (σ := σ) (I := I)]
    simp only [evalBinaryOp?]
    exact congrArg (fun b => EvalResult.ok (Value.bool b)) (decide_eq_true htokens1)
  simp only [orE, evalExpr?, EvalResult.bind, bind, pure]
  rw [hgt0]
  rw [hgt1]

theorem burnPositionUpdateValue_resolveTokensOwed0AfterTokensOwed1
    {v : PoolImmutables} {evm : EVM.State} {σ I}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256) :
    resolveStorageRef? (config v)
      (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
        (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
      evm { base := "position", steps := [.field "tokensOwed0"] } =
        .ok (burnPositionUpdateEvaledRef I "tokensOwed0", uint128St) := by
  rw [resolveStorageRef?]
  rw [burnPositionUpdateValueAfterTokensOwed1_position]
  simp [evalStorageRefFrom?, evalStorageRefStep, EvalResult.bind, EvalResult.ofOption, bind,
    pure, burnPositionUpdateEvaledRef, burnPositionUpdateEvaledBaseRef, uint128St,
    storageTypeStep?, positionInfoStructTy]

theorem burnPositionUpdateValue_resolveTokensOwed1AfterTokensOwed1
    {v : PoolImmutables} {evm : EVM.State} {σ I}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256) :
    resolveStorageRef? (config v)
      (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
        (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
      evm { base := "position", steps := [.field "tokensOwed1"] } =
        .ok (burnPositionUpdateEvaledRef I "tokensOwed1", uint128St) := by
  rw [resolveStorageRef?]
  rw [burnPositionUpdateValueAfterTokensOwed1_position]
  simp [evalStorageRefFrom?, evalStorageRefStep, EvalResult.bind, EvalResult.ofOption, bind,
    pure, burnPositionUpdateEvaledRef, burnPositionUpdateEvaledBaseRef, uint128St,
    storageTypeStep?, positionInfoStructTy]

theorem burnPositionUpdateStorageLocLoad_tokensOwed0
    (evm : EVM.State) (base : UInt256) :
    storageLocLoad evm
        (loc (base + ⟨3⟩) ⟨0, by decide⟩ ⟨16, by decide⟩ (by decide)
          (.int uint128Int)) =
      .int (Int.ofNat (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (base + ⟨3⟩))
        uint128Mask).toNat) := by
  rw [← show UInt256.ofNat (2 ^ (8 * 16) - 1) = uint128Mask by native_decide]
  simpa [loc, uint128Int] using
    storageLocLoad_uint_offset0 evm (base + ⟨3⟩) (16 : Fin 33) ⟨128, by decide⟩
      (hbound := by decide) (by decide)

theorem burnPositionUpdateStorageLocLoad_tokensOwed1
    (evm : EVM.State) (base : UInt256) :
    storageLocLoad evm
        (loc (base + ⟨3⟩) ⟨16, by decide⟩ ⟨16, by decide⟩ (by decide)
          (.int uint128Int)) =
      .int (Int.ofNat (UInt256.land
        (UInt256.div
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (base + ⟨3⟩))
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)) uint128Mask).toNat) := by
  rw [← show UInt256.ofNat ((256 : Nat) ^ (16 : Nat)) =
    UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩ by native_decide]
  rw [← show UInt256.ofNat ((256 : Nat) ^ (16 : Nat) - 1) = uint128Mask by native_decide]
  simpa [loc, uint128Int] using
    storageLocLoad_uint_offset evm (base + ⟨3⟩) (16 : Fin 32) (16 : Fin 33)
      ⟨128, by decide⟩ (by decide) (by decide)

private theorem burnPositionUpdateLow128_insert_toNat (low old : UInt256)
    (hlow : low.toNat < 2 ^ 128) :
    (UInt256.lor low (UInt256.land (UInt256.lnot uint128Mask) old)).toNat =
      low.toNat + old.toNat / 2 ^ 128 * 2 ^ 128 := by
  rw [u256_lor_toNat]
  have hclearMask :
      UInt256.lnot uint128Mask = UInt256.ofNat ((2 : Nat) ^ 256 - 2 ^ 128) := by
    native_decide
  have hhigh :
      (UInt256.land (UInt256.lnot uint128Mask) old).toNat =
        old.toNat / 2 ^ 128 * 2 ^ 128 := by
    rw [hclearMask]
    exact u256_land_high_mask_toNat old 128 (by norm_num)
  have hq : old.toNat / 2 ^ 128 < 2 ^ 128 := by
    apply Nat.div_lt_of_lt_mul
    rw [show 2 ^ 128 * 2 ^ 128 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
    change old.val.val < 2 ^ 256
    simp [UInt256.size]
  have hlorLt :
      Nat.lor low.toNat ((UInt256.land (UInt256.lnot uint128Mask) old).toNat) <
        UInt256.size := by
    rw [hhigh]
    rw [nat_lor_shift_add low.toNat (old.toNat / 2 ^ 128) 128 hlow]
    have hqle : old.toNat / 2 ^ 128 ≤ 2 ^ 128 - 1 := Nat.le_pred_of_lt hq
    have hprod : (old.toNat / 2 ^ 128) * 2 ^ 128 ≤ (2 ^ 128 - 1) * 2 ^ 128 :=
      Nat.mul_le_mul_right _ hqle
    norm_num [UInt256.size, Nat.pow_add] at hprod ⊢
    omega
  rw [Nat.mod_eq_of_lt hlorLt]
  rw [hhigh]
  exact nat_lor_shift_add low.toNat (old.toNat / 2 ^ 128) 128 hlow

private theorem burnPositionUpdateHigh128_insert_toNat (low old : UInt256)
    (hlow : low.toNat < 2 ^ 128) :
    (UInt256.lor (UInt256.mul low (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩))
        (UInt256.land old uint128Mask)).toNat =
      (UInt256.land old uint128Mask).toNat + low.toNat * 2 ^ 128 := by
  rw [u256_lor_toNat, u256_mul_toNat]
  have hshift : (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩).toNat = 2 ^ 128 := by
    native_decide
  rw [hshift]
  have hprodLt : low.toNat * 2 ^ 128 < UInt256.size := by
    have hlowle : low.toNat ≤ 2 ^ 128 - 1 := Nat.le_pred_of_lt hlow
    have hprod : low.toNat * 2 ^ 128 ≤ (2 ^ 128 - 1) * 2 ^ 128 :=
      Nat.mul_le_mul_right _ hlowle
    norm_num [UInt256.size, Nat.pow_add] at hprod ⊢
    omega
  rw [Nat.mod_eq_of_lt hprodLt]
  have hlowOldLt : (UInt256.land old uint128Mask).toNat < 2 ^ 128 := by
    simpa using uint128Mask_bound old
  have hlorLt :
      Nat.lor (low.toNat * 2 ^ 128) (UInt256.land old uint128Mask).toNat <
        UInt256.size := by
    rw [nat_lor_comm]
    rw [nat_lor_shift_add (UInt256.land old uint128Mask).toNat low.toNat 128 hlowOldLt]
    have hlowOldLe : (UInt256.land old uint128Mask).toNat ≤ 2 ^ 128 - 1 :=
      Nat.le_pred_of_lt hlowOldLt
    have hlowLe : low.toNat ≤ 2 ^ 128 - 1 := Nat.le_pred_of_lt hlow
    have hprod : low.toNat * 2 ^ 128 ≤ (2 ^ 128 - 1) * 2 ^ 128 :=
      Nat.mul_le_mul_right _ hlowLe
    have hmax : (2 ^ 128 - 1) + (2 ^ 128 - 1) * 2 ^ 128 < UInt256.size := by
      norm_num [UInt256.size, Nat.pow_add]
    omega
  rw [Nat.mod_eq_of_lt hlorLt]
  rw [nat_lor_comm]
  rw [nat_lor_shift_add (UInt256.land old uint128Mask).toNat low.toNat 128 hlowOldLt]

theorem burnPositionUpdateStorageLocStore_tokensOwed0
    (evm : EVM.State) (slot : UInt256) (n : Int) :
    storageLocStore evm
        (loc slot ⟨0, by decide⟩ ⟨16, by decide⟩ (by decide) (.int uint128Int))
        (.int n) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.lor
          (UInt256.land (EVM.wordOfInt n) uint128Mask)
          (UInt256.land (UInt256.lnot uint128Mask)
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)))) := by
  unfold storageLocStore storageLocWriteWord loc
  simp only [valueToWord, bind, Option.bind]
  congr 2
  apply u256_inj
  let old := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot
  let low := UInt256.land (EVM.wordOfInt n) uint128Mask
  show fromBytes'
      (List.take 0 ↑(EVM.Word.toBytesLEWithSizeProof old) ++
        List.take 16 ↑(EVM.Word.toBytesLEWithSizeProof (EVM.wordOfInt n)) ++
          List.drop (0 + 16) ↑(EVM.Word.toBytesLEWithSizeProof old)) =
    (UInt256.lor low (UInt256.land (UInt256.lnot uint128Mask) old)).toNat
  rw [List.take_zero, List.nil_append]
  rw [fromBytes'_append, fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
  rw [show 256 ^ (16 : Nat) = 2 ^ 128 by norm_num [Nat.pow_add]]
  have hlen16 :
      (List.take 16 (EVM.Word.toBytesLEWithSizeProof (EVM.wordOfInt n)).1).length = 16 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof (EVM.wordOfInt n)).2]
    norm_num
  rw [hlen16]
  rw [show 2 ^ (8 * 16) = 2 ^ 128 by norm_num]
  rw [burnPositionUpdateLow128_insert_toNat low old]
  · dsimp [low]
    rw [u256_land_toNat, uint128Mask_toNat, nat_land_mask_eq_mod]
    rw [Nat.mod_eq_of_lt
      (lt_trans (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 128)) (by norm_num [UInt256.size]))]
    ring_nf
  · dsimp [low]
    simpa using uint128Mask_bound (EVM.wordOfInt n)

theorem burnPositionUpdateStorageLocStore_tokensOwed1
    (evm : EVM.State) (slot : UInt256) (n : Int) :
    storageLocStore evm
        (loc slot ⟨16, by decide⟩ ⟨16, by decide⟩ (by decide) (.int uint128Int))
        (.int n) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.lor
          (UInt256.mul (UInt256.land (EVM.wordOfInt n) uint128Mask)
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩))
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            uint128Mask))) := by
  unfold storageLocStore storageLocWriteWord loc
  simp only [valueToWord, bind, Option.bind]
  congr 2
  apply u256_inj
  let old := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot
  let low := UInt256.land (EVM.wordOfInt n) uint128Mask
  show fromBytes'
      (List.take 16 ↑(EVM.Word.toBytesLEWithSizeProof old) ++
        List.take 16 ↑(EVM.Word.toBytesLEWithSizeProof (EVM.wordOfInt n)) ++
          List.drop (16 + 16) ↑(EVM.Word.toBytesLEWithSizeProof old)) =
    (UInt256.lor (UInt256.mul low (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩))
      (UInt256.land old uint128Mask)).toNat
  rw [fromBytes'_append, fromBytes'_append]
  rw [fromBytes'_take_wordLE, fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
  rw [show 256 ^ (16 : Nat) = 2 ^ 128 by norm_num [Nat.pow_add]]
  rw [show 256 ^ (32 : Nat) = 2 ^ 256 by norm_num [Nat.pow_add]]
  have hlen16old :
      (List.take 16 (EVM.Word.toBytesLEWithSizeProof old).1).length = 16 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof old).2]
    norm_num
  have hlen16val :
      (List.take 16 (EVM.Word.toBytesLEWithSizeProof (EVM.wordOfInt n)).1).length = 16 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof (EVM.wordOfInt n)).2]
    norm_num
  have hlen32 :
      (List.take 16 (EVM.Word.toBytesLEWithSizeProof old).1 ++
          List.take 16 (EVM.Word.toBytesLEWithSizeProof (EVM.wordOfInt n)).1).length = 32 := by
    rw [List.length_append, hlen16old, hlen16val]
  rw [hlen16old, hlen32]
  rw [show old.toNat / 2 ^ 256 = 0 by exact Nat.div_eq_of_lt old.val.isLt]
  rw [show 2 ^ (8 * 16) = 2 ^ 128 by norm_num]
  rw [burnPositionUpdateHigh128_insert_toNat low old]
  rw [show (UInt256.land old uint128Mask).toNat = old.toNat % 2 ^ 128 by
    rw [u256_land_toNat, uint128Mask_toNat, nat_land_mask_eq_mod]
    exact Nat.mod_eq_of_lt
      (lt_trans (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 128)) (by norm_num [UInt256.size]))]
  · dsimp [low]
    rw [u256_land_toNat, uint128Mask_toNat, nat_land_mask_eq_mod]
    rw [Nat.mod_eq_of_lt
      (lt_trans (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 128)) (by norm_num [UInt256.size]))]
    ring_nf
  · dsimp [low]
    simpa using uint128Mask_bound (EVM.wordOfInt n)

theorem burnPositionUpdateValue_evalPositionTokensOwed0AfterTokensOwed1
    {v : PoolImmutables} {evm σ I}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256) :
    evalExpr? (config v)
      (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
        (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
      evm (.field (.var "position") "tokensOwed0") =
        .ok (.int (Int.ofNat (UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (positionsBase (burnPositionKeyKey I) + ⟨3⟩))
          uint128Mask).toNat)) := by
  simp only [evalExpr?, EvalResult.bind, bind]
  rw [burnPositionUpdateValueAfterTokensOwed1_position (v := v) (σ := σ)]
  simp only [EvalResult.ofOption]
  rw [show storageTypeStep? positionInfoStructTy (.field "tokensOwed0") = some uint128St by
    simp [storageTypeStep?, positionInfoStructTy, uint128St]]
  change
    readStorage? (config v) evm (burnPositionUpdateEvaledRef I "tokensOwed0") uint128St =
      .ok (.int (Int.ofNat (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (positionsBase (burnPositionKeyKey I) + ⟨3⟩))
        uint128Mask).toNat))
  rw [show uint128St = .elem (.int uint128Int) by rfl]
  rw [readStorage?_elem
    (er := burnPositionUpdateEvaledRef I "tokensOwed0")
    (t := .int uint128Int)
    (loc := loc (positionsBase (burnPositionKeyKey I) + ⟨3⟩) ⟨0, by decide⟩
      ⟨16, by decide⟩ (by decide) (.int uint128Int))]
  · exact congrArg EvalResult.ok
      (burnPositionUpdateStorageLocLoad_tokensOwed0 evm (positionsBase (burnPositionKeyKey I)))
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      burnPositionUpdateEvaledRef, burnPositionKeyKey, loc]

theorem burnPositionUpdateValue_evalPositionTokensOwed1AfterTokensOwed1
    {v : PoolImmutables} {evm σ I}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256) :
    evalExpr? (config v)
      (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
        (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
      evm (.field (.var "position") "tokensOwed1") =
        .ok (.int (Int.ofNat (UInt256.land
          (UInt256.div
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (positionsBase (burnPositionKeyKey I) + ⟨3⟩))
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)) uint128Mask).toNat)) := by
  simp only [evalExpr?, EvalResult.bind, bind]
  rw [burnPositionUpdateValueAfterTokensOwed1_position (v := v) (σ := σ)]
  simp only [EvalResult.ofOption]
  rw [show storageTypeStep? positionInfoStructTy (.field "tokensOwed1") = some uint128St by
    simp [storageTypeStep?, positionInfoStructTy, uint128St]]
  change
    readStorage? (config v) evm (burnPositionUpdateEvaledRef I "tokensOwed1") uint128St =
      .ok (.int (Int.ofNat (UInt256.land
        (UInt256.div
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (positionsBase (burnPositionKeyKey I) + ⟨3⟩))
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)) uint128Mask).toNat))
  rw [show uint128St = .elem (.int uint128Int) by rfl]
  rw [readStorage?_elem
    (er := burnPositionUpdateEvaledRef I "tokensOwed1")
    (t := .int uint128Int)
    (loc := loc (positionsBase (burnPositionKeyKey I) + ⟨3⟩) ⟨16, by decide⟩
      ⟨16, by decide⟩ (by decide) (.int uint128Int))]
  · exact congrArg EvalResult.ok
      (burnPositionUpdateStorageLocLoad_tokensOwed1 evm (positionsBase (burnPositionKeyKey I)))
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      burnPositionUpdateEvaledRef, burnPositionKeyKey, loc]

theorem burnPositionUpdateValue_evalTokensOwed0AddAfterTokensOwed1
    {v : PoolImmutables} {evm σ I}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256) :
    evalExpr? (config v)
      (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
        (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
      evm (addE (.field (.var "position") "tokensOwed0") (.var "tokensOwed0")) =
        .ok (.int (burnPositionUpdateSourceStoredTokensOwed0Int evm I +
          burnPositionUpdateSourceTokensOwed0Int σ I
            (Int.ofNat feeGrowthInside0X128.toNat))) := by
  let frame := burnPositionUpdateValueAfterTokensOwed1Frame v σ I
    (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat)
  have hfield :=
    burnPositionUpdateValue_evalPositionTokensOwed0AfterTokensOwed1
      (v := v) (evm := evm) (σ := σ) (I := I)
      feeGrowthInside0X128 feeGrowthInside1X128
  have hvar :
      evalExpr? (config v) frame evm (.var "tokensOwed0") =
        .ok (.int (burnPositionUpdateSourceTokensOwed0Int σ I
          (Int.ofNat feeGrowthInside0X128.toNat))) := by
    simp only [frame, evalExpr?, EvalResult.ofOption]
    rw [burnPositionUpdateValueAfterTokensOwed1_tokensOwed0 (v := v) (σ := σ) (I := I)]
  unfold addE
  rw [evalExpr?]
  change
    EvalResult.bind (evalExpr? (config v) frame evm
      (.field (.var "position") "tokensOwed0")) (fun lhsValue =>
        EvalResult.bind (evalExpr? (config v) frame evm (.var "tokensOwed0"))
          (fun rhsValue => evalBinaryOp? .add lhsValue rhsValue)) =
      .ok (.int (burnPositionUpdateSourceStoredTokensOwed0Int evm I +
        burnPositionUpdateSourceTokensOwed0Int σ I (Int.ofNat feeGrowthInside0X128.toNat)))
  rw [hfield, hvar]
  simp only [EvalResult.bind, evalBinaryOp?,
    burnPositionUpdateSourceStoredTokensOwed0Int]
  all_goals decide

theorem burnPositionUpdateValue_evalTokensOwed1AddAfterTokensOwed1
    {v : PoolImmutables} {evm σ I}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256) :
    evalExpr? (config v)
      (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
        (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
      evm (addE (.field (.var "position") "tokensOwed1") (.var "tokensOwed1")) =
        .ok (.int (burnPositionUpdateSourceStoredTokensOwed1Int evm I +
          burnPositionUpdateSourceTokensOwed1Int σ I
            (Int.ofNat feeGrowthInside1X128.toNat))) := by
  let frame := burnPositionUpdateValueAfterTokensOwed1Frame v σ I
    (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat)
  have hfield :=
    burnPositionUpdateValue_evalPositionTokensOwed1AfterTokensOwed1
      (v := v) (evm := evm) (σ := σ) (I := I)
      feeGrowthInside0X128 feeGrowthInside1X128
  have hvar :
      evalExpr? (config v) frame evm (.var "tokensOwed1") =
        .ok (.int (burnPositionUpdateSourceTokensOwed1Int σ I
          (Int.ofNat feeGrowthInside1X128.toNat))) := by
    simp only [frame, evalExpr?, EvalResult.ofOption]
    rw [burnPositionUpdateValueAfterTokensOwed1_tokensOwed1 (v := v) (σ := σ) (I := I)]
  unfold addE
  rw [evalExpr?]
  change
    EvalResult.bind (evalExpr? (config v) frame evm
      (.field (.var "position") "tokensOwed1")) (fun lhsValue =>
        EvalResult.bind (evalExpr? (config v) frame evm (.var "tokensOwed1"))
          (fun rhsValue => evalBinaryOp? .add lhsValue rhsValue)) =
      .ok (.int (burnPositionUpdateSourceStoredTokensOwed1Int evm I +
        burnPositionUpdateSourceTokensOwed1Int σ I (Int.ofNat feeGrowthInside1X128.toNat)))
  rw [hfield, hvar]
  simp only [EvalResult.bind, evalBinaryOp?,
    burnPositionUpdateSourceStoredTokensOwed1Int]
  all_goals decide

theorem burnPositionUpdateValue_assignTokensOwed0AfterTokensOwed1
    {v : PoolImmutables} {evm σ I}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256) :
    assignStorageRef? (config v)
      (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
        (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
      evm .storage { base := "position", steps := [.field "tokensOwed0"] }
      (.int (burnPositionUpdateSourceTokensOwed0WriteInt evm σ I feeGrowthInside0X128)) =
        .ok ((burnPositionUpdateValueAfterTokensOwed1Frame v σ I
          (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat)),
          Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (burnPositionUpdateSourceTokensOwedSlot I)
            (burnPositionUpdateSourceTokensOwed0StoreWord evm σ I feeGrowthInside0X128)) := by
  rw [assignStorageRef?]
  rw [burnPositionUpdateValue_resolveTokensOwed0AfterTokensOwed1]
  simp only [EvalResult.bind, bind, EvalResult.ofOption, pure]
  rw [show (config v).storage.layout (burnPositionUpdateEvaledRef I "tokensOwed0") =
      fun _ => some (loc (burnPositionUpdateSourceTokensOwedSlot I) ⟨0, by decide⟩
        ⟨16, by decide⟩ (by decide) (.int uint128Int)) by
    funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      burnPositionUpdateEvaledRef, burnPositionKeyKey, burnPositionUpdateSourceTokensOwedSlot,
      loc]]
  simp only [EvalResult.bind, bind, EvalResult.ofOption, pure]
  rw [burnPositionUpdateStorageLocStore_tokensOwed0 evm
    (burnPositionUpdateSourceTokensOwedSlot I)
    (burnPositionUpdateSourceTokensOwed0WriteInt evm σ I feeGrowthInside0X128)]

theorem burnPositionUpdateValue_assignTokensOwed1AfterTokensOwed1
    {v : PoolImmutables} {evm σ I}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256) :
    assignStorageRef? (config v)
      (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
        (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
      evm .storage { base := "position", steps := [.field "tokensOwed1"] }
      (.int (burnPositionUpdateSourceTokensOwed1WriteInt evm σ I feeGrowthInside1X128)) =
        .ok ((burnPositionUpdateValueAfterTokensOwed1Frame v σ I
          (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat)),
          Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (burnPositionUpdateSourceTokensOwedSlot I)
            (burnPositionUpdateSourceTokensOwed1StoreWord evm σ I feeGrowthInside1X128)) := by
  rw [assignStorageRef?]
  rw [burnPositionUpdateValue_resolveTokensOwed1AfterTokensOwed1]
  simp only [EvalResult.bind, bind, EvalResult.ofOption, pure]
  rw [show (config v).storage.layout (burnPositionUpdateEvaledRef I "tokensOwed1") =
      fun _ => some (loc (burnPositionUpdateSourceTokensOwedSlot I) ⟨16, by decide⟩
        ⟨16, by decide⟩ (by decide) (.int uint128Int)) by
    funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      burnPositionUpdateEvaledRef, burnPositionKeyKey, burnPositionUpdateSourceTokensOwedSlot,
      loc]]
  simp only [EvalResult.bind, bind, EvalResult.ofOption, pure]
  rw [burnPositionUpdateStorageLocStore_tokensOwed1 evm
    (burnPositionUpdateSourceTokensOwedSlot I)
    (burnPositionUpdateSourceTokensOwed1WriteInt evm σ I feeGrowthInside1X128)]

theorem burnPositionUpdateValue_assignTokensOwed0AfterTokensOwed1_some
    {v : PoolImmutables} {evm σ I}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256) :
    ∃ evm',
      assignStorageRef? (config v)
        (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
          (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
        evm .storage { base := "position", steps := [.field "tokensOwed0"] }
        (.int (burnPositionUpdateSourceStoredTokensOwed0Int evm I +
          burnPositionUpdateSourceTokensOwed0Int σ I
            (Int.ofNat feeGrowthInside0X128.toNat))) =
          .ok ((burnPositionUpdateValueAfterTokensOwed1Frame v σ I
            (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat)),
            evm') := by
  refine ⟨Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (burnPositionUpdateSourceTokensOwedSlot I)
    (burnPositionUpdateSourceTokensOwed0StoreWord evm σ I feeGrowthInside0X128), ?_⟩
  simpa [burnPositionUpdateSourceTokensOwed0WriteInt] using
    burnPositionUpdateValue_assignTokensOwed0AfterTokensOwed1
      (v := v) (evm := evm) (σ := σ) (I := I)
      feeGrowthInside0X128 feeGrowthInside1X128

theorem burnPositionUpdateValue_assignTokensOwed1AfterTokensOwed1_some
    {v : PoolImmutables} {evm σ I}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256) :
    ∃ evm',
      assignStorageRef? (config v)
        (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
          (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
        evm .storage { base := "position", steps := [.field "tokensOwed1"] }
        (.int (burnPositionUpdateSourceStoredTokensOwed1Int evm I +
          burnPositionUpdateSourceTokensOwed1Int σ I
            (Int.ofNat feeGrowthInside1X128.toNat))) =
          .ok ((burnPositionUpdateValueAfterTokensOwed1Frame v σ I
            (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat)),
            evm') := by
  refine ⟨Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (burnPositionUpdateSourceTokensOwedSlot I)
    (burnPositionUpdateSourceTokensOwed1StoreWord evm σ I feeGrowthInside1X128), ?_⟩
  simpa [burnPositionUpdateSourceTokensOwed1WriteInt] using
    burnPositionUpdateValue_assignTokensOwed1AfterTokensOwed1
      (v := v) (evm := evm) (σ := σ) (I := I)
      feeGrowthInside0X128 feeGrowthInside1X128

theorem uniswapV3PoolPositionUpdateSourceZeroDeltaLiquidityNonzeroTokensOwedTrueTailValue
    {v : PoolImmutables} {evm σ I}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256)
    (hcond :
      evalExpr? (config v)
        (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
          (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
        evm
        (orE (gtE (.var "tokensOwed0") (.intLit 0))
          (gtE (.var "tokensOwed1") (.intLit 0))) = .ok (.bool true)) :
    ExecBlock (config v)
      (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
        (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
      evm
      [ Stmt.ite (orE (gtE (.var "tokensOwed0") (.intLit 0))
          (gtE (.var "tokensOwed1") (.intLit 0)))
        [ .assign .storage { base := "position", steps := [.field "tokensOwed0"] }
            (addE (.field (.var "position") "tokensOwed0") (.var "tokensOwed0")),
          .assign .storage { base := "position", steps := [.field "tokensOwed1"] }
            (addE (.field (.var "position") "tokensOwed1") (.var "tokensOwed1")) ]
        [] ]
      (ExecResult.ok
        (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
          (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
        (burnPositionUpdateSourceAfterTokensOwedState evm σ I
          feeGrowthInside0X128 feeGrowthInside1X128)) := by
  let frame := burnPositionUpdateValueAfterTokensOwed1Frame v σ I
    (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat)
  let evm1 := burnPositionUpdateSourceAfterTokensOwed0State evm σ I feeGrowthInside0X128
  let evm2 := burnPositionUpdateSourceAfterTokensOwedState evm σ I
    feeGrowthInside0X128 feeGrowthInside1X128
  have hstep0 :
      ExecStmt (config v) frame evm
        (.assign .storage { base := "position", steps := [.field "tokensOwed0"] }
          (addE (.field (.var "position") "tokensOwed0") (.var "tokensOwed0")))
        (.ok frame evm1) := by
    exact ExecStmt.assign
      (by
        simpa [frame] using
          burnPositionUpdateValue_evalTokensOwed0AddAfterTokensOwed1
            (v := v) (evm := evm) (σ := σ) (I := I)
            feeGrowthInside0X128 feeGrowthInside1X128)
      (by
        simpa [frame, evm1, burnPositionUpdateSourceAfterTokensOwed0State,
          burnPositionUpdateSourceTokensOwed0WriteInt] using
          burnPositionUpdateValue_assignTokensOwed0AfterTokensOwed1
            (v := v) (evm := evm) (σ := σ) (I := I)
            feeGrowthInside0X128 feeGrowthInside1X128)
  have hstep1 :
      ExecStmt (config v) frame evm1
        (.assign .storage { base := "position", steps := [.field "tokensOwed1"] }
          (addE (.field (.var "position") "tokensOwed1") (.var "tokensOwed1")))
        (.ok frame evm2) := by
    exact ExecStmt.assign
      (by
        simpa [frame] using
          burnPositionUpdateValue_evalTokensOwed1AddAfterTokensOwed1
            (v := v) (evm := evm1) (σ := σ) (I := I)
            feeGrowthInside0X128 feeGrowthInside1X128)
      (by
        simpa [frame, evm2, burnPositionUpdateSourceAfterTokensOwedState,
          burnPositionUpdateSourceTokensOwed1WriteInt] using
          burnPositionUpdateValue_assignTokensOwed1AfterTokensOwed1
            (v := v) (evm := evm1) (σ := σ) (I := I)
            feeGrowthInside0X128 feeGrowthInside1X128)
  have hthen :
      ExecBlock (config v) frame evm
        [ .assign .storage { base := "position", steps := [.field "tokensOwed0"] }
            (addE (.field (.var "position") "tokensOwed0") (.var "tokensOwed0")),
          .assign .storage { base := "position", steps := [.field "tokensOwed1"] }
            (addE (.field (.var "position") "tokensOwed1") (.var "tokensOwed1")) ]
        (.ok frame evm2) := by
    exact ExecBlock.consNormal hstep0 (ExecBlock.consNormal hstep1 ExecBlock.nil)
  simpa [frame, evm2] using
    ExecBlock.consNormal (ExecStmt.iteTrue (by simpa [frame] using hcond) hthen) ExecBlock.nil

set_option maxHeartbeats 800000 in
theorem uniswapV3PoolPositionUpdateSourceZeroDeltaLiquidityNonzeroTokensOwedTrueBlockValue
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256)
    (hzero : burnAmountCleanWord I = ⟨0⟩)
    (hliq :
      burnPositionUpdateSlot0Packed
          (solcSlotWord σ I (positionsBase (burnPositionKeyKey I))) ≠ ⟨0⟩)
    (hcond :
      evalExpr? (config v)
        (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
          (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner
            (positionsBase (burnPositionKeyKey I) + ⟨1⟩) feeGrowthInside0X128)
          I.codeOwner (positionsBase (burnPositionKeyKey I) + ⟨2⟩)
          feeGrowthInside1X128)
        (orE (gtE (.var "tokensOwed0") (.intLit 0))
          (gtE (.var "tokensOwed1") (.intLit 0))) = .ok (.bool true)) :
    ExecBlock (config v)
      (burnPositionUpdateValueFrame v I (.int (Int.ofNat feeGrowthInside0X128.toNat))
        (.int (Int.ofNat feeGrowthInside1X128.toNat)))
      (initState cA gh bl σ σ₀ g A I)
      ([ .letStorage "position" (positionsRef (.var "positionKey")),
        Stmt.ite (eqE (.var "liquidityDelta") (.intLit 0))
          [ .require (gtE (.field (.var "position") "liquidity") (.intLit 0)),
            .letDecl "liquidityNext" (some uint128)
              (.field (.var "position") "liquidity") ]
          [ .internalCall "liquidityAddDelta"
              [.field (.var "position") "liquidity", .var "liquidityDelta"]
              "liquidityNext" ],
        .letDecl "tokensOwed0" (some uint128)
          (uint128Wrap
            (divE
              (mulE
                (wordSub (.var "feeGrowthInside0X128")
                  (.field (.var "position") "feeGrowthInside0LastX128"))
                (.field (.var "position") "liquidity"))
              fixedPoint128Q128)),
        .letDecl "tokensOwed1" (some uint128)
          (uint128Wrap
            (divE
              (mulE
                (wordSub (.var "feeGrowthInside1X128")
                  (.field (.var "position") "feeGrowthInside1LastX128"))
                (.field (.var "position") "liquidity"))
              fixedPoint128Q128)),
        Stmt.ite (neE (.var "liquidityDelta") (.intLit 0))
          [ .assign .storage { base := "position", steps := [.field "liquidity"] }
              (.var "liquidityNext") ]
          [],
        .assign .storage { base := "position", steps := [.field "feeGrowthInside0LastX128"] }
          (.var "feeGrowthInside0X128"),
        .assign .storage { base := "position", steps := [.field "feeGrowthInside1LastX128"] }
          (.var "feeGrowthInside1X128") ] ++
      [ Stmt.ite (orE (gtE (.var "tokensOwed0") (.intLit 0))
            (gtE (.var "tokensOwed1") (.intLit 0)))
          [ .assign .storage { base := "position", steps := [.field "tokensOwed0"] }
              (addE (.field (.var "position") "tokensOwed0") (.var "tokensOwed0")),
            .assign .storage { base := "position", steps := [.field "tokensOwed1"] }
              (addE (.field (.var "position") "tokensOwed1") (.var "tokensOwed1")) ]
          [] ])
      (ExecResult.ok
        (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
          (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
        (burnPositionUpdateSourceAfterTokensOwedState
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner
              (positionsBase (burnPositionKeyKey I) + ⟨1⟩) feeGrowthInside0X128)
            I.codeOwner (positionsBase (burnPositionKeyKey I) + ⟨2⟩)
            feeGrowthInside1X128)
          σ I feeGrowthInside0X128 feeGrowthInside1X128)) := by
  let evmFee :=
    Solm.EVM.storageStore
      (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner
        (positionsBase (burnPositionKeyKey I) + ⟨1⟩) feeGrowthInside0X128)
      I.codeOwner (positionsBase (burnPositionKeyKey I) + ⟨2⟩) feeGrowthInside1X128
  have hprefix :=
    uniswapV3PoolPositionUpdateSourceZeroDeltaLiquidityNonzeroFeeGrowthLastPrefixValue
      (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) feeGrowthInside0X128 feeGrowthInside1X128 hzero hliq
  have hcondFee :
      evalExpr? (config v)
        (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
          (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
        evmFee
        (orE (gtE (.var "tokensOwed0") (.intLit 0))
          (gtE (.var "tokensOwed1") (.intLit 0))) = .ok (.bool true) := by
    simpa [evmFee] using hcond
  have htail :=
    uniswapV3PoolPositionUpdateSourceZeroDeltaLiquidityNonzeroTokensOwedTrueTailValue
      (v := v) (evm := evmFee) (σ := σ) (I := I)
      feeGrowthInside0X128 feeGrowthInside1X128 hcondFee
  simpa [evmFee] using execBlock_append hprefix htail

theorem burnPositionUpdateSourceAfterTokensOwedState_stateEquiv_of_final_word
    {evm σ I} {feeGrowthInside0X128 feeGrowthInside1X128 finalWord : UInt256}
    (hword :
      burnPositionUpdateSourceTokensOwed1StoreWord
          (burnPositionUpdateSourceAfterTokensOwed0State evm σ I feeGrowthInside0X128)
          σ I feeGrowthInside1X128 = finalWord) :
    EVMStateEquiv
      (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (burnPositionUpdateSourceTokensOwedSlot I) finalWord)
      (burnPositionUpdateSourceAfterTokensOwedState evm σ I
        feeGrowthInside0X128 feeGrowthInside1X128) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [burnPositionUpdateSourceAfterTokensOwedState,
      burnPositionUpdateSourceAfterTokensOwed0State, storageStore_executionEnv]
  · simp [burnPositionUpdateSourceAfterTokensOwedState,
      burnPositionUpdateSourceAfterTokensOwed0State, storageStore_createdAccounts]
  · rw [← hword]
    simp [burnPositionUpdateSourceAfterTokensOwedState,
      burnPositionUpdateSourceAfterTokensOwed0State, storageStore_accountMap,
      storageStore_executionEnv]
    exact accountMapEquiv_sstoreAccountMap_self_update evm.accountMap
      evm.executionEnv.codeOwner (burnPositionUpdateSourceTokensOwedSlot I)
      (burnPositionUpdateSourceTokensOwed0StoreWord evm σ I feeGrowthInside0X128)
      (burnPositionUpdateSourceTokensOwed1StoreWord
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (burnPositionUpdateSourceTokensOwedSlot I)
          (burnPositionUpdateSourceTokensOwed0StoreWord evm σ I feeGrowthInside0X128))
        σ I feeGrowthInside1X128)

theorem burnPositionUpdateTokensOwedState_stateEquiv_of_final_word
    {evmEvm evmSolm : EVM.State} {σ I}
    {feeGrowthInside0X128 feeGrowthInside1X128 finalWord : UInt256}
    (hstate : EVMStateEquiv evmEvm evmSolm)
    (hword :
      burnPositionUpdateSourceTokensOwed1StoreWord
          (burnPositionUpdateSourceAfterTokensOwed0State evmSolm σ I feeGrowthInside0X128)
          σ I feeGrowthInside1X128 = finalWord) :
    EVMStateEquiv
      (Solm.EVM.storageStore evmEvm evmEvm.executionEnv.codeOwner
        (burnPositionUpdateSourceTokensOwedSlot I) finalWord)
      (burnPositionUpdateSourceAfterTokensOwedState evmSolm σ I
        feeGrowthInside0X128 feeGrowthInside1X128) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [burnPositionUpdateSourceAfterTokensOwedState,
      burnPositionUpdateSourceAfterTokensOwed0State, storageStore_executionEnv]
    exact hstate.executionEnv
  · simp [burnPositionUpdateSourceAfterTokensOwedState,
      burnPositionUpdateSourceAfterTokensOwed0State, storageStore_createdAccounts]
    exact hstate.createdAccounts
  · have hsingle : accountMapEquiv
        (Solm.EVM.storageStore evmEvm evmEvm.executionEnv.codeOwner
          (burnPositionUpdateSourceTokensOwedSlot I) finalWord).accountMap
        (Solm.EVM.storageStore evmSolm evmSolm.executionEnv.codeOwner
          (burnPositionUpdateSourceTokensOwedSlot I) finalWord).accountMap := by
      rw [hstate.executionEnv]
      exact storageStore_accountMapEquiv hstate.accountMap evmSolm.executionEnv.codeOwner
        (burnPositionUpdateSourceTokensOwedSlot I) finalWord
    have hsource :=
      burnPositionUpdateSourceAfterTokensOwedState_stateEquiv_of_final_word
        (evm := evmSolm) (σ := σ) (I := I)
        (feeGrowthInside0X128 := feeGrowthInside0X128)
        (feeGrowthInside1X128 := feeGrowthInside1X128)
        (finalWord := finalWord) hword
    exact accountMapEquiv.trans hsingle hsource.accountMap

theorem uniswapV3PoolPositionUpdateSourceZeroDeltaLiquidityNonzeroTokensOwedZeroTailValue
    {v : PoolImmutables} {evm σ I}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256)
    (htokens0 :
      burnPositionUpdateSourceTokensOwed0Int σ I
          (Int.ofNat feeGrowthInside0X128.toNat) = 0)
    (htokens1 :
      burnPositionUpdateSourceTokensOwed1Int σ I
          (Int.ofNat feeGrowthInside1X128.toNat) = 0) :
    ExecBlock (config v)
      (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
        (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
      evm
      [ Stmt.ite (orE (gtE (.var "tokensOwed0") (.intLit 0))
          (gtE (.var "tokensOwed1") (.intLit 0)))
        [ .assign .storage { base := "position", steps := [.field "tokensOwed0"] }
            (addE (.field (.var "position") "tokensOwed0") (.var "tokensOwed0")),
          .assign .storage { base := "position", steps := [.field "tokensOwed1"] }
            (addE (.field (.var "position") "tokensOwed1") (.var "tokensOwed1")) ]
        [] ]
      (ExecResult.ok
        (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
          (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
        evm) := by
  refine ExecBlock.consNormal (ExecStmt.iteFalse ?_ ?_) ExecBlock.nil
  · exact burnPositionUpdateValue_evalTokensOwedGtFalseAfterTokensOwed1
      (v := v) (evm := evm) (σ := σ) (I := I)
      feeGrowthInside0X128 feeGrowthInside1X128 htokens0 htokens1
  · exact ExecBlock.nil

theorem uniswapV3PoolPositionUpdateSourceZeroDeltaLiquidityNonzeroTokensOwedZeroBlockValue
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256)
    (hzero : burnAmountCleanWord I = ⟨0⟩)
    (hliq :
      burnPositionUpdateSlot0Packed
          (solcSlotWord σ I (positionsBase (burnPositionKeyKey I))) ≠ ⟨0⟩)
    (htokens0 :
      burnPositionUpdateSourceTokensOwed0Int σ I
          (Int.ofNat feeGrowthInside0X128.toNat) = 0)
    (htokens1 :
      burnPositionUpdateSourceTokensOwed1Int σ I
          (Int.ofNat feeGrowthInside1X128.toNat) = 0) :
    ExecBlock (config v)
      (burnPositionUpdateValueFrame v I (.int (Int.ofNat feeGrowthInside0X128.toNat))
        (.int (Int.ofNat feeGrowthInside1X128.toNat)))
      (initState cA gh bl σ σ₀ g A I)
      [ .letStorage "position" (positionsRef (.var "positionKey")),
        Stmt.ite (eqE (.var "liquidityDelta") (.intLit 0))
          [ .require (gtE (.field (.var "position") "liquidity") (.intLit 0)),
            .letDecl "liquidityNext" (some uint128)
              (.field (.var "position") "liquidity") ]
          [ .internalCall "liquidityAddDelta"
              [.field (.var "position") "liquidity", .var "liquidityDelta"]
              "liquidityNext" ],
        .letDecl "tokensOwed0" (some uint128)
          (uint128Wrap
            (divE
              (mulE
                (wordSub (.var "feeGrowthInside0X128")
                  (.field (.var "position") "feeGrowthInside0LastX128"))
                (.field (.var "position") "liquidity"))
              fixedPoint128Q128)),
        .letDecl "tokensOwed1" (some uint128)
          (uint128Wrap
            (divE
              (mulE
                (wordSub (.var "feeGrowthInside1X128")
                  (.field (.var "position") "feeGrowthInside1LastX128"))
                (.field (.var "position") "liquidity"))
              fixedPoint128Q128)),
        Stmt.ite (neE (.var "liquidityDelta") (.intLit 0))
          [ .assign .storage { base := "position", steps := [.field "liquidity"] }
              (.var "liquidityNext") ]
          [],
        .assign .storage { base := "position", steps := [.field "feeGrowthInside0LastX128"] }
          (.var "feeGrowthInside0X128"),
        .assign .storage { base := "position", steps := [.field "feeGrowthInside1LastX128"] }
          (.var "feeGrowthInside1X128"),
        Stmt.ite (orE (gtE (.var "tokensOwed0") (.intLit 0))
            (gtE (.var "tokensOwed1") (.intLit 0)))
          [ .assign .storage { base := "position", steps := [.field "tokensOwed0"] }
              (addE (.field (.var "position") "tokensOwed0") (.var "tokensOwed0")),
            .assign .storage { base := "position", steps := [.field "tokensOwed1"] }
              (addE (.field (.var "position") "tokensOwed1") (.var "tokensOwed1")) ]
          [] ]
      (ExecResult.ok
        (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
          (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner
            (positionsBase (burnPositionKeyKey I) + ⟨1⟩) feeGrowthInside0X128)
          I.codeOwner (positionsBase (burnPositionKeyKey I) + ⟨2⟩)
          feeGrowthInside1X128)) := by
  have hprefix :=
    uniswapV3PoolPositionUpdateSourceZeroDeltaLiquidityNonzeroFeeGrowthLastPrefixValue
      (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) feeGrowthInside0X128 feeGrowthInside1X128 hzero hliq
  have htail :=
    uniswapV3PoolPositionUpdateSourceZeroDeltaLiquidityNonzeroTokensOwedZeroTailValue
      (v := v)
      (evm := Solm.EVM.storageStore
        (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner
          (positionsBase (burnPositionKeyKey I) + ⟨1⟩) feeGrowthInside0X128)
        I.codeOwner (positionsBase (burnPositionKeyKey I) + ⟨2⟩) feeGrowthInside1X128)
      (σ := σ) (I := I) feeGrowthInside0X128 feeGrowthInside1X128 htokens0 htokens1
  simpa using execBlock_append hprefix htail

end Benchmarks.UniswapV3Pool
