import Examples.UniswapV2Pair.MintFeeRoutinesCore

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace UniswapV2Pair

theorem mintFeeSqrtPrefix
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (kLast : UInt256)
    (hfit : mintFeeReserveProductNat reserve0 reserve1 < UInt256.size) :
    ∃ rootK rootKLast,
      ExecBlock config (mintFeeAfterKLastFrame reserve0 reserve1 feeTo true kLast) evm
        [ .internalCall "sqrt" [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))]
            "rootK",
          .internalCall "sqrt" [.var "_kLast"] "rootKLast" ]
        (.ok (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast)
          evm) := by
  obtain ⟨rootK, hrootK⟩ :=
    uniswapSqrtFunctionCallSuccessInt
      (caller := mintFeeAfterKLastFrame reserve0 reserve1 feeTo true kLast)
      (evm := evm) (y := mintFeeReserveProductWord reserve0 reserve1)
      (args := [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))])
      (retVar := "rootK") rfl
      (evalExprs_mintFee_reserveProductArg evm reserve0 reserve1 feeTo true kLast hfit)
  obtain ⟨rootKLast, hrootKLast⟩ :=
    uniswapSqrtFunctionCallSuccessInt
      (caller := mintFeeAfterRootKFrame reserve0 reserve1 feeTo true kLast rootK)
      (evm := evm) (y := kLast) (args := [.var "_kLast"]) (retVar := "rootKLast") rfl
      (evalExprs_mintFee_kLastArg evm reserve0 reserve1 feeTo true kLast rootK)
  have hrootK' :
      ExecStmt config (mintFeeAfterKLastFrame reserve0 reserve1 feeTo true kLast) evm
        (.internalCall "sqrt" [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))]
          "rootK")
        (.ok (mintFeeAfterRootKFrame reserve0 reserve1 feeTo true kLast rootK) evm) := by
    simpa [mintFeeAfterRootKFrame, mintFeeAfterRootKStore, resumeAfterInternalCall] using
      hrootK
  have hrootKLast' :
      ExecStmt config (mintFeeAfterRootKFrame reserve0 reserve1 feeTo true kLast rootK) evm
        (.internalCall "sqrt" [.var "_kLast"] "rootKLast")
        (.ok (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast)
          evm) := by
    simpa [mintFeeAfterRootKLastFrame, mintFeeAfterRootKLastStore, resumeAfterInternalCall]
      using hrootKLast
  exact ⟨rootK, rootKLast,
    ExecBlock.consNormal hrootK' (ExecBlock.consNormal hrootKLast' ExecBlock.nil)⟩

theorem mintFeeSqrtPrefixBounded
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (kLast : UInt256)
    (hfit : mintFeeReserveProductNat reserve0 reserve1 < UInt256.size) :
    ∃ rootK rootKLast,
      ExecBlock config (mintFeeAfterKLastFrame reserve0 reserve1 feeTo true kLast) evm
        [ .internalCall "sqrt" [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))]
            "rootK",
          .internalCall "sqrt" [.var "_kLast"] "rootKLast" ]
        (.ok (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast)
          evm) ∧
      0 ≤ rootK ∧ rootK.toNat < UInt256.size ∧
      0 ≤ rootKLast ∧ rootKLast.toNat < UInt256.size := by
  obtain ⟨rootK, hrootK, hrootKNonneg, hrootKSize⟩ :=
    uniswapSqrtFunctionCallSuccessIntBounded
      (caller := mintFeeAfterKLastFrame reserve0 reserve1 feeTo true kLast)
      (evm := evm) (y := mintFeeReserveProductWord reserve0 reserve1)
      (args := [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))])
      (retVar := "rootK") rfl
      (evalExprs_mintFee_reserveProductArg evm reserve0 reserve1 feeTo true kLast hfit)
  obtain ⟨rootKLast, hrootKLast, hrootKLastNonneg, hrootKLastSize⟩ :=
    uniswapSqrtFunctionCallSuccessIntBounded
      (caller := mintFeeAfterRootKFrame reserve0 reserve1 feeTo true kLast rootK)
      (evm := evm) (y := kLast) (args := [.var "_kLast"]) (retVar := "rootKLast") rfl
      (evalExprs_mintFee_kLastArg evm reserve0 reserve1 feeTo true kLast rootK)
  have hrootK' :
      ExecStmt config (mintFeeAfterKLastFrame reserve0 reserve1 feeTo true kLast) evm
        (.internalCall "sqrt" [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))]
          "rootK")
        (.ok (mintFeeAfterRootKFrame reserve0 reserve1 feeTo true kLast rootK) evm) := by
    simpa [mintFeeAfterRootKFrame, mintFeeAfterRootKStore, resumeAfterInternalCall] using
      hrootK
  have hrootKLast' :
      ExecStmt config (mintFeeAfterRootKFrame reserve0 reserve1 feeTo true kLast rootK) evm
        (.internalCall "sqrt" [.var "_kLast"] "rootKLast")
        (.ok (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast)
          evm) := by
    simpa [mintFeeAfterRootKLastFrame, mintFeeAfterRootKLastStore, resumeAfterInternalCall]
      using hrootKLast
  exact ⟨rootK, rootKLast,
    ExecBlock.consNormal hrootK' (ExecBlock.consNormal hrootKLast' ExecBlock.nil),
    hrootKNonneg, hrootKSize, hrootKLastNonneg, hrootKLastSize⟩

abbrev mintFeeRootComparisonStmt : Stmt :=
  .ite (.binary .gt (.var "rootK") (.var "rootKLast")) mintFeePositiveRootBranchStmts []

theorem uniswapMintFeeAfterRoots_noMint
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (kLast : UInt256) (rootK rootKLast : Int)
    (hroot : ¬ rootK > rootKLast) :
    ExecBlock config
      (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast) evm
      [mintFeeRootComparisonStmt]
      (.ok (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast)
        evm) := by
  exact ExecBlock.consNormal
    (ExecStmt.iteFalse
      (evalExpr_mintFee_rootK_gt_rootKLast_false evm reserve0 reserve1 feeTo true kLast rootK
        rootKLast hroot)
      ExecBlock.nil)
    ExecBlock.nil

theorem uniswapMintFeeAfterRoots_noMintReturn
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (kLast : UInt256) (rootK rootKLast : Int)
    (hroot : ¬ rootK > rootKLast) :
    ExecBlock config
      (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast) evm
      [mintFeeRootComparisonStmt, .return [(.var "feeOn")]]
      (.returned
        (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast)
        evm (some [.bool true])) := by
  have hite :
      ExecStmt config
        (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast) evm
        mintFeeRootComparisonStmt
        (.ok (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast)
          evm) := by
    exact ExecStmt.iteFalse
      (evalExpr_mintFee_rootK_gt_rootKLast_false evm reserve0 reserve1 feeTo true kLast rootK
        rootKLast hroot)
      ExecBlock.nil
  exact ExecBlock.consNormal hite
    (ExecBlock.consReturn
      (ExecStmt.return
        (evalExprs?_singleton
          (evalExpr_mintFee_afterRootKLast_feeOn evm reserve0 reserve1 feeTo true kLast rootK
            rootKLast))))

theorem uniswapMintFeeAfterRoots_positiveNoLiquidity
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (kLast : UInt256) (rootK rootKLast : Int)
    (hroot : rootK > rootKLast) (hrootKNonneg : 0 ≤ rootK)
    (hrootKSize : rootK.toNat < UInt256.size) (hrootKLastNonneg : 0 ≤ rootKLast)
    (hnumFit : mintFeeNumeratorNat evm rootK rootKLast < UInt256.size)
    (hrootFiveFit : mintFeeRootTimesFiveNat rootK < UInt256.size)
    (hdenFit : mintFeeDenominatorNat rootK rootKLast < UInt256.size)
    (hdenom : (mintFeeDenominatorWord rootK rootKLast).toNat ≠ 0)
    (hliq : ¬ mintFeeLiquidityInt evm rootK rootKLast > 0) :
    ExecBlock config
      (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast) evm
      [mintFeeRootComparisonStmt]
      (.ok (mintFeeAfterLiquidityFrame evm reserve0 reserve1 feeTo true kLast rootK rootKLast)
        evm) := by
  have hite :
      ExecStmt config
        (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast) evm
        mintFeeRootComparisonStmt
        (.ok (mintFeeAfterLiquidityFrame evm reserve0 reserve1 feeTo true kLast rootK rootKLast)
          evm) := by
    exact ExecStmt.iteTrue
      (evalExpr_mintFee_rootK_gt_rootKLast_true evm reserve0 reserve1 feeTo true kLast rootK
        rootKLast hroot)
      (uniswapMintFeePositiveRootBranch_noLiquidity evm reserve0 reserve1 feeTo kLast rootK
        rootKLast hroot hrootKNonneg hrootKSize hrootKLastNonneg hnumFit hrootFiveFit
        hdenFit hdenom hliq)
  exact ExecBlock.consNormal hite ExecBlock.nil

theorem uniswapMintFeeAfterRoots_positiveNoLiquidityReturn
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (kLast : UInt256) (rootK rootKLast : Int)
    (hroot : rootK > rootKLast) (hrootKNonneg : 0 ≤ rootK)
    (hrootKSize : rootK.toNat < UInt256.size) (hrootKLastNonneg : 0 ≤ rootKLast)
    (hnumFit : mintFeeNumeratorNat evm rootK rootKLast < UInt256.size)
    (hrootFiveFit : mintFeeRootTimesFiveNat rootK < UInt256.size)
    (hdenFit : mintFeeDenominatorNat rootK rootKLast < UInt256.size)
    (hdenom : (mintFeeDenominatorWord rootK rootKLast).toNat ≠ 0)
    (hliq : ¬ mintFeeLiquidityInt evm rootK rootKLast > 0) :
    ExecBlock config
      (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast) evm
      [mintFeeRootComparisonStmt, .return [(.var "feeOn")]]
      (.returned
        (mintFeeAfterLiquidityFrame evm reserve0 reserve1 feeTo true kLast rootK rootKLast)
        evm (some [.bool true])) := by
  have hite :
      ExecStmt config
        (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast) evm
        mintFeeRootComparisonStmt
        (.ok (mintFeeAfterLiquidityFrame evm reserve0 reserve1 feeTo true kLast rootK rootKLast)
          evm) := by
    exact ExecStmt.iteTrue
      (evalExpr_mintFee_rootK_gt_rootKLast_true evm reserve0 reserve1 feeTo true kLast rootK
        rootKLast hroot)
      (uniswapMintFeePositiveRootBranch_noLiquidity evm reserve0 reserve1 feeTo kLast rootK
        rootKLast hroot hrootKNonneg hrootKSize hrootKLastNonneg hnumFit hrootFiveFit
        hdenFit hdenom hliq)
  exact ExecBlock.consNormal hite
    (ExecBlock.consReturn
      (ExecStmt.return
        (evalExprs?_singleton
          (evalExpr_mintFee_afterLiquidity_feeOn evm reserve0 reserve1 feeTo true kLast rootK
            rootKLast))))

theorem uniswapMintFeeAfterRoots_positiveWithLiquidity
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (kLast : UInt256) (rootK rootKLast : Int)
    (hroot : rootK > rootKLast) (hrootKNonneg : 0 ≤ rootK)
    (hrootKSize : rootK.toNat < UInt256.size) (hrootKLastNonneg : 0 ≤ rootKLast)
    (hnumFit : mintFeeNumeratorNat evm rootK rootKLast < UInt256.size)
    (hrootFiveFit : mintFeeRootTimesFiveNat rootK < UInt256.size)
    (hdenFit : mintFeeDenominatorNat rootK rootKLast < UInt256.size)
    (hdenom : (mintFeeDenominatorWord rootK rootKLast).toNat ≠ 0)
    (hliq : mintFeeLiquidityInt evm rootK rootKLast > 0)
    (hliqFit : (mintFeeLiquidityInt evm rootK rootKLast).toNat < UInt256.size)
    (hfitSupply :
      mintFunctionTotalSupplyNewNat evm (mintFeeLiquidityWord evm rootK rootKLast) <
        UInt256.size)
    (hfitBalance :
      mintFunctionToBalanceNewNat evm feeTo (mintFeeLiquidityWord evm rootK rootKLast) <
        UInt256.size) :
    ExecBlock config
      (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast) evm
      [mintFeeRootComparisonStmt]
      (.ok (mintFeeAfterFeeMintFrame evm reserve0 reserve1 feeTo kLast rootK rootKLast)
        (mintFunctionPostState evm feeTo (mintFeeLiquidityWord evm rootK rootKLast))) := by
  have hite :
      ExecStmt config
        (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast) evm
        mintFeeRootComparisonStmt
        (.ok (mintFeeAfterFeeMintFrame evm reserve0 reserve1 feeTo kLast rootK rootKLast)
          (mintFunctionPostState evm feeTo (mintFeeLiquidityWord evm rootK rootKLast))) := by
    exact ExecStmt.iteTrue
      (evalExpr_mintFee_rootK_gt_rootKLast_true evm reserve0 reserve1 feeTo true kLast rootK
        rootKLast hroot)
      (uniswapMintFeePositiveRootBranch_withLiquidity evm reserve0 reserve1 feeTo kLast rootK
        rootKLast hroot hrootKNonneg hrootKSize hrootKLastNonneg hnumFit hrootFiveFit
        hdenFit hdenom hliq hliqFit hfitSupply hfitBalance)
  exact ExecBlock.consNormal hite ExecBlock.nil

theorem uniswapMintFeeAfterRoots_positiveWithLiquidityReturn
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (kLast : UInt256) (rootK rootKLast : Int)
    (hroot : rootK > rootKLast) (hrootKNonneg : 0 ≤ rootK)
    (hrootKSize : rootK.toNat < UInt256.size) (hrootKLastNonneg : 0 ≤ rootKLast)
    (hnumFit : mintFeeNumeratorNat evm rootK rootKLast < UInt256.size)
    (hrootFiveFit : mintFeeRootTimesFiveNat rootK < UInt256.size)
    (hdenFit : mintFeeDenominatorNat rootK rootKLast < UInt256.size)
    (hdenom : (mintFeeDenominatorWord rootK rootKLast).toNat ≠ 0)
    (hliq : mintFeeLiquidityInt evm rootK rootKLast > 0)
    (hliqFit : (mintFeeLiquidityInt evm rootK rootKLast).toNat < UInt256.size)
    (hfitSupply :
      mintFunctionTotalSupplyNewNat evm (mintFeeLiquidityWord evm rootK rootKLast) <
        UInt256.size)
    (hfitBalance :
      mintFunctionToBalanceNewNat evm feeTo (mintFeeLiquidityWord evm rootK rootKLast) <
        UInt256.size) :
    ExecBlock config
      (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast) evm
      [mintFeeRootComparisonStmt, .return [(.var "feeOn")]]
      (.returned
        (mintFeeAfterFeeMintFrame evm reserve0 reserve1 feeTo kLast rootK rootKLast)
        (mintFunctionPostState evm feeTo (mintFeeLiquidityWord evm rootK rootKLast))
        (some [.bool true])) := by
  have hite :
      ExecStmt config
        (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast) evm
        mintFeeRootComparisonStmt
        (.ok (mintFeeAfterFeeMintFrame evm reserve0 reserve1 feeTo kLast rootK rootKLast)
          (mintFunctionPostState evm feeTo (mintFeeLiquidityWord evm rootK rootKLast))) := by
    exact ExecStmt.iteTrue
      (evalExpr_mintFee_rootK_gt_rootKLast_true evm reserve0 reserve1 feeTo true kLast rootK
        rootKLast hroot)
      (uniswapMintFeePositiveRootBranch_withLiquidity evm reserve0 reserve1 feeTo kLast rootK
        rootKLast hroot hrootKNonneg hrootKSize hrootKLastNonneg hnumFit hrootFiveFit
        hdenFit hdenom hliq hliqFit hfitSupply hfitBalance)
  exact ExecBlock.consNormal hite
    (ExecBlock.consReturn
      (ExecStmt.return
        (evalExprs?_singleton
          (evalExpr_mintFee_afterFeeMint_feeOn evm
            (mintFunctionPostState evm feeTo (mintFeeLiquidityWord evm rootK rootKLast))
            reserve0 reserve1 feeTo kLast rootK rootKLast))))

theorem uniswapMintFeeFunctionBody_feeOn_kLastNonzero_fromRootBlock
    (evm evmFee finalEvm : EVM.State) (reserve0 reserve1 : UInt256) {out : ByteArray}
    (feeTo : AccountAddress) (finalFrame : Frame)
    (hguard :
      evalExpr? config (mintFeeCallFrame reserve0 reserve1) evm
        (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM config evm (EVM.address (uniswapAddressAtSlot evm ⟨5⟩))
      "feeTo" 0 [] (true, evmFee, out) false)
    (hdec : config.externalABI.decode? "feeTo" out = some [.address feeTo])
    (hfeeTo : feeTo ≠ AccountAddress.ofNat 0)
    (hkLast : (mintFeeKLastWord evmFee).toNat ≠ 0)
    (hrootBlock :
      ExecBlock config
        (mintFeeAfterKLastFrame reserve0 reserve1 feeTo true (mintFeeKLastWord evmFee))
        evmFee
        [ .internalCall "sqrt" [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))]
            "rootK",
          .internalCall "sqrt" [.var "_kLast"] "rootKLast",
          .ite (.binary .gt (.var "rootK") (.var "rootKLast"))
            [ .letDecl "numerator" (some uint256)
                (u256 (.binary .mul (.storage totalSupplyRef)
                  (u256 (.binary .sub (.var "rootK") (.var "rootKLast"))))),
              .letDecl "denominator" (some uint256)
                (u256 (.binary .add
                  (u256 (.binary .mul (.var "rootK") (.intLit 5)))
                  (.var "rootKLast"))),
              .letDecl "liquidity" (some uint256)
                (.binary .div (.var "numerator") (.var "denominator")),
              .ite (.binary .gt (.var "liquidity") (.intLit 0))
                [ .internalCall "_mint" [.var "feeTo", .var "liquidity"] "_feeMint" ]
                [] ]
            [] ]
        (.ok finalFrame finalEvm))
    (hreturn : evalExpr? config finalFrame finalEvm (.var "feeOn") = .ok (.bool true)) :
    ExecFuncBody config (mintFeeCallFrame reserve0 reserve1) evm mintFeeFunction.body
      (.returned finalFrame finalEvm (some [.bool true])) := by
  have hchecked :=
    uniswapMintFeeCheckedCallSuccess evm evmFee reserve0 reserve1 feeTo hguard hcall hdec
  have htail :
      ExecBlock config (mintFeeAfterFeeToFrame reserve0 reserve1 feeTo) evmFee
        [ .letDecl "feeOn" (some boolTy) (.binary .ne (.var "feeTo") zeroAddr),
          .letDecl "_kLast" (some uint256) (.storage kLastRef),
          .ite (.var "feeOn")
            [ .ite (.binary .ne (.var "_kLast") (.intLit 0))
                [ .internalCall "sqrt"
                    [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))] "rootK",
                  .internalCall "sqrt" [.var "_kLast"] "rootKLast",
                  .ite (.binary .gt (.var "rootK") (.var "rootKLast"))
                    [ .letDecl "numerator" (some uint256)
                        (u256 (.binary .mul (.storage totalSupplyRef)
                          (u256 (.binary .sub (.var "rootK") (.var "rootKLast"))))),
                      .letDecl "denominator" (some uint256)
                        (u256 (.binary .add
                          (u256 (.binary .mul (.var "rootK") (.intLit 5)))
                          (.var "rootKLast"))),
                      .letDecl "liquidity" (some uint256)
                        (.binary .div (.var "numerator") (.var "denominator")),
                      .ite (.binary .gt (.var "liquidity") (.intLit 0))
                        [ .internalCall "_mint" [.var "feeTo", .var "liquidity"] "_feeMint" ]
                        [] ]
                    [] ]
                [] ]
            [ .ite (.binary .ne (.var "_kLast") (.intLit 0))
                [ .assign .storage kLastRef (.intLit 0) ]
                [] ],
          .return [(.var "feeOn")] ]
        (.returned finalFrame finalEvm (some [.bool true])) := by
    refine ExecBlock.consNormal
      (ExecStmt.letDecl (evalExpr_mintFee_feeOn_true evmFee reserve0 reserve1 feeTo hfeeTo))
      ?_
    refine ExecBlock.consNormal
      (ExecStmt.letDecl (evalExpr_mintFee_afterFeeOn_kLast evmFee reserve0 reserve1 feeTo true))
      ?_
    have htrueBranch :
        ExecBlock config
          (mintFeeAfterKLastFrame reserve0 reserve1 feeTo true (mintFeeKLastWord evmFee))
          evmFee
          [ .ite (.binary .ne (.var "_kLast") (.intLit 0))
              [ .internalCall "sqrt"
                  [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))] "rootK",
                .internalCall "sqrt" [.var "_kLast"] "rootKLast",
                .ite (.binary .gt (.var "rootK") (.var "rootKLast"))
                  [ .letDecl "numerator" (some uint256)
                      (u256 (.binary .mul (.storage totalSupplyRef)
                        (u256 (.binary .sub (.var "rootK") (.var "rootKLast"))))),
                    .letDecl "denominator" (some uint256)
                      (u256 (.binary .add
                        (u256 (.binary .mul (.var "rootK") (.intLit 5)))
                        (.var "rootKLast"))),
                    .letDecl "liquidity" (some uint256)
                      (.binary .div (.var "numerator") (.var "denominator")),
                    .ite (.binary .gt (.var "liquidity") (.intLit 0))
                      [ .internalCall "_mint" [.var "feeTo", .var "liquidity"] "_feeMint" ]
                      [] ]
                  [] ]
              [] ]
          (.ok finalFrame finalEvm) := by
      exact ExecBlock.consNormal
        (ExecStmt.iteTrue
          (evalExpr_mintFee_afterKLast_kLast_ne_zero_true evmFee reserve0 reserve1 feeTo
            true (mintFeeKLastWord evmFee) hkLast)
          hrootBlock)
        ExecBlock.nil
    have houter :
        ExecStmt config
          (mintFeeAfterKLastFrame reserve0 reserve1 feeTo true (mintFeeKLastWord evmFee))
          evmFee
          (.ite (.var "feeOn")
            [ .ite (.binary .ne (.var "_kLast") (.intLit 0))
                [ .internalCall "sqrt"
                    [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))] "rootK",
                  .internalCall "sqrt" [.var "_kLast"] "rootKLast",
                  .ite (.binary .gt (.var "rootK") (.var "rootKLast"))
                    [ .letDecl "numerator" (some uint256)
                        (u256 (.binary .mul (.storage totalSupplyRef)
                          (u256 (.binary .sub (.var "rootK") (.var "rootKLast"))))),
                      .letDecl "denominator" (some uint256)
                        (u256 (.binary .add
                          (u256 (.binary .mul (.var "rootK") (.intLit 5)))
                          (.var "rootKLast"))),
                      .letDecl "liquidity" (some uint256)
                        (.binary .div (.var "numerator") (.var "denominator")),
                      .ite (.binary .gt (.var "liquidity") (.intLit 0))
                        [ .internalCall "_mint" [.var "feeTo", .var "liquidity"] "_feeMint" ]
                        [] ]
                    [] ]
                [] ]
            [ .ite (.binary .ne (.var "_kLast") (.intLit 0))
                [ .assign .storage kLastRef (.intLit 0) ]
                [] ])
          (.ok finalFrame finalEvm) := by
      exact ExecStmt.iteTrue
        (evalExpr_mintFee_afterKLast_feeOn evmFee reserve0 reserve1 feeTo true
          (mintFeeKLastWord evmFee))
        htrueBranch
    exact ExecBlock.consNormal houter
      (ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hreturn)))
  refine ExecFuncBody.execBlockRet ?_
  simpa [mintFeeFunction, List.append_assoc] using
    Reasoning.Refinement.execBlock_append hchecked htail

theorem uniswapMintFeeFunctionBody_feeOn_kLastNonzero_positiveNoLiquidity
    (evm evmFee : EVM.State) (reserve0 reserve1 : UInt256) {out : ByteArray}
    (feeTo : AccountAddress) (rootK rootKLast : Int)
    (hguard :
      evalExpr? config (mintFeeCallFrame reserve0 reserve1) evm
        (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM config evm (EVM.address (uniswapAddressAtSlot evm ⟨5⟩))
      "feeTo" 0 [] (true, evmFee, out) false)
    (hdec : config.externalABI.decode? "feeTo" out = some [.address feeTo])
    (hfeeTo : feeTo ≠ AccountAddress.ofNat 0)
    (hkLast : (mintFeeKLastWord evmFee).toNat ≠ 0)
    (hprefix :
      ExecBlock config
        (mintFeeAfterKLastFrame reserve0 reserve1 feeTo true (mintFeeKLastWord evmFee))
        evmFee
        [ .internalCall "sqrt" [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))]
            "rootK",
          .internalCall "sqrt" [.var "_kLast"] "rootKLast" ]
        (.ok
          (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true
            (mintFeeKLastWord evmFee) rootK rootKLast)
          evmFee))
    (hroot : rootK > rootKLast) (hrootKNonneg : 0 ≤ rootK)
    (hrootKSize : rootK.toNat < UInt256.size) (hrootKLastNonneg : 0 ≤ rootKLast)
    (hnumFit : mintFeeNumeratorNat evmFee rootK rootKLast < UInt256.size)
    (hrootFiveFit : mintFeeRootTimesFiveNat rootK < UInt256.size)
    (hdenFit : mintFeeDenominatorNat rootK rootKLast < UInt256.size)
    (hdenom : (mintFeeDenominatorWord rootK rootKLast).toNat ≠ 0)
    (hliq : ¬ mintFeeLiquidityInt evmFee rootK rootKLast > 0) :
    ExecFuncBody config (mintFeeCallFrame reserve0 reserve1) evm mintFeeFunction.body
      (.returned
        (mintFeeAfterLiquidityFrame evmFee reserve0 reserve1 feeTo true
          (mintFeeKLastWord evmFee) rootK rootKLast)
        evmFee (some [.bool true])) := by
  have hrootBlock :
      ExecBlock config
        (mintFeeAfterKLastFrame reserve0 reserve1 feeTo true (mintFeeKLastWord evmFee))
        evmFee
        [ .internalCall "sqrt" [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))]
            "rootK",
          .internalCall "sqrt" [.var "_kLast"] "rootKLast",
          .ite (.binary .gt (.var "rootK") (.var "rootKLast"))
            [ .letDecl "numerator" (some uint256)
                (u256 (.binary .mul (.storage totalSupplyRef)
                  (u256 (.binary .sub (.var "rootK") (.var "rootKLast"))))),
              .letDecl "denominator" (some uint256)
                (u256 (.binary .add
                  (u256 (.binary .mul (.var "rootK") (.intLit 5)))
                  (.var "rootKLast"))),
              .letDecl "liquidity" (some uint256)
                (.binary .div (.var "numerator") (.var "denominator")),
              .ite (.binary .gt (.var "liquidity") (.intLit 0))
                [ .internalCall "_mint" [.var "feeTo", .var "liquidity"] "_feeMint" ]
                [] ]
            [] ]
        (.ok
          (mintFeeAfterLiquidityFrame evmFee reserve0 reserve1 feeTo true
            (mintFeeKLastWord evmFee) rootK rootKLast)
          evmFee) := by
    simpa [mintFeeRootComparisonStmt, mintFeePositiveRootBranchStmts, List.append_assoc]
      using Reasoning.Refinement.execBlock_append hprefix
        (uniswapMintFeeAfterRoots_positiveNoLiquidity evmFee reserve0 reserve1 feeTo
          (mintFeeKLastWord evmFee) rootK rootKLast hroot hrootKNonneg hrootKSize
          hrootKLastNonneg hnumFit hrootFiveFit hdenFit hdenom hliq)
  exact uniswapMintFeeFunctionBody_feeOn_kLastNonzero_fromRootBlock
    evm evmFee evmFee reserve0 reserve1 feeTo
    (mintFeeAfterLiquidityFrame evmFee reserve0 reserve1 feeTo true
      (mintFeeKLastWord evmFee) rootK rootKLast)
    hguard hcall hdec hfeeTo hkLast hrootBlock
    (evalExpr_mintFee_afterLiquidity_feeOn evmFee reserve0 reserve1 feeTo true
      (mintFeeKLastWord evmFee) rootK rootKLast)

theorem uniswapMintFeeFunctionBody_feeOn_kLastNonzero_positiveWithLiquidity
    (evm evmFee : EVM.State) (reserve0 reserve1 : UInt256) {out : ByteArray}
    (feeTo : AccountAddress) (rootK rootKLast : Int)
    (hguard :
      evalExpr? config (mintFeeCallFrame reserve0 reserve1) evm
        (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM config evm (EVM.address (uniswapAddressAtSlot evm ⟨5⟩))
      "feeTo" 0 [] (true, evmFee, out) false)
    (hdec : config.externalABI.decode? "feeTo" out = some [.address feeTo])
    (hfeeTo : feeTo ≠ AccountAddress.ofNat 0)
    (hkLast : (mintFeeKLastWord evmFee).toNat ≠ 0)
    (hprefix :
      ExecBlock config
        (mintFeeAfterKLastFrame reserve0 reserve1 feeTo true (mintFeeKLastWord evmFee))
        evmFee
        [ .internalCall "sqrt" [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))]
            "rootK",
          .internalCall "sqrt" [.var "_kLast"] "rootKLast" ]
        (.ok
          (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true
            (mintFeeKLastWord evmFee) rootK rootKLast)
          evmFee))
    (hroot : rootK > rootKLast) (hrootKNonneg : 0 ≤ rootK)
    (hrootKSize : rootK.toNat < UInt256.size) (hrootKLastNonneg : 0 ≤ rootKLast)
    (hnumFit : mintFeeNumeratorNat evmFee rootK rootKLast < UInt256.size)
    (hrootFiveFit : mintFeeRootTimesFiveNat rootK < UInt256.size)
    (hdenFit : mintFeeDenominatorNat rootK rootKLast < UInt256.size)
    (hdenom : (mintFeeDenominatorWord rootK rootKLast).toNat ≠ 0)
    (hliq : mintFeeLiquidityInt evmFee rootK rootKLast > 0)
    (hliqFit : (mintFeeLiquidityInt evmFee rootK rootKLast).toNat < UInt256.size)
    (hfitSupply :
      mintFunctionTotalSupplyNewNat evmFee (mintFeeLiquidityWord evmFee rootK rootKLast) <
        UInt256.size)
    (hfitBalance :
      mintFunctionToBalanceNewNat evmFee feeTo (mintFeeLiquidityWord evmFee rootK rootKLast) <
        UInt256.size) :
    ExecFuncBody config (mintFeeCallFrame reserve0 reserve1) evm mintFeeFunction.body
      (.returned
        (mintFeeAfterFeeMintFrame evmFee reserve0 reserve1 feeTo (mintFeeKLastWord evmFee)
          rootK rootKLast)
        (mintFunctionPostState evmFee feeTo (mintFeeLiquidityWord evmFee rootK rootKLast))
        (some [.bool true])) := by
  have hrootBlock :
      ExecBlock config
        (mintFeeAfterKLastFrame reserve0 reserve1 feeTo true (mintFeeKLastWord evmFee))
        evmFee
        [ .internalCall "sqrt" [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))]
            "rootK",
          .internalCall "sqrt" [.var "_kLast"] "rootKLast",
          .ite (.binary .gt (.var "rootK") (.var "rootKLast"))
            [ .letDecl "numerator" (some uint256)
                (u256 (.binary .mul (.storage totalSupplyRef)
                  (u256 (.binary .sub (.var "rootK") (.var "rootKLast"))))),
              .letDecl "denominator" (some uint256)
                (u256 (.binary .add
                  (u256 (.binary .mul (.var "rootK") (.intLit 5)))
                  (.var "rootKLast"))),
              .letDecl "liquidity" (some uint256)
                (.binary .div (.var "numerator") (.var "denominator")),
              .ite (.binary .gt (.var "liquidity") (.intLit 0))
                [ .internalCall "_mint" [.var "feeTo", .var "liquidity"] "_feeMint" ]
                [] ]
            [] ]
        (.ok
          (mintFeeAfterFeeMintFrame evmFee reserve0 reserve1 feeTo (mintFeeKLastWord evmFee)
            rootK rootKLast)
          (mintFunctionPostState evmFee feeTo (mintFeeLiquidityWord evmFee rootK rootKLast))) := by
    simpa [mintFeeRootComparisonStmt, mintFeePositiveRootBranchStmts, List.append_assoc]
      using Reasoning.Refinement.execBlock_append hprefix
        (uniswapMintFeeAfterRoots_positiveWithLiquidity evmFee reserve0 reserve1 feeTo
          (mintFeeKLastWord evmFee) rootK rootKLast hroot hrootKNonneg hrootKSize
          hrootKLastNonneg hnumFit hrootFiveFit hdenFit hdenom hliq hliqFit hfitSupply
          hfitBalance)
  exact uniswapMintFeeFunctionBody_feeOn_kLastNonzero_fromRootBlock
    evm evmFee (mintFunctionPostState evmFee feeTo (mintFeeLiquidityWord evmFee rootK rootKLast))
    reserve0 reserve1 feeTo
    (mintFeeAfterFeeMintFrame evmFee reserve0 reserve1 feeTo (mintFeeKLastWord evmFee)
      rootK rootKLast)
    hguard hcall hdec hfeeTo hkLast hrootBlock
    (evalExpr_mintFee_afterFeeMint_feeOn evmFee
      (mintFunctionPostState evmFee feeTo (mintFeeLiquidityWord evmFee rootK rootKLast))
      reserve0 reserve1 feeTo (mintFeeKLastWord evmFee) rootK rootKLast)

theorem uniswapMintFeeFunctionBody_feeOn_kLastNonzero_noMint
    (evm evmFee : EVM.State) (reserve0 reserve1 : UInt256) {out : ByteArray}
    (feeTo : AccountAddress) (rootK rootKLast : Int)
    (hguard :
      evalExpr? config (mintFeeCallFrame reserve0 reserve1) evm
        (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM config evm (EVM.address (uniswapAddressAtSlot evm ⟨5⟩))
      "feeTo" 0 [] (true, evmFee, out) false)
    (hdec : config.externalABI.decode? "feeTo" out = some [.address feeTo])
    (hfeeTo : feeTo ≠ AccountAddress.ofNat 0)
    (hkLast : (mintFeeKLastWord evmFee).toNat ≠ 0)
    (hprefix :
      ExecBlock config
        (mintFeeAfterKLastFrame reserve0 reserve1 feeTo true (mintFeeKLastWord evmFee))
        evmFee
        [ .internalCall "sqrt" [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))]
            "rootK",
          .internalCall "sqrt" [.var "_kLast"] "rootKLast" ]
        (.ok
          (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true
            (mintFeeKLastWord evmFee) rootK rootKLast)
          evmFee))
    (hroot : ¬ rootK > rootKLast) :
    ExecFuncBody config (mintFeeCallFrame reserve0 reserve1) evm mintFeeFunction.body
      (.returned
        (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true (mintFeeKLastWord evmFee)
          rootK rootKLast)
        evmFee (some [.bool true])) := by
  have hchecked :=
    uniswapMintFeeCheckedCallSuccess evm evmFee reserve0 reserve1 feeTo hguard hcall hdec
  have hrootBlock :
      ExecBlock config
        (mintFeeAfterKLastFrame reserve0 reserve1 feeTo true (mintFeeKLastWord evmFee))
        evmFee
        [ .internalCall "sqrt" [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))]
            "rootK",
          .internalCall "sqrt" [.var "_kLast"] "rootKLast",
          .ite (.binary .gt (.var "rootK") (.var "rootKLast"))
            [ .letDecl "numerator" (some uint256)
                (u256 (.binary .mul (.storage totalSupplyRef)
                  (u256 (.binary .sub (.var "rootK") (.var "rootKLast"))))),
              .letDecl "denominator" (some uint256)
                (u256 (.binary .add
                  (u256 (.binary .mul (.var "rootK") (.intLit 5)))
                  (.var "rootKLast"))),
              .letDecl "liquidity" (some uint256)
                (.binary .div (.var "numerator") (.var "denominator")),
              .ite (.binary .gt (.var "liquidity") (.intLit 0))
                [ .internalCall "_mint" [.var "feeTo", .var "liquidity"] "_feeMint" ]
                [] ]
            [] ]
        (.ok
          (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true
            (mintFeeKLastWord evmFee) rootK rootKLast)
          evmFee) := by
    simpa [mintFeeRootComparisonStmt, mintFeePositiveRootBranchStmts, List.append_assoc]
      using Reasoning.Refinement.execBlock_append hprefix
        (uniswapMintFeeAfterRoots_noMint evmFee reserve0 reserve1 feeTo
          (mintFeeKLastWord evmFee) rootK rootKLast hroot)
  have htail :
      ExecBlock config (mintFeeAfterFeeToFrame reserve0 reserve1 feeTo) evmFee
        [ .letDecl "feeOn" (some boolTy) (.binary .ne (.var "feeTo") zeroAddr),
          .letDecl "_kLast" (some uint256) (.storage kLastRef),
          .ite (.var "feeOn")
            [ .ite (.binary .ne (.var "_kLast") (.intLit 0))
                [ .internalCall "sqrt"
                    [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))] "rootK",
                  .internalCall "sqrt" [.var "_kLast"] "rootKLast",
                  .ite (.binary .gt (.var "rootK") (.var "rootKLast"))
                    [ .letDecl "numerator" (some uint256)
                        (u256 (.binary .mul (.storage totalSupplyRef)
                          (u256 (.binary .sub (.var "rootK") (.var "rootKLast"))))),
                      .letDecl "denominator" (some uint256)
                        (u256 (.binary .add
                          (u256 (.binary .mul (.var "rootK") (.intLit 5)))
                          (.var "rootKLast"))),
                      .letDecl "liquidity" (some uint256)
                        (.binary .div (.var "numerator") (.var "denominator")),
                      .ite (.binary .gt (.var "liquidity") (.intLit 0))
                        [ .internalCall "_mint" [.var "feeTo", .var "liquidity"] "_feeMint" ]
                        [] ]
                    [] ]
                [] ]
            [ .ite (.binary .ne (.var "_kLast") (.intLit 0))
                [ .assign .storage kLastRef (.intLit 0) ]
                [] ],
          .return [(.var "feeOn")] ]
        (.returned
          (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true
            (mintFeeKLastWord evmFee) rootK rootKLast)
          evmFee (some [.bool true])) := by
    refine ExecBlock.consNormal
      (ExecStmt.letDecl (evalExpr_mintFee_feeOn_true evmFee reserve0 reserve1 feeTo hfeeTo))
      ?_
    refine ExecBlock.consNormal
      (ExecStmt.letDecl (evalExpr_mintFee_afterFeeOn_kLast evmFee reserve0 reserve1 feeTo true))
      ?_
    have htrueBranch :
        ExecBlock config
          (mintFeeAfterKLastFrame reserve0 reserve1 feeTo true (mintFeeKLastWord evmFee))
          evmFee
          [ .ite (.binary .ne (.var "_kLast") (.intLit 0))
              [ .internalCall "sqrt"
                  [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))] "rootK",
                .internalCall "sqrt" [.var "_kLast"] "rootKLast",
                .ite (.binary .gt (.var "rootK") (.var "rootKLast"))
                  [ .letDecl "numerator" (some uint256)
                      (u256 (.binary .mul (.storage totalSupplyRef)
                        (u256 (.binary .sub (.var "rootK") (.var "rootKLast"))))),
                    .letDecl "denominator" (some uint256)
                      (u256 (.binary .add
                        (u256 (.binary .mul (.var "rootK") (.intLit 5)))
                        (.var "rootKLast"))),
                    .letDecl "liquidity" (some uint256)
                      (.binary .div (.var "numerator") (.var "denominator")),
                    .ite (.binary .gt (.var "liquidity") (.intLit 0))
                      [ .internalCall "_mint" [.var "feeTo", .var "liquidity"] "_feeMint" ]
                      [] ]
                  [] ]
              [] ]
          (.ok
            (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true
              (mintFeeKLastWord evmFee) rootK rootKLast)
            evmFee) := by
      exact ExecBlock.consNormal
        (ExecStmt.iteTrue
          (evalExpr_mintFee_afterKLast_kLast_ne_zero_true evmFee reserve0 reserve1 feeTo
            true (mintFeeKLastWord evmFee) hkLast)
          hrootBlock)
        ExecBlock.nil
    have houter :
        ExecStmt config
          (mintFeeAfterKLastFrame reserve0 reserve1 feeTo true (mintFeeKLastWord evmFee))
          evmFee
          (.ite (.var "feeOn")
            [ .ite (.binary .ne (.var "_kLast") (.intLit 0))
                [ .internalCall "sqrt"
                    [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))] "rootK",
                  .internalCall "sqrt" [.var "_kLast"] "rootKLast",
                  .ite (.binary .gt (.var "rootK") (.var "rootKLast"))
                    [ .letDecl "numerator" (some uint256)
                        (u256 (.binary .mul (.storage totalSupplyRef)
                          (u256 (.binary .sub (.var "rootK") (.var "rootKLast"))))),
                      .letDecl "denominator" (some uint256)
                        (u256 (.binary .add
                          (u256 (.binary .mul (.var "rootK") (.intLit 5)))
                          (.var "rootKLast"))),
                      .letDecl "liquidity" (some uint256)
                        (.binary .div (.var "numerator") (.var "denominator")),
                      .ite (.binary .gt (.var "liquidity") (.intLit 0))
                        [ .internalCall "_mint" [.var "feeTo", .var "liquidity"] "_feeMint" ]
                        [] ]
                    [] ]
                [] ]
            [ .ite (.binary .ne (.var "_kLast") (.intLit 0))
                [ .assign .storage kLastRef (.intLit 0) ]
                [] ])
          (.ok
            (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true
              (mintFeeKLastWord evmFee) rootK rootKLast)
            evmFee) := by
      exact ExecStmt.iteTrue
        (evalExpr_mintFee_afterKLast_feeOn evmFee reserve0 reserve1 feeTo true
          (mintFeeKLastWord evmFee))
        htrueBranch
    exact ExecBlock.consNormal houter
      (ExecBlock.consReturn
        (ExecStmt.return
          (evalExprs?_singleton
            (evalExpr_mintFee_afterRootKLast_feeOn evmFee reserve0 reserve1 feeTo true
              (mintFeeKLastWord evmFee) rootK rootKLast))))
  refine ExecFuncBody.execBlockRet ?_
  simpa [mintFeeFunction, List.append_assoc] using
    Reasoning.Refinement.execBlock_append hchecked htail

theorem mintFeeAssignKLastZero
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) :
    assignStorageRef? config (mintFeeAfterKLastFrame reserve0 reserve1 feeTo feeOn kLast)
      evm .storage kLastRef (.int 0) =
        .ok (mintFeeAfterKLastFrame reserve0 reserve1 feeTo feeOn kLast,
          mintFeeKLastClearedState evm) := by
  apply assignStorageRef_storage_scalar
      (er := ({ base := "kLast", steps := [] } : EvaledStorageRef))
      (ty := uint256St) (loc := uint256Loc ⟨11⟩)
  · simp [kLastRef]
  · simp [evalStorageRef, evalStorageRefSteps, kLastRef, EvalResult.bind, pure, bind]
  · simp [storageTypeAt?, contract, storageDecls, uint256St]
  · rfl
  · simpa [mintFeeKLastClearedState, uniswapUint256Value, uint256Value] using
      uniswapStorageLocStore_uint256 evm ⟨11⟩ ⟨0⟩

theorem uniswapMintFeeFunctionBody_feeOff_kLastZero
    (evm evmFee : EVM.State) (reserve0 reserve1 : UInt256) {out : ByteArray}
    (feeTo : AccountAddress)
    (hguard :
      evalExpr? config (mintFeeCallFrame reserve0 reserve1) evm
        (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM config evm (EVM.address (uniswapAddressAtSlot evm ⟨5⟩))
      "feeTo" 0 [] (true, evmFee, out) false)
    (hdec : config.externalABI.decode? "feeTo" out = some [.address feeTo])
    (hfeeTo : feeTo = AccountAddress.ofNat 0)
    (hkLast : (mintFeeKLastWord evmFee).toNat = 0) :
    ExecFuncBody config (mintFeeCallFrame reserve0 reserve1) evm mintFeeFunction.body
      (.returned
        (mintFeeAfterKLastFrame reserve0 reserve1 feeTo false (mintFeeKLastWord evmFee))
        evmFee (some [.bool false])) := by
  have hchecked :=
    uniswapMintFeeCheckedCallSuccess evm evmFee reserve0 reserve1 feeTo hguard hcall hdec
  have htail :
      ExecBlock config (mintFeeAfterFeeToFrame reserve0 reserve1 feeTo) evmFee
        [ .letDecl "feeOn" (some boolTy) (.binary .ne (.var "feeTo") zeroAddr),
          .letDecl "_kLast" (some uint256) (.storage kLastRef),
          .ite (.var "feeOn")
            [ .ite (.binary .ne (.var "_kLast") (.intLit 0))
                [ .internalCall "sqrt"
                    [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))] "rootK",
                  .internalCall "sqrt" [.var "_kLast"] "rootKLast",
                  .ite (.binary .gt (.var "rootK") (.var "rootKLast"))
                    [ .letDecl "numerator" (some uint256)
                        (u256 (.binary .mul (.storage totalSupplyRef)
                          (u256 (.binary .sub (.var "rootK") (.var "rootKLast"))))),
                      .letDecl "denominator" (some uint256)
                        (u256 (.binary .add
                          (u256 (.binary .mul (.var "rootK") (.intLit 5)))
                          (.var "rootKLast"))),
                      .letDecl "liquidity" (some uint256)
                        (.binary .div (.var "numerator") (.var "denominator")),
                      .ite (.binary .gt (.var "liquidity") (.intLit 0))
                        [ .internalCall "_mint" [.var "feeTo", .var "liquidity"] "_feeMint" ]
                        [] ]
                    [] ]
                [] ]
            [ .ite (.binary .ne (.var "_kLast") (.intLit 0))
                [ .assign .storage kLastRef (.intLit 0) ]
                [] ],
          .return [(.var "feeOn")] ]
        (.returned
          (mintFeeAfterKLastFrame reserve0 reserve1 feeTo false (mintFeeKLastWord evmFee))
          evmFee (some [.bool false])) := by
    refine ExecBlock.consNormal
      (ExecStmt.letDecl (evalExpr_mintFee_feeOn_false evmFee reserve0 reserve1 feeTo hfeeTo))
      ?_
    refine ExecBlock.consNormal
      (ExecStmt.letDecl (evalExpr_mintFee_afterFeeOn_kLast evmFee reserve0 reserve1 feeTo false))
      ?_
    have hfalseBranch :
        ExecBlock config
          (mintFeeAfterKLastFrame reserve0 reserve1 feeTo false (mintFeeKLastWord evmFee))
          evmFee
          [ .ite (.binary .ne (.var "_kLast") (.intLit 0))
              [ .assign .storage kLastRef (.intLit 0) ]
              [] ]
          (.ok
            (mintFeeAfterKLastFrame reserve0 reserve1 feeTo false (mintFeeKLastWord evmFee))
            evmFee) := by
      exact ExecBlock.consNormal
        (ExecStmt.iteFalse
          (evalExpr_mintFee_afterKLast_kLast_ne_zero_false evmFee reserve0 reserve1 feeTo
            false (mintFeeKLastWord evmFee) hkLast)
          ExecBlock.nil)
        ExecBlock.nil
    have houter :
        ExecStmt config
          (mintFeeAfterKLastFrame reserve0 reserve1 feeTo false (mintFeeKLastWord evmFee))
          evmFee
          (.ite (.var "feeOn")
            [ .ite (.binary .ne (.var "_kLast") (.intLit 0))
                [ .internalCall "sqrt"
                    [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))] "rootK",
                  .internalCall "sqrt" [.var "_kLast"] "rootKLast",
                  .ite (.binary .gt (.var "rootK") (.var "rootKLast"))
                    [ .letDecl "numerator" (some uint256)
                        (u256 (.binary .mul (.storage totalSupplyRef)
                          (u256 (.binary .sub (.var "rootK") (.var "rootKLast"))))),
                      .letDecl "denominator" (some uint256)
                        (u256 (.binary .add
                          (u256 (.binary .mul (.var "rootK") (.intLit 5)))
                          (.var "rootKLast"))),
                      .letDecl "liquidity" (some uint256)
                        (.binary .div (.var "numerator") (.var "denominator")),
                      .ite (.binary .gt (.var "liquidity") (.intLit 0))
                        [ .internalCall "_mint" [.var "feeTo", .var "liquidity"] "_feeMint" ]
                        [] ]
                    [] ]
                [] ]
            [ .ite (.binary .ne (.var "_kLast") (.intLit 0))
                [ .assign .storage kLastRef (.intLit 0) ]
                [] ])
          (.ok
            (mintFeeAfterKLastFrame reserve0 reserve1 feeTo false (mintFeeKLastWord evmFee))
            evmFee) := by
      exact ExecStmt.iteFalse
        (evalExpr_mintFee_afterKLast_feeOn evmFee reserve0 reserve1 feeTo false
          (mintFeeKLastWord evmFee))
        hfalseBranch
    exact ExecBlock.consNormal houter
      (ExecBlock.consReturn
        (ExecStmt.return
          (evalExprs?_singleton
            (evalExpr_mintFee_return_feeOn evmFee reserve0 reserve1 feeTo false
              (mintFeeKLastWord evmFee)))))
  refine ExecFuncBody.execBlockRet ?_
  simpa [mintFeeFunction, List.append_assoc] using
    Reasoning.Refinement.execBlock_append hchecked htail

theorem uniswapMintFeeFunctionBody_feeOn_kLastZero
    (evm evmFee : EVM.State) (reserve0 reserve1 : UInt256) {out : ByteArray}
    (feeTo : AccountAddress)
    (hguard :
      evalExpr? config (mintFeeCallFrame reserve0 reserve1) evm
        (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM config evm (EVM.address (uniswapAddressAtSlot evm ⟨5⟩))
      "feeTo" 0 [] (true, evmFee, out) false)
    (hdec : config.externalABI.decode? "feeTo" out = some [.address feeTo])
    (hfeeTo : feeTo ≠ AccountAddress.ofNat 0)
    (hkLast : (mintFeeKLastWord evmFee).toNat = 0) :
    ExecFuncBody config (mintFeeCallFrame reserve0 reserve1) evm mintFeeFunction.body
      (.returned
        (mintFeeAfterKLastFrame reserve0 reserve1 feeTo true (mintFeeKLastWord evmFee))
        evmFee (some [.bool true])) := by
  have hchecked :=
    uniswapMintFeeCheckedCallSuccess evm evmFee reserve0 reserve1 feeTo hguard hcall hdec
  have htail :
      ExecBlock config (mintFeeAfterFeeToFrame reserve0 reserve1 feeTo) evmFee
        [ .letDecl "feeOn" (some boolTy) (.binary .ne (.var "feeTo") zeroAddr),
          .letDecl "_kLast" (some uint256) (.storage kLastRef),
          .ite (.var "feeOn")
            [ .ite (.binary .ne (.var "_kLast") (.intLit 0))
                [ .internalCall "sqrt"
                    [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))] "rootK",
                  .internalCall "sqrt" [.var "_kLast"] "rootKLast",
                  .ite (.binary .gt (.var "rootK") (.var "rootKLast"))
                    [ .letDecl "numerator" (some uint256)
                        (u256 (.binary .mul (.storage totalSupplyRef)
                          (u256 (.binary .sub (.var "rootK") (.var "rootKLast"))))),
                      .letDecl "denominator" (some uint256)
                        (u256 (.binary .add
                          (u256 (.binary .mul (.var "rootK") (.intLit 5)))
                          (.var "rootKLast"))),
                      .letDecl "liquidity" (some uint256)
                        (.binary .div (.var "numerator") (.var "denominator")),
                      .ite (.binary .gt (.var "liquidity") (.intLit 0))
                        [ .internalCall "_mint" [.var "feeTo", .var "liquidity"] "_feeMint" ]
                        [] ]
                    [] ]
                [] ]
            [ .ite (.binary .ne (.var "_kLast") (.intLit 0))
                [ .assign .storage kLastRef (.intLit 0) ]
                [] ],
          .return [(.var "feeOn")] ]
        (.returned
          (mintFeeAfterKLastFrame reserve0 reserve1 feeTo true (mintFeeKLastWord evmFee))
          evmFee (some [.bool true])) := by
    refine ExecBlock.consNormal
      (ExecStmt.letDecl (evalExpr_mintFee_feeOn_true evmFee reserve0 reserve1 feeTo hfeeTo))
      ?_
    refine ExecBlock.consNormal
      (ExecStmt.letDecl (evalExpr_mintFee_afterFeeOn_kLast evmFee reserve0 reserve1 feeTo true))
      ?_
    have htrueBranch :
        ExecBlock config
          (mintFeeAfterKLastFrame reserve0 reserve1 feeTo true (mintFeeKLastWord evmFee))
          evmFee
          [ .ite (.binary .ne (.var "_kLast") (.intLit 0))
              [ .internalCall "sqrt"
                  [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))] "rootK",
                .internalCall "sqrt" [.var "_kLast"] "rootKLast",
                .ite (.binary .gt (.var "rootK") (.var "rootKLast"))
                  [ .letDecl "numerator" (some uint256)
                      (u256 (.binary .mul (.storage totalSupplyRef)
                        (u256 (.binary .sub (.var "rootK") (.var "rootKLast"))))),
                    .letDecl "denominator" (some uint256)
                      (u256 (.binary .add
                        (u256 (.binary .mul (.var "rootK") (.intLit 5)))
                        (.var "rootKLast"))),
                    .letDecl "liquidity" (some uint256)
                      (.binary .div (.var "numerator") (.var "denominator")),
                    .ite (.binary .gt (.var "liquidity") (.intLit 0))
                      [ .internalCall "_mint" [.var "feeTo", .var "liquidity"] "_feeMint" ]
                      [] ]
                  [] ]
              [] ]
          (.ok
            (mintFeeAfterKLastFrame reserve0 reserve1 feeTo true (mintFeeKLastWord evmFee))
            evmFee) := by
      exact ExecBlock.consNormal
        (ExecStmt.iteFalse
          (evalExpr_mintFee_afterKLast_kLast_ne_zero_false evmFee reserve0 reserve1 feeTo
            true (mintFeeKLastWord evmFee) hkLast)
          ExecBlock.nil)
        ExecBlock.nil
    have houter :
        ExecStmt config
          (mintFeeAfterKLastFrame reserve0 reserve1 feeTo true (mintFeeKLastWord evmFee))
          evmFee
          (.ite (.var "feeOn")
            [ .ite (.binary .ne (.var "_kLast") (.intLit 0))
                [ .internalCall "sqrt"
                    [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))] "rootK",
                  .internalCall "sqrt" [.var "_kLast"] "rootKLast",
                  .ite (.binary .gt (.var "rootK") (.var "rootKLast"))
                    [ .letDecl "numerator" (some uint256)
                        (u256 (.binary .mul (.storage totalSupplyRef)
                          (u256 (.binary .sub (.var "rootK") (.var "rootKLast"))))),
                      .letDecl "denominator" (some uint256)
                        (u256 (.binary .add
                          (u256 (.binary .mul (.var "rootK") (.intLit 5)))
                          (.var "rootKLast"))),
                      .letDecl "liquidity" (some uint256)
                        (.binary .div (.var "numerator") (.var "denominator")),
                      .ite (.binary .gt (.var "liquidity") (.intLit 0))
                        [ .internalCall "_mint" [.var "feeTo", .var "liquidity"] "_feeMint" ]
                        [] ]
                    [] ]
                [] ]
            [ .ite (.binary .ne (.var "_kLast") (.intLit 0))
                [ .assign .storage kLastRef (.intLit 0) ]
                [] ])
          (.ok
            (mintFeeAfterKLastFrame reserve0 reserve1 feeTo true (mintFeeKLastWord evmFee))
            evmFee) := by
      exact ExecStmt.iteTrue
        (evalExpr_mintFee_afterKLast_feeOn evmFee reserve0 reserve1 feeTo true
          (mintFeeKLastWord evmFee))
        htrueBranch
    exact ExecBlock.consNormal houter
      (ExecBlock.consReturn
        (ExecStmt.return
          (evalExprs?_singleton
            (evalExpr_mintFee_return_feeOn evmFee reserve0 reserve1 feeTo true
              (mintFeeKLastWord evmFee)))))
  refine ExecFuncBody.execBlockRet ?_
  simpa [mintFeeFunction, List.append_assoc] using
    Reasoning.Refinement.execBlock_append hchecked htail

theorem uniswapMintFeeFunctionBody_feeOff_kLastNonzero
    (evm evmFee : EVM.State) (reserve0 reserve1 : UInt256) {out : ByteArray}
    (feeTo : AccountAddress)
    (hguard :
      evalExpr? config (mintFeeCallFrame reserve0 reserve1) evm
        (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM config evm (EVM.address (uniswapAddressAtSlot evm ⟨5⟩))
      "feeTo" 0 [] (true, evmFee, out) false)
    (hdec : config.externalABI.decode? "feeTo" out = some [.address feeTo])
    (hfeeTo : feeTo = AccountAddress.ofNat 0)
    (hkLast : (mintFeeKLastWord evmFee).toNat ≠ 0) :
    ExecFuncBody config (mintFeeCallFrame reserve0 reserve1) evm mintFeeFunction.body
      (.returned
        (mintFeeAfterKLastFrame reserve0 reserve1 feeTo false (mintFeeKLastWord evmFee))
        (mintFeeKLastClearedState evmFee) (some [.bool false])) := by
  have hchecked :=
    uniswapMintFeeCheckedCallSuccess evm evmFee reserve0 reserve1 feeTo hguard hcall hdec
  have htail :
      ExecBlock config (mintFeeAfterFeeToFrame reserve0 reserve1 feeTo) evmFee
        [ .letDecl "feeOn" (some boolTy) (.binary .ne (.var "feeTo") zeroAddr),
          .letDecl "_kLast" (some uint256) (.storage kLastRef),
          .ite (.var "feeOn")
            [ .ite (.binary .ne (.var "_kLast") (.intLit 0))
                [ .internalCall "sqrt"
                    [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))] "rootK",
                  .internalCall "sqrt" [.var "_kLast"] "rootKLast",
                  .ite (.binary .gt (.var "rootK") (.var "rootKLast"))
                    [ .letDecl "numerator" (some uint256)
                        (u256 (.binary .mul (.storage totalSupplyRef)
                          (u256 (.binary .sub (.var "rootK") (.var "rootKLast"))))),
                      .letDecl "denominator" (some uint256)
                        (u256 (.binary .add
                          (u256 (.binary .mul (.var "rootK") (.intLit 5)))
                          (.var "rootKLast"))),
                      .letDecl "liquidity" (some uint256)
                        (.binary .div (.var "numerator") (.var "denominator")),
                      .ite (.binary .gt (.var "liquidity") (.intLit 0))
                        [ .internalCall "_mint" [.var "feeTo", .var "liquidity"] "_feeMint" ]
                        [] ]
                    [] ]
                [] ]
            [ .ite (.binary .ne (.var "_kLast") (.intLit 0))
                [ .assign .storage kLastRef (.intLit 0) ]
                [] ],
          .return [(.var "feeOn")] ]
        (.returned
          (mintFeeAfterKLastFrame reserve0 reserve1 feeTo false (mintFeeKLastWord evmFee))
          (mintFeeKLastClearedState evmFee) (some [.bool false])) := by
    refine ExecBlock.consNormal
      (ExecStmt.letDecl (evalExpr_mintFee_feeOn_false evmFee reserve0 reserve1 feeTo hfeeTo))
      ?_
    refine ExecBlock.consNormal
      (ExecStmt.letDecl (evalExpr_mintFee_afterFeeOn_kLast evmFee reserve0 reserve1 feeTo false))
      ?_
    have hassign :
        ExecBlock config
          (mintFeeAfterKLastFrame reserve0 reserve1 feeTo false (mintFeeKLastWord evmFee))
          evmFee
          [ .assign .storage kLastRef (.intLit 0) ]
          (.ok
            (mintFeeAfterKLastFrame reserve0 reserve1 feeTo false (mintFeeKLastWord evmFee))
            (mintFeeKLastClearedState evmFee)) := by
      exact ExecBlock.consNormal
        (ExecStmt.assign (by simp [evalExpr?, pure])
          (mintFeeAssignKLastZero evmFee reserve0 reserve1 feeTo false
            (mintFeeKLastWord evmFee)))
        ExecBlock.nil
    have hfalseBranch :
        ExecBlock config
          (mintFeeAfterKLastFrame reserve0 reserve1 feeTo false (mintFeeKLastWord evmFee))
          evmFee
          [ .ite (.binary .ne (.var "_kLast") (.intLit 0))
              [ .assign .storage kLastRef (.intLit 0) ]
              [] ]
          (.ok
            (mintFeeAfterKLastFrame reserve0 reserve1 feeTo false (mintFeeKLastWord evmFee))
            (mintFeeKLastClearedState evmFee)) := by
      exact ExecBlock.consNormal
        (ExecStmt.iteTrue
          (evalExpr_mintFee_afterKLast_kLast_ne_zero_true evmFee reserve0 reserve1 feeTo
            false (mintFeeKLastWord evmFee) hkLast)
          hassign)
        ExecBlock.nil
    have houter :
        ExecStmt config
          (mintFeeAfterKLastFrame reserve0 reserve1 feeTo false (mintFeeKLastWord evmFee))
          evmFee
          (.ite (.var "feeOn")
            [ .ite (.binary .ne (.var "_kLast") (.intLit 0))
                [ .internalCall "sqrt"
                    [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))] "rootK",
                  .internalCall "sqrt" [.var "_kLast"] "rootKLast",
                  .ite (.binary .gt (.var "rootK") (.var "rootKLast"))
                    [ .letDecl "numerator" (some uint256)
                        (u256 (.binary .mul (.storage totalSupplyRef)
                          (u256 (.binary .sub (.var "rootK") (.var "rootKLast"))))),
                      .letDecl "denominator" (some uint256)
                        (u256 (.binary .add
                          (u256 (.binary .mul (.var "rootK") (.intLit 5)))
                          (.var "rootKLast"))),
                      .letDecl "liquidity" (some uint256)
                        (.binary .div (.var "numerator") (.var "denominator")),
                      .ite (.binary .gt (.var "liquidity") (.intLit 0))
                        [ .internalCall "_mint" [.var "feeTo", .var "liquidity"] "_feeMint" ]
                        [] ]
                    [] ]
                [] ]
            [ .ite (.binary .ne (.var "_kLast") (.intLit 0))
                [ .assign .storage kLastRef (.intLit 0) ]
                [] ])
          (.ok
            (mintFeeAfterKLastFrame reserve0 reserve1 feeTo false (mintFeeKLastWord evmFee))
            (mintFeeKLastClearedState evmFee)) := by
      exact ExecStmt.iteFalse
        (evalExpr_mintFee_afterKLast_feeOn evmFee reserve0 reserve1 feeTo false
          (mintFeeKLastWord evmFee))
        hfalseBranch
    exact ExecBlock.consNormal houter
      (ExecBlock.consReturn
        (ExecStmt.return
          (evalExprs?_singleton
            (evalExpr_mintFee_return_feeOn (mintFeeKLastClearedState evmFee) reserve0 reserve1
              feeTo false (mintFeeKLastWord evmFee)))))
  refine ExecFuncBody.execBlockRet ?_
  simpa [mintFeeFunction, List.append_assoc] using
    Reasoning.Refinement.execBlock_append hchecked htail


end UniswapV2Pair
