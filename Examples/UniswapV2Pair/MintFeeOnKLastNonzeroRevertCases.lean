import Examples.UniswapV2Pair.MintFeeOnKLastNonzeroInitialOverflowCases
import Examples.UniswapV2Pair.MintInternalMintReverts

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

theorem evalExpr_mintFee_numerator_overflow
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int)
    (hroot : rootK > rootKLast) (hrootKNonneg : 0 ≤ rootK)
    (hrootKSize : rootK.toNat < UInt256.size) (hrootKLastNonneg : 0 ≤ rootKLast)
    (hover : UInt256.size ≤ mintFeeNumeratorNat evm rootK rootKLast) :
    evalExpr? config
      (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo feeOn kLast rootK rootKLast) evm
      (u256 (.binary .mul (.storage totalSupplyRef)
        (u256 (.binary .sub (.var "rootK") (.var "rootKLast"))))) = .revert := by
  have hge :
      Int.ofNat ((mintFunctionTotalSupplyWord evm).toNat *
          (mintFeeRootDiffWord rootK rootKLast).toNat) ≥ (2 : Int) ^ 256 := by
    rw [UInt256.size] at hover
    exact Int.ofNat_le.mpr (by simpa [mintFeeNumeratorNat] using hover)
  have hdiffEval :=
    evalExpr_mintFee_rootDiff evm reserve0 reserve1 feeTo feeOn kLast rootK rootKLast
      hroot hrootKNonneg hrootKSize hrootKLastNonneg
  have hdiffEval' :
      evalExpr? config
        (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo feeOn kLast rootK rootKLast) evm
        (.inRange uint256Int (.binary .sub (.var "rootK") (.var "rootKLast"))) =
          .ok (mintFeeRootDiffValue rootK rootKLast) := by
    simpa [u256] using hdiffEval
  simp only [u256, evalExpr?, evalExpr_mintFee_afterRootKLast_totalSupply evm reserve0
    reserve1 feeTo feeOn kLast rootK rootKLast, hdiffEval', EvalResult.bind, bind, pure]
  simp only [evalBinaryOp?, uint256Int]
  rw [if_pos]
  simpa [Bool.or_eq_true, decide_eq_true_eq, ge_iff_le, Nat.cast_mul] using Or.inr hge

theorem evalExpr_mintFee_rootTimesFive_overflow
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int)
    (hrootKNonneg : 0 ≤ rootK)
    (hover : UInt256.size ≤ mintFeeRootTimesFiveNat rootK) :
    evalExpr? config
      (mintFeeAfterNumeratorFrame evm reserve0 reserve1 feeTo feeOn kLast rootK rootKLast) evm
      (u256 (.binary .mul (.var "rootK") (.intLit 5))) = .revert := by
  have hge : rootK * 5 ≥ (2 : Int) ^ 256 := by
    rw [UInt256.size] at hover
    have hcast : Int.ofNat (rootK.toNat * 5) ≥ (2 : Int) ^ 256 :=
      Int.ofNat_le.mpr (by simpa [mintFeeRootTimesFiveNat] using hover)
    simpa [Nat.cast_mul, Int.toNat_of_nonneg hrootKNonneg] using hcast
  simp only [u256, evalExpr?, evalExpr_mintFee_afterNumerator_rootK evm reserve0 reserve1
    feeTo feeOn kLast rootK rootKLast, EvalResult.bind, bind, pure]
  simp only [evalBinaryOp?, uint256Int]
  rw [if_pos]
  simpa [Bool.or_eq_true, decide_eq_true_eq] using Or.inr hge

theorem evalExpr_mintFee_denominator_rootTimesFive_overflow
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int)
    (hrootKNonneg : 0 ≤ rootK)
    (hover : UInt256.size ≤ mintFeeRootTimesFiveNat rootK) :
    evalExpr? config
      (mintFeeAfterNumeratorFrame evm reserve0 reserve1 feeTo feeOn kLast rootK rootKLast) evm
      (u256 (.binary .add (u256 (.binary .mul (.var "rootK") (.intLit 5)))
        (.var "rootKLast"))) = .revert := by
  have hrootFive :=
    evalExpr_mintFee_rootTimesFive_overflow evm reserve0 reserve1 feeTo feeOn kLast
      rootK rootKLast hrootKNonneg hover
  have hrootFive' :
      evalExpr? config
        (mintFeeAfterNumeratorFrame evm reserve0 reserve1 feeTo feeOn kLast rootK rootKLast) evm
        (.inRange uint256Int (.binary .mul (.var "rootK") (.intLit 5))) = .revert := by
    simpa [u256] using hrootFive
  simp only [u256, evalExpr?, hrootFive', EvalResult.bind, bind]

theorem evalExpr_mintFee_denominator_add_overflow
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int)
    (hrootKNonneg : 0 ≤ rootK) (hrootKLastNonneg : 0 ≤ rootKLast)
    (hrootFiveFit : mintFeeRootTimesFiveNat rootK < UInt256.size)
    (hover : UInt256.size ≤ mintFeeDenominatorNat rootK rootKLast) :
    evalExpr? config
      (mintFeeAfterNumeratorFrame evm reserve0 reserve1 feeTo feeOn kLast rootK rootKLast) evm
      (u256 (.binary .add (u256 (.binary .mul (.var "rootK") (.intLit 5)))
        (.var "rootKLast"))) = .revert := by
  have hrootFiveEval :=
    evalExpr_mintFee_rootTimesFive evm reserve0 reserve1 feeTo feeOn kLast rootK rootKLast
      hrootKNonneg hrootFiveFit
  have hrootFiveEval' :
      evalExpr? config
        (mintFeeAfterNumeratorFrame evm reserve0 reserve1 feeTo feeOn kLast rootK rootKLast) evm
        (.inRange uint256Int (.binary .mul (.var "rootK") (.intLit 5))) =
          .ok (mintFeeRootTimesFiveValue rootK) := by
    simpa [u256] using hrootFiveEval
  have hge :
      Int.ofNat (mintFeeRootTimesFiveWord rootK).toNat + rootKLast ≥ (2 : Int) ^ 256 := by
    rw [UInt256.size] at hover
    have hcast :
        Int.ofNat ((mintFeeRootTimesFiveWord rootK).toNat + rootKLast.toNat) ≥
          (2 : Int) ^ 256 := by
      exact Int.ofNat_le.mpr (by simpa [mintFeeDenominatorNat] using hover)
    simpa [Nat.cast_add, Int.toNat_of_nonneg hrootKLastNonneg] using hcast
  simp only [u256, evalExpr?, hrootFiveEval',
    evalExpr_mintFee_afterNumerator_rootKLast evm reserve0 reserve1 feeTo feeOn kLast rootK
      rootKLast, EvalResult.bind, bind, pure]
  simp only [evalBinaryOp?, uint256Int]
  rw [if_pos]
  simpa [Bool.or_eq_true, decide_eq_true_eq] using Or.inr hge

theorem uniswapMintFeePositiveRootBranch_numeratorOverflow
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (kLast : UInt256) (rootK rootKLast : Int)
    (hroot : rootK > rootKLast) (hrootKNonneg : 0 ≤ rootK)
    (hrootKSize : rootK.toNat < UInt256.size) (hrootKLastNonneg : 0 ≤ rootKLast)
    (hover : UInt256.size ≤ mintFeeNumeratorNat evm rootK rootKLast) :
    ExecBlock config
      (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast) evm
      mintFeePositiveRootBranchStmts .reverted := by
  have hnumStmt :
      ExecStmt config
        (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast) evm
        (.letDecl "numerator" (some uint256)
          (u256 (.binary .mul (.storage totalSupplyRef)
            (u256 (.binary .sub (.var "rootK") (.var "rootKLast"))))))
        .reverted :=
    ExecStmt.letDeclRevert
      (evalExpr_mintFee_numerator_overflow evm reserve0 reserve1 feeTo true kLast
        rootK rootKLast hroot hrootKNonneg hrootKSize hrootKLastNonneg hover)
  simpa [mintFeePositiveRootBranchStmts] using ExecBlock.consRevert hnumStmt

theorem uniswapMintFeePositiveRootBranch_rootTimesFiveOverflow
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (kLast : UInt256) (rootK rootKLast : Int)
    (hroot : rootK > rootKLast) (hrootKNonneg : 0 ≤ rootK)
    (hrootKSize : rootK.toNat < UInt256.size) (hrootKLastNonneg : 0 ≤ rootKLast)
    (hnumFit : mintFeeNumeratorNat evm rootK rootKLast < UInt256.size)
    (hover : UInt256.size ≤ mintFeeRootTimesFiveNat rootK) :
    ExecBlock config
      (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast) evm
      mintFeePositiveRootBranchStmts .reverted := by
  have hnumStmt :
      ExecStmt config
        (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast) evm
        (.letDecl "numerator" (some uint256)
          (u256 (.binary .mul (.storage totalSupplyRef)
            (u256 (.binary .sub (.var "rootK") (.var "rootKLast"))))))
        (.ok (mintFeeAfterNumeratorFrame evm reserve0 reserve1 feeTo true kLast rootK rootKLast)
          evm) := by
    simpa [mintFeeAfterNumeratorFrame, mintFeeAfterNumeratorStore] using
      ExecStmt.letDecl
        (evalExpr_mintFee_numerator evm reserve0 reserve1 feeTo true kLast rootK rootKLast
          hroot hrootKNonneg hrootKSize hrootKLastNonneg hnumFit)
  have hdenStmt :
      ExecStmt config
        (mintFeeAfterNumeratorFrame evm reserve0 reserve1 feeTo true kLast rootK rootKLast)
        evm
        (.letDecl "denominator" (some uint256)
          (u256 (.binary .add (u256 (.binary .mul (.var "rootK") (.intLit 5)))
            (.var "rootKLast"))))
        .reverted :=
    ExecStmt.letDeclRevert
      (evalExpr_mintFee_denominator_rootTimesFive_overflow evm reserve0 reserve1 feeTo true
        kLast rootK rootKLast hrootKNonneg hover)
  simpa [mintFeePositiveRootBranchStmts] using
    ExecBlock.consNormal hnumStmt (ExecBlock.consRevert hdenStmt)

theorem uniswapMintFeePositiveRootBranch_denominatorOverflow
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (kLast : UInt256) (rootK rootKLast : Int)
    (hroot : rootK > rootKLast) (hrootKNonneg : 0 ≤ rootK)
    (hrootKSize : rootK.toNat < UInt256.size) (hrootKLastNonneg : 0 ≤ rootKLast)
    (hnumFit : mintFeeNumeratorNat evm rootK rootKLast < UInt256.size)
    (hrootFiveFit : mintFeeRootTimesFiveNat rootK < UInt256.size)
    (hover : UInt256.size ≤ mintFeeDenominatorNat rootK rootKLast) :
    ExecBlock config
      (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast) evm
      mintFeePositiveRootBranchStmts .reverted := by
  have hnumStmt :
      ExecStmt config
        (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast) evm
        (.letDecl "numerator" (some uint256)
          (u256 (.binary .mul (.storage totalSupplyRef)
            (u256 (.binary .sub (.var "rootK") (.var "rootKLast"))))))
        (.ok (mintFeeAfterNumeratorFrame evm reserve0 reserve1 feeTo true kLast rootK rootKLast)
          evm) := by
    simpa [mintFeeAfterNumeratorFrame, mintFeeAfterNumeratorStore] using
      ExecStmt.letDecl
        (evalExpr_mintFee_numerator evm reserve0 reserve1 feeTo true kLast rootK rootKLast
          hroot hrootKNonneg hrootKSize hrootKLastNonneg hnumFit)
  have hdenStmt :
      ExecStmt config
        (mintFeeAfterNumeratorFrame evm reserve0 reserve1 feeTo true kLast rootK rootKLast)
        evm
        (.letDecl "denominator" (some uint256)
          (u256 (.binary .add (u256 (.binary .mul (.var "rootK") (.intLit 5)))
            (.var "rootKLast"))))
        .reverted :=
    ExecStmt.letDeclRevert
      (evalExpr_mintFee_denominator_add_overflow evm reserve0 reserve1 feeTo true kLast
        rootK rootKLast hrootKNonneg hrootKLastNonneg hrootFiveFit hover)
  simpa [mintFeePositiveRootBranchStmts] using
    ExecBlock.consNormal hnumStmt (ExecBlock.consRevert hdenStmt)

theorem uniswapMintFeeAfterRoots_positiveNumeratorOverflow
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (kLast : UInt256) (rootK rootKLast : Int)
    (hroot : rootK > rootKLast) (hrootKNonneg : 0 ≤ rootK)
    (hrootKSize : rootK.toNat < UInt256.size) (hrootKLastNonneg : 0 ≤ rootKLast)
    (hover : UInt256.size ≤ mintFeeNumeratorNat evm rootK rootKLast) :
    ExecBlock config
      (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast) evm
      [mintFeeRootComparisonStmt] .reverted := by
  exact ExecBlock.consRevert
    (ExecStmt.iteTrue
      (evalExpr_mintFee_rootK_gt_rootKLast_true evm reserve0 reserve1 feeTo true kLast
        rootK rootKLast hroot)
      (uniswapMintFeePositiveRootBranch_numeratorOverflow evm reserve0 reserve1 feeTo
        kLast rootK rootKLast hroot hrootKNonneg hrootKSize hrootKLastNonneg hover))

theorem uniswapMintFeeAfterRoots_positiveRootTimesFiveOverflow
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (kLast : UInt256) (rootK rootKLast : Int)
    (hroot : rootK > rootKLast) (hrootKNonneg : 0 ≤ rootK)
    (hrootKSize : rootK.toNat < UInt256.size) (hrootKLastNonneg : 0 ≤ rootKLast)
    (hnumFit : mintFeeNumeratorNat evm rootK rootKLast < UInt256.size)
    (hover : UInt256.size ≤ mintFeeRootTimesFiveNat rootK) :
    ExecBlock config
      (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast) evm
      [mintFeeRootComparisonStmt] .reverted := by
  exact ExecBlock.consRevert
    (ExecStmt.iteTrue
      (evalExpr_mintFee_rootK_gt_rootKLast_true evm reserve0 reserve1 feeTo true kLast
        rootK rootKLast hroot)
      (uniswapMintFeePositiveRootBranch_rootTimesFiveOverflow evm reserve0 reserve1 feeTo
        kLast rootK rootKLast hroot hrootKNonneg hrootKSize hrootKLastNonneg hnumFit hover))

theorem uniswapMintFeeAfterRoots_positiveDenominatorOverflow
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (kLast : UInt256) (rootK rootKLast : Int)
    (hroot : rootK > rootKLast) (hrootKNonneg : 0 ≤ rootK)
    (hrootKSize : rootK.toNat < UInt256.size) (hrootKLastNonneg : 0 ≤ rootKLast)
    (hnumFit : mintFeeNumeratorNat evm rootK rootKLast < UInt256.size)
    (hrootFiveFit : mintFeeRootTimesFiveNat rootK < UInt256.size)
    (hover : UInt256.size ≤ mintFeeDenominatorNat rootK rootKLast) :
    ExecBlock config
      (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast) evm
      [mintFeeRootComparisonStmt] .reverted := by
  exact ExecBlock.consRevert
    (ExecStmt.iteTrue
      (evalExpr_mintFee_rootK_gt_rootKLast_true evm reserve0 reserve1 feeTo true kLast
        rootK rootKLast hroot)
      (uniswapMintFeePositiveRootBranch_denominatorOverflow evm reserve0 reserve1 feeTo
        kLast rootK rootKLast hroot hrootKNonneg hrootKSize hrootKLastNonneg hnumFit
        hrootFiveFit hover))

theorem uniswapMintFeeFunctionBody_feeOn_kLastNonzero_fromRootBlockRevert
    (evm evmFee : EVM.State) (reserve0 reserve1 : UInt256) {out : ByteArray}
    (feeTo : AccountAddress)
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
          mintFeeRootComparisonStmt ]
        .reverted) :
    ExecFuncBody config (mintFeeCallFrame reserve0 reserve1) evm mintFeeFunction.body
      .reverted := by
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
                  mintFeeRootComparisonStmt ]
                [] ]
            [ .ite (.binary .ne (.var "_kLast") (.intLit 0))
                [ .assign .storage kLastRef (.intLit 0) ]
                [] ],
          .return [(.var "feeOn")] ]
        .reverted := by
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
                mintFeeRootComparisonStmt ]
              [] ]
          .reverted :=
      ExecBlock.consRevert
        (ExecStmt.iteTrue
          (evalExpr_mintFee_afterKLast_kLast_ne_zero_true evmFee reserve0 reserve1 feeTo
            true (mintFeeKLastWord evmFee) hkLast)
          hrootBlock)
    have houter :
        ExecStmt config
          (mintFeeAfterKLastFrame reserve0 reserve1 feeTo true (mintFeeKLastWord evmFee))
          evmFee
          (.ite (.var "feeOn")
            [ .ite (.binary .ne (.var "_kLast") (.intLit 0))
                [ .internalCall "sqrt"
                    [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))] "rootK",
                  .internalCall "sqrt" [.var "_kLast"] "rootKLast",
                  mintFeeRootComparisonStmt ]
                [] ]
            [ .ite (.binary .ne (.var "_kLast") (.intLit 0))
                [ .assign .storage kLastRef (.intLit 0) ]
                [] ])
          .reverted :=
      ExecStmt.iteTrue
        (evalExpr_mintFee_afterKLast_feeOn evmFee reserve0 reserve1 feeTo true
          (mintFeeKLastWord evmFee))
        htrueBranch
    exact ExecBlock.consRevert houter
  refine ExecFuncBody.execBlockRevert ?_
  simpa [mintFeeFunction, mintFeeRootComparisonStmt, mintFeePositiveRootBranchStmts,
    List.append_assoc] using
    Reasoning.Refinement.execBlock_append hchecked htail

theorem uniswapMintFeeCallFromMint_feeOn_kLastNonzero_fromRootBlockRevert
    (reserveEvm callEvm evmFee : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) {out : ByteArray} (feeTo : AccountAddress)
    (hguard :
      evalExpr? config
        (mintFeeCallFrame (uniswapReserve0Word reserveEvm) (uniswapReserve1Word reserveEvm))
        callEvm (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
          .ok (.bool true))
    (hcall : typedCallViaEVM config callEvm (EVM.address (uniswapAddressAtSlot callEvm ⟨5⟩))
      "feeTo" 0 [] (true, evmFee, out) false)
    (hdec : config.externalABI.decode? "feeTo" out = some [.address feeTo])
    (hfeeTo : feeTo ≠ AccountAddress.ofNat 0)
    (hkLast : (mintFeeKLastWord evmFee).toNat ≠ 0)
    (hrootBlock :
      ExecBlock config
        (mintFeeAfterKLastFrame (uniswapReserve0Word reserveEvm)
          (uniswapReserve1Word reserveEvm) feeTo true (mintFeeKLastWord evmFee))
        evmFee
        [ .internalCall "sqrt" [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))]
            "rootK",
          .internalCall "sqrt" [.var "_kLast"] "rootKLast",
          mintFeeRootComparisonStmt ]
        .reverted) :
    ExecStmt config
      { contract := contract, locals := mintAmountStore reserveEvm I balance0 balance1 }
      callEvm
      (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
      .reverted := by
  let reserve0 := uniswapReserve0Word reserveEvm
  let reserve1 := uniswapReserve1Word reserveEvm
  exact internalCallFunctionRevert
    (cfg := config)
    (caller := { contract := contract, locals := mintAmountStore reserveEvm I balance0 balance1 })
    (evm := callEvm)
    (name := "_mintFee") (retVar := "feeOn")
    (args := [.var "_reserve0", .var "_reserve1"])
    (argVals := [mintFeeReserve0Value reserve0, mintFeeReserve1Value reserve1])
    (callee := mintFeeFunction)
    (locals := mintFeeCallStore reserve0 reserve1)
    (by simpa [reserve0, reserve1] using
      evalExprs_mint_mintFeeArgs reserveEvm callEvm I balance0 balance1)
    (by simpa using uniswapLookupMintFeeFunction)
    (by simpa [reserve0, reserve1] using bindParams_mintFeeFunction_call reserve0 reserve1)
    (by
      simpa [reserve0, reserve1] using
        uniswapMintFeeFunctionBody_feeOn_kLastNonzero_fromRootBlockRevert callEvm evmFee
          reserve0 reserve1 feeTo hguard hcall hdec hfeeTo hkLast hrootBlock)

theorem uniswapMintAfterMintFeeReverts_of_call
    (evm evm0 evm1 : EVM.State) (I : ExecutionEnv)
    {out0 out1 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract, locals := mintReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals := (mintReserveStore (uniswapLockEnteredState evm) I).insert "balance0"
            (uniswapUint256Value balance0) } evm0
        (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool true))
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 :
      config.externalABI.decode? "balanceOf" out0 = some [uniswapUint256Value balance0])
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some [uniswapUint256Value balance1])
    (henough0 : (uniswapReserve0Word (uniswapLockEnteredState evm)).toNat ≤ balance0.toNat)
    (henough1 : (uniswapReserve1Word (uniswapLockEnteredState evm)).toNat ≤ balance1.toNat)
    (hfee :
      ExecStmt config
        { contract := contract,
          locals := mintAmountStore (uniswapLockEnteredState evm) I balance0 balance1 }
        evm1 (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
        .reverted) :
    ExecBlock config { contract := contract, locals := mintStore I } evm mintTransition.body
      .reverted := by
  let evmL := uniswapLockEnteredState evm
  have hprefix :=
    uniswapMintAmountsPrefix evm evm0 evm1 I hwv hunlocked hguard0 hguard1 hcall0 hdec0
      hcall1 hdec1 henough0 henough1
  have hfeeBlock :
      ExecBlock config
        { contract := contract, locals := mintAmountStore evmL I balance0 balance1 } evm1
        [ .internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn" ]
        .reverted := by
    exact ExecBlock.consRevert (by simpa [evmL] using hfee)
  have hprefixRevert :
      ExecBlock config { contract := contract, locals := mintStore I } evm
        (lockEnter ++
          [ .letDecl "_reserve0" (some uint112) (.storage reserve0Ref),
            .letDecl "_reserve1" (some uint112) (.storage reserve1Ref) ] ++
          pairBalanceOfThisStmts "balance0" "balance1" ++
          [ .letDecl "amount0" (some uint256)
              (u256 (.binary .sub (.var "balance0") (.var "_reserve0"))),
            .letDecl "amount1" (some uint256)
              (u256 (.binary .sub (.var "balance1") (.var "_reserve1"))),
            .internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn" ])
        .reverted := by
    simpa [evmL, List.append_assoc] using execBlock_append hprefix hfeeBlock
  simpa [mintTransition, mintLiquidityBranchStmt, mintInitialLiquidityBranchStmts,
    mintProportionalLiquidityBranchStmts, mintAfterLiquidityTailStmts, List.append_assoc] using
    (Reasoning.Refinement.execBlock_append_term
      (s2 :=
        [ .letDecl "_totalSupply" (some uint256) (.storage totalSupplyRef),
          mintLiquidityBranchStmt ] ++ mintAfterLiquidityTailStmts)
      hprefixRevert
      (by intro f e h; cases h))

set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeRuntimePositiveNumeratorOverflowReverts
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {evmFeeS : EVM.State}
    {mem rdata : ByteArray} {k C : ℕ}
    {rootK rootKLast : Int}
    {kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd7899 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7899⟩
      [UInt256.ofNat rootKLast.toNat, ⟨0⟩, UInt256.ofNat rootK.toNat, kLast, feeTo,
        ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1,
        balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = uniswapSlotWord ⟨0⟩ σFee I)
    (hroot : rootK > rootKLast) (hrootKNonneg : 0 ≤ rootK)
    (hrootKSize : rootK.toNat < UInt256.size) (hrootKLastNonneg : 0 ≤ rootKLast)
    (hover : UInt256.size ≤ mintFeeNumeratorNat evmFeeS rootK rootKLast)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  have hrootGt :=
    mintFeeRuntimeRootGt_of_int_gt rootK rootKLast hroot hrootKSize hrootKLastNonneg
  obtain ⟨_, _, rd6879⟩ :=
    uniswapMintFeeRuntimeAfterRootsPositiveSubEntry rd7899 hrootGt
  obtain ⟨_, _, rd6780⟩ :=
    uniswapMintFeeRuntimeAfterRootsPositiveSupplyMulEntry rd6879 hrootGt
  have hoverRuntime :
      UInt256.size ≤
        (uniswapSlotWord ⟨0⟩ σFee I).toNat *
          (UInt256.sub (UInt256.ofNat rootK.toNat) (UInt256.ofNat rootKLast.toNat)).toNat := by
    rw [← htotalEq]
    have hdiff :=
      congrArg UInt256.toNat
        (mintFeeRootDiffWord_eq_sub rootK rootKLast hroot hrootKNonneg hrootKSize
          hrootKLastNonneg)
    rw [← hdiff]
    simpa [mintFeeNumeratorNat] using hover
  exact RD.uniswapSafeMathMulOverflow_feeToStaticcall_size164
    (a := uniswapSlotWord ⟨0⟩ σFee I)
    (b := UInt256.sub (UInt256.ofNat rootK.toNat) (UInt256.ofNat rootKLast.toNat))
    rd6780 hoverRuntime hmem hread64
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeRuntimePositiveRootTimesFiveOverflowReverts
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {evmFeeS : EVM.State}
    {mem rdata : ByteArray} {k C : ℕ}
    {rootK rootKLast : Int}
    {kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd7899 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7899⟩
      [UInt256.ofNat rootKLast.toNat, ⟨0⟩, UInt256.ofNat rootK.toNat, kLast, feeTo,
        ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1,
        balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = uniswapSlotWord ⟨0⟩ σFee I)
    (hroot : rootK > rootKLast) (hrootKNonneg : 0 ≤ rootK)
    (hrootKSize : rootK.toNat < UInt256.size) (hrootKLastNonneg : 0 ≤ rootKLast)
    (hnumFit : mintFeeNumeratorNat evmFeeS rootK rootKLast < UInt256.size)
    (hover : UInt256.size ≤ mintFeeRootTimesFiveNat rootK)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  have hrootGt :=
    mintFeeRuntimeRootGt_of_int_gt rootK rootKLast hroot hrootKSize hrootKLastNonneg
  obtain ⟨_, _, rd6879⟩ :=
    uniswapMintFeeRuntimeAfterRootsPositiveSubEntry rd7899 hrootGt
  obtain ⟨_, _, rd6780Num⟩ :=
    uniswapMintFeeRuntimeAfterRootsPositiveSupplyMulEntry rd6879 hrootGt
  have hnumFitRuntime :
      (uniswapSlotWord ⟨0⟩ σFee I).toNat *
          (UInt256.sub (UInt256.ofNat rootK.toNat) (UInt256.ofNat rootKLast.toNat)).toNat <
        UInt256.size := by
    rw [← htotalEq]
    exact mintFeeRuntimeNumeratorFit evmFeeS rootK rootKLast hroot hrootKNonneg
      hrootKSize hrootKLastNonneg hnumFit
  obtain ⟨_, _, rd7945⟩ :=
    uniswapMintFeeRuntimePositiveNumeratorEntry rd6780Num hnumFitRuntime
  obtain ⟨_, _, rd6780Den⟩ :=
    uniswapMintFeeRuntimePositiveDenominatorMulEntry rd7945
  have hoverRuntime : UInt256.size ≤ (UInt256.ofNat rootK.toNat).toNat * 5 := by
    rw [ulit_toNat' _ hrootKSize]
    simpa [mintFeeRootTimesFiveNat] using hover
  exact RD.uniswapSafeMathMulOverflow_feeToStaticcall_size164
    (a := UInt256.ofNat rootK.toNat) (b := (⟨5⟩ : UInt256)) rd6780Den
    hoverRuntime hmem hread64
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeRuntimePositiveDenominatorOverflowReverts
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {evmFeeS : EVM.State}
    {mem rdata : ByteArray} {k C : ℕ}
    {rootK rootKLast : Int}
    {kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd7899 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7899⟩
      [UInt256.ofNat rootKLast.toNat, ⟨0⟩, UInt256.ofNat rootK.toNat, kLast, feeTo,
        ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1,
        balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = uniswapSlotWord ⟨0⟩ σFee I)
    (hroot : rootK > rootKLast) (hrootKNonneg : 0 ≤ rootK)
    (hrootKSize : rootK.toNat < UInt256.size) (hrootKLastNonneg : 0 ≤ rootKLast)
    (hrootKLastSize : rootKLast.toNat < UInt256.size)
    (hnumFit : mintFeeNumeratorNat evmFeeS rootK rootKLast < UInt256.size)
    (hrootFiveFit : mintFeeRootTimesFiveNat rootK < UInt256.size)
    (hover : UInt256.size ≤ mintFeeDenominatorNat rootK rootKLast)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  have hrootGt :=
    mintFeeRuntimeRootGt_of_int_gt rootK rootKLast hroot hrootKSize hrootKLastNonneg
  obtain ⟨_, _, rd6879⟩ :=
    uniswapMintFeeRuntimeAfterRootsPositiveSubEntry rd7899 hrootGt
  obtain ⟨_, _, rd6780Num⟩ :=
    uniswapMintFeeRuntimeAfterRootsPositiveSupplyMulEntry rd6879 hrootGt
  have hnumFitRuntime :
      (uniswapSlotWord ⟨0⟩ σFee I).toNat *
          (UInt256.sub (UInt256.ofNat rootK.toNat) (UInt256.ofNat rootKLast.toNat)).toNat <
        UInt256.size := by
    rw [← htotalEq]
    exact mintFeeRuntimeNumeratorFit evmFeeS rootK rootKLast hroot hrootKNonneg
      hrootKSize hrootKLastNonneg hnumFit
  obtain ⟨_, _, rd7945⟩ :=
    uniswapMintFeeRuntimePositiveNumeratorEntry rd6780Num hnumFitRuntime
  obtain ⟨_, _, rd6780Den⟩ :=
    uniswapMintFeeRuntimePositiveDenominatorMulEntry rd7945
  have hrootFiveFitRuntime := mintFeeRuntimeRootTimesFiveFit rootK hrootFiveFit
  obtain ⟨_, _, rd7970⟩ :=
    uniswapMintFeeRuntimePositiveDenominatorProductEntry rd6780Den hrootFiveFitRuntime
  obtain ⟨_, _, rd8515⟩ :=
    uniswapMintFeeRuntimePositiveDenominatorAddEntry rd7970
  have hoverRuntime :
      UInt256.size ≤
        (UInt256.mul (UInt256.ofNat rootK.toNat) (⟨5⟩ : UInt256)).toNat +
          (UInt256.ofNat rootKLast.toNat).toNat := by
    have hrootMul :=
      congrArg UInt256.toNat (mintFeeRootTimesFiveWord_eq_mul rootK hrootFiveFit)
    rw [← hrootMul, ulit_toNat' _ hrootKLastSize]
    simpa [mintFeeDenominatorNat] using hover
  exact RD.uniswapSafeMathAddOverflow_feeToStaticcall_size164
    (a := UInt256.mul (UInt256.ofNat rootK.toNat) (⟨5⟩ : UInt256))
    (b := UInt256.ofNat rootKLast.toNat) rd8515 hoverRuntime hmem hread64
    (by simp only [List.length_cons, List.length_nil]; omega)

def mintFeeOnKLastNonzeroRootArithmeticOverflowFromFactoryCaseData
    (feeToWord : UInt256) (σFee : AccountMap) (evmFeeS : EVM.State)
    (I : ExecutionEnv) : Prop :=
  UInt256.land feeToWord solcAddrMask ≠ ⟨0⟩ ∧
    mintFeeKLastSlotWord σFee I ≠ ⟨0⟩ ∧
    ∀ rootK rootKLast : Int,
      0 ≤ rootK → rootK.toNat < UInt256.size →
      0 ≤ rootKLast → rootKLast.toNat < UInt256.size →
      rootK > rootKLast ∧
        (UInt256.size ≤ mintFeeNumeratorNat evmFeeS rootK rootKLast ∨
          mintFeeNumeratorNat evmFeeS rootK rootKLast < UInt256.size ∧
            UInt256.size ≤ mintFeeRootTimesFiveNat rootK ∨
          mintFeeNumeratorNat evmFeeS rootK rootKLast < UInt256.size ∧
            mintFeeRootTimesFiveNat rootK < UInt256.size ∧
            UInt256.size ≤ mintFeeDenominatorNat rootK rootKLast)

set_option maxHeartbeats 3000000 in
theorem uniswapMintFeeOnKLastNonzeroRootArithmeticOverflowFromFactoryCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σ'' : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {outFee o o1 memFee : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel feeToWord : UInt256}
    {zFee : Bool}
    (feeTo : AccountAddress)
    (hcode : I.code = uniswapV2PairBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some mintTransition)
    (hsz36 : 36 ≤ I.calldata.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hunlockedSolm :
      Solm.EVM.storageLoad
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨12⟩ =
        ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract,
          locals :=
            mintReserveStore
              (uniswapLockEnteredState
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) I }
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) =
          .ok (.bool true))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals :=
            (mintReserveStore
              (uniswapLockEnteredState
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) I).insert
              "balance0" (uniswapUint256Value balance0) }
        evm0S (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) =
          .ok (.bool true))
    (hcall0 :
      typedCallViaEVM config
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
        (EVM.address
          (uniswapAddressAtSlot
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) ⟨6⟩))
        "balanceOf" 0
        [.address
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)).executionEnv.codeOwner]
        (true, evm0S, o) false)
    (hdec0 : config.externalABI.decode? "balanceOf" o = some [uniswapUint256Value balance0])
    (hcall1 :
      typedCallViaEVM config evm0S (EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩))
        "balanceOf" 0 [.address evm0S.executionEnv.codeOwner] (true, evm1S, o1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" o1 = some [uniswapUint256Value balance1])
    (hle0Source :
      (uniswapReserve0Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).toNat ≤
        balance0.toNat)
    (hle1Source :
      (uniswapReserve1Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).toNat ≤
        balance1.toNat)
    (hfeeGuard :
      evalExpr? config
        (mintFeeCallFrame
          (uniswapReserve0Word
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
          (uniswapReserve1Word
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))))
        evm1S (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
          .ok (.bool true))
    (hfeeCall :
      typedCallViaEVM config evm1S (EVM.address (uniswapAddressAtSlot evm1S ⟨5⟩))
        "feeTo" 0 [] (true, evmFeeS, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some [.address feeTo])
    (hreserve0Eq :
      uniswapReserve0Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) =
        reserve0)
    (hreserve1Eq :
      uniswapReserve1Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) =
        reserve1)
    (hruntimeReserve0 :
      reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I = reserve0)
    (hruntimeReserve1 :
      reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I = reserve1)
    (hkLastEq : mintFeeKLastWord evmFeeS = mintFeeKLastSlotWord σFee I)
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = uniswapSlotWord ⟨0⟩ σFee I)
    (rd7781 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨7781⟩
      [(if zFee then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨132⟩,
        feeToSelectorWord, mintFeeFactoryWord σ'' I, ⟨0⟩, ⟨0⟩,
        reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I,
        ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      memFee feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (ho132 : 32 ≤ o1.size) (ho1Size : o1.size < UInt256.size)
    (houtFeeSize : outFee.size < UInt256.size)
    (hzFeeTrue : zFee = true)
    (houtFee32 : 32 ≤ outFee.size)
    (hfeeToWord : feeToWord = UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (hfeeTo : feeTo = AccountAddress.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (hmemFee :
      memFee =
        feeToStaticcallMem
          (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
          outFee)
    (hcase :
      mintFeeOnKLastNonzeroRootArithmeticOverflowFromFactoryCaseData feeToWord σFee
        evmFeeS I) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  rcases hcase with ⟨hfeeToNonzero, hkLastNonzero, hrootCase⟩
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmL := uniswapLockEnteredState evmS
  have hfeeToAddr : feeTo ≠ AccountAddress.ofNat 0 := by
    rw [hfeeTo]
    exact accountAddress_ofNat_ne_zero_of_land_solcAddrMask_ne_zero
      (fromByteArrayBigEndian_extract0_32_lt houtFee32)
      (by simpa [hfeeToWord] using hfeeToNonzero)
  have hkLastSource : (mintFeeKLastWord evmFeeS).toNat ≠ 0 := by
    intro hzero
    apply hkLastNonzero
    rw [← hkLastEq]
    exact uint256_toNat_eq_zero hzero
  have hclean0 : UInt256.land reserve0 reserve112Mask = reserve0 := by
    rw [← hruntimeReserve0]
    exact reserve112Mask_clean_of_lt _ (reserve112Word_lt _)
  have hclean1 : UInt256.land reserve1 reserve112Mask = reserve1 := by
    rw [← hruntimeReserve1]
    exact reserve112Mask_clean_of_lt _ (reserve112Word_lt _)
  obtain ⟨rootK, rootKLast, _k7899, _C7899, hprefix, hrootKNonneg, hrootKSize,
      hrootKLastNonneg, hrootKLastSize, rd7899⟩ :=
    uniswapMintFeeOnKLastNonzeroFactoryRoots feeTo rd7781 ho32 hoSize ho132 ho1Size
      houtFeeSize hzFeeTrue houtFee32 hfeeToWord hmemFee hruntimeReserve0 hruntimeReserve1
      hfeeToNonzero hkLastNonzero hclean0 hclean1
  rcases hrootCase rootK rootKLast hrootKNonneg hrootKSize hrootKLastNonneg
      hrootKLastSize with
    ⟨hroot, hoverflow⟩
  have hmem : memFee.size = 164 := by
    rw [hmemFee]
    exact feeToStaticcallMem_size_of_size_ge (UInt256.ofNat I.codeOwner.val) o o1 outFee
      ho32 hoSize ho132 ho1Size houtFee32 houtFeeSize
  have hmem64 :
      memFee.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    rw [hmemFee]
    exact feeToStaticcallMem_read64_of_size_ge (UInt256.ofNat I.codeOwner.val) o o1 outFee
      ho32 hoSize ho132 ho1Size houtFee32 houtFeeSize
  have finish
      (htail :
        ExecBlock config
          (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true
            (mintFeeKLastSlotWord σFee I) rootK rootKLast)
          evmFeeS [mintFeeRootComparisonStmt] .reverted)
      (rdRev :
        RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)) :
      runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
    have hrootBlock :
        ExecBlock config
          (mintFeeAfterKLastFrame reserve0 reserve1 feeTo true (mintFeeKLastSlotWord σFee I))
          evmFeeS
          [ .internalCall "sqrt" [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))]
              "rootK",
            .internalCall "sqrt" [.var "_kLast"] "rootKLast",
            mintFeeRootComparisonStmt ]
          .reverted := by
      simpa [List.append_assoc] using execBlock_append hprefix htail
    have hfeeRevert :
        ExecStmt config { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
          evm1S (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
          .reverted := by
      exact
        uniswapMintFeeCallFromMint_feeOn_kLastNonzero_fromRootBlockRevert evmL evm1S
          evmFeeS I balance0 balance1 feeTo hfeeGuard hfeeCall hfeeDec hfeeToAddr
          hkLastSource
          (by simpa [evmL, evmS, hreserve0Eq, hreserve1Eq, hkLastEq] using hrootBlock)
    have hbody :
        ExecTransitionBody config contract evmS (mintStore I) mintTransition.body .reverted :=
      ExecFuncBody.execBlockRevert
        (uniswapMintAfterMintFeeReverts_of_call evmS evm0S evm1S I
          (by simp [evmS, initState]; exact hwv) hunlockedSolm hguard0 hguard1 hcall0
          hdec0 hcall1 hdec1 hle0Source hle1Source hfeeRevert)
    exact rdRev.reEquivExecutionRevert hcode hdispatch (uniswapDecode_mint_ok hsz36) hbody
  rcases hoverflow with hnumOverflow | hrest
  · have htail :=
      uniswapMintFeeAfterRoots_positiveNumeratorOverflow evmFeeS reserve0 reserve1 feeTo
        (mintFeeKLastSlotWord σFee I) rootK rootKLast hroot hrootKNonneg hrootKSize
        hrootKLastNonneg hnumOverflow
    have rdRev :=
      uniswapMintFeeRuntimePositiveNumeratorOverflowReverts rd7899 htotalEq hroot
        hrootKNonneg hrootKSize hrootKLastNonneg hnumOverflow hmem hmem64
    exact finish htail rdRev
  rcases hrest with hrootFiveOverflow | hdenOverflow
  · rcases hrootFiveOverflow with ⟨hnumFit, hrootFiveOverflow⟩
    have htail :=
      uniswapMintFeeAfterRoots_positiveRootTimesFiveOverflow evmFeeS reserve0 reserve1 feeTo
        (mintFeeKLastSlotWord σFee I) rootK rootKLast hroot hrootKNonneg hrootKSize
        hrootKLastNonneg hnumFit hrootFiveOverflow
    have rdRev :=
      uniswapMintFeeRuntimePositiveRootTimesFiveOverflowReverts rd7899 htotalEq hroot
        hrootKNonneg hrootKSize hrootKLastNonneg hnumFit hrootFiveOverflow hmem hmem64
    exact finish htail rdRev
  · rcases hdenOverflow with ⟨hnumFit, hrootFiveFit, hdenOverflow⟩
    have htail :=
      uniswapMintFeeAfterRoots_positiveDenominatorOverflow evmFeeS reserve0 reserve1 feeTo
        (mintFeeKLastSlotWord σFee I) rootK rootKLast hroot hrootKNonneg hrootKSize
        hrootKLastNonneg hnumFit hrootFiveFit hdenOverflow
    have rdRev :=
      uniswapMintFeeRuntimePositiveDenominatorOverflowReverts rd7899 htotalEq hroot
        hrootKNonneg hrootKSize hrootKLastNonneg hrootKLastSize hnumFit hrootFiveFit
        hdenOverflow hmem hmem64
    exact finish htail rdRev

end UniswapV2Pair
