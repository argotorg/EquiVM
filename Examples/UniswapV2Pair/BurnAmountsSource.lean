import Examples.UniswapV2Pair.BurnAmountsRuntime
import Examples.UniswapV2Pair.MintProportionalProductOverflow

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

abbrev burnAmountWord (liquidity balance totalSupply : UInt256) : UInt256 :=
  mintProportionalLiquidityWord liquidity balance totalSupply

theorem evalExpr_burn_amount_of_get
    {locals : Store} (evm : EVM.State) (balanceName : Ident) (liquidity balance totalSupply : UInt256)
    (hliq : locals.get? "liquidity" = some (uniswapUint256Value liquidity))
    (hbalance : locals.get? balanceName = some (uniswapUint256Value balance))
    (htotal : locals.get? "_totalSupply" = some (uniswapUint256Value totalSupply))
    (hfit : mintAmountProductNat liquidity balance < UInt256.size)
    (hnonzero : totalSupply ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .div (u256 (.binary .mul (.var "liquidity") (.var balanceName)))
        (.var "_totalSupply")) =
      .ok (uniswapUint256Value (burnAmountWord liquidity balance totalSupply)) := by
  have hmul := evalExpr_mint_namedProduct_of_get evm "liquidity" balanceName
    liquidity balance hliq hbalance hfit
  have hnonzeroNat : totalSupply.toNat ≠ 0 := fun hz => hnonzero (uint256_toNat_eq_zero hz)
  simp only [evalExpr?, hmul, EvalResult.ofOption, htotal, EvalResult.bind, bind]
  simp [evalBinaryOp?, burnAmountWord, mintProportionalLiquidityWord, mintAmountProductValue,
    uniswapUint256Value, uint256Value, hnonzeroNat, udiv_toNat]

theorem evalExpr_burn_amount_divZero
    {locals : Store} (evm : EVM.State) (balanceName : Ident) (liquidity balance : UInt256)
    (hliq : locals.get? "liquidity" = some (uniswapUint256Value liquidity))
    (hbalance : locals.get? balanceName = some (uniswapUint256Value balance))
    (htotal : locals.get? "_totalSupply" = some (.int 0))
    (hfit : mintAmountProductNat liquidity balance < UInt256.size) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .div (u256 (.binary .mul (.var "liquidity") (.var balanceName)))
        (.var "_totalSupply")) = .revert := by
  have hmul := evalExpr_mint_namedProduct_of_get evm "liquidity" balanceName
    liquidity balance hliq hbalance hfit
  simp only [evalExpr?, hmul, EvalResult.ofOption, htotal, EvalResult.bind, bind,
    mintAmountProductValue, uniswapUint256Value, uint256Value, evalBinaryOp?, ite_true]

theorem evalExpr_burn_amount_productOverflow
    {locals : Store} (evm : EVM.State) (balanceName : Ident) (liquidity balance : UInt256)
    (hliq : locals.get? "liquidity" = some (uniswapUint256Value liquidity))
    (hbalance : locals.get? balanceName = some (uniswapUint256Value balance))
    (hover : UInt256.size ≤ liquidity.toNat * balance.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .div (u256 (.binary .mul (.var "liquidity") (.var balanceName)))
        (.var "_totalSupply")) = .revert := by
  have hmul := evalExpr_mint_namedProduct_overflow evm "liquidity" balanceName
    liquidity balance hliq hbalance hover
  simp only [evalExpr?, hmul, EvalResult.bind, bind]

abbrev burnAmount0Stmt : Stmt :=
  .letDecl "amount0" (some uint256)
    (.binary .div (u256 (.binary .mul (.var "liquidity") (.var "balance0"))) (.var "_totalSupply"))

abbrev burnAmount1Stmt : Stmt :=
  .letDecl "amount1" (some uint256)
    (.binary .div (u256 (.binary .mul (.var "liquidity") (.var "balance1"))) (.var "_totalSupply"))

abbrev burnAmountsStore (locals : Store) (liquidity balance0 balance1 totalSupply : UInt256) : Store :=
  ((locals.insert "amount0" (uniswapUint256Value (burnAmountWord liquidity balance0 totalSupply))).insert
    "amount1" (uniswapUint256Value (burnAmountWord liquidity balance1 totalSupply)))

theorem uniswapBurnAmountsSourceSuccess
    {locals : Store} (evm : EVM.State) (liquidity balance0 balance1 totalSupply : UInt256)
    (hliq : locals.get? "liquidity" = some (uniswapUint256Value liquidity))
    (hb0 : locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hb1 : locals.get? "balance1" = some (uniswapUint256Value balance1))
    (htotal : locals.get? "_totalSupply" = some (uniswapUint256Value totalSupply))
    (hfit0 : mintAmountProductNat liquidity balance0 < UInt256.size)
    (hfit1 : mintAmountProductNat liquidity balance1 < UInt256.size)
    (hnonzero : totalSupply ≠ ⟨0⟩) :
    ExecBlock config { contract := contract, locals := locals } evm
      [burnAmount0Stmt, burnAmount1Stmt]
      (.ok { contract := contract, locals := burnAmountsStore locals liquidity balance0 balance1 totalSupply } evm) := by
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_burn_amount_of_get evm "balance0" liquidity balance0 totalSupply
      hliq hb0 htotal hfit0 hnonzero)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_burn_amount_of_get evm "balance1" liquidity balance1 totalSupply
      (by rw [store_get_ne _ _ (by decide), hliq])
      (by rw [store_get_ne _ _ (by decide), hb1])
      (by rw [store_get_ne _ _ (by decide), htotal]) hfit1 hnonzero)) ExecBlock.nil

theorem uniswapBurnAmountsSourceRevert_product1
    {locals : Store} (evm : EVM.State) (liquidity balance0 balance1 totalSupply : UInt256)
    (hliq : locals.get? "liquidity" = some (uniswapUint256Value liquidity))
    (hb0 : locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hb1 : locals.get? "balance1" = some (uniswapUint256Value balance1))
    (htotal : locals.get? "_totalSupply" = some (uniswapUint256Value totalSupply))
    (hfit0 : mintAmountProductNat liquidity balance0 < UInt256.size)
    (hover1 : UInt256.size ≤ liquidity.toNat * balance1.toNat)
    (hnonzero : totalSupply ≠ ⟨0⟩) :
    ExecBlock config { contract := contract, locals := locals } evm
      [burnAmount0Stmt, burnAmount1Stmt] .reverted := by
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_burn_amount_of_get evm "balance0" liquidity balance0 totalSupply
      hliq hb0 htotal hfit0 hnonzero)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.letDeclRevert (evalExpr_burn_amount_productOverflow evm "balance1" liquidity balance1
      (by rw [store_get_ne _ _ (by decide), hliq])
      (by rw [store_get_ne _ _ (by decide), hb1]) hover1))

end UniswapV2Pair
