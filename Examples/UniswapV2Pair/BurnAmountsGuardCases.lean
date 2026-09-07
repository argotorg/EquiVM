import Examples.UniswapV2Pair.BurnAmountsGuardRuntime
import Examples.UniswapV2Pair.BurnAfterFeeSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

abbrev burnAmountsRequireExpr : Expr :=
  .binary .and (.binary .gt (.var "amount0") (.intLit 0))
    (.binary .gt (.var "amount1") (.intLit 0))

abbrev burnAmountsRequireStmt : Stmt := .require burnAmountsRequireExpr
abbrev burnInternalBurnStmt : Stmt := .internalCall "_burn" [this, .var "liquidity"] "_burnResult"

theorem evalExpr_burn_amountsRequire (evm : EVM.State) {locals : Store}
    {amount0 amount1 : UInt256}
    (ha0 : locals.get? "amount0" = some (uniswapUint256Value amount0))
    (ha1 : locals.get? "amount1" = some (uniswapUint256Value amount1)) :
    evalExpr? config { contract := contract, locals := locals } evm burnAmountsRequireExpr =
      .ok (.bool (decide (0 < amount0.toNat ∧ 0 < amount1.toNat))) := by
  simp only [burnAmountsRequireExpr, evalExpr?, EvalResult.ofOption, ha0, ha1,
    EvalResult.bind, bind, pure]
  by_cases hp0 : 0 < amount0.toNat <;> simp [evalBinaryOp?, hp0]

set_option maxHeartbeats 1000000 in
theorem uniswapBurnAmountsGuardAndBurnCasesWithMemory
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {totalSupply feeOn liquidity balance0 balance1
      token0 token1 reserve0 reserve1 amount0 amount1 : UInt256} {R : List UInt256} {k C : ℕ}
    {locals : Store} (evm : EVM.State)
    (rd4533 : RD uniswapV2PairBytecode I g s0 ⟨4533⟩
      (totalSupply :: feeOn :: liquidity :: balance1 :: balance0 :: token1 :: token0 ::
        reserve1 :: reserve0 :: amount1 :: amount0 :: R)
      mem feeToStaticcallActiveWords rdata (cA, σ) k C)
    (hAccounts : accountMapEquiv σ evm.accountMap) (henv : evm.executionEnv = I)
    (hliq : locals.get? "liquidity" = some (uniswapUint256Value liquidity))
    (ha0 : locals.get? "amount0" = some (uniswapUint256Value amount0))
    (ha1 : locals.get? "amount1" = some (uniswapUint256Value amount1))
    (hperm : I.perm = true) (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 32 ≤ 1024) :
    (ExecBlock config { contract := contract, locals := locals } evm
        [burnAmountsRequireStmt, burnInternalBurnStmt] .reverted ∧ RDrev uniswapV2PairBytecode g s0) ∨
    (∃ mem' k' C',
      ExecBlock config { contract := contract, locals := locals } evm
        [burnAmountsRequireStmt, burnInternalBurnStmt]
        (.ok (resumeAfterInternalCall { contract := contract, locals := locals } "_burnResult" none)
          (burnFunctionPostState evm I.codeOwner liquidity)) ∧
      accountMapEquiv (burnRuntimePostMap σ I (UInt256.ofNat I.codeOwner.val) liquidity)
        (burnFunctionPostState evm I.codeOwner liquidity).accountMap ∧
      RD uniswapV2PairBytecode I g s0 ⟨4617⟩
        (totalSupply :: feeOn :: liquidity :: balance1 :: balance0 :: token1 :: token0 ::
          reserve1 :: reserve0 :: amount1 :: amount0 :: R)
        mem' feeToStaticcallActiveWords rdata
        (cA, burnRuntimePostMap σ I (UInt256.ofNat I.codeOwner.val) liquidity) k' C' ∧
      mem'.size = 164 ∧ mem'.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ ∧
      mem'.readWithPadding 96 32 = mem.readWithPadding 96 32) := by
  have hreq := evalExpr_burn_amountsRequire evm ha0 ha1
  rcases uniswapBurnRuntimeAmountsGuardCases rd4533 hmem hread64 (by omega) with
    ⟨hnot, hrev⟩ | ⟨hpos, _, _, rd8302⟩
  · exact Or.inl ⟨ExecBlock.consRevert
      (ExecStmt.requireFalse (by simpa only [hnot, decide_false] using hreq)), hrev⟩
  · have hreqTrue : ExecStmt config { contract := contract, locals := locals } evm
        burnAmountsRequireStmt (.ok { contract := contract, locals := locals } evm) :=
      ExecStmt.requireTrue (by simpa only [hpos, decide_true] using hreq)
    have hargs : evalExprs? config { contract := contract, locals := locals } evm
        [this, .var "liquidity"] =
        .ok [burnFunctionFromValue I.codeOwner, burnFunctionValueValue liquidity] := by
      simp only [evalExprs?, evalExpr_uniswap_this, evalExpr?, EvalResult.ofOption, hliq,
        EvalResult.bind, bind, pure, henv]
    have hholder : I.codeOwner = AccountAddress.ofNat (UInt256.ofNat I.codeOwner.val).toNat := by
      rw [UInt256.toNat_ofNat_of_lt (lt_trans I.codeOwner.isLt
        (by native_decide : 2 ^ 160 < UInt256.size))]
      apply Fin.ext
      simp [AccountAddress.ofNat]
    rcases uniswapInternalBurnCallRuntimeCasesWithMemory (retVar := "_burnResult") evm I.codeOwner rd8302
        hAccounts henv hholder rfl hargs hperm hmem hread64 (by jump_dest)
        (by simp only [List.length_cons]; omega) with
      ⟨hburn, hrev⟩ | ⟨mem', k', C', hburn, hpost, rd4617, hmem', hread', h96⟩
    · exact Or.inl ⟨ExecBlock.consNormal hreqTrue (ExecBlock.consRevert hburn), hrev⟩
    · exact Or.inr ⟨mem', k', C',
        ExecBlock.consNormal hreqTrue (ExecBlock.consNormal hburn ExecBlock.nil),
        hpost, rd4617, hmem', hread', h96⟩


set_option maxHeartbeats 1000000 in
theorem uniswapBurnAmountsGuardAndBurnCases
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {totalSupply feeOn liquidity balance0 balance1
      token0 token1 reserve0 reserve1 amount0 amount1 : UInt256} {R : List UInt256} {k C : ℕ}
    {locals : Store} (evm : EVM.State)
    (rd4533 : RD uniswapV2PairBytecode I g s0 ⟨4533⟩
      (totalSupply :: feeOn :: liquidity :: balance1 :: balance0 :: token1 :: token0 ::
        reserve1 :: reserve0 :: amount1 :: amount0 :: R)
      mem feeToStaticcallActiveWords rdata (cA, σ) k C)
    (hAccounts : accountMapEquiv σ evm.accountMap) (henv : evm.executionEnv = I)
    (hliq : locals.get? "liquidity" = some (uniswapUint256Value liquidity))
    (ha0 : locals.get? "amount0" = some (uniswapUint256Value amount0))
    (ha1 : locals.get? "amount1" = some (uniswapUint256Value amount1))
    (hperm : I.perm = true) (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 32 ≤ 1024) :
    (ExecBlock config { contract := contract, locals := locals } evm
        [burnAmountsRequireStmt, burnInternalBurnStmt] .reverted ∧ RDrev uniswapV2PairBytecode g s0) ∨
    (∃ mem' k' C',
      ExecBlock config { contract := contract, locals := locals } evm
        [burnAmountsRequireStmt, burnInternalBurnStmt]
        (.ok (resumeAfterInternalCall { contract := contract, locals := locals } "_burnResult" none)
          (burnFunctionPostState evm I.codeOwner liquidity)) ∧
      accountMapEquiv (burnRuntimePostMap σ I (UInt256.ofNat I.codeOwner.val) liquidity)
        (burnFunctionPostState evm I.codeOwner liquidity).accountMap ∧
      RD uniswapV2PairBytecode I g s0 ⟨4617⟩
        (totalSupply :: feeOn :: liquidity :: balance1 :: balance0 :: token1 :: token0 ::
          reserve1 :: reserve0 :: amount1 :: amount0 :: R)
        mem' feeToStaticcallActiveWords rdata
        (cA, burnRuntimePostMap σ I (UInt256.ofNat I.codeOwner.val) liquidity) k' C' ∧
      mem'.size = 164 ∧ mem'.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) := by
  rcases uniswapBurnAmountsGuardAndBurnCasesWithMemory evm rd4533 hAccounts henv hliq ha0 ha1
      hperm hmem hread64 hov with
    hrev | ⟨m, k', C', hb, ha, rd, hm, h64, _⟩
  · exact Or.inl hrev
  · exact Or.inr ⟨m, k', C', hb, ha, rd, hm, h64⟩

end UniswapV2Pair
