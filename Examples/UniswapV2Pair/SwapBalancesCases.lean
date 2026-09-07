import Examples.UniswapV2Pair.SwapBalancePrepare
import Examples.UniswapV2Pair.PairBalanceAnyDepthCases
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

abbrev swapBalanceStmts : List Stmt := balanceOfThisStmts (.var "_token0") "balance0" ++
  balanceOfThisStmts (.var "_token1") "balance1"
abbrev swapAfterBalancesFrame (caller : Frame) (balance0 balance1 : UInt256) : Frame :=
  { caller with locals := ((caller.locals.insert "balance0" (uniswapUint256Value balance0)).insert
      "balance1" (uniswapUint256Value balance1)) }

set_option maxHeartbeats 1000000 in
theorem uniswapSwapBalancesCases
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {aw ptr token1 token0 scratch1 scratch0 reserve1 reserve0
      dataLen dataPtr toWord amount1Out amount0Out : UInt256} {R : List UInt256} {k C : Nat}
    {caller : Frame} (evm : EVM.State) (token0Addr token1Addr : AccountAddress)
    (rd2091 : RD uniswapV2PairBytecode I g s0 ⟨2091⟩
      (token1 :: token0 :: scratch1 :: scratch0 :: reserve1 :: reserve0 :: dataLen :: dataPtr ::
        toWord :: amount1Out :: amount0Out :: R) mem aw rdata (cA, σ) k C)
    (ha : accountMapEquiv σ evm.accountMap) (he : evm.executionEnv = I)
    (hc : evm.createdAccounts = cA) (hs : evm.σ₀ = s0.σ₀)
    (hg : evm.genesisBlockHeader = s0.genesisBlockHeader) (hb : evm.blocks = s0.blocks)
    (hcaller : caller.contract = contract)
    (ht0 : caller.locals.get? "_token0" = some (.address token0Addr))
    (ht1 : caller.locals.get? "_token1" = some (.address token1Addr))
    (htarget0 : EVM.address token0Addr = AccountAddress.ofUInt256 (UInt256.land token0 solcAddrMask))
    (htarget1 : EVM.address token1Addr = AccountAddress.ofUInt256 (UInt256.land token1 solcAddrMask))
    (hin : 96 ≤ mem.size) (hgap : ptr.toNat - mem.size < USize.size) (hlo : 96 ≤ ptr.toNat)
    (haw : aw.toNat * 32 < UInt256.size) (hawLo : 96 ≤ aw.toNat * 32)
    (hfit : ptr.toNat + 67 < UInt256.size) (hread : mem.readWithPadding 64 32 = ptr.toByteArray)
    (hov : R.length + 25 ≤ 1024) :
    (ExecBlock config caller evm swapBalanceStmts .reverted ∧ RDrev uniswapV2PairBytecode g s0) ∨
    ∃ evm' σ' cA' mem' aw' out balance0 balance1 k' C',
      ExecBlock config caller evm swapBalanceStmts
        (.ok (swapAfterBalancesFrame caller balance0 balance1) evm') ∧
      accountMapEquiv σ' evm'.accountMap ∧ evm'.createdAccounts = cA' ∧ evm'.σ₀ = s0.σ₀ ∧
      evm'.genesisBlockHeader = s0.genesisBlockHeader ∧ evm'.blocks = s0.blocks ∧ evm'.executionEnv = I ∧
      96 ≤ mem'.size ∧ ptr.toNat - mem'.size < USize.size ∧ aw'.toNat * 32 < UInt256.size ∧
      96 ≤ aw'.toNat * 32 ∧ mem'.readWithPadding 64 32 = ptr.toByteArray ∧
      RD uniswapV2PairBytecode I g s0 ⟨2331⟩
        (⟨0⟩ :: balance1 :: balance0 :: reserve1 :: reserve0 :: dataLen :: dataPtr ::
          toWord :: amount1Out :: amount0Out :: R) mem' aw' out (cA', σ') k' C' := by
  rcases caller with ⟨decl, locals⟩
  dsimp only at hcaller
  subst decl
  rw [balanceCallAddress_self] at htarget0 htarget1
  obtain ⟨_, _, rd2149⟩ := RD.uniswapSwapBalance0Prepared rd2091 hin hgap hlo haw hawLo
    hfit hread (by omega)
  have hr0 : evalExpr? config { contract := contract, locals := locals } evm (.var "_token0") =
      .ok (.address token0Addr) := by
    simp only [evalExpr?, EvalResult.ofOption, ht0]
  rcases uniswapPairBalanceCallRuntimeAnyDepthCases (site := .swap0) evm token0Addr locals
      "_token0" "balance0" rd2149 ha he hc hs hg hb hr0 htarget0 hin hgap hlo haw hfit hread
      (by simp only [List.length_cons]; omega) with
    ⟨hfirst, rdRev⟩ | ⟨evm0, σ0, cA0, out0, k0, C0, hfirst, ha0, hc0, hs0, hg0, hb0, he0,
      hout0, hout0hi, rd2206⟩
  · exact Or.inl ⟨execBlock_append_term hfirst (by intro f e h; cases h), rdRev⟩
  · obtain ⟨hin0, hgap0, haw0, hawLo0, hread0⟩ := balanceDynamicReturnMem_invariants aw ptr
      (UInt256.ofNat I.codeOwner.val) out0 hin hlo hgap hfit haw hread hout0hi
    obtain ⟨_, _, rd2267⟩ := RD.uniswapSwapBalance1Prepared rd2206 hin0 hgap0 hlo haw0 hawLo0
      hfit hread0 (by omega)
    have hr1 : evalExpr? config
        { contract := contract, locals := locals.insert "balance0" (uniswapUint256Value
          (UInt256.ofNat (fromByteArrayBigEndian (out0.extract 0 32)))) } evm0 (.var "_token1") =
        .ok (.address token1Addr) := by
      simp only [evalExpr?, store_get_ne _ _ (by decide : ("balance0" == "_token1") = false),
        EvalResult.ofOption, ht1]
    rcases uniswapPairBalanceCallRuntimeAnyDepthCases (site := .swap1) evm0 token1Addr _
        "_token1" "balance1" rd2267 ha0 he0 hc0 hs0 hg0 hb0 hr1 htarget1 hin0 hgap0 hlo haw0
        hfit hread0 (by simp only [List.length_cons]; omega) with
      ⟨hsecond, rdRev⟩ | ⟨evm1, σ1, cA1, out1, k1, C1, hsecond, ha1, hc1, hs1, hg1, hb1, he1,
        hout1, hout1hi, rd2324⟩
    · exact Or.inl ⟨execBlock_append hfirst hsecond, rdRev⟩
    · obtain ⟨hin1, hgap1, haw1, hawLo1, hread1⟩ := balanceDynamicReturnMem_invariants
        (balanceDynamicCalldataWords aw ptr) ptr (UInt256.ofNat I.codeOwner.val) out1
        hin0 hlo hgap0 hfit haw0 hread0 hout1hi
      obtain ⟨_, _, rd2331⟩ := RD.uniswapSwapBalancesExit rd2324 (by omega)
      exact Or.inr ⟨evm1, σ1, cA1, _, _, out1, _, _, _, _, execBlock_append hfirst hsecond,
        ha1, hc1, hs1, hg1, hb1, he1, hin1, hgap1, haw1, hawLo1, hread1, rd2331⟩

end UniswapV2Pair
