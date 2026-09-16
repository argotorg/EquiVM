import Examples.UniswapV2Pair.SwapTransfersSource
import Examples.UniswapV2Pair.SwapTransfersRuntime
import Examples.UniswapV2Pair.OptionalSafeTransferAnyDepth
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem uniswapSwapTransfersAnyDepthCases
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {aw freePtr token1 token0 scratch1 scratch0 reserve1 reserve0
      dataLen dataPtr toWord amount1Out amount0Out : UInt256} {R : List UInt256} {k C : Nat}
    {caller : Frame} (evm : EVM.State) (token0Addr token1Addr recipient : AccountAddress)
    (rd1870 : RD uniswapV2PairBytecode I g s0 ⟨1870⟩
      (token1 :: token0 :: scratch1 :: scratch0 :: reserve1 :: reserve0 :: dataLen :: dataPtr ::
        toWord :: amount1Out :: amount0Out :: R) mem aw rdata (cA, σ) k C)
    (hAccounts : accountMapEquiv σ evm.accountMap) (henv : evm.executionEnv = I)
    (hcreated : evm.createdAccounts = cA) (hσ0 : evm.σ₀ = s0.σ₀)
    (hgenesis : evm.genesisBlockHeader = s0.genesisBlockHeader) (hblocks : evm.blocks = s0.blocks)
    (hcaller : caller.contract = contract)
    (ht0 : caller.locals.get? "_token0" = some (.address token0Addr))
    (ht1 : caller.locals.get? "_token1" = some (.address token1Addr))
    (hto : caller.locals.get? "to" = some (.address recipient))
    (ha0 : caller.locals.get? "amount0Out" = some (uniswapUint256Value amount0Out))
    (ha1 : caller.locals.get? "amount1Out" = some (uniswapUint256Value amount1Out))
    (htoken0 : EVM.address token0Addr = AccountAddress.ofUInt256 (UInt256.land token0 solcAddrMask))
    (htoken1 : EVM.address token1Addr = AccountAddress.ofUInt256 (UInt256.land token1 solcAddrMask))
    (hrecipient : UInt256.ofNat recipient.val = UInt256.land solcAddrMask toWord)
    (hperm : I.perm = true)
    (hready : SafeTransferMemoryReady mem aw freePtr)
    (hcap : freePtr.toNat + 2 ^ 138 + 227 ≤ 2 ^ 255 + 1024)
    (hov : R.length + 31 ≤ 1024) :
    (ExecBlock config caller evm [swapFirstTransferStmt, swapSecondTransferStmt] .reverted ∧
      RDrev uniswapV2PairBytecode g s0) ∨
    (∃ evm' σ' cA' mem' aw' ptr' data' k' C',
      ExecBlock config caller evm [swapFirstTransferStmt, swapSecondTransferStmt]
        (.ok (swapAfterTransfersFrame caller amount0Out amount1Out) evm') ∧
      accountMapEquiv σ' evm'.accountMap ∧ evm'.createdAccounts = cA' ∧ evm'.σ₀ = s0.σ₀ ∧
      evm'.genesisBlockHeader = s0.genesisBlockHeader ∧ evm'.blocks = s0.blocks ∧ evm'.executionEnv = I ∧
      SafeTransferMemoryReady mem' aw' ptr' ∧ ptr'.toNat ≤ freePtr.toNat + 2 * (2 ^ 138 + 227) ∧
      RD uniswapV2PairBytecode I g s0 ⟨1904⟩
        (token1 :: token0 :: scratch1 :: scratch0 :: reserve1 :: reserve0 :: dataLen :: dataPtr ::
          toWord :: amount1Out :: amount0Out :: R) mem' aw' data' (cA', σ') k' C') := by
  have hentry0 := uniswapSwapRuntimeFirstTransferCases rd1870 (by omega)
  have hcond0 := evalExpr_uint256_var_positive evm "amount0Out" amount0Out ha0 (cfg := config)
  have hargs0 := evalExprs_safeTransfer_args_of_get evm "_token0" "to" "amount0Out"
    token0Addr recipient amount0Out ht0 hto ha0
  rcases uniswapOptionalSafeTransferAnyDepthCases (retVar := "ok0") evm token0Addr recipient hentry0
      hAccounts henv hcreated hσ0 hgenesis hblocks hcaller hcond0 hargs0 htoken0 hrecipient hperm
      hready (by omega) (by jump_dest) (by simp only [List.length_cons]; omega) with
    ⟨hfirst, rdRev⟩ | ⟨evm0, σ0, cA0, mem0, aw0, ptr0, data0, k0, C0,
      hfirst, hAccounts0, hcreated0, hσ00, hgenesis0, hblocks0, henv0, hready0, hcap0, rd1887⟩
  · exact Or.inl ⟨ExecBlock.consRevert hfirst, rdRev⟩
  · let caller0 := optionalSafeTransferFrame caller "ok0" amount0Out
    have hcaller0 : caller0.contract = contract := by
      unfold caller0 optionalSafeTransferFrame
      split <;> exact hcaller
    have ht1' : caller0.locals.get? "_token1" = some (.address token1Addr) :=
      (optionalSafeTransferFrame_get_ne caller "ok0" "_token1" amount0Out (by decide)).trans ht1
    have hto' : caller0.locals.get? "to" = some (.address recipient) :=
      (optionalSafeTransferFrame_get_ne caller "ok0" "to" amount0Out (by decide)).trans hto
    have ha1' : caller0.locals.get? "amount1Out" = some (uniswapUint256Value amount1Out) :=
      (optionalSafeTransferFrame_get_ne caller "ok0" "amount1Out" amount0Out (by decide)).trans ha1
    have hentry1 := uniswapSwapRuntimeSecondTransferCases rd1887 (by omega)
    have hcond1 := evalExpr_uint256_var_positive evm0 "amount1Out" amount1Out ha1' (cfg := config)
    have hargs1 := evalExprs_safeTransfer_args_of_get evm0 "_token1" "to" "amount1Out"
      token1Addr recipient amount1Out ht1' hto' ha1'
    rcases uniswapOptionalSafeTransferAnyDepthCases (retVar := "ok1") evm0 token1Addr recipient hentry1
        hAccounts0 henv0 hcreated0 hσ00 hgenesis0 hblocks0 hcaller0 hcond1 hargs1 htoken1 hrecipient
        hperm hready0 (by omega) (by jump_dest) (by simp only [List.length_cons]; omega) with
      ⟨hsecond, rdRev⟩ | ⟨evm1, σ1, cA1, mem1, aw1, ptr1, data1, k1, C1,
        hsecond, hAccounts1, hcreated1, hσ01, hgenesis1, hblocks1, henv1, hready1, hcap1, rd1904⟩
    · exact Or.inl ⟨ExecBlock.consNormal hfirst (ExecBlock.consRevert hsecond), rdRev⟩
    · exact Or.inr ⟨evm1, σ1, cA1, mem1, aw1, ptr1, data1, k1, C1,
        ExecBlock.consNormal hfirst (ExecBlock.consNormal hsecond ExecBlock.nil),
        hAccounts1, hcreated1, hσ01, hgenesis1, hblocks1, henv1, hready1, by omega, rd1904⟩

end UniswapV2Pair
