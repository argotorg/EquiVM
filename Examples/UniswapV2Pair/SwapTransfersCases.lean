import Examples.UniswapV2Pair.SwapTransfersAnyDepth
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem uniswapSwapTransfersCases
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
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true)
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
  have _ := hdepth
  exact uniswapSwapTransfersAnyDepthCases evm token0Addr token1Addr recipient rd1870
    hAccounts henv hcreated hσ0 hgenesis hblocks hcaller ht0 ht1 hto ha0 ha1 htoken0 htoken1
    hrecipient hperm hready hcap hov

end UniswapV2Pair
