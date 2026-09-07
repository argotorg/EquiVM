import Examples.UniswapV2Pair.MintFeeRootRuntimeCases

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeActualRootRuntimeCases
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
     {mem rdata : ByteArray} {k C : ℕ}
    {rootK rootKLast : Int} {feeTo : AccountAddress}
    {kLast feeToWord amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (evmFeeS : EVM.State) (rd7899 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7899⟩
      [UInt256.ofNat rootKLast.toNat, ⟨0⟩, UInt256.ofNat rootK.toNat, kLast, feeToWord,
        ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1,
        balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hAccounts : accountMapEquiv σFee evmFeeS.accountMap)
    (henv : evmFeeS.executionEnv = I)
    (hrecipient : feeTo = AccountAddress.ofNat feeToWord.toNat)
    (hrootKNonneg : 0 ≤ rootK) (hrootKSize : rootK.toNat < UInt256.size)
    (hrootKLastNonneg : 0 ≤ rootKLast) (hrootKLastSize : rootKLast.toNat < UInt256.size)
    (hperm : I.perm = true) (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (ExecBlock config
      (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast)
      evmFeeS [mintFeeRootComparisonStmt] .reverted ∧
      RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)) ∨
    (∃ frame' evm' σ' mem' k' C',
      ExecBlock config
        (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast)
        evmFeeS [mintFeeRootComparisonStmt] (.ok frame' evm') ∧
      evalExpr? config frame' evm' (.var "feeOn") = .ok (.bool true) ∧
      accountMapEquiv σ' evm'.accountMap ∧ evm'.executionEnv = I ∧
      evm'.createdAccounts = evmFeeS.createdAccounts ∧
      RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
        [⟨1⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
          toWord, ⟨861⟩, sel] mem' feeToStaticcallActiveWords rdata (cAFee, σ') k' C' ∧
      mem'.size = 164 ∧ mem'.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) := by
  exact uniswapMintFeeActualRootRuntimeCasesOfTail evmFeeS rd7899 hAccounts henv hrecipient
    hrootKNonneg hrootKSize hrootKLastNonneg hrootKLastSize hperm hmem hmem64
    (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)

end UniswapV2Pair
