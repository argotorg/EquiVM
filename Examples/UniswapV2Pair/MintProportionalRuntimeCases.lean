import Examples.UniswapV2Pair.MintTailRuntimeCases
import Examples.UniswapV2Pair.MintProportionalArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem uniswapMintProportionalRuntimeCases
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {totalSupply feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel :
      UInt256} {locals : Store} (evm : EVM.State) (recipient : AccountAddress) (fee : Bool)
    (rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [feeOn, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hAccounts : accountMapEquiv σFee evm.accountMap)
    (henv : evm.executionEnv = I)
    (hrecipient : recipient = AccountAddress.ofNat toWord.toNat)
    (hto : locals.get? "to" = some (.address recipient))
    (htotalSlot : uniswapSlotWord ⟨0⟩ σFee I = totalSupply)
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
    (htotal : locals.get? "_totalSupply" = some (uniswapUint256Value totalSupply))
    (hamount0 : locals.get? "amount0" = some (uniswapUint256Value amount0))
    (hamount1 : locals.get? "amount1" = some (uniswapUint256Value amount1))
    (hflag : feeOn = if fee then ⟨1⟩ else ⟨0⟩)
    (hfee : locals.get? "feeOn" = some (.bool fee))
    (hbalance0 : locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hbalance1 : locals.get? "balance1" = some (uniswapUint256Value balance1))
    (hreserve0 : locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)))
    (hreserve1 : locals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)))
    (hreserve0Base : locals.get? "reserve0" = none)
    (hreserve1Base : locals.get? "reserve1" = none)
    (hkLast : locals.get? "kLast" = none)
    (hunlocked : locals.get? "unlocked" = none)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hperm : I.perm = true)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (ExecBlock config { contract := contract, locals := locals } evm
        ([mintLiquidityBranchStmt] ++ mintAfterLiquidityTailStmts) .reverted ∧
      (RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∨
        RDinvalid uniswapV2PairBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))) ∨
    (∃ liquidity frame' evm' σ',
      ExecBlock config { contract := contract, locals := locals } evm
        ([mintLiquidityBranchStmt] ++ mintAfterLiquidityTailStmts) (.returned frame' evm'
          (some [uniswapUint256Value liquidity])) ∧
      accountMapEquiv σ' evm'.accountMap ∧ evm'.createdAccounts = evm.createdAccounts ∧
      RDret uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (cAFee, σ') (UInt256.toByteArray liquidity)) := by
  obtain ⟨_, _, rd3762⟩ := uniswapMintRuntimeAfterMintFeeTotalSupplyNonzero rd3701
    htotalSlot htotalNonzero
  rcases uniswapMintProportionalArithmeticCases evm rd3762 hclean0 hclean1 hmem hmem64
      htotal htotalNonzero hamount0 hamount1 hreserve0 hreserve1 with
      ⟨hfit0, hr0, hfit1, hr1⟩ | ⟨hrev, hfailed⟩
  · let liquidity0 := mintProportionalLiquidityWord amount0 totalSupply reserve0
    let liquidity1 := mintProportionalLiquidityWord amount1 totalSupply reserve1
    let liquidity := minFunctionResultWord liquidity0 liquidity1
    let afterBranch : Frame := ⟨contract,
      ((locals.insert "liquidity0" (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert
        "liquidity1" (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert
        "liquidity" (uniswapUint256Value liquidity)⟩
    have hbranch : ExecStmt config ⟨contract, locals⟩ evm mintLiquidityBranchStmt
        (.ok afterBranch evm) := uniswapMintProportionalLiquidityBranchMin evm amount0 amount1
      totalSupply reserve0 reserve1 htotal htotalNonzero hamount0 hamount1 hreserve0 hreserve1
      hfit0 hfit1 hr0 hr1
    obtain ⟨k3841, C3841, rd3841Raw⟩ := uniswapMintRuntimeProportionalLiquidityEntry rd3762
      hclean0 hclean1 hfit0 hfit1 hr0 hr1
    have rd3841 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3841⟩
        [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
          liquidity, toWord, ⟨861⟩, sel]
        mem feeToStaticcallActiveWords rdata (cAFee, σFee) k3841 C3841 := by
      simpa only [liquidity, liquidity0, liquidity1, mintProportionalLiquidityWord,
        mintAmountProductWord_eq_mul _ _ hfit0, mintAmountProductWord_eq_mul _ _ hfit1]
        using rd3841Raw
    have htail := uniswapMintTailRuntimeCases (locals := afterBranch.locals) evm recipient fee
      rd3841 hAccounts henv hrecipient
      (by simp only [afterBranch]; rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
        store_get_ne _ _ (by decide), hto])
      (store_get_self _ _ _) hflag
      (by simp only [afterBranch]; rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
        store_get_ne _ _ (by decide), hfee])
      (by simp only [afterBranch]; rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
        store_get_ne _ _ (by decide), hbalance0])
      (by simp only [afterBranch]; rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
        store_get_ne _ _ (by decide), hbalance1])
      (by simp only [afterBranch]; rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
        store_get_ne _ _ (by decide), hreserve0])
      (by simp only [afterBranch]; rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
        store_get_ne _ _ (by decide), hreserve1])
      (by simp only [afterBranch]; rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
        store_get_ne _ _ (by decide), hreserve0Base])
      (by simp only [afterBranch]; rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
        store_get_ne _ _ (by decide), hreserve1Base])
      (by simp only [afterBranch]; rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
        store_get_ne _ _ (by decide), hkLast])
      (by simp only [afterBranch]; rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
        store_get_ne _ _ (by decide), hunlocked])
      hclean0 hclean1 hperm hmem hmem64
    rcases htail with ⟨hrev, rdRev⟩ | ⟨frameRet, evmRet, σRet, hreturn, hRetAccounts,
      hcreatedRet, rdRet⟩
    · exact Or.inl ⟨ExecBlock.consNormal hbranch hrev, Or.inl rdRev⟩
    · exact Or.inr ⟨liquidity, frameRet, evmRet, σRet, ExecBlock.consNormal hbranch hreturn,
        hRetAccounts, hcreatedRet, rdRet⟩
  · exact Or.inl ⟨ExecBlock.consRevert hrev, hfailed⟩

end UniswapV2Pair

