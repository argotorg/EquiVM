import Examples.UniswapV2Pair.MintFeeRuntimeSqrt

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

theorem mintFeeReserveProductNat_lt_of_clean (reserve0 reserve1 : UInt256)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1) :
    mintFeeReserveProductNat reserve0 reserve1 < UInt256.size := by
  have hreserve0Lt : reserve0.toNat < 2 ^ 112 := by
    have h := uniswapUint112Masked_lt reserve0
    simpa [hclean0] using h
  have hreserve1Lt : reserve1.toNat < 2 ^ 112 := by
    have h := uniswapUint112Masked_lt reserve1
    simpa [hclean1] using h
  have hprodLt224 : reserve0.toNat * reserve1.toNat < 2 ^ 224 := by
    nlinarith [hreserve0Lt, hreserve1Lt]
  exact lt_trans (by simpa [mintFeeReserveProductNat] using hprodLt224)
    (by norm_num [UInt256.size])

theorem sqrtFunctionSmallResultValue_eq_int_of_word (w : UInt256) :
    sqrtFunctionSmallResultValue w =
      .int (if w = ⟨0⟩ then (0 : Int) else 1) := by
  by_cases hzero : w = ⟨0⟩
  · simp [sqrtFunctionSmallResultValue, hzero]
  · have htoNat : w.toNat ≠ 0 := by
      intro h
      exact hzero (uint256_toNat_eq_zero h)
    simp [sqrtFunctionSmallResultValue, hzero, htoNat]

set_option maxHeartbeats 1000000 in
theorem mintFeeSqrtPrefixSmall
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (kLast : UInt256)
    (hfit : mintFeeReserveProductNat reserve0 reserve1 < UInt256.size)
    (hprodSmall : (UInt256.mul reserve0 reserve1).toNat ≤ 3)
    (hkLastSmall : kLast.toNat ≤ 3) :
    ExecBlock config (mintFeeAfterKLastFrame reserve0 reserve1 feeTo true kLast) evm
      [ .internalCall "sqrt" [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))]
          "rootK",
        .internalCall "sqrt" [.var "_kLast"] "rootKLast" ]
      (.ok
        (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast
          (if UInt256.mul reserve0 reserve1 = ⟨0⟩ then (0 : Int) else 1)
          (if kLast = ⟨0⟩ then (0 : Int) else 1))
        evm) := by
  let rootK : Int := if UInt256.mul reserve0 reserve1 = ⟨0⟩ then 0 else 1
  let rootKLast : Int := if kLast = ⟨0⟩ then 0 else 1
  have hprodWord :
      mintFeeReserveProductWord reserve0 reserve1 = UInt256.mul reserve0 reserve1 :=
    mintFeeReserveProductWord_eq_mul reserve0 reserve1 hfit
  have hprodSmall' : (mintFeeReserveProductWord reserve0 reserve1).toNat ≤ 3 := by
    simpa [hprodWord] using hprodSmall
  have hrootK :=
    uniswapSqrtFunctionCallSuccess_le3
      (caller := mintFeeAfterKLastFrame reserve0 reserve1 feeTo true kLast)
      (evm := evm) (y := mintFeeReserveProductWord reserve0 reserve1)
      (args := [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))])
      (retVar := "rootK") rfl hprodSmall'
      (evalExprs_mintFee_reserveProductArg evm reserve0 reserve1 feeTo true kLast hfit)
  have hrootKValue :
      sqrtFunctionSmallResultValue (mintFeeReserveProductWord reserve0 reserve1) =
        .int rootK := by
    rw [sqrtFunctionSmallResultValue_eq_int_of_word]
    simp [rootK, hprodWord]
  have hrootK' :
      ExecStmt config (mintFeeAfterKLastFrame reserve0 reserve1 feeTo true kLast) evm
        (.internalCall "sqrt" [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))]
          "rootK")
        (.ok (mintFeeAfterRootKFrame reserve0 reserve1 feeTo true kLast rootK) evm) := by
    rw [hrootKValue] at hrootK
    simpa [mintFeeAfterRootKFrame, mintFeeAfterRootKStore, resumeAfterInternalCall]
      using hrootK
  have hrootKLast :=
    uniswapSqrtFunctionCallSuccess_le3
      (caller := mintFeeAfterRootKFrame reserve0 reserve1 feeTo true kLast rootK)
      (evm := evm) (y := kLast) (args := [.var "_kLast"]) (retVar := "rootKLast")
      rfl hkLastSmall
      (evalExprs_mintFee_kLastArg evm reserve0 reserve1 feeTo true kLast rootK)
  have hrootKLastValue :
      sqrtFunctionSmallResultValue kLast = .int rootKLast := by
    rw [sqrtFunctionSmallResultValue_eq_int_of_word]
  have hrootKLast' :
      ExecStmt config (mintFeeAfterRootKFrame reserve0 reserve1 feeTo true kLast rootK) evm
        (.internalCall "sqrt" [.var "_kLast"] "rootKLast")
        (.ok (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast)
          evm) := by
    rw [hrootKLastValue] at hrootKLast
    simpa [mintFeeAfterRootKLastFrame, mintFeeAfterRootKLastStore,
      resumeAfterInternalCall] using hrootKLast
  simpa [rootK, rootKLast] using
    ExecBlock.consNormal hrootK' (ExecBlock.consNormal hrootKLast' ExecBlock.nil)

set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeRuntimeFactoryResultFeeOnKLastNonzeroRootEntry
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σ'' : AccountMap}
    {o o1 outFee : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 toWord sel : UInt256} {zFee : Bool}
    (rd7781 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7781⟩
      [(if zFee then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨132⟩,
        feeToSelectorWord, mintFeeFactoryWord σ'' I, ⟨0⟩, ⟨0⟩,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (feeToStaticcallMem
        (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
        outFee)
      feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (ho132 : 32 ≤ o1.size) (ho1Size : o1.size < UInt256.size)
    (houtFeeSize : outFee.size < UInt256.size)
    (hzFee : zFee = true)
    (hout32 : 32 ≤ outFee.size)
    (hfeeToNonzero :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
          solcAddrMask ≠
        ⟨0⟩)
    (hkLastNonzero : mintFeeKLastSlotWord σFee I ≠ ⟨0⟩)
    (hclean0 :
      UInt256.land (reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)
          reserve112Mask =
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)
    (hclean1 :
      UInt256.land (reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)
          reserve112Mask =
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8046⟩
      [UInt256.mul
          (reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)
          (reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨7886⟩, ⟨0⟩, mintFeeKLastSlotWord σFee I,
        UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)), ⟨1⟩,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (feeToStaticcallMem
        (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
        outFee)
      feeToStaticcallActiveWords outFee (cAFee, σFee) k' C' := by
  obtain ⟨_, _, hdecoded⟩ :=
    uniswapMintFeeRuntimeFactoryResultBranchesFromCall rd7781 ho32 hoSize ho132 ho1Size
      houtFeeSize
  obtain ⟨_, _, rd7825⟩ := hdecoded hzFee hout32
  exact uniswapMintFeeRuntimeFeeOnKLastNonzeroRootKEntryFromDecode rd7825
    hfeeToNonzero hkLastNonzero hclean0 hclean1

end UniswapV2Pair
