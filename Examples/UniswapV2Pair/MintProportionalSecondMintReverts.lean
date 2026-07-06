import Examples.UniswapV2Pair.MintInitialSecondMintReverts

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

set_option maxHeartbeats 1000000 in
theorem uniswapMintProportionalSecondMintTotalSupplyOverflowFromAfterFeeCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {evm0S evm1S evmAfter : EVM.State}
    {out0 out1 mem rdata : ByteArray} {k C : ℕ}
    {feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 totalSupply liquidity toWord sel :
      UInt256}
    (nextLocals : Store) (recipient : AccountAddress)
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
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
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
    (hcall0 : typedCallViaEVM config
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
      (true, evm0S, out0) false)
    (hdec0 :
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0S
      (EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩)) "balanceOf" 0
      [.address evm0S.executionEnv.codeOwner] (true, evm1S, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
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
    (hfee :
      ExecStmt config
        { contract := contract,
          locals :=
            mintAmountStore
              (uniswapLockEnteredState
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) I balance0
              balance1 }
        evm1S (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
        (.ok { contract := contract, locals := nextLocals } evmAfter))
    (hbase : nextLocals.get? "totalSupply" = none)
    (hto : nextLocals.get? "to" = some (.address recipient))
    (hamount0 : nextLocals.get? "amount0" = some (uniswapUint256Value amount0))
    (hamount1 : nextLocals.get? "amount1" = some (uniswapUint256Value amount1))
    (hreserve0 :
      nextLocals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)))
    (hreserve1 :
      nextLocals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)))
    (htotalEq : mintFunctionTotalSupplyWord evmAfter = totalSupply)
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
    (hmulFit0 : amount0.toNat * totalSupply.toNat < UInt256.size)
    (hmulFit1 : amount1.toNat * totalSupply.toNat < UInt256.size)
    (hreserve0Nonzero : reserve0 ≠ ⟨0⟩)
    (hreserve1Nonzero : reserve1 ≠ ⟨0⟩)
    (hliquidity :
      liquidity =
        minFunctionResultWord (UInt256.div (UInt256.mul amount0 totalSupply) reserve0)
          (UInt256.div (UInt256.mul amount1 totalSupply) reserve1))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hsourceOverflow : UInt256.size ≤ mintFunctionTotalSupplyNewNat evmAfter liquidity)
    (rd3762 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3762⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hruntimeOverflow :
      UInt256.size ≤ (uniswapSlotWord ⟨0⟩ σFee I).toNat + liquidity.toNat)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let afterTotalSupplyLocals :=
    nextLocals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))
  let caller : Frame := { contract := contract, locals := afterTotalSupplyLocals }
  let liquidity0 := mintProportionalLiquidityWord amount0 totalSupply reserve0
  let liquidity1 := mintProportionalLiquidityWord amount1 totalSupply reserve1
  let afterBranch :=
    resumeAfterInternalCall
      { contract := contract,
        locals :=
          (afterTotalSupplyLocals.insert "liquidity0"
            (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert
              "liquidity1" (mintProportionalLiquidityValue amount1 totalSupply reserve1) }
      "liquidity" (some (minFunctionResultValue liquidity0 liquidity1))
  have hprefix :=
    uniswapMintAfterMintFeeTotalSupplyPrefix_of_call evmS evm0S evm1S evmAfter I
      nextLocals (by simp only [evmS, initState]; exact hwv) hunlockedSolm hguard0
      hguard1 hcall0 hdec0 hcall1 hdec1 hle0Source hle1Source hfee hbase
  have htoAfterTotal :
      afterTotalSupplyLocals.get? "to" = some (.address recipient) := by
    change (nextLocals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "to" =
        some (.address recipient)
    rw [store_get_ne _ _ (by decide), hto]
  have htotalAfter :
      afterTotalSupplyLocals.get? "_totalSupply" = some (uniswapUint256Value totalSupply) := by
    change (nextLocals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "_totalSupply" =
        some (uniswapUint256Value totalSupply)
    rw [store_get_self]
    simp [htotalEq]
  have hamount0After :
      afterTotalSupplyLocals.get? "amount0" = some (uniswapUint256Value amount0) := by
    change (nextLocals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "amount0" =
        some (uniswapUint256Value amount0)
    rw [store_get_ne _ _ (by decide), hamount0]
  have hamount1After :
      afterTotalSupplyLocals.get? "amount1" = some (uniswapUint256Value amount1) := by
    change (nextLocals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "amount1" =
        some (uniswapUint256Value amount1)
    rw [store_get_ne _ _ (by decide), hamount1]
  have hreserve0After :
      afterTotalSupplyLocals.get? "_reserve0" =
        some (.int (Int.ofNat reserve0.toNat)) := by
    change (nextLocals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "_reserve0" =
        some (.int (Int.ofNat reserve0.toNat))
    rw [store_get_ne _ _ (by decide), hreserve0]
  have hreserve1After :
      afterTotalSupplyLocals.get? "_reserve1" =
        some (.int (Int.ofNat reserve1.toNat)) := by
    change (nextLocals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "_reserve1" =
        some (.int (Int.ofNat reserve1.toNat))
    rw [store_get_ne _ _ (by decide), hreserve1]
  have hbranchStmt :=
    uniswapMintProportionalLiquidityBranchMin (locals := afterTotalSupplyLocals) evmAfter
      amount0 amount1 totalSupply reserve0 reserve1 htotalAfter htotalNonzero hamount0After
      hamount1After hreserve0After hreserve1After
      (by simpa [mintAmountProductNat] using hmulFit0)
      (by simpa [mintAmountProductNat] using hmulFit1) hreserve0Nonzero hreserve1Nonzero
  have hbranch :
      ExecBlock config caller evmAfter [mintLiquidityBranchStmt] (.ok afterBranch evmAfter) := by
    exact ExecBlock.consNormal
      (by
        simpa [caller, afterBranch, liquidity0, liquidity1, hliquidity] using hbranchStmt)
      ExecBlock.nil
  have htoAfter :
      afterBranch.locals.get? "to" = some (.address recipient) := by
    change (((afterTotalSupplyLocals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "to" =
            some (.address recipient)
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), htoAfterTotal]
  have hprop0 :
      mintProportionalLiquidityWord amount0 totalSupply reserve0 =
        UInt256.div (UInt256.mul amount0 totalSupply) reserve0 := by
    simp [mintProportionalLiquidityWord,
      mintAmountProductWord_eq_mul amount0 totalSupply
        (by simpa [mintAmountProductNat] using hmulFit0)]
  have hprop1 :
      mintProportionalLiquidityWord amount1 totalSupply reserve1 =
        UInt256.div (UInt256.mul amount1 totalSupply) reserve1 := by
    simp [mintProportionalLiquidityWord,
      mintAmountProductWord_eq_mul amount1 totalSupply
        (by simpa [mintAmountProductNat] using hmulFit1)]
  have hliqAfter :
      afterBranch.locals.get? "liquidity" = some (uniswapUint256Value liquidity) := by
    change (((afterTotalSupplyLocals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "liquidity" =
            some (uniswapUint256Value liquidity)
    rw [store_get_self]
    rw [hliquidity]
    simp [minFunctionResultValue, liquidity0, liquidity1, hprop0, hprop1]
  have htail :
      ExecBlock config afterBranch evmAfter mintAfterLiquidityTailStmts .reverted := by
    exact uniswapMintAfterLiquidityMintTotalSupplyOverflowReverts evmAfter recipient liquidity
      htoAfter hliqAfter hliqNonzero hsourceOverflow
  have hthrough := execBlock_append hprefix (execBlock_append hbranch htail)
  have hbody :
      ExecTransitionBody config contract evmS (mintStore I) mintTransition.body .reverted := by
    exact ExecFuncBody.execBlockRevert (by
      simpa [mintTransition, mintLiquidityBranchStmt, mintInitialLiquidityBranchStmts,
        mintProportionalLiquidityBranchStmts, mintAfterLiquidityTailStmts, caller,
        afterTotalSupplyLocals, List.append_assoc] using hthrough)
  obtain ⟨_, _, rd3841⟩ :=
    uniswapMintRuntimeProportionalLiquidityEntry rd3762 hclean0 hclean1 hmulFit0 hmulFit1
      hreserve0Nonzero hreserve1Nonzero
  obtain ⟨_, _, rd8128⟩ :=
    uniswapMintRuntimeLiquidityMintEntry (by simpa [hliquidity] using rd3841) hliqNonzero
  have rdRev :
      RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    uniswapInternalMintRuntimeTotalSupplyOverflowReverts
      (value := liquidity) (recipient := toWord) (ret := ⟨3914⟩)
      (R := [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel])
      (σ := σFee) rd8128 hruntimeOverflow hmem hmem64
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact rdRev.reEquivExecutionRevert hcode hdispatch (uniswapDecode_mint_ok hsz36) hbody

set_option maxHeartbeats 1000000 in
theorem uniswapMintProportionalSecondMintBalanceOverflowFromAfterFeeCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {evm0S evm1S evmAfter : EVM.State}
    {out0 out1 mem rdata : ByteArray} {k C : ℕ}
    {feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 totalSupply liquidity toWord sel :
      UInt256}
    (nextLocals : Store) (recipient : AccountAddress)
    (hcode : I.code = uniswapV2PairBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some mintTransition)
    (hsz36 : 36 ≤ I.calldata.size)
    (hperm : I.perm = true)
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
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
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
    (hcall0 : typedCallViaEVM config
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
      (true, evm0S, out0) false)
    (hdec0 :
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0S
      (EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩)) "balanceOf" 0
      [.address evm0S.executionEnv.codeOwner] (true, evm1S, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
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
    (hfee :
      ExecStmt config
        { contract := contract,
          locals :=
            mintAmountStore
              (uniswapLockEnteredState
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) I balance0
              balance1 }
        evm1S (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
        (.ok { contract := contract, locals := nextLocals } evmAfter))
    (hbase : nextLocals.get? "totalSupply" = none)
    (hto : nextLocals.get? "to" = some (.address recipient))
    (hamount0 : nextLocals.get? "amount0" = some (uniswapUint256Value amount0))
    (hamount1 : nextLocals.get? "amount1" = some (uniswapUint256Value amount1))
    (hreserve0 :
      nextLocals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)))
    (hreserve1 :
      nextLocals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)))
    (htotalEq : mintFunctionTotalSupplyWord evmAfter = totalSupply)
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
    (hmulFit0 : amount0.toNat * totalSupply.toNat < UInt256.size)
    (hmulFit1 : amount1.toNat * totalSupply.toNat < UInt256.size)
    (hreserve0Nonzero : reserve0 ≠ ⟨0⟩)
    (hreserve1Nonzero : reserve1 ≠ ⟨0⟩)
    (hliquidity :
      liquidity =
        minFunctionResultWord (UInt256.div (UInt256.mul amount0 totalSupply) reserve0)
          (UInt256.div (UInt256.mul amount1 totalSupply) reserve1))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hfitSupplySource : mintFunctionTotalSupplyNewNat evmAfter liquidity < UInt256.size)
    (hsourceOverflow :
      UInt256.size ≤ mintFunctionToBalanceNewNat evmAfter recipient liquidity)
    (rd3762 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3762⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hruntimeSupplyFit :
      (uniswapSlotWord ⟨0⟩ σFee I).toNat + liquidity.toNat < UInt256.size)
    (hruntimeOverflow :
      UInt256.size ≤
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
          (uniswapInternalMintBalanceHashSlot toWord mem)).toNat + liquidity.toNat)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let afterTotalSupplyLocals :=
    nextLocals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))
  let caller : Frame := { contract := contract, locals := afterTotalSupplyLocals }
  let liquidity0 := mintProportionalLiquidityWord amount0 totalSupply reserve0
  let liquidity1 := mintProportionalLiquidityWord amount1 totalSupply reserve1
  let afterBranch :=
    resumeAfterInternalCall
      { contract := contract,
        locals :=
          (afterTotalSupplyLocals.insert "liquidity0"
            (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert
              "liquidity1" (mintProportionalLiquidityValue amount1 totalSupply reserve1) }
      "liquidity" (some (minFunctionResultValue liquidity0 liquidity1))
  have hprefix :=
    uniswapMintAfterMintFeeTotalSupplyPrefix_of_call evmS evm0S evm1S evmAfter I
      nextLocals (by simp only [evmS, initState]; exact hwv) hunlockedSolm hguard0
      hguard1 hcall0 hdec0 hcall1 hdec1 hle0Source hle1Source hfee hbase
  have htoAfterTotal :
      afterTotalSupplyLocals.get? "to" = some (.address recipient) := by
    change (nextLocals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "to" =
        some (.address recipient)
    rw [store_get_ne _ _ (by decide), hto]
  have htotalAfter :
      afterTotalSupplyLocals.get? "_totalSupply" = some (uniswapUint256Value totalSupply) := by
    change (nextLocals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "_totalSupply" =
        some (uniswapUint256Value totalSupply)
    rw [store_get_self]
    simp [htotalEq]
  have hamount0After :
      afterTotalSupplyLocals.get? "amount0" = some (uniswapUint256Value amount0) := by
    change (nextLocals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "amount0" =
        some (uniswapUint256Value amount0)
    rw [store_get_ne _ _ (by decide), hamount0]
  have hamount1After :
      afterTotalSupplyLocals.get? "amount1" = some (uniswapUint256Value amount1) := by
    change (nextLocals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "amount1" =
        some (uniswapUint256Value amount1)
    rw [store_get_ne _ _ (by decide), hamount1]
  have hreserve0After :
      afterTotalSupplyLocals.get? "_reserve0" =
        some (.int (Int.ofNat reserve0.toNat)) := by
    change (nextLocals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "_reserve0" =
        some (.int (Int.ofNat reserve0.toNat))
    rw [store_get_ne _ _ (by decide), hreserve0]
  have hreserve1After :
      afterTotalSupplyLocals.get? "_reserve1" =
        some (.int (Int.ofNat reserve1.toNat)) := by
    change (nextLocals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "_reserve1" =
        some (.int (Int.ofNat reserve1.toNat))
    rw [store_get_ne _ _ (by decide), hreserve1]
  have hbranchStmt :=
    uniswapMintProportionalLiquidityBranchMin (locals := afterTotalSupplyLocals) evmAfter
      amount0 amount1 totalSupply reserve0 reserve1 htotalAfter htotalNonzero hamount0After
      hamount1After hreserve0After hreserve1After
      (by simpa [mintAmountProductNat] using hmulFit0)
      (by simpa [mintAmountProductNat] using hmulFit1) hreserve0Nonzero hreserve1Nonzero
  have hbranch :
      ExecBlock config caller evmAfter [mintLiquidityBranchStmt] (.ok afterBranch evmAfter) := by
    exact ExecBlock.consNormal
      (by
        simpa [caller, afterBranch, liquidity0, liquidity1, hliquidity] using hbranchStmt)
      ExecBlock.nil
  have htoAfter :
      afterBranch.locals.get? "to" = some (.address recipient) := by
    change (((afterTotalSupplyLocals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "to" =
            some (.address recipient)
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), htoAfterTotal]
  have hprop0 :
      mintProportionalLiquidityWord amount0 totalSupply reserve0 =
        UInt256.div (UInt256.mul amount0 totalSupply) reserve0 := by
    simp [mintProportionalLiquidityWord,
      mintAmountProductWord_eq_mul amount0 totalSupply
        (by simpa [mintAmountProductNat] using hmulFit0)]
  have hprop1 :
      mintProportionalLiquidityWord amount1 totalSupply reserve1 =
        UInt256.div (UInt256.mul amount1 totalSupply) reserve1 := by
    simp [mintProportionalLiquidityWord,
      mintAmountProductWord_eq_mul amount1 totalSupply
        (by simpa [mintAmountProductNat] using hmulFit1)]
  have hliqAfter :
      afterBranch.locals.get? "liquidity" = some (uniswapUint256Value liquidity) := by
    change (((afterTotalSupplyLocals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "liquidity" =
            some (uniswapUint256Value liquidity)
    rw [store_get_self]
    rw [hliquidity]
    simp [minFunctionResultValue, liquidity0, liquidity1, hprop0, hprop1]
  have htail :
      ExecBlock config afterBranch evmAfter mintAfterLiquidityTailStmts .reverted := by
    exact uniswapMintAfterLiquidityMintBalanceOverflowReverts evmAfter recipient liquidity
      htoAfter hliqAfter hliqNonzero hfitSupplySource hsourceOverflow
  have hthrough := execBlock_append hprefix (execBlock_append hbranch htail)
  have hbody :
      ExecTransitionBody config contract evmS (mintStore I) mintTransition.body .reverted := by
    exact ExecFuncBody.execBlockRevert (by
      simpa [mintTransition, mintLiquidityBranchStmt, mintInitialLiquidityBranchStmts,
        mintProportionalLiquidityBranchStmts, mintAfterLiquidityTailStmts, caller,
        afterTotalSupplyLocals, List.append_assoc] using hthrough)
  obtain ⟨_, _, rd3841⟩ :=
    uniswapMintRuntimeProportionalLiquidityEntry rd3762 hclean0 hclean1 hmulFit0 hmulFit1
      hreserve0Nonzero hreserve1Nonzero
  obtain ⟨_, _, rd8128⟩ :=
    uniswapMintRuntimeLiquidityMintEntry (by simpa [hliquidity] using rd3841) hliqNonzero
  have rdRev :
      RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    uniswapInternalMintRuntimeBalanceOverflowReverts
      (value := liquidity) (recipient := toWord) (ret := ⟨3914⟩)
      (R := [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel])
      (σ := σFee) rd8128 hperm hruntimeSupplyFit hruntimeOverflow hmem hmem64
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact rdRev.reEquivExecutionRevert hcode hdispatch (uniswapDecode_mint_ok hsz36) hbody

end UniswapV2Pair
