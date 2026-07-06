import Examples.UniswapV2Pair.MintLiquidityZeroRuntime
import Examples.UniswapV2Pair.MintSourceCases

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

theorem uniswapMintAfterMintFeeProportionalLiquidityZeroReverts_of_call
    (evm evm0 evm1 evmAfter : EVM.State) (I : ExecutionEnv) (nextLocals : Store)
    {out0 out1 : ByteArray} {balance0 balance1 amount0 amount1 : UInt256}
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
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
    (henough0 : (uniswapReserve0Word (uniswapLockEnteredState evm)).toNat ≤ balance0.toNat)
    (henough1 : (uniswapReserve1Word (uniswapLockEnteredState evm)).toNat ≤ balance1.toNat)
    (hfee :
      ExecStmt config
        { contract := contract,
          locals := mintAmountStore (uniswapLockEnteredState evm) I balance0 balance1 }
        evm1 (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
        (.ok { contract := contract, locals := nextLocals } evmAfter))
    (htotalBase : nextLocals.get? "totalSupply" = none)
    (hamount0 : nextLocals.get? "amount0" = some (uniswapUint256Value amount0))
    (hamount1 : nextLocals.get? "amount1" = some (uniswapUint256Value amount1))
    (hreserve0 :
      nextLocals.get? "_reserve0" =
        some (.int (Int.ofNat (uniswapReserve0Word (uniswapLockEnteredState evm)).toNat)))
    (hreserve1 :
      nextLocals.get? "_reserve1" =
        some (.int (Int.ofNat (uniswapReserve1Word (uniswapLockEnteredState evm)).toNat)))
    (htotalNonzero : mintFunctionTotalSupplyWord evmAfter ≠ ⟨0⟩)
    (hfit0 : mintAmountProductNat amount0 (mintFunctionTotalSupplyWord evmAfter) < UInt256.size)
    (hfit1 : mintAmountProductNat amount1 (mintFunctionTotalSupplyWord evmAfter) < UInt256.size)
    (hreserve0Nonzero : uniswapReserve0Word (uniswapLockEnteredState evm) ≠ ⟨0⟩)
    (hreserve1Nonzero : uniswapReserve1Word (uniswapLockEnteredState evm) ≠ ⟨0⟩)
    (hliquidity :
      minFunctionResultWord
          (mintProportionalLiquidityWord amount0 (mintFunctionTotalSupplyWord evmAfter)
            (uniswapReserve0Word (uniswapLockEnteredState evm)))
          (mintProportionalLiquidityWord amount1 (mintFunctionTotalSupplyWord evmAfter)
            (uniswapReserve1Word (uniswapLockEnteredState evm))) =
        ⟨0⟩) :
    ExecBlock config { contract := contract, locals := mintStore I } evm
      mintTransition.body .reverted := by
  let totalSupply := mintFunctionTotalSupplyWord evmAfter
  let reserve0 := uniswapReserve0Word (uniswapLockEnteredState evm)
  let reserve1 := uniswapReserve1Word (uniswapLockEnteredState evm)
  let afterTotalSupplyLocals :=
    nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)
  have hprefix :=
    uniswapMintAfterMintFeeTotalSupplyPrefix_of_call evm evm0 evm1 evmAfter I nextLocals
      hwv hunlocked hguard0 hguard1 hcall0 hdec0 hcall1 hdec1 henough0 henough1 hfee
      htotalBase
  have htotal' :
      afterTotalSupplyLocals.get? "_totalSupply" =
        some (uniswapUint256Value totalSupply) := by
    change (nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)).get?
      "_totalSupply" = some (uniswapUint256Value totalSupply)
    rw [store_get_self]
  have hamount0' :
      afterTotalSupplyLocals.get? "amount0" = some (uniswapUint256Value amount0) := by
    change (nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)).get?
      "amount0" = some (uniswapUint256Value amount0)
    rw [store_get_ne _ _ (by decide), hamount0]
  have hamount1' :
      afterTotalSupplyLocals.get? "amount1" = some (uniswapUint256Value amount1) := by
    change (nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)).get?
      "amount1" = some (uniswapUint256Value amount1)
    rw [store_get_ne _ _ (by decide), hamount1]
  have hreserve0' :
      afterTotalSupplyLocals.get? "_reserve0" =
        some (.int (Int.ofNat reserve0.toNat)) := by
    change (nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)).get?
      "_reserve0" = some (.int (Int.ofNat reserve0.toNat))
    rw [store_get_ne _ _ (by decide)]
    simpa [reserve0] using hreserve0
  have hreserve1' :
      afterTotalSupplyLocals.get? "_reserve1" =
        some (.int (Int.ofNat reserve1.toNat)) := by
    change (nextLocals.insert "_totalSupply" (uniswapUint256Value totalSupply)).get?
      "_reserve1" = some (.int (Int.ofNat reserve1.toNat))
    rw [store_get_ne _ _ (by decide)]
    simpa [reserve1] using hreserve1
  have htail :
      ExecBlock config { contract := contract, locals := afterTotalSupplyLocals } evmAfter
        ([mintLiquidityBranchStmt] ++ mintAfterLiquidityTailStmts) .reverted := by
    simpa [afterTotalSupplyLocals, totalSupply, reserve0, reserve1, List.append_assoc] using
      uniswapMintProportionalLiquidityZeroReverts
        (locals := afterTotalSupplyLocals) evmAfter amount0 amount1 totalSupply reserve0
        reserve1 htotal' (by simpa [totalSupply] using htotalNonzero) hamount0'
        hamount1' hreserve0' hreserve1' (by simpa [totalSupply] using hfit0)
        (by simpa [totalSupply] using hfit1) (by simpa [reserve0] using hreserve0Nonzero)
        (by simpa [reserve1] using hreserve1Nonzero)
        (by simpa [totalSupply, reserve0, reserve1] using hliquidity)
  have hthrough := execBlock_append hprefix htail
  simpa [mintTransition, mintLiquidityBranchStmt, mintInitialLiquidityBranchStmts,
    mintProportionalLiquidityBranchStmts, mintAfterLiquidityTailStmts, List.append_assoc,
    afterTotalSupplyLocals, totalSupply, reserve0, reserve1] using hthrough

set_option maxHeartbeats 1000000 in
theorem uniswapMintProportionalLiquidityZeroAfterMintFeeCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 mem rdata : ByteArray} {k C : ℕ}
    {feeOnFlag totalSupply amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel :
      UInt256}
    (nextLocals : Store)
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
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) I balance0 balance1 }
        evm1S (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
        (.ok { contract := contract, locals := nextLocals } evmFeeS))
    (rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [feeOnFlag, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (htotalBase : nextLocals.get? "totalSupply" = none)
    (hamount0 : nextLocals.get? "amount0" = some (uniswapUint256Value amount0))
    (hamount1 : nextLocals.get? "amount1" = some (uniswapUint256Value amount1))
    (hreserve0 :
      nextLocals.get? "_reserve0" =
        some
          (.int
            (Int.ofNat
              (uniswapReserve0Word
                (uniswapLockEnteredState
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).toNat)))
    (hreserve1 :
      nextLocals.get? "_reserve1" =
        some
          (.int
            (Int.ofNat
              (uniswapReserve1Word
                (uniswapLockEnteredState
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).toNat)))
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = totalSupply)
    (htotalSlot : uniswapSlotWord ⟨0⟩ σFee I = totalSupply)
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
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
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hmulFit0 : amount0.toNat * totalSupply.toNat < UInt256.size)
    (hmulFit1 : amount1.toNat * totalSupply.toNat < UInt256.size)
    (hreserve0Nonzero : reserve0 ≠ ⟨0⟩)
    (hreserve1Nonzero : reserve1 ≠ ⟨0⟩)
    (hliquidityRuntime :
      minFunctionResultWord ((amount0.mul totalSupply).div reserve0)
          ((amount1.mul totalSupply).div reserve1) =
        ⟨0⟩)
    (hliquiditySource :
      minFunctionResultWord
          (mintProportionalLiquidityWord amount0 totalSupply reserve0)
          (mintProportionalLiquidityWord amount1 totalSupply reserve1) =
        ⟨0⟩)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hreserve0EqS : uniswapReserve0Word (uniswapLockEnteredState evmS) = reserve0 := by
    simpa [evmS] using hreserve0Eq
  have hreserve1EqS : uniswapReserve1Word (uniswapLockEnteredState evmS) = reserve1 := by
    simpa [evmS] using hreserve1Eq
  have hbody :
      ExecTransitionBody config contract evmS (mintStore I) mintTransition.body .reverted := by
    exact ExecFuncBody.execBlockRevert
      (uniswapMintAfterMintFeeProportionalLiquidityZeroReverts_of_call
        evmS evm0S evm1S evmFeeS I nextLocals
        (by simp only [evmS, initState]; exact hwv) hunlockedSolm hguard0 hguard1
        hcall0 hdec0 hcall1 hdec1 hle0Source hle1Source
        (by simpa [evmS] using hfee) htotalBase hamount0 hamount1 hreserve0 hreserve1
        (by simpa [htotalEq] using htotalNonzero)
        (by simpa [mintAmountProductNat, htotalEq] using hmulFit0)
        (by simpa [mintAmountProductNat, htotalEq] using hmulFit1)
        (by simpa [hreserve0EqS] using hreserve0Nonzero)
        (by simpa [hreserve1EqS] using hreserve1Nonzero)
        (by simpa [htotalEq, hreserve0EqS, hreserve1EqS] using hliquiditySource))
  obtain ⟨_, _, rd3762⟩ :=
    uniswapMintRuntimeAfterMintFeeTotalSupplyNonzero rd3701 htotalSlot htotalNonzero
  obtain ⟨_, _, rd3841⟩ :=
    uniswapMintRuntimeProportionalLiquidityEntry rd3762 hclean0 hclean1 hmulFit0 hmulFit1
      hreserve0Nonzero hreserve1Nonzero
  have rdRev :
      RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
    exact uniswapMintRuntimeLiquidityZeroReverts rd3841
      (by simpa [UInt256.mul, UInt256.div] using hliquidityRuntime) hmem hmem64
  exact rdRev.reEquivExecutionRevert hcode hdispatch (uniswapDecode_mint_ok hsz36) hbody

set_option maxHeartbeats 1000000 in
theorem uniswapMintProportionalFeeOffKLastZeroLiquidityZeroFromFactoryCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σ'' : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 outFee o o1 : ByteArray} {k C : ℕ}
    {totalSupply amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
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
    (hfeeCall : typedCallViaEVM config evm1S
      (EVM.address (uniswapAddressAtSlot evm1S ⟨5⟩)) "feeTo" 0 []
      (true, evmFeeS, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some (.address feeTo))
    (hfeeToEq : feeTo = AccountAddress.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
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
      (feeToStaticcallMem
        (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
        outFee)
      feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (ho132 : 32 ≤ o1.size) (ho1Size : o1.size < UInt256.size)
    (houtFeeSize : outFee.size < UInt256.size)
    (hzFeeTrue : zFee = true)
    (houtFee32 : 32 ≤ outFee.size)
    (hkLastEq : mintFeeKLastWord evmFeeS = mintFeeKLastSlotWord σFee I)
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = totalSupply)
    (htotalSlot : uniswapSlotWord ⟨0⟩ σFee I = totalSupply)
    (hruntimeReserve0 :
      reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I = reserve0)
    (hruntimeReserve1 :
      reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I = reserve1)
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
    (hamount0Eq :
      mintAmount0Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance0 =
        amount0)
    (hamount1Eq :
      mintAmount1Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance1 =
        amount1)
    (hzero :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
          solcAddrMask =
        ⟨0⟩ ∧
      mintFeeKLastSlotWord σFee I = ⟨0⟩ ∧
      totalSupply ≠ ⟨0⟩ ∧
      amount0.toNat * totalSupply.toNat < UInt256.size ∧
      amount1.toNat * totalSupply.toNat < UInt256.size ∧
      reserve0 ≠ ⟨0⟩ ∧ reserve1 ≠ ⟨0⟩ ∧
      minFunctionResultWord ((amount0.mul totalSupply).div reserve0)
          ((amount1.mul totalSupply).div reserve1) =
        ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  rcases hzero with
    ⟨hfeeToZero, hkLastZero, htotalNonzero, hmulFit0, hmulFit1, hreserve0Nonzero,
      hreserve1Nonzero, hliqZero⟩
  have hfeeToAddr : feeTo = AccountAddress.ofNat 0 := by
    rw [hfeeToEq]
    exact accountAddress_ofNat_eq_zero_of_land_solcAddrMask_eq_zero
      (fromByteArrayBigEndian_extract0_32_lt houtFee32) hfeeToZero
  have hkLastSource : (mintFeeKLastWord evmFeeS).toNat = 0 := by
    rw [hkLastEq, hkLastZero]
    rfl
  have hclean0 : UInt256.land reserve0 reserve112Mask = reserve0 :=
    reserve112Mask_clean_of_lt _ (by
      rw [← hruntimeReserve0]
      dsimp [reserve0Word]
      exact reserve112Word_lt _)
  have hclean1 : UInt256.land reserve1 reserve112Mask = reserve1 :=
    reserve112Mask_clean_of_lt _ (by
      rw [← hruntimeReserve1]
      dsimp [reserve1Word]
      exact reserve112Word_lt _)
  have hprod0 :
      mintAmountProductWord amount0 totalSupply = UInt256.mul amount0 totalSupply :=
    mintAmountProductWord_eq_mul amount0 totalSupply hmulFit0
  have hprod1 :
      mintAmountProductWord amount1 totalSupply = UInt256.mul amount1 totalSupply :=
    mintAmountProductWord_eq_mul amount1 totalSupply hmulFit1
  have hliqSource :
      minFunctionResultWord
          (mintProportionalLiquidityWord amount0 totalSupply reserve0)
          (mintProportionalLiquidityWord amount1 totalSupply reserve1) =
        ⟨0⟩ := by
    simpa [mintProportionalLiquidityWord, hprod0, hprod1] using hliqZero
  obtain ⟨k3701, C3701, rd3701Raw⟩ :=
    uniswapMintFeeRuntimeFactoryResultFeeOffKLastZeroReturn
      rd7781 ho32 hoSize ho132 ho1Size houtFeeSize hzFeeTrue houtFee32 hfeeToZero
      hkLastZero
  have rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨0⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      (feeToStaticcallMem
        (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
        outFee)
      feeToStaticcallActiveWords outFee (cAFee, σFee) k3701 C3701 := by
    simpa [hruntimeReserve0, hruntimeReserve1] using rd3701Raw
  have hmem :
      (feeToStaticcallMem
        (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
        outFee).size = 164 :=
    feeToStaticcallMem_size_of_size_ge
      (UInt256.ofNat I.codeOwner.val) o o1 outFee ho32 hoSize ho132 ho1Size houtFee32
      houtFeeSize
  have hmem64 :
      (feeToStaticcallMem
        (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
        outFee).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    feeToStaticcallMem_read64_of_size_ge
      (UInt256.ofNat I.codeOwner.val) o o1 outFee ho32 hoSize ho132 ho1Size houtFee32
      houtFeeSize
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmL := uniswapLockEnteredState evmS
  let nextFrame :=
    resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
      "feeOn" (some (.bool false))
  have hreserve0Eq' : uniswapReserve0Word evmL = reserve0 := by
    simpa [evmL, evmS] using hreserve0Eq
  have hreserve1Eq' : uniswapReserve1Word evmL = reserve1 := by
    simpa [evmL, evmS] using hreserve1Eq
  have hamount0Eq' : mintAmount0Word evmL balance0 = amount0 := by
    simpa [evmL, evmS] using hamount0Eq
  have hamount1Eq' : mintAmount1Word evmL balance1 = amount1 := by
    simpa [evmL, evmS] using hamount1Eq
  exact uniswapMintProportionalLiquidityZeroAfterMintFeeCase nextFrame.locals hcode
    hdispatch hsz36 hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1
    hle0Source hle1Source
    (by
      simpa [nextFrame, evmL, resumeAfterInternalCall] using
        uniswapMintFeeCallFromMint_feeOff_kLastZero evmL evm1S evmFeeS I balance0
          balance1 feeTo (by simpa [evmL] using hfeeGuard) hfeeCall hfeeDec
          hfeeToAddr hkLastSource)
    rd3701
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_totalSupply evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL, hamount0Eq', mintAmount0Value] using
      mintAfterMintFeeCallStore_amount0 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL, hamount1Eq', mintAmount1Value] using
      mintAfterMintFeeCallStore_amount1 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL, evmS, hreserve0Eq'] using
      mintAfterMintFeeCallStore_reserve0 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL, evmS, hreserve1Eq'] using
      mintAfterMintFeeCallStore_reserve1 evmL I balance0 balance1 false)
    htotalEq htotalSlot htotalNonzero hreserve0Eq hreserve1Eq hclean0 hclean1 hmulFit0
    hmulFit1 hreserve0Nonzero hreserve1Nonzero hliqZero hliqSource hmem hmem64

set_option maxHeartbeats 1000000 in
theorem uniswapMintProportionalFeeOffKLastZeroLiquidityZeroCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 outFee mem rdata : ByteArray} {k C : ℕ}
    {totalSupply amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
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
    (hfeeCall : typedCallViaEVM config evm1S
      (EVM.address (uniswapAddressAtSlot evm1S ⟨5⟩)) "feeTo" 0 []
      (true, evmFeeS, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some (.address feeTo))
    (hfeeToAddr : feeTo = AccountAddress.ofNat 0)
    (hkLastSource : (mintFeeKLastWord evmFeeS).toNat = 0)
    (rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨0⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = totalSupply)
    (htotalSlot : uniswapSlotWord ⟨0⟩ σFee I = totalSupply)
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
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
    (hamount0Eq :
      mintAmount0Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance0 =
        amount0)
    (hamount1Eq :
      mintAmount1Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance1 =
        amount1)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hmulFit0 : amount0.toNat * totalSupply.toNat < UInt256.size)
    (hmulFit1 : amount1.toNat * totalSupply.toNat < UInt256.size)
    (hreserve0Nonzero : reserve0 ≠ ⟨0⟩)
    (hreserve1Nonzero : reserve1 ≠ ⟨0⟩)
    (hliquidityRuntime :
      minFunctionResultWord ((amount0.mul totalSupply).div reserve0)
          ((amount1.mul totalSupply).div reserve1) =
        ⟨0⟩)
    (hliquiditySource :
      minFunctionResultWord
          (mintProportionalLiquidityWord amount0 totalSupply reserve0)
          (mintProportionalLiquidityWord amount1 totalSupply reserve1) =
        ⟨0⟩)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmL := uniswapLockEnteredState evmS
  let nextFrame :=
    resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
      "feeOn" (some (.bool false))
  have hreserve0Eq' : uniswapReserve0Word evmL = reserve0 := by
    simpa [evmL, evmS] using hreserve0Eq
  have hreserve1Eq' : uniswapReserve1Word evmL = reserve1 := by
    simpa [evmL, evmS] using hreserve1Eq
  have hreserve0EqS : uniswapReserve0Word (uniswapLockEnteredState evmS) = reserve0 := by
    simpa [evmS] using hreserve0Eq
  have hreserve1EqS : uniswapReserve1Word (uniswapLockEnteredState evmS) = reserve1 := by
    simpa [evmS] using hreserve1Eq
  have hamount0Eq' : mintAmount0Word evmL balance0 = amount0 := by
    simpa [evmL, evmS] using hamount0Eq
  have hamount1Eq' : mintAmount1Word evmL balance1 = amount1 := by
    simpa [evmL, evmS] using hamount1Eq
  have hbody :
      ExecTransitionBody config contract evmS (mintStore I) mintTransition.body .reverted := by
    exact ExecFuncBody.execBlockRevert
      (uniswapMintAfterMintFeeProportionalLiquidityZeroReverts_of_call
        evmS evm0S evm1S evmFeeS I nextFrame.locals
        (by simp only [evmS, initState]; exact hwv) hunlockedSolm hguard0 hguard1
        hcall0 hdec0 hcall1 hdec1 hle0Source hle1Source
        (by
          simpa [nextFrame, evmL, resumeAfterInternalCall] using
            uniswapMintFeeCallFromMint_feeOff_kLastZero evmL evm1S evmFeeS I balance0
              balance1 feeTo (by simpa [evmL] using hfeeGuard) hfeeCall hfeeDec
              hfeeToAddr hkLastSource)
        (by simpa [nextFrame, evmL] using
          mintAfterMintFeeCallStore_totalSupply evmL I balance0 balance1 false)
        (by simpa [nextFrame, evmL, hamount0Eq', mintAmount0Value] using
          mintAfterMintFeeCallStore_amount0 evmL I balance0 balance1 false)
        (by simpa [nextFrame, evmL, hamount1Eq', mintAmount1Value] using
          mintAfterMintFeeCallStore_amount1 evmL I balance0 balance1 false)
        (by simpa [nextFrame, evmL, hreserve0Eq'] using
          mintAfterMintFeeCallStore_reserve0 evmL I balance0 balance1 false)
        (by simpa [nextFrame, evmL, hreserve1Eq'] using
          mintAfterMintFeeCallStore_reserve1 evmL I balance0 balance1 false)
        (by simpa [htotalEq] using htotalNonzero)
        (by simpa [mintAmountProductNat, htotalEq, hamount0Eq'] using hmulFit0)
        (by simpa [mintAmountProductNat, htotalEq, hamount1Eq'] using hmulFit1)
        (by simpa [hreserve0EqS] using hreserve0Nonzero)
        (by simpa [hreserve1EqS] using hreserve1Nonzero)
        (by
          simpa [htotalEq, hreserve0EqS, hreserve1EqS, hamount0Eq', hamount1Eq'] using
            hliquiditySource))
  obtain ⟨_, _, rd3762⟩ :=
    uniswapMintRuntimeAfterMintFeeTotalSupplyNonzero rd3701 htotalSlot htotalNonzero
  obtain ⟨_, _, rd3841⟩ :=
    uniswapMintRuntimeProportionalLiquidityEntry rd3762 hclean0 hclean1 hmulFit0 hmulFit1
      hreserve0Nonzero hreserve1Nonzero
  have rdRev :
      RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
    exact uniswapMintRuntimeLiquidityZeroReverts rd3841
      (by simpa [UInt256.mul, UInt256.div] using hliquidityRuntime) hmem hmem64
  exact rdRev.reEquivExecutionRevert hcode hdispatch (uniswapDecode_mint_ok hsz36) hbody

set_option maxHeartbeats 1000000 in
theorem uniswapMintProportionalFeeOnKLastZeroLiquidityZeroCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 outFee mem rdata : ByteArray} {k C : ℕ}
    {totalSupply amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
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
    (hfeeCall : typedCallViaEVM config evm1S
      (EVM.address (uniswapAddressAtSlot evm1S ⟨5⟩)) "feeTo" 0 []
      (true, evmFeeS, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some (.address feeTo))
    (hfeeToAddr : feeTo ≠ AccountAddress.ofNat 0)
    (hkLastSource : (mintFeeKLastWord evmFeeS).toNat = 0)
    (rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨1⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = totalSupply)
    (htotalSlot : uniswapSlotWord ⟨0⟩ σFee I = totalSupply)
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
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
    (hamount0Eq :
      mintAmount0Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance0 =
        amount0)
    (hamount1Eq :
      mintAmount1Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance1 =
        amount1)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hmulFit0 : amount0.toNat * totalSupply.toNat < UInt256.size)
    (hmulFit1 : amount1.toNat * totalSupply.toNat < UInt256.size)
    (hreserve0Nonzero : reserve0 ≠ ⟨0⟩)
    (hreserve1Nonzero : reserve1 ≠ ⟨0⟩)
    (hliquidityRuntime :
      minFunctionResultWord ((amount0.mul totalSupply).div reserve0)
          ((amount1.mul totalSupply).div reserve1) =
        ⟨0⟩)
    (hliquiditySource :
      minFunctionResultWord
          (mintProportionalLiquidityWord amount0 totalSupply reserve0)
          (mintProportionalLiquidityWord amount1 totalSupply reserve1) =
        ⟨0⟩)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmL := uniswapLockEnteredState evmS
  let nextFrame :=
    resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
      "feeOn" (some (.bool true))
  have hamount0Eq' : mintAmount0Word evmL balance0 = amount0 := by
    simpa [evmL, evmS] using hamount0Eq
  have hamount1Eq' : mintAmount1Word evmL balance1 = amount1 := by
    simpa [evmL, evmS] using hamount1Eq
  have hreserve0Eq' : uniswapReserve0Word evmL = reserve0 := by
    simpa [evmL, evmS] using hreserve0Eq
  have hreserve1Eq' : uniswapReserve1Word evmL = reserve1 := by
    simpa [evmL, evmS] using hreserve1Eq
  exact uniswapMintProportionalLiquidityZeroAfterMintFeeCase nextFrame.locals hcode hdispatch
    hsz36 hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1 hle0Source hle1Source
    (by
      simpa [nextFrame, evmL, resumeAfterInternalCall] using
        uniswapMintFeeCallFromMint_feeOn_kLastZero evmL evm1S evmFeeS I balance0 balance1
          feeTo (by simpa [evmL] using hfeeGuard) hfeeCall hfeeDec hfeeToAddr
          hkLastSource)
    rd3701
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_totalSupply evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL, hamount0Eq', mintAmount0Value] using
      mintAfterMintFeeCallStore_amount0 evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL, hamount1Eq', mintAmount1Value] using
      mintAfterMintFeeCallStore_amount1 evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL, evmS] using
      mintAfterMintFeeCallStore_reserve0 evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL, evmS] using
      mintAfterMintFeeCallStore_reserve1 evmL I balance0 balance1 true)
    htotalEq htotalSlot htotalNonzero hreserve0Eq hreserve1Eq
    hclean0 hclean1 hmulFit0 hmulFit1 hreserve0Nonzero hreserve1Nonzero hliquidityRuntime
    hliquiditySource hmem hmem64

set_option maxHeartbeats 1000000 in
theorem uniswapMintProportionalFeeOffKLastNonzeroLiquidityZeroCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σCleared : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 outFee mem rdata : ByteArray} {k C : ℕ}
    {totalSupply amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
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
    (hfeeCall : typedCallViaEVM config evm1S
      (EVM.address (uniswapAddressAtSlot evm1S ⟨5⟩)) "feeTo" 0 []
      (true, evmFeeS, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some (.address feeTo))
    (hfeeToAddr : feeTo = AccountAddress.ofNat 0)
    (hkLastSource : (mintFeeKLastWord evmFeeS).toNat ≠ 0)
    (rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨0⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σCleared) k C)
    (htotalEq : mintFunctionTotalSupplyWord (mintFeeKLastClearedState evmFeeS) = totalSupply)
    (htotalSlot : uniswapSlotWord ⟨0⟩ σCleared I = totalSupply)
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
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
    (hamount0Eq :
      mintAmount0Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance0 =
        amount0)
    (hamount1Eq :
      mintAmount1Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance1 =
        amount1)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hmulFit0 : amount0.toNat * totalSupply.toNat < UInt256.size)
    (hmulFit1 : amount1.toNat * totalSupply.toNat < UInt256.size)
    (hreserve0Nonzero : reserve0 ≠ ⟨0⟩)
    (hreserve1Nonzero : reserve1 ≠ ⟨0⟩)
    (hliquidityRuntime :
      minFunctionResultWord ((amount0.mul totalSupply).div reserve0)
          ((amount1.mul totalSupply).div reserve1) =
        ⟨0⟩)
    (hliquiditySource :
      minFunctionResultWord
          (mintProportionalLiquidityWord amount0 totalSupply reserve0)
          (mintProportionalLiquidityWord amount1 totalSupply reserve1) =
        ⟨0⟩)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmL := uniswapLockEnteredState evmS
  let nextFrame :=
    resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
      "feeOn" (some (.bool false))
  have hamount0Eq' : mintAmount0Word evmL balance0 = amount0 := by
    simpa [evmL, evmS] using hamount0Eq
  have hamount1Eq' : mintAmount1Word evmL balance1 = amount1 := by
    simpa [evmL, evmS] using hamount1Eq
  have hreserve0Eq' : uniswapReserve0Word evmL = reserve0 := by
    simpa [evmL, evmS] using hreserve0Eq
  have hreserve1Eq' : uniswapReserve1Word evmL = reserve1 := by
    simpa [evmL, evmS] using hreserve1Eq
  exact uniswapMintProportionalLiquidityZeroAfterMintFeeCase nextFrame.locals hcode hdispatch
    hsz36 hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1 hle0Source hle1Source
    (by
      simpa [nextFrame, evmL, resumeAfterInternalCall] using
        uniswapMintFeeCallFromMint_feeOff_kLastNonzero evmL evm1S evmFeeS I balance0
          balance1 feeTo (by simpa [evmL] using hfeeGuard) hfeeCall hfeeDec hfeeToAddr
          hkLastSource)
    rd3701
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_totalSupply evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL, hamount0Eq', mintAmount0Value] using
      mintAfterMintFeeCallStore_amount0 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL, hamount1Eq', mintAmount1Value] using
      mintAfterMintFeeCallStore_amount1 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL, evmS] using
      mintAfterMintFeeCallStore_reserve0 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL, evmS] using
      mintAfterMintFeeCallStore_reserve1 evmL I balance0 balance1 false)
    htotalEq htotalSlot htotalNonzero hreserve0Eq hreserve1Eq hclean0 hclean1 hmulFit0
    hmulFit1 hreserve0Nonzero hreserve1Nonzero hliquidityRuntime hliquiditySource hmem
    hmem64

end UniswapV2Pair
