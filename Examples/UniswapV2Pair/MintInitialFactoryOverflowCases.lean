import Examples.UniswapV2Pair.MintInitialMinimumMintReverts
import Examples.UniswapV2Pair.MintRuntimeFitBridge

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

set_option maxHeartbeats 1000000 in
theorem uniswapMintInitialMinimumMintBalanceOverflowFromAfterFeeCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {evm0S evm1S evmAfter : EVM.State}
    {out0 out1 mem rdata : ByteArray} {k C : ℕ}
    {feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
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
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) I balance0
              balance1 }
        evm1S (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
        (.ok { contract := contract, locals := nextLocals } evmAfter))
    (hbase : nextLocals.get? "totalSupply" = none)
    (hamount0Get : nextLocals.get? "amount0" = some (uniswapUint256Value amount0))
    (hamount1Get : nextLocals.get? "amount1" = some (uniswapUint256Value amount1))
    (hPostAccountsAfter : accountMapEquiv σFee evmAfter.accountMap)
    (henvAfterI : evmAfter.executionEnv = I)
    (htotalSource : mintFunctionTotalSupplyWord evmAfter = ⟨0⟩)
    (htotalRuntimeZero : uniswapSlotWord ⟨0⟩ σFee I = ⟨0⟩)
    (hfit : amount0.toNat * amount1.toNat < UInt256.size)
    (rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [feeOn, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hruntimeOverflow :
      UInt256.size ≤
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem)).toNat +
          (⟨1000⟩ : UInt256).toNat)
    (hperm : I.perm = true)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let afterTotalSupplyLocals :=
    nextLocals.insert "_totalSupply" (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))
  let caller : Frame := { contract := contract, locals := afterTotalSupplyLocals }
  have hamount0After :
      afterTotalSupplyLocals.get? "amount0" = some (uniswapUint256Value amount0) := by
    dsimp [afterTotalSupplyLocals]
    change (Std.HashMap.insert nextLocals "_totalSupply"
        (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "amount0" =
      some (uniswapUint256Value amount0)
    rw [store_get_ne nextLocals (k := "_totalSupply") (a := "amount0")
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter)) (by decide)]
    exact hamount0Get
  have hamount1After :
      afterTotalSupplyLocals.get? "amount1" = some (uniswapUint256Value amount1) := by
    dsimp [afterTotalSupplyLocals]
    change (Std.HashMap.insert nextLocals "_totalSupply"
        (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "amount1" =
      some (uniswapUint256Value amount1)
    rw [store_get_ne nextLocals (k := "_totalSupply") (a := "amount1")
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter)) (by decide)]
    exact hamount1Get
  have hargs :
      evalExprs? config caller evmAfter
        [u256 (.binary .mul (.var "amount0") (.var "amount1"))] =
          .ok [sqrtFunctionYValue (mintAmountProductWord amount0 amount1)] := by
    simpa [caller] using
      evalExprs_mint_initialSqrtArg_of_get evmAfter amount0 amount1 hamount0After
        hamount1After (by simpa [mintAmountProductNat] using hfit)
  obtain ⟨root, _, _, hsqrt, _, hrootSize, rd2531⟩ :=
    mintInitialLiquiditySqrtPrefixRuntimeBounded
      (caller := caller) (evm := evmAfter) rfl hargs rd3701 htotalRuntimeZero
      (by simpa [mintAmountProductNat] using hfit)
  by_cases hrootLt : root < minimumLiquidity
  · exact uniswapMintInitialAfterMintFeeRootUnderflowRevertCase nextLocals root
      hcode hdispatch hsz36 hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1
      hdec1 hle0Source hle1Source hfee hbase htotalSource
      (by simpa [caller, afterTotalSupplyLocals] using hsqrt) rd2531 hrootSize hrootLt
      hmem hmem64
  · have hrootGeMin : minimumLiquidity ≤ root := le_of_not_gt hrootLt
    let liquidity := UInt256.ofNat (root - minimumLiquidity).toNat
    have hsourceSupplyFit :
        mintFunctionTotalSupplyNewNat evmAfter (⟨1000⟩ : UInt256) < UInt256.size := by
      simp [mintFunctionTotalSupplyNewNat, htotalSource]
      native_decide
    have hruntimeSupplyFit :
        (uniswapSlotWord ⟨0⟩ σFee I).toNat + (⟨1000⟩ : UInt256).toNat <
          UInt256.size := by
      rw [htotalRuntimeZero]
      native_decide
    have hsourceBalanceEq :
        mintFunctionToBalanceNewNat evmAfter (AccountAddress.ofNat 0)
            (⟨1000⟩ : UInt256) =
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem)).toNat +
            (⟨1000⟩ : UInt256).toNat := by
      simpa using
        mintFunctionToBalanceNewNat_eq_runtimeMintRecipient
          (σ := σFee) (evm := evmAfter) (I := I) (mem := mem)
          (liquidity := (⟨1000⟩ : UInt256)) (recipientWord := ⟨0⟩)
          (recipient := AccountAddress.ofNat 0)
          hPostAccountsAfter henvAfterI rfl (by rw [hmem]; omega) hsourceSupplyFit
    have hsourceOverflow :
        UInt256.size ≤
          mintFunctionToBalanceNewNat evmAfter (AccountAddress.ofNat 0)
            (⟨1000⟩ : UInt256) := by
      rw [hsourceBalanceEq]
      exact hruntimeOverflow
    exact uniswapMintInitialAfterMintFeeMinimumMintBalanceOverflowRevertCase
      (liquidity := liquidity) nextLocals root hcode hdispatch hsz36 hwv
      hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1 hle0Source hle1Source
      hfee hbase htotalSource (by simpa [caller, afterTotalSupplyLocals] using hsqrt)
      rd2531 hrootSize hrootGeMin rfl hsourceSupplyFit hsourceOverflow
      hruntimeSupplyFit hruntimeOverflow hperm hmem hmem64

set_option maxHeartbeats 1000000 in
theorem uniswapMintInitialFeeOffKLastZeroMinimumMintBalanceOverflowFromFactoryCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σ'' : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 outFee o o1 : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 toWord sel : UInt256} {zFee : Bool}
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
    (hPostAccountsFee : accountMapEquiv σFee evmFeeS.accountMap)
    (henvFeeI : evmFeeS.executionEnv = I)
    (hperm : I.perm = true)
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
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = uniswapSlotWord ⟨0⟩ σFee I)
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
    (hfeeToZero :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
          solcAddrMask =
        ⟨0⟩)
    (hkLastZero : mintFeeKLastSlotWord σFee I = ⟨0⟩)
    (htotalZero : uniswapSlotWord ⟨0⟩ σFee I = ⟨0⟩)
    (hfit : amount0.toNat * amount1.toNat < UInt256.size)
    (hbalanceOverflow :
      UInt256.size ≤
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (feeToStaticcallMem
              (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
              outFee))).toNat +
          (⟨1000⟩ : UInt256).toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmL := uniswapLockEnteredState evmS
  let nextFrame :=
    resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
      "feeOn" (some (.bool false))
  let afterTotalSupplyLocals :=
    nextFrame.locals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmFeeS))
  let caller : Frame := { contract := contract, locals := afterTotalSupplyLocals }
  let memFee :=
    feeToStaticcallMem
      (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
      outFee
  have hmem : memFee.size = 164 := by
    dsimp [memFee]
    exact feeToStaticcallMem_size_of_size_ge
      (UInt256.ofNat I.codeOwner.val) o o1 outFee ho32 hoSize ho132 ho1Size houtFee32
      houtFeeSize
  have hmem64 : memFee.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [memFee]
    exact feeToStaticcallMem_read64_of_size_ge
      (UInt256.ofNat I.codeOwner.val) o o1 outFee ho32 hoSize ho132 ho1Size houtFee32
      houtFeeSize
  have hfeeToAddr : feeTo = AccountAddress.ofNat 0 := by
    rw [hfeeToEq]
    exact accountAddress_ofNat_eq_zero_of_land_solcAddrMask_eq_zero
      (fromByteArrayBigEndian_extract0_32_lt houtFee32) hfeeToZero
  have hkLastSource : (mintFeeKLastWord evmFeeS).toNat = 0 := by
    rw [hkLastEq, hkLastZero]
    rfl
  have htotalSource : mintFunctionTotalSupplyWord evmFeeS = ⟨0⟩ := by
    rw [htotalEq, htotalZero]
  have hfitSource :
      mintAmountProductNat
          (mintAmount0Word
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance0)
          (mintAmount1Word
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance1) <
        UInt256.size := by
    simpa [mintAmountProductNat, hamount0Eq, hamount1Eq] using hfit
  obtain ⟨_, _, rd3701⟩ :=
    uniswapMintFeeRuntimeFactoryResultFeeOffKLastZeroReturn
      rd7781 ho32 hoSize ho132 ho1Size houtFeeSize hzFeeTrue houtFee32 hfeeToZero
      hkLastZero
  have hamount0Get :
      afterTotalSupplyLocals.get? "amount0" = some (uniswapUint256Value amount0) := by
    dsimp [afterTotalSupplyLocals]
    change (Std.HashMap.insert nextFrame.locals "_totalSupply"
        (uniswapUint256Value (mintFunctionTotalSupplyWord evmFeeS))).get? "amount0" =
      some (uniswapUint256Value amount0)
    rw [store_get_ne nextFrame.locals (k := "_totalSupply") (a := "amount0")
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmFeeS)) (by decide)]
    simpa [nextFrame, evmL, evmS, mintAmount0Value, hamount0Eq] using
      mintAfterMintFeeCallStore_amount0 evmL I balance0 balance1 false
  have hamount1Get :
      afterTotalSupplyLocals.get? "amount1" = some (uniswapUint256Value amount1) := by
    dsimp [afterTotalSupplyLocals]
    change (Std.HashMap.insert nextFrame.locals "_totalSupply"
        (uniswapUint256Value (mintFunctionTotalSupplyWord evmFeeS))).get? "amount1" =
      some (uniswapUint256Value amount1)
    rw [store_get_ne nextFrame.locals (k := "_totalSupply") (a := "amount1")
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmFeeS)) (by decide)]
    simpa [nextFrame, evmL, evmS, mintAmount1Value, hamount1Eq] using
      mintAfterMintFeeCallStore_amount1 evmL I balance0 balance1 false
  have hargs :
      evalExprs? config caller evmFeeS
        [u256 (.binary .mul (.var "amount0") (.var "amount1"))] =
          .ok [sqrtFunctionYValue (mintAmountProductWord amount0 amount1)] := by
    simpa [caller] using
      evalExprs_mint_initialSqrtArg_of_get evmFeeS amount0 amount1 hamount0Get
        hamount1Get (by simpa [mintAmountProductNat] using hfit)
  obtain ⟨root, _, _, hsqrt, _, hrootSize, rd2531⟩ :=
    mintInitialLiquiditySqrtPrefixRuntimeBounded
      (caller := caller) (evm := evmFeeS) rfl hargs rd3701 htotalZero
      (by simpa [mintAmountProductNat] using hfit)
  by_cases hrootLt : root < minimumLiquidity
  · exact uniswapMintInitialAfterMintFeeRootUnderflowRevertCase nextFrame.locals root
      hcode hdispatch hsz36 hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1
      hdec1 hle0Source hle1Source
      (by
        simpa [nextFrame, evmL, evmS, resumeAfterInternalCall] using
          uniswapMintFeeCallFromMint_feeOff_kLastZero evmL evm1S evmFeeS I balance0
            balance1 feeTo (by simpa [evmL, evmS] using hfeeGuard) hfeeCall hfeeDec
            hfeeToAddr hkLastSource)
      (by
        simpa [nextFrame, evmL, evmS] using
          mintAfterMintFeeCallStore_totalSupply evmL I balance0 balance1 false)
      htotalSource (by simpa [caller, afterTotalSupplyLocals] using hsqrt)
      (by simpa [memFee] using rd2531) hrootSize hrootLt hmem hmem64
  · have hrootGeMin : minimumLiquidity ≤ root := le_of_not_gt hrootLt
    let liquidity := UInt256.ofNat (root - minimumLiquidity).toNat
    have hsourceSupplyFit :
        mintFunctionTotalSupplyNewNat evmFeeS (⟨1000⟩ : UInt256) < UInt256.size := by
      simp [mintFunctionTotalSupplyNewNat, htotalSource]
      native_decide
    have hruntimeSupplyFit :
        (uniswapSlotWord ⟨0⟩ σFee I).toNat + (⟨1000⟩ : UInt256).toNat <
          UInt256.size := by
      rw [htotalZero]
      native_decide
    have hsourceBalanceEq :
        mintFunctionToBalanceNewNat evmFeeS (AccountAddress.ofNat 0)
            (⟨1000⟩ : UInt256) =
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩ memFee)).toNat +
            (⟨1000⟩ : UInt256).toNat := by
      simpa using
        mintFunctionToBalanceNewNat_eq_runtimeMintRecipient
          (σ := σFee) (evm := evmFeeS) (I := I) (mem := memFee)
          (liquidity := (⟨1000⟩ : UInt256)) (recipientWord := ⟨0⟩)
          (recipient := AccountAddress.ofNat 0)
          hPostAccountsFee henvFeeI rfl (by rw [hmem]; omega) hsourceSupplyFit
    have hsourceOverflow :
        UInt256.size ≤
          mintFunctionToBalanceNewNat evmFeeS (AccountAddress.ofNat 0)
            (⟨1000⟩ : UInt256) := by
      rw [hsourceBalanceEq]
      exact hbalanceOverflow
    exact uniswapMintInitialAfterMintFeeMinimumMintBalanceOverflowRevertCase
      (liquidity := liquidity) nextFrame.locals root hcode hdispatch hsz36 hwv
      hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1 hle0Source hle1Source
      (by
        simpa [nextFrame, evmL, evmS, resumeAfterInternalCall] using
          uniswapMintFeeCallFromMint_feeOff_kLastZero evmL evm1S evmFeeS I balance0
            balance1 feeTo (by simpa [evmL, evmS] using hfeeGuard) hfeeCall hfeeDec
            hfeeToAddr hkLastSource)
      (by
        simpa [nextFrame, evmL, evmS] using
          mintAfterMintFeeCallStore_totalSupply evmL I balance0 balance1 false)
      htotalSource (by simpa [caller, afterTotalSupplyLocals] using hsqrt)
      (by simpa [memFee] using rd2531) hrootSize hrootGeMin rfl hsourceSupplyFit
      hsourceOverflow hruntimeSupplyFit hbalanceOverflow hperm hmem hmem64

set_option maxHeartbeats 1000000 in
theorem uniswapMintInitialFeeOnKLastZeroMinimumMintBalanceOverflowFromFactoryCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σ'' : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 outFee o o1 : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 toWord sel : UInt256} {zFee : Bool}
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
    (hPostAccountsFee : accountMapEquiv σFee evmFeeS.accountMap)
    (henvFeeI : evmFeeS.executionEnv = I)
    (hperm : I.perm = true)
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
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = uniswapSlotWord ⟨0⟩ σFee I)
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
    (hfeeToNonzero :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
          solcAddrMask ≠
        ⟨0⟩)
    (hkLastZero : mintFeeKLastSlotWord σFee I = ⟨0⟩)
    (htotalZero : uniswapSlotWord ⟨0⟩ σFee I = ⟨0⟩)
    (hfit : amount0.toNat * amount1.toNat < UInt256.size)
    (hbalanceOverflow :
      UInt256.size ≤
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (feeToStaticcallMem
              (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
              outFee))).toNat +
          (⟨1000⟩ : UInt256).toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmL := uniswapLockEnteredState evmS
  let nextFrame :=
    resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
      "feeOn" (some (.bool true))
  let memFee :=
    feeToStaticcallMem
      (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
      outFee
  have hmem : memFee.size = 164 := by
    dsimp [memFee]
    exact feeToStaticcallMem_size_of_size_ge
      (UInt256.ofNat I.codeOwner.val) o o1 outFee ho32 hoSize ho132 ho1Size houtFee32
      houtFeeSize
  have hmem64 : memFee.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [memFee]
    exact feeToStaticcallMem_read64_of_size_ge
      (UInt256.ofNat I.codeOwner.val) o o1 outFee ho32 hoSize ho132 ho1Size houtFee32
      houtFeeSize
  have hfeeToAddr : feeTo ≠ AccountAddress.ofNat 0 := by
    rw [hfeeToEq]
    exact accountAddress_ofNat_ne_zero_of_land_solcAddrMask_ne_zero
      (fromByteArrayBigEndian_extract0_32_lt houtFee32) hfeeToNonzero
  have hkLastSource : (mintFeeKLastWord evmFeeS).toNat = 0 := by
    rw [hkLastEq, hkLastZero]
    rfl
  have htotalSource : mintFunctionTotalSupplyWord evmFeeS = ⟨0⟩ := by
    rw [htotalEq, htotalZero]
  obtain ⟨_, _, rd3701⟩ :=
    uniswapMintFeeRuntimeFactoryResultFeeOnKLastZeroReturn
      rd7781 ho32 hoSize ho132 ho1Size houtFeeSize hzFeeTrue houtFee32 hfeeToNonzero
      hkLastZero
  have hfee :
      ExecStmt config
        { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
        evm1S (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
        (.ok { contract := contract, locals := nextFrame.locals } evmFeeS) := by
    simpa [nextFrame, evmL, evmS, resumeAfterInternalCall] using
      uniswapMintFeeCallFromMint_feeOn_kLastZero evmL evm1S evmFeeS I balance0
        balance1 feeTo (by simpa [evmL, evmS] using hfeeGuard) hfeeCall hfeeDec
        hfeeToAddr hkLastSource
  have hbase : nextFrame.locals.get? "totalSupply" = none := by
    simpa [nextFrame, evmL, evmS] using
      mintAfterMintFeeCallStore_totalSupply evmL I balance0 balance1 true
  have hamount0Get : nextFrame.locals.get? "amount0" = some (uniswapUint256Value amount0) := by
    simpa [nextFrame, evmL, evmS, mintAmount0Value, hamount0Eq] using
      mintAfterMintFeeCallStore_amount0 evmL I balance0 balance1 true
  have hamount1Get : nextFrame.locals.get? "amount1" = some (uniswapUint256Value amount1) := by
    simpa [nextFrame, evmL, evmS, mintAmount1Value, hamount1Eq] using
      mintAfterMintFeeCallStore_amount1 evmL I balance0 balance1 true
  exact uniswapMintInitialMinimumMintBalanceOverflowFromAfterFeeCase nextFrame.locals
    hcode hdispatch hsz36 hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1
    hle0Source hle1Source hfee hbase hamount0Get hamount1Get hPostAccountsFee henvFeeI
    htotalSource htotalZero hfit (by simpa [memFee] using rd3701)
    (by simpa [memFee] using hbalanceOverflow) hperm hmem hmem64

set_option maxHeartbeats 1000000 in
theorem uniswapMintInitialFeeOffKLastNonzeroMinimumMintBalanceOverflowFromFactoryCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σ'' : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 outFee o o1 : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 toWord sel : UInt256} {zFee : Bool}
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
    (hPostAccountsFee : accountMapEquiv σFee evmFeeS.accountMap)
    (henvFeeI : evmFeeS.executionEnv = I)
    (hperm : I.perm = true)
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
    (hfeeToZero :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
          solcAddrMask =
        ⟨0⟩)
    (hkLastNonzero : mintFeeKLastSlotWord σFee I ≠ ⟨0⟩)
    (htotalZero :
      uniswapSlotWord ⟨0⟩ (sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩) I = ⟨0⟩)
    (hfit : amount0.toNat * amount1.toNat < UInt256.size)
    (hbalanceOverflow :
      UInt256.size ≤
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩) ⟨0⟩
            (uniswapSlotWord ⟨0⟩ (sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩) I +
              (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (feeToStaticcallMem
              (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
              outFee))).toNat +
          (⟨1000⟩ : UInt256).toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmL := uniswapLockEnteredState evmS
  let σCleared := sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩
  let evmAfterFee := mintFeeKLastClearedState evmFeeS
  let nextFrame :=
    resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
      "feeOn" (some (.bool false))
  let memFee :=
    feeToStaticcallMem
      (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
      outFee
  have hmem : memFee.size = 164 := by
    dsimp [memFee]
    exact feeToStaticcallMem_size_of_size_ge
      (UInt256.ofNat I.codeOwner.val) o o1 outFee ho32 hoSize ho132 ho1Size houtFee32
      houtFeeSize
  have hmem64 : memFee.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [memFee]
    exact feeToStaticcallMem_read64_of_size_ge
      (UInt256.ofNat I.codeOwner.val) o o1 outFee ho32 hoSize ho132 ho1Size houtFee32
      houtFeeSize
  have hfeeToAddr : feeTo = AccountAddress.ofNat 0 := by
    rw [hfeeToEq]
    exact accountAddress_ofNat_eq_zero_of_land_solcAddrMask_eq_zero
      (fromByteArrayBigEndian_extract0_32_lt houtFee32) hfeeToZero
  have hkLastSource : (mintFeeKLastWord evmFeeS).toNat ≠ 0 := by
    intro hzero
    apply hkLastNonzero
    rw [← hkLastEq]
    exact uint256_toNat_eq_zero hzero
  have hPostCleared : accountMapEquiv σCleared evmAfterFee.accountMap := by
    have hstore := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨11⟩ ⟨0⟩
      hPostAccountsFee
    simpa [σCleared, evmAfterFee, mintFeeKLastClearedState, henvFeeI,
      storageStore_accountMap] using hstore
  have henvCleared : evmAfterFee.executionEnv = I := by
    simp [evmAfterFee, mintFeeKLastClearedState, henvFeeI, storageStore_executionEnv]
  have htotalEqCleared :
      mintFunctionTotalSupplyWord evmAfterFee = uniswapSlotWord ⟨0⟩ σCleared I := by
    simpa [σCleared] using
      mintFunctionTotalSupplyWord_eq_slot_of_accountMapEquiv hPostCleared henvCleared
  have htotalSource : mintFunctionTotalSupplyWord evmAfterFee = ⟨0⟩ := by
    rw [htotalEqCleared]
    exact htotalZero
  obtain ⟨_, _, rd3701⟩ :=
    uniswapMintFeeRuntimeFactoryResultFeeOffKLastNonzeroReturn
      rd7781 ho32 hoSize ho132 ho1Size houtFeeSize hzFeeTrue houtFee32 hfeeToZero
      hperm hkLastNonzero
  have hfee :
      ExecStmt config
        { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
        evm1S (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
        (.ok { contract := contract, locals := nextFrame.locals } evmAfterFee) := by
    simpa [nextFrame, evmL, evmS, evmAfterFee, resumeAfterInternalCall] using
      uniswapMintFeeCallFromMint_feeOff_kLastNonzero evmL evm1S evmFeeS I balance0
        balance1 feeTo (by simpa [evmL, evmS] using hfeeGuard) hfeeCall hfeeDec
        hfeeToAddr hkLastSource
  have hbase : nextFrame.locals.get? "totalSupply" = none := by
    simpa [nextFrame, evmL, evmS] using
      mintAfterMintFeeCallStore_totalSupply evmL I balance0 balance1 false
  have hamount0Get : nextFrame.locals.get? "amount0" = some (uniswapUint256Value amount0) := by
    simpa [nextFrame, evmL, evmS, mintAmount0Value, hamount0Eq] using
      mintAfterMintFeeCallStore_amount0 evmL I balance0 balance1 false
  have hamount1Get : nextFrame.locals.get? "amount1" = some (uniswapUint256Value amount1) := by
    simpa [nextFrame, evmL, evmS, mintAmount1Value, hamount1Eq] using
      mintAfterMintFeeCallStore_amount1 evmL I balance0 balance1 false
  exact uniswapMintInitialMinimumMintBalanceOverflowFromAfterFeeCase
    (σFee := σCleared) (evmAfter := evmAfterFee) nextFrame.locals hcode hdispatch hsz36
    hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1 hle0Source hle1Source
    hfee hbase hamount0Get hamount1Get hPostCleared henvCleared htotalSource
    (by simpa [σCleared] using htotalZero) hfit (by simpa [σCleared, memFee] using rd3701)
    (by simpa [σCleared, memFee] using hbalanceOverflow) hperm hmem hmem64

end UniswapV2Pair
