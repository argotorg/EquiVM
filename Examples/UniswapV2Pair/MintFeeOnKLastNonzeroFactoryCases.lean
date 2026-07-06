import Examples.UniswapV2Pair.MintProportionalFinish
import Examples.UniswapV2Pair.MintFeeSqrtLoopBridge
import Examples.UniswapV2Pair.MintRuntimeFitBridge

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

set_option maxHeartbeats 2000000 in
theorem uniswapMintFeeOnKLastNonzeroFactoryRoots
    {cA gh bl σ_evm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σ'' : AccountMap}
    {evmFeeS : EVM.State}
    {outFee o o1 memFee : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel feeToWord : UInt256}
    {zFee : Bool}
    (feeTo : AccountAddress)
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
      memFee feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (ho132 : 32 ≤ o1.size) (ho1Size : o1.size < UInt256.size)
    (houtFeeSize : outFee.size < UInt256.size)
    (hzFeeTrue : zFee = true)
    (houtFee32 : 32 ≤ outFee.size)
    (hfeeToWord : feeToWord = UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (hmemFee :
      memFee =
        feeToStaticcallMem
          (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
          outFee)
    (hruntimeReserve0 :
      reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I = reserve0)
    (hruntimeReserve1 :
      reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I = reserve1)
    (hfeeToNonzero : UInt256.land feeToWord solcAddrMask ≠ ⟨0⟩)
    (hkLastNonzero : mintFeeKLastSlotWord σFee I ≠ ⟨0⟩)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1) :
    ∃ rootK rootKLast k' C',
      ExecBlock config
        (mintFeeAfterKLastFrame reserve0 reserve1 feeTo true (mintFeeKLastSlotWord σFee I))
        evmFeeS
        [ .internalCall "sqrt" [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))]
            "rootK",
          .internalCall "sqrt" [.var "_kLast"] "rootKLast" ]
        (.ok
          (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true
            (mintFeeKLastSlotWord σFee I) rootK rootKLast)
          evmFeeS) ∧
      0 ≤ rootK ∧ rootK.toNat < UInt256.size ∧
      0 ≤ rootKLast ∧ rootKLast.toNat < UInt256.size ∧
      RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨7899⟩
        [UInt256.ofNat rootKLast.toNat, ⟨0⟩, UInt256.ofNat rootK.toNat,
          mintFeeKLastSlotWord σFee I, feeToWord, ⟨1⟩, reserve1, reserve0, ⟨3701⟩,
          ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
          toWord, ⟨861⟩, sel]
        memFee feeToStaticcallActiveWords outFee (cAFee, σFee) k' C' := by
  obtain ⟨_, _, hcont⟩ :=
    uniswapMintFeeRuntimeFactoryResultBranchesFromCall
      (by simpa [hmemFee] using rd7781) ho32 hoSize ho132 ho1Size houtFeeSize
  obtain ⟨k7825, C7825, rd7825Raw⟩ := hcont hzFeeTrue houtFee32
  have rd7825 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨7825⟩
      [mintFeeKLastSlotWord σFee I, feeToWord, ⟨0⟩, ⟨0⟩, reserve1, reserve0,
        ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      memFee feeToStaticcallActiveWords outFee (cAFee, σFee) k7825 C7825 := by
    simpa [hfeeToWord, hmemFee, hruntimeReserve0, hruntimeReserve1] using rd7825Raw
  obtain ⟨k8046, C8046, rd8046⟩ :=
    uniswapMintFeeRuntimeFeeOnKLastNonzeroRootKEntryFromDecode rd7825
      (by simpa [hfeeToWord] using hfeeToNonzero) hkLastNonzero hclean0 hclean1
  have hfit : mintFeeReserveProductNat reserve0 reserve1 < UInt256.size :=
    mintFeeReserveProductNat_lt_of_clean reserve0 reserve1 hclean0 hclean1
  exact
    mintFeeSqrtPrefixRuntimeBounded evmFeeS feeTo rd8046 hfit

set_option maxHeartbeats 2000000 in
theorem uniswapMintFeeOnKLastNonzeroFactoryRootsInput
    {cA gh bl σ_evm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σ'' : AccountMap}
    {evmFeeS : EVM.State}
    {outFee o o1 memFee : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel feeToWord : UInt256}
    {zFee : Bool}
    (feeTo : AccountAddress)
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
      memFee feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (ho132 : 32 ≤ o1.size) (ho1Size : o1.size < UInt256.size)
    (houtFeeSize : outFee.size < UInt256.size)
    (hzFeeTrue : zFee = true)
    (houtFee32 : 32 ≤ outFee.size)
    (hfeeToWord : feeToWord = UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (hmemFee :
      memFee =
        feeToStaticcallMem
          (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
          outFee)
    (hruntimeReserve0 :
      reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I = reserve0)
    (hruntimeReserve1 :
      reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I = reserve1)
    (hfeeToNonzero : UInt256.land feeToWord solcAddrMask ≠ ⟨0⟩)
    (hkLastNonzero : mintFeeKLastSlotWord σFee I ≠ ⟨0⟩)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1) :
    ∃ rootK rootKLast k' C',
      ExecBlock config
        (mintFeeAfterKLastFrame reserve0 reserve1 feeTo true (mintFeeKLastSlotWord σFee I))
        evmFeeS
        [ .internalCall "sqrt" [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))]
            "rootK",
          .internalCall "sqrt" [.var "_kLast"] "rootKLast" ]
        (.ok
          (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true
            (mintFeeKLastSlotWord σFee I) rootK rootKLast)
          evmFeeS) ∧
      0 ≤ rootK ∧ rootK.toNat < UInt256.size ∧
      rootK.toNat ≤ (UInt256.mul reserve0 reserve1).toNat ∧
      0 ≤ rootKLast ∧ rootKLast.toNat < UInt256.size ∧
      RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨7899⟩
        [UInt256.ofNat rootKLast.toNat, ⟨0⟩, UInt256.ofNat rootK.toNat,
          mintFeeKLastSlotWord σFee I, feeToWord, ⟨1⟩, reserve1, reserve0, ⟨3701⟩,
          ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
          toWord, ⟨861⟩, sel]
        memFee feeToStaticcallActiveWords outFee (cAFee, σFee) k' C' := by
  obtain ⟨_, _, hcont⟩ :=
    uniswapMintFeeRuntimeFactoryResultBranchesFromCall
      (by simpa [hmemFee] using rd7781) ho32 hoSize ho132 ho1Size houtFeeSize
  obtain ⟨k7825, C7825, rd7825Raw⟩ := hcont hzFeeTrue houtFee32
  have rd7825 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨7825⟩
      [mintFeeKLastSlotWord σFee I, feeToWord, ⟨0⟩, ⟨0⟩, reserve1, reserve0,
        ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      memFee feeToStaticcallActiveWords outFee (cAFee, σFee) k7825 C7825 := by
    simpa [hfeeToWord, hmemFee, hruntimeReserve0, hruntimeReserve1] using rd7825Raw
  obtain ⟨k8046, C8046, rd8046⟩ :=
    uniswapMintFeeRuntimeFeeOnKLastNonzeroRootKEntryFromDecode rd7825
      (by simpa [hfeeToWord] using hfeeToNonzero) hkLastNonzero hclean0 hclean1
  have hfit : mintFeeReserveProductNat reserve0 reserve1 < UInt256.size :=
    mintFeeReserveProductNat_lt_of_clean reserve0 reserve1 hclean0 hclean1
  exact
    mintFeeSqrtPrefixRuntimeBoundedInput evmFeeS feeTo rd8046 hfit

set_option maxHeartbeats 2000000 in
theorem uniswapMintFeeOnKLastNonzeroFactoryProductZeroRoots
    {cA gh bl σ_evm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σ'' : AccountMap}
    {evmFeeS : EVM.State}
    {outFee o o1 memFee : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel feeToWord : UInt256}
    {zFee : Bool}
    (feeTo : AccountAddress)
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
      memFee feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (ho132 : 32 ≤ o1.size) (ho1Size : o1.size < UInt256.size)
    (houtFeeSize : outFee.size < UInt256.size)
    (hzFeeTrue : zFee = true)
    (houtFee32 : 32 ≤ outFee.size)
    (hfeeToWord : feeToWord = UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (hmemFee :
      memFee =
        feeToStaticcallMem
          (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
          outFee)
    (hruntimeReserve0 :
      reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I = reserve0)
    (hruntimeReserve1 :
      reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I = reserve1)
    (hfeeToNonzero : UInt256.land feeToWord solcAddrMask ≠ ⟨0⟩)
    (hkLastNonzero : mintFeeKLastSlotWord σFee I ≠ ⟨0⟩)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hprodZero : UInt256.mul reserve0 reserve1 = ⟨0⟩) :
    ∃ rootKLast k' C',
      ExecBlock config
        (mintFeeAfterKLastFrame reserve0 reserve1 feeTo true (mintFeeKLastSlotWord σFee I))
        evmFeeS
        [ .internalCall "sqrt" [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))]
            "rootK",
          .internalCall "sqrt" [.var "_kLast"] "rootKLast" ]
        (.ok
          (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true
            (mintFeeKLastSlotWord σFee I) (0 : Int) rootKLast)
          evmFeeS) ∧
      0 ≤ rootKLast ∧ rootKLast.toNat < UInt256.size ∧
      RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨7899⟩
        [UInt256.ofNat rootKLast.toNat, ⟨0⟩, ⟨0⟩, mintFeeKLastSlotWord σFee I,
          feeToWord, ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0,
          balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
        memFee feeToStaticcallActiveWords outFee (cAFee, σFee) k' C' := by
  obtain ⟨_, _, hcont⟩ :=
    uniswapMintFeeRuntimeFactoryResultBranchesFromCall
      (by simpa [hmemFee] using rd7781) ho32 hoSize ho132 ho1Size houtFeeSize
  obtain ⟨k7825, C7825, rd7825Raw⟩ := hcont hzFeeTrue houtFee32
  have rd7825 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨7825⟩
      [mintFeeKLastSlotWord σFee I, feeToWord, ⟨0⟩, ⟨0⟩, reserve1, reserve0,
        ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      memFee feeToStaticcallActiveWords outFee (cAFee, σFee) k7825 C7825 := by
    simpa [hfeeToWord, hmemFee, hruntimeReserve0, hruntimeReserve1] using rd7825Raw
  obtain ⟨k8046, C8046, rd8046⟩ :=
    uniswapMintFeeRuntimeFeeOnKLastNonzeroRootKEntryFromDecode rd7825
      (by simpa [hfeeToWord] using hfeeToNonzero) hkLastNonzero hclean0 hclean1
  have hfit : mintFeeReserveProductNat reserve0 reserve1 < UInt256.size :=
    mintFeeReserveProductNat_lt_of_clean reserve0 reserve1 hclean0 hclean1
  exact
    mintFeeSqrtPrefixRuntimeProductZero evmFeeS feeTo rd8046 hfit hprodZero

set_option maxHeartbeats 3000000 in
theorem uniswapMintFeeOnKLastNonzeroNoMintFromFactoryCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σ'' : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 outFee o o1 memFee : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 reserve0 reserve1 totalSupply liquidity toWord sel
      feeToWord : UInt256}
    {zFee : Bool}
    (feeTo : AccountAddress)
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
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) =
          .ok (.bool true))
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
    (hcall0 :
      typedCallViaEVM config
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
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 :
      typedCallViaEVM config evm0S (EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩))
        "balanceOf" 0 [.address evm0S.executionEnv.codeOwner] (true, evm1S, out1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
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
    (hfeeCall :
      typedCallViaEVM config evm1S (EVM.address (uniswapAddressAtSlot evm1S ⟨5⟩))
        "feeTo" 0 [] (true, evmFeeS, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some (.address feeTo))
    (hPostAccountsFee : accountMapEquiv σFee evmFeeS.accountMap)
    (henvFeeI : evmFeeS.executionEnv = I)
    (hcreatedFee : evmFeeS.createdAccounts = cAFee)
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
    (hruntimeReserve0 :
      reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I = reserve0)
    (hruntimeReserve1 :
      reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I = reserve1)
    (hamount0 :
      mintAmount0Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance0 =
        amount0)
    (hamount1 :
      mintAmount1Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance1 =
        amount1)
    (hkLastEq : mintFeeKLastWord evmFeeS = mintFeeKLastSlotWord σFee I)
    (htotalSlot : uniswapSlotWord ⟨0⟩ σFee I = totalSupply)
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = totalSupply)
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
      memFee
      feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (ho132 : 32 ≤ o1.size) (ho1Size : o1.size < UInt256.size)
    (houtFeeSize : outFee.size < UInt256.size)
    (hzFeeTrue : zFee = true)
    (houtFee32 : 32 ≤ outFee.size)
    (hfeeToWord : feeToWord = UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (hfeeTo : feeTo = AccountAddress.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (htoWord : toWord = mintToMaskedWord I)
    (hmemFee :
      memFee =
        feeToStaticcallMem
          (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
          outFee)
    (hliquidity :
      liquidity =
        minFunctionResultWord (UInt256.div (UInt256.mul amount0 totalSupply) reserve0)
          (UInt256.div (UInt256.mul amount1 totalSupply) reserve1))
    (hcase :
      UInt256.land feeToWord solcAddrMask ≠ ⟨0⟩ ∧
        mintFeeKLastSlotWord σFee I ≠ ⟨0⟩ ∧
        ((∀ (rootK rootKLast : Int),
          0 ≤ rootK → rootK.toNat < UInt256.size →
          0 ≤ rootKLast → rootKLast.toNat < UInt256.size →
          ¬ rootK > rootKLast) ∨
          UInt256.mul reserve0 reserve1 = ⟨0⟩) ∧
        totalSupply ≠ ⟨0⟩ ∧
        amount0.toNat * totalSupply.toNat < UInt256.size ∧
        amount1.toNat * totalSupply.toNat < UInt256.size ∧
        reserve0 ≠ ⟨0⟩ ∧ reserve1 ≠ ⟨0⟩ ∧
        liquidity ≠ ⟨0⟩ ∧
        totalSupply.toNat + liquidity.toNat < UInt256.size ∧
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (totalSupply + liquidity))
          (uniswapInternalMintBalanceHashSlot toWord memFee)).toNat + liquidity.toNat <
          UInt256.size ∧
        mintFunctionToBalanceNewNat evmFeeS (AccountAddress.ofNat (mintToWord I).toNat)
            liquidity <
          UInt256.size ∧
        balance0.toNat ≤ reserve112Mask.toNat ∧
        balance1.toNat ≤ reserve112Mask.toNat ∧
        UInt256.land
            (uniswapUpdateElapsedWord
              (uniswapSlotWord ⟨8⟩
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (totalSupply + liquidity))
                  (uniswapInternalMintBalanceHashSlot toWord
                    (uniswapInternalMintBalanceHashMem toWord memFee))
                  (uniswapCodeOwnerStorageWord I
                    (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (totalSupply + liquidity))
                    (uniswapInternalMintBalanceHashSlot toWord memFee) +
                    liquidity)) I) I) reserve32Mask =
          ⟨0⟩ ∧
        (let σAfterMint :=
          sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (totalSupply + liquidity))
            (uniswapInternalMintBalanceHashSlot toWord
              (uniswapInternalMintBalanceHashMem toWord memFee))
            (uniswapCodeOwnerStorageWord I
              (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (totalSupply + liquidity))
              (uniswapInternalMintBalanceHashSlot toWord memFee) + liquidity)
        let packed := uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σAfterMint I)
          (uniswapUpdateTimestampWord I) balance1 balance0
        let σPacked := sstoreAccountMap I.codeOwner σAfterMint ⟨8⟩ packed
        (UInt256.land (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Mask).toNat *
            (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Shift)
              reserve112Mask).toNat <
          UInt256.size) ∧
        syncTimeElapsedInt
            (mintFunctionPostState evmFeeS (AccountAddress.ofNat (mintToWord I).toNat)
              liquidity) =
          0 ∧
        mintFeeReserveProductNat
            (uniswapReserve0Word
              (syncUpdatePackedReserveState
                (mintFunctionPostState evmFeeS (AccountAddress.ofNat (mintToWord I).toNat)
                  liquidity)
                balance0 balance1))
            (uniswapReserve1Word
              (syncUpdatePackedReserveState
                (mintFunctionPostState evmFeeS (AccountAddress.ofNat (mintToWord I).toNat)
                  liquidity)
                balance0 balance1)) <
          UInt256.size) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  rcases hcase with
    ⟨hfeeToNonzero, hkLastNonzero, hrootCase, htotalNonzero, hmulFit0, hmulFit1,
      hreserve0Nonzero, hreserve1Nonzero, hliqNonzero, htotalFit, hbalanceFit,
      hbalanceFitSource, hbound0, hbound1, helapsed0, hfitKLastRuntime,
      helapsedSource, hfitKLastSource⟩
  have hclean0 : UInt256.land reserve0 reserve112Mask = reserve0 := by
    rw [← hruntimeReserve0]
    exact reserve112Mask_clean_of_lt _ (reserve112Word_lt _)
  have hclean1 : UInt256.land reserve1 reserve112Mask = reserve1 := by
    rw [← hruntimeReserve1]
    exact reserve112Mask_clean_of_lt _ (reserve112Word_lt _)
  obtain ⟨rootK, rootKLast, k7899, C7899, hprefixRuntime, hrootKNonneg, hrootKSize,
      hrootKLastNonneg, hrootKLastSize, rd7899, hrootNoMint⟩ :
      ∃ rootK rootKLast k7899 C7899,
        ExecBlock config
          (mintFeeAfterKLastFrame reserve0 reserve1 feeTo true
            (mintFeeKLastSlotWord σFee I))
          evmFeeS
          [ .internalCall "sqrt" [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))]
              "rootK",
            .internalCall "sqrt" [.var "_kLast"] "rootKLast" ]
          (.ok
            (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true
              (mintFeeKLastSlotWord σFee I) rootK rootKLast)
            evmFeeS) ∧
        0 ≤ rootK ∧ rootK.toNat < UInt256.size ∧
        0 ≤ rootKLast ∧ rootKLast.toNat < UInt256.size ∧
        RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨7899⟩
          [UInt256.ofNat rootKLast.toNat, ⟨0⟩, UInt256.ofNat rootK.toNat,
            mintFeeKLastSlotWord σFee I, feeToWord, ⟨1⟩, reserve1, reserve0,
            ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0,
            ⟨0⟩, toWord, ⟨861⟩, sel]
          memFee feeToStaticcallActiveWords outFee (cAFee, σFee) k7899 C7899 ∧
        ¬ rootK > rootKLast := by
    rcases hrootCase with hrootAll | hprodZero
    · obtain ⟨rootK, rootKLast, k7899, C7899, hprefixRuntime, hrootKNonneg,
          hrootKSize, hrootKLastNonneg, hrootKLastSize, rd7899⟩ :=
        uniswapMintFeeOnKLastNonzeroFactoryRoots feeTo rd7781 ho32 hoSize ho132 ho1Size
          houtFeeSize hzFeeTrue houtFee32 hfeeToWord hmemFee hruntimeReserve0
          hruntimeReserve1 hfeeToNonzero hkLastNonzero hclean0 hclean1
      exact ⟨rootK, rootKLast, k7899, C7899, hprefixRuntime, hrootKNonneg,
        hrootKSize, hrootKLastNonneg, hrootKLastSize, rd7899,
        hrootAll rootK rootKLast hrootKNonneg hrootKSize hrootKLastNonneg
          hrootKLastSize⟩
    · obtain ⟨rootKLast, k7899, C7899, hprefixRuntime, hrootKLastNonneg,
          hrootKLastSize, rd7899Raw⟩ :=
        uniswapMintFeeOnKLastNonzeroFactoryProductZeroRoots feeTo rd7781 ho32 hoSize
          ho132 ho1Size houtFeeSize hzFeeTrue houtFee32 hfeeToWord hmemFee
          hruntimeReserve0 hruntimeReserve1 hfeeToNonzero hkLastNonzero hclean0 hclean1
          hprodZero
      refine ⟨0, rootKLast, k7899, C7899, by simpa using hprefixRuntime, by omega,
        ?_, hrootKLastNonneg, hrootKLastSize, by simpa using rd7899Raw, by omega⟩
      norm_num [UInt256.size]
  obtain ⟨k3701, C3701, rd3701Raw⟩ :=
    uniswapMintFeeRuntimeAfterRootsNoMintReturnOfInt rootK rootKLast rd7899 hrootNoMint
      hrootKSize hrootKLastSize
  have hprefix :
      ExecBlock config
        (mintFeeAfterKLastFrame
          (uniswapReserve0Word
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
          (uniswapReserve1Word
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
          feeTo true (mintFeeKLastWord evmFeeS))
        evmFeeS
        [ .internalCall "sqrt" [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))]
            "rootK",
          .internalCall "sqrt" [.var "_kLast"] "rootKLast" ]
        (.ok
          (mintFeeAfterRootKLastFrame
            (uniswapReserve0Word
              (uniswapLockEnteredState
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
            (uniswapReserve1Word
              (uniswapLockEnteredState
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
            feeTo true (mintFeeKLastWord evmFeeS) rootK rootKLast)
          evmFeeS) := by
    simpa [hreserve0Eq, hreserve1Eq, hkLastEq] using hprefixRuntime
  have rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨1⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        mintToMaskedWord I, ⟨861⟩, sel]
      memFee feeToStaticcallActiveWords outFee (cAFee, σFee) k3701 C3701 := by
    simpa [htoWord] using rd3701Raw
  have hmem : memFee.size = 164 := by
    rw [hmemFee]
    exact feeToStaticcallMem_size_of_size_ge (UInt256.ofNat I.codeOwner.val) o o1 outFee
      ho32 hoSize ho132 ho1Size houtFee32 houtFeeSize
  have hmem64 :
      memFee.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    rw [hmemFee]
    exact feeToStaticcallMem_read64_of_size_ge (UInt256.ofNat I.codeOwner.val) o o1 outFee
      ho32 hoSize ho132 ho1Size houtFee32 houtFeeSize
  exact uniswapMintFeeOnKLastNonzeroNoMintCase rootK rootKLast hcode hdispatch hsz36
    hperm hwv houtFee32 hfeeToWord hfeeTo hunlockedSolm hguard0 hguard1 hcall0 hdec0
    hcall1 hdec1 hle0Source hle1Source hfeeGuard hfeeCall hfeeDec hPostAccountsFee
    henvFeeI hcreatedFee hreserve0Eq hreserve1Eq hamount0 hamount1 hkLastEq htotalSlot
    htotalEq hprefix hrootNoMint rd3701 hfeeToNonzero hkLastNonzero htotalNonzero
    hclean0 hclean1 hmulFit0 hmulFit1 hreserve0Nonzero hreserve1Nonzero hliquidity
    hliqNonzero htotalFit (by simpa [htoWord] using hbalanceFit) hbalanceFitSource hbound0
    hbound1 (by simpa [htoWord] using helapsed0) helapsedSource
    (by simpa [htoWord] using hfitKLastRuntime) hfitKLastSource hmem hmem64

set_option maxHeartbeats 3000000 in
theorem uniswapMintFeeOnKLastNonzeroPositiveNoLiquidityFromFactoryCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σ'' : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 outFee o o1 memFee : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 reserve0 reserve1 totalSupply liquidity toWord sel
      feeToWord : UInt256}
    {zFee : Bool}
    (feeTo : AccountAddress)
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
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) =
          .ok (.bool true))
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
    (hcall0 :
      typedCallViaEVM config
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
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 :
      typedCallViaEVM config evm0S (EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩))
        "balanceOf" 0 [.address evm0S.executionEnv.codeOwner] (true, evm1S, out1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
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
    (hfeeCall :
      typedCallViaEVM config evm1S (EVM.address (uniswapAddressAtSlot evm1S ⟨5⟩))
        "feeTo" 0 [] (true, evmFeeS, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some (.address feeTo))
    (hPostAccountsFee : accountMapEquiv σFee evmFeeS.accountMap)
    (henvFeeI : evmFeeS.executionEnv = I)
    (hcreatedFee : evmFeeS.createdAccounts = cAFee)
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
    (hruntimeReserve0 :
      reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I = reserve0)
    (hruntimeReserve1 :
      reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I = reserve1)
    (hamount0 :
      mintAmount0Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance0 =
        amount0)
    (hamount1 :
      mintAmount1Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance1 =
        amount1)
    (hkLastEq : mintFeeKLastWord evmFeeS = mintFeeKLastSlotWord σFee I)
    (htotalSlot : uniswapSlotWord ⟨0⟩ σFee I = totalSupply)
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = totalSupply)
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
      memFee
      feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (ho132 : 32 ≤ o1.size) (ho1Size : o1.size < UInt256.size)
    (houtFeeSize : outFee.size < UInt256.size)
    (hzFeeTrue : zFee = true)
    (houtFee32 : 32 ≤ outFee.size)
    (hfeeToWord : feeToWord = UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (hfeeTo : feeTo = AccountAddress.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (htoWord : toWord = mintToMaskedWord I)
    (hmemFee :
      memFee =
        feeToStaticcallMem
          (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
          outFee)
    (hliquidity :
      liquidity =
        minFunctionResultWord (UInt256.div (UInt256.mul amount0 totalSupply) reserve0)
          (UInt256.div (UInt256.mul amount1 totalSupply) reserve1))
    (hcase :
      UInt256.land feeToWord solcAddrMask ≠ ⟨0⟩ ∧
        mintFeeKLastSlotWord σFee I ≠ ⟨0⟩ ∧
        (∀ (rootK rootKLast : Int),
          0 ≤ rootK → rootK.toNat < UInt256.size →
          0 ≤ rootKLast → rootKLast.toNat < UInt256.size →
          rootK > rootKLast ∧
            mintFeeNumeratorNat evmFeeS rootK rootKLast < UInt256.size ∧
            mintFeeRootTimesFiveNat rootK < UInt256.size ∧
            mintFeeDenominatorNat rootK rootKLast < UInt256.size ∧
            (mintFeeDenominatorWord rootK rootKLast).toNat ≠ 0 ∧
            ¬ mintFeeLiquidityInt evmFeeS rootK rootKLast > 0) ∧
        totalSupply ≠ ⟨0⟩ ∧
        amount0.toNat * totalSupply.toNat < UInt256.size ∧
        amount1.toNat * totalSupply.toNat < UInt256.size ∧
        reserve0 ≠ ⟨0⟩ ∧ reserve1 ≠ ⟨0⟩ ∧
        liquidity ≠ ⟨0⟩ ∧
        totalSupply.toNat + liquidity.toNat < UInt256.size ∧
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (totalSupply + liquidity))
          (uniswapInternalMintBalanceHashSlot toWord memFee)).toNat + liquidity.toNat <
          UInt256.size ∧
        mintFunctionToBalanceNewNat evmFeeS (AccountAddress.ofNat (mintToWord I).toNat)
            liquidity <
          UInt256.size ∧
        balance0.toNat ≤ reserve112Mask.toNat ∧
        balance1.toNat ≤ reserve112Mask.toNat ∧
        UInt256.land
            (uniswapUpdateElapsedWord
              (uniswapSlotWord ⟨8⟩
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (totalSupply + liquidity))
                  (uniswapInternalMintBalanceHashSlot toWord
                    (uniswapInternalMintBalanceHashMem toWord memFee))
                  (uniswapCodeOwnerStorageWord I
                    (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (totalSupply + liquidity))
                    (uniswapInternalMintBalanceHashSlot toWord memFee) +
                    liquidity)) I) I) reserve32Mask =
          ⟨0⟩ ∧
        (let σAfterMint :=
          sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (totalSupply + liquidity))
            (uniswapInternalMintBalanceHashSlot toWord
              (uniswapInternalMintBalanceHashMem toWord memFee))
            (uniswapCodeOwnerStorageWord I
              (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (totalSupply + liquidity))
              (uniswapInternalMintBalanceHashSlot toWord memFee) + liquidity)
        let packed := uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σAfterMint I)
          (uniswapUpdateTimestampWord I) balance1 balance0
        let σPacked := sstoreAccountMap I.codeOwner σAfterMint ⟨8⟩ packed
        (UInt256.land (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Mask).toNat *
            (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Shift)
              reserve112Mask).toNat <
          UInt256.size) ∧
        syncTimeElapsedInt
            (mintFunctionPostState evmFeeS (AccountAddress.ofNat (mintToWord I).toNat)
              liquidity) =
          0 ∧
        mintFeeReserveProductNat
            (uniswapReserve0Word
              (syncUpdatePackedReserveState
                (mintFunctionPostState evmFeeS (AccountAddress.ofNat (mintToWord I).toNat)
                  liquidity)
                balance0 balance1))
            (uniswapReserve1Word
              (syncUpdatePackedReserveState
                (mintFunctionPostState evmFeeS (AccountAddress.ofNat (mintToWord I).toNat)
                  liquidity)
                balance0 balance1)) <
          UInt256.size) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  rcases hcase with
    ⟨hfeeToNonzero, hkLastNonzero, hrootCase, htotalNonzero, hmulFit0, hmulFit1,
      hreserve0Nonzero, hreserve1Nonzero, hliqNonzero, htotalFit, hbalanceFit,
      hbalanceFitSource, hbound0, hbound1, helapsed0, hfitKLastRuntime,
      helapsedSource, hfitKLastSource⟩
  have hclean0 : UInt256.land reserve0 reserve112Mask = reserve0 := by
    rw [← hruntimeReserve0]
    exact reserve112Mask_clean_of_lt _ (reserve112Word_lt _)
  have hclean1 : UInt256.land reserve1 reserve112Mask = reserve1 := by
    rw [← hruntimeReserve1]
    exact reserve112Mask_clean_of_lt _ (reserve112Word_lt _)
  obtain ⟨rootK, rootKLast, k7899, C7899, hprefixRuntime, hrootKNonneg, hrootKSize,
      hrootKLastNonneg, hrootKLastSize, rd7899⟩ :=
    uniswapMintFeeOnKLastNonzeroFactoryRoots feeTo rd7781 ho32 hoSize ho132 ho1Size
      houtFeeSize hzFeeTrue houtFee32 hfeeToWord hmemFee hruntimeReserve0 hruntimeReserve1
      hfeeToNonzero hkLastNonzero hclean0 hclean1
  rcases hrootCase rootK rootKLast hrootKNonneg hrootKSize hrootKLastNonneg
      hrootKLastSize with
    ⟨hroot, hnumFit, hrootFiveFit, hdenFit, hdenom, hfeeLiq⟩
  obtain ⟨k3701, C3701, rd3701Raw⟩ :=
    uniswapMintFeeRuntimeAfterRootsPositiveNoLiquidityReturn rootK rootKLast rd7899 evmFeeS
      (htotalEq.trans htotalSlot.symm) hroot hrootKNonneg hrootKSize hrootKLastNonneg
      hnumFit hrootFiveFit hdenFit hdenom hfeeLiq
  have hprefix :
      ExecBlock config
        (mintFeeAfterKLastFrame
          (uniswapReserve0Word
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
          (uniswapReserve1Word
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
          feeTo true (mintFeeKLastWord evmFeeS))
        evmFeeS
        [ .internalCall "sqrt" [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))]
            "rootK",
          .internalCall "sqrt" [.var "_kLast"] "rootKLast" ]
        (.ok
          (mintFeeAfterRootKLastFrame
            (uniswapReserve0Word
              (uniswapLockEnteredState
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
            (uniswapReserve1Word
              (uniswapLockEnteredState
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
            feeTo true (mintFeeKLastWord evmFeeS) rootK rootKLast)
          evmFeeS) := by
    simpa [hreserve0Eq, hreserve1Eq, hkLastEq] using hprefixRuntime
  have rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨1⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        mintToMaskedWord I, ⟨861⟩, sel]
      memFee feeToStaticcallActiveWords outFee (cAFee, σFee) k3701 C3701 := by
    simpa [htoWord] using rd3701Raw
  have hmem : memFee.size = 164 := by
    rw [hmemFee]
    exact feeToStaticcallMem_size_of_size_ge (UInt256.ofNat I.codeOwner.val) o o1 outFee
      ho32 hoSize ho132 ho1Size houtFee32 houtFeeSize
  have hmem64 :
      memFee.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    rw [hmemFee]
    exact feeToStaticcallMem_read64_of_size_ge (UInt256.ofNat I.codeOwner.val) o o1 outFee
      ho32 hoSize ho132 ho1Size houtFee32 houtFeeSize
  exact uniswapMintFeeOnKLastNonzeroPositiveNoLiquidityCase rootK rootKLast hcode hdispatch
    hsz36 hperm hwv houtFee32 hfeeToWord hfeeTo hunlockedSolm hguard0 hguard1 hcall0
    hdec0 hcall1 hdec1 hle0Source hle1Source hfeeGuard hfeeCall hfeeDec hPostAccountsFee
    henvFeeI hcreatedFee hreserve0Eq hreserve1Eq hamount0 hamount1 hkLastEq htotalSlot
    htotalEq hprefix hroot hrootKNonneg hrootKSize hrootKLastNonneg hnumFit hrootFiveFit
    hdenFit hdenom hfeeLiq rd3701 hfeeToNonzero hkLastNonzero htotalNonzero hclean0
    hclean1 hmulFit0 hmulFit1 hreserve0Nonzero hreserve1Nonzero hliquidity hliqNonzero
    htotalFit (by simpa [htoWord] using hbalanceFit) hbalanceFitSource hbound0 hbound1
    (by simpa [htoWord] using helapsed0) helapsedSource
    (by simpa [htoWord] using hfitKLastRuntime) hfitKLastSource hmem hmem64

set_option maxHeartbeats 3000000 in
theorem uniswapMintFeeOnKLastNonzeroPositiveWithLiquidityRuntimeFromFactory
    {cA gh bl σ_evm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σ'' : AccountMap}
    {evmFeeS : EVM.State}
    {outFee o o1 memFee : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel feeToWord : UInt256}
    {zFee : Bool}
    (feeTo : AccountAddress)
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
      memFee feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (ho132 : 32 ≤ o1.size) (ho1Size : o1.size < UInt256.size)
    (houtFeeSize : outFee.size < UInt256.size)
    (hzFeeTrue : zFee = true)
    (houtFee32 : 32 ≤ outFee.size)
    (hfeeToWord : feeToWord = UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (hfeeTo : feeTo = AccountAddress.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (hmemFee :
      memFee =
        feeToStaticcallMem
          (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
          outFee)
    (hruntimeReserve0 :
      reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I = reserve0)
    (hruntimeReserve1 :
      reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I = reserve1)
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = uniswapSlotWord ⟨0⟩ σFee I)
    (hfeeToNonzero : UInt256.land feeToWord solcAddrMask ≠ ⟨0⟩)
    (hkLastNonzero : mintFeeKLastSlotWord σFee I ≠ ⟨0⟩)
    (hrootCase :
      ∀ (rootK rootKLast : Int),
        0 ≤ rootK → rootK.toNat < UInt256.size →
        0 ≤ rootKLast → rootKLast.toNat < UInt256.size →
        rootK > rootKLast ∧
          mintFeeNumeratorNat evmFeeS rootK rootKLast < UInt256.size ∧
          mintFeeRootTimesFiveNat rootK < UInt256.size ∧
          mintFeeDenominatorNat rootK rootKLast < UInt256.size ∧
          (mintFeeDenominatorWord rootK rootKLast).toNat ≠ 0 ∧
          mintFeeLiquidityInt evmFeeS rootK rootKLast > 0 ∧
          (mintFeeLiquidityInt evmFeeS rootK rootKLast).toNat < UInt256.size ∧
          mintFunctionTotalSupplyNewNat evmFeeS
              (mintFeeLiquidityWord evmFeeS rootK rootKLast) <
            UInt256.size ∧
          mintFunctionToBalanceNewNat evmFeeS feeTo
              (mintFeeLiquidityWord evmFeeS rootK rootKLast) <
            UInt256.size) :
    ∃ rootK rootKLast k' C',
      ExecBlock config
        (mintFeeAfterKLastFrame reserve0 reserve1 feeTo true (mintFeeKLastSlotWord σFee I))
        evmFeeS
        [ .internalCall "sqrt" [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))]
            "rootK",
          .internalCall "sqrt" [.var "_kLast"] "rootKLast" ]
        (.ok
          (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true
            (mintFeeKLastSlotWord σFee I) rootK rootKLast)
          evmFeeS) ∧
      0 ≤ rootK ∧ rootK.toNat < UInt256.size ∧
      0 ≤ rootKLast ∧ rootKLast.toNat < UInt256.size ∧
      rootK > rootKLast ∧
      mintFeeNumeratorNat evmFeeS rootK rootKLast < UInt256.size ∧
      mintFeeRootTimesFiveNat rootK < UInt256.size ∧
      mintFeeDenominatorNat rootK rootKLast < UInt256.size ∧
      (mintFeeDenominatorWord rootK rootKLast).toNat ≠ 0 ∧
      mintFeeLiquidityInt evmFeeS rootK rootKLast > 0 ∧
      (mintFeeLiquidityInt evmFeeS rootK rootKLast).toNat < UInt256.size ∧
      mintFunctionTotalSupplyNewNat evmFeeS
          (mintFeeLiquidityWord evmFeeS rootK rootKLast) <
        UInt256.size ∧
      mintFunctionToBalanceNewNat evmFeeS feeTo
          (mintFeeLiquidityWord evmFeeS rootK rootKLast) <
        UInt256.size ∧
      RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
        [⟨1⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0,
          ⟨0⟩, toWord, ⟨861⟩, sel]
        (uniswapInternalMintLogMem (mintFeeLiquidityWord evmFeeS rootK rootKLast)
          (uniswapInternalMintBalanceHashMem feeToWord
            (uniswapInternalMintBalanceHashMem feeToWord memFee)))
        feeToStaticcallActiveWords outFee
        (cAFee, sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + mintFeeLiquidityWord evmFeeS rootK rootKLast))
          (uniswapInternalMintBalanceHashSlot feeToWord
            (uniswapInternalMintBalanceHashMem feeToWord memFee))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + mintFeeLiquidityWord evmFeeS rootK rootKLast))
            (uniswapInternalMintBalanceHashSlot feeToWord memFee) +
              mintFeeLiquidityWord evmFeeS rootK rootKLast)) k' C' := by
  have hclean0 : UInt256.land reserve0 reserve112Mask = reserve0 := by
    rw [← hruntimeReserve0]
    exact reserve112Mask_clean_of_lt _ (reserve112Word_lt _)
  have hclean1 : UInt256.land reserve1 reserve112Mask = reserve1 := by
    rw [← hruntimeReserve1]
    exact reserve112Mask_clean_of_lt _ (reserve112Word_lt _)
  obtain ⟨rootK, rootKLast, k7899, C7899, hprefixRuntime, hrootKNonneg, hrootKSize,
      hrootKLastNonneg, hrootKLastSize, rd7899⟩ :=
    uniswapMintFeeOnKLastNonzeroFactoryRoots feeTo rd7781 ho32 hoSize ho132 ho1Size
      houtFeeSize hzFeeTrue houtFee32 hfeeToWord hmemFee hruntimeReserve0 hruntimeReserve1
      hfeeToNonzero hkLastNonzero hclean0 hclean1
  rcases hrootCase rootK rootKLast hrootKNonneg hrootKSize hrootKLastNonneg
      hrootKLastSize with
    ⟨hroot, hnumFit, hrootFiveFit, hdenFit, hdenom, hfeeLiq, hfeeLiqFit,
      hfeeFitSupply, hfeeFitBalance⟩
  let feeLiquidity := mintFeeLiquidityWord evmFeeS rootK rootKLast
  have hmem : memFee.size = 164 := by
    rw [hmemFee]
    exact feeToStaticcallMem_size_of_size_ge (UInt256.ofNat I.codeOwner.val) o o1 outFee
      ho32 hoSize ho132 ho1Size houtFee32 houtFeeSize
  have hmem64 :
      memFee.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    rw [hmemFee]
    exact feeToStaticcallMem_read64_of_size_ge (UInt256.ofNat I.codeOwner.val) o o1 outFee
      ho32 hoSize ho132 ho1Size houtFee32 houtFeeSize
  have hfeeFitSupply' :
      mintFunctionTotalSupplyNewNat evmFeeS feeLiquidity < UInt256.size := by
    simpa [feeLiquidity] using hfeeFitSupply
  have htotalRuntimeEq :=
    mintFunctionTotalSupplyNewNat_eq_runtime
      (σ := σFee) (evm := evmFeeS) (I := I) (liquidity := feeLiquidity)
      hPostAccountsFee henvFeeI
  have hfeeTotalFitRuntime :
      (uniswapSlotWord ⟨0⟩ σFee I).toNat + feeLiquidity.toNat < UInt256.size := by
    simpa [htotalRuntimeEq] using hfeeFitSupply'
  have hfeeToRuntime : feeTo = AccountAddress.ofNat feeToWord.toNat := by
    rw [hfeeTo, hfeeToWord,
      UInt256.toNat_ofNat_of_lt (fromByteArrayBigEndian_extract0_32_lt houtFee32)]
  have hfeeFitBalance' :
      mintFunctionToBalanceNewNat evmFeeS feeTo feeLiquidity < UInt256.size := by
    simpa [feeLiquidity] using hfeeFitBalance
  have hbalanceRuntimeEq :=
    mintFunctionToBalanceNewNat_eq_runtimeMintRecipient
      (σ := σFee) (evm := evmFeeS) (I := I) (mem := memFee)
      (liquidity := feeLiquidity) (recipientWord := feeToWord) (recipient := feeTo)
      hPostAccountsFee henvFeeI hfeeToRuntime (by rw [hmem]; omega) hfeeFitSupply'
  have hfeeBalanceFitRuntime :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + feeLiquidity))
        (uniswapInternalMintBalanceHashSlot feeToWord memFee)).toNat +
          feeLiquidity.toNat <
        UInt256.size := by
    simpa [hbalanceRuntimeEq] using hfeeFitBalance'
  have hmload64 :=
    uniswapInternalMintDoubleBalanceHashMem_mload64_of_ge160 feeToWord
      (by rw [hmem]; omega) hmem64
  have hlogMload64 :=
    uniswapInternalMintSuccessMem_mload64_of_ge160 feeToWord feeLiquidity
      (by rw [hmem]; omega) hmem64
  obtain ⟨k3701, C3701, rd3701⟩ :=
    uniswapMintFeeRuntimeAfterRootsPositiveWithLiquidityReturn rootK rootKLast rd7899
      evmFeeS htotalEq hroot hrootKNonneg hrootKSize hrootKLastNonneg hnumFit
      hrootFiveFit hdenFit hdenom hfeeLiq hfeeLiqFit hperm hfeeTotalFitRuntime
      hfeeBalanceFitRuntime hmload64 hlogMload64
  exact ⟨rootK, rootKLast, k3701, C3701, hprefixRuntime, hrootKNonneg, hrootKSize,
    hrootKLastNonneg, hrootKLastSize, hroot, hnumFit, hrootFiveFit, hdenFit, hdenom,
    hfeeLiq, hfeeLiqFit, hfeeFitSupply, hfeeFitBalance, by simpa [feeLiquidity] using rd3701⟩

def mintFeeOnKLastNonzeroPositiveWithLiquidityCaseData
    (feeTo : AccountAddress) (evmFeeS : EVM.State) (σFee : AccountMap) (I : ExecutionEnv)
    (feeToWord amount0 amount1 balance0 balance1 reserve0 reserve1 toWord : UInt256)
    (memFee : ByteArray) (rootK rootKLast : Int) : Prop :=
  let feeLiquidity := mintFeeLiquidityWord evmFeeS rootK rootKLast
  let σAfterFee :=
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σFee ⟨0⟩
        (uniswapSlotWord ⟨0⟩ σFee I + feeLiquidity))
      (uniswapInternalMintBalanceHashSlot feeToWord
        (uniswapInternalMintBalanceHashMem feeToWord memFee))
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + feeLiquidity))
        (uniswapInternalMintBalanceHashSlot feeToWord memFee) + feeLiquidity)
  let memAfterFee :=
    uniswapInternalMintLogMem feeLiquidity
      (uniswapInternalMintBalanceHashMem feeToWord
        (uniswapInternalMintBalanceHashMem feeToWord memFee))
  let evmAfterFee := mintFunctionPostState evmFeeS feeTo feeLiquidity
  let totalSupplyAfterFee := uniswapSlotWord ⟨0⟩ σAfterFee I
  let liquidityAfterFee :=
    minFunctionResultWord (UInt256.div (UInt256.mul amount0 totalSupplyAfterFee) reserve0)
      (UInt256.div (UInt256.mul amount1 totalSupplyAfterFee) reserve1)
  let σAfterMint :=
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σAfterFee ⟨0⟩
        (totalSupplyAfterFee + liquidityAfterFee))
      (uniswapInternalMintBalanceHashSlot toWord
        (uniswapInternalMintBalanceHashMem toWord memAfterFee))
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σAfterFee ⟨0⟩
          (totalSupplyAfterFee + liquidityAfterFee))
        (uniswapInternalMintBalanceHashSlot toWord memAfterFee) + liquidityAfterFee)
  let packed := uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σAfterMint I)
    (uniswapUpdateTimestampWord I) balance1 balance0
  let σPacked := sstoreAccountMap I.codeOwner σAfterMint ⟨8⟩ packed
  let postMint :=
    mintFunctionPostState evmAfterFee (AccountAddress.ofNat (mintToWord I).toNat)
      liquidityAfterFee
  let syncState := syncUpdatePackedReserveState postMint balance0 balance1
  rootK > rootKLast ∧
    mintFeeNumeratorNat evmFeeS rootK rootKLast < UInt256.size ∧
    mintFeeRootTimesFiveNat rootK < UInt256.size ∧
    mintFeeDenominatorNat rootK rootKLast < UInt256.size ∧
    (mintFeeDenominatorWord rootK rootKLast).toNat ≠ 0 ∧
    mintFeeLiquidityInt evmFeeS rootK rootKLast > 0 ∧
    (mintFeeLiquidityInt evmFeeS rootK rootKLast).toNat < UInt256.size ∧
    mintFunctionTotalSupplyNewNat evmFeeS feeLiquidity < UInt256.size ∧
    mintFunctionToBalanceNewNat evmFeeS feeTo feeLiquidity < UInt256.size ∧
    totalSupplyAfterFee ≠ ⟨0⟩ ∧
    amount0.toNat * totalSupplyAfterFee.toNat < UInt256.size ∧
    amount1.toNat * totalSupplyAfterFee.toNat < UInt256.size ∧
    reserve0 ≠ ⟨0⟩ ∧ reserve1 ≠ ⟨0⟩ ∧
    liquidityAfterFee ≠ ⟨0⟩ ∧
    totalSupplyAfterFee.toNat + liquidityAfterFee.toNat < UInt256.size ∧
    (uniswapCodeOwnerStorageWord I
      (sstoreAccountMap I.codeOwner σAfterFee ⟨0⟩
        (totalSupplyAfterFee + liquidityAfterFee))
      (uniswapInternalMintBalanceHashSlot toWord memAfterFee)).toNat +
        liquidityAfterFee.toNat <
      UInt256.size ∧
    mintFunctionToBalanceNewNat evmAfterFee
        (AccountAddress.ofNat (mintToWord I).toNat) liquidityAfterFee <
      UInt256.size ∧
    balance0.toNat ≤ reserve112Mask.toNat ∧
    balance1.toNat ≤ reserve112Mask.toNat ∧
    UInt256.land (uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σAfterMint I) I)
        reserve32Mask =
      ⟨0⟩ ∧
    (UInt256.land (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Mask).toNat *
        (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Shift)
          reserve112Mask).toNat <
      UInt256.size ∧
    syncTimeElapsedInt postMint = 0 ∧
    mintFeeReserveProductNat (uniswapReserve0Word syncState)
        (uniswapReserve1Word syncState) <
      UInt256.size

def mintFeeOnKLastNonzeroNoMintFromFactoryCaseData
    (feeToWord totalSupply amount0 amount1 balance0 balance1 reserve0 reserve1 toWord
      liquidity : UInt256)
    (σFee : AccountMap) (evmFeeS : EVM.State) (I : ExecutionEnv) (memFee : ByteArray) :
    Prop :=
  let σAfterMint :=
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (totalSupply + liquidity))
      (uniswapInternalMintBalanceHashSlot toWord
        (uniswapInternalMintBalanceHashMem toWord memFee))
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (totalSupply + liquidity))
        (uniswapInternalMintBalanceHashSlot toWord memFee) + liquidity)
  let packed := uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σAfterMint I)
    (uniswapUpdateTimestampWord I) balance1 balance0
  let σPacked := sstoreAccountMap I.codeOwner σAfterMint ⟨8⟩ packed
  let postMint :=
    mintFunctionPostState evmFeeS (AccountAddress.ofNat (mintToWord I).toNat) liquidity
  let syncState := syncUpdatePackedReserveState postMint balance0 balance1
  UInt256.land feeToWord solcAddrMask ≠ ⟨0⟩ ∧
    mintFeeKLastSlotWord σFee I ≠ ⟨0⟩ ∧
    ((∀ (rootK rootKLast : Int),
      0 ≤ rootK → rootK.toNat < UInt256.size →
      0 ≤ rootKLast → rootKLast.toNat < UInt256.size →
      ¬ rootK > rootKLast) ∨
      UInt256.mul reserve0 reserve1 = ⟨0⟩) ∧
    totalSupply ≠ ⟨0⟩ ∧
    amount0.toNat * totalSupply.toNat < UInt256.size ∧
    amount1.toNat * totalSupply.toNat < UInt256.size ∧
    reserve0 ≠ ⟨0⟩ ∧ reserve1 ≠ ⟨0⟩ ∧
    liquidity ≠ ⟨0⟩ ∧
    totalSupply.toNat + liquidity.toNat < UInt256.size ∧
    (uniswapCodeOwnerStorageWord I
      (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (totalSupply + liquidity))
      (uniswapInternalMintBalanceHashSlot toWord memFee)).toNat + liquidity.toNat <
      UInt256.size ∧
    mintFunctionToBalanceNewNat evmFeeS
        (AccountAddress.ofNat (mintToWord I).toNat) liquidity <
      UInt256.size ∧
    balance0.toNat ≤ reserve112Mask.toNat ∧
    balance1.toNat ≤ reserve112Mask.toNat ∧
    UInt256.land (uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σAfterMint I) I)
        reserve32Mask =
      ⟨0⟩ ∧
    (UInt256.land (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Mask).toNat *
        (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Shift)
          reserve112Mask).toNat <
      UInt256.size ∧
    syncTimeElapsedInt postMint = 0 ∧
    mintFeeReserveProductNat (uniswapReserve0Word syncState)
        (uniswapReserve1Word syncState) <
      UInt256.size

def mintFeeOnKLastNonzeroPositiveNoLiquidityFromFactoryCaseData
    (feeToWord totalSupply amount0 amount1 balance0 balance1 reserve0 reserve1 toWord
      liquidity : UInt256)
    (σFee : AccountMap) (evmFeeS : EVM.State) (I : ExecutionEnv) (memFee : ByteArray) :
    Prop :=
  let σAfterMint :=
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (totalSupply + liquidity))
      (uniswapInternalMintBalanceHashSlot toWord
        (uniswapInternalMintBalanceHashMem toWord memFee))
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (totalSupply + liquidity))
        (uniswapInternalMintBalanceHashSlot toWord memFee) + liquidity)
  let packed := uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σAfterMint I)
    (uniswapUpdateTimestampWord I) balance1 balance0
  let σPacked := sstoreAccountMap I.codeOwner σAfterMint ⟨8⟩ packed
  let postMint :=
    mintFunctionPostState evmFeeS (AccountAddress.ofNat (mintToWord I).toNat) liquidity
  let syncState := syncUpdatePackedReserveState postMint balance0 balance1
  UInt256.land feeToWord solcAddrMask ≠ ⟨0⟩ ∧
    mintFeeKLastSlotWord σFee I ≠ ⟨0⟩ ∧
    (∀ (rootK rootKLast : Int),
      0 ≤ rootK → rootK.toNat < UInt256.size →
      0 ≤ rootKLast → rootKLast.toNat < UInt256.size →
      rootK > rootKLast ∧
        mintFeeNumeratorNat evmFeeS rootK rootKLast < UInt256.size ∧
        mintFeeRootTimesFiveNat rootK < UInt256.size ∧
        mintFeeDenominatorNat rootK rootKLast < UInt256.size ∧
        (mintFeeDenominatorWord rootK rootKLast).toNat ≠ 0 ∧
        ¬ mintFeeLiquidityInt evmFeeS rootK rootKLast > 0) ∧
    totalSupply ≠ ⟨0⟩ ∧
    amount0.toNat * totalSupply.toNat < UInt256.size ∧
    amount1.toNat * totalSupply.toNat < UInt256.size ∧
    reserve0 ≠ ⟨0⟩ ∧ reserve1 ≠ ⟨0⟩ ∧
    liquidity ≠ ⟨0⟩ ∧
    totalSupply.toNat + liquidity.toNat < UInt256.size ∧
    (uniswapCodeOwnerStorageWord I
      (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (totalSupply + liquidity))
      (uniswapInternalMintBalanceHashSlot toWord memFee)).toNat + liquidity.toNat <
      UInt256.size ∧
    mintFunctionToBalanceNewNat evmFeeS
        (AccountAddress.ofNat (mintToWord I).toNat) liquidity <
      UInt256.size ∧
    balance0.toNat ≤ reserve112Mask.toNat ∧
    balance1.toNat ≤ reserve112Mask.toNat ∧
    UInt256.land (uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σAfterMint I) I)
        reserve32Mask =
      ⟨0⟩ ∧
    (UInt256.land (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Mask).toNat *
        (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Shift)
          reserve112Mask).toNat <
      UInt256.size ∧
    syncTimeElapsedInt postMint = 0 ∧
    mintFeeReserveProductNat (uniswapReserve0Word syncState)
        (uniswapReserve1Word syncState) <
      UInt256.size

def mintFeeOnKLastNonzeroPositiveWithLiquidityFromFactoryCaseData
    (feeTo : AccountAddress) (feeToWord amount0 amount1 balance0 balance1 reserve0 reserve1
      toWord : UInt256)
    (σFee : AccountMap) (evmFeeS : EVM.State) (I : ExecutionEnv) (memFee : ByteArray) :
    Prop :=
  UInt256.land feeToWord solcAddrMask ≠ ⟨0⟩ ∧
    mintFeeKLastSlotWord σFee I ≠ ⟨0⟩ ∧
    (∀ (rootK rootKLast : Int),
      0 ≤ rootK → rootK.toNat < UInt256.size →
      0 ≤ rootKLast → rootKLast.toNat < UInt256.size →
      mintFeeOnKLastNonzeroPositiveWithLiquidityCaseData feeTo evmFeeS σFee I
        feeToWord amount0 amount1 balance0 balance1 reserve0 reserve1 toWord memFee
        rootK rootKLast)

def mintFeeOnKLastNonzeroSuccessFromFactoryCasesData
    (feeTo : AccountAddress)
    (feeToWord totalSupply amount0 amount1 balance0 balance1 reserve0 reserve1 toWord
      liquidity : UInt256)
    (σFee : AccountMap) (evmFeeS : EVM.State) (I : ExecutionEnv) (memFee : ByteArray) :
    Prop :=
  mintFeeOnKLastNonzeroNoMintFromFactoryCaseData feeToWord totalSupply amount0 amount1
      balance0 balance1 reserve0 reserve1 toWord liquidity σFee evmFeeS I memFee ∨
    mintFeeOnKLastNonzeroPositiveNoLiquidityFromFactoryCaseData feeToWord totalSupply amount0
      amount1 balance0 balance1 reserve0 reserve1 toWord liquidity σFee evmFeeS I memFee ∨
    mintFeeOnKLastNonzeroPositiveWithLiquidityFromFactoryCaseData feeTo feeToWord amount0
      amount1 balance0 balance1 reserve0 reserve1 toWord σFee evmFeeS I memFee

set_option maxHeartbeats 3000000 in
theorem uniswapMintFeeOnKLastNonzeroPositiveWithLiquidityFromFactoryCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σ'' : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 outFee o o1 memFee : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 reserve0 reserve1 totalSupply toWord sel
      feeToWord : UInt256}
    {zFee : Bool}
    (feeTo : AccountAddress)
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
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) =
          .ok (.bool true))
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
    (hcall0 :
      typedCallViaEVM config
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
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 :
      typedCallViaEVM config evm0S (EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩))
        "balanceOf" 0 [.address evm0S.executionEnv.codeOwner] (true, evm1S, out1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
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
    (hfeeCall :
      typedCallViaEVM config evm1S (EVM.address (uniswapAddressAtSlot evm1S ⟨5⟩))
        "feeTo" 0 [] (true, evmFeeS, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some (.address feeTo))
    (hPostAccountsFee : accountMapEquiv σFee evmFeeS.accountMap)
    (henvFeeI : evmFeeS.executionEnv = I)
    (hcreatedFee : evmFeeS.createdAccounts = cAFee)
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
    (hruntimeReserve0 :
      reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I = reserve0)
    (hruntimeReserve1 :
      reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I = reserve1)
    (hamount0 :
      mintAmount0Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance0 =
        amount0)
    (hamount1 :
      mintAmount1Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance1 =
        amount1)
    (hkLastEq : mintFeeKLastWord evmFeeS = mintFeeKLastSlotWord σFee I)
    (htotalSlot : uniswapSlotWord ⟨0⟩ σFee I = totalSupply)
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = totalSupply)
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
      memFee
      feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (ho132 : 32 ≤ o1.size) (ho1Size : o1.size < UInt256.size)
    (houtFeeSize : outFee.size < UInt256.size)
    (hzFeeTrue : zFee = true)
    (houtFee32 : 32 ≤ outFee.size)
    (hfeeToWord : feeToWord = UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (hfeeTo : feeTo = AccountAddress.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (htoWord : toWord = mintToMaskedWord I)
    (hmemFee :
      memFee =
        feeToStaticcallMem
          (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
          outFee)
    (hcase :
      UInt256.land feeToWord solcAddrMask ≠ ⟨0⟩ ∧
        mintFeeKLastSlotWord σFee I ≠ ⟨0⟩ ∧
        (∀ (rootK rootKLast : Int),
          0 ≤ rootK → rootK.toNat < UInt256.size →
          0 ≤ rootKLast → rootKLast.toNat < UInt256.size →
          mintFeeOnKLastNonzeroPositiveWithLiquidityCaseData feeTo evmFeeS σFee I
            feeToWord amount0 amount1 balance0 balance1 reserve0 reserve1 toWord memFee
            rootK rootKLast)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  rcases hcase with ⟨hfeeToNonzero, hkLastNonzero, hcaseData⟩
  have hrootCase :
      ∀ (rootK rootKLast : Int),
        0 ≤ rootK → rootK.toNat < UInt256.size →
        0 ≤ rootKLast → rootKLast.toNat < UInt256.size →
        rootK > rootKLast ∧
          mintFeeNumeratorNat evmFeeS rootK rootKLast < UInt256.size ∧
          mintFeeRootTimesFiveNat rootK < UInt256.size ∧
          mintFeeDenominatorNat rootK rootKLast < UInt256.size ∧
          (mintFeeDenominatorWord rootK rootKLast).toNat ≠ 0 ∧
          mintFeeLiquidityInt evmFeeS rootK rootKLast > 0 ∧
          (mintFeeLiquidityInt evmFeeS rootK rootKLast).toNat < UInt256.size ∧
          mintFunctionTotalSupplyNewNat evmFeeS
              (mintFeeLiquidityWord evmFeeS rootK rootKLast) <
            UInt256.size ∧
          mintFunctionToBalanceNewNat evmFeeS feeTo
              (mintFeeLiquidityWord evmFeeS rootK rootKLast) <
            UInt256.size := by
    intro rootK rootKLast hrootKNonneg hrootKSize hrootKLastNonneg hrootKLastSize
    have hdata := hcaseData rootK rootKLast hrootKNonneg hrootKSize
      hrootKLastNonneg hrootKLastSize
    unfold mintFeeOnKLastNonzeroPositiveWithLiquidityCaseData at hdata
    rcases hdata with
      ⟨hroot, hnumFit, hrootFiveFit, hdenFit, hdenom, hfeeLiq, hfeeLiqFit,
        hfeeFitSupply, hfeeFitBalance, _⟩
    exact ⟨hroot, hnumFit, hrootFiveFit, hdenFit, hdenom, hfeeLiq, hfeeLiqFit,
      hfeeFitSupply, hfeeFitBalance⟩
  obtain ⟨rootK, rootKLast, k3701, C3701, hprefixRuntime, hrootKNonneg, hrootKSize,
      hrootKLastNonneg, hrootKLastSize, hroot, hnumFit, hrootFiveFit, hdenFit, hdenom,
      hfeeLiq, hfeeLiqFit, hfeeFitSupply, hfeeFitBalance, rd3701Raw⟩ :=
    uniswapMintFeeOnKLastNonzeroPositiveWithLiquidityRuntimeFromFactory feeTo
      hPostAccountsFee henvFeeI hperm rd7781 ho32 hoSize ho132 ho1Size houtFeeSize
      hzFeeTrue houtFee32 hfeeToWord hfeeTo hmemFee hruntimeReserve0 hruntimeReserve1
      (htotalEq.trans htotalSlot.symm) hfeeToNonzero hkLastNonzero hrootCase
  let feeLiquidity := mintFeeLiquidityWord evmFeeS rootK rootKLast
  let σAfterFee :=
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σFee ⟨0⟩
        (uniswapSlotWord ⟨0⟩ σFee I + feeLiquidity))
      (uniswapInternalMintBalanceHashSlot feeToWord
        (uniswapInternalMintBalanceHashMem feeToWord memFee))
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + feeLiquidity))
        (uniswapInternalMintBalanceHashSlot feeToWord memFee) + feeLiquidity)
  let memAfterFee :=
    uniswapInternalMintLogMem feeLiquidity
      (uniswapInternalMintBalanceHashMem feeToWord
        (uniswapInternalMintBalanceHashMem feeToWord memFee))
  let evmAfterFee := mintFunctionPostState evmFeeS feeTo feeLiquidity
  let totalSupplyAfterFee := uniswapSlotWord ⟨0⟩ σAfterFee I
  let liquidityAfterFee :=
    minFunctionResultWord (UInt256.div (UInt256.mul amount0 totalSupplyAfterFee) reserve0)
      (UInt256.div (UInt256.mul amount1 totalSupplyAfterFee) reserve1)
  have hdata := hcaseData rootK rootKLast hrootKNonneg hrootKSize hrootKLastNonneg
    hrootKLastSize
  unfold mintFeeOnKLastNonzeroPositiveWithLiquidityCaseData at hdata
  rcases hdata with
    ⟨_, _, _, _, _, _, _, _, _, htotalNonzero, hmulFit0, hmulFit1,
      hreserve0Nonzero, hreserve1Nonzero, hliqNonzero, htotalFit, hbalanceFit,
      hbalanceFitSource, hbound0, hbound1, helapsed0, hfitKLastRuntime,
      helapsedSource, hfitKLastSource⟩
  have hclean0 : UInt256.land reserve0 reserve112Mask = reserve0 := by
    rw [← hruntimeReserve0]
    exact reserve112Mask_clean_of_lt _ (reserve112Word_lt _)
  have hclean1 : UInt256.land reserve1 reserve112Mask = reserve1 := by
    rw [← hruntimeReserve1]
    exact reserve112Mask_clean_of_lt _ (reserve112Word_lt _)
  have hprefix :
      ExecBlock config
        (mintFeeAfterKLastFrame
          (uniswapReserve0Word
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
          (uniswapReserve1Word
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
          feeTo true (mintFeeKLastWord evmFeeS))
        evmFeeS
        [ .internalCall "sqrt" [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))]
            "rootK",
          .internalCall "sqrt" [.var "_kLast"] "rootKLast" ]
        (.ok
          (mintFeeAfterRootKLastFrame
            (uniswapReserve0Word
              (uniswapLockEnteredState
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
            (uniswapReserve1Word
              (uniswapLockEnteredState
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
            feeTo true (mintFeeKLastWord evmFeeS) rootK rootKLast)
          evmFeeS) := by
    simpa [hreserve0Eq, hreserve1Eq, hkLastEq] using hprefixRuntime
  have rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨1⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        mintToMaskedWord I, ⟨861⟩, sel]
      memAfterFee feeToStaticcallActiveWords outFee (cAFee, σAfterFee) k3701 C3701 := by
    simpa [feeLiquidity, memAfterFee, σAfterFee, htoWord] using rd3701Raw
  have hmem : memFee.size = 164 := by
    rw [hmemFee]
    exact feeToStaticcallMem_size_of_size_ge (UInt256.ofNat I.codeOwner.val) o o1 outFee
      ho32 hoSize ho132 ho1Size houtFee32 houtFeeSize
  have hmem64 :
      memFee.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    rw [hmemFee]
    exact feeToStaticcallMem_read64_of_size_ge (UInt256.ofNat I.codeOwner.val) o o1 outFee
      ho32 hoSize ho132 ho1Size houtFee32 houtFeeSize
  exact uniswapMintFeeOnKLastNonzeroPositiveWithLiquidityCase rootK rootKLast
    hcode hdispatch hsz36 hperm hwv houtFee32 hfeeToWord hfeeTo (by rfl) (by rfl)
    hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1 hle0Source hle1Source
    hfeeGuard hfeeCall hfeeDec hPostAccountsFee henvFeeI hcreatedFee hreserve0Eq
    hreserve1Eq hamount0 hamount1 hkLastEq (by rfl) hprefix hroot hrootKNonneg
    hrootKSize hrootKLastNonneg hnumFit hrootFiveFit hdenFit hdenom hfeeLiq
    hfeeLiqFit hfeeFitSupply hfeeFitBalance rd3701 hfeeToNonzero hkLastNonzero
    htotalNonzero hclean0 hclean1 hmulFit0 hmulFit1 hreserve0Nonzero hreserve1Nonzero
    (by rfl) hliqNonzero htotalFit
    (by
      simpa [σAfterFee, memAfterFee, totalSupplyAfterFee, liquidityAfterFee, htoWord] using
        hbalanceFit)
    (by simpa [evmAfterFee, feeLiquidity, liquidityAfterFee] using hbalanceFitSource)
    hbound0 hbound1
    (by
      simpa [σAfterFee, memAfterFee, totalSupplyAfterFee, liquidityAfterFee, htoWord] using
        helapsed0)
    (by simpa [evmAfterFee, feeLiquidity, liquidityAfterFee] using helapsedSource)
    (by
      simpa [σAfterFee, memAfterFee, totalSupplyAfterFee, liquidityAfterFee, htoWord] using
        hfitKLastRuntime)
    (by simpa [evmAfterFee, feeLiquidity, liquidityAfterFee] using hfitKLastSource)
    hmem hmem64

set_option maxHeartbeats 3000000 in
theorem uniswapMintFeeOnKLastNonzeroSuccessFromFactoryCases
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σ'' : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 outFee o o1 memFee : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 reserve0 reserve1 totalSupply liquidity toWord sel
      feeToWord : UInt256}
    {zFee : Bool}
    (feeTo : AccountAddress)
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
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) =
          .ok (.bool true))
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
    (hcall0 :
      typedCallViaEVM config
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
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 :
      typedCallViaEVM config evm0S (EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩))
        "balanceOf" 0 [.address evm0S.executionEnv.codeOwner] (true, evm1S, out1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
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
    (hfeeCall :
      typedCallViaEVM config evm1S (EVM.address (uniswapAddressAtSlot evm1S ⟨5⟩))
        "feeTo" 0 [] (true, evmFeeS, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some (.address feeTo))
    (hPostAccountsFee : accountMapEquiv σFee evmFeeS.accountMap)
    (henvFeeI : evmFeeS.executionEnv = I)
    (hcreatedFee : evmFeeS.createdAccounts = cAFee)
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
    (hruntimeReserve0 :
      reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I = reserve0)
    (hruntimeReserve1 :
      reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I = reserve1)
    (hamount0 :
      mintAmount0Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance0 =
        amount0)
    (hamount1 :
      mintAmount1Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance1 =
        amount1)
    (hkLastEq : mintFeeKLastWord evmFeeS = mintFeeKLastSlotWord σFee I)
    (htotalSlot : uniswapSlotWord ⟨0⟩ σFee I = totalSupply)
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = totalSupply)
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
      memFee
      feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (ho132 : 32 ≤ o1.size) (ho1Size : o1.size < UInt256.size)
    (houtFeeSize : outFee.size < UInt256.size)
    (hzFeeTrue : zFee = true)
    (houtFee32 : 32 ≤ outFee.size)
    (hfeeToWord : feeToWord = UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (hfeeTo : feeTo = AccountAddress.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (htoWord : toWord = mintToMaskedWord I)
    (hmemFee :
      memFee =
        feeToStaticcallMem
          (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
          outFee)
    (hliquidity :
      liquidity =
        minFunctionResultWord (UInt256.div (UInt256.mul amount0 totalSupply) reserve0)
          (UInt256.div (UInt256.mul amount1 totalSupply) reserve1))
    (hcase :
      mintFeeOnKLastNonzeroSuccessFromFactoryCasesData feeTo feeToWord totalSupply amount0
        amount1 balance0 balance1 reserve0 reserve1 toWord liquidity σFee evmFeeS I memFee) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  rcases hcase with hnoMint | hrest
  · exact
      uniswapMintFeeOnKLastNonzeroNoMintFromFactoryCase feeTo hcode hdispatch hsz36
        hperm hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1 hle0Source
        hle1Source hfeeGuard hfeeCall hfeeDec hPostAccountsFee henvFeeI hcreatedFee
        hreserve0Eq hreserve1Eq hruntimeReserve0 hruntimeReserve1 hamount0 hamount1
        hkLastEq htotalSlot htotalEq rd7781 ho32 hoSize ho132 ho1Size houtFeeSize
        hzFeeTrue houtFee32 hfeeToWord hfeeTo htoWord hmemFee hliquidity
        (by simpa [mintFeeOnKLastNonzeroNoMintFromFactoryCaseData] using hnoMint)
  rcases hrest with hposNoLiquidity | hposWithLiquidity
  · exact
      uniswapMintFeeOnKLastNonzeroPositiveNoLiquidityFromFactoryCase feeTo hcode hdispatch
        hsz36 hperm hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1
        hle0Source hle1Source hfeeGuard hfeeCall hfeeDec hPostAccountsFee henvFeeI
        hcreatedFee hreserve0Eq hreserve1Eq hruntimeReserve0 hruntimeReserve1 hamount0
        hamount1 hkLastEq htotalSlot htotalEq rd7781 ho32 hoSize ho132 ho1Size
        houtFeeSize hzFeeTrue houtFee32 hfeeToWord hfeeTo htoWord hmemFee hliquidity
        (by
          simpa [mintFeeOnKLastNonzeroPositiveNoLiquidityFromFactoryCaseData] using
            hposNoLiquidity)
  · exact
      uniswapMintFeeOnKLastNonzeroPositiveWithLiquidityFromFactoryCase feeTo hcode
        hdispatch hsz36 hperm hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1
        hdec1 hle0Source hle1Source hfeeGuard hfeeCall hfeeDec hPostAccountsFee henvFeeI
        hcreatedFee hreserve0Eq hreserve1Eq hruntimeReserve0 hruntimeReserve1 hamount0
        hamount1 hkLastEq htotalSlot htotalEq rd7781 ho32 hoSize ho132 ho1Size
        houtFeeSize hzFeeTrue houtFee32 hfeeToWord hfeeTo htoWord hmemFee
        (by
          simpa [mintFeeOnKLastNonzeroPositiveWithLiquidityFromFactoryCaseData] using
            hposWithLiquidity)

set_option maxHeartbeats 3000000 in
theorem uniswapMintFeeOnKLastNonzeroSmallNoMintFromFactoryCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σ'' : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 outFee o o1 memFee : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 reserve0 reserve1 totalSupply liquidity toWord sel
      feeToWord : UInt256}
    {zFee : Bool}
    (feeTo : AccountAddress)
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
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) =
          .ok (.bool true))
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
    (hcall0 :
      typedCallViaEVM config
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
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 :
      typedCallViaEVM config evm0S (EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩))
        "balanceOf" 0 [.address evm0S.executionEnv.codeOwner] (true, evm1S, out1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
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
    (hfeeCall :
      typedCallViaEVM config evm1S (EVM.address (uniswapAddressAtSlot evm1S ⟨5⟩))
        "feeTo" 0 [] (true, evmFeeS, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some (.address feeTo))
    (hPostAccountsFee : accountMapEquiv σFee evmFeeS.accountMap)
    (henvFeeI : evmFeeS.executionEnv = I)
    (hcreatedFee : evmFeeS.createdAccounts = cAFee)
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
    (hruntimeReserve0 :
      reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I = reserve0)
    (hruntimeReserve1 :
      reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I = reserve1)
    (hamount0 :
      mintAmount0Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance0 =
        amount0)
    (hamount1 :
      mintAmount1Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance1 =
        amount1)
    (hkLastEq : mintFeeKLastWord evmFeeS = mintFeeKLastSlotWord σFee I)
    (htotalSlot : uniswapSlotWord ⟨0⟩ σFee I = totalSupply)
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = totalSupply)
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
      memFee
      feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (ho132 : 32 ≤ o1.size) (ho1Size : o1.size < UInt256.size)
    (houtFeeSize : outFee.size < UInt256.size)
    (hzFeeTrue : zFee = true)
    (houtFee32 : 32 ≤ outFee.size)
    (hfeeToWord : feeToWord = UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (hfeeTo : feeTo = AccountAddress.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (htoWord : toWord = mintToMaskedWord I)
    (hmemFee :
      memFee =
        feeToStaticcallMem
          (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
          outFee)
    (hliquidity :
      liquidity =
        minFunctionResultWord (UInt256.div (UInt256.mul amount0 totalSupply) reserve0)
          (UInt256.div (UInt256.mul amount1 totalSupply) reserve1))
    (hcase :
      UInt256.land feeToWord solcAddrMask ≠ ⟨0⟩ ∧
        mintFeeKLastSlotWord σFee I ≠ ⟨0⟩ ∧
        (UInt256.mul reserve0 reserve1).toNat ≤ 3 ∧
        (mintFeeKLastSlotWord σFee I).toNat ≤ 3 ∧
        (if UInt256.mul reserve0 reserve1 = ⟨0⟩ then (⟨0⟩ : UInt256) else ⟨1⟩).toNat ≤
          (if mintFeeKLastSlotWord σFee I = ⟨0⟩ then (⟨0⟩ : UInt256) else ⟨1⟩).toNat ∧
        totalSupply ≠ ⟨0⟩ ∧
        amount0.toNat * totalSupply.toNat < UInt256.size ∧
        amount1.toNat * totalSupply.toNat < UInt256.size ∧
        reserve0 ≠ ⟨0⟩ ∧ reserve1 ≠ ⟨0⟩ ∧
        liquidity ≠ ⟨0⟩ ∧
        totalSupply.toNat + liquidity.toNat < UInt256.size ∧
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (totalSupply + liquidity))
          (uniswapInternalMintBalanceHashSlot toWord memFee)).toNat + liquidity.toNat <
          UInt256.size ∧
        mintFunctionToBalanceNewNat evmFeeS (AccountAddress.ofNat (mintToWord I).toNat)
            liquidity <
          UInt256.size ∧
        balance0.toNat ≤ reserve112Mask.toNat ∧
        balance1.toNat ≤ reserve112Mask.toNat ∧
        UInt256.land
            (uniswapUpdateElapsedWord
              (uniswapSlotWord ⟨8⟩
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (totalSupply + liquidity))
                  (uniswapInternalMintBalanceHashSlot toWord
                    (uniswapInternalMintBalanceHashMem toWord memFee))
                  (uniswapCodeOwnerStorageWord I
                    (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (totalSupply + liquidity))
                    (uniswapInternalMintBalanceHashSlot toWord memFee) +
                    liquidity)) I) I) reserve32Mask =
          ⟨0⟩ ∧
        (let σAfterMint :=
          sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (totalSupply + liquidity))
            (uniswapInternalMintBalanceHashSlot toWord
              (uniswapInternalMintBalanceHashMem toWord memFee))
            (uniswapCodeOwnerStorageWord I
              (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (totalSupply + liquidity))
              (uniswapInternalMintBalanceHashSlot toWord memFee) + liquidity)
        let packed := uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σAfterMint I)
          (uniswapUpdateTimestampWord I) balance1 balance0
        let σPacked := sstoreAccountMap I.codeOwner σAfterMint ⟨8⟩ packed
        (UInt256.land (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Mask).toNat *
            (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Shift)
              reserve112Mask).toNat <
          UInt256.size) ∧
        syncTimeElapsedInt
            (mintFunctionPostState evmFeeS (AccountAddress.ofNat (mintToWord I).toNat)
              liquidity) =
          0 ∧
        mintFeeReserveProductNat
            (uniswapReserve0Word
              (syncUpdatePackedReserveState
                (mintFunctionPostState evmFeeS (AccountAddress.ofNat (mintToWord I).toNat)
                  liquidity)
                balance0 balance1))
            (uniswapReserve1Word
              (syncUpdatePackedReserveState
                (mintFunctionPostState evmFeeS (AccountAddress.ofNat (mintToWord I).toNat)
                  liquidity)
                balance0 balance1)) <
          UInt256.size) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  rcases hcase with
    ⟨hfeeToNonzero, hkLastNonzero, hprodSmall, hkLastSmall, hrootLeRuntime,
      htotalNonzero, hmulFit0, hmulFit1, hreserve0Nonzero, hreserve1Nonzero,
      hliqNonzero, htotalFit, hbalanceFit, hbalanceFitSource, hbound0, hbound1,
      helapsed0, hfitKLastRuntime, helapsedSource, hfitKLastSource⟩
  have hclean0 : UInt256.land reserve0 reserve112Mask = reserve0 :=
    by
      rw [← hruntimeReserve0]
      exact reserve112Mask_clean_of_lt _ (reserve112Word_lt _)
  have hclean1 : UInt256.land reserve1 reserve112Mask = reserve1 :=
    by
      rw [← hruntimeReserve1]
      exact reserve112Mask_clean_of_lt _ (reserve112Word_lt _)
  have hclean0Runtime :
      UInt256.land (reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)
          reserve112Mask =
        reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I := by
    exact reserve112Mask_clean_of_lt _ (reserve112Word_lt _)
  have hclean1Runtime :
      UInt256.land (reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)
          reserve112Mask =
        reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I := by
    exact reserve112Mask_clean_of_lt _ (reserve112Word_lt _)
  obtain ⟨k3701, C3701, rd3701Raw⟩ :=
    uniswapMintFeeRuntimeFactoryResultFeeOnKLastNonzeroBothSqrtSmallNoMintReturn
      (by simpa [hmemFee] using rd7781) ho32 hoSize ho132 ho1Size houtFeeSize hzFeeTrue houtFee32
      (by simpa [hfeeToWord] using hfeeToNonzero) hkLastNonzero hclean0Runtime hclean1Runtime
      (by simpa [hruntimeReserve0, hruntimeReserve1] using hprodSmall)
      hkLastSmall
      (by simpa [hruntimeReserve0, hruntimeReserve1] using hrootLeRuntime)
  have rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨1⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        mintToMaskedWord I, ⟨861⟩, sel]
      memFee feeToStaticcallActiveWords outFee (cAFee, σFee) k3701 C3701 := by
    simpa [hruntimeReserve0, hruntimeReserve1, htoWord, hmemFee] using rd3701Raw
  have hmem : memFee.size = 164 := by
    rw [hmemFee]
    exact feeToStaticcallMem_size_of_size_ge (UInt256.ofNat I.codeOwner.val) o o1 outFee
      ho32 hoSize ho132 ho1Size houtFee32 houtFeeSize
  have hmem64 :
      memFee.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    rw [hmemFee]
    exact feeToStaticcallMem_read64_of_size_ge (UInt256.ofNat I.codeOwner.val) o o1 outFee
      ho32 hoSize ho132 ho1Size houtFee32 houtFeeSize
  exact uniswapMintFeeOnKLastNonzeroSmallNoMintCase hcode hdispatch hsz36 hperm
    hwv houtFee32 hfeeToWord hfeeTo hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1
    hdec1 hle0Source hle1Source hfeeGuard hfeeCall hfeeDec hPostAccountsFee henvFeeI
    hcreatedFee hreserve0Eq hreserve1Eq hamount0 hamount1 hkLastEq htotalSlot htotalEq
    rd3701 hfeeToNonzero hkLastNonzero hrootLeRuntime htotalNonzero hclean0 hclean1
    hprodSmall hkLastSmall hmulFit0 hmulFit1 hreserve0Nonzero hreserve1Nonzero
    hliquidity hliqNonzero htotalFit (by simpa [htoWord] using hbalanceFit)
    hbalanceFitSource hbound0 hbound1 (by simpa [htoWord] using helapsed0)
    helapsedSource (by simpa [htoWord] using hfitKLastRuntime) hfitKLastSource hmem hmem64

end UniswapV2Pair
