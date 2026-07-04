import Benchmarks.UniswapV3Pool.Uint128

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.UniswapV3Pool

abbrev positionsArgWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev positionsArgValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width (EVM.Word.toBytesBE (positionsArgWord I))

abbrev positionsArgKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width (EVM.Word.toBytesBE (positionsArgWord I))

abbrev positionsStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "arg0" (positionsArgValue I)

abbrev positionsBaseSlot (I : ExecutionEnv) : UInt256 :=
  positionsBase (positionsArgKey I)

abbrev positionsPackedSlot (I : ExecutionEnv) : UInt256 :=
  positionsBaseSlot I + ⟨3⟩

abbrev positionsShift : UInt256 :=
  UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩

abbrev positionsLiquidityWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (solcSlotWord σ I (positionsBaseSlot I)) uint128Mask

abbrev positionsFeeGrowthInside0Word (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (positionsBaseSlot I + ⟨1⟩)

abbrev positionsFeeGrowthInside1Word (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (positionsBaseSlot I + ⟨2⟩)

abbrev positionsPackedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (positionsPackedSlot I)

abbrev positionsTokensOwed0Word (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (positionsPackedWord σ I) uint128Mask

abbrev positionsTokensOwed1Word (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (UInt256.div (positionsPackedWord σ I) positionsShift) uint128Mask

def positionsReturnValues (σ : AccountMap) (I : ExecutionEnv) : List Value :=
  [ .int (Int.ofNat (positionsLiquidityWord σ I).toNat),
    .int (Int.ofNat (positionsFeeGrowthInside0Word σ I).toNat),
    .int (Int.ofNat (positionsFeeGrowthInside1Word σ I).toNat),
    .int (Int.ofNat (positionsTokensOwed0Word σ I).toNat),
    .int (Int.ofNat (positionsTokensOwed1Word σ I).toNat) ]

theorem positionsArgSlice_eq_toBytesBE {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (I.calldata.toList.drop 4).take 32 = EVM.Word.toBytesBE (positionsArgWord I) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hlen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword := decode_word_at_eq I.calldata 4 (by omega : 4 + 32 ≤ I.calldata.size)
    (by native_decide : 4 < 2 ^ 64)
  calc
    (I.calldata.toList.drop 4).take 32 =
        EVM.Word.toBytesBE (ABI.bytesToWord ((I.calldata.toList.drop 4).take 32)) := by
      exact (toBytesBE_bytesToWord_of_length hlen).symm
    _ = EVM.Word.toBytesBE (positionsArgWord I) := by
      rw [hword]

theorem positionsBaseSlot_eq_solcMappingSlot (I : ExecutionEnv) :
    positionsBaseSlot I = solcMappingSlot ⟨7⟩ (positionsArgWord I) := by
  have hkey :
      keyValueToWord (KeyValue.fixedBytes bytes32Width
        (EVM.Word.toBytesBE (positionsArgWord I))) = positionsArgWord I := by
    simpa [bytes32Width] using keyValueToWord_fixedBytes32 (positionsArgWord I)
  unfold positionsBaseSlot positionsBase positionsArgKey mapSlot solcMappingSlot
  rw [hkey]

private theorem decodeCalldataWithMode_legacy_bytes32_ok {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiBytes32] cd =
      some ((∅ : Solm.Store).insert x
        (.fixedBytes abiBytes32Width ((cd.toList.drop 4).take 32))) := by
  unfold decodeCalldataWithMode decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hnot4 : ¬ cd.toList.length < 4 := by
    rw [htlen]
    omega
  rw [if_neg hnot4]
  have hnotDyn : ¬ ([abiBytes32].any isDynamicABIType = true ∧ 2 ^ 255 ≤ cd.toList.length) := by
    simp [abiBytes32, isDynamicABIType]
  rw [if_neg hnotDyn]
  have hread : readBytes? (cd.toList.drop 4) 0 32 =
      some ((cd.toList.drop 4).take 32) := by
    unfold readBytes?
    have hlen : (((cd.toList.drop 4).drop 0).take 32).length = 32 := by
      rw [List.drop_zero, List.length_take, List.length_drop, htlen]
      omega
    rw [if_pos hlen, List.drop_zero]
  have hblen : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake : List.take 32 ((cd.toList.drop 4).take 32) = (cd.toList.drop 4).take 32 :=
    List.take_of_length_le (by rw [hblen])
  have hnotArgShort : ¬ cd.toList.length - 4 < 32 := by
    rw [htlen]
    omega
  simp [decodeCalldata.decodeArgs, decodeCalldata.insertValues, abiBytes32,
    ABI.decodeABIValues?, ABI.decodeABIValue?, isDynamicABIType, staticABIEncodedSize?,
    abiTupleHeadSize?, hread, abiBytes32Width, htake, hnotArgShort]

private theorem decodeCalldataWithMode_legacy_bytes32_none_short {cd : ByteArray}
    {x : Solm.Ident} (hshort : cd.size < 36) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiBytes32] cd = none := by
  unfold decodeCalldataWithMode decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hnotDyn : ¬ ([abiBytes32].any isDynamicABIType = true ∧ 2 ^ 255 ≤ cd.toList.length) := by
    simp [abiBytes32, isDynamicABIType]
  by_cases hsz4 : cd.size < 4
  · rw [if_pos (by rw [htlen]; omega : cd.toList.length < 4)]
  · rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
    rw [if_neg hnotDyn]
    have hread : readBytes? (cd.toList.drop 4) 0 32 = none := by
      unfold readBytes?
      have hlen : ¬ (((cd.toList.drop 4).drop 0).take 32).length = 32 := by
        rw [List.drop_zero, List.length_take, List.length_drop, htlen]
        omega
      rw [if_neg hlen]
    simp [decodeCalldata.decodeArgs, abiBytes32, ABI.decodeABIValues?, ABI.decodeABIValue?,
      isDynamicABIType, staticABIEncodedSize?, abiTupleHeadSize?, hread]

theorem uniswapV3PoolPositionsDecodeOk {v : PoolImmutables} {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode
      (positionsTransition.params.map Param.name)
      (transitionSignature positionsTransition).paramTypes I.calldata =
        some (positionsStore I) := by
  have hdecode := decodeCalldataWithMode_legacy_bytes32_ok
    (cd := I.calldata) (x := "arg0") hsz36
  have hslice := positionsArgSlice_eq_toBytesBE (I := I) hsz36
  simpa [config, positionsTransition, transitionSignature, positionsStore, positionsArgValue,
    bytes32, bytes32Width, abiBytes32, abiBytes32Width, hslice] using hdecode

theorem uniswapV3PoolPositionsDecodeShort {v : PoolImmutables} {I : ExecutionEnv}
    (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode (config v).abiDecodeMode
      (positionsTransition.params.map Param.name)
      (transitionSignature positionsTransition).paramTypes I.calldata = none := by
  simpa [config, positionsTransition, transitionSignature, bytes32, bytes32Width, abiBytes32,
    abiBytes32Width] using
      decodeCalldataWithMode_legacy_bytes32_none_short (cd := I.calldata) (x := "arg0") hshort

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolDispatch_positions {v : PoolImmutables} {cd : ByteArray}
    (hsel : (uniswapV3PoolSelBytes 11 == cd.extract 0 4) = true) :
    dispatchMsg (contract v) cd = some positionsTransition := by
  apply dispatchMsg_eq_some_of_split
    (pre := [burnTransition, collectTransition v, collectprotocolTransition v, factoryTransition v,
      feeTransition v, feegrowthglobal0X128Transition, feegrowthglobal1X128Transition,
      flashTransition v, increaseobservationcardinalitynextTransition v, initializeTransition,
      liquidityTransition, maxliquiditypertickTransition v, mintTransition v, observationsTransition,
      observeTransition v])
    (post := [protocolfeesTransition, setfeeprotocolTransition v, slot0Transition,
      snapshotcumulativesinsideTransition v, swapTransition v, tickbitmapTransition,
      tickspacingTransition v, ticksTransition, token0Transition v, token1Transition v])
  · simp [contract, transitions]
  · intro t ht
    simp at ht
    rcases ht with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    · rw [selectorOf, burnSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 17) (j := 11)
          (by native_decide) hsel
    · rw [selectorOf, collectSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 10) (j := 11)
          (by native_decide) hsel
    · rw [selectorOf, collectProtocolSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 15) (j := 11)
          (by native_decide) hsel
    · rw [selectorOf, factorySelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 19) (j := 11)
          (by native_decide) hsel
    · rw [selectorOf, feeSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 22) (j := 11)
          (by native_decide) hsel
    · rw [selectorOf, feeGrowthGlobal0X128SelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 23) (j := 11)
          (by native_decide) hsel
    · rw [selectorOf, feeGrowthGlobal1X128SelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 8) (j := 11)
          (by native_decide) hsel
    · rw [selectorOf, flashSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 9) (j := 11)
          (by native_decide) hsel
    · rw [selectorOf, increaseObservationCardinalityNextSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 5) (j := 11)
          (by native_decide) hsel
    · rw [selectorOf, initializeSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 25) (j := 11)
          (by native_decide) hsel
    · rw [selectorOf, liquiditySelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 2) (j := 11)
          (by native_decide) hsel
    · rw [selectorOf, maxLiquidityPerTickSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 13) (j := 11)
          (by native_decide) hsel
    · rw [selectorOf, mintSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 7) (j := 11)
          (by native_decide) hsel
    · rw [selectorOf, observationsSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 4) (j := 11)
          (by native_decide) hsel
    · rw [selectorOf, observeSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 16) (j := 11)
          (by native_decide) hsel
  · rw [selectorOf, positionsSelectorBytes]
    simpa [uniswapV3PoolSelBytes] using hsel

private theorem uniswapV3PoolPatchPreservesJumpDest8093 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨8093⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched8093 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨8093⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest8093

theorem uniswapV3PoolPositionsReachEntry {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 11 == I.calldata.extract 0 4) = true) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨1357⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := uniswapV3PoolReachSelector32
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize
  have hword : solcSelectorWord I = uniswapV3PoolSelNat 11 := by
    simpa [uniswapV3PoolSelBytes, uniswapV3PoolSelNat] using
      solcSelectorWord_eq_of_beq I hsz 0x51 0x4e 0xa4 0xbf
        (uniswapV3PoolSelNat 11) (by native_decide) hsel
  have hgt32 : UInt256.gt (armSelNat code ⟨32⟩) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h239 := uniswapV3PoolSelectorSplitTakenTo (next := ⟨239⟩) hpatch h32 hgt32
  have hgt239 : UInt256.gt (armSelNat code ⟨239⟩) (solcSelectorWord I) = ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h250 := uniswapV3PoolSelectorSplitNotTakenTo (next := ⟨250⟩) hpatch h239 hgt239
  have hgt250 : UInt256.gt (armSelNat code ⟨250⟩) (solcSelectorWord I) = ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h261 := uniswapV3PoolSelectorSplitNotTakenTo (next := ⟨261⟩) hpatch h250 hgt250
  have hmiss9 : (uniswapV3PoolSelBytes 9 == I.calldata.extract 0 4) = false :=
    uniswapV3PoolSelectorMissOfHit I (by native_decide) hsel
  have h272 := uniswapV3PoolSelectorArmMissToOf (i := 9) (next := ⟨272⟩)
    hpatch hsz hmiss9 h261
  have hmiss10 : (uniswapV3PoolSelBytes 10 == I.calldata.extract 0 4) = false :=
    uniswapV3PoolSelectorMissOfHit I (by native_decide) hsel
  have h283 := uniswapV3PoolSelectorArmMissToOf (i := 10) (next := ⟨283⟩)
    hpatch hsz hmiss10 h272
  have h1357 := uniswapV3PoolSelectorArmHitTo (i := 11) (target := ⟨1357⟩)
    hpatch hsz hsel h283
  exact ⟨_, _, h1357⟩

private theorem uniswapV3PoolPositionsDecodedReachRoutine {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {de ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨1379⟩ (de :: ⟨4⟩ :: ret :: R) mem aw rdata acc k C)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8093⟩ (positionsArgWord ee :: ret :: R)
      mem aw rdata acc k' C' := by
  have rd1380 : RD code ee g s0 ⟨1380⟩ (de :: ⟨4⟩ :: ret :: R)
      mem aw rdata acc (k + 1) (C + 1) := by
    simpa using h.jumpdest
      (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide)
      (by evm_ov)
  have rd1381 : RD code ee g s0 ⟨1381⟩ (⟨4⟩ :: ret :: R)
      mem aw rdata acc (k + 1 + 1) (C + 1 + 2) := by
    simpa using rd1380.pop
      (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide)
      (by evm_ov)
  have rd1382 : RD code ee g s0 ⟨1382⟩ (positionsArgWord ee :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1) (C + 1 + 2 + 3) := by
    simpa [positionsArgWord, calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      using (rd1381.calldataload
        (by
          rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
          native_decide)
        (by evm_ov))
  have rd1385 : RD code ee g s0 ⟨1385⟩ (⟨8093⟩ :: positionsArgWord ee :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1 + 1) (C + 1 + 2 + 3 + 3) := by
    simpa using rd1382.push2 ⟨8093⟩
      (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide)
      (by evm_ov)
  exact ⟨_, _, rd1385.jump
    (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide)
    (uniswapV3PoolJumpDestPatched8093 hpatch)
    (by evm_ov)⟩

set_option maxHeartbeats 3000000 in
private theorem uniswapV3PoolPositionsExternalLenOk {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨1357⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨1379⟩
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ⟨1386⟩ ::
        [solcSelectorWord I])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  exact RD.solcExternalStaticArgsLenOk (need := ⟨32⟩)
    (entry := ⟨1357⟩) (ret := ⟨1386⟩) (decoded := ⟨1379⟩) hreach
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (uniswapV3PoolJumpDestPatched2258 hpatch (by native_decide))
    (solcDecodeLenCheckOkUnsigned (by simpa using hsz36) hsize)

theorem uniswapV3PoolPositionsEvmDecodeShort {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 11 == I.calldata.extract 0 4) = true)
    (hshort : I.calldata.size < 36) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  have hreach := uniswapV3PoolPositionsReachEntry
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize hsel
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by
      rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      omega) hsize]
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
    rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]
    omega
  exact RD.solcExternalStaticArgsShortReverts (need := ⟨32⟩)
    (entry := ⟨1357⟩) (ret := ⟨1386⟩) (decoded := ⟨1379⟩) hreach
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    hlt

private theorem uniswapV3PoolPositionsRoutinePatchDisjoint1 {v : PoolImmutables}
    {pc : UInt256} (hlo : 8093 ≤ pc.toNat) (hhi : pc.toNat + 1 ≤ 8174) :
    ∀ p ∈ patches v, pc.toNat + 1 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  all_goals omega

private theorem uniswapV3PoolPositionsRoutinePatchDisjoint2 {v : PoolImmutables}
    {pc : UInt256} (hlo : 8093 ≤ pc.toNat) (hhi : pc.toNat + 2 ≤ 8174) :
    ∀ p ∈ patches v, pc.toNat + 2 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  all_goals omega

private theorem uniswapV3PoolPositionsDecodePatchedPush1 {v : PoolImmutables}
    {code : ByteArray} {pc n : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hwin : pc.toNat + 2 ≤ uniswapV3PoolBytecode.size)
    (hdisj : ∀ p ∈ patches v, pc.toNat + 2 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat)
    (hgetTemplate : uniswapV3PoolBytecode.get? pc.toNat = some 0x60)
    (hval : uInt256OfByteArray
        (uniswapV3PoolBytecode.extract' pc.toNat.succ (pc.toNat.succ + 1)) = n) :
    decode code pc = some (.Push .PUSH1, some (n, 1)) := by
  have hsize := uniswapV3PoolPatchedSize hpatch
  have htemplate64 : uniswapV3PoolBytecode.size < 2 ^ 64 := by native_decide
  have hget : code.get? pc.toNat = uniswapV3PoolBytecode.get? pc.toNat := by
    apply get?_eq_of_extract_one
    · rw [hsize]
      omega
    · omega
    · exact patchRuntime_extract_eq (start := pc.toNat) (stop := pc.toNat + 1)
        (template := uniswapV3PoolBytecode) (out := code) (ps := patches v)
        (by omega) (by omega)
        (fun p hp => by
          rcases hdisj p hp with hbefore | hafter
          · exact Or.inl (by omega)
          · exact Or.inr hafter)
        hpatch
  have hextract :
      code.extract' pc.toNat.succ (pc.toNat.succ + 1) =
        uniswapV3PoolBytecode.extract' pc.toNat.succ (pc.toNat.succ + 1) := by
    unfold ByteArray.extract'
    have hguard :
        (decide (pc.toNat.succ < 2 ^ 64) && decide (pc.toNat.succ + 1 < 2 ^ 64)) =
          true := by
      rw [Bool.and_eq_true]
      constructor <;> rw [decide_eq_true_eq] <;> omega
    rw [if_pos hguard, if_pos hguard]
    exact patchRuntime_extract_eq (start := pc.toNat.succ) (stop := pc.toNat.succ + 1)
      (template := uniswapV3PoolBytecode) (out := code) (ps := patches v)
      (by omega) (by omega)
      (fun p hp => by
        rcases hdisj p hp with hbefore | hafter
        · exact Or.inl hbefore
        · exact Or.inr (by omega))
      hpatch
  have hgetSome : code.get? pc.toNat = some 0x60 := by
    rw [hget, hgetTemplate]
  have hparse : (some (0x60 : UInt8) >>= parseInstr) = some (.Push .PUSH1) := by
    native_decide
  unfold decode
  rw [hgetSome, hparse]
  change some (Operation.Push Operation.POp.PUSH1,
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 1)), 1)) =
    some (Operation.Push Operation.POp.PUSH1, some (n, 1))
  rw [hextract, hval]

theorem positionsStore_arg0 (I : ExecutionEnv) :
    Std.HashMap.get? (positionsStore I) "arg0" = some (positionsArgValue I) := by
  simp [positionsStore]

theorem evalExpr_positions_arg0 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := positionsStore I } evm
      (.var "arg0") = .ok (positionsArgValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [positionsStore_arg0]

def positionsEvaledRef (I : ExecutionEnv) (field : Ident) : EvaledStorageRef :=
  { base := "positions", steps := [.mindex (positionsArgKey I), .field field] }

theorem evalStorageRef_positions {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) (field : Ident) :
    evalStorageRef (config v) { contract := contract v, locals := positionsStore I } evm
      (positionsF (.var "arg0") field) = .ok (positionsEvaledRef I field) := by
  have hlen : (EVM.Word.toBytesBE (positionsArgWord I)).length = bytes32Width.val + 1 := by
    simpa [bytes32Width] using word_toBytesBE_toByteArray_size (positionsArgWord I)
  simp [evalStorageRef, evalStorageRefStep, evalStorageRefSteps, positionsF,
    positionsEvaledRef, evalExpr_positions_arg0, positionsArgValue, positionsArgKey,
    valueToKey?, hlen, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem positionsStorageLocLoad_liquidity (evm : EVM.State) (I : ExecutionEnv) :
    storageLocLoad evm
        (loc (positionsBaseSlot I) ⟨0, by decide⟩ ⟨16, by decide⟩ (by decide)
          (.int uint128Int)) =
      .int (Int.ofNat (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (positionsBaseSlot I))
        uint128Mask).toNat) := by
  rw [← show UInt256.ofNat (2 ^ (8 * 16) - 1) = uint128Mask by native_decide]
  simpa [loc, uint128Int] using
    storageLocLoad_uint_offset0 evm (positionsBaseSlot I) (16 : Fin 33) ⟨128, by decide⟩
      (hbound := by decide) (by decide)

theorem positionsStorageLocLoad_feeGrowthInside0 (evm : EVM.State) (I : ExecutionEnv) :
    storageLocLoad evm
        (loc (positionsBaseSlot I + ⟨1⟩) ⟨0, by decide⟩ ⟨32, by decide⟩
          (by decide) (.int uint256Int)) =
      .int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (positionsBaseSlot I + ⟨1⟩)).toNat) := by
  simpa [loc, uint256Loc] using
    storageLocLoad_uint256 evm (positionsBaseSlot I + ⟨1⟩)

theorem positionsStorageLocLoad_feeGrowthInside1 (evm : EVM.State) (I : ExecutionEnv) :
    storageLocLoad evm
        (loc (positionsBaseSlot I + ⟨2⟩) ⟨0, by decide⟩ ⟨32, by decide⟩
          (by decide) (.int uint256Int)) =
      .int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (positionsBaseSlot I + ⟨2⟩)).toNat) := by
  simpa [loc, uint256Loc] using
    storageLocLoad_uint256 evm (positionsBaseSlot I + ⟨2⟩)

theorem positionsStorageLocLoad_tokensOwed0 (evm : EVM.State) (I : ExecutionEnv) :
    storageLocLoad evm
        (loc (positionsPackedSlot I) ⟨0, by decide⟩ ⟨16, by decide⟩ (by decide)
          (.int uint128Int)) =
      .int (Int.ofNat (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (positionsPackedSlot I))
        uint128Mask).toNat) := by
  rw [← show UInt256.ofNat (2 ^ (8 * 16) - 1) = uint128Mask by native_decide]
  simpa [loc, uint128Int] using
    storageLocLoad_uint_offset0 evm (positionsPackedSlot I) (16 : Fin 33) ⟨128, by decide⟩
      (hbound := by decide) (by decide)

theorem positionsStorageLocLoad_tokensOwed1 (evm : EVM.State) (I : ExecutionEnv) :
    storageLocLoad evm
        (loc (positionsPackedSlot I) ⟨16, by decide⟩ ⟨16, by decide⟩ (by decide)
          (.int uint128Int)) =
      .int (Int.ofNat (UInt256.land
        (UInt256.div
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (positionsPackedSlot I))
          positionsShift) uint128Mask).toNat) := by
  rw [← show UInt256.ofNat (256 ^ 16) = positionsShift by native_decide]
  rw [← show UInt256.ofNat (256 ^ 16 - 1) = uint128Mask by native_decide]
  simpa [loc, uint128Int] using
    storageLocLoad_uint_offset evm (positionsPackedSlot I) (16 : Fin 32) (16 : Fin 33)
      ⟨128, by decide⟩ (by decide) (by decide)

theorem uniswapV3PoolPositionsSourceBody {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (positionsStore I) positionsTransition.body
      (.returned { contract := contract v, locals := positionsStore I }
        (initState cA gh bl σ σ₀ g A I)
        (some (positionsReturnValues σ I))) := by
  change ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (positionsStore I)
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return [ .storage (positionsF (.var "arg0") "liquidity"),
          .storage (positionsF (.var "arg0") "feeGrowthInside0LastX128"),
          .storage (positionsF (.var "arg0") "feeGrowthInside1LastX128"),
          .storage (positionsF (.var "arg0") "tokensOwed0"),
          .storage (positionsF (.var "arg0") "tokensOwed1") ] ] _
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by simp [initState, hwv]))) <|
      ExecBlock.consReturn <| ExecStmt.return (by
        have hliq :
            evalExpr? (config v) { contract := contract v, locals := positionsStore I }
              (initState cA gh bl σ σ₀ g A I)
              (.storage (positionsF (.var "arg0") "liquidity")) =
            .ok (.int (Int.ofNat (positionsLiquidityWord σ I).toNat)) := by
          apply evalExpr_storage_scalar_value
              (er := positionsEvaledRef I "liquidity")
              (t := .int uint128Int)
              (loc := loc (positionsBaseSlot I) ⟨0, by decide⟩ ⟨16, by decide⟩
                (by decide) (.int uint128Int))
          · simp [positionsStore, positionsF]
          · exact evalStorageRef_positions (v := v) (initState cA gh bl σ σ₀ g A I) I
              "liquidity"
          · simp [positionsEvaledRef, contract, storageDecls, storageTypeAt?,
              storageTypeStep?, positionInfoStructTy, uint128St]
          · funext evm
            simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
              positionsEvaledRef, positionsBaseSlot, loc]
          · simpa [initState, positionsLiquidityWord, solcSlotWord] using
              positionsStorageLocLoad_liquidity (initState cA gh bl σ σ₀ g A I) I
        have hfee0 :
            evalExpr? (config v) { contract := contract v, locals := positionsStore I }
              (initState cA gh bl σ σ₀ g A I)
              (.storage (positionsF (.var "arg0") "feeGrowthInside0LastX128")) =
            .ok (.int (Int.ofNat (positionsFeeGrowthInside0Word σ I).toNat)) := by
          apply evalExpr_storage_scalar_value
              (er := positionsEvaledRef I "feeGrowthInside0LastX128")
              (t := .int uint256Int)
              (loc := loc (positionsBaseSlot I + ⟨1⟩) ⟨0, by decide⟩
                ⟨32, by decide⟩ (by decide) (.int uint256Int))
          · simp [positionsStore, positionsF]
          · exact evalStorageRef_positions (v := v) (initState cA gh bl σ σ₀ g A I) I
              "feeGrowthInside0LastX128"
          · simp [positionsEvaledRef, contract, storageDecls, storageTypeAt?,
              storageTypeStep?, positionInfoStructTy, uint256St]
          · funext evm
            simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
              positionsEvaledRef, positionsBaseSlot, loc]
          · simpa [initState, positionsFeeGrowthInside0Word, solcSlotWord] using
              positionsStorageLocLoad_feeGrowthInside0 (initState cA gh bl σ σ₀ g A I) I
        have hfee1 :
            evalExpr? (config v) { contract := contract v, locals := positionsStore I }
              (initState cA gh bl σ σ₀ g A I)
              (.storage (positionsF (.var "arg0") "feeGrowthInside1LastX128")) =
            .ok (.int (Int.ofNat (positionsFeeGrowthInside1Word σ I).toNat)) := by
          apply evalExpr_storage_scalar_value
              (er := positionsEvaledRef I "feeGrowthInside1LastX128")
              (t := .int uint256Int)
              (loc := loc (positionsBaseSlot I + ⟨2⟩) ⟨0, by decide⟩
                ⟨32, by decide⟩ (by decide) (.int uint256Int))
          · simp [positionsStore, positionsF]
          · exact evalStorageRef_positions (v := v) (initState cA gh bl σ σ₀ g A I) I
              "feeGrowthInside1LastX128"
          · simp [positionsEvaledRef, contract, storageDecls, storageTypeAt?,
              storageTypeStep?, positionInfoStructTy, uint256St]
          · funext evm
            simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
              positionsEvaledRef, positionsBaseSlot, loc]
          · simpa [initState, positionsFeeGrowthInside1Word, solcSlotWord] using
              positionsStorageLocLoad_feeGrowthInside1 (initState cA gh bl σ σ₀ g A I) I
        have htok0 :
            evalExpr? (config v) { contract := contract v, locals := positionsStore I }
              (initState cA gh bl σ σ₀ g A I)
              (.storage (positionsF (.var "arg0") "tokensOwed0")) =
            .ok (.int (Int.ofNat (positionsTokensOwed0Word σ I).toNat)) := by
          apply evalExpr_storage_scalar_value
              (er := positionsEvaledRef I "tokensOwed0")
              (t := .int uint128Int)
              (loc := loc (positionsPackedSlot I) ⟨0, by decide⟩ ⟨16, by decide⟩
                (by decide) (.int uint128Int))
          · simp [positionsStore, positionsF]
          · exact evalStorageRef_positions (v := v) (initState cA gh bl σ σ₀ g A I) I
              "tokensOwed0"
          · simp [positionsEvaledRef, contract, storageDecls, storageTypeAt?,
              storageTypeStep?, positionInfoStructTy, uint128St]
          · funext evm
            simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
              positionsEvaledRef, positionsBaseSlot, positionsPackedSlot, loc]
          · simpa [initState, positionsTokensOwed0Word, positionsPackedWord, solcSlotWord] using
              positionsStorageLocLoad_tokensOwed0 (initState cA gh bl σ σ₀ g A I) I
        have htok1 :
            evalExpr? (config v) { contract := contract v, locals := positionsStore I }
              (initState cA gh bl σ σ₀ g A I)
              (.storage (positionsF (.var "arg0") "tokensOwed1")) =
            .ok (.int (Int.ofNat (positionsTokensOwed1Word σ I).toNat)) := by
          apply evalExpr_storage_scalar_value
              (er := positionsEvaledRef I "tokensOwed1")
              (t := .int uint128Int)
              (loc := loc (positionsPackedSlot I) ⟨16, by decide⟩ ⟨16, by decide⟩
                (by decide) (.int uint128Int))
          · simp [positionsStore, positionsF]
          · exact evalStorageRef_positions (v := v) (initState cA gh bl σ σ₀ g A I) I
              "tokensOwed1"
          · simp [positionsEvaledRef, contract, storageDecls, storageTypeAt?,
              storageTypeStep?, positionInfoStructTy, uint128St]
          · funext evm
            simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
              positionsEvaledRef, positionsBaseSlot, positionsPackedSlot, loc]
          · simpa [initState, positionsTokensOwed1Word, positionsPackedWord, solcSlotWord] using
              positionsStorageLocLoad_tokensOwed1 (initState cA gh bl σ σ₀ g A I) I
        simp only [positionsReturnValues, Solm.evalExprs?.eq_def, hliq, hfee0, hfee1, htok0,
          htok1, EvalResult.bind, bind, pure])

theorem uniswapV3PoolPositionsValueTransport {σ_evm σ_solm : AccountMap}
    {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    some (positionsReturnValues σ_solm I) = some (positionsReturnValues σ_evm I) := by
  have hbase := accountMapEquiv_storage_findD hAccounts I.codeOwner
    (positionsBaseSlot I) (⟨0⟩ : UInt256)
  have hfee0 := accountMapEquiv_storage_findD hAccounts I.codeOwner
    (positionsBaseSlot I + ⟨1⟩) (⟨0⟩ : UInt256)
  have hfee1 := accountMapEquiv_storage_findD hAccounts I.codeOwner
    (positionsBaseSlot I + ⟨2⟩) (⟨0⟩ : UInt256)
  have hpacked := accountMapEquiv_storage_findD hAccounts I.codeOwner
    (positionsPackedSlot I) (⟨0⟩ : UInt256)
  dsimp [positionsReturnValues, positionsLiquidityWord, positionsFeeGrowthInside0Word,
    positionsFeeGrowthInside1Word, positionsTokensOwed0Word, positionsTokensOwed1Word,
    positionsPackedWord, solcSlotWord]
  rw [← hbase, ← hfee0, ← hfee1, ← hpacked]

theorem uniswapV3PoolPositionsBodyCore {v : PoolImmutables}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsel : (uniswapV3PoolSelBytes 11 == I.calldata.extract 0 4) = true) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdispatch := uniswapV3PoolDispatch_positions (v := v) (cd := I.calldata) hsel
  have hvalue := uniswapV3PoolPositionsValueTransport (σ_evm := σ_evm)
    (σ_solm := σ_solm) (I := I) hAccounts
  sorry

end Benchmarks.UniswapV3Pool
