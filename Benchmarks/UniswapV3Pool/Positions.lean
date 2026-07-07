import Benchmarks.UniswapV3Pool.Uint128
import Reasoning.MemCascade

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

theorem uniswapV3PoolPositionsRoutine {v : PoolImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {ret : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨8093⟩ (positionsArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (positionsTokensOwed1Word σ ee :: positionsTokensOwed0Word σ ee ::
        positionsFeeGrowthInside1Word σ ee :: positionsFeeGrowthInside0Word σ ee ::
        positionsLiquidityWord σ ee :: ret :: R)
      (solcMappingHashMem ⟨7⟩ (positionsArgWord ee)) (UInt256.ofNat 3) rdata (cA, σ)
      k' C' := by
  have hd8093 : decode code ⟨8093⟩ = some (.JUMPDEST, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8093⟩) (byte := 0x5b)
      (op := .JUMPDEST) hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8094 : decode code ⟨8094⟩ = some (.Push .PUSH1, some (⟨7⟩, 1)) := by
    exact uniswapV3PoolPositionsDecodePatchedPush1 (pc := ⟨8094⟩) (n := ⟨7⟩)
      hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint2 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8096 : decode code ⟨8096⟩ = some (.Push .PUSH1, some (⟨32⟩, 1)) := by
    exact uniswapV3PoolPositionsDecodePatchedPush1 (pc := ⟨8096⟩) (n := ⟨32⟩)
      hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint2 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8098 : decode code ⟨8098⟩ = some (.MSTORE, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8098⟩) (byte := 0x52)
      (op := .MSTORE) hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8099 : decode code ⟨8099⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    exact uniswapV3PoolPositionsDecodePatchedPush1 (pc := ⟨8099⟩) (n := ⟨0⟩)
      hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint2 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8101 : decode code ⟨8101⟩ = some (.SWAP1, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8101⟩) (byte := 0x90)
      (op := .SWAP1) hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8102 : decode code ⟨8102⟩ = some (.DUP2, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8102⟩) (byte := 0x81)
      (op := .DUP2) hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8103 : decode code ⟨8103⟩ = some (.MSTORE, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8103⟩) (byte := 0x52)
      (op := .MSTORE) hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8104 : decode code ⟨8104⟩ = some (.Push .PUSH1, some (⟨64⟩, 1)) := by
    exact uniswapV3PoolPositionsDecodePatchedPush1 (pc := ⟨8104⟩) (n := ⟨64⟩)
      hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint2 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8106 : decode code ⟨8106⟩ = some (.SWAP1, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8106⟩) (byte := 0x90)
      (op := .SWAP1) hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8107 : decode code ⟨8107⟩ = some (.KECCAK256, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8107⟩) (byte := 0x20)
      (op := .KECCAK256) hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8108 : decode code ⟨8108⟩ = some (.DUP1, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8108⟩) (byte := 0x80)
      (op := .DUP1) hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8109 : decode code ⟨8109⟩ = some (.SLOAD, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8109⟩) (byte := 0x54)
      (op := .SLOAD) hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8110 : decode code ⟨8110⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    exact uniswapV3PoolPositionsDecodePatchedPush1 (pc := ⟨8110⟩) (n := ⟨1⟩)
      hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint2 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8112 : decode code ⟨8112⟩ = some (.DUP3, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8112⟩) (byte := 0x82)
      (op := .DUP3) hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8113 : decode code ⟨8113⟩ = some (.ADD, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8113⟩) (byte := 0x01)
      (op := .ADD) hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8114 : decode code ⟨8114⟩ = some (.SLOAD, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8114⟩) (byte := 0x54)
      (op := .SLOAD) hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8115 : decode code ⟨8115⟩ = some (.Push .PUSH1, some (⟨2⟩, 1)) := by
    exact uniswapV3PoolPositionsDecodePatchedPush1 (pc := ⟨8115⟩) (n := ⟨2⟩)
      hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint2 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8117 : decode code ⟨8117⟩ = some (.DUP4, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8117⟩) (byte := 0x83)
      (op := .DUP4) hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8118 : decode code ⟨8118⟩ = some (.ADD, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8118⟩) (byte := 0x01)
      (op := .ADD) hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8119 : decode code ⟨8119⟩ = some (.SLOAD, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8119⟩) (byte := 0x54)
      (op := .SLOAD) hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8120 : decode code ⟨8120⟩ = some (.Push .PUSH1, some (⟨3⟩, 1)) := by
    exact uniswapV3PoolPositionsDecodePatchedPush1 (pc := ⟨8120⟩) (n := ⟨3⟩)
      hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint2 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8122 : decode code ⟨8122⟩ = some (.SWAP1, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8122⟩) (byte := 0x90)
      (op := .SWAP1) hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8123 : decode code ⟨8123⟩ = some (.SWAP4, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8123⟩) (byte := 0x93)
      (op := .SWAP4) hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8124 : decode code ⟨8124⟩ = some (.ADD, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8124⟩) (byte := 0x01)
      (op := .ADD) hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8125 : decode code ⟨8125⟩ = some (.SLOAD, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8125⟩) (byte := 0x54)
      (op := .SLOAD) hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8126 : decode code ⟨8126⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    exact uniswapV3PoolPositionsDecodePatchedPush1 (pc := ⟨8126⟩) (n := ⟨1⟩)
      hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint2 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8128 : decode code ⟨8128⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    exact uniswapV3PoolPositionsDecodePatchedPush1 (pc := ⟨8128⟩) (n := ⟨1⟩)
      hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint2 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8130 : decode code ⟨8130⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    exact uniswapV3PoolPositionsDecodePatchedPush1 (pc := ⟨8130⟩) (n := ⟨128⟩)
      hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint2 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8132 : decode code ⟨8132⟩ = some (.SHL, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8132⟩) (byte := 0x1b)
      (op := .SHL) hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8133 : decode code ⟨8133⟩ = some (.SUB, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8133⟩) (byte := 0x03)
      (op := .SUB) hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8134 : decode code ⟨8134⟩ = some (.SWAP3, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8134⟩) (byte := 0x92)
      (op := .SWAP3) hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8135 : decode code ⟨8135⟩ = some (.DUP4, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8135⟩) (byte := 0x83)
      (op := .DUP4) hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8136 : decode code ⟨8136⟩ = some (.AND, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8136⟩) (byte := 0x16)
      (op := .AND) hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8137 : decode code ⟨8137⟩ = some (.SWAP4, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8137⟩) (byte := 0x93)
      (op := .SWAP4) hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8138 : decode code ⟨8138⟩ = some (.SWAP2, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8138⟩) (byte := 0x91)
      (op := .SWAP2) hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8139 : decode code ⟨8139⟩ = some (.SWAP3, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8139⟩) (byte := 0x92)
      (op := .SWAP3) hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8140 : decode code ⟨8140⟩ = some (.DUP2, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8140⟩) (byte := 0x81)
      (op := .DUP2) hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8141 : decode code ⟨8141⟩ = some (.DUP2, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8141⟩) (byte := 0x81)
      (op := .DUP2) hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8142 : decode code ⟨8142⟩ = some (.AND, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8142⟩) (byte := 0x16)
      (op := .AND) hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8143 : decode code ⟨8143⟩ = some (.SWAP2, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8143⟩) (byte := 0x91)
      (op := .SWAP2) hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8144 : decode code ⟨8144⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    exact uniswapV3PoolPositionsDecodePatchedPush1 (pc := ⟨8144⟩) (n := ⟨1⟩)
      hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint2 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8146 : decode code ⟨8146⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    exact uniswapV3PoolPositionsDecodePatchedPush1 (pc := ⟨8146⟩) (n := ⟨128⟩)
      hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint2 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8148 : decode code ⟨8148⟩ = some (.SHL, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8148⟩) (byte := 0x1b)
      (op := .SHL) hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8149 : decode code ⟨8149⟩ = some (.SWAP1, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8149⟩) (byte := 0x90)
      (op := .SWAP1) hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8150 : decode code ⟨8150⟩ = some (.DIV, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8150⟩) (byte := 0x04)
      (op := .DIV) hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8151 : decode code ⟨8151⟩ = some (.AND, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8151⟩) (byte := 0x16)
      (op := .AND) hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8152 : decode code ⟨8152⟩ = some (.DUP6, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8152⟩) (byte := 0x85)
      (op := .DUP6) hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8153 : decode code ⟨8153⟩ = some (.JUMP, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8153⟩) (byte := 0x56)
      (op := .JUMP) hpatch (by native_decide)
      (uniswapV3PoolPositionsRoutinePatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have rd8094 := h.jumpdest hd8093 (by simp only [List.length_cons]; omega)
  have rd8096 := rd8094.push1 ⟨7⟩ hd8094 (by evm_ov)
  have rd8098 := rd8096.push1 ⟨32⟩ hd8096 (by evm_ov)
  have rd8099 := rd8098.mstore 0 (solcMappingBaseSlotMem ⟨7⟩)
    (UInt256.ofNat 3) hd8098 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd8101 := rd8099.push1 ⟨0⟩ hd8099 (by evm_ov)
  have rd8102 := rd8101.swap1 hd8101 (by evm_ov)
  have rd8103 := rd8102.dup2 hd8102 (by evm_ov)
  have rd8104 := rd8103.mstore 0 (solcMappingHashMem ⟨7⟩ (positionsArgWord ee))
    (UInt256.ofNat 3) hd8103 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd8106 := rd8104.push1 ⟨64⟩ hd8104 (by evm_ov)
  have rd8107 := rd8106.swap1 hd8106 (by evm_ov)
  have hslot := solcMappingKeccakSlot ⟨7⟩ (positionsArgWord ee)
  have rd8108 := rd8107.keccak256 0 (solcMappingSlot ⟨7⟩ (positionsArgWord ee))
    (UInt256.ofNat 3) hd8107 mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hslot)
    (by native_decide) (by evm_ov)
  have rd8109 := rd8108.dup1 hd8108 (by evm_ov)
  obtain ⟨_, _, rd8110⟩ := rd8109.sload hd8109 (by evm_ov)
  have rd8114 := evm_run rd8110 with [
    raw push1 ⟨1⟩ hd8110 (by evm_ov),
    raw dup3 hd8112 (by evm_ov),
    raw add hd8113 (by evm_ov)]
  obtain ⟨_, _, rd8115⟩ := rd8114.sload hd8114 (by evm_ov)
  have rd8119 := evm_run rd8115 with [
    raw push1 ⟨2⟩ hd8115 (by evm_ov),
    raw dup4 hd8117 (by evm_ov),
    raw add hd8118 (by evm_ov)]
  obtain ⟨_, _, rd8120⟩ := rd8119.sload hd8119 (by evm_ov)
  have rd8125 := evm_run rd8120 with [
    raw push1 ⟨3⟩ hd8120 (by evm_ov),
    raw swap1 hd8122 (by evm_ov),
    raw swap4 hd8123 (by evm_ov),
    raw add hd8124 (by evm_ov)]
  obtain ⟨_, _, rd8126⟩ := rd8125.sload hd8125 (by evm_ov)
  have rd8153 := evm_run rd8126 with [
    raw push1 ⟨1⟩ hd8126 (by evm_ov),
    raw push1 ⟨1⟩ hd8128 (by evm_ov),
    raw push1 ⟨128⟩ hd8130 (by evm_ov),
    raw shl hd8132 (by evm_ov),
    raw sub hd8133 (by evm_ov),
    raw swap3 hd8134 (by evm_ov),
    raw dup4 hd8135 (by evm_ov),
    raw and hd8136 (by evm_ov),
    raw swap4 hd8137 (by evm_ov),
    raw swap2 hd8138 (by evm_ov),
    raw swap3 hd8139 (by evm_ov),
    raw dup2 hd8140 (by evm_ov),
    raw dup2 hd8141 (by evm_ov),
    raw and hd8142 (by evm_ov),
    raw swap2 hd8143 (by evm_ov),
    raw push1 ⟨1⟩ hd8144 (by evm_ov),
    raw push1 ⟨128⟩ hd8146 (by evm_ov),
    raw shl hd8148 (by evm_ov),
    raw swap1 hd8149 (by evm_ov),
    raw div hd8150 (by evm_ov),
    raw and hd8151 (by evm_ov),
    raw dup6 hd8152 (by evm_ov)]
  have rdRet := rd8153.jump hd8153 hret (by evm_ov)
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩) ⟨1⟩ = uint128Mask := by
    native_decide
  have hliqComm :
      UInt256.land uint128Mask
          (σ.find? ee.codeOwner |>.option ⟨0⟩
            (fun ac =>
              ac.storage.findD (solcMappingSlot ⟨7⟩ (positionsArgWord ee)) ⟨0⟩)) =
        UInt256.land
          (σ.find? ee.codeOwner |>.option ⟨0⟩
            (fun ac =>
              ac.storage.findD (solcMappingSlot ⟨7⟩ (positionsArgWord ee)) ⟨0⟩))
          uint128Mask := by
    rw [u256_land_comm]
  have htow0Comm :
      UInt256.land uint128Mask
          (σ.find? ee.codeOwner |>.option ⟨0⟩
            (fun ac =>
              ac.storage.findD (solcMappingSlot ⟨7⟩ (positionsArgWord ee) + ⟨3⟩) ⟨0⟩)) =
        UInt256.land
          (σ.find? ee.codeOwner |>.option ⟨0⟩
            (fun ac =>
              ac.storage.findD (solcMappingSlot ⟨7⟩ (positionsArgWord ee) + ⟨3⟩) ⟨0⟩))
          uint128Mask := by
    rw [u256_land_comm]
  exact ⟨_, _, by
    rw [hmask] at rdRet
    simpa [positionsTokensOwed1Word, positionsTokensOwed0Word,
      positionsFeeGrowthInside1Word, positionsFeeGrowthInside0Word, positionsLiquidityWord,
      positionsPackedWord, positionsPackedSlot, positionsBaseSlot_eq_solcMappingSlot ee,
      positionsShift, solcSlotWord, hliqComm, htow0Comm] using rdRet⟩

private theorem uniswapV3PoolPositionsDecodedToLoaded {v : PoolImmutables}
    {code : ByteArray} {cA gh bl σ σ₀ A I} {g : Sat256} {de : UInt256} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (rdDecoded : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨1379⟩
      (de :: ⟨4⟩ :: ⟨1386⟩ :: [solcSelectorWord I])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g (initState cA gh bl σ σ₀ g A I) ⟨1386⟩
      (positionsTokensOwed1Word σ I :: positionsTokensOwed0Word σ I ::
        positionsFeeGrowthInside1Word σ I :: positionsFeeGrowthInside0Word σ I ::
        positionsLiquidityWord σ I :: ⟨1386⟩ :: [solcSelectorWord I])
      (solcMappingHashMem ⟨7⟩ (positionsArgWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rdRoutine⟩ :=
    uniswapV3PoolPositionsDecodedReachRoutine hpatch rdDecoded
      (by simp only [List.length_singleton]; omega)
  exact uniswapV3PoolPositionsRoutine hpatch rdRoutine
    (uniswapV3PoolJumpDestPatched2258 hpatch (by native_decide))
    (by simp only [List.length_singleton]; omega)

noncomputable def positionsReturnMem1 (liq : UInt256) : ByteArray :=
  writeCascade solcFreePtrMem [(128, liq)]

noncomputable def positionsReturnMem2 (liq fee0 : UInt256) : ByteArray :=
  writeCascade solcFreePtrMem [(128, liq), (160, fee0)]

noncomputable def positionsReturnMem3 (liq fee0 fee1 : UInt256) : ByteArray :=
  writeCascade solcFreePtrMem [(128, liq), (160, fee0), (192, fee1)]

noncomputable def positionsReturnMem4 (liq fee0 fee1 owed0 : UInt256) : ByteArray :=
  writeCascade solcFreePtrMem [(128, liq), (160, fee0), (192, fee1), (224, owed0)]

noncomputable def positionsReturnMem
    (liq fee0 fee1 owed0 owed1 : UInt256) : ByteArray :=
  writeCascade solcFreePtrMem
    [(128, liq), (160, fee0), (192, fee1), (224, owed0), (256, owed1)]

theorem positionsReturnMem1_eq (liq : UInt256) :
    positionsReturnMem1 liq = writeWord solcFreePtrMem 128 liq := by
  rfl

theorem positionsReturnMem2_eq (liq fee0 : UInt256) :
    positionsReturnMem2 liq fee0 = writeWord (positionsReturnMem1 liq) 160 fee0 := by
  rfl

theorem positionsReturnMem3_eq (liq fee0 fee1 : UInt256) :
    positionsReturnMem3 liq fee0 fee1 =
      writeWord (positionsReturnMem2 liq fee0) 192 fee1 := by
  rfl

theorem positionsReturnMem4_eq (liq fee0 fee1 owed0 : UInt256) :
    positionsReturnMem4 liq fee0 fee1 owed0 =
      writeWord (positionsReturnMem3 liq fee0 fee1) 224 owed0 := by
  rfl

theorem positionsReturnMem_eq (liq fee0 fee1 owed0 owed1 : UInt256) :
    positionsReturnMem liq fee0 fee1 owed0 owed1 =
      writeWord (positionsReturnMem4 liq fee0 fee1 owed0) 256 owed1 := by
  rfl

theorem positionsReturnMem1_size (liq : UInt256) :
    (positionsReturnMem1 liq).size = 160 := by
  unfold positionsReturnMem1
  exact writeCascade_size_of_base solcFreePtrMem _ solcFreePtrMem_size
    (by
      norm_num [WriteGapsOk]
      all_goals native_decide)
    (by norm_num [writeCascadeSize])

theorem positionsReturnMem2_size (liq fee0 : UInt256) :
    (positionsReturnMem2 liq fee0).size = 192 := by
  unfold positionsReturnMem2
  exact writeCascade_size_of_base solcFreePtrMem _ solcFreePtrMem_size
    (by
      norm_num [WriteGapsOk]
      all_goals native_decide)
    (by norm_num [writeCascadeSize])

theorem positionsReturnMem3_size (liq fee0 fee1 : UInt256) :
    (positionsReturnMem3 liq fee0 fee1).size = 224 := by
  unfold positionsReturnMem3
  exact writeCascade_size_of_base solcFreePtrMem _ solcFreePtrMem_size
    (by
      norm_num [WriteGapsOk]
      all_goals native_decide)
    (by norm_num [writeCascadeSize])

theorem positionsReturnMem4_size (liq fee0 fee1 owed0 : UInt256) :
    (positionsReturnMem4 liq fee0 fee1 owed0).size = 256 := by
  unfold positionsReturnMem4
  exact writeCascade_size_of_base solcFreePtrMem _ solcFreePtrMem_size
    (by
      norm_num [WriteGapsOk]
      all_goals native_decide)
    (by norm_num [writeCascadeSize])

theorem positionsReturnMem_size (liq fee0 fee1 owed0 owed1 : UInt256) :
    (positionsReturnMem liq fee0 fee1 owed0 owed1).size = 288 := by
  unfold positionsReturnMem
  exact writeCascade_size_of_base solcFreePtrMem _ solcFreePtrMem_size
    (by
      norm_num [WriteGapsOk]
      all_goals native_decide)
    (by norm_num [writeCascadeSize])

theorem positionsReturnMem_read64 (liq fee0 fee1 owed0 owed1 : UInt256) :
    (positionsReturnMem liq fee0 fee1 owed0 owed1).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold positionsReturnMem
  rw [writeCascade_read_preserved_of_base solcFreePtrMem _ solcFreePtrMem_size
    (by
      norm_num [WindowDisjointFromWrites]
      all_goals native_decide)]
  exact solcFreePtrMem_read64

theorem positionsReturnMem_mload64 (liq fee0 fee1 owed0 owed1 : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (positionsReturnMem liq fee0 fee1 owed0 owed1).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((positionsReturnMem liq fee0 fee1 owed0 owed1).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
  mloadFreePtrValue (by rw [positionsReturnMem_size]; decide) (by decide)
    (positionsReturnMem_read64 liq fee0 fee1 owed0 owed1)

theorem positionsReturnMem_read128 (liq fee0 fee1 owed0 owed1 : UInt256) :
    (positionsReturnMem liq fee0 fee1 owed0 owed1).readWithPadding 128 32 =
      UInt256.toByteArray liq := by
  unfold positionsReturnMem
  exact writeCascade_read_word_of_head_of_base solcFreePtrMem (base := 96) (off := 128)
    liq [(160, fee0), (192, fee1), (224, owed0), (256, owed1)]
      solcFreePtrMem_size (by native_decide)
      (by
        norm_num [WindowDisjointFromWrites])

theorem positionsReturnMem_read160 (liq fee0 fee1 owed0 owed1 : UInt256) :
    (positionsReturnMem liq fee0 fee1 owed0 owed1).readWithPadding 160 32 =
      UInt256.toByteArray fee0 := by
  unfold positionsReturnMem
  change (writeCascade (positionsReturnMem1 liq)
      [(160, fee0), (192, fee1), (224, owed0), (256, owed1)]).readWithPadding 160 32 =
    UInt256.toByteArray fee0
  exact writeCascade_read_word_of_head_of_base (positionsReturnMem1 liq) (base := 160)
    (off := 160) fee0 [(192, fee1), (224, owed0), (256, owed1)]
      (positionsReturnMem1_size liq) (by native_decide)
      (by
        norm_num [WindowDisjointFromWrites])

theorem positionsReturnMem_read192 (liq fee0 fee1 owed0 owed1 : UInt256) :
    (positionsReturnMem liq fee0 fee1 owed0 owed1).readWithPadding 192 32 =
      UInt256.toByteArray fee1 := by
  unfold positionsReturnMem
  change (writeCascade (positionsReturnMem2 liq fee0)
      [(192, fee1), (224, owed0), (256, owed1)]).readWithPadding 192 32 =
    UInt256.toByteArray fee1
  exact writeCascade_read_word_of_head_of_base (positionsReturnMem2 liq fee0) (base := 192)
    (off := 192) fee1 [(224, owed0), (256, owed1)]
      (positionsReturnMem2_size liq fee0) (by native_decide)
      (by
        norm_num [WindowDisjointFromWrites])

theorem positionsReturnMem_read224 (liq fee0 fee1 owed0 owed1 : UInt256) :
    (positionsReturnMem liq fee0 fee1 owed0 owed1).readWithPadding 224 32 =
      UInt256.toByteArray owed0 := by
  unfold positionsReturnMem
  change (writeCascade (positionsReturnMem3 liq fee0 fee1)
      [(224, owed0), (256, owed1)]).readWithPadding 224 32 =
    UInt256.toByteArray owed0
  exact writeCascade_read_word_of_head_of_base (positionsReturnMem3 liq fee0 fee1)
    (base := 224) (off := 224) owed0 [(256, owed1)]
      (positionsReturnMem3_size liq fee0 fee1) (by native_decide)
      (by
        norm_num [WindowDisjointFromWrites])

theorem positionsReturnMem_read256 (liq fee0 fee1 owed0 owed1 : UInt256) :
    (positionsReturnMem liq fee0 fee1 owed0 owed1).readWithPadding 256 32 =
      UInt256.toByteArray owed1 := by
  unfold positionsReturnMem
  change (writeCascade (positionsReturnMem4 liq fee0 fee1 owed0)
      [(256, owed1)]).readWithPadding 256 32 =
    UInt256.toByteArray owed1
  exact writeCascade_read_word_of_head_of_base (positionsReturnMem4 liq fee0 fee1 owed0)
    (base := 256) (off := 256) owed1 []
      (positionsReturnMem4_size liq fee0 fee1 owed0) (by native_decide)
      (by
        norm_num [WindowDisjointFromWrites])

theorem positionsReturnMem_read128_160 (liq fee0 fee1 owed0 owed1 : UInt256) :
    (positionsReturnMem liq fee0 fee1 owed0 owed1).readWithPadding 128 160 =
      UInt256.toByteArray liq ++ UInt256.toByteArray fee0 ++ UInt256.toByteArray fee1 ++
        UInt256.toByteArray owed0 ++ UInt256.toByteArray owed1 := by
  let mem := positionsReturnMem liq fee0 fee1 owed0 owed1
  have hsize : mem.size = 288 := by
    simpa [mem] using positionsReturnMem_size liq fee0 fee1 owed0 owed1
  have h128 : mem.readWithPadding 128 32 = UInt256.toByteArray liq := by
    simpa [mem] using positionsReturnMem_read128 liq fee0 fee1 owed0 owed1
  have h160 : mem.readWithPadding 160 32 = UInt256.toByteArray fee0 := by
    simpa [mem] using positionsReturnMem_read160 liq fee0 fee1 owed0 owed1
  have h192 : mem.readWithPadding 192 32 = UInt256.toByteArray fee1 := by
    simpa [mem] using positionsReturnMem_read192 liq fee0 fee1 owed0 owed1
  have h224 : mem.readWithPadding 224 32 = UInt256.toByteArray owed0 := by
    simpa [mem] using positionsReturnMem_read224 liq fee0 fee1 owed0 owed1
  have h256 : mem.readWithPadding 256 32 = UInt256.toByteArray owed1 := by
    simpa [mem] using positionsReturnMem_read256 liq fee0 fee1 owed0 owed1
  change mem.readWithPadding 128 160 = _
  rw [byteArray_readWithPadding_split mem 128 32 128 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by omega), h128]
  rw [byteArray_readWithPadding_split mem 160 32 96 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by omega), h160]
  rw [byteArray_readWithPadding_split mem 192 32 64 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by omega), h192]
  rw [byteArray_readWithPadding_split mem 224 32 32 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by omega), h224, h256]
  simp only [ByteArray.append_assoc]

noncomputable def positionsScratchReturnMem1 (scratch : ByteArray) (liq : UInt256) :
    ByteArray :=
  writeCascade scratch [(128, liq)]

noncomputable def positionsScratchReturnMem2 (scratch : ByteArray) (liq fee0 : UInt256) :
    ByteArray :=
  writeCascade scratch [(128, liq), (160, fee0)]

noncomputable def positionsScratchReturnMem3
    (scratch : ByteArray) (liq fee0 fee1 : UInt256) : ByteArray :=
  writeCascade scratch [(128, liq), (160, fee0), (192, fee1)]

noncomputable def positionsScratchReturnMem4
    (scratch : ByteArray) (liq fee0 fee1 owed0 : UInt256) : ByteArray :=
  writeCascade scratch [(128, liq), (160, fee0), (192, fee1), (224, owed0)]

noncomputable def positionsScratchReturnMem
    (scratch : ByteArray) (liq fee0 fee1 owed0 owed1 : UInt256) : ByteArray :=
  writeCascade scratch
    [(128, liq), (160, fee0), (192, fee1), (224, owed0), (256, owed1)]

theorem positionsScratchReturnMem1_eq (scratch : ByteArray) (liq : UInt256) :
    positionsScratchReturnMem1 scratch liq = writeWord scratch 128 liq := by
  rfl

theorem positionsScratchReturnMem2_eq (scratch : ByteArray) (liq fee0 : UInt256) :
    positionsScratchReturnMem2 scratch liq fee0 =
      writeWord (positionsScratchReturnMem1 scratch liq) 160 fee0 := by
  rfl

theorem positionsScratchReturnMem3_eq
    (scratch : ByteArray) (liq fee0 fee1 : UInt256) :
    positionsScratchReturnMem3 scratch liq fee0 fee1 =
      writeWord (positionsScratchReturnMem2 scratch liq fee0) 192 fee1 := by
  rfl

theorem positionsScratchReturnMem4_eq
    (scratch : ByteArray) (liq fee0 fee1 owed0 : UInt256) :
    positionsScratchReturnMem4 scratch liq fee0 fee1 owed0 =
      writeWord (positionsScratchReturnMem3 scratch liq fee0 fee1) 224 owed0 := by
  rfl

theorem positionsScratchReturnMem_eq
    (scratch : ByteArray) (liq fee0 fee1 owed0 owed1 : UInt256) :
    positionsScratchReturnMem scratch liq fee0 fee1 owed0 owed1 =
      writeWord (positionsScratchReturnMem4 scratch liq fee0 fee1 owed0) 256 owed1 := by
  rfl

theorem positionsScratchReturnMem1_size {scratch : ByteArray} (liq : UInt256)
    (hscratch : scratch.size = 96) :
    (positionsScratchReturnMem1 scratch liq).size = 160 := by
  unfold positionsScratchReturnMem1
  exact writeCascade_size_of_base scratch _ hscratch
    (by
      norm_num [WriteGapsOk]
      all_goals native_decide)
    (by norm_num [writeCascadeSize])

theorem positionsScratchReturnMem2_size {scratch : ByteArray} (liq fee0 : UInt256)
    (hscratch : scratch.size = 96) :
    (positionsScratchReturnMem2 scratch liq fee0).size = 192 := by
  unfold positionsScratchReturnMem2
  exact writeCascade_size_of_base scratch _ hscratch
    (by
      norm_num [WriteGapsOk]
      all_goals native_decide)
    (by norm_num [writeCascadeSize])

theorem positionsScratchReturnMem3_size {scratch : ByteArray} (liq fee0 fee1 : UInt256)
    (hscratch : scratch.size = 96) :
    (positionsScratchReturnMem3 scratch liq fee0 fee1).size = 224 := by
  unfold positionsScratchReturnMem3
  exact writeCascade_size_of_base scratch _ hscratch
    (by
      norm_num [WriteGapsOk]
      all_goals native_decide)
    (by norm_num [writeCascadeSize])

theorem positionsScratchReturnMem4_size {scratch : ByteArray} (liq fee0 fee1 owed0 : UInt256)
    (hscratch : scratch.size = 96) :
    (positionsScratchReturnMem4 scratch liq fee0 fee1 owed0).size = 256 := by
  unfold positionsScratchReturnMem4
  exact writeCascade_size_of_base scratch _ hscratch
    (by
      norm_num [WriteGapsOk]
      all_goals native_decide)
    (by norm_num [writeCascadeSize])

theorem positionsScratchReturnMem_size {scratch : ByteArray}
    (liq fee0 fee1 owed0 owed1 : UInt256) (hscratch : scratch.size = 96) :
    (positionsScratchReturnMem scratch liq fee0 fee1 owed0 owed1).size = 288 := by
  unfold positionsScratchReturnMem
  exact writeCascade_size_of_base scratch _ hscratch
    (by
      norm_num [WriteGapsOk]
      all_goals native_decide)
    (by norm_num [writeCascadeSize])

theorem positionsScratchReturnMem_read64 {scratch : ByteArray}
    (liq fee0 fee1 owed0 owed1 : UInt256) (hscratch : scratch.size = 96)
    (hread64 : scratch.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (positionsScratchReturnMem scratch liq fee0 fee1 owed0 owed1).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold positionsScratchReturnMem
  rw [writeCascade_read_preserved_of_base scratch _ hscratch
    (by
      norm_num [WindowDisjointFromWrites]
      all_goals native_decide)]
  exact hread64

theorem positionsScratchReturnMem_mload64 {scratch : ByteArray}
    (liq fee0 fee1 owed0 owed1 : UInt256) (hscratch : scratch.size = 96)
    (hread64 : scratch.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (positionsScratchReturnMem scratch liq fee0 fee1 owed0 owed1).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((positionsScratchReturnMem scratch liq fee0 fee1 owed0 owed1).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
  mloadFreePtrValue (by rw [positionsScratchReturnMem_size liq fee0 fee1 owed0 owed1 hscratch]; decide)
    (by decide)
    (positionsScratchReturnMem_read64 liq fee0 fee1 owed0 owed1 hscratch hread64)

theorem positionsScratchReturnMem_read128 {scratch : ByteArray}
    (liq fee0 fee1 owed0 owed1 : UInt256) (hscratch : scratch.size = 96) :
    (positionsScratchReturnMem scratch liq fee0 fee1 owed0 owed1).readWithPadding 128 32 =
      UInt256.toByteArray liq := by
  unfold positionsScratchReturnMem
  exact writeCascade_read_word_of_head_of_base scratch (base := 96) (off := 128)
    liq [(160, fee0), (192, fee1), (224, owed0), (256, owed1)]
      hscratch (by native_decide)
      (by
        norm_num [WindowDisjointFromWrites])

theorem positionsScratchReturnMem_read160 {scratch : ByteArray}
    (liq fee0 fee1 owed0 owed1 : UInt256) (hscratch : scratch.size = 96) :
    (positionsScratchReturnMem scratch liq fee0 fee1 owed0 owed1).readWithPadding 160 32 =
      UInt256.toByteArray fee0 := by
  unfold positionsScratchReturnMem
  change (writeCascade (positionsScratchReturnMem1 scratch liq)
      [(160, fee0), (192, fee1), (224, owed0), (256, owed1)]).readWithPadding 160 32 =
    UInt256.toByteArray fee0
  exact writeCascade_read_word_of_head_of_base (positionsScratchReturnMem1 scratch liq)
    (base := 160) (off := 160) fee0 [(192, fee1), (224, owed0), (256, owed1)]
      (positionsScratchReturnMem1_size liq hscratch) (by native_decide)
      (by
        norm_num [WindowDisjointFromWrites])

theorem positionsScratchReturnMem_read192 {scratch : ByteArray}
    (liq fee0 fee1 owed0 owed1 : UInt256) (hscratch : scratch.size = 96) :
    (positionsScratchReturnMem scratch liq fee0 fee1 owed0 owed1).readWithPadding 192 32 =
      UInt256.toByteArray fee1 := by
  unfold positionsScratchReturnMem
  change (writeCascade (positionsScratchReturnMem2 scratch liq fee0)
      [(192, fee1), (224, owed0), (256, owed1)]).readWithPadding 192 32 =
    UInt256.toByteArray fee1
  exact writeCascade_read_word_of_head_of_base (positionsScratchReturnMem2 scratch liq fee0)
    (base := 192) (off := 192) fee1 [(224, owed0), (256, owed1)]
      (positionsScratchReturnMem2_size liq fee0 hscratch) (by native_decide)
      (by
        norm_num [WindowDisjointFromWrites])

theorem positionsScratchReturnMem_read224 {scratch : ByteArray}
    (liq fee0 fee1 owed0 owed1 : UInt256) (hscratch : scratch.size = 96) :
    (positionsScratchReturnMem scratch liq fee0 fee1 owed0 owed1).readWithPadding 224 32 =
      UInt256.toByteArray owed0 := by
  unfold positionsScratchReturnMem
  change (writeCascade (positionsScratchReturnMem3 scratch liq fee0 fee1)
      [(224, owed0), (256, owed1)]).readWithPadding 224 32 =
    UInt256.toByteArray owed0
  exact writeCascade_read_word_of_head_of_base
    (positionsScratchReturnMem3 scratch liq fee0 fee1) (base := 224) (off := 224)
      owed0 [(256, owed1)]
      (positionsScratchReturnMem3_size liq fee0 fee1 hscratch) (by native_decide)
      (by
        norm_num [WindowDisjointFromWrites])

theorem positionsScratchReturnMem_read256 {scratch : ByteArray}
    (liq fee0 fee1 owed0 owed1 : UInt256) (hscratch : scratch.size = 96) :
    (positionsScratchReturnMem scratch liq fee0 fee1 owed0 owed1).readWithPadding 256 32 =
      UInt256.toByteArray owed1 := by
  unfold positionsScratchReturnMem
  change (writeCascade (positionsScratchReturnMem4 scratch liq fee0 fee1 owed0)
      [(256, owed1)]).readWithPadding 256 32 =
    UInt256.toByteArray owed1
  exact writeCascade_read_word_of_head_of_base
    (positionsScratchReturnMem4 scratch liq fee0 fee1 owed0) (base := 256) (off := 256)
      owed1 []
      (positionsScratchReturnMem4_size liq fee0 fee1 owed0 hscratch) (by native_decide)
      (by
        norm_num [WindowDisjointFromWrites])

theorem positionsScratchReturnMem_read128_160 {scratch : ByteArray}
    (liq fee0 fee1 owed0 owed1 : UInt256) (hscratch : scratch.size = 96) :
    (positionsScratchReturnMem scratch liq fee0 fee1 owed0 owed1).readWithPadding 128 160 =
      UInt256.toByteArray liq ++ UInt256.toByteArray fee0 ++ UInt256.toByteArray fee1 ++
        UInt256.toByteArray owed0 ++ UInt256.toByteArray owed1 := by
  let mem := positionsScratchReturnMem scratch liq fee0 fee1 owed0 owed1
  have hsize : mem.size = 288 := by
    simpa [mem] using positionsScratchReturnMem_size liq fee0 fee1 owed0 owed1 hscratch
  have h128 : mem.readWithPadding 128 32 = UInt256.toByteArray liq := by
    simpa [mem] using positionsScratchReturnMem_read128 liq fee0 fee1 owed0 owed1 hscratch
  have h160 : mem.readWithPadding 160 32 = UInt256.toByteArray fee0 := by
    simpa [mem] using positionsScratchReturnMem_read160 liq fee0 fee1 owed0 owed1 hscratch
  have h192 : mem.readWithPadding 192 32 = UInt256.toByteArray fee1 := by
    simpa [mem] using positionsScratchReturnMem_read192 liq fee0 fee1 owed0 owed1 hscratch
  have h224 : mem.readWithPadding 224 32 = UInt256.toByteArray owed0 := by
    simpa [mem] using positionsScratchReturnMem_read224 liq fee0 fee1 owed0 owed1 hscratch
  have h256 : mem.readWithPadding 256 32 = UInt256.toByteArray owed1 := by
    simpa [mem] using positionsScratchReturnMem_read256 liq fee0 fee1 owed0 owed1 hscratch
  change mem.readWithPadding 128 160 = _
  rw [byteArray_readWithPadding_split mem 128 32 128 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by omega), h128]
  rw [byteArray_readWithPadding_split mem 160 32 96 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by omega), h160]
  rw [byteArray_readWithPadding_split mem 192 32 64 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by omega), h192]
  rw [byteArray_readWithPadding_split mem 224 32 32 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by omega), h224, h256]
  simp only [ByteArray.append_assoc]

theorem positionsScratch_mload64 {scratch : ByteArray}
    (hscratch : scratch.size = 96)
    (hread64 : scratch.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ scratch.size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian (scratch.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
  mloadFreePtrValue (by rw [hscratch]; decide) (by decide) hread64

theorem positionsReturnEncodingMasked
    (liq fee0 fee1 owed0 owed1 : UInt256) :
    encodeReturnValues? [uint128, uint256, uint256, uint128, uint128]
        [.int (Int.ofNat (UInt256.land liq uint128Mask).toNat),
          .int (Int.ofNat fee0.toNat),
          .int (Int.ofNat fee1.toNat),
          .int (Int.ofNat (UInt256.land owed0 uint128Mask).toNat),
          .int (Int.ofNat (UInt256.land owed1 uint128Mask).toNat)] =
      some (UInt256.toByteArray (UInt256.land liq uint128Mask) ++
        UInt256.toByteArray fee0 ++ UInt256.toByteArray fee1 ++
          UInt256.toByteArray (UInt256.land owed0 uint128Mask) ++
            UInt256.toByteArray (UInt256.land owed1 uint128Mask)) := by
  let liq' := UInt256.land liq uint128Mask
  let owed0' := UInt256.land owed0 uint128Mask
  let owed1' := UInt256.land owed1 uint128Mask
  have hwordLiq : EVM.word liq'.toNat = liq' := by
    show UInt256.ofNat liq'.toNat = liq'
    exact u256_ofNat_toNat liq'
  have hwordFee0 : EVM.word fee0.toNat = fee0 := by
    show UInt256.ofNat fee0.toNat = fee0
    exact u256_ofNat_toNat fee0
  have hwordFee1 : EVM.word fee1.toNat = fee1 := by
    show UInt256.ofNat fee1.toNat = fee1
    exact u256_ofNat_toNat fee1
  have hwordOwed0 : EVM.word owed0'.toNat = owed0' := by
    show UInt256.ofNat owed0'.toNat = owed0'
    exact u256_ofNat_toNat owed0'
  have hwordOwed1 : EVM.word owed1'.toNat = owed1' := by
    show UInt256.ofNat owed1'.toNat = owed1'
    exact u256_ofNat_toNat owed1'
  have hfee0Lt : fee0.toNat < EVM.twoPow 256 := by
    change fee0.val.val < EVM.twoPow 256
    exact fee0.val.isLt
  have hfee1Lt : fee1.toNat < EVM.twoPow 256 := by
    change fee1.val.val < EVM.twoPow 256
    exact fee1.val.isLt
  have hliqLt : liq'.toNat < EVM.twoPow 128 := by
    simpa [liq'] using uint128Mask_bound liq
  have howed0Lt : owed0'.toNat < EVM.twoPow 128 := by
    simpa [owed0'] using uint128Mask_bound owed0
  have howed1Lt : owed1'.toNat < EVM.twoPow 128 := by
    simpa [owed1'] using uint128Mask_bound owed1
  have hencLiq :
      encodeABIValue? uint128 (.int (Int.ofNat liq'.toNat)) =
        some (EVM.Word.toBytesBE liq') := by
    simp [uint128, uint128Int, encodeABIValue?, encodeABIWord?, hwordLiq,
      hliqLt]
  have hencFee0 :
      encodeABIValue? uint256 (.int (Int.ofNat fee0.toNat)) =
        some (EVM.Word.toBytesBE fee0) := by
    simp [uint256, uint256Int, encodeABIValue?, encodeABIWord?, hwordFee0, hfee0Lt]
  have hencFee1 :
      encodeABIValue? uint256 (.int (Int.ofNat fee1.toNat)) =
        some (EVM.Word.toBytesBE fee1) := by
    simp [uint256, uint256Int, encodeABIValue?, encodeABIWord?, hwordFee1, hfee1Lt]
  have hencOwed0 :
      encodeABIValue? uint128 (.int (Int.ofNat owed0'.toNat)) =
        some (EVM.Word.toBytesBE owed0') := by
    simp [uint128, uint128Int, encodeABIValue?, encodeABIWord?, hwordOwed0,
      howed0Lt]
  have hencOwed1 :
      encodeABIValue? uint128 (.int (Int.ofNat owed1'.toNat)) =
        some (EVM.Word.toBytesBE owed1') := by
    simp [uint128, uint128Int, encodeABIValue?, encodeABIWord?, hwordOwed1,
      howed1Lt]
  have hhead :
      abiTupleHeadSize? [uint128, uint256, uint256, uint128, uint128] = some 160 := by
    native_decide
  have hdyn128 : isDynamicABIType uint128 = false := by native_decide
  have hdyn256 : isDynamicABIType uint256 = false := by native_decide
  change encodeReturnValues? [uint128, uint256, uint256, uint128, uint128]
      [.int (Int.ofNat liq'.toNat), .int (Int.ofNat fee0.toNat),
        .int (Int.ofNat fee1.toNat), .int (Int.ofNat owed0'.toNat),
        .int (Int.ofNat owed1'.toNat)] =
    some (UInt256.toByteArray liq' ++ UInt256.toByteArray fee0 ++
      UInt256.toByteArray fee1 ++ UInt256.toByteArray owed0' ++ UInt256.toByteArray owed1')
  rw [toByteArray_eq_toBytesBE liq', toByteArray_eq_toBytesBE fee0,
    toByteArray_eq_toBytesBE fee1, toByteArray_eq_toBytesBE owed0',
    toByteArray_eq_toBytesBE owed1']
  simp only [encodeReturnValues?, encodeABIValues?, encodeABIValuesFrom?, hhead, hencLiq,
    hencFee0, hencFee1, hencOwed0, hencOwed1, hdyn128, hdyn256, bind, Option.bind,
    Bool.false_eq_true, if_false, List.nil_append, List.append_nil]
  apply congrArg some
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp [liq', owed0', owed1']

theorem uniswapV3PoolPositionsReturn {v : PoolImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {owed1 owed0 fee1 fee0 liq : UInt256} {R : List UInt256} {scratch rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨1386⟩
      (owed1 :: owed0 :: fee1 :: fee0 :: liq :: R)
      scratch (UInt256.ofNat 3) rdata acc k C)
    (hscratch : scratch.size = 96)
    (hread64 : scratch.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 12 ≤ 1024) :
    RDret code g s0 acc
      (UInt256.toByteArray (UInt256.land liq uint128Mask) ++
        UInt256.toByteArray fee0 ++ UInt256.toByteArray fee1 ++
          UInt256.toByteArray (UInt256.land owed0 uint128Mask) ++
            UInt256.toByteArray (UInt256.land owed1 uint128Mask)) := by
  let liq' := UInt256.land liq uint128Mask
  let owed0' := UInt256.land owed0 uint128Mask
  let owed1' := UInt256.land owed1 uint128Mask
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩) ⟨1⟩ = uint128Mask := by
    native_decide
  exact evm_run h with [
    raw jumpdest (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw dup1 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) mem_cost (positionsScratch_mload64 hscratch hread64) (by decide)
      (by evm_ov),
    raw push1 ⟨1⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨128⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw shl (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw sub (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw swap7 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw dup8 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw and (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw dup2 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw mstore 6 (positionsScratchReturnMem1 scratch liq') (UInt256.ofNat 5) (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) mem_cost
      (by
        dsimp [liq']
        rw [hmask, show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          u256_land_comm uint128Mask liq, positionsScratchReturnMem1_eq]
        rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw dup2 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw add (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw swap6 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw swap1 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw swap6 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw mstore 3 (positionsScratchReturnMem2 scratch liq' fee0) (UInt256.ofNat 6) (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) mem_cost
      (by
        rw [show ((⟨128⟩ : UInt256) + ⟨32⟩).toNat = 160 from by decide,
          positionsScratchReturnMem2_eq]
        rfl)
      (by decide) (by evm_ov),
    raw dup5 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw dup2 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw add (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw swap4 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw swap1 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw swap4 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw mstore 3 (positionsScratchReturnMem3 scratch liq' fee0 fee1)
      (UInt256.ofNat 7) (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide) mem_cost
      (by
        rw [show ((⟨64⟩ : UInt256) + ⟨128⟩).toNat = 192 from by decide,
          positionsScratchReturnMem3_eq]
        rfl)
      (by decide) (by evm_ov),
    raw swap1 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw dup5 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw and (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨96⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw dup5 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw add (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw mstore 3 (positionsScratchReturnMem4 scratch liq' fee0 fee1 owed0')
      (UInt256.ofNat 8) (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide) mem_cost
      (by
        dsimp [owed0']
        rw [hmask, show ((⟨128⟩ : UInt256) + ⟨96⟩).toNat = 224 from by decide,
          u256_land_comm uint128Mask owed0, positionsScratchReturnMem4_eq]
        rfl)
      (by decide) (by evm_ov),
    raw swap1 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw swap3 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw and (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨128⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw dup3 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw add (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw mstore 3 (positionsScratchReturnMem scratch liq' fee0 fee1 owed0' owed1')
      (UInt256.ofNat 9) (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide) mem_cost
      (by
        dsimp [owed1']
        rw [hmask, show ((⟨128⟩ : UInt256) + ⟨128⟩).toNat = 256 from by decide,
          u256_land_comm uint128Mask owed1, positionsScratchReturnMem_eq]
        rfl)
      (by decide) (by evm_ov),
    raw swap1 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) mem_cost
      (positionsScratchReturnMem_mload64 liq' fee0 fee1 owed0' owed1' hscratch hread64)
      (by decide) (by evm_ov),
    raw swap1 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw dup2 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw swap1 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw sub (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw add (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw swap1 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw ret 0
      (UInt256.toByteArray liq' ++ UInt256.toByteArray fee0 ++ UInt256.toByteArray fee1 ++
        UInt256.toByteArray owed0' ++ UInt256.toByteArray owed1')
      (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide) mem_cost
      (by
        dsimp [liq', owed0', owed1']
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show ((⟨160⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat =
            160 from by decide]
        exact positionsScratchReturnMem_read128_160
          (UInt256.land liq uint128Mask) fee0 fee1
          (UInt256.land owed0 uint128Mask) (UInt256.land owed1 uint128Mask) hscratch)
      (by evm_ov)]

private theorem uniswapV3PoolPositionsLoadedToReturn {v : PoolImmutables}
    {code : ByteArray} {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (rdLoaded : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨1386⟩
      (positionsTokensOwed1Word σ I :: positionsTokensOwed0Word σ I ::
        positionsFeeGrowthInside1Word σ I :: positionsFeeGrowthInside0Word σ I ::
        positionsLiquidityWord σ I :: ⟨1386⟩ :: [solcSelectorWord I])
      (solcMappingHashMem ⟨7⟩ (positionsArgWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    RDret code g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.land (positionsLiquidityWord σ I) uint128Mask) ++
        UInt256.toByteArray (positionsFeeGrowthInside0Word σ I) ++
          UInt256.toByteArray (positionsFeeGrowthInside1Word σ I) ++
            UInt256.toByteArray (UInt256.land (positionsTokensOwed0Word σ I) uint128Mask) ++
              UInt256.toByteArray
                (UInt256.land (positionsTokensOwed1Word σ I) uint128Mask)) := by
  exact uniswapV3PoolPositionsReturn hpatch
    (owed1 := positionsTokensOwed1Word σ I) (owed0 := positionsTokensOwed0Word σ I)
    (fee1 := positionsFeeGrowthInside1Word σ I)
    (fee0 := positionsFeeGrowthInside0Word σ I)
    (liq := positionsLiquidityWord σ I) (R := [⟨1386⟩, solcSelectorWord I])
    rdLoaded (solcMappingHashMem_size ⟨7⟩ (positionsArgWord I))
    (solcMappingHashMem_read64 ⟨7⟩ (positionsArgWord I))
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem uniswapV3PoolPositionsEvm {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 11 == I.calldata.extract 0 4) = true)
    (hsz36 : 36 ≤ I.calldata.size) :
    RDret code g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (positionsLiquidityWord σ I) ++
        UInt256.toByteArray (positionsFeeGrowthInside0Word σ I) ++
          UInt256.toByteArray (positionsFeeGrowthInside1Word σ I) ++
            UInt256.toByteArray (positionsTokensOwed0Word σ I) ++
              UInt256.toByteArray (positionsTokensOwed1Word σ I)) := by
  have hreach := uniswapV3PoolPositionsReachEntry
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize hsel
  have hdecoded := uniswapV3PoolPositionsExternalLenOk hpatch hreach hsz36 hsize
  obtain ⟨_, _, rdDecoded⟩ := hdecoded
  obtain ⟨_, _, rdLoaded⟩ := uniswapV3PoolPositionsDecodedToLoaded hpatch rdDecoded
  have hret := uniswapV3PoolPositionsLoadedToReturn hpatch rdLoaded
  have hcleanLiq :
      UInt256.land (positionsLiquidityWord σ I) uint128Mask =
        positionsLiquidityWord σ I := by
    exact uint128Mask_clean (by
      simpa [positionsLiquidityWord] using uint128Mask_bound (solcSlotWord σ I
        (positionsBaseSlot I)))
  have hcleanOwed0 :
      UInt256.land (positionsTokensOwed0Word σ I) uint128Mask =
        positionsTokensOwed0Word σ I := by
    exact uint128Mask_clean (by
      simpa [positionsTokensOwed0Word] using uint128Mask_bound (positionsPackedWord σ I))
  have hcleanOwed1 :
      UInt256.land (positionsTokensOwed1Word σ I) uint128Mask =
        positionsTokensOwed1Word σ I := by
    exact uint128Mask_clean (by
      simpa [positionsTokensOwed1Word] using
        uint128Mask_bound (UInt256.div (positionsPackedWord σ I) positionsShift))
  simpa [hcleanLiq, hcleanOwed0, hcleanOwed1] using hret

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
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdecode := uniswapV3PoolPositionsDecodeOk (v := v) (I := I) hsz36
    have hbody := uniswapV3PoolPositionsSourceBody (v := v) (cA := cA)
      (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) hwv
    have hrd := uniswapV3PoolPositionsEvm (v := v) (code := code) (cA := cA)
      (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) hpatch hcode hwv hsz hsize hsel hsz36
    exact hrd.reEquivExecutionTransport hcode hdispatch hdecode hbody hvalue hAccounts
      (by
        rw [show positionsTransition.returnType =
          [uint128, uint256, uint256, uint128, uint128] from rfl]
        exact returnEquiv.returned rfl
          (positionsReturnEncodingMasked (solcSlotWord σ_evm I (positionsBaseSlot I))
            (positionsFeeGrowthInside0Word σ_evm I)
            (positionsFeeGrowthInside1Word σ_evm I)
            (positionsPackedWord σ_evm I)
            (UInt256.div (positionsPackedWord σ_evm I) positionsShift)))
  · have hshort : I.calldata.size < 36 := by omega
    have hdecode := uniswapV3PoolPositionsDecodeShort (v := v) (I := I) hshort
    have hrd := uniswapV3PoolPositionsEvmDecodeShort (v := v) (code := code)
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) hpatch hcode hwv hsz hsize hsel hshort
    exact hrd.reEquivDecodingFailed hcode hdispatch hdecode

end Benchmarks.UniswapV3Pool
