import Benchmarks.UniswapV3Pool.SetFeeProtocolSuccess

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

theorem setFeeProtocolUint8Mask_toNat :
    setFeeProtocolUint8Mask.toNat = 2 ^ 8 - 1 := by
  exact ulit_toNat' _ (by norm_num [UInt256.size])

theorem setFeeProtocolUint8Mask_decode (w : UInt256) :
    (UInt256.land w setFeeProtocolUint8Mask).toNat = w.toNat % EVM.twoPow 8 := by
  rw [u256_land_toNat, setFeeProtocolUint8Mask_toNat, nat_land_mask_eq_mod]
  exact Nat.mod_eq_of_lt (by
    exact lt_trans (Nat.mod_lt _ (by norm_num [EVM.twoPow]))
      (by norm_num [EVM.twoPow, UInt256.size]))

theorem decodeScalarWordWithMode_uint8_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeScalarWordWithMode? DecodeMode.legacySolc05 uint8 bytes start =
      some
        (.int (Int.ofNat
          (UInt256.land (ABI.bytesToWord ((bytes.drop start).take 32))
            setFeeProtocolUint8Mask).toNat),
          start + 32) := by
  simp only [decodeScalarWordWithMode?]
  unfold readWord? readBytes? uint8 uint8Int
  rw [if_pos hlen]
  simp only [bind, Option.bind]
  unfold decodeABIWord?
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
  rw [setFeeProtocolUint8Mask_decode]
  rfl

theorem decodeScalarWordsWithMode_uint8_uint8_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32) :
    decodeScalarWordsWithMode? DecodeMode.legacySolc05 [uint8, uint8] bytes 0 =
      some
        [ .int (Int.ofNat
            (UInt256.land (ABI.bytesToWord (bytes.take 32))
              setFeeProtocolUint8Mask).toNat),
          .int (Int.ofNat
            (UInt256.land (ABI.bytesToWord ((bytes.drop 32).take 32))
              setFeeProtocolUint8Mask).toNat) ] := by
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWordWithMode_uint8_ok (bytes := bytes) (start := 0) (by simpa using hlen0)]
  simp only [List.drop_zero, bind, Option.bind]
  rw [decodeScalarWordWithMode_uint8_ok (bytes := bytes) (start := 32) hlen32]

theorem decodeScalarWordsWithMode_uint8_uint8_none_short {bytes : List UInt8}
    (hshort : bytes.length < 64) :
    decodeScalarWordsWithMode? DecodeMode.legacySolc05 [uint8, uint8] bytes 0 = none := by
  simp only [decodeScalarWordsWithMode?]
  by_cases hlen0 : (bytes.take 32).length = 32
  · rw [decodeScalarWordWithMode_uint8_ok (bytes := bytes) (start := 0) (by simpa using hlen0)]
    simp only [bind, Option.bind]
    have hlen32 : ¬ ((bytes.drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop]
      omega
    unfold decodeScalarWordWithMode? readWord? readBytes? uint8 uint8Int
    rw [if_neg hlen32]
    simp only [bind, Option.bind]
  · unfold decodeScalarWordWithMode? readWord? readBytes? uint8 uint8Int
    simp only [List.drop_zero]
    rw [if_neg hlen0]
    simp only [bind, Option.bind]

theorem uniswapV3PoolSetFeeProtocolDecodeOk {v : PoolImmutables} {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode
      ((setfeeprotocolTransition v).params.map Param.name)
      (transitionSignature (setfeeprotocolTransition v)).paramTypes I.calldata =
        some (setFeeProtocolStore I) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 :
      (((I.calldata.toList.drop 4).drop 32).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) =
      calldataWord I.calldata 4 :=
    decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord ((I.calldata.toList.drop 36).take 32) =
      calldataWord I.calldata 36 := by
    exact decode_word_at_eq I.calldata 36 (by omega) (by norm_num)
  rw [show (config v).abiDecodeMode = DecodeMode.legacySolc05 from rfl]
  rw [decodeCalldataWithMode_legacyScalarWords_eq
    (names := (setfeeprotocolTransition v).params.map Param.name)
    (types := (transitionSignature (setfeeprotocolTransition v)).paramTypes)
    (cd := I.calldata)]
  · rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
    change (match decodeScalarWordsWithMode? DecodeMode.legacySolc05 [uint8, uint8]
        (I.calldata.toList.drop 4) 0 with
      | some values => decodeCalldata.insertValues ["feeProtocol0", "feeProtocol1"] values ∅
      | none => none) = some (setFeeProtocolStore I)
    rw [decodeScalarWordsWithMode_uint8_uint8_ok
      (bytes := I.calldata.toList.drop 4) htake4 htake36]
    simp [decodeCalldata.insertValues, setFeeProtocolStore, setFeeProtocolArg0Value,
      setFeeProtocolArg1Value, setFeeProtocolArg0Word, setFeeProtocolArg1Word]
    rw [hword4, hword36]
  · simp [setfeeprotocolTransition, transitionSignature, isABIScalarWordType, uint8]

theorem uniswapV3PoolSetFeeProtocolDecodeShort {v : PoolImmutables} {I : ExecutionEnv}
    (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode (config v).abiDecodeMode
      ((setfeeprotocolTransition v).params.map Param.name)
      (transitionSignature (setfeeprotocolTransition v)).paramTypes I.calldata = none := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [show (config v).abiDecodeMode = DecodeMode.legacySolc05 from rfl]
  rw [decodeCalldataWithMode_legacyScalarWords_eq
    (names := (setfeeprotocolTransition v).params.map Param.name)
    (types := (transitionSignature (setfeeprotocolTransition v)).paramTypes)
    (cd := I.calldata)]
  · by_cases hsz4 : I.calldata.size < 4
    · rw [if_pos (by rw [htlen]; omega : I.calldata.toList.length < 4)]
    · rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
      change (match decodeScalarWordsWithMode? DecodeMode.legacySolc05 [uint8, uint8]
          (I.calldata.toList.drop 4) 0 with
        | some values => decodeCalldata.insertValues ["feeProtocol0", "feeProtocol1"] values ∅
        | none => none) = none
      rw [decodeScalarWordsWithMode_uint8_uint8_none_short
        (bytes := I.calldata.toList.drop 4)
        (by rw [List.length_drop, htlen]; omega)]
  · simp [setfeeprotocolTransition, transitionSignature, isABIScalarWordType, uint8]

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolDispatch_setFeeProtocol {v : PoolImmutables} {cd : ByteArray}
    (hsel : (uniswapV3PoolSelBytes 14 == cd.extract 0 4) = true) :
    dispatchMsg (contract v) cd = some (setfeeprotocolTransition v) := by
  apply dispatchMsg_eq_some_of_split
    (pre := [burnTransition, collectTransition v, collectprotocolTransition v,
      factoryTransition v, feeTransition v, feegrowthglobal0X128Transition,
      feegrowthglobal1X128Transition, flashTransition v,
      increaseobservationcardinalitynextTransition v, initializeTransition, liquidityTransition,
      maxliquiditypertickTransition v, mintTransition v, observationsTransition,
      observeTransition v, positionsTransition, protocolfeesTransition])
    (post := [slot0Transition, snapshotcumulativesinsideTransition v, swapTransition v,
      tickbitmapTransition, tickspacingTransition v, ticksTransition, token0Transition v,
      token1Transition v])
  · simp [contract, transitions]
  · intro t ht
    simp at ht
    rcases ht with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    · rw [selectorOf, burnSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 17) (j := 14)
          (by native_decide) hsel
    · rw [selectorOf, collectSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 10) (j := 14)
          (by native_decide) hsel
    · rw [selectorOf, collectProtocolSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 15) (j := 14)
          (by native_decide) hsel
    · rw [selectorOf, factorySelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 19) (j := 14)
          (by native_decide) hsel
    · rw [selectorOf, feeSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 22) (j := 14)
          (by native_decide) hsel
    · rw [selectorOf, feeGrowthGlobal0X128SelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 23) (j := 14)
          (by native_decide) hsel
    · rw [selectorOf, feeGrowthGlobal1X128SelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 8) (j := 14)
          (by native_decide) hsel
    · rw [selectorOf, flashSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 9) (j := 14)
          (by native_decide) hsel
    · rw [selectorOf, increaseObservationCardinalityNextSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 5) (j := 14)
          (by native_decide) hsel
    · rw [selectorOf, initializeSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 25) (j := 14)
          (by native_decide) hsel
    · rw [selectorOf, liquiditySelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 2) (j := 14)
          (by native_decide) hsel
    · rw [selectorOf, maxLiquidityPerTickSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 13) (j := 14)
          (by native_decide) hsel
    · rw [selectorOf, mintSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 7) (j := 14)
          (by native_decide) hsel
    · rw [selectorOf, observationsSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 4) (j := 14)
          (by native_decide) hsel
    · rw [selectorOf, observeSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 16) (j := 14)
          (by native_decide) hsel
    · rw [selectorOf, positionsSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 11) (j := 14)
          (by native_decide) hsel
    · rw [selectorOf, protocolFeesSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 3) (j := 14)
          (by native_decide) hsel
  · rw [selectorOf, setFeeProtocolSelectorBytes v]
    simpa [uniswapV3PoolSelBytes] using hsel

private theorem uniswapV3PoolPatchPreservesJumpDest8208 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨8208⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolPatchPreservesJumpDest8276 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨8276⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched8208 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨8208⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest8208

theorem uniswapV3PoolJumpDestPatched8276 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨8276⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest8276

theorem uniswapV3PoolSetFeeProtocolReachEntry {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 14 == I.calldata.extract 0 4) = true) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨1486⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := uniswapV3PoolReachSelector32
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize
  have hword : solcSelectorWord I = uniswapV3PoolSelNat 14 := by
    simpa [uniswapV3PoolSelBytes, uniswapV3PoolSelNat] using
      solcSelectorWord_eq_of_beq I hsz 0x82 0x06 0xa4 0xd1
        (uniswapV3PoolSelNat 14) (by native_decide) hsel
  have hgt32 : UInt256.gt (armSelNat code ⟨32⟩) (solcSelectorWord I) = ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h43 := uniswapV3PoolSelectorSplitNotTakenTo (next := ⟨43⟩) hpatch h32 hgt32
  have hgt43 : UInt256.gt (armSelNat code ⟨43⟩) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h152 := uniswapV3PoolSelectorSplitTakenTo (next := ⟨152⟩) hpatch h43 hgt43
  have hgt152 : UInt256.gt (armSelNat code ⟨152⟩) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h201 := uniswapV3PoolSelectorSplitTakenTo (next := ⟨201⟩) hpatch h152 hgt152
  have hmiss13 : (uniswapV3PoolSelBytes 13 == I.calldata.extract 0 4) = false :=
    uniswapV3PoolSelectorMissOfHit I (by native_decide) hsel
  have h212 := uniswapV3PoolSelectorArmMissToOf (i := 13) (next := ⟨212⟩)
    hpatch hsz hmiss13 h201
  have h1486 := uniswapV3PoolSelectorArmHitTo (i := 14) (target := ⟨1486⟩)
    hpatch hsz hsel h212
  exact ⟨_, _, h1486⟩

set_option maxHeartbeats 3000000 in
private theorem uniswapV3PoolSetFeeProtocolExternalLenOk {v : PoolImmutables}
    {code : ByteArray} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨1486⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨1508⟩
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ⟨857⟩ ::
        [solcSelectorWord I])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  exact RD.solcExternalStaticArgsLenOk (need := ⟨64⟩)
    (entry := ⟨1486⟩) (ret := ⟨857⟩) (decoded := ⟨1508⟩) hreach
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
    (solcDecodeLenCheckOkUnsigned (by simpa using hsz68) hsize)

private theorem uniswapV3PoolSetFeeProtocolDecodedReachRoutine {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {de ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨1508⟩ (de :: ⟨4⟩ :: ret :: R) mem aw rdata acc k C)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8208⟩
      (setFeeProtocolArg1Word ee :: setFeeProtocolArg0Word ee :: ret :: R)
      mem aw rdata acc k' C' := by
  have harg0 :
      UInt256.land setFeeProtocolUint8Mask (calldataWord ee.calldata 4) =
        setFeeProtocolArg0Word ee := by
    rw [u256_land_comm]
  have rd1509 : RD code ee g s0 ⟨1509⟩ (de :: ⟨4⟩ :: ret :: R)
      mem aw rdata acc (k + 1) (C + 1) := by
    simpa using h.jumpdest
      (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide)
      (by evm_ov)
  have rd1510 : RD code ee g s0 ⟨1510⟩ (⟨4⟩ :: ret :: R)
      mem aw rdata acc (k + 1 + 1) (C + 1 + 2) := by
    simpa using rd1509.pop
      (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide)
      (by evm_ov)
  have rd1512 : RD code ee g s0 ⟨1512⟩ (setFeeProtocolUint8Mask :: ⟨4⟩ :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1) (C + 1 + 2 + 3) := by
    simpa [setFeeProtocolUint8Mask] using rd1510.push1 ⟨255⟩
      (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide)
      (by evm_ov)
  have rd1513 : RD code ee g s0 ⟨1513⟩
      (⟨4⟩ :: setFeeProtocolUint8Mask :: ⟨4⟩ :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1 + 1) (C + 1 + 2 + 3 + 3) := by
    simpa using rd1512.dup2
      (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide)
      (by evm_ov)
  have rd1514 : RD code ee g s0 ⟨1514⟩
      (calldataWord ee.calldata 4 :: setFeeProtocolUint8Mask :: ⟨4⟩ :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1 + 1 + 1) (C + 1 + 2 + 3 + 3 + 3) := by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide] using
      (rd1513.calldataload
        (by
          rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
          native_decide)
        (by evm_ov))
  have rd1515 : RD code ee g s0 ⟨1515⟩
      (setFeeProtocolUint8Mask :: calldataWord ee.calldata 4 ::
        setFeeProtocolUint8Mask :: ⟨4⟩ :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1 + 1 + 1 + 1)
        (C + 1 + 2 + 3 + 3 + 3 + 3) := by
    simpa using rd1514.dup2
      (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide)
      (by evm_ov)
  have rd1516 : RD code ee g s0 ⟨1516⟩
      (setFeeProtocolArg0Word ee :: setFeeProtocolUint8Mask :: ⟨4⟩ :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (C + 1 + 2 + 3 + 3 + 3 + 3 + 3) := by
    simpa [harg0] using rd1515.and
      (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide)
      (by evm_ov)
  have rd1517 : RD code ee g s0 ⟨1517⟩
      (⟨4⟩ :: setFeeProtocolUint8Mask :: setFeeProtocolArg0Word ee :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (C + 1 + 2 + 3 + 3 + 3 + 3 + 3 + 3) := by
    simpa using rd1516.swap2
      (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide)
      (by evm_ov)
  have rd1519 : RD code ee g s0 ⟨1519⟩
      (⟨32⟩ :: ⟨4⟩ :: setFeeProtocolUint8Mask :: setFeeProtocolArg0Word ee :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (C + 1 + 2 + 3 + 3 + 3 + 3 + 3 + 3 + 3) := by
    simpa using rd1517.push1 ⟨32⟩
      (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide)
      (by evm_ov)
  have rd1520 : RD code ee g s0 ⟨1520⟩
      (⟨36⟩ :: setFeeProtocolUint8Mask :: setFeeProtocolArg0Word ee :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (C + 1 + 2 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3) := by
    simpa using rd1519.add
      (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide)
      (by evm_ov)
  have rd1521 : RD code ee g s0 ⟨1521⟩
      (calldataWord ee.calldata 36 :: setFeeProtocolUint8Mask ::
        setFeeProtocolArg0Word ee :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (C + 1 + 2 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3) := by
    simpa [calldataWord, show (⟨36⟩ : UInt256).toNat = 36 from by decide] using
      (rd1520.calldataload
        (by
          rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
          native_decide)
        (by evm_ov))
  have rd1522 : RD code ee g s0 ⟨1522⟩
      (setFeeProtocolArg1Word ee :: setFeeProtocolArg0Word ee :: ret :: R)
      mem aw rdata acc
        (k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (C + 1 + 2 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3) := by
    simpa [setFeeProtocolArg1Word] using rd1521.and
      (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide)
      (by evm_ov)
  have rd1525 : RD code ee g s0 ⟨1525⟩
      (⟨8208⟩ :: setFeeProtocolArg1Word ee :: setFeeProtocolArg0Word ee :: ret :: R)
      mem aw rdata acc
        (k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (C + 1 + 2 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3) := by
    simpa using rd1522.push2 ⟨8208⟩
      (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide)
      (by evm_ov)
  exact ⟨_, _, rd1525.jump
    (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide)
    (uniswapV3PoolJumpDestPatched8208 hpatch)
    (by evm_ov)⟩

private theorem uniswapV3PoolSetFeeProtocolPatchDisjoint1 {v : PoolImmutables}
    {pc : UInt256} (hlo : 8208 ≤ pc.toNat) (hhi : pc.toNat + 1 ≤ 8315) :
    ∀ p ∈ patches v, pc.toNat + 1 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  all_goals omega

private theorem uniswapV3PoolSetFeeProtocolPatchDisjoint2 {v : PoolImmutables}
    {pc : UInt256} (hlo : 8208 ≤ pc.toNat) (hhi : pc.toNat + 2 ≤ 8315) :
    ∀ p ∈ patches v, pc.toNat + 2 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  all_goals omega

private theorem uniswapV3PoolSetFeeProtocolPatchDisjoint3 {v : PoolImmutables}
    {pc : UInt256} (hlo : 8208 ≤ pc.toNat) (hhi : pc.toNat + 3 ≤ 8315) :
    ∀ p ∈ patches v, pc.toNat + 3 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  all_goals omega

private theorem uniswapV3PoolSetFeeProtocolPatchDisjoint4 {v : PoolImmutables}
    {pc : UInt256} (hlo : 8208 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ 8315) :
    ∀ p ∈ patches v, pc.toNat + 4 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  all_goals omega

private theorem uniswapV3PoolSetFeeProtocolPatchDisjoint5 {v : PoolImmutables}
    {pc : UInt256} (hlo : 8208 ≤ pc.toNat) (hhi : pc.toNat + 5 ≤ 8315) :
    ∀ p ∈ patches v, pc.toNat + 5 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  all_goals omega

private theorem uniswapV3PoolSetFeeProtocolPatchDisjointAfterFactory1 {v : PoolImmutables}
    {pc : UInt256} (hlo : 8347 ≤ pc.toNat) (hhi : pc.toNat + 1 ≤ 8829) :
    ∀ p ∈ patches v, pc.toNat + 1 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  all_goals omega

private theorem uniswapV3PoolSetFeeProtocolPatchDisjointAfterFactory2 {v : PoolImmutables}
    {pc : UInt256} (hlo : 8347 ≤ pc.toNat) (hhi : pc.toNat + 2 ≤ 8829) :
    ∀ p ∈ patches v, pc.toNat + 2 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  all_goals omega

private theorem uniswapV3PoolSetFeeProtocolPatchDisjointAfterFactory3 {v : PoolImmutables}
    {pc : UInt256} (hlo : 8347 ≤ pc.toNat) (hhi : pc.toNat + 3 ≤ 8829) :
    ∀ p ∈ patches v, pc.toNat + 3 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  all_goals omega

private theorem uniswapV3PoolSetFeeProtocolPatchDisjointAfterFactory4 {v : PoolImmutables}
    {pc : UInt256} (hlo : 8347 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ 8829) :
    ∀ p ∈ patches v, pc.toNat + 4 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  all_goals omega

private theorem uniswapV3PoolSetFeeProtocolPatchDisjointAfterFactory5 {v : PoolImmutables}
    {pc : UInt256} (hlo : 8347 ≤ pc.toNat) (hhi : pc.toNat + 5 ≤ 8829) :
    ∀ p ∈ patches v, pc.toNat + 5 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  all_goals omega

private theorem uniswapV3PoolSetFeeProtocolDecodePatchedPush1 {v : PoolImmutables}
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

private theorem uniswapV3PoolSetFeeProtocolDecodePatchedPush2 {v : PoolImmutables}
    {code : ByteArray} {pc n : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hwin : pc.toNat + 3 ≤ uniswapV3PoolBytecode.size)
    (hdisj : ∀ p ∈ patches v, pc.toNat + 3 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat)
    (hgetTemplate : uniswapV3PoolBytecode.get? pc.toNat = some 0x61)
    (hval : uInt256OfByteArray
        (uniswapV3PoolBytecode.extract' pc.toNat.succ (pc.toNat.succ + 2)) = n) :
    decode code pc = some (.Push .PUSH2, some (n, 2)) := by
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
      code.extract' pc.toNat.succ (pc.toNat.succ + 2) =
        uniswapV3PoolBytecode.extract' pc.toNat.succ (pc.toNat.succ + 2) := by
    unfold ByteArray.extract'
    have hguard :
        (decide (pc.toNat.succ < 2 ^ 64) && decide (pc.toNat.succ + 2 < 2 ^ 64)) =
          true := by
      rw [Bool.and_eq_true]
      constructor <;> rw [decide_eq_true_eq] <;> omega
    rw [if_pos hguard, if_pos hguard]
    exact patchRuntime_extract_eq (start := pc.toNat.succ) (stop := pc.toNat.succ + 2)
      (template := uniswapV3PoolBytecode) (out := code) (ps := patches v)
      (by omega) (by omega)
      (fun p hp => by
        rcases hdisj p hp with hbefore | hafter
        · exact Or.inl hbefore
        · exact Or.inr (by omega))
      hpatch
  have hgetSome : code.get? pc.toNat = some 0x61 := by
    rw [hget, hgetTemplate]
  have hparse : (some (0x61 : UInt8) >>= parseInstr) = some (.Push .PUSH2) := by
    native_decide
  unfold decode
  rw [hgetSome, hparse]
  change some (Operation.Push Operation.POp.PUSH2,
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 2)), 2)) =
    some (Operation.Push Operation.POp.PUSH2, some (n, 2))
  rw [hextract, hval]

private theorem uniswapV3PoolSetFeeProtocolDecodePatchedPush3 {v : PoolImmutables}
    {code : ByteArray} {pc n : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hwin : pc.toNat + 4 ≤ uniswapV3PoolBytecode.size)
    (hdisj : ∀ p ∈ patches v, pc.toNat + 4 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat)
    (hgetTemplate : uniswapV3PoolBytecode.get? pc.toNat = some 0x62)
    (hval : uInt256OfByteArray
        (uniswapV3PoolBytecode.extract' pc.toNat.succ (pc.toNat.succ + 3)) = n) :
    decode code pc = some (.Push .PUSH3, some (n, 3)) := by
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
      code.extract' pc.toNat.succ (pc.toNat.succ + 3) =
        uniswapV3PoolBytecode.extract' pc.toNat.succ (pc.toNat.succ + 3) := by
    unfold ByteArray.extract'
    have hguard :
        (decide (pc.toNat.succ < 2 ^ 64) && decide (pc.toNat.succ + 3 < 2 ^ 64)) =
          true := by
      rw [Bool.and_eq_true]
      constructor <;> rw [decide_eq_true_eq] <;> omega
    rw [if_pos hguard, if_pos hguard]
    exact patchRuntime_extract_eq (start := pc.toNat.succ) (stop := pc.toNat.succ + 3)
      (template := uniswapV3PoolBytecode) (out := code) (ps := patches v)
      (by omega) (by omega)
      (fun p hp => by
        rcases hdisj p hp with hbefore | hafter
        · exact Or.inl hbefore
        · exact Or.inr (by omega))
      hpatch
  have hgetSome : code.get? pc.toNat = some 0x62 := by
    rw [hget, hgetTemplate]
  have hparse : (some (0x62 : UInt8) >>= parseInstr) = some (.Push .PUSH3) := by
    native_decide
  unfold decode
  rw [hgetSome, hparse]
  change some (Operation.Push Operation.POp.PUSH3,
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 3)), 3)) =
    some (Operation.Push Operation.POp.PUSH3, some (n, 3))
  rw [hextract, hval]

private theorem uniswapV3PoolSetFeeProtocolDecodePatchedPush4 {v : PoolImmutables}
    {code : ByteArray} {pc n : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hwin : pc.toNat + 5 ≤ uniswapV3PoolBytecode.size)
    (hdisj : ∀ p ∈ patches v, pc.toNat + 5 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat)
    (hgetTemplate : uniswapV3PoolBytecode.get? pc.toNat = some 0x63)
    (hval : uInt256OfByteArray
        (uniswapV3PoolBytecode.extract' pc.toNat.succ (pc.toNat.succ + 4)) = n) :
    decode code pc = some (.Push .PUSH4, some (n, 4)) := by
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
      code.extract' pc.toNat.succ (pc.toNat.succ + 4) =
        uniswapV3PoolBytecode.extract' pc.toNat.succ (pc.toNat.succ + 4) := by
    unfold ByteArray.extract'
    have hguard :
        (decide (pc.toNat.succ < 2 ^ 64) && decide (pc.toNat.succ + 4 < 2 ^ 64)) =
          true := by
      rw [Bool.and_eq_true]
      constructor <;> rw [decide_eq_true_eq] <;> omega
    rw [if_pos hguard, if_pos hguard]
    exact patchRuntime_extract_eq (start := pc.toNat.succ) (stop := pc.toNat.succ + 4)
      (template := uniswapV3PoolBytecode) (out := code) (ps := patches v)
      (by omega) (by omega)
      (fun p hp => by
        rcases hdisj p hp with hbefore | hafter
        · exact Or.inl hbefore
        · exact Or.inr (by omega))
      hpatch
  have hgetSome : code.get? pc.toNat = some 0x63 := by
    rw [hget, hgetTemplate]
  have hparse : (some (0x63 : UInt8) >>= parseInstr) = some (.Push .PUSH4) := by
    native_decide
  unfold decode
  rw [hgetSome, hparse]
  change some (Operation.Push Operation.POp.PUSH4,
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 4)), 4)) =
    some (Operation.Push Operation.POp.PUSH4, some (n, 4))
  rw [hextract, hval]

private theorem uniswapV3PoolSetFeeProtocolLockedRevertTailWf {v : PoolImmutables}
    {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcErrorStringRevertTailWf code ⟨8226⟩ ⟨3⟩ ⟨5001035⟩ ⟨232⟩ .PUSH3 3 := by
  repeat' constructor
  · exact uniswapV3PoolSetFeeProtocolDecodePatchedPush1 (pc := ⟨8226⟩) (n := ⟨64⟩)
      hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint2 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  · refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8228⟩) (byte := 0x80)
      (op := .DUP1) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  · refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8229⟩) (byte := 0x51)
      (op := .MLOAD) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  · exact uniswapV3PoolSetFeeProtocolDecodePatchedPush3 (pc := ⟨8230⟩)
      (n := ⟨4594637⟩) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint4 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  · exact uniswapV3PoolSetFeeProtocolDecodePatchedPush1 (pc := ⟨8234⟩) (n := ⟨229⟩)
      hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint2 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  · refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8236⟩) (byte := 0x1b)
      (op := .SHL) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  · refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8237⟩) (byte := 0x81)
      (op := .DUP2) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  · refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8238⟩) (byte := 0x52)
      (op := .MSTORE) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  · exact uniswapV3PoolSetFeeProtocolDecodePatchedPush1 (pc := ⟨8239⟩) (n := ⟨32⟩)
      hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint2 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  · exact uniswapV3PoolSetFeeProtocolDecodePatchedPush1 (pc := ⟨8241⟩) (n := ⟨4⟩)
      hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint2 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  · refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8243⟩) (byte := 0x82)
      (op := .DUP3) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  · refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8244⟩) (byte := 0x01)
      (op := .ADD) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  · refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8245⟩) (byte := 0x52)
      (op := .MSTORE) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  · exact uniswapV3PoolSetFeeProtocolDecodePatchedPush1 (pc := ⟨8246⟩) (n := ⟨3⟩)
      hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint2 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  · exact uniswapV3PoolSetFeeProtocolDecodePatchedPush1 (pc := ⟨8248⟩) (n := ⟨36⟩)
      hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint2 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  · refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8250⟩) (byte := 0x82)
      (op := .DUP3) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  · refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8251⟩) (byte := 0x01)
      (op := .ADD) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  · refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8252⟩) (byte := 0x52)
      (op := .MSTORE) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  · exact uniswapV3PoolSetFeeProtocolDecodePatchedPush3 (pc := ⟨8253⟩)
      (n := ⟨5001035⟩) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint4 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  · exact uniswapV3PoolSetFeeProtocolDecodePatchedPush1 (pc := ⟨8257⟩) (n := ⟨232⟩)
      hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint2 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  · refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8259⟩) (byte := 0x1b)
      (op := .SHL) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  · exact uniswapV3PoolSetFeeProtocolDecodePatchedPush1 (pc := ⟨8260⟩) (n := ⟨68⟩)
      hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint2 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  · refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8262⟩) (byte := 0x82)
      (op := .DUP3) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  · refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8263⟩) (byte := 0x01)
      (op := .ADD) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  · refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8264⟩) (byte := 0x52)
      (op := .MSTORE) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  · refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8265⟩) (byte := 0x90)
      (op := .SWAP1) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  · refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8266⟩) (byte := 0x51)
      (op := .MLOAD) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  · refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8267⟩) (byte := 0x90)
      (op := .SWAP1) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  · refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8268⟩) (byte := 0x81)
      (op := .DUP2) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  · refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8269⟩) (byte := 0x90)
      (op := .SWAP1) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  · refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8270⟩) (byte := 0x03)
      (op := .SUB) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  · exact uniswapV3PoolSetFeeProtocolDecodePatchedPush1 (pc := ⟨8271⟩) (n := ⟨100⟩)
      hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint2 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  · refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8273⟩) (byte := 0x01)
      (op := .ADD) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  · refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8274⟩) (byte := 0x90)
      (op := .SWAP1) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  · refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8275⟩) (byte := 0xfd)
      (op := .REVERT) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)

private theorem uniswapV3PoolSetFeeProtocolLockEnterOk {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨8208⟩ R mem aw rdata (cA, σ) k C)
    (hperm : ee.perm = true)
    (hunlocked : setFeeProtocolUnlockedByte σ ee ≠ ⟨0⟩)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8290⟩ R mem aw rdata
      (cA, sstoreAccountMap ee.codeOwner σ ⟨0⟩ (setFeeProtocolLockedSlotWord σ ee)) k' C' := by
  have hd8208 : decode code ⟨8208⟩ = some (.JUMPDEST, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8208⟩) (byte := 0x5b)
      (op := .JUMPDEST) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8209 : decode code ⟨8209⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    exact uniswapV3PoolSetFeeProtocolDecodePatchedPush1 (pc := ⟨8209⟩) (n := ⟨0⟩)
      hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint2 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8211 : decode code ⟨8211⟩ = some (.SLOAD, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8211⟩) (byte := 0x54)
      (op := .SLOAD) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8212 : decode code ⟨8212⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    exact uniswapV3PoolSetFeeProtocolDecodePatchedPush1 (pc := ⟨8212⟩) (n := ⟨1⟩)
      hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint2 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8214 : decode code ⟨8214⟩ = some (.Push .PUSH1, some (⟨240⟩, 1)) := by
    exact uniswapV3PoolSetFeeProtocolDecodePatchedPush1 (pc := ⟨8214⟩) (n := ⟨240⟩)
      hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint2 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8216 : decode code ⟨8216⟩ = some (.SHL, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8216⟩) (byte := 0x1b)
      (op := .SHL) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8217 : decode code ⟨8217⟩ = some (.SWAP1, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8217⟩) (byte := 0x90)
      (op := .SWAP1) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8218 : decode code ⟨8218⟩ = some (.DIV, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8218⟩) (byte := 0x04)
      (op := .DIV) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8219 : decode code ⟨8219⟩ = some (.Push .PUSH1, some (⟨255⟩, 1)) := by
    exact uniswapV3PoolSetFeeProtocolDecodePatchedPush1 (pc := ⟨8219⟩) (n := ⟨255⟩)
      hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint2 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8221 : decode code ⟨8221⟩ = some (.AND, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8221⟩) (byte := 0x16)
      (op := .AND) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8222 : decode code ⟨8222⟩ = some (.Push .PUSH2, some (⟨8276⟩, 2)) := by
    exact uniswapV3PoolSetFeeProtocolDecodePatchedPush2 (pc := ⟨8222⟩) (n := ⟨8276⟩)
      hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint3 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8225 : decode code ⟨8225⟩ = some (.JUMPI, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8225⟩) (byte := 0x57)
      (op := .JUMPI) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8276 : decode code ⟨8276⟩ = some (.JUMPDEST, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8276⟩) (byte := 0x5b)
      (op := .JUMPDEST) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8277 : decode code ⟨8277⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    exact uniswapV3PoolSetFeeProtocolDecodePatchedPush1 (pc := ⟨8277⟩) (n := ⟨0⟩)
      hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint2 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8279 : decode code ⟨8279⟩ = some (.DUP1, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8279⟩) (byte := 0x80)
      (op := .DUP1) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8280 : decode code ⟨8280⟩ = some (.SLOAD, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8280⟩) (byte := 0x54)
      (op := .SLOAD) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8281 : decode code ⟨8281⟩ = some (.Push .PUSH1, some (⟨255⟩, 1)) := by
    exact uniswapV3PoolSetFeeProtocolDecodePatchedPush1 (pc := ⟨8281⟩) (n := ⟨255⟩)
      hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint2 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8283 : decode code ⟨8283⟩ = some (.Push .PUSH1, some (⟨240⟩, 1)) := by
    exact uniswapV3PoolSetFeeProtocolDecodePatchedPush1 (pc := ⟨8283⟩) (n := ⟨240⟩)
      hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint2 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8285 : decode code ⟨8285⟩ = some (.SHL, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8285⟩) (byte := 0x1b)
      (op := .SHL) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8286 : decode code ⟨8286⟩ = some (.NOT, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8286⟩) (byte := 0x19)
      (op := .NOT) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8287 : decode code ⟨8287⟩ = some (.AND, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8287⟩) (byte := 0x16)
      (op := .AND) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8288 : decode code ⟨8288⟩ = some (.SWAP1, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8288⟩) (byte := 0x90)
      (op := .SWAP1) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8289 : decode code ⟨8289⟩ = some (.SSTORE, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8289⟩) (byte := 0x55)
      (op := .SSTORE) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have rd8209 : RD code ee g s0 ⟨8209⟩ R mem aw rdata (cA, σ) (k + 1) (C + 1) := by
    simpa using h.jumpdest
      hd8208
      (by evm_ov)
  have rd8211 : RD code ee g s0 ⟨8211⟩ (⟨0⟩ :: R) mem aw rdata (cA, σ)
      (k + 1 + 1) (C + 1 + 3) := by
    simpa using rd8209.push1 ⟨0⟩
      hd8209
      (by evm_ov)
  obtain ⟨_, _, rd8212₀⟩ := rd8211.sload
    hd8211
    (by evm_ov)
  have rd8212 := by
    simpa [solcSlotWord] using rd8212₀
  have rd8214 := by
    simpa using rd8212.push1 ⟨1⟩
      hd8212
      (by evm_ov)
  have rd8216 := by
    simpa using rd8214.push1 ⟨240⟩
      hd8214
      (by evm_ov)
  have rd8217 := by
    simpa [setFeeProtocolUnlockedShift] using rd8216.shl
      hd8216
      (by evm_ov)
  have rd8218 := by
    simpa using rd8217.swap1
      hd8217
      (by evm_ov)
  have rd8219 := by
    simpa using rd8218.div
      hd8218
      (by evm_ov)
  have rd8221 := by
    simpa [setFeeProtocolUint8Mask] using rd8219.push1 ⟨255⟩
      hd8219
      (by evm_ov)
  have rd8222 := by
    simpa [setFeeProtocolUnlockedByte] using rd8221.and
      hd8221
      (by evm_ov)
  have rd8225 := by
    simpa using rd8222.push2 ⟨8276⟩
      hd8222
      (by evm_ov)
  have rd8276 := rd8225.jumpiT
    hd8225
    hunlocked
    (uniswapV3PoolJumpDestPatched8276 hpatch)
    (by evm_ov)
  have rd8277 := by
    simpa using rd8276.jumpdest
      hd8276
      (by evm_ov)
  have rd8279 := by
    simpa using rd8277.push1 ⟨0⟩
      hd8277
      (by evm_ov)
  have rd8280 := by
    simpa using rd8279.dup1
      hd8279
      (by evm_ov)
  obtain ⟨_, _, rd8281₀⟩ := rd8280.sload
    hd8280
    (by evm_ov)
  have rd8281 := by
    simpa [solcSlotWord] using rd8281₀
  have rd8283 := by
    simpa [setFeeProtocolUint8Mask] using rd8281.push1 ⟨255⟩
      hd8281
      (by evm_ov)
  have rd8285 := by
    simpa using rd8283.push1 ⟨240⟩
      hd8283
      (by evm_ov)
  have rd8286 := by
    simpa using rd8285.shl
      hd8285
      (by evm_ov)
  have rd8287 := by
    simpa [setFeeProtocolUnlockedClearMask] using rd8286.not
      hd8286
      (by evm_ov)
  have rd8288 := by
    simpa [setFeeProtocolLockedSlotWord] using rd8287.and
      hd8287
      (by evm_ov)
  have rd8289 := by
    simpa using rd8288.swap1
      hd8288
      (by evm_ov)
  exact rd8289.sstore hperm
    hd8289
    (by evm_ov)

private theorem uniswapV3PoolSetFeeProtocolLockEnterLockedRevert {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨8208⟩ R solcFreePtrMem (UInt256.ofNat 3) rdata
      (cA, σ) k C)
    (hlocked : setFeeProtocolUnlockedByte σ ee = ⟨0⟩)
    (hov : R.length + 6 ≤ 1024) :
    RDrev code g s0 := by
  have hd8208 : decode code ⟨8208⟩ = some (.JUMPDEST, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8208⟩) (byte := 0x5b)
      (op := .JUMPDEST) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8209 : decode code ⟨8209⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    exact uniswapV3PoolSetFeeProtocolDecodePatchedPush1 (pc := ⟨8209⟩) (n := ⟨0⟩)
      hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint2 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8211 : decode code ⟨8211⟩ = some (.SLOAD, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8211⟩) (byte := 0x54)
      (op := .SLOAD) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8212 : decode code ⟨8212⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    exact uniswapV3PoolSetFeeProtocolDecodePatchedPush1 (pc := ⟨8212⟩) (n := ⟨1⟩)
      hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint2 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8214 : decode code ⟨8214⟩ = some (.Push .PUSH1, some (⟨240⟩, 1)) := by
    exact uniswapV3PoolSetFeeProtocolDecodePatchedPush1 (pc := ⟨8214⟩) (n := ⟨240⟩)
      hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint2 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8216 : decode code ⟨8216⟩ = some (.SHL, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8216⟩) (byte := 0x1b)
      (op := .SHL) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8217 : decode code ⟨8217⟩ = some (.SWAP1, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8217⟩) (byte := 0x90)
      (op := .SWAP1) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8218 : decode code ⟨8218⟩ = some (.DIV, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8218⟩) (byte := 0x04)
      (op := .DIV) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8219 : decode code ⟨8219⟩ = some (.Push .PUSH1, some (⟨255⟩, 1)) := by
    exact uniswapV3PoolSetFeeProtocolDecodePatchedPush1 (pc := ⟨8219⟩) (n := ⟨255⟩)
      hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint2 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8221 : decode code ⟨8221⟩ = some (.AND, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8221⟩) (byte := 0x16)
      (op := .AND) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8222 : decode code ⟨8222⟩ = some (.Push .PUSH2, some (⟨8276⟩, 2)) := by
    exact uniswapV3PoolSetFeeProtocolDecodePatchedPush2 (pc := ⟨8222⟩) (n := ⟨8276⟩)
      hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint3 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8225 : decode code ⟨8225⟩ = some (.JUMPI, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8225⟩) (byte := 0x57)
      (op := .JUMPI) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolPatchDisjoint1 (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have rd8209 : RD code ee g s0 ⟨8209⟩ R solcFreePtrMem (UInt256.ofNat 3) rdata
      (cA, σ) (k + 1) (C + 1) := by
    simpa using h.jumpdest
      hd8208
      (by evm_ov)
  have rd8211 : RD code ee g s0 ⟨8211⟩ (⟨0⟩ :: R) solcFreePtrMem
      (UInt256.ofNat 3) rdata (cA, σ) (k + 1 + 1) (C + 1 + 3) := by
    simpa using rd8209.push1 ⟨0⟩
      hd8209
      (by evm_ov)
  obtain ⟨_, _, rd8212₀⟩ := rd8211.sload
    hd8211
    (by evm_ov)
  have rd8212 := by
    simpa [solcSlotWord] using rd8212₀
  have rd8214 := by
    simpa using rd8212.push1 ⟨1⟩
      hd8212
      (by evm_ov)
  have rd8216 := by
    simpa using rd8214.push1 ⟨240⟩
      hd8214
      (by evm_ov)
  have rd8217 := by
    simpa [setFeeProtocolUnlockedShift] using rd8216.shl
      hd8216
      (by evm_ov)
  have rd8218 := by
    simpa using rd8217.swap1
      hd8217
      (by evm_ov)
  have rd8219 := by
    simpa using rd8218.div
      hd8218
      (by evm_ov)
  have rd8221 := by
    simpa [setFeeProtocolUint8Mask] using rd8219.push1 ⟨255⟩
      hd8219
      (by evm_ov)
  have rd8222 := by
    simpa [setFeeProtocolUnlockedByte] using rd8221.and
      hd8221
      (by evm_ov)
  have rd8225 := by
    simpa using rd8222.push2 ⟨8276⟩
      hd8222
      (by evm_ov)
  have rd8226 := rd8225.jumpiNT
    hd8225
    hlocked
    (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨8226⟩) (len := ⟨3⟩) (rawWord := ⟨5001035⟩) (shift := ⟨232⟩)
    (word := UInt256.shiftLeft ⟨5001035⟩ ⟨232⟩) (op := .PUSH3) (width := 3)
    rd8226
    (uniswapV3PoolSetFeeProtocolLockedRevertTailWf hpatch)
    (by native_decide)
    rfl
    solcFreePtrMem_size
    solcFreePtrMem_read64
    (by omega)

private theorem uniswapV3PoolSetFeeProtocolEvmAfterLock {v : PoolImmutables}
    {code : ByteArray} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hsel : (uniswapV3PoolSelBytes 14 == I.calldata.extract 0 4) = true)
    (hsz68 : 68 ≤ I.calldata.size)
    (hunlocked : setFeeProtocolUnlockedByte σ I ≠ ⟨0⟩) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨8290⟩
      (setFeeProtocolArg1Word I :: setFeeProtocolArg0Word I :: ⟨857⟩ ::
        [solcSelectorWord I])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ (setFeeProtocolLockedSlotWord σ I)) k C := by
  have hreach := uniswapV3PoolSetFeeProtocolReachEntry
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize hsel
  obtain ⟨_, _, rdDecoded⟩ :=
    uniswapV3PoolSetFeeProtocolExternalLenOk hpatch hreach hsz68 hsize
  obtain ⟨_, _, rdRoutine⟩ :=
    uniswapV3PoolSetFeeProtocolDecodedReachRoutine hpatch rdDecoded
      (by simp only [List.length_singleton]; omega)
  exact uniswapV3PoolSetFeeProtocolLockEnterOk hpatch rdRoutine hperm hunlocked
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem uniswapV3PoolSetFeeProtocolEvmLocked {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 14 == I.calldata.extract 0 4) = true)
    (hsz68 : 68 ≤ I.calldata.size)
    (hlocked : setFeeProtocolUnlockedByte σ I = ⟨0⟩) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  have hreach := uniswapV3PoolSetFeeProtocolReachEntry
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize hsel
  obtain ⟨_, _, rdDecoded⟩ :=
    uniswapV3PoolSetFeeProtocolExternalLenOk hpatch hreach hsz68 hsize
  obtain ⟨_, _, rdRoutine⟩ :=
    uniswapV3PoolSetFeeProtocolDecodedReachRoutine hpatch rdDecoded
      (by simp only [List.length_singleton]; omega)
  exact uniswapV3PoolSetFeeProtocolLockEnterLockedRevert hpatch rdRoutine hlocked
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem uniswapV3PoolSetFeeProtocolEvmDecodeShort {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 14 == I.calldata.extract 0 4) = true)
    (hshort : I.calldata.size < 68) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  have hreach := uniswapV3PoolSetFeeProtocolReachEntry
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize hsel
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by
      rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      omega) hsize]
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
    rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]
    omega
  exact RD.solcExternalStaticArgsShortReverts (need := ⟨64⟩)
    (entry := ⟨1486⟩) (ret := ⟨857⟩) (decoded := ⟨1508⟩) hreach
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

theorem uniswapV3PoolSetFeeProtocolBodyCore {v : PoolImmutables}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsel : (uniswapV3PoolSelBytes 14 == I.calldata.extract 0 4) = true) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdispatch := uniswapV3PoolDispatch_setFeeProtocol (v := v) (cd := I.calldata) hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · have hdecode := uniswapV3PoolSetFeeProtocolDecodeOk (v := v) (I := I) hsz68
    by_cases hunlocked : setFeeProtocolUnlockedByte σ_evm I ≠ ⟨0⟩
    · obtain ⟨kLock, CLock, hrdAfterLock⟩ :=
        uniswapV3PoolSetFeeProtocolEvmAfterLock (v := v) (code := code)
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hpatch hcode hwv hsz hsize _hperm hsel
        hsz68 hunlocked
      have hunlockedSolm : setFeeProtocolUnlockedByte σ_solm I ≠ ⟨0⟩ := by
        rw [setFeeProtocolUnlockedByte_transport (σ_evm := σ_evm) (σ_solm := σ_solm)
          hAccounts]
        exact hunlocked
      have hsourceLock := uniswapV3PoolSetFeeProtocolSourceLockPrefixExact (v := v)
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hwv hunlockedSolm
      have hlockedWord :
          setFeeProtocolLockedSlotWord σ_solm I =
            setFeeProtocolLockedSlotWord σ_evm I :=
        setFeeProtocolLockedSlotWord_transport (σ_evm := σ_evm) (σ_solm := σ_solm)
          hAccounts
      have hAccountsAfterLock :
          accountMapEquiv
            (sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
              (setFeeProtocolLockedSlotWord σ_evm I))
            (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
              (setFeeProtocolLockedSlotWord σ_solm I)) := by
        rw [hlockedWord]
        exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩
          (setFeeProtocolLockedSlotWord σ_evm I) hAccounts
      obtain ⟨kOwnerSetup, COwnerSetup, hrdOwnerSetup⟩ :=
        uniswapV3PoolSetFeeProtocolOwnerCallSetup (v := v) (code := code)
          (ee := I) (g := Sat256.ofUInt256 g)
          (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          (R := [setFeeProtocolArg1Word I, setFeeProtocolArg0Word I, ⟨857⟩,
            solcSelectorWord I])
          (rdata := ByteArray.empty) (cA := cA)
          (σ := sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
            (setFeeProtocolLockedSlotWord σ_evm I))
          hpatch hrdAfterLock
          (by simp only [List.length_cons, List.length_nil]; omega)
      obtain ⟨kOwnerGuard, COwnerGuard, hrdOwnerGuard⟩ :=
        uniswapV3PoolSetFeeProtocolOwnerCallGuardSetup (v := v) (code := code)
          (ee := I) (g := Sat256.ofUInt256 g)
          (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          (R := [setFeeProtocolArg1Word I, setFeeProtocolArg0Word I, ⟨857⟩,
            solcSelectorWord I])
          (rdata := ByteArray.empty) (cA := cA)
          (σ := sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
            (setFeeProtocolLockedSlotWord σ_evm I))
          hpatch hrdOwnerSetup
          (by simp only [List.length_cons, List.length_nil]; omega)
      by_cases hfactoryCode :
          Reasoning.Theory.extCodeSizeWord
              (sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
                (setFeeProtocolLockedSlotWord σ_evm I))
              (setFeeProtocolFactoryWord v) ≠ ⟨0⟩
      · have hfactoryCodeSolm :
            Reasoning.Theory.extCodeSizeWord
                (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
                  (setFeeProtocolLockedSlotWord σ_solm I))
                (setFeeProtocolFactoryWord v) ≠ ⟨0⟩ := by
          rw [← extCodeSizeWord_accountMapEquiv hAccountsAfterLock
            (setFeeProtocolFactoryWord v)]
          exact hfactoryCode
        let evmLockSolm :=
          initState cA gh bl
            (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
              (setFeeProtocolLockedSlotWord σ_solm I)) σ₀ (Sat256.ofUInt256 g) A I
        have hfactoryGuardSolm :
            evalExpr? (config v) { contract := contract v, locals := setFeeProtocolStore I }
              evmLockSolm
              (.binary .gt (.extCodeSize (addrLit v.factory)) (.intLit 0)) =
                .ok (.bool true) := by
          exact evalExpr_setFeeProtocol_factoryExtCodeSizeGuard_true (v := v)
            (evm := evmLockSolm) (I := I) (by simpa [evmLockSolm, initState])
        by_cases hdepth : I.depth.val < 1024
        · obtain ⟨cAOwner, σOwnerEvm, zOwner, oOwner, AOwnerEvm,
              kOwnerCall, COwnerCall, hrdOwnerCall, hcallOwnerEvm, hoOwnerSize⟩ :=
            uniswapV3PoolSetFeeProtocolOwnerTypedStaticcallMade (v := v) (code := code)
              (cA := cA) (gh := gh) (bl := bl)
              (σ := sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
                (setFeeProtocolLockedSlotWord σ_evm I))
              (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (R := [setFeeProtocolArg1Word I, setFeeProtocolArg0Word I, ⟨857⟩,
                solcSelectorWord I])
              (rdata := ByteArray.empty) hpatch (by rfl) (by rfl) (by rfl)
              hrdOwnerGuard hfactoryCode hdepth
              (by simp only [List.length_cons, List.length_nil]; omega)
          obtain ⟨σOwnerSolm, AOwnerSolm, hcallOwnerSolm, hAccountsOwner⟩ :=
            typedCallViaEVM_initState_accountMapEquiv (hcall := hcallOwnerEvm)
              hAccountsAfterLock
          obtain ⟨hOwnerStatusOk, hOwnerStatusRevert⟩ :=
            uniswapV3PoolSetFeeProtocolOwnerStaticcallStatusGuard (v := v) (code := code)
              (ee := I) (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (R := [setFeeProtocolArg1Word I, setFeeProtocolArg0Word I, ⟨857⟩,
                solcSelectorWord I])
              (o := oOwner) (mem := setFeeProtocolOwnerStaticcallMem oOwner)
              (aw := setFeeProtocolOwnerStaticcallActiveWords) (acc := (cAOwner, σOwnerEvm))
              hpatch hrdOwnerCall hoOwnerSize
              (by simp only [List.length_cons, List.length_nil]; omega)
          by_cases hzOwner : zOwner = true
          · obtain ⟨kOwnerStatus, COwnerStatus, hrdOwnerStatus⟩ :=
              hOwnerStatusOk hzOwner
            by_cases hownerShort : oOwner.size < 32
            · have hrdOwnerDecodeShort :=
                uniswapV3PoolSetFeeProtocolOwnerReturnDecodeShortReverts (v := v)
                  (code := code) (ee := I) (g := Sat256.ofUInt256 g)
                  (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                  (R := [setFeeProtocolArg1Word I, setFeeProtocolArg0Word I, ⟨857⟩,
                    solcSelectorWord I])
                  (o := oOwner) (acc := (cAOwner, σOwnerEvm))
                  hpatch hrdOwnerStatus hownerShort hoOwnerSize
                  (by simp only [List.length_cons, List.length_nil]; omega)
              have hcallOwnerSolmTrue :
                  typedCallViaEVM (config v)
                    (initState cA gh bl
                      (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
                        (setFeeProtocolLockedSlotWord σ_solm I)) σ₀ (Sat256.ofUInt256 g) A I)
                    (EVM.address (AccountAddress.ofNat v.factory.toNat)) "owner" 0 []
                    (true, { initState cA gh bl
                        (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
                          (setFeeProtocolLockedSlotWord σ_solm I)) σ₀
                        (Sat256.ofUInt256 g) A I with
                        accountMap := σOwnerSolm
                        substate := AOwnerSolm
                        createdAccounts := cAOwner }, oOwner) false := by
                simpa [hzOwner] using hcallOwnerSolm
              have hownerRevert :=
                uniswapV3PoolSetFeeProtocolSourceOwnerCallDecodeRevert (v := v)
                  (evm := evmLockSolm)
                  (evm' := { evmLockSolm with
                    accountMap := σOwnerSolm
                    substate := AOwnerSolm
                    createdAccounts := cAOwner })
                  (I := I) (out := oOwner) hfactoryGuardSolm
                  (by simpa [evmLockSolm] using hcallOwnerSolmTrue)
                  (setFeeProtocolOwnerDecodeNoneShort (v := v) hownerShort)
              have hbody :=
                uniswapV3PoolSetFeeProtocolSourceOwnerCallRevertBody (v := v)
                  (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                  (A := A) (I := I) (g := Sat256.ofUInt256 g) hwv hunlockedSolm
                  hownerRevert
              exact hrdOwnerDecodeShort.reEquivExecutionRevert hcode hdispatch hdecode hbody
            · have hownerSize32 : 32 ≤ oOwner.size := Nat.le_of_not_gt hownerShort
              obtain ⟨kOwnerDecode, COwnerDecode, hrdOwnerDecode⟩ :=
                uniswapV3PoolSetFeeProtocolOwnerReturnDecodeOk (v := v) (code := code)
                  (ee := I) (g := Sat256.ofUInt256 g)
                  (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                  (R := [setFeeProtocolArg1Word I, setFeeProtocolArg0Word I, ⟨857⟩,
                    solcSelectorWord I])
                  (o := oOwner) (acc := (cAOwner, σOwnerEvm))
                  hpatch hrdOwnerStatus hownerSize32 hoOwnerSize
                  (by simp only [List.length_cons, List.length_nil]; omega)
              have hcallOwnerSolmTrue :
                  typedCallViaEVM (config v)
                    (initState cA gh bl
                      (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
                        (setFeeProtocolLockedSlotWord σ_solm I)) σ₀ (Sat256.ofUInt256 g) A I)
                    (EVM.address (AccountAddress.ofNat v.factory.toNat)) "owner" 0 []
                    (true, { initState cA gh bl
                        (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
                          (setFeeProtocolLockedSlotWord σ_solm I)) σ₀
                        (Sat256.ofUInt256 g) A I with
                        accountMap := σOwnerSolm
                        substate := AOwnerSolm
                        createdAccounts := cAOwner }, oOwner) false := by
                simpa [hzOwner] using hcallOwnerSolm
              have hownerCallOk :=
                uniswapV3PoolSetFeeProtocolSourceOwnerCallSuccess (v := v)
                  (evm := evmLockSolm)
                  (evm' := { evmLockSolm with
                    accountMap := σOwnerSolm
                    substate := AOwnerSolm
                    createdAccounts := cAOwner })
                  (I := I) (out := oOwner)
                  (value := [Value.address
                    (AccountAddress.ofNat
                      (UInt256.ofNat (fromByteArrayBigEndian (oOwner.extract 0 32))).toNat)])
                  hfactoryGuardSolm
                  (by simpa [evmLockSolm] using hcallOwnerSolmTrue)
                  (setFeeProtocolOwnerDecodeOk (v := v) hownerSize32)
              by_cases hownerCaller :
                  UInt256.land solcAddrMask (setFeeProtocolOwnerWord oOwner) = solcSourceWord I
              · obtain ⟨kOwnerCaller, COwnerCaller, hrdOwnerCaller⟩ :=
                  uniswapV3PoolSetFeeProtocolOwnerCallerGuardOk (v := v) (code := code)
                    (ee := I) (g := Sat256.ofUInt256 g)
                    (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                    (R := [setFeeProtocolArg1Word I, setFeeProtocolArg0Word I, ⟨857⟩,
                      solcSelectorWord I])
                    (owner := setFeeProtocolOwnerWord oOwner)
                    (mem := setFeeProtocolOwnerStaticcallMem oOwner)
                    (aw := setFeeProtocolOwnerStaticcallActiveWords) (rdata := oOwner)
                    (acc := (cAOwner, σOwnerEvm)) hpatch
                    (by simpa [setFeeProtocolOwnerWord] using hrdOwnerDecode)
                    hownerCaller
                    (by simp only [List.length_cons, List.length_nil]; omega)
                have hownerAddress :
                    setFeeProtocolOwnerAddress oOwner =
                      ({ evmLockSolm with
                        accountMap := σOwnerSolm
                        substate := AOwnerSolm
                        createdAccounts := cAOwner }).executionEnv.source := by
                  have haddr :=
                    setFeeProtocolOwnerAddress_eq_source_of_mask_eq
                      (out := oOwner) (I := I) hownerCaller
                  simpa [evmLockSolm, initState] using haddr
                have hownerRequireOk :=
                  uniswapV3PoolSetFeeProtocolSourceOwnerRequireSuccessPrefixExact (v := v)
                    (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                    (A := A) (I := I) (g := Sat256.ofUInt256 g)
                    (evmOwner := { evmLockSolm with
                      accountMap := σOwnerSolm
                      substate := AOwnerSolm
                      createdAccounts := cAOwner })
                    (out := oOwner) hwv hunlockedSolm
                    (by
                      simpa [evmLockSolm, setFeeProtocolStoreWithOwner,
                        setFeeProtocolOwnerAddress, setFeeProtocolOwnerWord] using hownerCallOk)
                    hownerAddress
                by_cases hfee :
                    setFeeProtocolEnabledNat (setFeeProtocolArg0Word I).toNat ∧
                      setFeeProtocolEnabledNat (setFeeProtocolArg1Word I).toNat
                · obtain ⟨hfee0, hfee1⟩ := hfee
                  obtain ⟨kFee, CFee, hrdFee⟩ :=
                    uniswapV3PoolSetFeeProtocolFeeProtocolGuardsOk (v := v) (code := code)
                      (ee := I) (g := Sat256.ofUInt256 g)
                      (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                      (R := [⟨857⟩, solcSelectorWord I])
                      (mem := setFeeProtocolOwnerStaticcallMem oOwner)
                      (aw := setFeeProtocolOwnerStaticcallActiveWords) (rdata := oOwner)
                      (acc := (cAOwner, σOwnerEvm)) hpatch hrdOwnerCaller hfee0 hfee1
                      (by simp only [List.length_cons, List.length_nil]; omega)
                  have hfeeRequireOk :=
                    uniswapV3PoolSetFeeProtocolSourceFeeProtocolRequireSuccessPrefixExact (v := v)
                      (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                      (A := A) (I := I) (g := Sat256.ofUInt256 g)
                      (evmOwner := { evmLockSolm with
                        accountMap := σOwnerSolm
                        substate := AOwnerSolm
                        createdAccounts := cAOwner })
                      (out := oOwner) hownerRequireOk hfee0 hfee1
                  have hbody :=
                    uniswapV3PoolSetFeeProtocolSourceSuccessBody (v := v)
                      (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                      (A := A) (I := I) (g := Sat256.ofUInt256 g)
                      (evmOwner := { evmLockSolm with
                        accountMap := σOwnerSolm
                        substate := AOwnerSolm
                        createdAccounts := cAOwner })
                      (out := oOwner) hfeeRequireOk
                  obtain ⟨kStore, CStore, hrdStore⟩ :=
                    uniswapV3PoolSetFeeProtocolFeeProtocolStoreEvm (v := v) (code := code)
                      (ee := I) (g := Sat256.ofUInt256 g)
                      (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                      (R := [⟨857⟩, solcSelectorWord I])
                      (mem := setFeeProtocolOwnerStaticcallMem oOwner)
                      (aw := setFeeProtocolOwnerStaticcallActiveWords) (rdata := oOwner)
                      (cA := cAOwner) (σ := σOwnerEvm) hpatch hrdFee _hperm
                      (by simp only [List.length_cons, List.length_nil]; omega)
                  obtain ⟨kEvent, CEvent, hrdEvent⟩ :=
                    uniswapV3PoolSetFeeProtocolEventLogEvm (v := v) (code := code)
                      (ee := I) (g := Sat256.ofUInt256 g)
                      (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                      (R := [⟨857⟩, solcSelectorWord I]) (out := oOwner)
                      (rdata := oOwner) (cA := cAOwner)
                      (σ := sstoreAccountMap I.codeOwner σOwnerEvm ⟨0⟩
                        (setFeeProtocolEvmFeeProtocolSlotWord σOwnerEvm I))
                      (oldSlot := codeOwnerStorageWord I σOwnerEvm ⟨0⟩)
                      hpatch hrdStore _hperm hownerSize32 hoOwnerSize
                      (by simp only [List.length_cons, List.length_nil]; omega)
                  have hrdSuccess :=
                    uniswapV3PoolSetFeeProtocolUnlockReturnEvm (v := v) (code := code)
                      (ee := I) (g := Sat256.ofUInt256 g)
                      (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                      (R := [solcSelectorWord I])
                      (mem := setFeeProtocolEventMem
                        (codeOwnerStorageWord I σOwnerEvm ⟨0⟩) I oOwner)
                      (aw := UInt256.ofNat 8) (rdata := oOwner)
                      (cA := cAOwner)
                      (σ := sstoreAccountMap I.codeOwner σOwnerEvm ⟨0⟩
                        (setFeeProtocolEvmFeeProtocolSlotWord σOwnerEvm I))
                      (oldFeeProtocol := setFeeProtocolEventOldFeeProtocolWord
                        (codeOwnerStorageWord I σOwnerEvm ⟨0⟩))
                      hpatch hrdEvent _hperm
                      (by simp only [List.length_cons, List.length_nil]; omega)
                  exact hrdSuccess.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
                    (by
                      simp [setFeeProtocolAfterUnlockState, setFeeProtocolAfterFeeProtocolState,
                        storageStore_createdAccounts])
                    (by
                      exact setFeeProtocolFinalAccountMapEquiv
                        (evmOwner := { evmLockSolm with
                          accountMap := σOwnerSolm
                          substate := AOwnerSolm
                          createdAccounts := cAOwner })
                        (σOwnerEvm := σOwnerEvm) (I := I)
                        (by simpa using hAccountsOwner)
                        (by simp [evmLockSolm, initState])
                        hfee0 hfee1)
                    (by
                      rw [show (setfeeprotocolTransition v).returnType = [] from rfl]
                      exact returnEquiv.fallthrough rfl rfl (by native_decide))
                · have hrdFeeRevert :=
                    uniswapV3PoolSetFeeProtocolFeeProtocolGuardsRevert (v := v) (code := code)
                      (ee := I) (g := Sat256.ofUInt256 g)
                      (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                      (R := [⟨857⟩, solcSelectorWord I])
                      (mem := setFeeProtocolOwnerStaticcallMem oOwner)
                      (aw := setFeeProtocolOwnerStaticcallActiveWords) (rdata := oOwner)
                      (acc := (cAOwner, σOwnerEvm)) hpatch hrdOwnerCaller hfee
                      (by simp only [List.length_cons, List.length_nil]; omega)
                  have hbody :=
                    uniswapV3PoolSetFeeProtocolSourceFeeProtocolRequireRevertBody (v := v)
                      (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                      (A := A) (I := I) (g := Sat256.ofUInt256 g)
                      (evmOwner := { evmLockSolm with
                        accountMap := σOwnerSolm
                        substate := AOwnerSolm
                        createdAccounts := cAOwner })
                      (out := oOwner) hownerRequireOk hfee
                  exact hrdFeeRevert.reEquivExecutionRevert hcode hdispatch hdecode hbody
              · have hrdOwnerCallerRevert :=
                  uniswapV3PoolSetFeeProtocolOwnerCallerGuardReverts (v := v) (code := code)
                    (ee := I) (g := Sat256.ofUInt256 g)
                    (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                    (R := [setFeeProtocolArg1Word I, setFeeProtocolArg0Word I, ⟨857⟩,
                      solcSelectorWord I])
                    (owner := setFeeProtocolOwnerWord oOwner)
                    (mem := setFeeProtocolOwnerStaticcallMem oOwner)
                    (aw := setFeeProtocolOwnerStaticcallActiveWords) (rdata := oOwner)
                    (acc := (cAOwner, σOwnerEvm)) hpatch
                    (by simpa [setFeeProtocolOwnerWord] using hrdOwnerDecode)
                    hownerCaller
                    (by simp only [List.length_cons, List.length_nil]; omega)
                have hownerAddressNe :
                    setFeeProtocolOwnerAddress oOwner ≠
                      ({ evmLockSolm with
                        accountMap := σOwnerSolm
                        substate := AOwnerSolm
                        createdAccounts := cAOwner }).executionEnv.source := by
                  have hne :=
                    setFeeProtocolOwnerAddress_ne_source_of_mask_ne
                      (out := oOwner) (I := I) hownerCaller
                  simpa [evmLockSolm, initState] using hne
                have hbody :=
                  uniswapV3PoolSetFeeProtocolSourceOwnerRequireRevertBody (v := v)
                    (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                    (A := A) (I := I) (g := Sat256.ofUInt256 g)
                    (evmOwner := { evmLockSolm with
                      accountMap := σOwnerSolm
                      substate := AOwnerSolm
                      createdAccounts := cAOwner })
                    (out := oOwner) hwv hunlockedSolm
                    (by
                      simpa [evmLockSolm, setFeeProtocolStoreWithOwner,
                        setFeeProtocolOwnerAddress, setFeeProtocolOwnerWord] using hownerCallOk)
                    hownerAddressNe
                exact hrdOwnerCallerRevert.reEquivExecutionRevert hcode hdispatch hdecode hbody
          · have hzOwnerFalse : zOwner = false := by
              cases zOwner <;> simp at hzOwner ⊢
            have hrdOwnerRevert := hOwnerStatusRevert hzOwnerFalse
            have hcallOwnerSolmFalse :
                typedCallViaEVM (config v)
                  (initState cA gh bl
                    (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
                      (setFeeProtocolLockedSlotWord σ_solm I)) σ₀ (Sat256.ofUInt256 g) A I)
                  (EVM.address (AccountAddress.ofNat v.factory.toNat)) "owner" 0 []
                  (false, { initState cA gh bl
                      (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
                        (setFeeProtocolLockedSlotWord σ_solm I)) σ₀ (Sat256.ofUInt256 g) A I with
                      accountMap := σOwnerSolm
                      substate := AOwnerSolm
                      createdAccounts := cAOwner }, oOwner) false := by
              simpa [hzOwnerFalse] using hcallOwnerSolm
            have hownerRevert :=
              uniswapV3PoolSetFeeProtocolSourceOwnerCallFailure (v := v)
                (evm := evmLockSolm)
                (evm' := { evmLockSolm with
                  accountMap := σOwnerSolm
                  substate := AOwnerSolm
                  createdAccounts := cAOwner })
                (I := I) (out := oOwner) hfactoryGuardSolm
                (by simpa [evmLockSolm] using hcallOwnerSolmFalse)
            have hbody :=
              uniswapV3PoolSetFeeProtocolSourceOwnerCallRevertBody (v := v)
                (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                (A := A) (I := I) (g := Sat256.ofUInt256 g) hwv hunlockedSolm
                hownerRevert
            exact hrdOwnerRevert.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · have hdepthEq : I.depth = (1024 : Fin 1025) := by
            apply Fin.ext
            have hle : 1024 ≤ I.depth.val := Nat.le_of_not_gt hdepth
            exact le_antisymm (Nat.le_of_lt_succ I.depth.isLt) hle
          have hrdOwnerDepth :=
            uniswapV3PoolSetFeeProtocolOwnerStaticcallDepthLimitReverts (v := v) (code := code)
              (ee := I) (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (R := [setFeeProtocolArg1Word I, setFeeProtocolArg0Word I, ⟨857⟩,
                solcSelectorWord I])
              (rdata := ByteArray.empty) (cA := cA)
              (σ := sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
                (setFeeProtocolLockedSlotWord σ_evm I))
              hpatch hrdOwnerGuard hfactoryCode hdepthEq
              (by simp only [List.length_cons, List.length_nil]; omega)
          have hcallOwnerDepth :
              typedCallViaEVM (config v) evmLockSolm
                (EVM.address (AccountAddress.ofNat v.factory.toNat)) "owner" 0 []
                (false,
                  { evmLockSolm with
                    substate :=
                      (evmLockSolm.addAccessedAccount
                        (EVM.address (AccountAddress.ofNat v.factory.toNat))).substate },
                  ByteArray.empty) false := by
            exact callNotMade_depthLimit (cfg := config v) (evm := evmLockSolm)
              (tgt := EVM.address (AccountAddress.ofNat v.factory.toNat))
              (name := "owner") (args := []) (callPerm := false)
              (setFeeProtocolOwnerCallMem_encode_owner (v := v))
              (by simpa [evmLockSolm, initState] using hdepthEq)
          have hownerRevert :=
            uniswapV3PoolSetFeeProtocolSourceOwnerCallFailure (v := v)
              (evm := evmLockSolm)
              (evm' := { evmLockSolm with
                substate :=
                  (evmLockSolm.addAccessedAccount
                    (EVM.address (AccountAddress.ofNat v.factory.toNat))).substate })
              (I := I) (out := ByteArray.empty) hfactoryGuardSolm hcallOwnerDepth
          have hbody :=
            uniswapV3PoolSetFeeProtocolSourceOwnerCallRevertBody (v := v)
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
              (A := A) (I := I) (g := Sat256.ofUInt256 g) hwv hunlockedSolm
              hownerRevert
          exact hrdOwnerDepth.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hfactoryNoCodeEvm :
            Reasoning.Theory.extCodeSizeWord
                (sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
                  (setFeeProtocolLockedSlotWord σ_evm I))
                (setFeeProtocolFactoryWord v) = ⟨0⟩ := by
          by_contra hne
          exact hfactoryCode hne
        have hrdOwnerNoCode :=
          uniswapV3PoolSetFeeProtocolOwnerExtcodesizeMissingReverts (v := v) (code := code)
            (ee := I) (g := Sat256.ofUInt256 g)
            (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
            (R := [setFeeProtocolArg1Word I, setFeeProtocolArg0Word I, ⟨857⟩,
              solcSelectorWord I])
            (rdata := ByteArray.empty) (cA := cA)
            (σ := sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
              (setFeeProtocolLockedSlotWord σ_evm I))
            hpatch hrdOwnerGuard hfactoryNoCodeEvm
            (by simp only [List.length_cons, List.length_nil]; omega)
        have hfactoryNoCodeSolm :
            Reasoning.Theory.extCodeSizeWord
                (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
                  (setFeeProtocolLockedSlotWord σ_solm I))
                (setFeeProtocolFactoryWord v) = ⟨0⟩ := by
          rw [← extCodeSizeWord_accountMapEquiv hAccountsAfterLock
            (setFeeProtocolFactoryWord v)]
          exact hfactoryNoCodeEvm
        let evmLockSolm :=
          initState cA gh bl
            (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
              (setFeeProtocolLockedSlotWord σ_solm I)) σ₀ (Sat256.ofUInt256 g) A I
        have hfactoryGuardNoCodeSolm :
            evalExpr? (config v) { contract := contract v, locals := setFeeProtocolStore I }
              evmLockSolm
              (.binary .gt (.extCodeSize (addrLit v.factory)) (.intLit 0)) =
                .ok (.bool false) := by
          exact evalExpr_setFeeProtocol_factoryExtCodeSizeGuard_false (v := v)
            (evm := evmLockSolm) (I := I) (by simpa [evmLockSolm, initState])
        have hownerRevert :
            ExecBlock (config v) { contract := contract v, locals := setFeeProtocolStore I }
              evmLockSolm
              [ .require (.binary .gt (.extCodeSize (addrLit v.factory)) (.intLit 0)),
                .externalCall (addrLit v.factory) "owner" (.intLit 0) [] "_factoryOwner"
                  (perm := false) ]
              .reverted := by
          exact checkedExternalCallNoCode (receiver := addrLit v.factory) (name := "owner")
            (sendVal := 0) (args := []) (retVar := "_factoryOwner")
            (perm := false) hfactoryGuardNoCodeSolm
        have hbody :=
          uniswapV3PoolSetFeeProtocolSourceOwnerCallRevertBody (v := v)
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
            (A := A) (I := I) (g := Sat256.ofUInt256 g) hwv hunlockedSolm hownerRevert
        exact hrdOwnerNoCode.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hlockedEvm : setFeeProtocolUnlockedByte σ_evm I = ⟨0⟩ := by
        by_contra hne
        exact hunlocked hne
      have hlockedSolm : setFeeProtocolUnlockedByte σ_solm I = ⟨0⟩ := by
        rw [setFeeProtocolUnlockedByte_transport (σ_evm := σ_evm) (σ_solm := σ_solm)
          hAccounts]
        exact hlockedEvm
      have hbody := uniswapV3PoolSetFeeProtocolSourceLockedReverts (v := v)
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hwv hlockedSolm
      have hrd := uniswapV3PoolSetFeeProtocolEvmLocked (v := v) (code := code)
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hpatch hcode hwv hsz hsize hsel hsz68
        hlockedEvm
      exact hrd.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hshort : I.calldata.size < 68 := by omega
    have hdecode := uniswapV3PoolSetFeeProtocolDecodeShort (v := v) (I := I) hshort
    have hrd := uniswapV3PoolSetFeeProtocolEvmDecodeShort (v := v) (code := code)
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) hpatch hcode hwv hsz hsize hsel hshort
    exact hrd.reEquivDecodingFailed hcode hdispatch hdecode

end Benchmarks.UniswapV3Pool
