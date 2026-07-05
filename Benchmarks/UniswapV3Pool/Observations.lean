import Benchmarks.UniswapV3Pool.ObservationsInt56
import Reasoning.MemCascade

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.UniswapV3Pool

abbrev observationsArgWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev observationsArgValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (observationsArgWord I).toNat)

abbrev observationsArgKey (I : ExecutionEnv) : KeyValue :=
  .int (Int.ofNat (observationsArgWord I).toNat)

abbrev observationsStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "arg0" (observationsArgValue I)

abbrev observationsBaseSlot (I : ExecutionEnv) : UInt256 :=
  observationBase (observationsArgKey I)

theorem observationsArgAddBase_eq_baseSlot (I : ExecutionEnv) :
    observationsArgWord I + ⟨8⟩ = observationsBaseSlot I := by
  unfold observationsBaseSlot observationsArgKey observationBase
  rw [keyValueToWord_uint256]
  rw [u256_ofNat_toNat]
  rw [u256_add_comm]

abbrev observationsSlotWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (observationsBaseSlot I)

abbrev observationsShiftBytes (n : Nat) : UInt256 :=
  UInt256.ofNat (256 ^ n)

abbrev observationsUint32Mask : UInt256 :=
  UInt256.ofNat (2 ^ 32 - 1)

theorem observationsUint32Mask_toNat :
    observationsUint32Mask.toNat = 2 ^ 32 - 1 := by
  exact ulit_toNat' _ (by norm_num [UInt256.size])

theorem observationsUint32Mask_bound (w : UInt256) :
    (UInt256.land w observationsUint32Mask).toNat < EVM.twoPow 32 := by
  rw [uland_toNat]
  rw [observationsUint32Mask_toNat]
  exact lt_of_le_of_lt (nat_land_le_right _ _) (by norm_num [EVM.twoPow])

theorem observationsUint32Mask_clean {w : UInt256} (hcanon : w.toNat < EVM.twoPow 32) :
    UInt256.land w observationsUint32Mask = w := by
  apply u256_inj
  show Nat.land w.toNat observationsUint32Mask.toNat % EVM.twoPow 256 = w.toNat
  rw [observationsUint32Mask_toNat, nat_land_mask_eq_mod]
  rw [show EVM.twoPow 32 = 2 ^ 32 from rfl] at hcanon
  rw [Nat.mod_eq_of_lt hcanon]
  exact Nat.mod_eq_of_lt w.val.isLt

abbrev observationsBlockTimestampWord (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  UInt256.land (observationsSlotWord σ I) observationsUint32Mask

abbrev observationsTickRawWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.div (observationsSlotWord σ I) (observationsShiftBytes 4)

abbrev observationsTickStorageWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (observationsTickRawWord σ I) observationsUint56Mask

abbrev observationsTickReturnWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.signextend ⟨6⟩ (observationsTickRawWord σ I)

abbrev observationsSecondsPerLiquidityWord (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  UInt256.land (UInt256.div (observationsSlotWord σ I) (observationsShiftBytes 11))
    slot0Uint160Mask

abbrev observationsInitializedRawWord (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  UInt256.land (UInt256.div (observationsSlotWord σ I) (observationsShiftBytes 31))
    slot0Uint8Mask

abbrev observationsInitializedReturnWord (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  slot0BoolReturnWord (observationsInitializedRawWord σ I)

abbrev observationsReturnValues (σ : AccountMap) (I : ExecutionEnv) : List Value :=
  [ .int (Int.ofNat (observationsBlockTimestampWord σ I).toNat),
    wordToElem (.int int56Int) (observationsTickStorageWord σ I),
    .int (Int.ofNat (observationsSecondsPerLiquidityWord σ I).toNat),
    wordToElem .bool (observationsInitializedRawWord σ I) ]

theorem observationsStore_arg0 (I : ExecutionEnv) :
    Std.HashMap.get? (observationsStore I) "arg0" = some (observationsArgValue I) := by
  simp [observationsStore]

theorem evalExpr_observations_arg0 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := observationsStore I } evm
      (.var "arg0") = .ok (observationsArgValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [observationsStore_arg0]

def observationsEvaledRef (I : ExecutionEnv) (field : Ident) : EvaledStorageRef :=
  { base := "observations", steps := [.aindex (observationsArgKey I), .field field] }

def observationsRawEvaledRef (I : ExecutionEnv) (field : Ident) : EvaledStorageRef :=
  { base := "observationsRaw", steps := [.mindex (observationsArgKey I), .field field] }

theorem evalStorageRef_observationsRaw {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) (field : Ident) :
    evalStorageRef (config v) { contract := contract v, locals := observationsStore I } evm
      (observationsRawF (.var "arg0") field) =
        .ok (observationsRawEvaledRef I field) := by
  simp [evalStorageRef, evalStorageRefStep, evalStorageRefSteps, observationsRawF,
    observationsRawEvaledRef, evalExpr_observations_arg0, observationsArgValue,
    observationsArgKey, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem evalExpr_observations_bound_true {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) (hbound : (observationsArgWord I).toNat < 65535) :
    evalExpr? (config v) { contract := contract v, locals := observationsStore I } evm
      (ltE (.var "arg0") (.intLit 65535)) = .ok (.bool true) := by
  unfold ltE
  simp only [evalExpr?, evalExpr_observations_arg0, observationsArgValue,
    EvalResult.bind, bind, pure, evalBinaryOp?]
  have hlt : Int.ofNat (observationsArgWord I).toNat < (65535 : Int) := by
    change ((observationsArgWord I).toNat : Int) < (65535 : Int)
    exact_mod_cast hbound
  rw [show decide (Int.ofNat (observationsArgWord I).toNat < 65535) = true from
    decide_eq_true hlt]

theorem evalExpr_observations_bound_false {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) (hoob : 65535 ≤ (observationsArgWord I).toNat) :
    evalExpr? (config v) { contract := contract v, locals := observationsStore I } evm
      (ltE (.var "arg0") (.intLit 65535)) = .ok (.bool false) := by
  unfold ltE
  simp only [evalExpr?, evalExpr_observations_arg0, observationsArgValue,
    EvalResult.bind, bind, pure, evalBinaryOp?]
  have hnot : ¬ Int.ofNat (observationsArgWord I).toNat < (65535 : Int) := by
    intro hlt
    change ((observationsArgWord I).toNat : Int) < (65535 : Int) at hlt
    have hltNat : (observationsArgWord I).toNat < 65535 := by
      exact_mod_cast hlt
    exact not_lt_of_ge hoob hltNat
  rw [show decide (Int.ofNat (observationsArgWord I).toNat < 65535) = false from
    decide_eq_false hnot]

private theorem observationsStorageTypeAtBase :
    storageTypeAt? storageDecls { base := "observations", steps := [] } =
      some (.array observationStructTy 65535) := by
  rfl

theorem observationsArrayIndexInBounds_ok {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) (hbound : (observationsArgWord I).toNat < 65535) :
    arrayIndexInBounds? (config v) evm (contract v).storage "observations" []
      (observationsArgKey I) = .ok () := by
  unfold arrayIndexInBounds?
  rw [show (contract v).storage = storageDecls by rfl, observationsStorageTypeAtBase]
  change (if 0 ≤ Int.ofNat (observationsArgWord I).toNat ∧
      Int.ofNat (observationsArgWord I).toNat < (↑(65535 : Nat) : Int) then
        EvalResult.ok () else EvalResult.revert) = EvalResult.ok ()
  have hin : 0 ≤ Int.ofNat (observationsArgWord I).toNat ∧
      Int.ofNat (observationsArgWord I).toNat < (↑(65535 : Nat) : Int) := by
    constructor
    · exact Int.natCast_nonneg _
    · change ((observationsArgWord I).toNat : Int) < (65535 : Int)
      exact_mod_cast hbound
  rw [if_pos hin]

theorem observationsArrayIndexInBounds_oob {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) (hoob : 65535 ≤ (observationsArgWord I).toNat) :
    arrayIndexInBounds? (config v) evm (contract v).storage "observations" []
      (observationsArgKey I) = .revert := by
  unfold arrayIndexInBounds?
  rw [show (contract v).storage = storageDecls by rfl, observationsStorageTypeAtBase]
  change (if 0 ≤ Int.ofNat (observationsArgWord I).toNat ∧
      Int.ofNat (observationsArgWord I).toNat < (↑(65535 : Nat) : Int) then
        EvalResult.ok () else EvalResult.revert) = EvalResult.revert
  have hout : ¬(0 ≤ Int.ofNat (observationsArgWord I).toNat ∧
      Int.ofNat (observationsArgWord I).toNat < (↑(65535 : Nat) : Int)) := by
    intro h
    have hltInt : ((observationsArgWord I).toNat : Int) < (65535 : Int) := by
      simpa using h.2
    exact not_lt_of_ge hoob (by exact_mod_cast hltInt)
  rw [if_neg hout]

theorem uniswapV3PoolObservationsDecodeOk {v : PoolImmutables} {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode
      (observationsTransition.params.map Param.name)
      (transitionSignature observationsTransition).paramTypes I.calldata =
        some (observationsStore I) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) =
      calldataWord I.calldata 4 :=
    decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  rw [show (config v).abiDecodeMode = DecodeMode.legacySolc05 from rfl]
  rw [decodeCalldataWithMode_legacyScalarWords_eq
    (names := observationsTransition.params.map Param.name)
    (types := (transitionSignature observationsTransition).paramTypes) (cd := I.calldata)]
  · rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
    change (match decodeScalarWordsWithMode? DecodeMode.legacySolc05 [uint256]
        (I.calldata.toList.drop 4) 0 with
      | some values => decodeCalldata.insertValues ["arg0"] values ∅
      | none => none) = some (observationsStore I)
    rw [show uint256 = abiUInt256 by rfl]
    simp only [decodeScalarWordsWithMode?]
    rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
      (bytes := I.calldata.toList.drop 4) (start := 0) htake4]
    change decodeCalldata.insertValues ["arg0"]
        [Value.int
          (Int.ofNat (ABI.bytesToWord ((I.calldata.toList.drop 4).take 32)).toNat)] ∅ =
      some (observationsStore I)
    simp [decodeCalldata.insertValues, observationsStore, observationsArgValue,
      observationsArgWord]
    rw [hword4]
  · native_decide

theorem uniswapV3PoolObservationsDecodeShort {v : PoolImmutables} {I : ExecutionEnv}
    (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode (config v).abiDecodeMode
      (observationsTransition.params.map Param.name)
      (transitionSignature observationsTransition).paramTypes I.calldata = none := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [show (config v).abiDecodeMode = DecodeMode.legacySolc05 from rfl]
  rw [decodeCalldataWithMode_legacyScalarWords_eq
    (names := observationsTransition.params.map Param.name)
    (types := (transitionSignature observationsTransition).paramTypes) (cd := I.calldata)]
  · by_cases hsz4 : I.calldata.size < 4
    · rw [if_pos (by rw [htlen]; omega : I.calldata.toList.length < 4)]
    · rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
      change (match decodeScalarWordsWithMode? DecodeMode.legacySolc05 [uint256]
          (I.calldata.toList.drop 4) 0 with
        | some values => decodeCalldata.insertValues ["arg0"] values ∅
        | none => none) = none
      rw [show uint256 = abiUInt256 by rfl]
      simp only [decodeScalarWordsWithMode?]
      rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
        (bytes := I.calldata.toList.drop 4) (start := 0) (by
          have htake0n : ¬ ((I.calldata.toList.drop 4).take 32).length = 32 := by
            rw [List.length_take, List.length_drop, htlen]
            omega
          simpa using htake0n)]
      simp only [Option.bind, bind]
  · native_decide

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolDispatch_observations {v : PoolImmutables} {cd : ByteArray}
    (hsel : (uniswapV3PoolSelBytes 4 == cd.extract 0 4) = true) :
    dispatchMsg (contract v) cd = some observationsTransition := by
  apply dispatchMsg_eq_some_of_split
    (pre := [burnTransition, collectTransition v, collectprotocolTransition v, factoryTransition v,
      feeTransition v, feegrowthglobal0X128Transition, feegrowthglobal1X128Transition,
      flashTransition v, increaseobservationcardinalitynextTransition v, initializeTransition,
      liquidityTransition, maxliquiditypertickTransition v, mintTransition v])
    (post := [observeTransition v, positionsTransition, protocolfeesTransition,
      setfeeprotocolTransition v, slot0Transition, snapshotcumulativesinsideTransition v,
      swapTransition v, tickbitmapTransition, tickspacingTransition v, ticksTransition,
      token0Transition v, token1Transition v])
  · simp [contract, transitions]
  · intro t ht
    simp at ht
    rcases ht with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [selectorOf, burnSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 17) (j := 4)
          (by native_decide) hsel
    · rw [selectorOf, collectSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 10) (j := 4)
          (by native_decide) hsel
    · rw [selectorOf, collectProtocolSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 15) (j := 4)
          (by native_decide) hsel
    · rw [selectorOf, factorySelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 19) (j := 4)
          (by native_decide) hsel
    · rw [selectorOf, feeSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 22) (j := 4)
          (by native_decide) hsel
    · rw [selectorOf, feeGrowthGlobal0X128SelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 23) (j := 4)
          (by native_decide) hsel
    · rw [selectorOf, feeGrowthGlobal1X128SelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 8) (j := 4)
          (by native_decide) hsel
    · rw [selectorOf, flashSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 9) (j := 4)
          (by native_decide) hsel
    · rw [selectorOf, increaseObservationCardinalityNextSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 5) (j := 4)
          (by native_decide) hsel
    · rw [selectorOf, initializeSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 25) (j := 4)
          (by native_decide) hsel
    · rw [selectorOf, liquiditySelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 2) (j := 4)
          (by native_decide) hsel
    · rw [selectorOf, maxLiquidityPerTickSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 13) (j := 4)
          (by native_decide) hsel
    · rw [selectorOf, mintSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 7) (j := 4)
          (by native_decide) hsel
  · rw [selectorOf, observationsSelectorBytes]
    simpa [uniswapV3PoolSelBytes] using hsel

theorem uniswapV3PoolObservationsReachEntry {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 4 == I.calldata.extract 0 4) = true) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨737⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := uniswapV3PoolReachSelector32
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize
  have hword : solcSelectorWord I = uniswapV3PoolSelNat 4 := by
    simpa [uniswapV3PoolSelBytes, uniswapV3PoolSelNat] using
      solcSelectorWord_eq_of_beq I hsz 0x25 0x2c 0x09 0xd7
        (uniswapV3PoolSelNat 4) (by native_decide) hsel
  have hgt32 : UInt256.gt (armSelNat code ⟨32⟩) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h239 := uniswapV3PoolSelectorSplitTakenTo (next := ⟨239⟩) hpatch h32 hgt32
  have hgt239 : UInt256.gt (armSelNat code ⟨239⟩) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h348 := uniswapV3PoolSelectorSplitTakenTo (next := ⟨348⟩) hpatch h239 hgt239
  have hgt348 : UInt256.gt (armSelNat code ⟨348⟩) (solcSelectorWord I) = ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h359 := uniswapV3PoolSelectorSplitNotTakenTo (next := ⟨359⟩) hpatch h348 hgt348
  have hmiss3 : (uniswapV3PoolSelBytes 3 == I.calldata.extract 0 4) = false :=
    uniswapV3PoolSelectorMissOfHit I (by native_decide) hsel
  have h370 := uniswapV3PoolSelectorArmMissToOf (i := 3) (next := ⟨370⟩)
    hpatch hsz hmiss3 h359
  have h737 := uniswapV3PoolSelectorArmHitTo (i := 4) (target := ⟨737⟩)
    hpatch hsz hsel h370
  exact ⟨_, _, h737⟩

private theorem uniswapV3PoolPatchPreservesJumpDest5334 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨5334⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched5334 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨5334⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest5334

private theorem uniswapV3PoolPatchPreservesJumpDest5351 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨5351⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched5351 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨5351⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest5351

private theorem uniswapV3PoolObservationsDecodedReachRoutine {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {de ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨759⟩ (de :: ⟨4⟩ :: ret :: R) mem aw rdata acc k C)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨5334⟩ (observationsArgWord ee :: ret :: R)
      mem aw rdata acc k' C' := by
  have rd760 : RD code ee g s0 ⟨760⟩ (de :: ⟨4⟩ :: ret :: R)
      mem aw rdata acc (k + 1) (C + 1) := by
    simpa using h.jumpdest
      (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide)
      (by evm_ov)
  have rd761 : RD code ee g s0 ⟨761⟩ (⟨4⟩ :: ret :: R)
      mem aw rdata acc (k + 1 + 1) (C + 1 + 2) := by
    simpa using rd760.pop
      (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide)
      (by evm_ov)
  have rd762 : RD code ee g s0 ⟨762⟩ (observationsArgWord ee :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1) (C + 1 + 2 + 3) := by
    simpa [observationsArgWord, calldataWord,
        show (⟨4⟩ : UInt256).toNat = 4 from by decide] using
      (rd761.calldataload
        (by
          rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
          native_decide)
        (by evm_ov))
  have rd765 : RD code ee g s0 ⟨765⟩ (⟨5334⟩ :: observationsArgWord ee :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1 + 1) (C + 1 + 2 + 3 + 3) := by
    simpa using rd762.push2 ⟨5334⟩
      (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide)
      (by evm_ov)
  exact ⟨_, _, rd765.jump
    (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide)
    (uniswapV3PoolJumpDestPatched5334 hpatch)
    (by evm_ov)⟩

set_option maxHeartbeats 3000000 in
private theorem uniswapV3PoolObservationsExternalLenOk {v : PoolImmutables}
    {code : ByteArray} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨737⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨759⟩
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ⟨766⟩ ::
        [solcSelectorWord I])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  exact RD.solcExternalStaticArgsLenOk (need := ⟨32⟩)
    (entry := ⟨737⟩) (ret := ⟨766⟩) (decoded := ⟨759⟩) hreach
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

theorem uniswapV3PoolObservationsEvmDecodeShort {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 4 == I.calldata.extract 0 4) = true)
    (hshort : I.calldata.size < 36) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  have hreach := uniswapV3PoolObservationsReachEntry
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
    (entry := ⟨737⟩) (ret := ⟨766⟩) (decoded := ⟨759⟩) hreach
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

private theorem uniswapV3PoolObservationsRoutinePatchDisjoint {v : PoolImmutables}
    {pc : UInt256} (hlo : 5308 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 6603) :
    ∀ p ∈ patches v, pc.toNat + 33 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;>
    omega

private def observationsStSignextend (s : State) (v : UInt256)
    (t : List UInt256) : State :=
  { s with
      machineState.stack := v :: t,
      machineState.gasAvailable := s.machineState.gasAvailable.subNat 5
      machineState.pc := s.machineState.pc + ⟨1⟩
      machineState.execLength := s.machineState.execLength + 1 }

private theorem observationsSignextendXstep {code : ByteArray} {s : State}
    {pc a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pc)
    (hdec : decode code pc = some (.SIGNEXTEND, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s =
      if s.machineState.gasAvailable.toNat < 5 then .error .OutOfGass
      else .ok (observationsStSignextend s (UInt256.signextend a b) t, .none) := by
  have hdecS : decode s.executionEnv.code s.machineState.pc = some (.SIGNEXTEND, .none) := by
    rw [hcode, hpc]
    exact hdec
  have hstep := step_signextend s hdecS
  have hnoOverflow : ¬ 1024 ≤ t.length := by omega
  simpa [hcode, hstk, GasConstants.Glow, observationsStSignextend, hnoOverflow] using hstep

private theorem observationsRDSignextend {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {pc : UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SIGNEXTEND, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.signextend a b :: t) mem aw rdata acc
      (k + 1) (C + 5) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc,
      hee, hworld⟩
  · exact Or.inl hoog
  · have st := observationsSignextendXstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 5
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨observationsStSignextend s (UInt256.signextend a b) t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_,
        by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [observationsStSignextend]; exact hcode
      · simp only [observationsStSignextend]; rw [hpc]
      · rfl
      · simp only [observationsStSignextend]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [observationsStSignextend]; exact hmem
      · simp only [observationsStSignextend]; exact haw
      · simp only [observationsStSignextend]; exact hrdata
      · simp only [observationsStSignextend]; exact hacc
      · exact hee
      · exact hworld

theorem uniswapV3PoolObservationsRoutine {v : PoolImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {ret : UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨5334⟩ (observationsArgWord ee :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hret : (D_J code 0).contains ret = true)
    (hbound : (observationsArgWord ee).toNat < 65535)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (observationsInitializedRawWord σ ee ::
        observationsSecondsPerLiquidityWord σ ee ::
        observationsTickReturnWord σ ee ::
        observationsBlockTimestampWord σ ee :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
  have hlt : UInt256.lt (observationsArgWord ee) ⟨65535⟩ = ⟨1⟩ := by
    apply ult_one
    rw [show (⟨65535⟩ : UInt256).toNat = 65535 from by decide]
    exact hbound
  have hdecode {pc : UInt256} (hlo : 5308 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 6603) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 6603 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolObservationsRoutinePatchDisjoint hlo hhi)]
  have hd5334 : decode code ⟨5334⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5335 : decode code ⟨5335⟩ = some (.Push .PUSH1, some (⟨8⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5337 : decode code ⟨5337⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5338 : decode code ⟨5338⟩ = some (.Push .PUSH2, some (⟨65535⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5341 : decode code ⟨5341⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5342 : decode code ⟨5342⟩ = some (.LT, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5343 : decode code ⟨5343⟩ = some (.Push .PUSH2, some (⟨5351⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5346 : decode code ⟨5346⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5351 : decode code ⟨5351⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5352 : decode code ⟨5352⟩ = some (.ADD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5353 : decode code ⟨5353⟩ = some (.SLOAD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5354 : decode code ⟨5354⟩ = some (.Push .PUSH4, some (⟨4294967295⟩, 4)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5359 : decode code ⟨5359⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5360 : decode code ⟨5360⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5361 : decode code ⟨5361⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5362 : decode code ⟨5362⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5363 : decode code ⟨5363⟩ =
      some (.Push .PUSH5, some (⟨4294967296⟩, 5)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5369 : decode code ⟨5369⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5370 : decode code ⟨5370⟩ = some (.DIV, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5371 : decode code ⟨5371⟩ = some (.Push .PUSH1, some (⟨6⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5373 : decode code ⟨5373⟩ = some (.SIGNEXTEND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5374 : decode code ⟨5374⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5375 : decode code ⟨5375⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5377 : decode code ⟨5377⟩ = some (.Push .PUSH1, some (⟨88⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5379 : decode code ⟨5379⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5380 : decode code ⟨5380⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5381 : decode code ⟨5381⟩ = some (.DIV, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5382 : decode code ⟨5382⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5384 : decode code ⟨5384⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5386 : decode code ⟨5386⟩ = some (.Push .PUSH1, some (⟨160⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5388 : decode code ⟨5388⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5389 : decode code ⟨5389⟩ = some (.SUB, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5390 : decode code ⟨5390⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5391 : decode code ⟨5391⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5392 : decode code ⟨5392⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5394 : decode code ⟨5394⟩ = some (.Push .PUSH1, some (⟨248⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5396 : decode code ⟨5396⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5397 : decode code ⟨5397⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5398 : decode code ⟨5398⟩ = some (.DIV, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5399 : decode code ⟨5399⟩ = some (.Push .PUSH1, some (⟨255⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5401 : decode code ⟨5401⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5402 : decode code ⟨5402⟩ = some (.DUP5, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5403 : decode code ⟨5403⟩ = some (.JUMP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd5343 := evm_run h with [
    raw jumpdest hd5334 (by evm_ov),
    raw push1 ⟨8⟩ hd5335 (by evm_ov),
    raw dup2 hd5337 (by evm_ov),
    raw push2 ⟨65535⟩ hd5338 (by evm_ov),
    raw dup2 hd5341 (by evm_ov),
    raw lt hd5342 (by evm_ov)]
  rw [hlt] at rd5343
  have rd5346 := evm_run rd5343 with [
    raw push2 ⟨5351⟩ hd5343 (by evm_ov)]
  have rd5351 := rd5346.jumpiT hd5346
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (uniswapV3PoolJumpDestPatched5351 hpatch)
    (by evm_ov)
  have rd5353 := evm_run rd5351 with [
    raw jumpdest hd5351 (by evm_ov),
    raw add hd5352 (by evm_ov)]
  obtain ⟨_, _, rd5354⟩ := rd5353.sload hd5353 (by evm_ov)
  have rd5363 := evm_run rd5354 with [
    raw push4 ⟨4294967295⟩ hd5354 (by evm_ov),
    raw dup2 hd5359 (by evm_ov),
    raw and hd5360 (by evm_ov),
    raw swap2 hd5361 (by evm_ov),
    raw pop hd5362 (by evm_ov)]
  have rd5369Ex : ∃ k' C', RD code ee g s0 ⟨5369⟩
      (⟨4294967296⟩ ::
        (σ.find? ee.codeOwner |>.option ⟨0⟩
          (fun ac => ac.storage.findD (observationsArgWord ee + ⟨8⟩) ⟨0⟩)) ::
        UInt256.land
          (σ.find? ee.codeOwner |>.option ⟨0⟩
          (fun ac => ac.storage.findD (observationsArgWord ee + ⟨8⟩) ⟨0⟩))
          ⟨4294967295⟩ ::
        ret :: R)
      mem aw rdata (cA, σ) k' C' := by
    exact ⟨_, _, by
      simpa using rd5363.pushConst ⟨4294967296⟩
        (by decide : Operation.POp.PUSH5 ≠ .PUSH0) hd5363 (by evm_ov)⟩
  obtain ⟨_, _, rd5369⟩ := rd5369Ex
  have rd5373 := evm_run rd5369 with [
    raw dup2 hd5369 (by evm_ov),
    raw div hd5370 (by evm_ov),
    raw push1 ⟨6⟩ hd5371 (by evm_ov)]
  have rd5374 := observationsRDSignextend rd5373 hd5373 (by evm_ov)
  have rd5403 := evm_run rd5374 with [
    raw swap1 hd5374 (by evm_ov),
    raw push1 ⟨1⟩ hd5375 (by evm_ov),
    raw push1 ⟨88⟩ hd5377 (by evm_ov),
    raw shl hd5379 (by evm_ov),
    raw dup2 hd5380 (by evm_ov),
    raw div hd5381 (by evm_ov),
    raw push1 ⟨1⟩ hd5382 (by evm_ov),
    raw push1 ⟨1⟩ hd5384 (by evm_ov),
    raw push1 ⟨160⟩ hd5386 (by evm_ov),
    raw shl hd5388 (by evm_ov),
    raw sub hd5389 (by evm_ov),
    raw and hd5390 (by evm_ov),
    raw swap1 hd5391 (by evm_ov),
    raw push1 ⟨1⟩ hd5392 (by evm_ov),
    raw push1 ⟨248⟩ hd5394 (by evm_ov),
    raw shl hd5396 (by evm_ov),
    raw swap1 hd5397 (by evm_ov),
    raw div hd5398 (by evm_ov),
    raw push1 ⟨255⟩ hd5399 (by evm_ov),
    raw and hd5401 (by evm_ov),
    raw dup5 hd5402 (by evm_ov)]
  have rdRet := rd5403.jump hd5403 hret (by evm_ov)
  have hmask32 : (⟨4294967295⟩ : UInt256) = observationsUint32Mask := by
    native_decide
  have hshift32 : (⟨4294967296⟩ : UInt256) = observationsShiftBytes 4 := by
    native_decide
  have hshift88 :
      UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨88⟩ = observationsShiftBytes 11 := by
    native_decide
  have hmask160 :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        slot0Uint160Mask := by
    native_decide
  have hshift248 :
      UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨248⟩ = observationsShiftBytes 31 := by
    native_decide
  have hmask8 : (⟨255⟩ : UInt256) = slot0Uint8Mask := by
    native_decide
  have hsecondsComm :
      UInt256.land slot0Uint160Mask
          (UInt256.div (observationsSlotWord σ ee) (observationsShiftBytes 11)) =
        UInt256.land
          (UInt256.div (observationsSlotWord σ ee) (observationsShiftBytes 11))
          slot0Uint160Mask := by
    rw [u256_land_comm]
  have hinitializedComm :
      UInt256.land slot0Uint8Mask
          (UInt256.div (observationsSlotWord σ ee) (observationsShiftBytes 31)) =
        UInt256.land
          (UInt256.div (observationsSlotWord σ ee) (observationsShiftBytes 31))
          slot0Uint8Mask := by
    rw [u256_land_comm]
  exact ⟨_, _, by
    rw [hmask32, hshift32, hshift88, hmask160, hshift248, hmask8] at rdRet
    simpa [observationsInitializedRawWord, observationsSecondsPerLiquidityWord,
      observationsTickReturnWord, observationsTickRawWord, observationsBlockTimestampWord,
      observationsSlotWord, solcSlotWord, observationsArgAddBase_eq_baseSlot,
      hsecondsComm, hinitializedComm] using rdRet⟩

theorem uniswapV3PoolObservationsRoutineOob {v : PoolImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {ret : UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨5334⟩ (observationsArgWord ee :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hoob : 65535 ≤ (observationsArgWord ee).toNat)
    (hov : R.length + 6 ≤ 1024) :
    RDrev code g s0 := by
  have hlt : UInt256.lt (observationsArgWord ee) ⟨65535⟩ = ⟨0⟩ := by
    apply ult_zero
    rw [show (⟨65535⟩ : UInt256).toNat = 65535 from by decide]
    exact hoob
  have hdecode {pc : UInt256} (hlo : 5308 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 6603) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 6603 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolObservationsRoutinePatchDisjoint hlo hhi)]
  have hd5334 : decode code ⟨5334⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5335 : decode code ⟨5335⟩ = some (.Push .PUSH1, some (⟨8⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5337 : decode code ⟨5337⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5338 : decode code ⟨5338⟩ = some (.Push .PUSH2, some (⟨65535⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5341 : decode code ⟨5341⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5342 : decode code ⟨5342⟩ = some (.LT, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5343 : decode code ⟨5343⟩ = some (.Push .PUSH2, some (⟨5351⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5346 : decode code ⟨5346⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5347 : decode code ⟨5347⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5349 : decode code ⟨5349⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5350 : decode code ⟨5350⟩ = some (.REVERT, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd5343 := evm_run h with [
    raw jumpdest hd5334 (by evm_ov),
    raw push1 ⟨8⟩ hd5335 (by evm_ov),
    raw dup2 hd5337 (by evm_ov),
    raw push2 ⟨65535⟩ hd5338 (by evm_ov),
    raw dup2 hd5341 (by evm_ov),
    raw lt hd5342 (by evm_ov)]
  rw [hlt] at rd5343
  have rd5346 := evm_run rd5343 with [
    raw push2 ⟨5351⟩ hd5343 (by evm_ov)]
  have rd5347 := rd5346.jumpiNT hd5346
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by evm_ov)
  exact RD.uniswapPush1Dup1Revert0 rd5347 hd5347 hd5349 hd5350 (by evm_ov)

theorem uniswapV3PoolObservationsEvmOob {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 4 == I.calldata.extract 0 4) = true)
    (hsz36 : 36 ≤ I.calldata.size)
    (hoob : 65535 ≤ (observationsArgWord I).toNat) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  have hreach := uniswapV3PoolObservationsReachEntry
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize hsel
  obtain ⟨_, _, hdecoded⟩ := uniswapV3PoolObservationsExternalLenOk
    hpatch hreach hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := uniswapV3PoolObservationsDecodedReachRoutine
    hpatch hdecoded (by simp only [List.length_singleton]; omega)
  exact uniswapV3PoolObservationsRoutineOob hpatch hroutine hoob
    (by simp only [List.length_singleton]; omega)

theorem uniswapV3PoolObservationsEvmLoaded {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 4 == I.calldata.extract 0 4) = true)
    (hsz36 : 36 ≤ I.calldata.size)
    (hbound : (observationsArgWord I).toNat < 65535) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨766⟩
      (observationsInitializedRawWord σ I ::
        observationsSecondsPerLiquidityWord σ I ::
        observationsTickReturnWord σ I ::
        observationsBlockTimestampWord σ I :: ⟨766⟩ :: [solcSelectorWord I])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hreach := uniswapV3PoolObservationsReachEntry
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize hsel
  obtain ⟨_, _, hdecoded⟩ := uniswapV3PoolObservationsExternalLenOk
    hpatch hreach hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := uniswapV3PoolObservationsDecodedReachRoutine
    hpatch hdecoded (by simp only [List.length_singleton]; omega)
  exact uniswapV3PoolObservationsRoutine hpatch hroutine
    (uniswapV3PoolJumpDestPatched2258 hpatch (by native_decide))
    hbound (by simp only [List.length_singleton]; omega)

noncomputable def observationsReturnMem1 (blockTimestamp : UInt256) : ByteArray :=
  writeCascade solcFreePtrMem [(128, blockTimestamp)]

noncomputable def observationsReturnMem2 (blockTimestamp tick : UInt256) : ByteArray :=
  writeCascade solcFreePtrMem [(128, blockTimestamp), (160, tick)]

noncomputable def observationsReturnMem3 (blockTimestamp tick seconds : UInt256) :
    ByteArray :=
  writeCascade solcFreePtrMem [(128, blockTimestamp), (160, tick), (192, seconds)]

noncomputable def observationsReturnMem
    (blockTimestamp tick seconds initialized : UInt256) : ByteArray :=
  writeCascade solcFreePtrMem
    [(128, blockTimestamp), (160, tick), (192, seconds), (224, initialized)]

theorem observationsReturnMem1_eq (blockTimestamp : UInt256) :
    observationsReturnMem1 blockTimestamp = writeWord solcFreePtrMem 128 blockTimestamp := by
  rfl

theorem observationsReturnMem2_eq (blockTimestamp tick : UInt256) :
    observationsReturnMem2 blockTimestamp tick =
      writeWord (observationsReturnMem1 blockTimestamp) 160 tick := by
  rfl

theorem observationsReturnMem3_eq (blockTimestamp tick seconds : UInt256) :
    observationsReturnMem3 blockTimestamp tick seconds =
      writeWord (observationsReturnMem2 blockTimestamp tick) 192 seconds := by
  rfl

theorem observationsReturnMem_eq
    (blockTimestamp tick seconds initialized : UInt256) :
    observationsReturnMem blockTimestamp tick seconds initialized =
      writeWord (observationsReturnMem3 blockTimestamp tick seconds) 224 initialized := by
  rfl

theorem observationsReturnMem1_size (blockTimestamp : UInt256) :
    (observationsReturnMem1 blockTimestamp).size = 160 := by
  unfold observationsReturnMem1
  exact writeCascade_size_of_base solcFreePtrMem _ solcFreePtrMem_size
    (by
      norm_num [WriteGapsOk]
      all_goals native_decide)
    (by norm_num [writeCascadeSize])

theorem observationsReturnMem2_size (blockTimestamp tick : UInt256) :
    (observationsReturnMem2 blockTimestamp tick).size = 192 := by
  unfold observationsReturnMem2
  exact writeCascade_size_of_base solcFreePtrMem _ solcFreePtrMem_size
    (by
      norm_num [WriteGapsOk]
      all_goals native_decide)
    (by norm_num [writeCascadeSize])

theorem observationsReturnMem3_size (blockTimestamp tick seconds : UInt256) :
    (observationsReturnMem3 blockTimestamp tick seconds).size = 224 := by
  unfold observationsReturnMem3
  exact writeCascade_size_of_base solcFreePtrMem _ solcFreePtrMem_size
    (by
      norm_num [WriteGapsOk]
      all_goals native_decide)
    (by norm_num [writeCascadeSize])

theorem observationsReturnMem_size
    (blockTimestamp tick seconds initialized : UInt256) :
    (observationsReturnMem blockTimestamp tick seconds initialized).size = 256 := by
  unfold observationsReturnMem
  exact writeCascade_size_of_base solcFreePtrMem _ solcFreePtrMem_size
    (by
      norm_num [WriteGapsOk]
      all_goals native_decide)
    (by norm_num [writeCascadeSize])

theorem observationsReturnMem_read64
    (blockTimestamp tick seconds initialized : UInt256) :
    (observationsReturnMem blockTimestamp tick seconds initialized).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold observationsReturnMem
  rw [writeCascade_read_preserved_of_base solcFreePtrMem _ solcFreePtrMem_size
    (by
      norm_num [WindowDisjointFromWrites]
      all_goals native_decide)]
  exact solcFreePtrMem_read64

theorem observationsReturnMem_mload64
    (blockTimestamp tick seconds initialized : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (observationsReturnMem blockTimestamp tick seconds initialized).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((observationsReturnMem blockTimestamp tick seconds initialized).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
  mloadFreePtrValue (by rw [observationsReturnMem_size]; decide) (by decide)
    (observationsReturnMem_read64 blockTimestamp tick seconds initialized)

theorem observationsReturnMem_read128
    (blockTimestamp tick seconds initialized : UInt256) :
    (observationsReturnMem blockTimestamp tick seconds initialized).readWithPadding 128 32 =
      UInt256.toByteArray blockTimestamp := by
  unfold observationsReturnMem
  exact writeCascade_read_word_of_head_of_base solcFreePtrMem (base := 96) (off := 128)
    blockTimestamp [(160, tick), (192, seconds), (224, initialized)]
      solcFreePtrMem_size (by native_decide)
      (by
        norm_num [WindowDisjointFromWrites])

theorem observationsReturnMem_read160
    (blockTimestamp tick seconds initialized : UInt256) :
    (observationsReturnMem blockTimestamp tick seconds initialized).readWithPadding 160 32 =
      UInt256.toByteArray tick := by
  unfold observationsReturnMem
  change (writeCascade (observationsReturnMem1 blockTimestamp)
      [(160, tick), (192, seconds), (224, initialized)]).readWithPadding 160 32 =
    UInt256.toByteArray tick
  exact writeCascade_read_word_of_head_of_base (observationsReturnMem1 blockTimestamp)
    (base := 160) (off := 160) tick [(192, seconds), (224, initialized)]
      (observationsReturnMem1_size blockTimestamp) (by native_decide)
      (by
        norm_num [WindowDisjointFromWrites])

theorem observationsReturnMem_read192
    (blockTimestamp tick seconds initialized : UInt256) :
    (observationsReturnMem blockTimestamp tick seconds initialized).readWithPadding 192 32 =
      UInt256.toByteArray seconds := by
  unfold observationsReturnMem
  change (writeCascade (observationsReturnMem2 blockTimestamp tick)
      [(192, seconds), (224, initialized)]).readWithPadding 192 32 =
    UInt256.toByteArray seconds
  exact writeCascade_read_word_of_head_of_base (observationsReturnMem2 blockTimestamp tick)
    (base := 192) (off := 192) seconds [(224, initialized)]
      (observationsReturnMem2_size blockTimestamp tick) (by native_decide)
      (by
        norm_num [WindowDisjointFromWrites])

theorem observationsReturnMem_read224
    (blockTimestamp tick seconds initialized : UInt256) :
    (observationsReturnMem blockTimestamp tick seconds initialized).readWithPadding 224 32 =
      UInt256.toByteArray initialized := by
  unfold observationsReturnMem
  change (writeCascade (observationsReturnMem3 blockTimestamp tick seconds)
      [(224, initialized)]).readWithPadding 224 32 =
    UInt256.toByteArray initialized
  exact writeCascade_read_word_of_head_of_base
    (observationsReturnMem3 blockTimestamp tick seconds) (base := 224) (off := 224)
      initialized [] (observationsReturnMem3_size blockTimestamp tick seconds)
      (by native_decide)
      (by
        norm_num [WindowDisjointFromWrites])

theorem observationsReturnMem_read128_128
    (blockTimestamp tick seconds initialized : UInt256) :
    (observationsReturnMem blockTimestamp tick seconds initialized).readWithPadding 128 128 =
      UInt256.toByteArray blockTimestamp ++ UInt256.toByteArray tick ++
        UInt256.toByteArray seconds ++ UInt256.toByteArray initialized := by
  let mem := observationsReturnMem blockTimestamp tick seconds initialized
  have hsize : mem.size = 256 := by
    simpa [mem] using observationsReturnMem_size blockTimestamp tick seconds initialized
  have h128 : mem.readWithPadding 128 32 = UInt256.toByteArray blockTimestamp := by
    simpa [mem] using observationsReturnMem_read128 blockTimestamp tick seconds initialized
  have h160 : mem.readWithPadding 160 32 = UInt256.toByteArray tick := by
    simpa [mem] using observationsReturnMem_read160 blockTimestamp tick seconds initialized
  have h192 : mem.readWithPadding 192 32 = UInt256.toByteArray seconds := by
    simpa [mem] using observationsReturnMem_read192 blockTimestamp tick seconds initialized
  have h224 : mem.readWithPadding 224 32 = UInt256.toByteArray initialized := by
    simpa [mem] using observationsReturnMem_read224 blockTimestamp tick seconds initialized
  change mem.readWithPadding 128 128 = _
  rw [byteArray_readWithPadding_split mem 128 32 96 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by omega), h128]
  rw [byteArray_readWithPadding_split mem 160 32 64 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by omega), h160]
  rw [byteArray_readWithPadding_split mem 192 32 32 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by omega), h192, h224]
  simp only [ByteArray.append_assoc]

theorem uniswapV3PoolObservationsReturn {v : PoolImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {initialized seconds tick blockTimestamp : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨766⟩
      (initialized :: seconds :: tick :: blockTimestamp :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 10 ≤ 1024) :
    RDret code g s0 acc
      (UInt256.toByteArray (UInt256.land blockTimestamp observationsUint32Mask) ++
        UInt256.toByteArray (UInt256.signextend ⟨6⟩ tick) ++
          UInt256.toByteArray (UInt256.land seconds slot0Uint160Mask) ++
            UInt256.toByteArray (slot0BoolReturnWord initialized)) := by
  let blockTimestamp' := UInt256.land blockTimestamp observationsUint32Mask
  let tick' := UInt256.signextend ⟨6⟩ tick
  let seconds' := UInt256.land seconds slot0Uint160Mask
  let initialized' := slot0BoolReturnWord initialized
  have hmask32 : (⟨4294967295⟩ : UInt256) = observationsUint32Mask := by
    native_decide
  have hmask160 :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        slot0Uint160Mask := by
    native_decide
  have hdecode {pc : UInt256} (hpc : pc.toNat + 33 ≤ 2258) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch hpc]
  have hd766 : decode code ⟨766⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd767 : decode code ⟨767⟩ = some (.Push .PUSH1, some (⟨64⟩, 1)) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd769 : decode code ⟨769⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd770 : decode code ⟨770⟩ = some (.MLOAD, .none) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd771 : decode code ⟨771⟩ =
      some (.Push .PUSH4, some (⟨4294967295⟩, 4)) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd776 : decode code ⟨776⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd777 : decode code ⟨777⟩ = some (.SWAP6, .none) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd778 : decode code ⟨778⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd779 : decode code ⟨779⟩ = some (.DUP6, .none) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd780 : decode code ⟨780⟩ = some (.MSTORE, .none) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd781 : decode code ⟨781⟩ = some (.Push .PUSH1, some (⟨6⟩, 1)) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd783 : decode code ⟨783⟩ = some (.SWAP4, .none) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd784 : decode code ⟨784⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd785 : decode code ⟨785⟩ = some (.SWAP4, .none) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd786 : decode code ⟨786⟩ = some (.SIGNEXTEND, .none) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd787 : decode code ⟨787⟩ = some (.Push .PUSH1, some (⟨32⟩, 1)) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd789 : decode code ⟨789⟩ = some (.DUP6, .none) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd790 : decode code ⟨790⟩ = some (.ADD, .none) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd791 : decode code ⟨791⟩ = some (.MSTORE, .none) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd792 : decode code ⟨792⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd794 : decode code ⟨794⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd796 : decode code ⟨796⟩ = some (.Push .PUSH1, some (⟨160⟩, 1)) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd798 : decode code ⟨798⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd799 : decode code ⟨799⟩ = some (.SUB, .none) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd800 : decode code ⟨800⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd801 : decode code ⟨801⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd802 : decode code ⟨802⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd803 : decode code ⟨803⟩ = some (.DUP4, .none) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd804 : decode code ⟨804⟩ = some (.DUP4, .none) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd805 : decode code ⟨805⟩ = some (.ADD, .none) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd806 : decode code ⟨806⟩ = some (.MSTORE, .none) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd807 : decode code ⟨807⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd808 : decode code ⟨808⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd809 : decode code ⟨809⟩ = some (.Push .PUSH1, some (⟨96⟩, 1)) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd811 : decode code ⟨811⟩ = some (.DUP4, .none) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd812 : decode code ⟨812⟩ = some (.ADD, .none) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd813 : decode code ⟨813⟩ = some (.MSTORE, .none) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd814 : decode code ⟨814⟩ = some (.MLOAD, .none) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd815 : decode code ⟨815⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd816 : decode code ⟨816⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd817 : decode code ⟨817⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd818 : decode code ⟨818⟩ = some (.SUB, .none) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd819 : decode code ⟨819⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd821 : decode code ⟨821⟩ = some (.ADD, .none) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd822 : decode code ⟨822⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide)]
    native_decide
  have hd823 : decode code ⟨823⟩ = some (.RETURN, .none) := by
    rw [hdecode (by native_decide)]
    native_decide
  have rd780 := evm_run h with [
    raw jumpdest hd766 (by evm_ov),
    raw push1 ⟨64⟩ hd767 (by evm_ov),
    raw dup1 hd769 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd770 mem_cost solcFreePtrMem_mload64
      (by decide) (by evm_ov),
    raw push4 ⟨4294967295⟩ hd771 (by evm_ov),
    raw swap1 hd776 (by evm_ov),
    raw swap6 hd777 (by evm_ov),
    raw and hd778 (by evm_ov),
    raw dup6 hd779 (by evm_ov)]
  have rd781 := rd780.mstore 6 (observationsReturnMem1 blockTimestamp')
    (UInt256.ofNat 5) hd780 mem_cost
    (by
      dsimp [blockTimestamp']
      rw [hmask32, show (⟨128⟩ : UInt256).toNat = 128 from by decide,
        observationsReturnMem1_eq]
      rfl)
    (by decide) (by evm_ov)
  have rd786 := evm_run rd781 with [
    raw push1 ⟨6⟩ hd781 (by evm_ov),
    raw swap4 hd783 (by evm_ov),
    raw swap1 hd784 (by evm_ov),
    raw swap4 hd785 (by evm_ov)]
  have rd787 := observationsRDSignextend rd786 hd786 (by evm_ov)
  have rd791 := evm_run rd787 with [
    raw push1 ⟨32⟩ hd787 (by evm_ov),
    raw dup6 hd789 (by evm_ov),
    raw add hd790 (by evm_ov)]
  have rd792 := rd791.mstore 3 (observationsReturnMem2 blockTimestamp' tick')
    (UInt256.ofNat 6) hd791 mem_cost
    (by
      dsimp [tick']
      rw [show ((⟨128⟩ : UInt256) + ⟨32⟩).toNat = 160 from by decide,
        observationsReturnMem2_eq]
      rfl)
    (by decide) (by evm_ov)
  have rd806 := evm_run rd792 with [
    raw push1 ⟨1⟩ hd792 (by evm_ov),
    raw push1 ⟨1⟩ hd794 (by evm_ov),
    raw push1 ⟨160⟩ hd796 (by evm_ov),
    raw shl hd798 (by evm_ov),
    raw sub hd799 (by evm_ov),
    raw swap1 hd800 (by evm_ov),
    raw swap2 hd801 (by evm_ov),
    raw and hd802 (by evm_ov),
    raw dup4 hd803 (by evm_ov),
    raw dup4 hd804 (by evm_ov),
    raw add hd805 (by evm_ov)]
  have rd807 := rd806.mstore 3 (observationsReturnMem3 blockTimestamp' tick' seconds')
    (UInt256.ofNat 7) hd806 mem_cost
    (by
      dsimp [seconds']
      rw [hmask160, show ((⟨64⟩ : UInt256) + ⟨128⟩).toNat = 192 from by decide,
        observationsReturnMem3_eq]
      rfl)
    (by decide) (by evm_ov)
  have rd813 := evm_run rd807 with [
    raw iszero hd807 (by evm_ov),
    raw iszero hd808 (by evm_ov),
    raw push1 ⟨96⟩ hd809 (by evm_ov),
    raw dup4 hd811 (by evm_ov),
    raw add hd812 (by evm_ov)]
  have rd814 := rd813.mstore 3
    (observationsReturnMem blockTimestamp' tick' seconds' initialized')
    (UInt256.ofNat 8) hd813 mem_cost
    (by
      dsimp [initialized', slot0BoolReturnWord]
      rw [show ((⟨128⟩ : UInt256) + ⟨96⟩).toNat = 224 from by decide,
        observationsReturnMem_eq]
      rfl)
    (by decide) (by evm_ov)
  exact evm_run rd814 with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) hd814 mem_cost
      (observationsReturnMem_mload64 blockTimestamp' tick' seconds' initialized')
      (by decide) (by evm_ov),
    raw swap1 hd815 (by evm_ov),
    raw dup2 hd816 (by evm_ov),
    raw swap1 hd817 (by evm_ov),
    raw sub hd818 (by evm_ov),
    raw push1 ⟨128⟩ hd819 (by evm_ov),
    raw add hd821 (by evm_ov),
    raw swap1 hd822 (by evm_ov),
    raw ret 0
      (UInt256.toByteArray blockTimestamp' ++ UInt256.toByteArray tick' ++
        UInt256.toByteArray seconds' ++ UInt256.toByteArray initialized')
      hd823 mem_cost
      (by
        dsimp [blockTimestamp', tick', seconds', initialized']
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show ((⟨128⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat =
            128 from by decide]
        exact observationsReturnMem_read128_128
          (UInt256.land blockTimestamp observationsUint32Mask)
          (UInt256.signextend ⟨6⟩ tick)
          (UInt256.land seconds slot0Uint160Mask) (slot0BoolReturnWord initialized))
      (by evm_ov)]

theorem uniswapV3PoolObservationsEvm {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 4 == I.calldata.extract 0 4) = true)
    (hsz36 : 36 ≤ I.calldata.size)
    (hbound : (observationsArgWord I).toNat < 65535) :
    RDret code g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (observationsBlockTimestampWord σ I) ++
        UInt256.toByteArray (UInt256.signextend ⟨6⟩ (observationsTickReturnWord σ I)) ++
          UInt256.toByteArray (observationsSecondsPerLiquidityWord σ I) ++
            UInt256.toByteArray (observationsInitializedReturnWord σ I)) := by
  obtain ⟨_, _, rdReturn⟩ := uniswapV3PoolObservationsEvmLoaded
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize hsel
    hsz36 hbound
  have hret := uniswapV3PoolObservationsReturn hpatch
    (initialized := observationsInitializedRawWord σ I)
    (seconds := observationsSecondsPerLiquidityWord σ I)
    (tick := observationsTickReturnWord σ I)
    (blockTimestamp := observationsBlockTimestampWord σ I)
    (R := [⟨766⟩, solcSelectorWord I]) rdReturn
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hblock :
      UInt256.land (observationsBlockTimestampWord σ I) observationsUint32Mask =
        observationsBlockTimestampWord σ I := by
    exact observationsUint32Mask_clean (by
      simpa [observationsBlockTimestampWord] using
        observationsUint32Mask_bound (observationsSlotWord σ I))
  have hseconds :
      UInt256.land (observationsSecondsPerLiquidityWord σ I) slot0Uint160Mask =
        observationsSecondsPerLiquidityWord σ I := by
    exact slot0Uint160Mask_clean (by
      simpa [observationsSecondsPerLiquidityWord] using
        slot0Uint160Mask_bound
          (UInt256.div (observationsSlotWord σ I) (observationsShiftBytes 11)))
  simpa [observationsInitializedReturnWord, hblock, hseconds] using hret

theorem observationsStorageLocLoad_blockTimestamp (evm : EVM.State) (I : ExecutionEnv) :
    storageLocLoad evm
        (loc (observationsBaseSlot I) ⟨0, by decide⟩ ⟨4, by decide⟩
          (by decide) (.int uint32Int)) =
      .int (Int.ofNat (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (observationsBaseSlot I))
        observationsUint32Mask).toNat) := by
  rw [← show UInt256.ofNat (2 ^ (8 * 4) - 1) = observationsUint32Mask by native_decide]
  simpa [loc, uint32Int] using
    storageLocLoad_uint_offset0 evm (observationsBaseSlot I) (4 : Fin 33) ⟨32, by decide⟩
      (hbound := by decide) (by decide)

theorem observationsStorageLocLoad_tickCumulative (evm : EVM.State) (I : ExecutionEnv) :
    storageLocLoad evm
        (loc (observationsBaseSlot I) ⟨4, by decide⟩ ⟨7, by decide⟩
          (by decide) (.int int56Int)) =
      wordToElem (.int int56Int)
        (UInt256.land
          (UInt256.div
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (observationsBaseSlot I))
            (observationsShiftBytes 4))
          observationsUint56Mask) := by
  rw [← show UInt256.ofNat (256 ^ (4 : Nat)) = observationsShiftBytes 4 by rfl]
  rw [← show UInt256.ofNat (256 ^ (7 : Nat) - 1) = observationsUint56Mask by
    native_decide]
  simpa [loc, int56Int] using
    storageLocLoad_sint_offset evm (observationsBaseSlot I) (4 : Fin 32) (7 : Fin 33)
      ⟨56, by decide⟩ (hbound := by decide) (by decide) (by decide)

theorem observationsStorageLocLoad_secondsPerLiquidity (evm : EVM.State)
    (I : ExecutionEnv) :
    storageLocLoad evm
        (loc (observationsBaseSlot I) ⟨11, by decide⟩ ⟨20, by decide⟩
          (by decide) (.int uint160Int)) =
      .int (Int.ofNat (UInt256.land
        (UInt256.div
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (observationsBaseSlot I))
          (observationsShiftBytes 11))
        slot0Uint160Mask).toNat) := by
  rw [← show UInt256.ofNat (256 ^ (11 : Nat)) = observationsShiftBytes 11 by rfl]
  rw [← show UInt256.ofNat (256 ^ (20 : Nat) - 1) = slot0Uint160Mask by native_decide]
  simpa [loc, uint160Int] using
    storageLocLoad_uint_offset evm (observationsBaseSlot I) (11 : Fin 32) (20 : Fin 33)
      ⟨160, by decide⟩ (hbound := by decide) (by decide) (by decide)

theorem observationsStorageLocLoad_initialized (evm : EVM.State) (I : ExecutionEnv) :
    storageLocLoad evm
        (loc (observationsBaseSlot I) ⟨31, by decide⟩ ⟨1, by decide⟩
          (by decide) .bool) =
      wordToElem .bool
        (UInt256.land
          (UInt256.div
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (observationsBaseSlot I))
            (observationsShiftBytes 31))
          slot0Uint8Mask) := by
  rw [← show UInt256.ofNat (256 ^ (31 : Nat)) = observationsShiftBytes 31 by rfl]
  simpa [loc] using
    storageLocLoad_bool_offset evm (observationsBaseSlot I) (31 : Fin 32)
      (hbound := by decide) (by decide)

theorem uniswapV3PoolObservationsSourceBody {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hbound : (observationsArgWord I).toNat < 65535) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (observationsStore I) observationsTransition.body
      (.returned { contract := contract v, locals := observationsStore I }
        (initState cA gh bl σ σ₀ g A I)
        (some (observationsReturnValues σ I))) := by
  change ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (observationsStore I)
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (ltE (.var "arg0") (.intLit 65535)),
        .return [ .storage (observationsRawF (.var "arg0") "blockTimestamp"),
          .storage (observationsRawF (.var "arg0") "tickCumulative"),
          .storage (observationsRawF (.var "arg0") "secondsPerLiquidityCumulativeX128"),
          .storage (observationsRawF (.var "arg0") "initialized") ] ] _
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by simp [initState, hwv]))) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue
          (evalExpr_observations_bound_true (initState cA gh bl σ σ₀ g A I) I hbound)) <|
        ExecBlock.consReturn <| ExecStmt.return (by
          have hblock :
              evalExpr? (config v) { contract := contract v, locals := observationsStore I }
                (initState cA gh bl σ σ₀ g A I)
                (.storage (observationsRawF (.var "arg0") "blockTimestamp")) =
              .ok (.int (Int.ofNat (observationsBlockTimestampWord σ I).toNat)) := by
            apply evalExpr_storage_scalar_value
                (er := observationsRawEvaledRef I "blockTimestamp")
                (t := .int uint32Int)
                (loc := loc (observationsBaseSlot I) ⟨0, by decide⟩ ⟨4, by decide⟩
                  (by decide) (.int uint32Int))
            · simp [observationsStore, observationsRawF]
            · exact evalStorageRef_observationsRaw
                (v := v) (initState cA gh bl σ σ₀ g A I) I "blockTimestamp"
            · simp [observationsRawEvaledRef, contract, storageDecls, storageTypeAt?,
                storageTypeStep?, observationStructTy, uint32St]
            · funext evm
              simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
                observationsRawEvaledRef, observationsBaseSlot, loc]
            · simpa [initState, observationsBlockTimestampWord, observationsSlotWord,
                solcSlotWord] using
                observationsStorageLocLoad_blockTimestamp (initState cA gh bl σ σ₀ g A I) I
          have htick :
              evalExpr? (config v) { contract := contract v, locals := observationsStore I }
                (initState cA gh bl σ σ₀ g A I)
                (.storage (observationsRawF (.var "arg0") "tickCumulative")) =
              .ok (wordToElem (.int int56Int) (observationsTickStorageWord σ I)) := by
            apply evalExpr_storage_scalar_value
                (er := observationsRawEvaledRef I "tickCumulative")
                (t := .int int56Int)
                (loc := loc (observationsBaseSlot I) ⟨4, by decide⟩ ⟨7, by decide⟩
                  (by decide) (.int int56Int))
            · simp [observationsStore, observationsRawF]
            · exact evalStorageRef_observationsRaw
                (v := v) (initState cA gh bl σ σ₀ g A I) I "tickCumulative"
            · simp [observationsRawEvaledRef, contract, storageDecls, storageTypeAt?,
                storageTypeStep?, observationStructTy, int56St]
            · funext evm
              simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
                observationsRawEvaledRef, observationsBaseSlot, loc]
            · simpa [initState, observationsTickStorageWord, observationsTickRawWord,
                observationsSlotWord, solcSlotWord] using
                observationsStorageLocLoad_tickCumulative (initState cA gh bl σ σ₀ g A I) I
          have hseconds :
              evalExpr? (config v) { contract := contract v, locals := observationsStore I }
                (initState cA gh bl σ σ₀ g A I)
                (.storage (observationsRawF (.var "arg0")
                  "secondsPerLiquidityCumulativeX128")) =
              .ok (.int (Int.ofNat (observationsSecondsPerLiquidityWord σ I).toNat)) := by
            apply evalExpr_storage_scalar_value
                (er := observationsRawEvaledRef I "secondsPerLiquidityCumulativeX128")
                (t := .int uint160Int)
                (loc := loc (observationsBaseSlot I) ⟨11, by decide⟩ ⟨20, by decide⟩
                  (by decide) (.int uint160Int))
            · simp [observationsStore, observationsRawF]
            · exact evalStorageRef_observationsRaw
                (v := v) (initState cA gh bl σ σ₀ g A I)
                I "secondsPerLiquidityCumulativeX128"
            · simp [observationsRawEvaledRef, contract, storageDecls, storageTypeAt?,
                storageTypeStep?, observationStructTy, uint160St]
            · funext evm
              simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
                observationsRawEvaledRef, observationsBaseSlot, loc]
            · simpa [initState, observationsSecondsPerLiquidityWord, observationsSlotWord,
                solcSlotWord] using
                observationsStorageLocLoad_secondsPerLiquidity
                  (initState cA gh bl σ σ₀ g A I) I
          have hinit :
              evalExpr? (config v) { contract := contract v, locals := observationsStore I }
                (initState cA gh bl σ σ₀ g A I)
                (.storage (observationsRawF (.var "arg0") "initialized")) =
              .ok (wordToElem .bool (observationsInitializedRawWord σ I)) := by
            apply evalExpr_storage_scalar_value
                (er := observationsRawEvaledRef I "initialized")
                (t := .bool)
                (loc := loc (observationsBaseSlot I) ⟨31, by decide⟩ ⟨1, by decide⟩
                  (by decide) .bool)
            · simp [observationsStore, observationsRawF]
            · exact evalStorageRef_observationsRaw
                (v := v) (initState cA gh bl σ σ₀ g A I) I "initialized"
            · simp [observationsRawEvaledRef, contract, storageDecls, storageTypeAt?,
                storageTypeStep?, observationStructTy, boolSt]
            · funext evm
              simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
                observationsRawEvaledRef, observationsBaseSlot, loc]
            · simpa [initState, observationsInitializedRawWord, observationsSlotWord,
                solcSlotWord] using
                observationsStorageLocLoad_initialized (initState cA gh bl σ σ₀ g A I) I
          simp only [observationsReturnValues, Solm.evalExprs?.eq_def, hblock, htick,
            hseconds, hinit, EvalResult.bind, bind, pure])

theorem uniswapV3PoolObservationsSourceBodyOob {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hoob : 65535 ≤ (observationsArgWord I).toNat) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (observationsStore I) observationsTransition.body
      .reverted := by
  change ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (observationsStore I)
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (ltE (.var "arg0") (.intLit 65535)),
        .return [ .storage (observationsRawF (.var "arg0") "blockTimestamp"),
          .storage (observationsRawF (.var "arg0") "tickCumulative"),
          .storage (observationsRawF (.var "arg0") "secondsPerLiquidityCumulativeX128"),
          .storage (observationsRawF (.var "arg0") "initialized") ] ] _
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by simp [initState, hwv]))) <|
      ExecBlock.consRevert <|
        ExecStmt.requireFalse
          (evalExpr_observations_bound_false (initState cA gh bl σ σ₀ g A I) I hoob)

theorem observationsReturnEncoding (σ : AccountMap) (I : ExecutionEnv) :
    encodeReturnValues? [uint32, int56, uint160, boolTy]
        (observationsReturnValues σ I) =
      some (UInt256.toByteArray (observationsBlockTimestampWord σ I) ++
        UInt256.toByteArray (UInt256.signextend ⟨6⟩ (observationsTickReturnWord σ I)) ++
          UInt256.toByteArray (observationsSecondsPerLiquidityWord σ I) ++
            UInt256.toByteArray (slot0BoolReturnWord (observationsInitializedRawWord σ I))) := by
  have hwordBlock : EVM.word (observationsBlockTimestampWord σ I).toNat =
      observationsBlockTimestampWord σ I := u256_ofNat_toNat _
  have hwordSeconds : EVM.word (observationsSecondsPerLiquidityWord σ I).toNat =
      observationsSecondsPerLiquidityWord σ I := u256_ofNat_toNat _
  have hblockLt : (observationsBlockTimestampWord σ I).toNat < EVM.twoPow 32 := by
    simpa [observationsBlockTimestampWord] using
      observationsUint32Mask_bound (observationsSlotWord σ I)
  have hsecondsLt : (observationsSecondsPerLiquidityWord σ I).toNat <
      EVM.twoPow 160 := by
    simpa [observationsSecondsPerLiquidityWord] using
      slot0Uint160Mask_bound
        (UInt256.div (observationsSlotWord σ I) (observationsShiftBytes 11))
  have hencBlock :
      encodeABIValue? uint32
          (.int (Int.ofNat (observationsBlockTimestampWord σ I).toNat)) =
        some (EVM.Word.toBytesBE (observationsBlockTimestampWord σ I)) := by
    simp [uint32, uint32Int, encodeABIValue?, encodeABIWord?, hwordBlock, hblockLt]
  have hencTick :
      encodeABIValue? int56
          (wordToElem (.int int56Int) (observationsTickStorageWord σ I)) =
        some (EVM.Word.toBytesBE
          (UInt256.signextend ⟨6⟩ (observationsTickReturnWord σ I))) := by
    change encodeABIValue? int56
        (.int (observationsSint56Value (observationsTickStorageWord σ I))) =
      some (EVM.Word.toBytesBE
        (UInt256.signextend ⟨6⟩ (observationsTickReturnWord σ I)))
    have hge := observationsSint56Value_ge (observationsTickStorageWord σ I)
    have hlt := observationsSint56Value_lt (observationsTickStorageWord σ I)
    have hidem : UInt256.signextend ⟨6⟩ (observationsTickReturnWord σ I) =
        observationsTickReturnWord σ I := by
      dsimp [observationsTickReturnWord]
      exact observationsSignextendSix_idempotent (observationsTickRawWord σ I)
    have hword : EVM.wordOfInt
          (observationsSint56Value (observationsTickStorageWord σ I)) =
        UInt256.signextend ⟨6⟩ (observationsTickReturnWord σ I) := by
      rw [hidem]
      dsimp [observationsTickStorageWord, observationsTickReturnWord]
      exact observationsTickRawValue_wordOfInt (observationsTickRawWord σ I)
    simp only [int56, int56Int, encodeABIValue?, encodeABIWord?]
    rw [if_neg (by decide : 56 ≠ 0), if_pos]
    · rw [hword]
      rfl
    · constructor
      · simpa [EVM.twoPow] using hge
      · simpa [EVM.twoPow] using hlt
  have hencSeconds :
      encodeABIValue? uint160
          (.int (Int.ofNat (observationsSecondsPerLiquidityWord σ I).toNat)) =
        some (EVM.Word.toBytesBE (observationsSecondsPerLiquidityWord σ I)) := by
    simp [uint160, uint160Int, encodeABIValue?, encodeABIWord?, hwordSeconds,
      hsecondsLt]
  have hencInitialized :
      encodeABIValue? boolTy (wordToElem .bool (observationsInitializedRawWord σ I)) =
        some (EVM.Word.toBytesBE
          (slot0BoolReturnWord (observationsInitializedRawWord σ I))) :=
    slot0BoolABIEncoding (observationsInitializedRawWord σ I)
  have hhead : abiTupleHeadSize? [uint32, int56, uint160, boolTy] = some 128 := by
    native_decide
  have hdyn32 : isDynamicABIType uint32 = false := by native_decide
  have hdyn56 : isDynamicABIType int56 = false := by native_decide
  have hdyn160 : isDynamicABIType uint160 = false := by native_decide
  have hdynBool : isDynamicABIType boolTy = false := by native_decide
  rw [toByteArray_eq_toBytesBE (observationsBlockTimestampWord σ I),
    toByteArray_eq_toBytesBE (UInt256.signextend ⟨6⟩ (observationsTickReturnWord σ I)),
    toByteArray_eq_toBytesBE (observationsSecondsPerLiquidityWord σ I),
    toByteArray_eq_toBytesBE (slot0BoolReturnWord (observationsInitializedRawWord σ I))]
  simp only [observationsReturnValues, encodeReturnValues?, encodeABIValues?,
    encodeABIValuesFrom?, hhead, hencBlock, hencTick, hencSeconds, hencInitialized,
    hdyn32, hdyn56, hdyn160, hdynBool, bind, Option.bind, Bool.false_eq_true, if_false,
    List.nil_append, List.append_nil]
  apply congrArg some
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

theorem uniswapV3PoolObservationsValueTransport {σ_evm σ_solm : AccountMap}
    {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    some (observationsReturnValues σ_solm I) =
      some (observationsReturnValues σ_evm I) := by
  have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner
    (observationsBaseSlot I) (⟨0⟩ : UInt256)
  dsimp [observationsReturnValues, observationsBlockTimestampWord,
    observationsTickStorageWord, observationsTickRawWord, observationsSecondsPerLiquidityWord,
    observationsInitializedRawWord, observationsSlotWord, solcSlotWord]
  rw [← hslot]

theorem uniswapV3PoolObservationsBodyCore {v : PoolImmutables}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsel : (uniswapV3PoolSelBytes 4 == I.calldata.extract 0 4) = true) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdispatch := uniswapV3PoolDispatch_observations (v := v) (cd := I.calldata) hsel
  have hvalue := uniswapV3PoolObservationsValueTransport (σ_evm := σ_evm)
    (σ_solm := σ_solm) (I := I) hAccounts
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdecode := uniswapV3PoolObservationsDecodeOk (v := v) (I := I) hsz36
    by_cases hbound : (observationsArgWord I).toNat < 65535
    · have hbody := uniswapV3PoolObservationsSourceBody (v := v) (cA := cA)
        (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) hwv hbound
      have hrd := uniswapV3PoolObservationsEvm (v := v) (code := code) (cA := cA)
        (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) hpatch hcode hwv hsz hsize hsel hsz36 hbound
      exact hrd.reEquivExecutionTransport hcode hdispatch hdecode hbody hvalue hAccounts
        (by
          rw [show observationsTransition.returnType = [uint32, int56, uint160, boolTy] from rfl]
          exact returnEquiv.returned rfl (observationsReturnEncoding σ_evm I))
    · have hoob : 65535 ≤ (observationsArgWord I).toNat := by omega
      have hbody := uniswapV3PoolObservationsSourceBodyOob (v := v) (cA := cA)
        (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) hwv hoob
      have hrd := uniswapV3PoolObservationsEvmOob (v := v) (code := code) (cA := cA)
        (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) hpatch hcode hwv hsz hsize hsel hsz36 hoob
      exact hrd.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hshort : I.calldata.size < 36 := by omega
    have hdecode := uniswapV3PoolObservationsDecodeShort (v := v) (I := I) hshort
    have hrd := uniswapV3PoolObservationsEvmDecodeShort (v := v) (code := code)
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) hpatch hcode hwv hsz hsize hsel hshort
    exact hrd.reEquivDecodingFailed hcode hdispatch hdecode

end Benchmarks.UniswapV3Pool
