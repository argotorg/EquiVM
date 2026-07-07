import Benchmarks.UniswapV3Pool.SetFeeProtocolOwnerCall
import Benchmarks.UniswapV3Pool.Slot0

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.UniswapV3Pool

abbrev initializeUint160Mask : UInt256 := UInt256.ofNat (2 ^ 160 - 1)

abbrev initializeArgWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land (calldataWord I.calldata 4) initializeUint160Mask

abbrev initializeArgValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (initializeArgWord I).toNat)

abbrev initializeStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "sqrtPriceX96" (initializeArgValue I)

theorem initializeUint160Mask_toNat :
    initializeUint160Mask.toNat = 2 ^ 160 - 1 := by
  exact ulit_toNat' _ (by norm_num [UInt256.size])

theorem initializeUint160Mask_decode (w : UInt256) :
    (UInt256.land w initializeUint160Mask).toNat = w.toNat % EVM.twoPow 160 := by
  rw [u256_land_toNat, initializeUint160Mask_toNat, nat_land_mask_eq_mod]
  exact Nat.mod_eq_of_lt (by
    exact lt_trans (Nat.mod_lt _ (by norm_num [EVM.twoPow]))
      (by norm_num [EVM.twoPow, UInt256.size]))

theorem decodeScalarWordWithMode_uint160_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeScalarWordWithMode? DecodeMode.legacySolc05 uint160 bytes start =
      some
        (.int (Int.ofNat
          (UInt256.land (ABI.bytesToWord ((bytes.drop start).take 32))
            initializeUint160Mask).toNat),
          start + 32) := by
  simp only [decodeScalarWordWithMode?]
  unfold readWord? readBytes? uint160 uint160Int
  rw [if_pos hlen]
  simp only [bind, Option.bind]
  unfold decodeABIWord?
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
  rw [initializeUint160Mask_decode]
  rfl

theorem decodeScalarWordsWithMode_uint160_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32) :
    decodeScalarWordsWithMode? DecodeMode.legacySolc05 [uint160] bytes 0 =
      some
        [ .int (Int.ofNat
            (UInt256.land (ABI.bytesToWord (bytes.take 32))
              initializeUint160Mask).toNat) ] := by
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWordWithMode_uint160_ok (bytes := bytes) (start := 0) (by simpa using hlen0)]
  simp only [List.drop_zero, bind, Option.bind]

theorem decodeScalarWordsWithMode_uint160_none_short {bytes : List UInt8}
    (hshort : bytes.length < 32) :
    decodeScalarWordsWithMode? DecodeMode.legacySolc05 [uint160] bytes 0 = none := by
  simp only [decodeScalarWordsWithMode?]
  have htake0n : ¬ (bytes.take 32).length = 32 := by
    rw [List.length_take]
    omega
  unfold decodeScalarWordWithMode? readWord? readBytes? uint160 uint160Int
  simp only [List.drop_zero]
  rw [if_neg htake0n]
  simp only [Option.bind, bind]

theorem uniswapV3PoolInitializeDecodeOk {v : PoolImmutables} {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode
      (initializeTransition.params.map Param.name)
      (transitionSignature initializeTransition).paramTypes I.calldata =
        some (initializeStore I) := by
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
    (names := initializeTransition.params.map Param.name)
    (types := (transitionSignature initializeTransition).paramTypes)
    (cd := I.calldata)]
  · rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
    change (match decodeScalarWordsWithMode? DecodeMode.legacySolc05 [uint160]
        (I.calldata.toList.drop 4) 0 with
      | some values => decodeCalldata.insertValues ["sqrtPriceX96"] values ∅
      | none => none) = some (initializeStore I)
    rw [decodeScalarWordsWithMode_uint160_ok (bytes := I.calldata.toList.drop 4) htake4]
    simp [decodeCalldata.insertValues, initializeStore, initializeArgValue, initializeArgWord]
    rw [hword4]
  · simp [initializeTransition, transitionSignature, isABIScalarWordType, uint160]

theorem uniswapV3PoolInitializeDecodeShort {v : PoolImmutables} {I : ExecutionEnv}
    (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode (config v).abiDecodeMode
      (initializeTransition.params.map Param.name)
      (transitionSignature initializeTransition).paramTypes I.calldata = none := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [show (config v).abiDecodeMode = DecodeMode.legacySolc05 from rfl]
  rw [decodeCalldataWithMode_legacyScalarWords_eq
    (names := initializeTransition.params.map Param.name)
    (types := (transitionSignature initializeTransition).paramTypes)
    (cd := I.calldata)]
  · by_cases hsz4 : I.calldata.size < 4
    · rw [if_pos (by rw [htlen]; omega : I.calldata.toList.length < 4)]
    · rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
      change (match decodeScalarWordsWithMode? DecodeMode.legacySolc05 [uint160]
          (I.calldata.toList.drop 4) 0 with
        | some values => decodeCalldata.insertValues ["sqrtPriceX96"] values ∅
        | none => none) = none
      rw [decodeScalarWordsWithMode_uint160_none_short
        (bytes := I.calldata.toList.drop 4) (by rw [List.length_drop, htlen]; omega)]
  · simp [initializeTransition, transitionSignature, isABIScalarWordType, uint160]

theorem uniswapV3PoolInitializePatchDisjointBeforeFirst {v : PoolImmutables}
    {pc : UInt256} {n : Nat} (hhi : pc.toNat + n ≤ 2258) :
    ∀ p ∈ patches v, pc.toNat + n ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  all_goals omega

theorem uniswapV3PoolInitializeDecodeNoArg {v : PoolImmutables} {code : ByteArray}
    {pc : UInt256} {byte : UInt8} {op : Operation}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hhi : pc.toNat + 1 ≤ 2258)
    (hgetTemplate : uniswapV3PoolBytecode.get? pc.toNat = some byte)
    (hparse : (some byte >>= parseInstr) = some op)
    (harg : argOnNBytesOfInstr op = 0) :
    decode code pc = some (op, .none) := by
  refine uniswapV3PoolDecodePatchedNoArg hpatch ?_ ?_ hgetTemplate hparse harg
  · have hsize : 2258 ≤ uniswapV3PoolBytecode.size := by native_decide
    omega
  · exact uniswapV3PoolInitializePatchDisjointBeforeFirst (v := v) (n := 1) hhi

theorem uniswapV3PoolInitializeDecodePush1 {v : PoolImmutables} {code : ByteArray}
    {pc n : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hhi : pc.toNat + 2 ≤ 2258)
    (hgetTemplate : uniswapV3PoolBytecode.get? pc.toNat = some 0x60)
    (hval : uInt256OfByteArray
        (uniswapV3PoolBytecode.extract' pc.toNat.succ (pc.toNat.succ + 1)) = n) :
    decode code pc = some (.Push .PUSH1, some (n, 1)) := by
  refine uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush1 hpatch ?_ ?_
    hgetTemplate hval
  · have hsize : 2258 ≤ uniswapV3PoolBytecode.size := by native_decide
    omega
  · exact uniswapV3PoolInitializePatchDisjointBeforeFirst (v := v) (n := 2) hhi

theorem uniswapV3PoolInitializeDecodePush2 {v : PoolImmutables} {code : ByteArray}
    {pc n : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hhi : pc.toNat + 3 ≤ 2258)
    (hgetTemplate : uniswapV3PoolBytecode.get? pc.toNat = some 0x61)
    (hval : uInt256OfByteArray
        (uniswapV3PoolBytecode.extract' pc.toNat.succ (pc.toNat.succ + 2)) = n) :
    decode code pc = some (.Push .PUSH2, some (n, 2)) := by
  refine uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush2 hpatch ?_ ?_
    hgetTemplate hval
  · have hsize : 2258 ≤ uniswapV3PoolBytecode.size := by native_decide
    omega
  · exact uniswapV3PoolInitializePatchDisjointBeforeFirst (v := v) (n := 3) hhi

theorem uniswapV3PoolInitializePatchDisjointBody {v : PoolImmutables}
    {pc : UInt256} {n : Nat} (hlo : 10597 ≤ pc.toNat) (hhi : pc.toNat + n ≤ 11259) :
    ∀ p ∈ patches v, pc.toNat + n ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  all_goals omega

theorem uniswapV3PoolInitializePatchDisjointGetTickAtSqrtRatio {v : PoolImmutables}
    {pc : UInt256} {n : Nat} (hlo : 13989 ≤ pc.toNat) (hhi : pc.toNat + n ≤ 15650) :
    ∀ p ∈ patches v, pc.toNat + n ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  all_goals omega

private theorem uniswapV3PoolInitializePatchPreservesJumpDest10715 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨10715⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolInitializePatchPreservesJumpDest10782 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨10782⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolInitializePatchPreservesJumpDest13989 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨13989⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolInitializePatchPreservesJumpDest14049 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨14049⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolInitializePatchPreservesJumpDest14102 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨14102⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched10715 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨10715⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest10715

theorem uniswapV3PoolJumpDestPatched10782 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨10782⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest10782

theorem uniswapV3PoolJumpDestPatched13989 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨13989⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest13989

theorem uniswapV3PoolJumpDestPatched14049 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨14049⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest14049

theorem uniswapV3PoolJumpDestPatched14102 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨14102⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest14102

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolDispatch_initialize {v : PoolImmutables} {cd : ByteArray}
    (hsel : (uniswapV3PoolSelBytes 25 == cd.extract 0 4) = true) :
    dispatchMsg (contract v) cd = some initializeTransition := by
  apply dispatchMsg_eq_some_of_split
    (pre := [burnTransition, collectTransition v, collectprotocolTransition v,
      factoryTransition v, feeTransition v, feegrowthglobal0X128Transition,
      feegrowthglobal1X128Transition, flashTransition v,
      increaseobservationcardinalitynextTransition v])
    (post := [liquidityTransition, maxliquiditypertickTransition v,
      mintTransition v, observationsTransition, observeTransition v, positionsTransition,
      protocolfeesTransition, setfeeprotocolTransition v, slot0Transition,
      snapshotcumulativesinsideTransition v, swapTransition v, tickbitmapTransition,
      tickspacingTransition v, ticksTransition, token0Transition v, token1Transition v])
  · simp [contract, transitions]
  · intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [selectorOf, burnSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 17) (j := 25)
          (by native_decide) hsel
    · rw [selectorOf, collectSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 10) (j := 25)
          (by native_decide) hsel
    · rw [selectorOf, collectProtocolSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 15) (j := 25)
          (by native_decide) hsel
    · rw [selectorOf, factorySelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 19) (j := 25)
          (by native_decide) hsel
    · rw [selectorOf, feeSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 22) (j := 25)
          (by native_decide) hsel
    · rw [selectorOf, feeGrowthGlobal0X128SelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 23) (j := 25)
          (by native_decide) hsel
    · rw [selectorOf, feeGrowthGlobal1X128SelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 8) (j := 25)
          (by native_decide) hsel
    · rw [selectorOf, flashSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 9) (j := 25)
          (by native_decide) hsel
    · rw [selectorOf, increaseObservationCardinalityNextSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 5) (j := 25)
          (by native_decide) hsel
  · rw [selectorOf, initializeSelectorBytes]
    simpa [uniswapV3PoolSelBytes] using hsel

theorem uniswapV3PoolInitializeReachEntry {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 25 == I.calldata.extract 0 4) = true) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨2218⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := uniswapV3PoolReachSelector32
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize
  have hword : solcSelectorWord I = uniswapV3PoolSelNat 25 := by
    simpa [uniswapV3PoolSelBytes, uniswapV3PoolSelNat] using
      solcSelectorWord_eq_of_beq I hsz 0xf6 0x37 0x73 0x1d
        (uniswapV3PoolSelNat 25) (by native_decide) hsel
  have hgt32 : UInt256.gt (armSelNat code ⟨32⟩) (solcSelectorWord I) = ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h43 := uniswapV3PoolSelectorSplitNotTakenTo (next := ⟨43⟩) hpatch h32 hgt32
  have hgt43 : UInt256.gt (armSelNat code ⟨43⟩) (solcSelectorWord I) = ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h54 := uniswapV3PoolSelectorSplitNotTakenTo (next := ⟨54⟩) hpatch h43 hgt43
  have hgt54 : UInt256.gt (armSelNat code ⟨54⟩) (solcSelectorWord I) = ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h65 := uniswapV3PoolSelectorSplitNotTakenTo (next := ⟨65⟩) hpatch h54 hgt54
  have hmiss22 : (uniswapV3PoolSelBytes 22 == I.calldata.extract 0 4) = false :=
    uniswapV3PoolSelectorMissOfHit I (by native_decide) hsel
  have h76 := uniswapV3PoolSelectorArmMissToOf (i := 22) (next := ⟨76⟩)
    hpatch hsz hmiss22 h65
  have hmiss23 : (uniswapV3PoolSelBytes 23 == I.calldata.extract 0 4) = false :=
    uniswapV3PoolSelectorMissOfHit I (by native_decide) hsel
  have h87 := uniswapV3PoolSelectorArmMissToOf (i := 23) (next := ⟨87⟩)
    hpatch hsz hmiss23 h76
  have hmiss24 : (uniswapV3PoolSelBytes 24 == I.calldata.extract 0 4) = false :=
    uniswapV3PoolSelectorMissOfHit I (by native_decide) hsel
  have h98 := uniswapV3PoolSelectorArmMissToOf (i := 24) (next := ⟨98⟩)
    hpatch hsz hmiss24 h87
  have h2218 := uniswapV3PoolSelectorArmHitTo (i := 25) (target := ⟨2218⟩)
    hpatch hsz hsel h98
  exact ⟨_, _, h2218⟩

theorem uniswapV3PoolInitializeEvmDecodeShort {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 25 == I.calldata.extract 0 4) = true)
    (hshort : I.calldata.size < 36) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  have hreach := uniswapV3PoolInitializeReachEntry
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
    (entry := ⟨2218⟩) (ret := ⟨857⟩) (decoded := ⟨2240⟩) hreach
    (by
      refine uniswapV3PoolInitializeDecodeNoArg (pc := ⟨2218⟩) (byte := 0x5b)
        (op := .JUMPDEST) hpatch (by native_decide) ?_ ?_ ?_
      all_goals native_decide)
    (by
      exact uniswapV3PoolInitializeDecodePush2 (pc := ⟨2219⟩) (n := ⟨857⟩)
        hpatch (by native_decide) (by native_decide) (by native_decide))
    (by
      exact uniswapV3PoolInitializeDecodePush1 (pc := ⟨2222⟩) (n := ⟨4⟩)
        hpatch (by native_decide) (by native_decide) (by native_decide))
    (by
      refine uniswapV3PoolInitializeDecodeNoArg (pc := ⟨2224⟩) (byte := 0x80)
        (op := .DUP1) hpatch (by native_decide) ?_ ?_ ?_
      all_goals native_decide)
    (by
      refine uniswapV3PoolInitializeDecodeNoArg (pc := ⟨2225⟩) (byte := 0x36)
        (op := .CALLDATASIZE) hpatch (by native_decide) ?_ ?_ ?_
      all_goals native_decide)
    (by
      refine uniswapV3PoolInitializeDecodeNoArg (pc := ⟨2226⟩) (byte := 0x03)
        (op := .SUB) hpatch (by native_decide) ?_ ?_ ?_
      all_goals native_decide)
    (by
      exact uniswapV3PoolInitializeDecodePush1 (pc := ⟨2227⟩) (n := ⟨32⟩)
        hpatch (by native_decide) (by native_decide) (by native_decide))
    (by
      refine uniswapV3PoolInitializeDecodeNoArg (pc := ⟨2229⟩) (byte := 0x81)
        (op := .DUP2) hpatch (by native_decide) ?_ ?_ ?_
      all_goals native_decide)
    (by
      refine uniswapV3PoolInitializeDecodeNoArg (pc := ⟨2230⟩) (byte := 0x10)
        (op := .LT) hpatch (by native_decide) ?_ ?_ ?_
      all_goals native_decide)
    (by
      refine uniswapV3PoolInitializeDecodeNoArg (pc := ⟨2231⟩) (byte := 0x15)
        (op := .ISZERO) hpatch (by native_decide) ?_ ?_ ?_
      all_goals native_decide)
    (by
      exact uniswapV3PoolInitializeDecodePush2 (pc := ⟨2232⟩) (n := ⟨2240⟩)
        hpatch (by native_decide) (by native_decide) (by native_decide))
    (by
      refine uniswapV3PoolInitializeDecodeNoArg (pc := ⟨2235⟩) (byte := 0x57)
        (op := .JUMPI) hpatch (by native_decide) ?_ ?_ ?_
      all_goals native_decide)
    (by
      exact uniswapV3PoolInitializeDecodePush1 (pc := ⟨2236⟩) (n := ⟨0⟩)
        hpatch (by native_decide) (by native_decide) (by native_decide))
    (by
      refine uniswapV3PoolInitializeDecodeNoArg (pc := ⟨2238⟩) (byte := 0x80)
        (op := .DUP1) hpatch (by native_decide) ?_ ?_ ?_
      all_goals native_decide)
    (by
      refine uniswapV3PoolInitializeDecodeNoArg (pc := ⟨2239⟩) (byte := 0xfd)
        (op := .REVERT) hpatch (by native_decide) ?_ ?_ ?_
      all_goals native_decide)
    hlt

set_option maxHeartbeats 3000000 in
theorem uniswapV3PoolInitializeExternalLenOk {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨2218⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨2240⟩
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ⟨857⟩ ::
        [solcSelectorWord I])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  exact RD.solcExternalStaticArgsLenOk (need := ⟨32⟩)
    (entry := ⟨2218⟩) (ret := ⟨857⟩) (decoded := ⟨2240⟩) hreach
    (by
      refine uniswapV3PoolInitializeDecodeNoArg (pc := ⟨2218⟩) (byte := 0x5b)
        (op := .JUMPDEST) hpatch (by native_decide) ?_ ?_ ?_
      all_goals native_decide)
    (by
      exact uniswapV3PoolInitializeDecodePush2 (pc := ⟨2219⟩) (n := ⟨857⟩)
        hpatch (by native_decide) (by native_decide) (by native_decide))
    (by
      exact uniswapV3PoolInitializeDecodePush1 (pc := ⟨2222⟩) (n := ⟨4⟩)
        hpatch (by native_decide) (by native_decide) (by native_decide))
    (by
      refine uniswapV3PoolInitializeDecodeNoArg (pc := ⟨2224⟩) (byte := 0x80)
        (op := .DUP1) hpatch (by native_decide) ?_ ?_ ?_
      all_goals native_decide)
    (by
      refine uniswapV3PoolInitializeDecodeNoArg (pc := ⟨2225⟩) (byte := 0x36)
        (op := .CALLDATASIZE) hpatch (by native_decide) ?_ ?_ ?_
      all_goals native_decide)
    (by
      refine uniswapV3PoolInitializeDecodeNoArg (pc := ⟨2226⟩) (byte := 0x03)
        (op := .SUB) hpatch (by native_decide) ?_ ?_ ?_
      all_goals native_decide)
    (by
      exact uniswapV3PoolInitializeDecodePush1 (pc := ⟨2227⟩) (n := ⟨32⟩)
        hpatch (by native_decide) (by native_decide) (by native_decide))
    (by
      refine uniswapV3PoolInitializeDecodeNoArg (pc := ⟨2229⟩) (byte := 0x81)
        (op := .DUP2) hpatch (by native_decide) ?_ ?_ ?_
      all_goals native_decide)
    (by
      refine uniswapV3PoolInitializeDecodeNoArg (pc := ⟨2230⟩) (byte := 0x10)
        (op := .LT) hpatch (by native_decide) ?_ ?_ ?_
      all_goals native_decide)
    (by
      refine uniswapV3PoolInitializeDecodeNoArg (pc := ⟨2231⟩) (byte := 0x15)
        (op := .ISZERO) hpatch (by native_decide) ?_ ?_ ?_
      all_goals native_decide)
    (by
      exact uniswapV3PoolInitializeDecodePush2 (pc := ⟨2232⟩) (n := ⟨2240⟩)
        hpatch (by native_decide) (by native_decide) (by native_decide))
    (by
      refine uniswapV3PoolInitializeDecodeNoArg (pc := ⟨2235⟩) (byte := 0x57)
        (op := .JUMPI) hpatch (by native_decide) ?_ ?_ ?_
      all_goals native_decide)
    (uniswapV3PoolJumpDestPatched2258 hpatch (by native_decide))
    (solcDecodeLenCheckOkUnsigned (by simpa using hsz36) hsize)

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolInitializeDecodedReachRoutine {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {de ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨2240⟩ (de :: ⟨4⟩ :: ret :: R) mem aw rdata acc k C)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨10715⟩ (initializeArgWord ee :: ret :: R)
      mem aw rdata acc k' C' := by
  have harg :
      UInt256.land initializeUint160Mask (calldataWord ee.calldata 4) =
        initializeArgWord ee := by
    rw [initializeArgWord, u256_land_comm]
  have rd2241 : RD code ee g s0 ⟨2241⟩ (de :: ⟨4⟩ :: ret :: R)
      mem aw rdata acc (k + 1) (C + 1) := by
    simpa using h.jumpdest
      (by
        refine uniswapV3PoolInitializeDecodeNoArg (pc := ⟨2240⟩) (byte := 0x5b)
          (op := .JUMPDEST) hpatch (by native_decide) ?_ ?_ ?_
        all_goals native_decide)
      (by evm_ov)
  have rd2242 : RD code ee g s0 ⟨2242⟩ (⟨4⟩ :: ret :: R)
      mem aw rdata acc (k + 1 + 1) (C + 1 + 2) := by
    simpa using rd2241.pop
      (by
        refine uniswapV3PoolInitializeDecodeNoArg (pc := ⟨2241⟩) (byte := 0x50)
          (op := .POP) hpatch (by native_decide) ?_ ?_ ?_
        all_goals native_decide)
      (by evm_ov)
  have rd2243 : RD code ee g s0 ⟨2243⟩ (calldataWord ee.calldata 4 :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1) (C + 1 + 2 + 3) := by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide] using
      (rd2242.calldataload
        (by
          refine uniswapV3PoolInitializeDecodeNoArg (pc := ⟨2242⟩) (byte := 0x35)
            (op := .CALLDATALOAD) hpatch (by native_decide) ?_ ?_ ?_
          all_goals native_decide)
        (by evm_ov))
  have rd2245 : RD code ee g s0 ⟨2245⟩
      (⟨1⟩ :: calldataWord ee.calldata 4 :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1 + 1) (C + 1 + 2 + 3 + 3) := by
    simpa using rd2243.push1 ⟨1⟩
      (uniswapV3PoolInitializeDecodePush1 (pc := ⟨2243⟩) (n := ⟨1⟩)
        hpatch (by native_decide) (by native_decide) (by native_decide))
      (by evm_ov)
  have rd2247 : RD code ee g s0 ⟨2247⟩
      (⟨1⟩ :: ⟨1⟩ :: calldataWord ee.calldata 4 :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1 + 1 + 1) (C + 1 + 2 + 3 + 3 + 3) := by
    simpa using rd2245.push1 ⟨1⟩
      (uniswapV3PoolInitializeDecodePush1 (pc := ⟨2245⟩) (n := ⟨1⟩)
        hpatch (by native_decide) (by native_decide) (by native_decide))
      (by
        have h := hov
        simp only [List.length_cons] at h ⊢
        omega)
  have rd2249 : RD code ee g s0 ⟨2249⟩
      (⟨160⟩ :: ⟨1⟩ :: ⟨1⟩ :: calldataWord ee.calldata 4 :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1 + 1 + 1 + 1)
      (C + 1 + 2 + 3 + 3 + 3 + 3) := by
    simpa using rd2247.push1 ⟨160⟩
      (uniswapV3PoolInitializeDecodePush1 (pc := ⟨2247⟩) (n := ⟨160⟩)
        hpatch (by native_decide) (by native_decide) (by native_decide))
      (by
        have h := hov
        simp only [List.length_cons] at h ⊢
        omega)
  have rd2250 := by
    simpa using rd2249.shl
      (by
        refine uniswapV3PoolInitializeDecodeNoArg (pc := ⟨2249⟩) (byte := 0x1b)
          (op := .SHL) hpatch (by native_decide) ?_ ?_ ?_
        all_goals native_decide)
      (by
        have h := hov
        simp only [List.length_cons] at h ⊢
        omega)
  have rd2251 := by
    simpa [initializeUint160Mask] using rd2250.sub
      (by
        refine uniswapV3PoolInitializeDecodeNoArg (pc := ⟨2250⟩) (byte := 0x03)
          (op := .SUB) hpatch (by native_decide) ?_ ?_ ?_
        all_goals native_decide)
      (by evm_ov)
  have rd2252 : RD code ee g s0 ⟨2252⟩ (initializeArgWord ee :: ret :: R)
      mem aw rdata acc
      (k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
      (C + 1 + 2 + 3 + 3 + 3 + 3 + 3 + 3 + 3) := by
    simpa [harg, initializeUint160Mask, u256_land_comm,
      show (⟨2249⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ : UInt256) = ⟨2252⟩ by native_decide] using rd2251.and
      (by
        refine uniswapV3PoolInitializeDecodeNoArg (pc := ⟨2251⟩) (byte := 0x16)
          (op := .AND) hpatch (by native_decide) ?_ ?_ ?_
        all_goals native_decide)
      (by
        simp only [List.length_cons]
        omega)
  have rd2255 := by
    simpa using rd2252.push2 ⟨10715⟩
      (uniswapV3PoolInitializeDecodePush2 (pc := ⟨2252⟩) (n := ⟨10715⟩)
        hpatch (by native_decide) (by native_decide) (by native_decide))
      (by evm_ov)
  exact ⟨_, _, rd2255.jump
    (by
      refine uniswapV3PoolInitializeDecodeNoArg (pc := ⟨2255⟩) (byte := 0x56)
        (op := .JUMP) hpatch (by native_decide) ?_ ?_ ?_
      all_goals native_decide)
    (uniswapV3PoolJumpDestPatched10715 hpatch)
    (by evm_ov)⟩

private theorem uniswapV3PoolInitializeAlreadyInitializedRevertTailWf
    {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcErrorStringRevertTailWf code ⟨10733⟩ ⟨2⟩ ⟨16713⟩ ⟨240⟩ .PUSH2 2 := by
  have hdecode {pc : UInt256} (hlo : 10597 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 11259) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 11259 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointBody hlo hhi)]
  dsimp [solcErrorStringRevertTailWf]
  repeat' constructor
  all_goals
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide

theorem uniswapV3PoolInitializeAlreadyInitializedRevert {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨10715⟩ (initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hnz : slot0SqrtPriceX96Word σ ee ≠ ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    RDrev code g s0 := by
  have hdecode {pc : UInt256} (hlo : 10597 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 11259) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 11259 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointBody hlo hhi)]
  have hd10715 : decode code ⟨10715⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10716 : decode code ⟨10716⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10718 : decode code ⟨10718⟩ = some (.SLOAD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10719 : decode code ⟨10719⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10721 : decode code ⟨10721⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10723 : decode code ⟨10723⟩ = some (.Push .PUSH1, some (⟨160⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10725 : decode code ⟨10725⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10726 : decode code ⟨10726⟩ = some (.SUB, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10727 : decode code ⟨10727⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10728 : decode code ⟨10728⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10729 : decode code ⟨10729⟩ = some (.Push .PUSH2, some (⟨10782⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10732 : decode code ⟨10732⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd10716 := by
    simpa using h.jumpdest hd10715 (by evm_ov)
  have rd10718 := by
    simpa using rd10716.push1 ⟨0⟩ hd10716 (by evm_ov)
  obtain ⟨_, _, rd10719₀⟩ := rd10718.sload hd10718 (by evm_ov)
  have rd10719 := by
    simpa [slot0SlotWord, solcSlotWord] using rd10719₀
  have rd10721 := by
    simpa using rd10719.push1 ⟨1⟩ hd10719 (by evm_ov)
  have rd10723 := by
    simpa using rd10721.push1 ⟨1⟩ hd10721 (by evm_ov)
  have rd10725 := by
    simpa using rd10723.push1 ⟨160⟩ hd10723 (by evm_ov)
  have rd10726 := by
    simpa using rd10725.shl hd10725 (by evm_ov)
  have rd10727 := by
    simpa [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        slot0Uint160Mask by native_decide] using rd10726.sub hd10726 (by evm_ov)
  have rd10728 := by
    simpa [slot0SqrtPriceX96Word, u256_land_comm] using rd10727.and hd10727
      (by evm_ov)
  have rd10729 := by
    simpa using rd10728.iszero hd10728 (by evm_ov)
  have rd10732 := by
    simpa using rd10729.push2 ⟨10782⟩ hd10729 (by evm_ov)
  have hnzGuard := by
    simpa [slot0SqrtPriceX96Word, slot0SlotWord, solcSlotWord, u256_land_comm] using hnz
  have rd10733 := rd10732.jumpiNT hd10732 (isZero_eq_zero_of_ne hnzGuard) (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨10733⟩) (len := ⟨2⟩) (rawWord := ⟨16713⟩) (shift := ⟨240⟩)
    (word := UInt256.shiftLeft ⟨16713⟩ ⟨240⟩) (op := .PUSH2) (width := 2)
    rd10733
    (uniswapV3PoolInitializeAlreadyInitializedRevertTailWf hpatch)
    (by native_decide)
    rfl
    solcFreePtrMem_size
    solcFreePtrMem_read64
    (by simp only [List.length_cons]; omega)

theorem uniswapV3PoolInitializeReachGetTickAtSqrtRatio {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨10715⟩ (initializeArgWord ee :: ret :: R)
      mem aw rdata acc k C)
    (hzero : slot0SqrtPriceX96Word acc.2 ee = ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨13989⟩
      (initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ :: initializeArgWord ee :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 10597 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 11259) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 11259 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointBody hlo hhi)]
  have hd10715 : decode code ⟨10715⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10716 : decode code ⟨10716⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10718 : decode code ⟨10718⟩ = some (.SLOAD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10719 : decode code ⟨10719⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10721 : decode code ⟨10721⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10723 : decode code ⟨10723⟩ = some (.Push .PUSH1, some (⟨160⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10725 : decode code ⟨10725⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10726 : decode code ⟨10726⟩ = some (.SUB, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10727 : decode code ⟨10727⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10728 : decode code ⟨10728⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10729 : decode code ⟨10729⟩ = some (.Push .PUSH2, some (⟨10782⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10732 : decode code ⟨10732⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10782 : decode code ⟨10782⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10783 : decode code ⟨10783⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10785 : decode code ⟨10785⟩ = some (.Push .PUSH2, some (⟨10793⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10788 : decode code ⟨10788⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10789 : decode code ⟨10789⟩ = some (.Push .PUSH2, some (⟨13989⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10792 : decode code ⟨10792⟩ = some (.JUMP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd10716 := by
    simpa using h.jumpdest hd10715 (by evm_ov)
  have rd10718 := by
    simpa using rd10716.push1 ⟨0⟩ hd10716 (by evm_ov)
  obtain ⟨_, _, rd10719₀⟩ := rd10718.sload hd10718 (by evm_ov)
  have rd10719 := by
    simpa [slot0SlotWord, solcSlotWord] using rd10719₀
  have rd10721 := by
    simpa using rd10719.push1 ⟨1⟩ hd10719 (by evm_ov)
  have rd10723 := by
    simpa using rd10721.push1 ⟨1⟩ hd10721 (by evm_ov)
  have rd10725 := by
    simpa using rd10723.push1 ⟨160⟩ hd10723 (by evm_ov)
  have rd10726 := by
    simpa using rd10725.shl hd10725 (by evm_ov)
  have rd10727 := by
    simpa [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        slot0Uint160Mask by native_decide] using rd10726.sub hd10726 (by evm_ov)
  have rd10728 := by
    simpa [slot0SqrtPriceX96Word, u256_land_comm] using rd10727.and hd10727
      (by evm_ov)
  have rd10729 := by
    simpa using rd10728.iszero hd10728 (by evm_ov)
  have rd10732 := by
    simpa using rd10729.push2 ⟨10782⟩ hd10729 (by evm_ov)
  have hzeroGuard := by
    simpa [slot0SqrtPriceX96Word, slot0SlotWord, solcSlotWord, u256_land_comm] using hzero
  have rd10782 := rd10732.jumpiT hd10732 (by
    rw [hzeroGuard]
    native_decide)
    (uniswapV3PoolJumpDestPatched10782 hpatch) (by evm_ov)
  have rd10783 := by
    simpa using rd10782.jumpdest hd10782 (by evm_ov)
  have rd10785 := by
    simpa using rd10783.push1 ⟨0⟩ hd10783 (by evm_ov)
  have rd10788 := by
    simpa using rd10785.push2 ⟨10793⟩ hd10785 (by evm_ov)
  have rd10789 := by
    simpa using rd10788.dup3 hd10788 (by simp only [List.length_cons]; omega)
  have rd10792 := by
    simpa using rd10789.push2 ⟨13989⟩ hd10789 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd10792.jump hd10792 (uniswapV3PoolJumpDestPatched13989 hpatch)
    (by simp only [List.length_cons]; omega)⟩

private theorem uniswapV3PoolGetTickAtSqrtRatioRRevertTailWf
    {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcErrorStringRevertTailWf code ⟨14054⟩ ⟨1⟩ ⟨41⟩ ⟨249⟩ .PUSH1 1 := by
  have hdecode {pc : UInt256} (hlo : 13989 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 15650) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 15650 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetTickAtSqrtRatio hlo hhi)]
  dsimp [solcErrorStringRevertTailWf]
  repeat' constructor
  all_goals
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide

theorem uniswapV3PoolGetTickAtSqrtRatioLowerRevert {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨13989⟩
      (initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ :: initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hlo : (initializeArgWord ee).toNat < 4295128739)
    (hov : R.length + 12 ≤ 1024) :
    RDrev code g s0 := by
  have hdecode {pc : UInt256} (hlo : 13989 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 15650) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 15650 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetTickAtSqrtRatio hlo hhi)]
  have hd13989 : decode code ⟨13989⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13990 : decode code ⟨13990⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13992 : decode code ⟨13992⟩ =
      some (.Push .PUSH5, some (⟨4295128739⟩, 5)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13998 : decode code ⟨13998⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14000 : decode code ⟨14000⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14002 : decode code ⟨14002⟩ = some (.Push .PUSH1, some (⟨160⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14004 : decode code ⟨14004⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14005 : decode code ⟨14005⟩ = some (.SUB, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14006 : decode code ⟨14006⟩ = some (.DUP4, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14007 : decode code ⟨14007⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14008 : decode code ⟨14008⟩ = some (.LT, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14009 : decode code ⟨14009⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14010 : decode code ⟨14010⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14011 : decode code ⟨14011⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14012 : decode code ⟨14012⟩ = some (.Push .PUSH2, some (⟨14049⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14015 : decode code ⟨14015⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14049 : decode code ⟨14049⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14050 : decode code ⟨14050⟩ = some (.Push .PUSH2, some (⟨14102⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14053 : decode code ⟨14053⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hargClean : UInt256.land (initializeArgWord ee) slot0Uint160Mask =
      initializeArgWord ee := by
    apply slot0Uint160Mask_clean
    rw [initializeArgWord, show initializeUint160Mask = slot0Uint160Mask by native_decide]
    exact slot0Uint160Mask_bound (calldataWord ee.calldata 4)
  have hlt : UInt256.lt (initializeArgWord ee) ⟨4295128739⟩ = ⟨1⟩ := by
    apply ult_one
    rw [show (⟨4295128739⟩ : UInt256).toNat = 4295128739 from by decide]
    exact hlo
  have rd13990 := by
    simpa using h.jumpdest hd13989 (by evm_ov)
  have rd13992 := by
    simpa using rd13990.push1 ⟨0⟩ hd13990 (by evm_ov)
  have rd13998 := by
    simpa using rd13992.pushConst (⟨4295128739⟩ : UInt256)
      (by native_decide : Operation.POp.PUSH5 ≠ .PUSH0) hd13992 (by evm_ov)
  have rd14000 := by
    simpa using rd13998.push1 ⟨1⟩ hd13998 (by evm_ov)
  have rd14002 := by
    simpa using rd14000.push1 ⟨1⟩ hd14000 (by
      simp only [List.length_cons]
      omega)
  have rd14004 := by
    simpa using rd14002.push1 ⟨160⟩ hd14002 (by
      simp only [List.length_cons]
      omega)
  have rd14005 := by
    simpa using rd14004.shl hd14004 (by
      simp only [List.length_cons]
      omega)
  have rd14006 := by
    simpa [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        slot0Uint160Mask by native_decide] using rd14005.sub hd14005 (by evm_ov)
  have rd14007 := by
    simpa using rd14006.dup4 hd14006 (by
      simp only [List.length_cons]
      omega)
  have rd14008 := by
    simpa [hargClean, u256_land_comm] using rd14007.and hd14007 (by
      simp only [List.length_cons]
      omega)
  have rd14009 := by
    simpa [hlt] using rd14008.lt hd14008 (by evm_ov)
  have rd14010 := by
    simpa using rd14009.dup1 hd14009 (by
      simp only [List.length_cons]
      omega)
  have rd14011 := by
    simpa using rd14010.iszero hd14010 (by evm_ov)
  have rd14012 := by
    simpa using rd14011.swap1 hd14011 (by
      simp only [List.length_cons]
      omega)
  have rd14015 := by
    simpa using rd14012.push2 ⟨14049⟩ hd14012 (by
      simp only [List.length_cons]
      omega)
  have rd14049 := rd14015.jumpiT hd14015 (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (uniswapV3PoolJumpDestPatched14049 hpatch) (by
      simp only [List.length_cons]
      omega)
  have rd14050 := by
    simpa using rd14049.jumpdest hd14049 (by
      simp only [List.length_cons]
      omega)
  have rd14053 := by
    simpa using rd14050.push2 ⟨14102⟩ hd14050 (by
      simp only [List.length_cons]
      omega)
  have rd14054 := by
    simpa [show (⟨14049⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ : UInt256) = ⟨14054⟩
        by native_decide] using
      rd14053.jumpiNT hd14053 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
        (by simp only [List.length_cons]; omega)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨14054⟩) (len := ⟨1⟩) (rawWord := ⟨41⟩) (shift := ⟨249⟩)
    (word := UInt256.shiftLeft ⟨41⟩ ⟨249⟩) (op := .PUSH1) (width := 1)
    rd14054
    (uniswapV3PoolGetTickAtSqrtRatioRRevertTailWf hpatch)
    (by native_decide)
    rfl
    solcFreePtrMem_size
    solcFreePtrMem_read64
    (by simp only [List.length_cons]; omega)

theorem uniswapV3PoolGetTickAtSqrtRatioUpperRevert {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨13989⟩
      (initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ :: initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hlo : 4295128739 ≤ (initializeArgWord ee).toNat)
    (hhi : 1461446703485210103287273052203988822378723970342 ≤
      (initializeArgWord ee).toNat)
    (hov : R.length + 12 ≤ 1024) :
    RDrev code g s0 := by
  have hdecode {pc : UInt256} (hlo : 13989 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 15650) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 15650 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetTickAtSqrtRatio hlo hhi)]
  have hd13989 : decode code ⟨13989⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13990 : decode code ⟨13990⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13992 : decode code ⟨13992⟩ =
      some (.Push .PUSH5, some (⟨4295128739⟩, 5)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13998 : decode code ⟨13998⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14000 : decode code ⟨14000⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14002 : decode code ⟨14002⟩ = some (.Push .PUSH1, some (⟨160⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14004 : decode code ⟨14004⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14005 : decode code ⟨14005⟩ = some (.SUB, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14006 : decode code ⟨14006⟩ = some (.DUP4, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14007 : decode code ⟨14007⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14008 : decode code ⟨14008⟩ = some (.LT, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14009 : decode code ⟨14009⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14010 : decode code ⟨14010⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14011 : decode code ⟨14011⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14012 : decode code ⟨14012⟩ = some (.Push .PUSH2, some (⟨14049⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14015 : decode code ⟨14015⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14016 : decode code ⟨14016⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14017 : decode code ⟨14017⟩ = some (.Push .PUSH20,
      some (⟨1461446703485210103287273052203988822378723970342⟩, 20)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14038 : decode code ⟨14038⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14040 : decode code ⟨14040⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14042 : decode code ⟨14042⟩ = some (.Push .PUSH1, some (⟨160⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14044 : decode code ⟨14044⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14045 : decode code ⟨14045⟩ = some (.SUB, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14046 : decode code ⟨14046⟩ = some (.DUP4, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14047 : decode code ⟨14047⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14048 : decode code ⟨14048⟩ = some (.LT, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14049 : decode code ⟨14049⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14050 : decode code ⟨14050⟩ = some (.Push .PUSH2, some (⟨14102⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14053 : decode code ⟨14053⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hargClean : UInt256.land (initializeArgWord ee) slot0Uint160Mask =
      initializeArgWord ee := by
    apply slot0Uint160Mask_clean
    rw [initializeArgWord, show initializeUint160Mask = slot0Uint160Mask by native_decide]
    exact slot0Uint160Mask_bound (calldataWord ee.calldata 4)
  have hltLow : UInt256.lt (initializeArgWord ee) ⟨4295128739⟩ = ⟨0⟩ := by
    apply ult_zero
    rw [show (⟨4295128739⟩ : UInt256).toNat = 4295128739 from by decide]
    exact hlo
  have hltHigh : UInt256.lt (initializeArgWord ee)
      ⟨1461446703485210103287273052203988822378723970342⟩ = ⟨0⟩ := by
    apply ult_zero
    rw [show (⟨1461446703485210103287273052203988822378723970342⟩ : UInt256).toNat =
        1461446703485210103287273052203988822378723970342 from by decide]
    exact hhi
  have rd13990 := by
    simpa using h.jumpdest hd13989 (by evm_ov)
  have rd13992 := by
    simpa using rd13990.push1 ⟨0⟩ hd13990 (by evm_ov)
  have rd13998 := by
    simpa using rd13992.pushConst (⟨4295128739⟩ : UInt256)
      (by native_decide : Operation.POp.PUSH5 ≠ .PUSH0) hd13992 (by evm_ov)
  have rd14000 := by
    simpa using rd13998.push1 ⟨1⟩ hd13998 (by evm_ov)
  have rd14002 := by
    simpa using rd14000.push1 ⟨1⟩ hd14000 (by
      simp only [List.length_cons]
      omega)
  have rd14004 := by
    simpa using rd14002.push1 ⟨160⟩ hd14002 (by
      simp only [List.length_cons]
      omega)
  have rd14005 := by
    simpa using rd14004.shl hd14004 (by
      simp only [List.length_cons]
      omega)
  have rd14006 := by
    simpa [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        slot0Uint160Mask by native_decide] using rd14005.sub hd14005 (by evm_ov)
  have rd14007 := by
    simpa using rd14006.dup4 hd14006 (by
      simp only [List.length_cons]
      omega)
  have rd14008 := by
    simpa [hargClean, u256_land_comm] using rd14007.and hd14007 (by
      simp only [List.length_cons]
      omega)
  have rd14009 := by
    simpa [hltLow] using rd14008.lt hd14008 (by evm_ov)
  have rd14010 := by
    simpa using rd14009.dup1 hd14009 (by
      simp only [List.length_cons]
      omega)
  have rd14011 := by
    simpa using rd14010.iszero hd14010 (by evm_ov)
  have rd14012 := by
    simpa using rd14011.swap1 hd14011 (by
      simp only [List.length_cons]
      omega)
  have rd14015 := by
    simpa using rd14012.push2 ⟨14049⟩ hd14012 (by
      simp only [List.length_cons]
      omega)
  have rd14016 := by
    simpa [show (⟨14012⟩ + UInt256.ofNat 3 + ⟨1⟩ : UInt256) = ⟨14016⟩
        by native_decide] using
      rd14015.jumpiNT hd14015 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
        (by simp only [List.length_cons]; omega)
  have rd14017 := by
    simpa using rd14016.pop hd14016 (by evm_ov)
  have rd14038 := by
    simpa using rd14017.pushConst
      (⟨1461446703485210103287273052203988822378723970342⟩ : UInt256)
      (by native_decide : Operation.POp.PUSH20 ≠ .PUSH0) hd14017 (by evm_ov)
  have rd14040 := by
    simpa using rd14038.push1 ⟨1⟩ hd14038 (by evm_ov)
  have rd14042 := by
    simpa using rd14040.push1 ⟨1⟩ hd14040 (by
      simp only [List.length_cons]
      omega)
  have rd14044 := by
    simpa using rd14042.push1 ⟨160⟩ hd14042 (by
      simp only [List.length_cons]
      omega)
  have rd14045 := by
    simpa using rd14044.shl hd14044 (by
      simp only [List.length_cons]
      omega)
  have rd14046 := by
    simpa [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        slot0Uint160Mask by native_decide] using rd14045.sub hd14045 (by evm_ov)
  have rd14047 := by
    simpa using rd14046.dup4 hd14046 (by
      simp only [List.length_cons]
      omega)
  have rd14048 := by
    simpa [hargClean, u256_land_comm] using rd14047.and hd14047 (by
      simp only [List.length_cons]
      omega)
  have rd14049 := by
    simpa [hltHigh] using rd14048.lt hd14048 (by evm_ov)
  have rd14050 := by
    simpa using rd14049.jumpdest hd14049 (by
      simp only [List.length_cons]
      omega)
  have rd14053 := by
    simpa using rd14050.push2 ⟨14102⟩ hd14050 (by
      simp only [List.length_cons]
      omega)
  have rd14054 := by
    simpa [show (⟨14049⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ : UInt256) = ⟨14054⟩
        by native_decide] using
      rd14053.jumpiNT hd14053 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
        (by simp only [List.length_cons]; omega)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨14054⟩) (len := ⟨1⟩) (rawWord := ⟨41⟩) (shift := ⟨249⟩)
    (word := UInt256.shiftLeft ⟨41⟩ ⟨249⟩) (op := .PUSH1) (width := 1)
    rd14054
    (uniswapV3PoolGetTickAtSqrtRatioRRevertTailWf hpatch)
    (by native_decide)
    rfl
    solcFreePtrMem_size
    solcFreePtrMem_read64
    (by simp only [List.length_cons]; omega)

theorem uniswapV3PoolGetTickAtSqrtRatioRangeOk {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨13989⟩
      (initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ :: initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hlo : 4295128739 ≤ (initializeArgWord ee).toNat)
    (hhi : (initializeArgWord ee).toNat <
      1461446703485210103287273052203988822378723970342)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨14102⟩
      (⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ :: initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 13989 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 15650) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 15650 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetTickAtSqrtRatio hlo hhi)]
  have hd13989 : decode code ⟨13989⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13990 : decode code ⟨13990⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13992 : decode code ⟨13992⟩ =
      some (.Push .PUSH5, some (⟨4295128739⟩, 5)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13998 : decode code ⟨13998⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14000 : decode code ⟨14000⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14002 : decode code ⟨14002⟩ = some (.Push .PUSH1, some (⟨160⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14004 : decode code ⟨14004⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14005 : decode code ⟨14005⟩ = some (.SUB, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14006 : decode code ⟨14006⟩ = some (.DUP4, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14007 : decode code ⟨14007⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14008 : decode code ⟨14008⟩ = some (.LT, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14009 : decode code ⟨14009⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14010 : decode code ⟨14010⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14011 : decode code ⟨14011⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14012 : decode code ⟨14012⟩ = some (.Push .PUSH2, some (⟨14049⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14015 : decode code ⟨14015⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14016 : decode code ⟨14016⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14017 : decode code ⟨14017⟩ = some (.Push .PUSH20,
      some (⟨1461446703485210103287273052203988822378723970342⟩, 20)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14038 : decode code ⟨14038⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14040 : decode code ⟨14040⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14042 : decode code ⟨14042⟩ = some (.Push .PUSH1, some (⟨160⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14044 : decode code ⟨14044⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14045 : decode code ⟨14045⟩ = some (.SUB, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14046 : decode code ⟨14046⟩ = some (.DUP4, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14047 : decode code ⟨14047⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14048 : decode code ⟨14048⟩ = some (.LT, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14049 : decode code ⟨14049⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14050 : decode code ⟨14050⟩ = some (.Push .PUSH2, some (⟨14102⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14053 : decode code ⟨14053⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hargClean : UInt256.land (initializeArgWord ee) slot0Uint160Mask =
      initializeArgWord ee := by
    apply slot0Uint160Mask_clean
    rw [initializeArgWord, show initializeUint160Mask = slot0Uint160Mask by native_decide]
    exact slot0Uint160Mask_bound (calldataWord ee.calldata 4)
  have hltLow : UInt256.lt (initializeArgWord ee) ⟨4295128739⟩ = ⟨0⟩ := by
    apply ult_zero
    rw [show (⟨4295128739⟩ : UInt256).toNat = 4295128739 from by decide]
    exact hlo
  have hltHigh : UInt256.lt (initializeArgWord ee)
      ⟨1461446703485210103287273052203988822378723970342⟩ = ⟨1⟩ := by
    apply ult_one
    rw [show (⟨1461446703485210103287273052203988822378723970342⟩ : UInt256).toNat =
        1461446703485210103287273052203988822378723970342 from by decide]
    exact hhi
  have rd13990 := by
    simpa using h.jumpdest hd13989 (by evm_ov)
  have rd13992 := by
    simpa using rd13990.push1 ⟨0⟩ hd13990 (by evm_ov)
  have rd13998 := by
    simpa using rd13992.pushConst (⟨4295128739⟩ : UInt256)
      (by native_decide : Operation.POp.PUSH5 ≠ .PUSH0) hd13992 (by evm_ov)
  have rd14000 := by
    simpa using rd13998.push1 ⟨1⟩ hd13998 (by evm_ov)
  have rd14002 := by
    simpa using rd14000.push1 ⟨1⟩ hd14000 (by
      simp only [List.length_cons]
      omega)
  have rd14004 := by
    simpa using rd14002.push1 ⟨160⟩ hd14002 (by
      simp only [List.length_cons]
      omega)
  have rd14005 := by
    simpa using rd14004.shl hd14004 (by
      simp only [List.length_cons]
      omega)
  have rd14006 := by
    simpa [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        slot0Uint160Mask by native_decide] using rd14005.sub hd14005 (by evm_ov)
  have rd14007 := by
    simpa using rd14006.dup4 hd14006 (by
      simp only [List.length_cons]
      omega)
  have rd14008 := by
    simpa [hargClean, u256_land_comm] using rd14007.and hd14007 (by
      simp only [List.length_cons]
      omega)
  have rd14009 := by
    simpa [hltLow] using rd14008.lt hd14008 (by evm_ov)
  have rd14010 := by
    simpa using rd14009.dup1 hd14009 (by
      simp only [List.length_cons]
      omega)
  have rd14011 := by
    simpa using rd14010.iszero hd14010 (by evm_ov)
  have rd14012 := by
    simpa using rd14011.swap1 hd14011 (by
      simp only [List.length_cons]
      omega)
  have rd14015 := by
    simpa using rd14012.push2 ⟨14049⟩ hd14012 (by
      simp only [List.length_cons]
      omega)
  have rd14016 := by
    simpa [show (⟨14012⟩ + UInt256.ofNat 3 + ⟨1⟩ : UInt256) = ⟨14016⟩
        by native_decide] using
      rd14015.jumpiNT hd14015 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
        (by simp only [List.length_cons]; omega)
  have rd14017 := by
    simpa using rd14016.pop hd14016 (by evm_ov)
  have rd14038 := by
    simpa using rd14017.pushConst
      (⟨1461446703485210103287273052203988822378723970342⟩ : UInt256)
      (by native_decide : Operation.POp.PUSH20 ≠ .PUSH0) hd14017 (by evm_ov)
  have rd14040 := by
    simpa using rd14038.push1 ⟨1⟩ hd14038 (by evm_ov)
  have rd14042 := by
    simpa using rd14040.push1 ⟨1⟩ hd14040 (by
      simp only [List.length_cons]
      omega)
  have rd14044 := by
    simpa using rd14042.push1 ⟨160⟩ hd14042 (by
      simp only [List.length_cons]
      omega)
  have rd14045 := by
    simpa using rd14044.shl hd14044 (by
      simp only [List.length_cons]
      omega)
  have rd14046 := by
    simpa [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        slot0Uint160Mask by native_decide] using rd14045.sub hd14045 (by evm_ov)
  have rd14047 := by
    simpa using rd14046.dup4 hd14046 (by
      simp only [List.length_cons]
      omega)
  have rd14048 := by
    simpa [hargClean, u256_land_comm] using rd14047.and hd14047 (by
      simp only [List.length_cons]
      omega)
  have rd14049 := by
    simpa [hltHigh] using rd14048.lt hd14048 (by evm_ov)
  have rd14050 := by
    simpa using rd14049.jumpdest hd14049 (by
      simp only [List.length_cons]
      omega)
  have rd14053 := by
    simpa using rd14050.push2 ⟨14102⟩ hd14050 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd14053.jumpiT hd14053 (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (uniswapV3PoolJumpDestPatched14102 hpatch) (by simp only [List.length_cons]; omega)⟩

theorem uniswapV3PoolInitializeEvmAlreadyInitialized {v : PoolImmutables}
    {code : ByteArray} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 25 == I.calldata.extract 0 4) = true)
    (hsz36 : 36 ≤ I.calldata.size)
    (hnz : slot0SqrtPriceX96Word σ I ≠ ⟨0⟩) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  have hreach := uniswapV3PoolInitializeReachEntry
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize hsel
  obtain ⟨_, _, hdecoded⟩ :=
    uniswapV3PoolInitializeExternalLenOk (v := v) (code := code)
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hpatch hreach hsz36 hsize
  obtain ⟨_, _, hbody⟩ :=
    uniswapV3PoolInitializeDecodedReachRoutine (v := v) (code := code)
      (ee := I) (g := g) (s0 := initState cA gh bl σ σ₀ g A I)
      (ret := ⟨857⟩) (R := [solcSelectorWord I]) (mem := solcFreePtrMem)
      (aw := UInt256.ofNat 3) (rdata := ByteArray.empty) (acc := (cA, σ))
      hpatch hdecoded (by simp only [List.length_singleton]; omega)
  exact uniswapV3PoolInitializeAlreadyInitializedRevert (v := v) (code := code)
    (ee := I) (g := g) (s0 := initState cA gh bl σ σ₀ g A I)
    (ret := ⟨857⟩) (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
    (cA := cA) (σ := σ) hpatch hbody hnz (by simp only [List.length_singleton]; omega)

theorem uniswapV3PoolInitializeEvalSqrtPriceX96 {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? (config v) { contract := contract v, locals := initializeStore I }
      (initState cA gh bl σ σ₀ g A I) (.storage (slot0F "sqrtPriceX96")) =
      .ok (.int (Int.ofNat (slot0SqrtPriceX96Word σ I).toNat)) := by
  rw [evalExpr_storage_scalar
    (t := .int uint160Int)
    (slot := slot0F "sqrtPriceX96")
    (er := { base := "slot0", steps := [.field "sqrtPriceX96"] })
    (loc := loc ⟨0⟩ ⟨0, by decide⟩ ⟨20, by decide⟩ (by decide) (.int uint160Int))
    (hbase := by simp [slot0F, initializeStore])
    (her := by
      simp [evalStorageRef, evalStorageRefStep, slot0F, EvalResult.bind, pure, bind])
    (hty := by
      simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, slot0StructTy, uint160St])
    (hloc := by
      funext evm
      simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout, loc])]
  simpa [slot0SqrtPriceX96Word, slot0SlotWord] using
    slot0StorageLocLoad_sqrtPriceX96 (initState cA gh bl σ σ₀ g A I)

theorem uniswapV3PoolInitializeEvalSqrtPriceX96EqZeroFalse {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hnz : slot0SqrtPriceX96Word σ I ≠ ⟨0⟩) :
    evalExpr? (config v) { contract := contract v, locals := initializeStore I }
      (initState cA gh bl σ σ₀ g A I)
      (eqE (.storage (slot0F "sqrtPriceX96")) (.intLit 0)) = .ok (.bool false) := by
  unfold eqE
  simp only [evalExpr?, uniswapV3PoolInitializeEvalSqrtPriceX96, EvalResult.bind, bind,
    pure, evalBinaryOp?]
  have hnat : ¬ (slot0SqrtPriceX96Word σ I).toNat = 0 := by
    intro h
    apply hnz
    apply u256_inj
    simpa [UInt256.toNat] using h
  simp [hnat]

theorem uniswapV3PoolInitializeEvalSqrtPriceX96EqZeroTrue {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hzero : slot0SqrtPriceX96Word σ I = ⟨0⟩) :
    evalExpr? (config v) { contract := contract v, locals := initializeStore I }
      (initState cA gh bl σ σ₀ g A I)
      (eqE (.storage (slot0F "sqrtPriceX96")) (.intLit 0)) = .ok (.bool true) := by
  unfold eqE
  simp only [evalExpr?, uniswapV3PoolInitializeEvalSqrtPriceX96, EvalResult.bind, bind,
    pure, evalBinaryOp?]
  have hnat : (slot0SqrtPriceX96Word σ I).toNat = 0 := by
    rw [hzero]
    rfl
  simp [hnat]

theorem uniswapV3PoolInitializeEvalSqrtPriceVar {v : PoolImmutables}
    {evm I} :
    evalExpr? (config v) { contract := contract v, locals := initializeStore I }
      evm (.var "sqrtPriceX96") = .ok (initializeArgValue I) := by
  simp [evalExpr?, initializeStore, EvalResult.ofOption]

theorem uniswapV3PoolGetTickAtSqrtRatioEvalRangeFalseLow {v : PoolImmutables}
    {evm I} (hlo : (initializeArgWord I).toNat < 4295128739) :
    evalExpr? (config v) { contract := contract v, locals := initializeStore I } evm
      (andE (geE (.var "sqrtPriceX96") minSqrtRatio)
        (ltE (.var "sqrtPriceX96") maxSqrtRatio)) = .ok (.bool false) := by
  unfold andE geE minSqrtRatio
  simp only [evalExpr?, uniswapV3PoolInitializeEvalSqrtPriceVar, initializeArgValue,
    EvalResult.bind, bind, pure, evalBinaryOp?]
  have hnot : ¬ Int.ofNat (initializeArgWord I).toNat ≥ (4295128739 : Int) := by
    change ¬ ((initializeArgWord I).toNat : Int) ≥ (4295128739 : Int)
    omega
  rw [show decide (Int.ofNat (initializeArgWord I).toNat ≥ (4295128739 : Int)) = false
    from decide_eq_false hnot]

theorem uniswapV3PoolGetTickAtSqrtRatioEvalRangeFalseHigh {v : PoolImmutables}
    {evm I}
    (hhi : 1461446703485210103287273052203988822378723970342 ≤
      (initializeArgWord I).toNat) :
    evalExpr? (config v) { contract := contract v, locals := initializeStore I } evm
      (andE (geE (.var "sqrtPriceX96") minSqrtRatio)
        (ltE (.var "sqrtPriceX96") maxSqrtRatio)) = .ok (.bool false) := by
  unfold andE geE ltE minSqrtRatio maxSqrtRatio
  simp only [evalExpr?, uniswapV3PoolInitializeEvalSqrtPriceVar, initializeArgValue,
    EvalResult.bind, bind, pure, evalBinaryOp?]
  have hge : Int.ofNat (initializeArgWord I).toNat ≥ (4295128739 : Int) := by
    change ((initializeArgWord I).toNat : Int) ≥ (4295128739 : Int)
    omega
  have hnot : ¬ Int.ofNat (initializeArgWord I).toNat <
      (1461446703485210103287273052203988822378723970342 : Int) := by
    change ¬ ((initializeArgWord I).toNat : Int) <
      (1461446703485210103287273052203988822378723970342 : Int)
    omega
  rw [show decide (Int.ofNat (initializeArgWord I).toNat ≥ (4295128739 : Int)) = true
    from decide_eq_true hge]
  rw [show decide (Int.ofNat (initializeArgWord I).toNat <
      (1461446703485210103287273052203988822378723970342 : Int)) = false
    from decide_eq_false hnot]

theorem uniswapV3PoolGetTickAtSqrtRatioEvalRangeTrue {v : PoolImmutables}
    {evm I} (hlo : 4295128739 ≤ (initializeArgWord I).toNat)
    (hhi : (initializeArgWord I).toNat <
      1461446703485210103287273052203988822378723970342) :
    evalExpr? (config v) { contract := contract v, locals := initializeStore I } evm
      (andE (geE (.var "sqrtPriceX96") minSqrtRatio)
        (ltE (.var "sqrtPriceX96") maxSqrtRatio)) = .ok (.bool true) := by
  unfold andE geE ltE minSqrtRatio maxSqrtRatio
  simp only [evalExpr?, uniswapV3PoolInitializeEvalSqrtPriceVar, initializeArgValue,
    EvalResult.bind, bind, pure, evalBinaryOp?]
  have hge : Int.ofNat (initializeArgWord I).toNat ≥ (4295128739 : Int) := by
    change ((initializeArgWord I).toNat : Int) ≥ (4295128739 : Int)
    omega
  have hlt : Int.ofNat (initializeArgWord I).toNat <
      (1461446703485210103287273052203988822378723970342 : Int) := by
    change ((initializeArgWord I).toNat : Int) <
      (1461446703485210103287273052203988822378723970342 : Int)
    omega
  rw [show decide (Int.ofNat (initializeArgWord I).toNat ≥ (4295128739 : Int)) = true
    from decide_eq_true hge]
  rw [show decide (Int.ofNat (initializeArgWord I).toNat <
      (1461446703485210103287273052203988822378723970342 : Int)) = true
    from decide_eq_true hlt]

theorem uniswapV3PoolGetTickAtSqrtRatioSourceRevertsLow {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hlo : (initializeArgWord I).toNat < 4295128739) :
    ExecFuncBody (config v) { contract := contract v, locals := initializeStore I }
      (initState cA gh bl σ σ₀ g A I) getTickAtSqrtRatioFunction.body .reverted := by
  dsimp [getTickAtSqrtRatioFunction]
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consRevert (ExecStmt.requireFalse
      (uniswapV3PoolGetTickAtSqrtRatioEvalRangeFalseLow (v := v) hlo))

theorem uniswapV3PoolGetTickAtSqrtRatioSourceRevertsHigh {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hhi : 1461446703485210103287273052203988822378723970342 ≤
      (initializeArgWord I).toNat) :
    ExecFuncBody (config v) { contract := contract v, locals := initializeStore I }
      (initState cA gh bl σ σ₀ g A I) getTickAtSqrtRatioFunction.body .reverted := by
  dsimp [getTickAtSqrtRatioFunction]
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consRevert (ExecStmt.requireFalse
      (uniswapV3PoolGetTickAtSqrtRatioEvalRangeFalseHigh (v := v) hhi))

theorem slot0SqrtPriceX96Word_transport {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    slot0SqrtPriceX96Word σ_solm I = slot0SqrtPriceX96Word σ_evm I := by
  have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ (⟨0⟩ : UInt256)
  dsimp [slot0SqrtPriceX96Word, slot0SlotWord, solcSlotWord]
  rw [← hslot]

theorem uniswapV3PoolInitializeSourceAlreadyInitializedReverts {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hnz : slot0SqrtPriceX96Word σ I ≠ ⟨0⟩) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (initializeStore I)
      initializeTransition.body .reverted := by
  change ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (initializeStore I)
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (eqE (.storage (slot0F "sqrtPriceX96")) (.intLit 0)),
        .internalCall "getTickAtSqrtRatio" [.var "sqrtPriceX96"] "tick",
        .letDecl "time" (some uint32) (modE (.env .timestamp) uint32Modulus),
        .assign .storage (observationsF (.intLit 0) "blockTimestamp") (.var "time"),
        .assign .storage (observationsF (.intLit 0) "tickCumulative") (.intLit 0),
        .assign .storage (observationsF (.intLit 0) "secondsPerLiquidityCumulativeX128")
          (.intLit 0),
        .assign .storage (observationsF (.intLit 0) "initialized") (.boolLit true),
        .assign .storage (slot0F "sqrtPriceX96") (.var "sqrtPriceX96"),
        .assign .storage (slot0F "tick") (.var "tick"),
        .assign .storage (slot0F "observationIndex") (.intLit 0),
        .assign .storage (slot0F "observationCardinality") (.intLit 1),
        .assign .storage (slot0F "observationCardinalityNext") (.intLit 1),
        .assign .storage (slot0F "feeProtocol") (.intLit 0),
        .assign .storage (slot0F "unlocked") (.boolLit true) ] .reverted
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by
      simp [initState, hwv]))) <|
      ExecBlock.consRevert (ExecStmt.requireFalse
        (uniswapV3PoolInitializeEvalSqrtPriceX96EqZeroFalse (v := v) hnz))

theorem uniswapV3PoolInitializeSourceGetTickLowReverts {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hzero : slot0SqrtPriceX96Word σ I = ⟨0⟩)
    (hlo : (initializeArgWord I).toNat < 4295128739) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (initializeStore I)
      initializeTransition.body .reverted := by
  change ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (initializeStore I)
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (eqE (.storage (slot0F "sqrtPriceX96")) (.intLit 0)),
        .internalCall "getTickAtSqrtRatio" [.var "sqrtPriceX96"] "tick",
        .letDecl "time" (some uint32) (modE (.env .timestamp) uint32Modulus),
        .assign .storage (observationsF (.intLit 0) "blockTimestamp") (.var "time"),
        .assign .storage (observationsF (.intLit 0) "tickCumulative") (.intLit 0),
        .assign .storage (observationsF (.intLit 0) "secondsPerLiquidityCumulativeX128")
          (.intLit 0),
        .assign .storage (observationsF (.intLit 0) "initialized") (.boolLit true),
        .assign .storage (slot0F "sqrtPriceX96") (.var "sqrtPriceX96"),
        .assign .storage (slot0F "tick") (.var "tick"),
        .assign .storage (slot0F "observationIndex") (.intLit 0),
        .assign .storage (slot0F "observationCardinality") (.intLit 1),
        .assign .storage (slot0F "observationCardinalityNext") (.intLit 1),
        .assign .storage (slot0F "feeProtocol") (.intLit 0),
        .assign .storage (slot0F "unlocked") (.boolLit true) ] .reverted
  refine ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by
      simp [initState, hwv]))) <|
      ExecBlock.consNormal (ExecStmt.requireTrue
        (uniswapV3PoolInitializeEvalSqrtPriceX96EqZeroTrue (v := v) hzero)) <|
        ExecBlock.consRevert ?_
  refine internalCallFunctionRevert (callee := getTickAtSqrtRatioFunction)
    (argVals := [initializeArgValue I]) (locals := initializeStore I) ?_ ?_ ?_ ?_
  · simp [evalExprs?, uniswapV3PoolInitializeEvalSqrtPriceVar, EvalResult.bind, bind, pure]
  · simp [lookupCallable?, lookupFunction?, contract, functions, getSqrtRatioAtTickFunction,
      getTickAtSqrtRatioFunction]
  · rfl
  · exact uniswapV3PoolGetTickAtSqrtRatioSourceRevertsLow (v := v) hlo

theorem uniswapV3PoolInitializeSourceGetTickHighReverts {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hzero : slot0SqrtPriceX96Word σ I = ⟨0⟩)
    (hhi : 1461446703485210103287273052203988822378723970342 ≤
      (initializeArgWord I).toNat) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (initializeStore I)
      initializeTransition.body .reverted := by
  change ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (initializeStore I)
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (eqE (.storage (slot0F "sqrtPriceX96")) (.intLit 0)),
        .internalCall "getTickAtSqrtRatio" [.var "sqrtPriceX96"] "tick",
        .letDecl "time" (some uint32) (modE (.env .timestamp) uint32Modulus),
        .assign .storage (observationsF (.intLit 0) "blockTimestamp") (.var "time"),
        .assign .storage (observationsF (.intLit 0) "tickCumulative") (.intLit 0),
        .assign .storage (observationsF (.intLit 0) "secondsPerLiquidityCumulativeX128")
          (.intLit 0),
        .assign .storage (observationsF (.intLit 0) "initialized") (.boolLit true),
        .assign .storage (slot0F "sqrtPriceX96") (.var "sqrtPriceX96"),
        .assign .storage (slot0F "tick") (.var "tick"),
        .assign .storage (slot0F "observationIndex") (.intLit 0),
        .assign .storage (slot0F "observationCardinality") (.intLit 1),
        .assign .storage (slot0F "observationCardinalityNext") (.intLit 1),
        .assign .storage (slot0F "feeProtocol") (.intLit 0),
        .assign .storage (slot0F "unlocked") (.boolLit true) ] .reverted
  refine ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by
      simp [initState, hwv]))) <|
      ExecBlock.consNormal (ExecStmt.requireTrue
        (uniswapV3PoolInitializeEvalSqrtPriceX96EqZeroTrue (v := v) hzero)) <|
        ExecBlock.consRevert ?_
  refine internalCallFunctionRevert (callee := getTickAtSqrtRatioFunction)
    (argVals := [initializeArgValue I]) (locals := initializeStore I) ?_ ?_ ?_ ?_
  · simp [evalExprs?, uniswapV3PoolInitializeEvalSqrtPriceVar, EvalResult.bind, bind, pure]
  · simp [lookupCallable?, lookupFunction?, contract, functions, getSqrtRatioAtTickFunction,
      getTickAtSqrtRatioFunction]
  · rfl
  · exact uniswapV3PoolGetTickAtSqrtRatioSourceRevertsHigh (v := v) hhi

end Benchmarks.UniswapV3Pool
