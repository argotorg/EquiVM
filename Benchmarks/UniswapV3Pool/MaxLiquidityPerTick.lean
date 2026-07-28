import Benchmarks.UniswapV3Pool.Liquidity

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

private theorem uniswapV3PoolPatchPreservesJumpDest8172 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨8172⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched8172 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨8172⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest8172

theorem uniswapV3PoolMaxLiquidityPerTickReachEntry {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 13 == I.calldata.extract 0 4) = true) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨1478⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := uniswapV3PoolReachSelector32
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize
  have hword : solcSelectorWord I = uniswapV3PoolSelNat 13 := by
    simpa [uniswapV3PoolSelBytes, uniswapV3PoolSelNat] using
      solcSelectorWord_eq_of_beq I hsz 0x70 0xcf 0x75 0x4a
        (uniswapV3PoolSelNat 13) (by native_decide) hsel
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
  have h1478 := uniswapV3PoolSelectorArmHitTo (i := 13) (target := ⟨1478⟩)
    hpatch hsz hsel h201
  exact ⟨_, _, h1478⟩

theorem uniswapV3PoolMaxLiquidityPerTickDecode {v : PoolImmutables} {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode
      ((maxliquiditypertickTransition v).params.map Param.name)
      (transitionSignature (maxliquiditypertickTransition v)).paramTypes I.calldata =
        some (∅ : Store) := by
  simpa [config, maxliquiditypertickTransition, transitionSignature] using
    decodeCalldataWithMode_empty_ok (mode := DecodeMode.legacySolc05) (cd := I.calldata) hsz

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolDispatch_maxLiquidityPerTick {v : PoolImmutables} {cd : ByteArray}
    (hsel : (uniswapV3PoolSelBytes 13 == cd.extract 0 4) = true) :
    dispatchMsg (contract v) cd = some (maxliquiditypertickTransition v) := by
  apply dispatchMsg_eq_some_of_split
    (pre := [burnTransition, collectTransition v, collectprotocolTransition v,
      factoryTransition v, feeTransition v, feegrowthglobal0X128Transition,
      feegrowthglobal1X128Transition, flashTransition v,
      increaseobservationcardinalitynextTransition v, initializeTransition, liquidityTransition])
    (post := [mintTransition v, observationsTransition, observeTransition v, positionsTransition,
      protocolfeesTransition, setfeeprotocolTransition v, slot0Transition,
      snapshotcumulativesinsideTransition v, swapTransition v, tickbitmapTransition,
      tickspacingTransition v, ticksTransition, token0Transition v, token1Transition v])
  · simp [contract, transitions]
  · intro t ht
    simp at ht
    rcases ht with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [selectorOf, burnSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 17) (j := 13)
          (by native_decide) hsel
    · rw [selectorOf, collectSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 10) (j := 13)
          (by native_decide) hsel
    · rw [selectorOf, collectProtocolSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 15) (j := 13)
          (by native_decide) hsel
    · rw [selectorOf, factorySelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 19) (j := 13)
          (by native_decide) hsel
    · rw [selectorOf, feeSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 22) (j := 13)
          (by native_decide) hsel
    · rw [selectorOf, feeGrowthGlobal0X128SelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 23) (j := 13)
          (by native_decide) hsel
    · rw [selectorOf, feeGrowthGlobal1X128SelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 8) (j := 13)
          (by native_decide) hsel
    · rw [selectorOf, flashSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 9) (j := 13)
          (by native_decide) hsel
    · rw [selectorOf, increaseObservationCardinalityNextSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 5) (j := 13)
          (by native_decide) hsel
    · rw [selectorOf, initializeSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 25) (j := 13)
          (by native_decide) hsel
    · rw [selectorOf, liquiditySelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 2) (j := 13)
          (by native_decide) hsel
  · rw [selectorOf, maxLiquidityPerTickSelectorBytes v]
    simpa [uniswapV3PoolSelBytes] using hsel

theorem uniswapV3PoolMaxLiquidityPerTickPatchWord {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    code.extract 8174 8206 = UInt256.toByteArray (EVM.wordOfInt v.maxLiquidityPerTick) := by
  let value := UInt256.toByteArray (EVM.wordOfInt v.maxLiquidityPerTick)
  let pre : List (Nat × ByteArray) :=
    [(8315, UInt256.toByteArray (EVM.Word.ofNat v.factory.toNat)),
     (8829, UInt256.toByteArray (EVM.Word.ofNat v.factory.toNat)),
     (10457, UInt256.toByteArray (EVM.Word.ofNat v.factory.toNat)),
     (2258, UInt256.toByteArray (EVM.Word.ofNat v.token0.toNat)),
     (4853, UInt256.toByteArray (EVM.Word.ofNat v.token0.toNat)),
     (6740, UInt256.toByteArray (EVM.Word.ofNat v.token0.toNat)),
     (7822, UInt256.toByteArray (EVM.Word.ofNat v.token0.toNat)),
     (9150, UInt256.toByteArray (EVM.Word.ofNat v.token0.toNat)),
     (15650, UInt256.toByteArray (EVM.Word.ofNat v.token0.toNat)),
     (4551, UInt256.toByteArray (EVM.Word.ofNat v.token1.toNat)),
     (6789, UInt256.toByteArray (EVM.Word.ofNat v.token1.toNat)),
     (7924, UInt256.toByteArray (EVM.Word.ofNat v.token1.toNat)),
     (9284, UInt256.toByteArray (EVM.Word.ofNat v.token1.toNat)),
     (10529, UInt256.toByteArray (EVM.Word.ofNat v.token1.toNat)),
     (15979, UInt256.toByteArray (EVM.Word.ofNat v.token1.toNat)),
     (3311, UInt256.toByteArray (EVM.wordOfInt v.fee)),
     (6603, UInt256.toByteArray (EVM.wordOfInt v.fee)),
     (6658, UInt256.toByteArray (EVM.wordOfInt v.fee)),
     (10565, UInt256.toByteArray (EVM.wordOfInt v.fee)),
     (3072, UInt256.toByteArray (EVM.wordOfInt v.tickSpacing)),
     (10493, UInt256.toByteArray (EVM.wordOfInt v.tickSpacing)),
     (19402, UInt256.toByteArray (EVM.wordOfInt v.tickSpacing)),
     (19452, UInt256.toByteArray (EVM.wordOfInt v.tickSpacing))]
  let post : List (Nat × ByteArray) :=
    [(19295, value), (19350, value),
     (11259, UInt256.toByteArray (EVM.Word.ofNat v.original.toNat))]
  have hpatch' : patchRuntime uniswapV3PoolBytecode (pre ++ (8174, value) :: post) =
      some code := by
    dsimp [pre, post, value]
    simpa [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup,
      toByteArray_eq_toBytesBE] using hpatch
  have hpost : ∀ p ∈ post, 8174 + 32 ≤ p.1 ∨ p.1 + 32 ≤ 8174 := by
    intro p hp
    dsimp [post] at hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals omega
  have hsize : value.size = 32 := by
    dsimp [value]
    exact toByteArray_size _
  exact patchRuntime_extract_patch hsize hpost hpatch'

theorem uniswapV3PoolMaxLiquidityPerTickConstDecode {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    decode code ⟨8173⟩ =
      some (.Push .PUSH32, some (EVM.wordOfInt v.maxLiquidityPerTick, 32)) := by
  have hsize := uniswapV3PoolPatchedSize hpatch
  have hget : code.get? ({ val := 8173 } : UInt256).toNat =
      uniswapV3PoolBytecode.get? ({ val := 8173 } : UInt256).toNat := by
    change code.get? 8173 = uniswapV3PoolBytecode.get? 8173
    apply get?_eq_of_extract_one
    · rw [hsize]
      native_decide
    · native_decide
    · exact patchRuntime_extract_eq (start := 8173) (stop := 8174)
        (template := uniswapV3PoolBytecode) (out := code) (ps := patches v)
        (by omega) (by native_decide)
        (fun p hp => by
          simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord,
            List.lookup] at hp
          rcases hp with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl
          all_goals omega) hpatch
  have hextract : code.extract' ({ val := 8173 } : UInt256).toNat.succ
      (({ val := 8173 } : UInt256).toNat.succ + 32) =
      UInt256.toByteArray (EVM.wordOfInt v.maxLiquidityPerTick) := by
    change code.extract' 8174 8206 =
      UInt256.toByteArray (EVM.wordOfInt v.maxLiquidityPerTick)
    unfold ByteArray.extract'
    have hguard : (decide (8174 < 2 ^ 64) && decide (8206 < 2 ^ 64)) = true := by
      native_decide
    rw [if_pos hguard]
    exact uniswapV3PoolMaxLiquidityPerTickPatchWord hpatch
  have hgetSome : code.get? ({ val := 8173 } : UInt256).toNat = some 0x7f := by
    rw [hget]
    native_decide
  have hparse : (some (0x7f : UInt8) >>= parseInstr) = some (.Push .PUSH32) := by
    native_decide
  unfold decode
  rw [hgetSome, hparse]
  change some (Operation.Push Operation.POp.PUSH32,
      some (uInt256OfByteArray
        (code.extract' ({ val := 8173 } : UInt256).toNat.succ
          (({ val := 8173 } : UInt256).toNat.succ + 32)), 32)) =
    some (Operation.Push Operation.POp.PUSH32,
      some (EVM.wordOfInt v.maxLiquidityPerTick, 32))
  rw [hextract, uInt256OfByteArray_eq, fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

theorem uniswapV3PoolMaxLiquidityPerTickGetterJumpdestDecode {v : PoolImmutables}
    {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    decode code ⟨8172⟩ = some (.JUMPDEST, .none) := by
  refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8172⟩) (byte := 0x5b)
    (op := .JUMPDEST) hpatch (by native_decide) ?_ (by native_decide)
    (by native_decide) (by native_decide)
  change ∀ p ∈ patches v, 8173 ≤ p.1 ∨ p.1 + 32 ≤ 8172
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals omega

theorem uniswapV3PoolMaxLiquidityPerTickGetterDupDecode {v : PoolImmutables}
    {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    decode code ⟨8206⟩ = some (.DUP2, .none) := by
  refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8206⟩) (byte := 0x81)
    (op := .DUP2) hpatch (by native_decide) ?_ (by native_decide)
    (by native_decide) (by native_decide)
  change ∀ p ∈ patches v, 8207 ≤ p.1 ∨ p.1 + 32 ≤ 8206
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals omega

theorem uniswapV3PoolMaxLiquidityPerTickGetterJumpDecode {v : PoolImmutables}
    {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    decode code ⟨8207⟩ = some (.JUMP, .none) := by
  refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8207⟩) (byte := 0x56)
    (op := .JUMP) hpatch (by native_decide) ?_ (by native_decide)
    (by native_decide) (by native_decide)
  change ∀ p ∈ patches v, 8208 ≤ p.1 ∨ p.1 + 32 ≤ 8207
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals omega

theorem uniswapV3PoolMaxLiquidityPerTickEntryWf {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcGetterEntryWf code ⟨1478⟩ ⟨654⟩ ⟨8172⟩ := by
  dsimp [solcGetterEntryWf]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide

theorem uniswapV3PoolMaxLiquidityPerTickGetterWf {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcConstGetterWf code ⟨8172⟩ (EVM.wordOfInt v.maxLiquidityPerTick) 32 .PUSH32 := by
  dsimp [solcConstGetterWf]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact uniswapV3PoolMaxLiquidityPerTickGetterJumpdestDecode hpatch
  · native_decide
  · exact uniswapV3PoolMaxLiquidityPerTickConstDecode hpatch
  · exact uniswapV3PoolMaxLiquidityPerTickGetterDupDecode hpatch
  · exact uniswapV3PoolMaxLiquidityPerTickGetterJumpDecode hpatch

theorem RD.solcUint128ConstGetterExternal {code : ByteArray} {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel entry routine returnPc val : UInt256} {width : Nat}
    {op : Operation.POp}
    (hreach : ∃ k C, RD code I g (Reasoning.Theory.initState cA gh bl σ σ₀ g A I)
      entry [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hgetter : solcConstGetterWf code routine val width op)
    (hroutine : (D_J code 0).contains routine = true)
    (hret : (D_J code 0).contains returnPc = true)
    (hreturn : solcReturnUint128FromMemWf code returnPc) :
    RDret code g (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.land val uint128Mask)) := by
  obtain ⟨_, _, rdRoutine⟩ := RD.solcGetterThunk hreach hentry hroutine
  obtain ⟨_, _, rdReturn⟩ := RD.solcConstGetter (val := val) (width := width)
    (op := op) (R := [sel]) rdRoutine hgetter hret
    (by simp only [List.length_singleton]; omega)
  exact RD.solcReturnUint128FromMem rdReturn hreturn
    solcFreePtrMem_mload64
    (by rfl)
    (solcReturnMem_mload64 (UInt256.land val uint128Mask))
    (solcReturnMem_read128 (UInt256.land val uint128Mask))
    (by simp only [List.length_singleton]; omega)

theorem uniswapV3PoolMaxLiquidityPerTickEvm {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 13 == I.calldata.extract 0 4) = true) :
    RDret code g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.land (EVM.wordOfInt v.maxLiquidityPerTick) uint128Mask)) := by
  have hreach := uniswapV3PoolMaxLiquidityPerTickReachEntry
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize hsel
  exact RD.solcUint128ConstGetterExternal
    (sel := solcSelectorWord I) (entry := ⟨1478⟩) (routine := ⟨8172⟩)
    (returnPc := ⟨654⟩) (val := EVM.wordOfInt v.maxLiquidityPerTick) (width := 32)
    (op := .PUSH32) hreach
    (uniswapV3PoolMaxLiquidityPerTickEntryWf hpatch)
    (uniswapV3PoolMaxLiquidityPerTickGetterWf hpatch)
    (uniswapV3PoolJumpDestPatched8172 hpatch)
    (uniswapV3PoolLiquidityReturnJumpDest hpatch)
    (uniswapV3PoolLiquidityReturnWf hpatch)

theorem uint128ReturnEncodingInt (i : Int) (h0 : 0 ≤ i) (hlt : i < 2 ^ 128) :
    encodeReturnValue? uint128 (.int i) = some (UInt256.toByteArray (EVM.wordOfInt i)) := by
  have hword : EVM.wordOfInt i = EVM.word i.toNat := wordOfInt_nonneg i h0
  have hltWord : i < ↑(EVM.twoPow 128) := by
    simpa [EVM.twoPow] using hlt
  refine scalarReturnEncoding (t := (.int (.uint ⟨128, by decide⟩)))
    (w := EVM.wordOfInt i) rfl ?_ ?_
  · simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, bind, Option.bind]
    decide
  · simp [encodeABIValue?, encodeABIWord?, hword, h0, hltWord]

theorem uint128MaskCleanOfInt (i : Int) (h0 : 0 ≤ i) (hlt : i < 2 ^ 128) :
    UInt256.land (EVM.wordOfInt i) uint128Mask = EVM.wordOfInt i := by
  apply uint128Mask_clean
  rw [wordOfInt_nonneg i h0]
  have hltNat : i.toNat < EVM.twoPow 128 := by
    exact (Int.toNat_lt h0).2 (by simpa [EVM.twoPow] using hlt)
  unfold EVM.word EVM.uintN UInt256.toNat
  simp only
  rw [Nat.mod_eq_of_lt]
  · exact hltNat
  · have : EVM.twoPow 128 < EVM.twoPow 256 := by
      norm_num [EVM.twoPow]
    omega

theorem uniswapV3PoolMaxLiquidityPerTickSourceBody {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (∅ : Store) (maxliquiditypertickTransition v).body
      (.returned { contract := contract v, locals := ∅ }
        (initState cA gh bl σ σ₀ g A I)
        (some [Value.int v.maxLiquidityPerTick])) := by
  change ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (∅ : Store)
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return [.intLit v.maxLiquidityPerTick] ] _
  exact nonpayableIntLiteralBodyReturns (initState cA gh bl σ σ₀ g A I)
    (∅ : Store) v.maxLiquidityPerTick hwv

theorem uniswapV3PoolMaxLiquidityPerTickBodyCore {v : PoolImmutables}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsel : (uniswapV3PoolSelBytes 13 == I.calldata.extract 0 4) = true) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdispatch := uniswapV3PoolDispatch_maxLiquidityPerTick (v := v) (cd := I.calldata) hsel
  have hdecode := uniswapV3PoolMaxLiquidityPerTickDecode (v := v) (I := I) hsz
  have hbody := uniswapV3PoolMaxLiquidityPerTickSourceBody (v := v) (cA := cA) (gh := gh)
    (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hwv
  have hrd := uniswapV3PoolMaxLiquidityPerTickEvm (v := v) (code := code) (cA := cA)
    (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hpatch hcode hwv hsz hsize hsel
  have hmask := uint128MaskCleanOfInt v.maxLiquidityPerTick
    v.maxLiquidityPerTick_nonneg v.maxLiquidityPerTick_lt
  exact hrd.reEquivExecution hcode hdispatch hdecode hbody hAccounts
    (returnEquiv_of_encode (by
      simpa [hmask] using uint128ReturnEncodingInt v.maxLiquidityPerTick
        v.maxLiquidityPerTick_nonneg v.maxLiquidityPerTick_lt))

end Benchmarks.UniswapV3Pool
