import Benchmarks.UniswapV3Pool.Common

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.UniswapV3Pool

def uint24Mask : UInt256 := UInt256.ofNat (2 ^ 24 - 1)

theorem uint24Mask_toNat :
    uint24Mask.toNat = 2 ^ 24 - 1 := by
  exact ulit_toNat' _ (by norm_num [UInt256.size])

theorem uint24Mask_bound (w : UInt256) :
    (UInt256.land w uint24Mask).toNat < EVM.twoPow 24 := by
  rw [uland_toNat]
  rw [uint24Mask_toNat]
  exact lt_of_le_of_lt (nat_land_le_right _ _) (by norm_num [EVM.twoPow])

theorem uint24Mask_clean {w : UInt256} (hcanon : w.toNat < EVM.twoPow 24) :
    UInt256.land w uint24Mask = w := by
  apply u256_inj
  show Nat.land w.toNat uint24Mask.toNat % EVM.twoPow 256 = w.toNat
  rw [uint24Mask_toNat, nat_land_mask_eq_mod]
  rw [show EVM.twoPow 24 = 2 ^ 24 from rfl] at hcanon
  rw [Nat.mod_eq_of_lt hcanon]
  exact Nat.mod_eq_of_lt w.val.isLt

theorem uint24ReturnEncodingInt (i : Int) (h0 : 0 ≤ i) (hlt : i < 2 ^ 24) :
    encodeReturnValue? uint24 (.int i) = some (UInt256.toByteArray (EVM.wordOfInt i)) := by
  have hword : EVM.wordOfInt i = EVM.word i.toNat := wordOfInt_nonneg i h0
  have hltWord : i < ↑(EVM.twoPow 24) := by
    simpa [EVM.twoPow] using hlt
  refine scalarReturnEncoding (t := (.int (.uint ⟨24, by decide⟩)))
    (w := EVM.wordOfInt i) rfl ?_ ?_
  · simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, bind, Option.bind]
    decide
  · simp [encodeABIValue?, encodeABIWord?, hword, h0, hltWord]

theorem uint24MaskCleanOfInt (i : Int) (h0 : 0 ≤ i) (hlt : i < 2 ^ 24) :
    UInt256.land (EVM.wordOfInt i) uint24Mask = EVM.wordOfInt i := by
  apply uint24Mask_clean
  rw [wordOfInt_nonneg i h0]
  have hltNat : i.toNat < EVM.twoPow 24 := by
    exact (Int.toNat_lt h0).2 (by simpa [EVM.twoPow] using hlt)
  unfold EVM.word EVM.uintN UInt256.toNat
  simp only
  rw [Nat.mod_eq_of_lt]
  · exact hltNat
  · have : EVM.twoPow 24 < EVM.twoPow 256 := by
      norm_num [EVM.twoPow]
    omega

private theorem uniswapV3PoolPatchPreservesJumpDest10563 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨10563⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched10563 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨10563⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest10563

theorem uniswapV3PoolFeeReachEntry {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 22 == I.calldata.extract 0 4) = true) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨2048⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := uniswapV3PoolReachSelector32
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize
  have hword : solcSelectorWord I = uniswapV3PoolSelNat 22 := by
    simpa [uniswapV3PoolSelBytes, uniswapV3PoolSelNat] using
      solcSelectorWord_eq_of_beq I hsz 0xdd 0xca 0x3f 0x43
        (uniswapV3PoolSelNat 22) (by native_decide) hsel
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
  have h2048 := uniswapV3PoolSelectorArmHitTo (i := 22) (target := ⟨2048⟩)
    hpatch hsz hsel h65
  exact ⟨_, _, h2048⟩

theorem uniswapV3PoolFeeDecode {v : PoolImmutables} {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode ((feeTransition v).params.map Param.name)
      (transitionSignature (feeTransition v)).paramTypes I.calldata = some (∅ : Store) := by
  simpa [config, feeTransition, transitionSignature] using
    decodeCalldataWithMode_empty_ok (mode := DecodeMode.legacySolc05) (cd := I.calldata) hsz

theorem uniswapV3PoolDispatch_fee {v : PoolImmutables} {cd : ByteArray}
    (hsel : (uniswapV3PoolSelBytes 22 == cd.extract 0 4) = true) :
    dispatchMsg (contract v) cd = some (feeTransition v) := by
  apply dispatchMsg_eq_some_of_split
    (pre := [burnTransition, collectTransition v, collectprotocolTransition v, factoryTransition v])
    (post := [feegrowthglobal0X128Transition, feegrowthglobal1X128Transition, flashTransition v,
      increaseobservationcardinalitynextTransition v, initializeTransition, liquidityTransition,
      maxliquiditypertickTransition v, mintTransition v, observationsTransition, observeTransition v,
      positionsTransition, protocolfeesTransition, setfeeprotocolTransition v, slot0Transition,
      snapshotcumulativesinsideTransition v, swapTransition v, tickbitmapTransition,
      tickspacingTransition v, ticksTransition, token0Transition v, token1Transition v])
  · simp [contract, transitions]
  · intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl
    · rw [selectorOf, burnSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 17) (j := 22)
          (by native_decide) hsel
    · rw [selectorOf, collectSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 10) (j := 22)
          (by native_decide) hsel
    · rw [selectorOf, collectProtocolSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 15) (j := 22)
          (by native_decide) hsel
    · rw [selectorOf, factorySelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 19) (j := 22)
          (by native_decide) hsel
  · rw [selectorOf, feeSelectorBytes v]
    simpa [uniswapV3PoolSelBytes] using hsel

theorem uniswapV3PoolFeePatchWord {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    code.extract 10565 10597 = UInt256.toByteArray (EVM.wordOfInt v.fee) := by
  let value := UInt256.toByteArray (EVM.wordOfInt v.fee)
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
     (3311, value), (6603, value), (6658, value)]
  let post : List (Nat × ByteArray) :=
    [(3072, UInt256.toByteArray (EVM.wordOfInt v.tickSpacing)),
     (10493, UInt256.toByteArray (EVM.wordOfInt v.tickSpacing)),
     (19402, UInt256.toByteArray (EVM.wordOfInt v.tickSpacing)),
     (19452, UInt256.toByteArray (EVM.wordOfInt v.tickSpacing)),
     (8174, UInt256.toByteArray (EVM.wordOfInt v.maxLiquidityPerTick)),
     (19295, UInt256.toByteArray (EVM.wordOfInt v.maxLiquidityPerTick)),
     (19350, UInt256.toByteArray (EVM.wordOfInt v.maxLiquidityPerTick)),
     (11259, UInt256.toByteArray (EVM.Word.ofNat v.original.toNat))]
  have hpatch' : patchRuntime uniswapV3PoolBytecode (pre ++ (10565, value) :: post) =
      some code := by
    dsimp [pre, post, value]
    simpa [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup,
      toByteArray_eq_toBytesBE] using hpatch
  have hpost : ∀ p ∈ post, 10565 + 32 ≤ p.1 ∨ p.1 + 32 ≤ 10565 := by
    intro p hp
    dsimp [post] at hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals omega
  have hsize : value.size = 32 := by
    dsimp [value]
    exact toByteArray_size _
  exact patchRuntime_extract_patch hsize hpost hpatch'

theorem uniswapV3PoolFeeConstDecode {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    decode code ⟨10564⟩ = some (.Push .PUSH32, some (EVM.wordOfInt v.fee, 32)) := by
  have hsize := uniswapV3PoolPatchedSize hpatch
  have hget : code.get? ({ val := 10564 } : UInt256).toNat =
      uniswapV3PoolBytecode.get? ({ val := 10564 } : UInt256).toNat := by
    change code.get? 10564 = uniswapV3PoolBytecode.get? 10564
    apply get?_eq_of_extract_one
    · rw [hsize]
      native_decide
    · native_decide
    · exact patchRuntime_extract_eq (start := 10564) (stop := 10565)
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
  have hextract : code.extract' ({ val := 10564 } : UInt256).toNat.succ
      (({ val := 10564 } : UInt256).toNat.succ + 32) =
      UInt256.toByteArray (EVM.wordOfInt v.fee) := by
    change code.extract' 10565 10597 = UInt256.toByteArray (EVM.wordOfInt v.fee)
    unfold ByteArray.extract'
    have hguard : (decide (10565 < 2 ^ 64) && decide (10597 < 2 ^ 64)) = true := by
      native_decide
    rw [if_pos hguard]
    exact uniswapV3PoolFeePatchWord hpatch
  have hgetSome : code.get? ({ val := 10564 } : UInt256).toNat = some 0x7f := by
    rw [hget]
    native_decide
  have hparse : (some (0x7f : UInt8) >>= parseInstr) = some (.Push .PUSH32) := by
    native_decide
  unfold decode
  rw [hgetSome, hparse]
  change some (Operation.Push Operation.POp.PUSH32,
      some (uInt256OfByteArray
        (code.extract' ({ val := 10564 } : UInt256).toNat.succ
          (({ val := 10564 } : UInt256).toNat.succ + 32)), 32)) =
    some (Operation.Push Operation.POp.PUSH32, some (EVM.wordOfInt v.fee, 32))
  rw [hextract, uInt256OfByteArray_eq, fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

theorem uniswapV3PoolFeeGetterJumpdestDecode {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    decode code ⟨10563⟩ = some (.JUMPDEST, .none) := by
  refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨10563⟩) (byte := 0x5b)
    (op := .JUMPDEST) hpatch (by native_decide) ?_ (by native_decide)
    (by native_decide) (by native_decide)
  change ∀ p ∈ patches v, 10564 ≤ p.1 ∨ p.1 + 32 ≤ 10563
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals omega

theorem uniswapV3PoolFeeGetterDupDecode {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    decode code ⟨10597⟩ = some (.DUP2, .none) := by
  refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨10597⟩) (byte := 0x81)
    (op := .DUP2) hpatch (by native_decide) ?_ (by native_decide)
    (by native_decide) (by native_decide)
  change ∀ p ∈ patches v, 10598 ≤ p.1 ∨ p.1 + 32 ≤ 10597
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals omega

theorem uniswapV3PoolFeeGetterJumpDecode {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    decode code ⟨10598⟩ = some (.JUMP, .none) := by
  refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨10598⟩) (byte := 0x56)
    (op := .JUMP) hpatch (by native_decide) ?_ (by native_decide)
    (by native_decide) (by native_decide)
  change ∀ p ∈ patches v, 10599 ≤ p.1 ∨ p.1 + 32 ≤ 10598
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals omega

theorem uniswapV3PoolFeeEntryWf {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcGetterEntryWf code ⟨2048⟩ ⟨2056⟩ ⟨10563⟩ := by
  dsimp [solcGetterEntryWf]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide

theorem uniswapV3PoolFeeGetterWf {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcConstGetterWf code ⟨10563⟩ (EVM.wordOfInt v.fee) 32 .PUSH32 := by
  dsimp [solcConstGetterWf]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact uniswapV3PoolFeeGetterJumpdestDecode hpatch
  · native_decide
  · exact uniswapV3PoolFeeConstDecode hpatch
  · exact uniswapV3PoolFeeGetterDupDecode hpatch
  · exact uniswapV3PoolFeeGetterJumpDecode hpatch

@[reducible] def solcReturnUint24FromMemWf (code : ByteArray) (pc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p9 := p5 + UInt256.ofNat 4
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p21 := p19 + UInt256.ofNat 2
  let p22 := p21 + ⟨1⟩
  let p23 := p22 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p3 = some (.DUP1, .none)
  ∧ decode code p4 = some (.MLOAD, .none)
  ∧ decode code p5 = some (.Push .PUSH3, some (uint24Mask, 3))
  ∧ decode code p9 = some (.SWAP1, .none)
  ∧ decode code p10 = some (.SWAP3, .none)
  ∧ decode code p11 = some (.AND, .none)
  ∧ decode code p12 = some (.DUP3, .none)
  ∧ decode code p13 = some (.MSTORE, .none)
  ∧ decode code p14 = some (.MLOAD, .none)
  ∧ decode code p15 = some (.SWAP1, .none)
  ∧ decode code p16 = some (.DUP2, .none)
  ∧ decode code p17 = some (.SWAP1, .none)
  ∧ decode code p18 = some (.SUB, .none)
  ∧ decode code p19 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p21 = some (.ADD, .none)
  ∧ decode code p22 = some (.SWAP1, .none)
  ∧ decode code p23 = some (.RETURN, .none)

theorem RD.solcReturnUint24FromMem {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc val ret : UInt256} {R : List UInt256}
    {mem memout rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (val :: ret :: R) mem (UInt256.ofNat 3) rdata acc k C)
    (hwf : solcReturnUint24FromMemWf code pc)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hmemout :
      (UInt256.toByteArray (UInt256.land val uint24Mask)).write 0 mem 128 32 = memout)
    (hmemoutLoad64 :
      (if (⟨64⟩ : UInt256).toNat ≥ memout.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memout.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hread128 :
      memout.readWithPadding 128 32 = UInt256.toByteArray (UInt256.land val uint24Mask))
    (hov : R.length + 9 ≤ 1024) :
    RDret code g s0 acc (UInt256.toByteArray (UInt256.land val uint24Mask)) := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hd5, hd9, hd10, hd11, hd12, hd13, hd14, hd15, hd16,
      hd17, hd18, hd19, hd21, hd22, hd23⟩
  exact evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨64⟩ hd1 (by evm_ov),
    raw dup1 hd3 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd4 mem_cost hmload64 (by decide) (by evm_ov),
    raw pushConst uint24Mask (by native_decide) hd5 (by evm_ov),
    raw swap1 hd9 (by evm_ov),
    raw swap3 hd10 (by evm_ov),
    raw and hd11 (by evm_ov),
    raw dup3 hd12 (by evm_ov),
    raw mstore 6 memout (UInt256.ofNat 5) hd13 mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        exact hmemout)
      (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) hd14 mem_cost hmemoutLoad64 (by decide)
      (by evm_ov),
    raw swap1 hd15 (by evm_ov),
    raw dup2 hd16 (by evm_ov),
    raw swap1 hd17 (by evm_ov),
    raw sub hd18 (by evm_ov),
    raw push1 ⟨32⟩ hd19 (by evm_ov),
    raw add hd21 (by evm_ov),
    raw swap1 hd22 (by evm_ov),
    raw ret 0 (UInt256.toByteArray (UInt256.land val uint24Mask)) hd23 mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show ((⟨32⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat = 32
            from by decide]
        exact hread128)
      (by evm_ov)]

theorem RD.solcUint24ConstGetterExternal {code : ByteArray} {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel entry routine returnPc val : UInt256} {width : Nat}
    {op : Operation.POp}
    (hreach : ∃ k C, RD code I g (Reasoning.Theory.initState cA gh bl σ σ₀ g A I)
      entry [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hgetter : solcConstGetterWf code routine val width op)
    (hroutine : (D_J code 0).contains routine = true)
    (hret : (D_J code 0).contains returnPc = true)
    (hreturn : solcReturnUint24FromMemWf code returnPc) :
    RDret code g (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.land val uint24Mask)) := by
  obtain ⟨_, _, rdRoutine⟩ := RD.solcGetterThunk hreach hentry hroutine
  obtain ⟨_, _, rdReturn⟩ := RD.solcConstGetter (val := val) (width := width)
    (op := op) (R := [sel]) rdRoutine hgetter hret
    (by simp only [List.length_singleton]; omega)
  exact RD.solcReturnUint24FromMem rdReturn hreturn
    solcFreePtrMem_mload64
    (by rfl)
    (solcReturnMem_mload64 (UInt256.land val uint24Mask))
    (solcReturnMem_read128 (UInt256.land val uint24Mask))
    (by simp only [List.length_singleton]; omega)

theorem uniswapV3PoolFeeReturnWf {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcReturnUint24FromMemWf code ⟨2056⟩ := by
  dsimp [solcReturnUint24FromMemWf]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide

theorem uniswapV3PoolFeeReturnJumpDest {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨2056⟩ = true :=
  uniswapV3PoolJumpDestPatched2258 hpatch (by native_decide)

theorem uniswapV3PoolFeeEvm {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 22 == I.calldata.extract 0 4) = true) :
    RDret code g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.land (EVM.wordOfInt v.fee) uint24Mask)) := by
  have hreach := uniswapV3PoolFeeReachEntry
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize hsel
  exact RD.solcUint24ConstGetterExternal
    (sel := solcSelectorWord I) (entry := ⟨2048⟩) (routine := ⟨10563⟩)
    (returnPc := ⟨2056⟩) (val := EVM.wordOfInt v.fee) (width := 32)
    (op := .PUSH32) hreach
    (uniswapV3PoolFeeEntryWf hpatch)
    (uniswapV3PoolFeeGetterWf hpatch)
    (uniswapV3PoolJumpDestPatched10563 hpatch)
    (uniswapV3PoolFeeReturnJumpDest hpatch)
    (uniswapV3PoolFeeReturnWf hpatch)

theorem uniswapV3PoolFeeSourceBody {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (∅ : Store) (feeTransition v).body
      (.returned { contract := contract v, locals := ∅ }
        (initState cA gh bl σ σ₀ g A I)
        (some [Value.int v.fee])) := by
  change ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (∅ : Store)
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return [.intLit v.fee] ] _
  exact nonpayableIntLiteralBodyReturns (initState cA gh bl σ σ₀ g A I)
    (∅ : Store) v.fee hwv

theorem uniswapV3PoolFeeBodyCore {v : PoolImmutables}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsel : (uniswapV3PoolSelBytes 22 == I.calldata.extract 0 4) = true) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdispatch := uniswapV3PoolDispatch_fee (v := v) (cd := I.calldata) hsel
  have hdecode := uniswapV3PoolFeeDecode (v := v) (I := I) hsz
  have hbody := uniswapV3PoolFeeSourceBody (v := v) (cA := cA) (gh := gh)
    (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hwv
  have hrd := uniswapV3PoolFeeEvm (v := v) (code := code) (cA := cA)
    (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hpatch hcode hwv hsz hsize hsel
  have hmask := uint24MaskCleanOfInt v.fee v.fee_nonneg v.fee_lt
  exact hrd.reEquivExecution hcode hdispatch hdecode hbody hAccounts
    (returnEquiv_of_encode (by
      simpa [hmask] using uint24ReturnEncodingInt v.fee v.fee_nonneg v.fee_lt))

end Benchmarks.UniswapV3Pool
