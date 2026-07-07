import Benchmarks.UniswapV3Pool.Common

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.UniswapV3Pool

theorem uniswapV3PoolFeeGrowthGlobal1X128ReachEntry {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 8 == I.calldata.extract 0 4) = true) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨1110⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := uniswapV3PoolReachSelector32
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize
  have hword : solcSelectorWord I = uniswapV3PoolSelNat 8 := by
    simpa [uniswapV3PoolSelBytes, uniswapV3PoolSelNat] using
      solcSelectorWord_eq_of_beq I hsz 0x46 0x14 0x13 0x19
        (uniswapV3PoolSelNat 8) (by native_decide) hsel
  have hgt32 : UInt256.gt (armSelNat code ⟨32⟩) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h239 := uniswapV3PoolSelectorSplitTakenTo (next := ⟨239⟩) hpatch h32 hgt32
  have hgt239 : UInt256.gt (armSelNat code ⟨239⟩) (solcSelectorWord I) = ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h250 := uniswapV3PoolSelectorSplitNotTakenTo (next := ⟨250⟩) hpatch h239 hgt239
  have hgt250 : UInt256.gt (armSelNat code ⟨250⟩) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h310 := uniswapV3PoolSelectorSplitTakenTo (next := ⟨310⟩) hpatch h250 hgt250
  have hmiss6 : (uniswapV3PoolSelBytes 6 == I.calldata.extract 0 4) = false :=
    uniswapV3PoolSelectorMissOfHit I (by native_decide) hsel
  have h321 := uniswapV3PoolSelectorArmMissToOf (i := 6) (next := ⟨321⟩)
    hpatch hsz hmiss6 h310
  have hmiss7 : (uniswapV3PoolSelBytes 7 == I.calldata.extract 0 4) = false :=
    uniswapV3PoolSelectorMissOfHit I (by native_decide) hsel
  have h332 := uniswapV3PoolSelectorArmMissToOf (i := 7) (next := ⟨332⟩)
    hpatch hsz hmiss7 h321
  have h1110 := uniswapV3PoolSelectorArmHitTo (i := 8) (target := ⟨1110⟩)
    hpatch hsz hsel h332
  exact ⟨_, _, h1110⟩

theorem uniswapV3PoolFeeGrowthGlobal1X128Decode {v : PoolImmutables} {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode
      (feegrowthglobal1X128Transition.params.map Param.name)
      (transitionSignature feegrowthglobal1X128Transition).paramTypes I.calldata =
        some (∅ : Store) := by
  simpa [config, feegrowthglobal1X128Transition, transitionSignature] using
    decodeCalldataWithMode_empty_ok (mode := DecodeMode.legacySolc05) (cd := I.calldata) hsz

theorem uniswapV3PoolDispatch_feeGrowthGlobal1X128 {v : PoolImmutables} {cd : ByteArray}
    (hsel : (uniswapV3PoolSelBytes 8 == cd.extract 0 4) = true) :
    dispatchMsg (contract v) cd = some feegrowthglobal1X128Transition := by
  apply dispatchMsg_eq_some_of_split
    (pre := [burnTransition, collectTransition v, collectprotocolTransition v,
      factoryTransition v, feeTransition v, feegrowthglobal0X128Transition])
    (post := [flashTransition v, increaseobservationcardinalitynextTransition v,
      initializeTransition, liquidityTransition, maxliquiditypertickTransition v, mintTransition v,
      observationsTransition, observeTransition v, positionsTransition, protocolfeesTransition,
      setfeeprotocolTransition v, slot0Transition, snapshotcumulativesinsideTransition v,
      swapTransition v, tickbitmapTransition, tickspacingTransition v, ticksTransition,
      token0Transition v, token1Transition v])
  · simp [contract, transitions]
  · intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [selectorOf, burnSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 17) (j := 8)
          (by native_decide) hsel
    · rw [selectorOf, collectSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 10) (j := 8)
          (by native_decide) hsel
    · rw [selectorOf, collectProtocolSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 15) (j := 8)
          (by native_decide) hsel
    · rw [selectorOf, factorySelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 19) (j := 8)
          (by native_decide) hsel
    · rw [selectorOf, feeSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 22) (j := 8)
          (by native_decide) hsel
    · rw [selectorOf, feeGrowthGlobal0X128SelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 23) (j := 8)
          (by native_decide) hsel
  · rw [selectorOf, feeGrowthGlobal1X128SelectorBytes]
    simpa [uniswapV3PoolSelBytes] using hsel

private theorem uniswapV3PoolFeeGrowthGlobal1X128PatchDisjoint {v : PoolImmutables}
    {pc : UInt256} (hlo : 6434 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 6603) :
    ∀ p ∈ patches v, pc.toNat + 33 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    omega

theorem uniswapV3PoolFeeGrowthGlobal1X128EntryWf {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcGetterEntryWf code ⟨1110⟩ ⟨1118⟩ ⟨6434⟩ := by
  dsimp [solcGetterEntryWf]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide

theorem uniswapV3PoolFeeGrowthGlobal1X128GetterWf {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcWordSlotGetterWf code ⟨6434⟩ ⟨2⟩ := by
  dsimp [solcWordSlotGetterWf]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
      (uniswapV3PoolFeeGrowthGlobal1X128PatchDisjoint
        (by native_decide) (by native_decide))]
    native_decide

theorem uniswapV3PoolFeeGrowthGlobal1X128ReturnWf {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcReturnWordFromMemWf code ⟨1118⟩ := by
  dsimp [solcReturnWordFromMemWf]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide

theorem uniswapV3PoolFeeGrowthGlobal1X128RoutineJumpDest {v : PoolImmutables}
    {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨6434⟩ = true :=
  uniswapV3PoolJumpDestPatched6434 hpatch

theorem uniswapV3PoolFeeGrowthGlobal1X128ReturnJumpDest {v : PoolImmutables}
    {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨1118⟩ = true :=
  uniswapV3PoolJumpDestPatched2258 hpatch (by native_decide)

theorem uniswapV3PoolFeeGrowthGlobal1X128Evm {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 8 == I.calldata.extract 0 4) = true) :
    RDret code g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (solcSlotWord σ I ⟨2⟩)) := by
  have hreach := uniswapV3PoolFeeGrowthGlobal1X128ReachEntry
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize hsel
  exact RD.solcWordGetterExternal (slot := ⟨2⟩) hreach
    (uniswapV3PoolFeeGrowthGlobal1X128EntryWf hpatch)
    (uniswapV3PoolFeeGrowthGlobal1X128GetterWf hpatch)
    (uniswapV3PoolFeeGrowthGlobal1X128RoutineJumpDest hpatch)
    (uniswapV3PoolFeeGrowthGlobal1X128ReturnJumpDest hpatch)
    (uniswapV3PoolFeeGrowthGlobal1X128ReturnWf hpatch)

theorem uniswapV3PoolFeeGrowthGlobal1X128SourceBody {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (∅ : Store) feegrowthglobal1X128Transition.body
      (.returned { contract := contract v, locals := ∅ }
        (initState cA gh bl σ σ₀ g A I)
        (some [Value.int (Int.ofNat (solcSlotWord σ I ⟨2⟩).toNat)])) := by
  change ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (∅ : Store)
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return [.storage feeGrowthGlobal1X128Ref] ] _
  apply nonpayableReturnExprBodyReturns
  · simp [initState, hwv]
  · apply evalExpr_storage_scalar_value
      (er := { base := "feeGrowthGlobal1X128", steps := [] })
      (t := .int uint256Int)
      (loc := loc ⟨2⟩ ⟨0, by decide⟩ ⟨32, by decide⟩ (by decide) (.int uint256Int))
    · simp [feeGrowthGlobal1X128Ref]
    · simp [evalStorageRef, feeGrowthGlobal1X128Ref, pure, bind, EvalResult.bind]
    · simp [contract, storageDecls, storageTypeAt?, uint256St]
    · funext evm
      simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout, loc]
    · simpa [initState, solcSlotWord, loc, uint256Loc] using
        (storageLocLoad_uint256 (initState cA gh bl σ σ₀ g A I) ⟨2⟩)

theorem uniswapV3PoolFeeGrowthGlobal1X128ValueTransport {σ_evm σ_solm : AccountMap}
    {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    some [Value.int (Int.ofNat (solcSlotWord σ_solm I ⟨2⟩).toNat)] =
      some [Value.int (Int.ofNat (solcSlotWord σ_evm I ⟨2⟩).toNat)] := by
  have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ (⟨0⟩ : UInt256)
  dsimp [solcSlotWord]
  rw [← hslot]

theorem uniswapV3PoolFeeGrowthGlobal1X128BodyCore {v : PoolImmutables}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsel : (uniswapV3PoolSelBytes 8 == I.calldata.extract 0 4) = true) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdispatch := uniswapV3PoolDispatch_feeGrowthGlobal1X128 (v := v) (cd := I.calldata) hsel
  have hdecode := uniswapV3PoolFeeGrowthGlobal1X128Decode (v := v) (I := I) hsz
  have hbody := uniswapV3PoolFeeGrowthGlobal1X128SourceBody (v := v) (cA := cA)
    (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hwv
  have hvalue := uniswapV3PoolFeeGrowthGlobal1X128ValueTransport (σ_evm := σ_evm)
    (σ_solm := σ_solm) (I := I) hAccounts
  have hrd := uniswapV3PoolFeeGrowthGlobal1X128Evm (v := v) (code := code) (cA := cA)
    (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hpatch hcode hwv hsz hsize hsel
  exact hrd.reEquivExecutionTransport hcode hdispatch hdecode hbody hvalue hAccounts
    (returnEquiv_of_encode (uint256ReturnEncoding (solcSlotWord σ_evm I ⟨2⟩)))

end Benchmarks.UniswapV3Pool
