import Benchmarks.UniswapV3Pool.Common

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

theorem uniswapV3PoolFeeGrowthGlobal0X128ReachEntry {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 23 == I.calldata.extract 0 4) = true) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨2080⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := uniswapV3PoolReachSelector32
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize
  have hword : solcSelectorWord I = uniswapV3PoolSelNat 23 := by
    simpa [uniswapV3PoolSelBytes, uniswapV3PoolSelNat] using
      solcSelectorWord_eq_of_beq I hsz 0xf3 0x05 0x83 0x99
        (uniswapV3PoolSelNat 23) (by native_decide) hsel
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
  have h2080 := uniswapV3PoolSelectorArmHitTo (i := 23) (target := ⟨2080⟩)
    hpatch hsz hsel h76
  exact ⟨_, _, h2080⟩

theorem uniswapV3PoolFeeGrowthGlobal0X128Decode {v : PoolImmutables} {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode
      (feegrowthglobal0X128Transition.params.map Param.name)
      (transitionSignature feegrowthglobal0X128Transition).paramTypes I.calldata =
        some (∅ : Store) := by
  simpa [config, feegrowthglobal0X128Transition, transitionSignature] using
    decodeCalldataWithMode_empty_ok (mode := DecodeMode.legacySolc05) (cd := I.calldata) hsz

theorem uniswapV3PoolDispatch_feeGrowthGlobal0X128 {v : PoolImmutables} {cd : ByteArray}
    (hsel : (uniswapV3PoolSelBytes 23 == cd.extract 0 4) = true) :
    dispatchMsg (contract v) cd = some feegrowthglobal0X128Transition := by
  apply dispatchMsg_eq_some_of_split
    (pre := [burnTransition, collectTransition v, collectprotocolTransition v,
      factoryTransition v, feeTransition v])
    (post := [feegrowthglobal1X128Transition, flashTransition v,
      increaseobservationcardinalitynextTransition v, initializeTransition, liquidityTransition,
      maxliquiditypertickTransition v, mintTransition v, observationsTransition,
      observeTransition v, positionsTransition, protocolfeesTransition, setfeeprotocolTransition v,
      slot0Transition, snapshotcumulativesinsideTransition v, swapTransition v,
      tickbitmapTransition, tickspacingTransition v, ticksTransition, token0Transition v,
      token1Transition v])
  · simp [contract, transitions]
  · intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · rw [selectorOf, burnSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 17) (j := 23)
          (by native_decide) hsel
    · rw [selectorOf, collectSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 10) (j := 23)
          (by native_decide) hsel
    · rw [selectorOf, collectProtocolSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 15) (j := 23)
          (by native_decide) hsel
    · rw [selectorOf, factorySelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 19) (j := 23)
          (by native_decide) hsel
    · rw [selectorOf, feeSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 22) (j := 23)
          (by native_decide) hsel
  · rw [selectorOf, feeGrowthGlobal0X128SelectorBytes]
    simpa [uniswapV3PoolSelBytes] using hsel

private theorem uniswapV3PoolFeeGrowthGlobal0X128PatchDisjoint {v : PoolImmutables}
    {pc : UInt256} (hlo : 10599 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 11259) :
    ∀ p ∈ patches v, pc.toNat + 33 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    omega

theorem uniswapV3PoolFeeGrowthGlobal0X128EntryWf {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcGetterEntryWf code ⟨2080⟩ ⟨1118⟩ ⟨10599⟩ := by
  dsimp [solcGetterEntryWf]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide

theorem uniswapV3PoolFeeGrowthGlobal0X128GetterWf {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcWordSlotGetterWf code ⟨10599⟩ ⟨1⟩ := by
  dsimp [solcWordSlotGetterWf]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
      (uniswapV3PoolFeeGrowthGlobal0X128PatchDisjoint
        (by native_decide) (by native_decide))]
    native_decide

theorem uniswapV3PoolFeeGrowthGlobal0X128ReturnWf {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcReturnWordFromMemWf code ⟨1118⟩ := by
  dsimp [solcReturnWordFromMemWf]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide

theorem uniswapV3PoolFeeGrowthGlobal0X128RoutineJumpDest {v : PoolImmutables}
    {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨10599⟩ = true :=
  uniswapV3PoolJumpDestPatched10599 hpatch

theorem uniswapV3PoolFeeGrowthGlobal0X128ReturnJumpDest {v : PoolImmutables}
    {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨1118⟩ = true :=
  uniswapV3PoolJumpDestPatched2258 hpatch (by native_decide)

theorem uniswapV3PoolFeeGrowthGlobal0X128Evm {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 23 == I.calldata.extract 0 4) = true) :
    RDret code g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (solcSlotWord σ I ⟨1⟩)) := by
  have hreach := uniswapV3PoolFeeGrowthGlobal0X128ReachEntry
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize hsel
  exact RD.solcWordGetterExternal (slot := ⟨1⟩) hreach
    (uniswapV3PoolFeeGrowthGlobal0X128EntryWf hpatch)
    (uniswapV3PoolFeeGrowthGlobal0X128GetterWf hpatch)
    (uniswapV3PoolFeeGrowthGlobal0X128RoutineJumpDest hpatch)
    (uniswapV3PoolFeeGrowthGlobal0X128ReturnJumpDest hpatch)
    (uniswapV3PoolFeeGrowthGlobal0X128ReturnWf hpatch)

theorem uniswapV3PoolFeeGrowthGlobal0X128SourceBody {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (∅ : Store) feegrowthglobal0X128Transition.body
      (.returned { contract := contract v, locals := ∅ }
        (initState cA gh bl σ σ₀ g A I)
        (some [Value.int (Int.ofNat (solcSlotWord σ I ⟨1⟩).toNat)])) := by
  change ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (∅ : Store)
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return [.storage feeGrowthGlobal0X128Ref] ] _
  apply nonpayableReturnExprBodyReturns
  · simp [initState, hwv]
  · apply evalExpr_storage_scalar_value
      (er := { base := "feeGrowthGlobal0X128", steps := [] })
      (t := .int uint256Int)
      (loc := loc ⟨1⟩ ⟨0, by decide⟩ ⟨32, by decide⟩ (by decide) (.int uint256Int))
    · simp [feeGrowthGlobal0X128Ref]
    · simp [evalStorageRef, feeGrowthGlobal0X128Ref, pure, bind, EvalResult.bind]
    · simp [contract, storageDecls, storageTypeAt?, uint256St]
    · funext evm
      simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout, loc]
    · simpa [initState, solcSlotWord, loc, uint256Loc] using
        (storageLocLoad_uint256 (initState cA gh bl σ σ₀ g A I) ⟨1⟩)

theorem uniswapV3PoolFeeGrowthGlobal0X128ValueTransport {σ_evm σ_solm : AccountMap}
    {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    some [Value.int (Int.ofNat (solcSlotWord σ_solm I ⟨1⟩).toNat)] =
      some [Value.int (Int.ofNat (solcSlotWord σ_evm I ⟨1⟩).toNat)] := by
  have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ (⟨0⟩ : UInt256)
  dsimp [solcSlotWord]
  rw [← hslot]

theorem uniswapV3PoolFeeGrowthGlobal0X128BodyCore {v : PoolImmutables}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsel : (uniswapV3PoolSelBytes 23 == I.calldata.extract 0 4) = true) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdispatch := uniswapV3PoolDispatch_feeGrowthGlobal0X128 (v := v) (cd := I.calldata) hsel
  have hdecode := uniswapV3PoolFeeGrowthGlobal0X128Decode (v := v) (I := I) hsz
  have hbody := uniswapV3PoolFeeGrowthGlobal0X128SourceBody (v := v) (cA := cA)
    (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hwv
  have hvalue := uniswapV3PoolFeeGrowthGlobal0X128ValueTransport (σ_evm := σ_evm)
    (σ_solm := σ_solm) (I := I) hAccounts
  have hrd := uniswapV3PoolFeeGrowthGlobal0X128Evm (v := v) (code := code) (cA := cA)
    (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hpatch hcode hwv hsz hsize hsel
  exact hrd.reEquivExecutionTransport hcode hdispatch hdecode hbody hvalue hAccounts
    (returnEquiv_of_encode (uint256ReturnEncoding (solcSlotWord σ_evm I ⟨1⟩)))

end Benchmarks.UniswapV3Pool
