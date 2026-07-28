import Benchmarks.UniswapV3Pool.Common

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

theorem uniswapV3PoolToken0ReachEntry {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 0 == I.calldata.extract 0 4) = true) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨435⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := uniswapV3PoolReachSelector32
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize
  have hword : solcSelectorWord I = uniswapV3PoolSelNat 0 := by
    simpa [uniswapV3PoolSelBytes, uniswapV3PoolSelNat] using
      solcSelectorWord_eq_of_beq I hsz 0x0d 0xfe 0x16 0x81
        (uniswapV3PoolSelNat 0) (by native_decide) hsel
  have hgt32 : UInt256.gt (armSelNat code ⟨32⟩) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h239 := uniswapV3PoolSelectorSplitTakenTo (next := ⟨239⟩) hpatch h32 hgt32
  have hgt239 : UInt256.gt (armSelNat code ⟨239⟩) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h348 := uniswapV3PoolSelectorSplitTakenTo (next := ⟨348⟩) hpatch h239 hgt239
  have hgt348 : UInt256.gt (armSelNat code ⟨348⟩) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h397 := uniswapV3PoolSelectorSplitTakenTo (next := ⟨397⟩) hpatch h348 hgt348
  have h435 := uniswapV3PoolSelectorArmHitTo (i := 0) (target := ⟨435⟩)
    hpatch hsz hsel h397
  exact ⟨_, _, h435⟩

theorem uniswapV3PoolToken0Decode {v : PoolImmutables} {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode ((token0Transition v).params.map Param.name)
      (transitionSignature (token0Transition v)).paramTypes I.calldata = some (∅ : Store) := by
  simpa [config, token0Transition, transitionSignature] using
    decodeCalldataWithMode_empty_ok (mode := DecodeMode.legacySolc05) (cd := I.calldata) hsz

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolDispatch_token0 {v : PoolImmutables} {cd : ByteArray}
    (hsel : (uniswapV3PoolSelBytes 0 == cd.extract 0 4) = true) :
    dispatchMsg (contract v) cd = some (token0Transition v) := by
  apply dispatchMsg_eq_some_of_split
    (pre := [burnTransition, collectTransition v, collectprotocolTransition v, factoryTransition v,
      feeTransition v, feegrowthglobal0X128Transition, feegrowthglobal1X128Transition,
      flashTransition v, increaseobservationcardinalitynextTransition v, initializeTransition,
      liquidityTransition, maxliquiditypertickTransition v, mintTransition v, observationsTransition,
      observeTransition v, positionsTransition, protocolfeesTransition, setfeeprotocolTransition v,
      slot0Transition, snapshotcumulativesinsideTransition v, swapTransition v, tickbitmapTransition,
      tickspacingTransition v, ticksTransition])
    (post := [token1Transition v])
  · simp [contract, transitions]
  · intro t ht
    simp at ht
    rcases ht with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [selectorOf, burnSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 17) (j := 0)
          (by native_decide) hsel
    · rw [selectorOf, collectSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 10) (j := 0)
          (by native_decide) hsel
    · rw [selectorOf, collectProtocolSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 15) (j := 0)
          (by native_decide) hsel
    · rw [selectorOf, factorySelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 19) (j := 0)
          (by native_decide) hsel
    · rw [selectorOf, feeSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 22) (j := 0)
          (by native_decide) hsel
    · rw [selectorOf, feeGrowthGlobal0X128SelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 23) (j := 0)
          (by native_decide) hsel
    · rw [selectorOf, feeGrowthGlobal1X128SelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 8) (j := 0)
          (by native_decide) hsel
    · rw [selectorOf, flashSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 9) (j := 0)
          (by native_decide) hsel
    · rw [selectorOf, increaseObservationCardinalityNextSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 5) (j := 0)
          (by native_decide) hsel
    · rw [selectorOf, initializeSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 25) (j := 0)
          (by native_decide) hsel
    · rw [selectorOf, liquiditySelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 2) (j := 0)
          (by native_decide) hsel
    · rw [selectorOf, maxLiquidityPerTickSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 13) (j := 0)
          (by native_decide) hsel
    · rw [selectorOf, mintSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 7) (j := 0)
          (by native_decide) hsel
    · rw [selectorOf, observationsSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 4) (j := 0)
          (by native_decide) hsel
    · rw [selectorOf, observeSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 16) (j := 0)
          (by native_decide) hsel
    · rw [selectorOf, positionsSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 11) (j := 0)
          (by native_decide) hsel
    · rw [selectorOf, protocolFeesSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 3) (j := 0)
          (by native_decide) hsel
    · rw [selectorOf, setFeeProtocolSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 14) (j := 0)
          (by native_decide) hsel
    · rw [selectorOf, slot0SelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 6) (j := 0)
          (by native_decide) hsel
    · rw [selectorOf, snapshotCumulativesInsideSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 18) (j := 0)
          (by native_decide) hsel
    · rw [selectorOf, swapSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 1) (j := 0)
          (by native_decide) hsel
    · rw [selectorOf, tickBitmapSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 12) (j := 0)
          (by native_decide) hsel
    · rw [selectorOf, tickSpacingSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 20) (j := 0)
          (by native_decide) hsel
    · rw [selectorOf, ticksSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 24) (j := 0)
          (by native_decide) hsel
  · rw [selectorOf, token0SelectorBytes v]
    simpa [uniswapV3PoolSelBytes] using hsel

private theorem uniswapV3PoolToken0PatchDisjoint {v : PoolImmutables} {pc : UInt256}
    (hlo : 2290 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 3072) :
    ∀ p ∈ patches v, pc.toNat + 33 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    omega

theorem uniswapV3PoolToken0EntryWf {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcGetterEntryWf code ⟨435⟩ ⟨443⟩ ⟨2256⟩ := by
  dsimp [solcGetterEntryWf]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide

theorem uniswapV3PoolToken0GetterWf {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcConstGetterWf code ⟨2256⟩ (EVM.Word.ofNat v.token0.toNat) 32 .PUSH32 := by
  dsimp [solcConstGetterWf]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact uniswapV3PoolToken0GetterJumpdestDecode hpatch
  · native_decide
  · exact uniswapV3PoolToken0ConstDecode hpatch
  · rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
      (uniswapV3PoolToken0PatchDisjoint (by native_decide) (by native_decide))]
    native_decide
  · rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
      (uniswapV3PoolToken0PatchDisjoint (by native_decide) (by native_decide))]
    native_decide

theorem uniswapV3PoolToken0ReturnWf {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcReturnAddressFromMemWf code ⟨443⟩ :=
  uniswapV3PoolReturnAddress443Wf hpatch

theorem uniswapV3PoolToken0RoutineJumpDest {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨2256⟩ = true :=
  uniswapV3PoolJumpDestPatched2258 hpatch (by native_decide)

theorem uniswapV3PoolToken0ReturnJumpDest {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨443⟩ = true :=
  uniswapV3PoolReturn443JumpDest hpatch

theorem uniswapV3PoolToken0Evm {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 0 == I.calldata.extract 0 4) = true) :
    RDret code g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.land (EVM.Word.ofNat v.token0.toNat) solcAddrMask)) := by
  have hreach := uniswapV3PoolToken0ReachEntry
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize hsel
  exact RD.solcAddressConstGetterExternal
    (sel := solcSelectorWord I) (entry := ⟨435⟩) (routine := ⟨2256⟩)
    (returnPc := ⟨443⟩) (val := EVM.Word.ofNat v.token0.toNat) (width := 32)
    (op := .PUSH32) hreach
    (uniswapV3PoolToken0EntryWf hpatch)
    (uniswapV3PoolToken0GetterWf hpatch)
    (uniswapV3PoolToken0RoutineJumpDest hpatch)
    (uniswapV3PoolToken0ReturnJumpDest hpatch)
    (uniswapV3PoolToken0ReturnWf hpatch)

theorem uniswapV3PoolToken0SourceBody {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (∅ : Store) (token0Transition v).body
      (.returned { contract := contract v, locals := ∅ }
        (initState cA gh bl σ σ₀ g A I)
        (some [Value.address (AccountAddress.ofNat v.token0.toNat)])) := by
  change ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (∅ : Store)
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return [addrLit v.token0] ] _
  apply nonpayableReturnExprBodyReturns
  · simp [initState, hwv]
  · exact uniswapV3PoolAddrLitEval (v := v) (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v.token0

theorem uniswapV3PoolToken0ValueTransport {v : PoolImmutables} :
    some [Value.address (AccountAddress.ofNat v.token0.toNat)] =
      some [Value.address (AccountAddress.ofNat
        (UInt256.land (EVM.Word.ofNat v.token0.toNat) solcAddrMask).toNat)] :=
  uniswapV3PoolAddressValueTransport v.token0

theorem uniswapV3PoolToken0BodyCore {v : PoolImmutables}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsel : (uniswapV3PoolSelBytes 0 == I.calldata.extract 0 4) = true) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdispatch := uniswapV3PoolDispatch_token0 (v := v) (cd := I.calldata) hsel
  have hdecode := uniswapV3PoolToken0Decode (v := v) (I := I) hsz
  have hbody := uniswapV3PoolToken0SourceBody (v := v) (cA := cA) (gh := gh)
    (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hwv
  have hrd := uniswapV3PoolToken0Evm (v := v) (code := code) (cA := cA)
    (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hpatch hcode hwv hsz hsize hsel
  exact hrd.reEquivExecutionTransport hcode hdispatch hdecode hbody
    (uniswapV3PoolToken0ValueTransport (v := v)) hAccounts
    (returnEquiv_of_encode
      (solcAddressReturnEncoding rfl (EVM.Word.ofNat v.token0.toNat)))

end Benchmarks.UniswapV3Pool
