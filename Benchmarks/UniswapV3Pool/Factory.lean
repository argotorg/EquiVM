import Benchmarks.UniswapV3Pool.ImmutableGetters

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

theorem uniswapV3PoolFactoryReachEntry {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 19 == I.calldata.extract 0 4) = true) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨2001⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := uniswapV3PoolReachSelector32
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize
  have hword : solcSelectorWord I = uniswapV3PoolSelNat 19 := by
    simpa [uniswapV3PoolSelBytes, uniswapV3PoolSelNat] using
      solcSelectorWord_eq_of_beq I hsz 0xc4 0x5a 0x01 0x55
        (uniswapV3PoolSelNat 19) (by native_decide) hsel
  have hgt32 : UInt256.gt (armSelNat code ⟨32⟩) (solcSelectorWord I) = ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h43 := uniswapV3PoolSelectorSplitNotTakenTo (next := ⟨43⟩) hpatch h32 hgt32
  have hgt43 : UInt256.gt (armSelNat code ⟨43⟩) (solcSelectorWord I) = ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h54 := uniswapV3PoolSelectorSplitNotTakenTo (next := ⟨54⟩) hpatch h43 hgt43
  have hgt54 : UInt256.gt (armSelNat code ⟨54⟩) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h114 := uniswapV3PoolSelectorSplitTakenTo (next := ⟨114⟩) hpatch h54 hgt54
  have h2001 := uniswapV3PoolSelectorArmHitTo (i := 19) (target := ⟨2001⟩)
    hpatch hsz hsel h114
  exact ⟨_, _, h2001⟩

theorem uniswapV3PoolFactoryDecode {v : PoolImmutables} {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode ((factoryTransition v).params.map Param.name)
      (transitionSignature (factoryTransition v)).paramTypes I.calldata = some (∅ : Store) := by
  simpa [config, factoryTransition, transitionSignature] using
    decodeCalldataWithMode_empty_ok (mode := DecodeMode.legacySolc05) (cd := I.calldata) hsz

theorem uniswapV3PoolDispatch_factory {v : PoolImmutables} {cd : ByteArray}
    (hsel : (uniswapV3PoolSelBytes 19 == cd.extract 0 4) = true) :
    dispatchMsg (contract v) cd = some (factoryTransition v) := by
  apply dispatchMsg_eq_some_of_split
    (pre := [burnTransition, collectTransition v, collectprotocolTransition v])
    (post := [feeTransition v, feegrowthglobal0X128Transition, feegrowthglobal1X128Transition,
      flashTransition v, increaseobservationcardinalitynextTransition v, initializeTransition,
      liquidityTransition, maxliquiditypertickTransition v, mintTransition v, observationsTransition,
      observeTransition v, positionsTransition, protocolfeesTransition, setfeeprotocolTransition v,
      slot0Transition, snapshotcumulativesinsideTransition v, swapTransition v, tickbitmapTransition,
      tickspacingTransition v, ticksTransition, token0Transition v, token1Transition v])
  · simp [contract, transitions]
  · intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl
    · rw [selectorOf, burnSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 17) (j := 19)
          (by native_decide) hsel
    · rw [selectorOf, collectSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 10) (j := 19)
          (by native_decide) hsel
    · rw [selectorOf, collectProtocolSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 15) (j := 19)
          (by native_decide) hsel
  · rw [selectorOf, factorySelectorBytes v]
    simpa [uniswapV3PoolSelBytes] using hsel

theorem uniswapV3PoolFactoryEntryWf {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcGetterEntryWf code ⟨2001⟩ ⟨443⟩ ⟨10455⟩ := by
  dsimp [solcGetterEntryWf]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide

theorem uniswapV3PoolFactoryGetterWf {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcConstGetterWf code ⟨10455⟩ (EVM.Word.ofNat v.factory.toNat) 32 .PUSH32 := by
  dsimp [solcConstGetterWf]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact uniswapV3PoolFactoryGetterJumpdestDecode hpatch
  · native_decide
  · exact uniswapV3PoolFactoryConstDecode hpatch
  · exact uniswapV3PoolFactoryGetterDupDecode hpatch
  · exact uniswapV3PoolFactoryGetterJumpDecode hpatch

theorem uniswapV3PoolFactoryReturnWf {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcReturnAddressFromMemWf code ⟨443⟩ :=
  uniswapV3PoolReturnAddress443Wf hpatch

theorem uniswapV3PoolFactoryRoutineJumpDest {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨10455⟩ = true :=
  uniswapV3PoolJumpDestPatched10455 hpatch

theorem uniswapV3PoolFactoryReturnJumpDest {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨443⟩ = true :=
  uniswapV3PoolReturn443JumpDest hpatch

theorem uniswapV3PoolFactoryEvm {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 19 == I.calldata.extract 0 4) = true) :
    RDret code g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.land (EVM.Word.ofNat v.factory.toNat) solcAddrMask)) := by
  have hreach := uniswapV3PoolFactoryReachEntry
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize hsel
  exact RD.solcAddressConstGetterExternal
    (sel := solcSelectorWord I) (entry := ⟨2001⟩) (routine := ⟨10455⟩)
    (returnPc := ⟨443⟩) (val := EVM.Word.ofNat v.factory.toNat) (width := 32)
    (op := .PUSH32) hreach
    (uniswapV3PoolFactoryEntryWf hpatch)
    (uniswapV3PoolFactoryGetterWf hpatch)
    (uniswapV3PoolFactoryRoutineJumpDest hpatch)
    (uniswapV3PoolFactoryReturnJumpDest hpatch)
    (uniswapV3PoolFactoryReturnWf hpatch)

theorem uniswapV3PoolFactorySourceBody {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (∅ : Store) (factoryTransition v).body
      (.returned { contract := contract v, locals := ∅ }
        (initState cA gh bl σ σ₀ g A I)
        (some [Value.address (AccountAddress.ofNat v.factory.toNat)])) := by
  change ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (∅ : Store)
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return [addrLit v.factory] ] _
  apply nonpayableReturnExprBodyReturns
  · simp [initState, hwv]
  · exact uniswapV3PoolAddrLitEval (v := v) (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v.factory

theorem uniswapV3PoolFactoryValueTransport {v : PoolImmutables} :
    some [Value.address (AccountAddress.ofNat v.factory.toNat)] =
      some [Value.address (AccountAddress.ofNat
        (UInt256.land (EVM.Word.ofNat v.factory.toNat) solcAddrMask).toNat)] :=
  uniswapV3PoolAddressValueTransport v.factory

theorem uniswapV3PoolFactoryBodyCore {v : PoolImmutables}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsel : (uniswapV3PoolSelBytes 19 == I.calldata.extract 0 4) = true) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdispatch := uniswapV3PoolDispatch_factory (v := v) (cd := I.calldata) hsel
  have hdecode := uniswapV3PoolFactoryDecode (v := v) (I := I) hsz
  have hbody := uniswapV3PoolFactorySourceBody (v := v) (cA := cA) (gh := gh)
    (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hwv
  have hrd := uniswapV3PoolFactoryEvm (v := v) (code := code) (cA := cA)
    (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hpatch hcode hwv hsz hsize hsel
  exact hrd.reEquivExecutionTransport hcode hdispatch hdecode hbody
    (uniswapV3PoolFactoryValueTransport (v := v)) hAccounts
    (returnEquiv_of_encode
      (solcAddressReturnEncoding rfl (EVM.Word.ofNat v.factory.toNat)))

end Benchmarks.UniswapV3Pool
