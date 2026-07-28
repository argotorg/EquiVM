import Benchmarks.UniswapV3Pool.Uint128

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

theorem uniswapV3PoolLiquidityReachEntry {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 2 == I.calldata.extract 0 4) = true) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨646⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := uniswapV3PoolReachSelector32
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize
  have hword : solcSelectorWord I = uniswapV3PoolSelNat 2 := by
    simpa [uniswapV3PoolSelBytes, uniswapV3PoolSelNat] using
      solcSelectorWord_eq_of_beq I hsz 0x1a 0x68 0x65 0x02
        (uniswapV3PoolSelNat 2) (by native_decide) hsel
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
  have hmiss0 : (uniswapV3PoolSelBytes 0 == I.calldata.extract 0 4) = false :=
    uniswapV3PoolSelectorMissOfHit I (by native_decide) hsel
  have h408 := uniswapV3PoolSelectorArmMissToOf (i := 0) (next := ⟨408⟩)
    hpatch hsz hmiss0 h397
  have hmiss1 : (uniswapV3PoolSelBytes 1 == I.calldata.extract 0 4) = false :=
    uniswapV3PoolSelectorMissOfHit I (by native_decide) hsel
  have h419 := uniswapV3PoolSelectorArmMissToOf (i := 1) (next := ⟨419⟩)
    hpatch hsz hmiss1 h408
  have h646 := uniswapV3PoolSelectorArmHitTo (i := 2) (target := ⟨646⟩)
    hpatch hsz hsel h419
  exact ⟨_, _, h646⟩

theorem uniswapV3PoolLiquidityDecode {v : PoolImmutables} {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode (liquidityTransition.params.map Param.name)
      (transitionSignature liquidityTransition).paramTypes I.calldata = some (∅ : Store) := by
  simpa [config, liquidityTransition, transitionSignature] using
    decodeCalldataWithMode_empty_ok (mode := DecodeMode.legacySolc05) (cd := I.calldata) hsz

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolDispatch_liquidity {v : PoolImmutables} {cd : ByteArray}
    (hsel : (uniswapV3PoolSelBytes 2 == cd.extract 0 4) = true) :
    dispatchMsg (contract v) cd = some liquidityTransition := by
  apply dispatchMsg_eq_some_of_split
    (pre := [burnTransition, collectTransition v, collectprotocolTransition v, factoryTransition v,
      feeTransition v, feegrowthglobal0X128Transition, feegrowthglobal1X128Transition,
      flashTransition v, increaseobservationcardinalitynextTransition v, initializeTransition])
    (post := [maxliquiditypertickTransition v, mintTransition v, observationsTransition,
      observeTransition v, positionsTransition, protocolfeesTransition, setfeeprotocolTransition v,
      slot0Transition, snapshotcumulativesinsideTransition v, swapTransition v,
      tickbitmapTransition, tickspacingTransition v, ticksTransition, token0Transition v,
      token1Transition v])
  · simp [contract, transitions]
  · intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [selectorOf, burnSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 17) (j := 2)
          (by native_decide) hsel
    · rw [selectorOf, collectSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 10) (j := 2)
          (by native_decide) hsel
    · rw [selectorOf, collectProtocolSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 15) (j := 2)
          (by native_decide) hsel
    · rw [selectorOf, factorySelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 19) (j := 2)
          (by native_decide) hsel
    · rw [selectorOf, feeSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 22) (j := 2)
          (by native_decide) hsel
    · rw [selectorOf, feeGrowthGlobal0X128SelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 23) (j := 2)
          (by native_decide) hsel
    · rw [selectorOf, feeGrowthGlobal1X128SelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 8) (j := 2)
          (by native_decide) hsel
    · rw [selectorOf, flashSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 9) (j := 2)
          (by native_decide) hsel
    · rw [selectorOf, increaseObservationCardinalityNextSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 5) (j := 2)
          (by native_decide) hsel
    · rw [selectorOf, initializeSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 25) (j := 2)
          (by native_decide) hsel
  · rw [selectorOf, liquiditySelectorBytes]
    simpa [uniswapV3PoolSelBytes] using hsel

/- LIBRARY CANDIDATE: generalizes Reasoning.Solc.solcAddressSlotGetterWf to 128-bit masks. -/
@[reducible] def solcUint128SlotGetterWf
    (code : ByteArray) (pc slot : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p6 := p4 + UInt256.ofNat 2
  let p8 := p6 + UInt256.ofNat 2
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (slot, 1))
  ∧ decode code p3 = some (.SLOAD, .none)
  ∧ decode code p4 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p6 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p8 = some (.Push .PUSH1, some (⟨128⟩, 1))
  ∧ decode code p10 = some (.SHL, .none)
  ∧ decode code p11 = some (.SUB, .none)
  ∧ decode code p12 = some (.AND, .none)
  ∧ decode code p13 = some (.DUP2, .none)
  ∧ decode code p14 = some (.JUMP, .none)

theorem RD.solcUint128SlotGetter {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc slot ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (ret :: R) mem aw rdata (cA, σ) k C)
    (hwf : solcUint128SlotGetterWf code pc slot)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (UInt256.land uint128Mask
        (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)) ::
        ret :: R) mem aw rdata (cA, σ) k' C' := by
  rcases hwf with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 slot hd1 (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd4⟩ := rd3.sload hd2 (by simp only [List.length_cons]; omega)
  have rd6 := rd4.push1 ⟨1⟩ hd3 (by simp only [List.length_cons]; omega)
  have rd8 := rd6.push1 ⟨1⟩ hd4 (by simp only [List.length_cons]; omega)
  have rd10 := rd8.push1 ⟨128⟩ hd5 (by simp only [List.length_cons]; omega)
  have rd11 := rd10.shl hd6 (by simp only [List.length_cons]; omega)
  have rd12 := rd11.sub hd7 (by simp only [List.length_cons]; omega)
  have rd13 := rd12.and hd8 (by simp only [List.length_cons]; omega)
  have rd14 := rd13.dup2 hd9 (by omega)
  have rdRet := rd14.jump hd10 hret (by simp only [List.length_cons]; omega)
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩) ⟨1⟩ = uint128Mask := by
    native_decide
  exact ⟨_, _, by simpa [hmask] using rdRet⟩

/- LIBRARY CANDIDATE: generalizes Reasoning.Solc.solcReturnAddressFromMemWf to 128-bit masks. -/
@[reducible] def solcReturnUint128FromMemWf (code : ByteArray) (pc : UInt256) : Prop :=
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code (pc + ⟨1⟩) = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2) = some (.DUP1, .none)
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) = some (.MLOAD, .none)
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
      some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) =
      some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2) =
      some (.Push .PUSH1, some (⟨128⟩, 1))
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2) =
      some (.SHL, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩) =
      some (.SUB, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
      some (.SWAP1, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.SWAP3, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.AND, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩) =
      some (.DUP3, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩) =
      some (.MSTORE, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.MLOAD, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.SWAP1, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.DUP2, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.SWAP1, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.SUB, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        UInt256.ofNat 2) =
      some (.ADD, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        UInt256.ofNat 2 + ⟨1⟩) =
      some (.SWAP1, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
      some (.RETURN, .none)

theorem RD.solcReturnUint128FromMem {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc val ret : UInt256} {R : List UInt256}
    {mem memout rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (val :: ret :: R) mem (UInt256.ofNat 3) rdata acc k C)
    (hwf : solcReturnUint128FromMemWf code pc)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hmemout :
      (UInt256.toByteArray (UInt256.land val uint128Mask)).write 0 mem 128 32 = memout)
    (hmemoutLoad64 :
      (if (⟨64⟩ : UInt256).toNat ≥ memout.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memout.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hread128 : memout.readWithPadding 128 32 =
      UInt256.toByteArray (UInt256.land val uint128Mask))
    (hov : R.length + 9 ≤ 1024) :
    RDret code g s0 acc (UInt256.toByteArray (UInt256.land val uint128Mask)) := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hd5, hd7, hd9, hd11, hd12, hd13, hd14, hd15, hd16, hd17,
      hd18, hd19, hd20, hd21, hd22, hd23, hd25, hd26, hd27⟩
  exact evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨64⟩ hd1 (by evm_ov),
    raw dup1 hd3 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd4 mem_cost hmload64 (by decide) (by evm_ov),
    raw push1 ⟨1⟩ hd5 (by evm_ov),
    raw push1 ⟨1⟩ hd7 (by evm_ov),
    raw push1 ⟨128⟩ hd9 (by evm_ov),
    raw shl hd11 (by evm_ov),
    raw sub hd12 (by evm_ov),
    raw swap1 hd13 (by evm_ov),
    raw swap3 hd14 (by evm_ov),
    raw and hd15 (by evm_ov),
    raw dup3 hd16 (by evm_ov),
    raw mstore 6 memout (UInt256.ofNat 5) hd17 mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩) ⟨1⟩ =
          uint128Mask from by native_decide,
          show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        exact hmemout)
      (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) hd18 mem_cost hmemoutLoad64 (by decide)
      (by evm_ov),
    raw swap1 hd19 (by evm_ov),
    raw dup2 hd20 (by evm_ov),
    raw swap1 hd21 (by evm_ov),
    raw sub hd22 (by evm_ov),
    raw push1 ⟨32⟩ hd23 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw swap1 hd26 (by evm_ov),
    raw ret 0 (UInt256.toByteArray (UInt256.land val uint128Mask)) hd27 mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show ((⟨32⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat = 32
            from by decide]
        exact hread128)
      (by evm_ov)]

theorem RD.solcUint128GetterExternal {code : ByteArray} {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel entry routine slot returnPc : UInt256}
    (hreach : ∃ k C, RD code I g (Reasoning.Theory.initState cA gh bl σ σ₀ g A I)
      entry [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hgetter : solcUint128SlotGetterWf code routine slot)
    (hroutine : (D_J code 0).contains routine = true)
    (hret : (D_J code 0).contains returnPc = true)
    (hreturn : solcReturnUint128FromMemWf code returnPc) :
    RDret code g (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.land (solcSlotWord σ I slot) uint128Mask)) := by
  obtain ⟨_, _, rdRoutine⟩ := RD.solcGetterThunk hreach hentry hroutine
  obtain ⟨_, _, rdReturn⟩ := RD.solcUint128SlotGetter (slot := slot) (R := [sel])
    rdRoutine hgetter hret (by simp only [List.length_singleton]; omega)
  have hrd := RD.solcReturnUint128FromMem rdReturn hreturn
    solcFreePtrMem_mload64
    (by rfl)
    (solcReturnMem_mload64
      (UInt256.land (UInt256.land uint128Mask (solcSlotWord σ I slot)) uint128Mask))
    (solcReturnMem_read128
      (UInt256.land (UInt256.land uint128Mask (solcSlotWord σ I slot)) uint128Mask))
    (by simp only [List.length_singleton]; omega)
  have hclean :
      UInt256.land (UInt256.land uint128Mask (solcSlotWord σ I slot)) uint128Mask =
        UInt256.land (solcSlotWord σ I slot) uint128Mask := by
    rw [u256_land_comm uint128Mask (solcSlotWord σ I slot)]
    exact uint128Mask_clean (uint128Mask_bound (solcSlotWord σ I slot))
  simpa [hclean] using hrd

private theorem uniswapV3PoolLiquidityPatchDisjoint {v : PoolImmutables} {pc : UInt256}
    (hlo : 5293 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 6603) :
    ∀ p ∈ patches v, pc.toNat + 33 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    omega

theorem uniswapV3PoolLiquidityEntryWf {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcGetterEntryWf code ⟨646⟩ ⟨654⟩ ⟨5293⟩ := by
  dsimp [solcGetterEntryWf]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide

theorem uniswapV3PoolLiquidityGetterWf {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcUint128SlotGetterWf code ⟨5293⟩ ⟨4⟩ := by
  dsimp [solcUint128SlotGetterWf]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
      (uniswapV3PoolLiquidityPatchDisjoint (by native_decide) (by native_decide))]
    native_decide

theorem uniswapV3PoolLiquidityReturnWf {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcReturnUint128FromMemWf code ⟨654⟩ := by
  dsimp [solcReturnUint128FromMemWf]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide

theorem uniswapV3PoolLiquidityReturnJumpDest {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨654⟩ = true :=
  uniswapV3PoolJumpDestPatched2258 hpatch (by native_decide)

theorem uniswapV3PoolLiquidityEvm {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 2 == I.calldata.extract 0 4) = true) :
    RDret code g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.land (solcSlotWord σ I ⟨4⟩) uint128Mask)) := by
  have hreach := uniswapV3PoolLiquidityReachEntry
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize hsel
  exact RD.solcUint128GetterExternal (slot := ⟨4⟩) hreach
    (uniswapV3PoolLiquidityEntryWf hpatch)
    (uniswapV3PoolLiquidityGetterWf hpatch)
    (uniswapV3PoolJumpDestPatched5293 hpatch)
    (uniswapV3PoolLiquidityReturnJumpDest hpatch)
    (uniswapV3PoolLiquidityReturnWf hpatch)

theorem uniswapV3PoolLiquiditySourceBody {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (∅ : Store) liquidityTransition.body
      (.returned { contract := contract v, locals := ∅ }
        (initState cA gh bl σ σ₀ g A I)
        (some [Value.int (Int.ofNat
          (UInt256.land (solcSlotWord σ I ⟨4⟩) uint128Mask).toNat)])) := by
  change ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (∅ : Store)
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return [.storage liquidityRef] ] _
  apply nonpayableReturnExprBodyReturns
  · simp [initState, hwv]
  · apply evalExpr_storage_scalar_value
      (er := { base := "liquidity", steps := [] })
      (t := .int uint128Int)
      (loc := loc ⟨4⟩ ⟨0, by decide⟩ ⟨16, by decide⟩ (by decide) (.int uint128Int))
    · simp [liquidityRef]
    · simp [evalStorageRef, liquidityRef, pure, bind, EvalResult.bind]
    · simp [contract, storageDecls, storageTypeAt?, uint128St]
    · funext evm
      simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout, loc]
    · simpa [initState, solcSlotWord, loc] using
        (storageLocLoad_uint_offset0 (initState cA gh bl σ σ₀ g A I) ⟨4⟩
          ⟨16, by decide⟩ ⟨128, by decide⟩ (hbound := by decide) (by decide))

theorem uniswapV3PoolLiquidityValueTransport {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    some [Value.int (Int.ofNat (UInt256.land (solcSlotWord σ_solm I ⟨4⟩) uint128Mask).toNat)] =
      some [Value.int (Int.ofNat (UInt256.land (solcSlotWord σ_evm I ⟨4⟩) uint128Mask).toNat)] := by
  have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨4⟩ (⟨0⟩ : UInt256)
  dsimp [solcSlotWord]
  rw [← hslot]

theorem uniswapV3PoolLiquidityBodyCore {v : PoolImmutables}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsel : (uniswapV3PoolSelBytes 2 == I.calldata.extract 0 4) = true) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdispatch := uniswapV3PoolDispatch_liquidity (v := v) (cd := I.calldata) hsel
  have hdecode := uniswapV3PoolLiquidityDecode (v := v) (I := I) hsz
  have hbody := uniswapV3PoolLiquiditySourceBody (v := v) (cA := cA) (gh := gh)
    (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hwv
  have hvalue := uniswapV3PoolLiquidityValueTransport (σ_evm := σ_evm)
    (σ_solm := σ_solm) (I := I) hAccounts
  have hrd := uniswapV3PoolLiquidityEvm (v := v) (code := code) (cA := cA)
    (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hpatch hcode hwv hsz hsize hsel
  exact hrd.reEquivExecutionTransport hcode hdispatch hdecode hbody hvalue hAccounts
    (returnEquiv_of_encode (uint128ReturnEncodingMasked (solcSlotWord σ_evm I ⟨4⟩)))

end Benchmarks.UniswapV3Pool
