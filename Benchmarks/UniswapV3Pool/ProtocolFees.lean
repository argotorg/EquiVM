import Benchmarks.UniswapV3Pool.Uint128

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.UniswapV3Pool

abbrev protocolFeesShift : UInt256 := UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩

abbrev protocolFeesSlotWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I ⟨3⟩

abbrev protocolFeesToken0Word (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (protocolFeesSlotWord σ I) uint128Mask

abbrev protocolFeesToken1Word (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (UInt256.div (protocolFeesSlotWord σ I) protocolFeesShift) uint128Mask

theorem uniswapV3PoolProtocolFeesReachEntry {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 3 == I.calldata.extract 0 4) = true) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨682⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := uniswapV3PoolReachSelector32
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize
  have hword : solcSelectorWord I = uniswapV3PoolSelNat 3 := by
    simpa [uniswapV3PoolSelBytes, uniswapV3PoolSelNat] using
      solcSelectorWord_eq_of_beq I hsz 0x1a 0xd8 0xb0 0x3b
        (uniswapV3PoolSelNat 3) (by native_decide) hsel
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
  have h682 := uniswapV3PoolSelectorArmHitTo (i := 3) (target := ⟨682⟩)
    hpatch hsz hsel h359
  exact ⟨_, _, h682⟩

theorem uniswapV3PoolProtocolFeesDecode {v : PoolImmutables} {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode
      (protocolfeesTransition.params.map Param.name)
      (transitionSignature protocolfeesTransition).paramTypes I.calldata = some (∅ : Store) := by
  simpa [config, protocolfeesTransition, transitionSignature] using
    decodeCalldataWithMode_empty_ok (mode := DecodeMode.legacySolc05) (cd := I.calldata) hsz

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolDispatch_protocolFees {v : PoolImmutables} {cd : ByteArray}
    (hsel : (uniswapV3PoolSelBytes 3 == cd.extract 0 4) = true) :
    dispatchMsg (contract v) cd = some protocolfeesTransition := by
  apply dispatchMsg_eq_some_of_split
    (pre := [burnTransition, collectTransition v, collectprotocolTransition v, factoryTransition v,
      feeTransition v, feegrowthglobal0X128Transition, feegrowthglobal1X128Transition,
      flashTransition v, increaseobservationcardinalitynextTransition v, initializeTransition,
      liquidityTransition, maxliquiditypertickTransition v, mintTransition v, observationsTransition,
      observeTransition v, positionsTransition])
    (post := [setfeeprotocolTransition v, slot0Transition, snapshotcumulativesinsideTransition v,
      swapTransition v, tickbitmapTransition, tickspacingTransition v, ticksTransition,
      token0Transition v, token1Transition v])
  · simp [contract, transitions]
  · intro t ht
    simp at ht
    rcases ht with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · rw [selectorOf, burnSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 17) (j := 3)
          (by native_decide) hsel
    · rw [selectorOf, collectSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 10) (j := 3)
          (by native_decide) hsel
    · rw [selectorOf, collectProtocolSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 15) (j := 3)
          (by native_decide) hsel
    · rw [selectorOf, factorySelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 19) (j := 3)
          (by native_decide) hsel
    · rw [selectorOf, feeSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 22) (j := 3)
          (by native_decide) hsel
    · rw [selectorOf, feeGrowthGlobal0X128SelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 23) (j := 3)
          (by native_decide) hsel
    · rw [selectorOf, feeGrowthGlobal1X128SelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 8) (j := 3)
          (by native_decide) hsel
    · rw [selectorOf, flashSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 9) (j := 3)
          (by native_decide) hsel
    · rw [selectorOf, increaseObservationCardinalityNextSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 5) (j := 3)
          (by native_decide) hsel
    · rw [selectorOf, initializeSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 25) (j := 3)
          (by native_decide) hsel
    · rw [selectorOf, liquiditySelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 2) (j := 3)
          (by native_decide) hsel
    · rw [selectorOf, maxLiquidityPerTickSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 13) (j := 3)
          (by native_decide) hsel
    · rw [selectorOf, mintSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 7) (j := 3)
          (by native_decide) hsel
    · rw [selectorOf, observationsSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 4) (j := 3)
          (by native_decide) hsel
    · rw [selectorOf, observeSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 16) (j := 3)
          (by native_decide) hsel
    · rw [selectorOf, positionsSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 11) (j := 3)
          (by native_decide) hsel
  · rw [selectorOf, protocolFeesSelectorBytes]
    simpa [uniswapV3PoolSelBytes] using hsel

private theorem uniswapV3PoolProtocolFeesPatchDisjoint {v : PoolImmutables} {pc : UInt256}
    (hlo : 5308 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 6603) :
    ∀ p ∈ patches v, pc.toNat + 33 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    omega

private theorem uniswapV3PoolPatchPreservesJumpDest5308 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨5308⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched5308 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨5308⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest5308

theorem uniswapV3PoolProtocolFeesEntryWf {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcGetterEntryWf code ⟨682⟩ ⟨690⟩ ⟨5308⟩ := by
  dsimp [solcGetterEntryWf]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide

theorem uniswapV3PoolProtocolFeesRoutine {v : PoolImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {ret : UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨5308⟩ (ret :: R) mem aw rdata (cA, σ) k C)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (protocolFeesToken1Word σ ee :: protocolFeesToken0Word σ ee :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
  have hd5308 : decode code ⟨5308⟩ = some (.JUMPDEST, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
      (uniswapV3PoolProtocolFeesPatchDisjoint (by native_decide) (by native_decide))]
    native_decide
  have hd5309 : decode code ⟨5309⟩ = some (.Push .PUSH1, some (⟨3⟩, 1)) := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
      (uniswapV3PoolProtocolFeesPatchDisjoint (by native_decide) (by native_decide))]
    native_decide
  have hd5311 : decode code ⟨5311⟩ = some (.SLOAD, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
      (uniswapV3PoolProtocolFeesPatchDisjoint (by native_decide) (by native_decide))]
    native_decide
  have hd5312 : decode code ⟨5312⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
      (uniswapV3PoolProtocolFeesPatchDisjoint (by native_decide) (by native_decide))]
    native_decide
  have hd5314 : decode code ⟨5314⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
      (uniswapV3PoolProtocolFeesPatchDisjoint (by native_decide) (by native_decide))]
    native_decide
  have hd5316 : decode code ⟨5316⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
      (uniswapV3PoolProtocolFeesPatchDisjoint (by native_decide) (by native_decide))]
    native_decide
  have hd5318 : decode code ⟨5318⟩ = some (.SHL, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
      (uniswapV3PoolProtocolFeesPatchDisjoint (by native_decide) (by native_decide))]
    native_decide
  have hd5319 : decode code ⟨5319⟩ = some (.SUB, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
      (uniswapV3PoolProtocolFeesPatchDisjoint (by native_decide) (by native_decide))]
    native_decide
  have hd5320 : decode code ⟨5320⟩ = some (.DUP1, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
      (uniswapV3PoolProtocolFeesPatchDisjoint (by native_decide) (by native_decide))]
    native_decide
  have hd5321 : decode code ⟨5321⟩ = some (.DUP3, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
      (uniswapV3PoolProtocolFeesPatchDisjoint (by native_decide) (by native_decide))]
    native_decide
  have hd5322 : decode code ⟨5322⟩ = some (.AND, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
      (uniswapV3PoolProtocolFeesPatchDisjoint (by native_decide) (by native_decide))]
    native_decide
  have hd5323 : decode code ⟨5323⟩ = some (.SWAP2, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
      (uniswapV3PoolProtocolFeesPatchDisjoint (by native_decide) (by native_decide))]
    native_decide
  have hd5324 : decode code ⟨5324⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
      (uniswapV3PoolProtocolFeesPatchDisjoint (by native_decide) (by native_decide))]
    native_decide
  have hd5326 : decode code ⟨5326⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
      (uniswapV3PoolProtocolFeesPatchDisjoint (by native_decide) (by native_decide))]
    native_decide
  have hd5328 : decode code ⟨5328⟩ = some (.SHL, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
      (uniswapV3PoolProtocolFeesPatchDisjoint (by native_decide) (by native_decide))]
    native_decide
  have hd5329 : decode code ⟨5329⟩ = some (.SWAP1, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
      (uniswapV3PoolProtocolFeesPatchDisjoint (by native_decide) (by native_decide))]
    native_decide
  have hd5330 : decode code ⟨5330⟩ = some (.DIV, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
      (uniswapV3PoolProtocolFeesPatchDisjoint (by native_decide) (by native_decide))]
    native_decide
  have hd5331 : decode code ⟨5331⟩ = some (.AND, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
      (uniswapV3PoolProtocolFeesPatchDisjoint (by native_decide) (by native_decide))]
    native_decide
  have hd5332 : decode code ⟨5332⟩ = some (.DUP3, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
      (uniswapV3PoolProtocolFeesPatchDisjoint (by native_decide) (by native_decide))]
    native_decide
  have hd5333 : decode code ⟨5333⟩ = some (.JUMP, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
      (uniswapV3PoolProtocolFeesPatchDisjoint (by native_decide) (by native_decide))]
    native_decide
  have rd5309 := h.jumpdest hd5308 (by simp only [List.length_cons]; omega)
  have rd5311 := rd5309.push1 ⟨3⟩ hd5309 (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd5312⟩ := rd5311.sload hd5311 (by simp only [List.length_cons]; omega)
  have rd5333 := evm_run rd5312 with [
    raw push1 ⟨1⟩ hd5312 (by evm_ov),
    raw push1 ⟨1⟩ hd5314 (by evm_ov),
    raw push1 ⟨128⟩ hd5316 (by evm_ov),
    raw shl hd5318 (by evm_ov),
    raw sub hd5319 (by evm_ov),
    raw dup1 hd5320 (by evm_ov),
    raw dup3 hd5321 (by evm_ov),
    raw and hd5322 (by evm_ov),
    raw swap2 hd5323 (by evm_ov),
    raw push1 ⟨1⟩ hd5324 (by evm_ov),
    raw push1 ⟨128⟩ hd5326 (by evm_ov),
    raw shl hd5328 (by evm_ov),
    raw swap1 hd5329 (by evm_ov),
    raw div hd5330 (by evm_ov),
    raw and hd5331 (by evm_ov),
    raw dup3 hd5332 (by evm_ov)]
  have rdRet := rd5333.jump hd5333 hret (by simp only [List.length_cons]; omega)
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩) ⟨1⟩ = uint128Mask := by
    native_decide
  exact ⟨_, _, by
    rw [hmask] at rdRet
    simpa [protocolFeesToken0Word, protocolFeesToken1Word, protocolFeesSlotWord,
      protocolFeesShift] using rdRet⟩

noncomputable def protocolFeesReturn0Mem (t0 : UInt256) : ByteArray :=
  (UInt256.toByteArray t0).write 0 solcFreePtrMem 128 32

noncomputable def protocolFeesReturnMem (t0 t1 : UInt256) : ByteArray :=
  (UInt256.toByteArray t1).write 0 (protocolFeesReturn0Mem t0) 160 32

theorem protocolFeesReturn0Mem_size (t0 : UInt256) :
    (protocolFeesReturn0Mem t0).size = 160 := by
  unfold protocolFeesReturn0Mem
  rw [toByteArray_write_eq _ _ _ (by rw [solcFreePtrMem_size]; omega)
      (by rw [solcFreePtrMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, solcFreePtrMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem protocolFeesReturnMem_size (t0 t1 : UInt256) :
    (protocolFeesReturnMem t0 t1).size = 192 := by
  unfold protocolFeesReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [protocolFeesReturn0Mem_size])
      (by rw [protocolFeesReturn0Mem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, protocolFeesReturn0Mem_size,
    ByteArray_zeroes_size,
    show (USize.ofNat (160 - 160)).toNat = 0 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem protocolFeesReturn0Mem_read64 (t0 : UInt256) :
    (protocolFeesReturn0Mem t0).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold protocolFeesReturn0Mem
  rw [toByteArray_write_eq _ _ _ (by rw [solcFreePtrMem_size]; omega)
      (by rw [solcFreePtrMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, solcFreePtrMem_size,
        ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, solcFreePtrMem_size, ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
      omega)]
  rw [extract_append_left _ _ _ _ (by rw [solcFreePtrMem_size]),
    ← readWithPadding_eq_extract _ 64 (by rw [solcFreePtrMem_size]), solcFreePtrMem_read64]

theorem protocolFeesReturnMem_read64 (t0 t1 : UInt256) :
    (protocolFeesReturnMem t0 t1).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold protocolFeesReturnMem
  rw [write32_read_below _ _ 160 64 (by rw [toByteArray_size])
      (by rw [protocolFeesReturn0Mem_size]) (by omega)]
  exact protocolFeesReturn0Mem_read64 t0

theorem protocolFeesReturnMem_mload64 (t0 t1 : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (protocolFeesReturnMem t0 t1).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((protocolFeesReturnMem t0 t1).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [protocolFeesReturnMem_size]; decide) (by decide)
    (protocolFeesReturnMem_read64 t0 t1)

set_option maxHeartbeats 800000 in
theorem protocolFeesReturnMem_read128_64 (t0 t1 : UInt256) :
    (protocolFeesReturnMem t0 t1).readWithPadding 128 64 =
      UInt256.toByteArray t0 ++ UInt256.toByteArray t1 := by
  rw [readWithPadding_eq_extract' _ 128 64 (by norm_num) (by norm_num)
      (by rw [protocolFeesReturnMem_size])]
  unfold protocolFeesReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [protocolFeesReturn0Mem_size])
      (by rw [protocolFeesReturn0Mem_size]; exact lt_usize _ (by norm_num))]
  rw [extract_append_span
      (protocolFeesReturn0Mem t0 ++
        ffi.ByteArray.zeroes (USize.ofNat (160 - (protocolFeesReturn0Mem t0).size)))
      (UInt256.toByteArray t1) 128 192 (by
        rw [ByteArray.size_append, protocolFeesReturn0Mem_size, ByteArray_zeroes_size,
          show (USize.ofNat (160 - 160)).toNat = 0 from by
            exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
        omega) (by
        rw [ByteArray.size_append, protocolFeesReturn0Mem_size, ByteArray_zeroes_size,
          show (USize.ofNat (160 - 160)).toNat = 0 from by
            exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
        omega)]
  rw [ByteArray.size_append, protocolFeesReturn0Mem_size, ByteArray_zeroes_size,
    show (USize.ofNat (160 - 160)).toNat = 0 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
  rw [show ffi.ByteArray.zeroes (USize.ofNat (160 - 160)) = ByteArray.empty by
      exact zeroes_zero (n := USize.ofNat 0)
        (by exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)))]
  simp
  unfold protocolFeesReturn0Mem
  rw [toByteArray_write_eq _ _ _ (by rw [solcFreePtrMem_size]; omega)
      (by rw [solcFreePtrMem_size]; exact lt_usize _ (by norm_num))]
  rw [extract_append_right_window
      (solcFreePtrMem ++ ffi.ByteArray.zeroes (USize.ofNat (128 - solcFreePtrMem.size)))
      (UInt256.toByteArray t0) 128 160 (by
        rw [ByteArray.size_append, solcFreePtrMem_size, ByteArray_zeroes_size,
          show (USize.ofNat (128 - 96)).toNat = 32 from by
            exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))])]
  rw [ByteArray.size_append, solcFreePtrMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
  norm_num
  repeat'
    first
    | rw [show (UInt256.toByteArray t0).extract 0 32 = UInt256.toByteArray t0 from by
        apply ByteArray.ext
        rw [ByteArray.data_extract]
        exact Array.extract_eq_self_of_le (by
          change (UInt256.toByteArray t0).size ≤ 32
          rw [toByteArray_size])]
    | rw [show (UInt256.toByteArray t1).extract 0 32 = UInt256.toByteArray t1 from by
        apply ByteArray.ext
        rw [ByteArray.data_extract]
        exact Array.extract_eq_self_of_le (by
          change (UInt256.toByteArray t1).size ≤ 32
          rw [toByteArray_size])]

theorem protocolFeesRetLen_toNat :
    ((⟨64⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat = 64 := by
  decide

theorem uniswapV3PoolProtocolFeesReturn {v : PoolImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {t1 t0 : UInt256} {R : List UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨690⟩ (t1 :: t0 :: R) solcFreePtrMem (UInt256.ofNat 3)
      rdata acc k C)
    (hov : R.length + 10 ≤ 1024) :
    RDret code g s0 acc
      (UInt256.toByteArray (UInt256.land t0 uint128Mask) ++
        UInt256.toByteArray (UInt256.land t1 uint128Mask)) := by
  let t0' := UInt256.land t0 uint128Mask
  let t1' := UInt256.land t1 uint128Mask
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩) ⟨1⟩ = uint128Mask := by
    native_decide
  exact evm_run h with [
    raw jumpdest (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    raw dup1 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw dup4 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨128⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw shl (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw sub (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw and (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw dup2 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw mstore 6 (protocolFeesReturn0Mem t0') (UInt256.ofNat 5) (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) mem_cost
      (by
        rw [hmask, u256_land_comm uint128Mask t0,
          show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw add (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw dup3 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨128⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw shl (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw sub (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw and (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw dup2 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw mstore 3 (protocolFeesReturnMem t0' t1') (UInt256.ofNat 6) (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) mem_cost
      (by
        rw [hmask, u256_land_comm uint128Mask t1,
          show ((⟨32⟩ : UInt256) + ⟨128⟩).toNat = 160 from by decide]
        rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw add (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw swap3 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw pop (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw pop (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw pop (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) mem_cost (protocolFeesReturnMem_mload64 t0' t1') (by decide)
      (by evm_ov),
    raw dup1 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw swap2 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw sub (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw swap1 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw ret 0 (UInt256.toByteArray t0' ++ UInt256.toByteArray t1') (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show ((⟨32⟩ + (⟨32⟩ + ⟨128⟩ : UInt256)).sub ⟨128⟩).toNat = 64 from by
            decide]
        exact protocolFeesReturnMem_read128_64 t0' t1')
      (by evm_ov)]

theorem uniswapV3PoolProtocolFeesReturnJumpDest {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨690⟩ = true :=
  uniswapV3PoolJumpDestPatched2258 hpatch (by native_decide)

theorem uniswapV3PoolProtocolFeesEvm {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 3 == I.calldata.extract 0 4) = true) :
    RDret code g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (protocolFeesToken0Word σ I) ++
        UInt256.toByteArray (protocolFeesToken1Word σ I)) := by
  have hreach := uniswapV3PoolProtocolFeesReachEntry
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize hsel
  obtain ⟨_, _, rdRoutine⟩ := RD.solcGetterThunk hreach
    (uniswapV3PoolProtocolFeesEntryWf hpatch)
    (uniswapV3PoolJumpDestPatched5308 hpatch)
  obtain ⟨_, _, rdReturn⟩ := uniswapV3PoolProtocolFeesRoutine hpatch rdRoutine
    (uniswapV3PoolProtocolFeesReturnJumpDest hpatch)
    (by simp only [List.length_singleton]; omega)
  have hret := uniswapV3PoolProtocolFeesReturn hpatch
    (t1 := protocolFeesToken1Word σ I) (t0 := protocolFeesToken0Word σ I)
    (R := [⟨690⟩, solcSelectorWord I]) rdReturn
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hclean0 : UInt256.land (protocolFeesToken0Word σ I) uint128Mask =
      protocolFeesToken0Word σ I := by
    exact uint128Mask_clean (by
      simpa [protocolFeesToken0Word] using uint128Mask_bound (protocolFeesSlotWord σ I))
  have hclean1 : UInt256.land (protocolFeesToken1Word σ I) uint128Mask =
      protocolFeesToken1Word σ I := by
    exact uint128Mask_clean (by
      simpa [protocolFeesToken1Word] using
        uint128Mask_bound (UInt256.div (protocolFeesSlotWord σ I) protocolFeesShift))
  simpa [hclean0, hclean1] using hret

theorem protocolFeesStorageLocLoad_token0 (evm : EVM.State) :
    storageLocLoad evm
        (loc ⟨3⟩ ⟨0, by decide⟩ ⟨16, by decide⟩ (by decide) (.int uint128Int)) =
      .int (Int.ofNat (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩) uint128Mask).toNat) := by
  rw [← show UInt256.ofNat (2 ^ (8 * 16) - 1) = uint128Mask by native_decide]
  simpa [loc, uint128Int] using
    storageLocLoad_uint_offset0 evm ⟨3⟩ (16 : Fin 33) ⟨128, by decide⟩
      (hbound := by decide) (by decide)

theorem protocolFeesStorageLocLoad_token1 (evm : EVM.State) :
    storageLocLoad evm
        (loc ⟨3⟩ ⟨16, by decide⟩ ⟨16, by decide⟩ (by decide) (.int uint128Int)) =
      .int (Int.ofNat (UInt256.land
        (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
          protocolFeesShift) uint128Mask).toNat) := by
  rw [← show UInt256.ofNat (256 ^ 16) = protocolFeesShift by native_decide]
  rw [← show UInt256.ofNat (256 ^ 16 - 1) = uint128Mask by native_decide]
  simpa [loc, uint128Int] using
    storageLocLoad_uint_offset evm ⟨3⟩ (16 : Fin 32) (16 : Fin 33) ⟨128, by decide⟩
      (by decide) (by decide)

theorem uniswapV3PoolProtocolFeesSourceBody {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (∅ : Store) protocolfeesTransition.body
      (.returned { contract := contract v, locals := ∅ }
        (initState cA gh bl σ σ₀ g A I)
        (some [Value.int (Int.ofNat (protocolFeesToken0Word σ I).toNat),
          Value.int (Int.ofNat (protocolFeesToken1Word σ I).toNat)])) := by
  change ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (∅ : Store)
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return [.storage (protocolFeesF "token0"), .storage (protocolFeesF "token1")] ] _
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by simp [initState, hwv]))) <|
      ExecBlock.consReturn <| ExecStmt.return (by
        have hret0 :
            evalExpr? (config v) { contract := contract v, locals := ∅ }
              (initState cA gh bl σ σ₀ g A I) (.storage (protocolFeesF "token0")) =
            .ok (.int (Int.ofNat (protocolFeesToken0Word σ I).toNat)) := by
          rw [evalExpr_storage_scalar
            (t := .int uint128Int)
            (slot := protocolFeesF "token0")
            (er := { base := "protocolFees", steps := [.field "token0"] })
            (loc := loc ⟨3⟩ ⟨0, by decide⟩ ⟨16, by decide⟩ (by decide)
              (.int uint128Int))
            (hbase := by simp [protocolFeesF])
            (her := by
              simp [evalStorageRef, evalStorageRefStep, protocolFeesF, EvalResult.bind,
                pure, bind])
            (hty := by
              simp [contract, storageDecls, storageTypeAt?, storageTypeStep?,
                protocolFeesStructTy, uint128St])
            (hloc := by
              funext evm
              simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout, loc])]
          simpa [initState, protocolFeesToken0Word, protocolFeesSlotWord, solcSlotWord] using
            protocolFeesStorageLocLoad_token0 (initState cA gh bl σ σ₀ g A I)
        have hret1 :
            evalExpr? (config v) { contract := contract v, locals := ∅ }
              (initState cA gh bl σ σ₀ g A I) (.storage (protocolFeesF "token1")) =
            .ok (.int (Int.ofNat (protocolFeesToken1Word σ I).toNat)) := by
          rw [evalExpr_storage_scalar
            (t := .int uint128Int)
            (slot := protocolFeesF "token1")
            (er := { base := "protocolFees", steps := [.field "token1"] })
            (loc := loc ⟨3⟩ ⟨16, by decide⟩ ⟨16, by decide⟩ (by decide)
              (.int uint128Int))
            (hbase := by simp [protocolFeesF])
            (her := by
              simp [evalStorageRef, evalStorageRefStep, protocolFeesF, EvalResult.bind,
                pure, bind])
            (hty := by
              simp [contract, storageDecls, storageTypeAt?, storageTypeStep?,
                protocolFeesStructTy, uint128St])
            (hloc := by
              funext evm
              simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout, loc])]
          simpa [initState, protocolFeesToken1Word, protocolFeesSlotWord, solcSlotWord] using
            protocolFeesStorageLocLoad_token1 (initState cA gh bl σ σ₀ g A I)
        simp only [Solm.evalExprs?.eq_def, hret0, hret1, EvalResult.bind, bind, pure])

theorem uniswapV3PoolProtocolFeesValueTransport {σ_evm σ_solm : AccountMap}
    {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    some [Value.int (Int.ofNat (protocolFeesToken0Word σ_solm I).toNat),
      Value.int (Int.ofNat (protocolFeesToken1Word σ_solm I).toNat)] =
      some [Value.int (Int.ofNat (protocolFeesToken0Word σ_evm I).toNat),
        Value.int (Int.ofNat (protocolFeesToken1Word σ_evm I).toNat)] := by
  have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ (⟨0⟩ : UInt256)
  dsimp [protocolFeesToken0Word, protocolFeesToken1Word, protocolFeesSlotWord, solcSlotWord]
  rw [← hslot]

theorem uniswapV3PoolProtocolFeesBodyCore {v : PoolImmutables}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsel : (uniswapV3PoolSelBytes 3 == I.calldata.extract 0 4) = true) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdispatch := uniswapV3PoolDispatch_protocolFees (v := v) (cd := I.calldata) hsel
  have hdecode := uniswapV3PoolProtocolFeesDecode (v := v) (I := I) hsz
  have hbody := uniswapV3PoolProtocolFeesSourceBody (v := v) (cA := cA)
    (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hwv
  have hvalue := uniswapV3PoolProtocolFeesValueTransport (σ_evm := σ_evm)
    (σ_solm := σ_solm) (I := I) hAccounts
  have hrd := uniswapV3PoolProtocolFeesEvm (v := v) (code := code) (cA := cA)
    (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hpatch hcode hwv hsz hsize hsel
  exact hrd.reEquivExecutionTransport hcode hdispatch hdecode hbody hvalue hAccounts
    (by
      rw [show protocolfeesTransition.returnType = [uint128, uint128] from rfl]
      exact returnEquiv.returned rfl
        (uint128PairReturnEncodingMasked (protocolFeesSlotWord σ_evm I)
          (UInt256.div (protocolFeesSlotWord σ_evm I) protocolFeesShift)))

end Benchmarks.UniswapV3Pool
