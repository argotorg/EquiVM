import Benchmarks.UniswapV3Pool.BurnObserveSingle
import Benchmarks.UniswapV3Pool.BurnTickGetFeeGrowthInsideSource
import Benchmarks.UniswapV3Pool.InitializeGetTickLog
import Benchmarks.UniswapV3Pool.SetFeeProtocolOwnerCall

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

private theorem uniswapV3PoolBurnPostObservePatchDisjoint {v : PoolImmutables}
    {pc : UInt256} {n : Nat} (hlo : 19273 ≤ pc.toNat)
    (hhi : pc.toNat + n ≤ 19350)
    (havoid : pc.toNat + n ≤ 19295 ∨ 19327 ≤ pc.toNat) :
    ∀ p ∈ patches v, pc.toNat + n ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord,
    List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  all_goals omega

private theorem uniswapV3PoolBurnPostObserveMaxLiquidityPatchWord19295
    {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    code.extract 19295 19327 =
      UInt256.toByteArray (EVM.wordOfInt v.maxLiquidityPerTick) := by
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
     (19452, UInt256.toByteArray (EVM.wordOfInt v.tickSpacing)),
     (8174, value)]
  let post : List (Nat × ByteArray) :=
    [(19350, value), (11259, UInt256.toByteArray (EVM.Word.ofNat v.original.toNat))]
  have hpatch' : patchRuntime uniswapV3PoolBytecode (pre ++ (19295, value) :: post) =
      some code := by
    dsimp [pre, post, value]
    simpa [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord,
      List.lookup, toByteArray_eq_toBytesBE] using hpatch
  have hpost : ∀ p ∈ post, 19295 + 32 ≤ p.1 ∨ p.1 + 32 ≤ 19295 := by
    intro p hp
    dsimp [post] at hp
    simp at hp
    rcases hp with rfl | rfl
    all_goals omega
  have hsize : value.size = 32 := by
    dsimp [value]
    exact toByteArray_size _
  exact patchRuntime_extract_patch hsize hpost hpatch'

private theorem uniswapV3PoolBurnPostObserveMaxLiquidityConstDecode19294
    {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    decode code ⟨19294⟩ =
      some (.Push .PUSH32, some (EVM.wordOfInt v.maxLiquidityPerTick, 32)) := by
  have hsize := uniswapV3PoolPatchedSize hpatch
  have hget : code.get? ({ val := 19294 } : UInt256).toNat =
      uniswapV3PoolBytecode.get? ({ val := 19294 } : UInt256).toNat := by
    change code.get? 19294 = uniswapV3PoolBytecode.get? 19294
    apply get?_eq_of_extract_one
    · rw [hsize]
      native_decide
    · native_decide
    · exact patchRuntime_extract_eq (start := 19294) (stop := 19295)
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
  have hextract : code.extract' ({ val := 19294 } : UInt256).toNat.succ
      (({ val := 19294 } : UInt256).toNat.succ + 32) =
      UInt256.toByteArray (EVM.wordOfInt v.maxLiquidityPerTick) := by
    change code.extract' 19295 19327 =
      UInt256.toByteArray (EVM.wordOfInt v.maxLiquidityPerTick)
    unfold ByteArray.extract'
    have hguard : (decide (19295 < 2 ^ 64) && decide (19327 < 2 ^ 64)) = true := by
      native_decide
    rw [if_pos hguard]
    exact uniswapV3PoolBurnPostObserveMaxLiquidityPatchWord19295 hpatch
  have hgetSome : code.get? ({ val := 19294 } : UInt256).toNat = some 0x7f := by
    rw [hget]
    native_decide
  have hparse : (some (0x7f : UInt8) >>= parseInstr) = some (.Push .PUSH32) := by
    native_decide
  unfold decode
  rw [hgetSome, hparse]
  change some (Operation.Push Operation.POp.PUSH32,
      some (uInt256OfByteArray
        (code.extract' ({ val := 19294 } : UInt256).toNat.succ
          (({ val := 19294 } : UInt256).toNat.succ + 32)), 32)) =
    some (Operation.Push Operation.POp.PUSH32,
      some (EVM.wordOfInt v.maxLiquidityPerTick, 32))
  rw [hextract, uInt256OfByteArray_eq, fromByteArrayBigEndian_toByteArray,
    u256_ofNat_toNat]

private theorem uniswapV3PoolBurnPostObservePatchPreservesJumpDest20795 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨20795⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolBurnJumpDestPatched20795 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨20795⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolBurnPostObservePatchPreservesJumpDest20795

theorem uniswapV3PoolBurnPostObserveSingleToLowerTickUpdate
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State}
    {seconds tick z0 z1 time z2 z3 feeGrowthGlobal1 feeGrowthGlobal0 positionBase
      slot0Tick liquidityDelta tickUpper tickLower source : UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨19273⟩
      (seconds :: tick :: z0 :: z1 :: time :: z2 :: z3 ::
        feeGrowthGlobal1 :: feeGrowthGlobal0 :: positionBase :: slot0Tick ::
        liquidityDelta :: tickUpper :: tickLower :: source :: R)
      mem aw rdata (cA, σ) k C)
    (hov : R.length + 43 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨20795⟩
      (EVM.wordOfInt v.maxLiquidityPerTick :: ⟨0⟩ :: time :: tick :: seconds ::
        feeGrowthGlobal1 :: feeGrowthGlobal0 :: liquidityDelta :: slot0Tick ::
        tickLower :: ⟨5⟩ :: ⟨19331⟩ :: seconds :: tick :: time :: z2 :: z3 ::
        feeGrowthGlobal1 :: feeGrowthGlobal0 :: positionBase :: slot0Tick ::
        liquidityDelta :: tickUpper :: tickLower :: source :: R)
      mem aw rdata (cA, σ) k' C' := by
  have hd19273 : decode code ⟨19273⟩ = some (.JUMPDEST, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨19273⟩) (byte := 0x5b)
      (op := .JUMPDEST) hpatch (by native_decide) ?_ (by native_decide)
      (by native_decide) (by native_decide)
    exact uniswapV3PoolBurnPostObservePatchDisjoint
      (pc := ⟨19273⟩) (n := 1) (by native_decide) (by native_decide)
      (Or.inl (by native_decide))
  have hd19274 : decode code ⟨19274⟩ = some (.SWAP1, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨19274⟩) (byte := 0x90)
      (op := .SWAP1) hpatch (by native_decide) ?_ (by native_decide)
      (by native_decide) (by native_decide)
    exact uniswapV3PoolBurnPostObservePatchDisjoint
      (pc := ⟨19274⟩) (n := 1) (by native_decide) (by native_decide)
      (Or.inl (by native_decide))
  have hd19275 : decode code ⟨19275⟩ = some (.SWAP3, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨19275⟩) (byte := 0x92)
      (op := .SWAP3) hpatch (by native_decide) ?_ (by native_decide)
      (by native_decide) (by native_decide)
    exact uniswapV3PoolBurnPostObservePatchDisjoint
      (pc := ⟨19275⟩) (n := 1) (by native_decide) (by native_decide)
      (Or.inl (by native_decide))
  have hd19276 : decode code ⟨19276⟩ = some (.POP, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨19276⟩) (byte := 0x50)
      (op := .POP) hpatch (by native_decide) ?_ (by native_decide)
      (by native_decide) (by native_decide)
    exact uniswapV3PoolBurnPostObservePatchDisjoint
      (pc := ⟨19276⟩) (n := 1) (by native_decide) (by native_decide)
      (Or.inl (by native_decide))
  have hd19277 : decode code ⟨19277⟩ = some (.SWAP1, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨19277⟩) (byte := 0x90)
      (op := .SWAP1) hpatch (by native_decide) ?_ (by native_decide)
      (by native_decide) (by native_decide)
    exact uniswapV3PoolBurnPostObservePatchDisjoint
      (pc := ⟨19277⟩) (n := 1) (by native_decide) (by native_decide)
      (Or.inl (by native_decide))
  have hd19278 : decode code ⟨19278⟩ = some (.POP, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨19278⟩) (byte := 0x50)
      (op := .POP) hpatch (by native_decide) ?_ (by native_decide)
      (by native_decide) (by native_decide)
    exact uniswapV3PoolBurnPostObservePatchDisjoint
      (pc := ⟨19278⟩) (n := 1) (by native_decide) (by native_decide)
      (Or.inl (by native_decide))
  have hd19279 : decode code ⟨19279⟩ =
      some (.Push .PUSH2, some (⟨19331⟩, 2)) := by
    exact uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush2 hpatch
      (by native_decide)
      (uniswapV3PoolBurnPostObservePatchDisjoint
        (pc := ⟨19279⟩) (n := 3) (by native_decide) (by native_decide)
        (Or.inl (by native_decide)))
      (by native_decide) (by native_decide)
  have hd19282 : decode code ⟨19282⟩ =
      some (.Push .PUSH1, some (⟨5⟩, 1)) := by
    exact uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush1 hpatch
      (by native_decide)
      (uniswapV3PoolBurnPostObservePatchDisjoint
        (pc := ⟨19282⟩) (n := 2) (by native_decide) (by native_decide)
        (Or.inl (by native_decide)))
      (by native_decide) (by native_decide)
  have hd19284 : decode code ⟨19284⟩ = some (.DUP14, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨19284⟩) (byte := 0x8d)
      (op := .DUP14) hpatch (by native_decide) ?_ (by native_decide)
      (by native_decide) (by native_decide)
    exact uniswapV3PoolBurnPostObservePatchDisjoint
      (pc := ⟨19284⟩) (n := 1) (by native_decide) (by native_decide)
      (Or.inl (by native_decide))
  have hd19285 : decode code ⟨19285⟩ = some (.DUP12, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨19285⟩) (byte := 0x8b)
      (op := .DUP12) hpatch (by native_decide) ?_ (by native_decide)
      (by native_decide) (by native_decide)
    exact uniswapV3PoolBurnPostObservePatchDisjoint
      (pc := ⟨19285⟩) (n := 1) (by native_decide) (by native_decide)
      (Or.inl (by native_decide))
  have hd19286 : decode code ⟨19286⟩ = some (.DUP14, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨19286⟩) (byte := 0x8d)
      (op := .DUP14) hpatch (by native_decide) ?_ (by native_decide)
      (by native_decide) (by native_decide)
    exact uniswapV3PoolBurnPostObservePatchDisjoint
      (pc := ⟨19286⟩) (n := 1) (by native_decide) (by native_decide)
      (Or.inl (by native_decide))
  have hd19287 : decode code ⟨19287⟩ = some (.DUP12, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨19287⟩) (byte := 0x8b)
      (op := .DUP12) hpatch (by native_decide) ?_ (by native_decide)
      (by native_decide) (by native_decide)
    exact uniswapV3PoolBurnPostObservePatchDisjoint
      (pc := ⟨19287⟩) (n := 1) (by native_decide) (by native_decide)
      (Or.inl (by native_decide))
  have hd19288 : decode code ⟨19288⟩ = some (.DUP12, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨19288⟩) (byte := 0x8b)
      (op := .DUP12) hpatch (by native_decide) ?_ (by native_decide)
      (by native_decide) (by native_decide)
    exact uniswapV3PoolBurnPostObservePatchDisjoint
      (pc := ⟨19288⟩) (n := 1) (by native_decide) (by native_decide)
      (Or.inl (by native_decide))
  have hd19289 : decode code ⟨19289⟩ = some (.DUP8, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨19289⟩) (byte := 0x87)
      (op := .DUP8) hpatch (by native_decide) ?_ (by native_decide)
      (by native_decide) (by native_decide)
    exact uniswapV3PoolBurnPostObservePatchDisjoint
      (pc := ⟨19289⟩) (n := 1) (by native_decide) (by native_decide)
      (Or.inl (by native_decide))
  have hd19290 : decode code ⟨19290⟩ = some (.DUP10, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨19290⟩) (byte := 0x89)
      (op := .DUP10) hpatch (by native_decide) ?_ (by native_decide)
      (by native_decide) (by native_decide)
    exact uniswapV3PoolBurnPostObservePatchDisjoint
      (pc := ⟨19290⟩) (n := 1) (by native_decide) (by native_decide)
      (Or.inl (by native_decide))
  have hd19291 : decode code ⟨19291⟩ = some (.DUP12, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨19291⟩) (byte := 0x8b)
      (op := .DUP12) hpatch (by native_decide) ?_ (by native_decide)
      (by native_decide) (by native_decide)
    exact uniswapV3PoolBurnPostObservePatchDisjoint
      (pc := ⟨19291⟩) (n := 1) (by native_decide) (by native_decide)
      (Or.inl (by native_decide))
  have hd19292 : decode code ⟨19292⟩ =
      some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    exact uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush1 hpatch
      (by native_decide)
      (uniswapV3PoolBurnPostObservePatchDisjoint
        (pc := ⟨19292⟩) (n := 2) (by native_decide) (by native_decide)
        (Or.inl (by native_decide)))
      (by native_decide) (by native_decide)
  have hd19294 := uniswapV3PoolBurnPostObserveMaxLiquidityConstDecode19294 hpatch
  have hd19327 : decode code ⟨19327⟩ =
      some (.Push .PUSH2, some (⟨20795⟩, 2)) := by
    exact uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush2 hpatch
      (by native_decide)
      (uniswapV3PoolBurnPostObservePatchDisjoint
        (pc := ⟨19327⟩) (n := 3) (by native_decide) (by native_decide)
        (Or.inr (by native_decide)))
      (by native_decide) (by native_decide)
  have hd19330 : decode code ⟨19330⟩ = some (.JUMP, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨19330⟩) (byte := 0x56)
      (op := .JUMP) hpatch (by native_decide) ?_ (by native_decide)
      (by native_decide) (by native_decide)
    exact uniswapV3PoolBurnPostObservePatchDisjoint
      (pc := ⟨19330⟩) (n := 1) (by native_decide) (by native_decide)
      (Or.inr (by native_decide))
  have h19284 := evm_run h with [
    raw jumpdest hd19273 (by evm_ov),
    raw swap1 hd19274 (by evm_ov),
    raw swap3 hd19275 (by evm_ov),
    raw pop hd19276 (by evm_ov),
    raw swap1 hd19277 (by evm_ov),
    raw pop hd19278 (by evm_ov),
    raw push2 ⟨19331⟩ hd19279 (by evm_ov),
    raw push1 ⟨5⟩ hd19282 (by evm_ov)]
  have h19285 := by
    simpa using h19284.dup14 hd19284 (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega)
  have h19286 := by
    simpa using RD.dup12 h19285 hd19285 (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega)
  have h19287 := by
    simpa using h19286.dup14 hd19286 (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega)
  have h19288 := by
    simpa using RD.dup12 h19287 hd19287 (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega)
  have h19289 := by
    simpa using RD.dup12 h19288 hd19288 (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega)
  have h19290 := by
    simpa using h19289.dup8 hd19289 (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega)
  have h19291 := by
    simpa using h19290.dup10 hd19290 (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega)
  have h19292 := by
    simpa using RD.dup12 h19291 hd19291 (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega)
  have h19294 := evm_run h19292 with [
    raw push1 ⟨0⟩ hd19292 (by evm_ov)]
  have h19327 := by
    simpa using
      h19294.pushConst (EVM.wordOfInt v.maxLiquidityPerTick)
        (by native_decide : Operation.POp.PUSH32 ≠ .PUSH0) hd19294
        (by
          have hlen := hov
          simp only [List.length_cons] at hlen ⊢
          omega)
  have h19330 := evm_run h19327 with [
    raw push2 ⟨20795⟩ hd19327 (by evm_ov)]
  exact ⟨_, _, h19330.jump hd19330 (uniswapV3PoolBurnJumpDestPatched20795 hpatch)
    (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega)⟩

theorem uniswapV3PoolBurnObserveSingleTimestampEqualToLowerTickUpdate
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State}
    {obsWord cardinality liquidity index currentTick time z0 z1 callerTime z2 z3
      feeGrowthGlobal1 feeGrowthGlobal0 positionBase slot0Tick liquidityDelta
      tickUpper tickLower source : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨13242⟩
      (obsWord :: burnPositionKeyNewFreePtrWord :: ⟨64⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        cardinality :: liquidity :: index :: currentTick :: ⟨0⟩ :: time :: ⟨8⟩ ::
        ⟨19273⟩ :: z0 :: z1 :: callerTime :: z2 :: z3 :: feeGrowthGlobal1 ::
        feeGrowthGlobal0 :: positionBase :: slot0Tick :: liquidityDelta :: tickUpper ::
        tickLower :: source :: R)
      (burnObserveSingleAllocMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k C)
    (heq : UInt256.eq (UInt256.land time observationsUint32Mask)
        (burnObserveSingleDecodedBlockWord obsWord) ≠ ⟨0⟩)
    (hov : R.length + 55 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨20795⟩
      (EVM.wordOfInt v.maxLiquidityPerTick :: ⟨0⟩ :: callerTime ::
        burnObserveSingleDecodedTickWord obsWord ::
        burnObserveSingleDecodedSecondsWord obsWord :: feeGrowthGlobal1 ::
        feeGrowthGlobal0 :: liquidityDelta :: slot0Tick :: tickLower :: ⟨5⟩ ::
        ⟨19331⟩ :: burnObserveSingleDecodedSecondsWord obsWord ::
        burnObserveSingleDecodedTickWord obsWord :: callerTime :: z2 :: z3 ::
        feeGrowthGlobal1 :: feeGrowthGlobal0 :: positionBase :: slot0Tick ::
        liquidityDelta :: tickUpper :: tickLower :: source :: R)
      (burnObserveSingleDecodedMem σ ee obsWord) (UInt256.ofNat 21) rdata
      (cA, σ) k' C' := by
  obtain ⟨_, _, hret⟩ :=
    uniswapV3PoolBurnObserveSingleTimestampEqualLoadedReturn
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (obsWord := obsWord) (cardinality := cardinality) (liquidity := liquidity)
      (index := index) (tick := currentTick) (time := time) (ret := ⟨19273⟩)
      (R := z0 :: z1 :: callerTime :: z2 :: z3 :: feeGrowthGlobal1 ::
        feeGrowthGlobal0 :: positionBase :: slot0Tick :: liquidityDelta :: tickUpper ::
        tickLower :: source :: R)
      (rdata := rdata) (cA := cA) (σ := σ) hpatch h heq
      (uniswapV3PoolBurnJumpDestPatched19273 hpatch)
      (by
        have hlen := hov
        simp only [List.length_cons] at hlen ⊢
        omega)
  exact
    uniswapV3PoolBurnPostObserveSingleToLowerTickUpdate
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (seconds := burnObserveSingleDecodedSecondsWord obsWord)
      (tick := burnObserveSingleDecodedTickWord obsWord) (z0 := z0) (z1 := z1)
      (time := callerTime) (z2 := z2) (z3 := z3)
      (feeGrowthGlobal1 := feeGrowthGlobal1) (feeGrowthGlobal0 := feeGrowthGlobal0)
      (positionBase := positionBase) (slot0Tick := slot0Tick)
      (liquidityDelta := liquidityDelta) (tickUpper := tickUpper)
      (tickLower := tickLower) (source := source) (R := R)
      (mem := burnObserveSingleDecodedMem σ ee obsWord) (aw := UInt256.ofNat 21)
      (rdata := rdata) (cA := cA) (σ := σ) hpatch hret (by
        have hlen := hov
        omega)

abbrev burnTickUpdateLowerArgValues (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) : List Value :=
  [ burnTickLowerValue I,
    burnSlot0TickValue σ I,
    burnLiquidityDeltaValue I,
    burnFeeGrowthGlobal0Value σ I,
    burnFeeGrowthGlobal1Value σ I,
    .int (Int.ofNat (burnObserveSingleSecondsPerLiquidityWord σ I).toNat),
    wordToElem (.int int56Int) (burnObserveSingleTickStorageWord σ I),
    burnBlockTimestamp32Value I,
    .bool false,
    .int v.maxLiquidityPerTick ]

abbrev burnTickUpdateLowerStore (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) : Store :=
  ((((((((((∅ : Store)
    |>.insert "maxLiquidity" (.int v.maxLiquidityPerTick))
    |>.insert "upper" (.bool false))
    |>.insert "time" (burnBlockTimestamp32Value I))
    |>.insert "tickCumulative" (wordToElem (.int int56Int)
      (burnObserveSingleTickStorageWord σ I)))
    |>.insert "secondsPerLiquidityCumulativeX128"
      (.int (Int.ofNat (burnObserveSingleSecondsPerLiquidityWord σ I).toNat)))
    |>.insert "feeGrowthGlobal1X128" (burnFeeGrowthGlobal1Value σ I))
    |>.insert "feeGrowthGlobal0X128" (burnFeeGrowthGlobal0Value σ I))
    |>.insert "liquidityDelta" (burnLiquidityDeltaValue I))
    |>.insert "tickCurrent" (burnSlot0TickValue σ I))
    |>.insert "tick" (burnTickLowerValue I)

abbrev burnTickUpdateLowerFrame (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) : Frame :=
  { contract := contract v, locals := burnTickUpdateLowerStore v σ I }

theorem burnTickUpdateLower_bindParams (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) :
    bindParams? tickUpdateFunction.params (burnTickUpdateLowerArgValues v σ I) =
      some (burnTickUpdateLowerStore v σ I) := by
  rfl

theorem burnAfterObserveSingleFrame_observedForUpdate {v : PoolImmutables}
    (σ : AccountMap) (I : ExecutionEnv) :
    (burnModifyPositionAfterObserveSingleFrame v σ I).locals.get? "observedForUpdate" =
      some (.tuple (burnObserveSingleTimestampEqualReturnValues σ I)) := by
  rw [burnModifyPositionAfterObserveSingleFrame]
  exact store_get_self (burnModifyPositionAfterTimeFrame v σ I).locals
    "observedForUpdate" (.tuple (burnObserveSingleTimestampEqualReturnValues σ I))

theorem burnAfterObserveSingleFrame_time {v : PoolImmutables} (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnModifyPositionAfterObserveSingleFrame v σ I).locals.get? "time" =
      some (burnBlockTimestamp32Value I) := by
  rw [burnModifyPositionAfterObserveSingleFrame]
  rw [store_get_ne (burnModifyPositionAfterTimeFrame v σ I).locals
    (k := "observedForUpdate") (a := "time")
    (.tuple (burnObserveSingleTimestampEqualReturnValues σ I)) (by native_decide)]
  rw [burnModifyPositionAfterTimeFrame]
  exact store_get_self (burnModifyPositionAfterFeeGrowthGlobalsFrame v σ I).locals
    "time" (burnBlockTimestamp32Value I)

theorem burnAfterObserveSingleFrame_tickLower {v : PoolImmutables} (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnModifyPositionAfterObserveSingleFrame v σ I).locals.get? "tickLower" =
      some (burnTickLowerValue I) := by
  rw [burnModifyPositionAfterObserveSingleFrame]
  rw [store_get_ne (burnModifyPositionAfterTimeFrame v σ I).locals
    (k := "observedForUpdate") (a := "tickLower")
    (.tuple (burnObserveSingleTimestampEqualReturnValues σ I)) (by native_decide)]
  rw [burnModifyPositionAfterTimeFrame]
  rw [store_get_ne (burnModifyPositionAfterFeeGrowthGlobalsFrame v σ I).locals
    (k := "time") (a := "tickLower") (burnBlockTimestamp32Value I)
    (by native_decide)]
  exact burnAfterFeeGrowthGlobalsFrame_tickLower σ I

theorem burnAfterObserveSingleFrame_slot0tick {v : PoolImmutables} (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnModifyPositionAfterObserveSingleFrame v σ I).locals.get? "_slot0tick" =
      some (burnSlot0TickValue σ I) := by
  rw [burnModifyPositionAfterObserveSingleFrame]
  rw [store_get_ne (burnModifyPositionAfterTimeFrame v σ I).locals
    (k := "observedForUpdate") (a := "_slot0tick")
    (.tuple (burnObserveSingleTimestampEqualReturnValues σ I)) (by native_decide)]
  rw [burnModifyPositionAfterTimeFrame]
  rw [store_get_ne (burnModifyPositionAfterFeeGrowthGlobalsFrame v σ I).locals
    (k := "time") (a := "_slot0tick") (burnBlockTimestamp32Value I)
    (by native_decide)]
  exact burnAfterFeeGrowthGlobalsFrame_slot0tick σ I

theorem burnAfterObserveSingleFrame_liquidityDelta {v : PoolImmutables}
    (σ : AccountMap) (I : ExecutionEnv) :
    (burnModifyPositionAfterObserveSingleFrame v σ I).locals.get? "liquidityDelta" =
      some (burnLiquidityDeltaValue I) := by
  rw [burnModifyPositionAfterObserveSingleFrame]
  rw [store_get_ne (burnModifyPositionAfterTimeFrame v σ I).locals
    (k := "observedForUpdate") (a := "liquidityDelta")
    (.tuple (burnObserveSingleTimestampEqualReturnValues σ I)) (by native_decide)]
  rw [burnModifyPositionAfterTimeFrame]
  rw [store_get_ne (burnModifyPositionAfterFeeGrowthGlobalsFrame v σ I).locals
    (k := "time") (a := "liquidityDelta") (burnBlockTimestamp32Value I)
    (by native_decide)]
  exact burnAfterFeeGrowthGlobalsFrame_liquidityDelta σ I

theorem burnAfterObserveSingleFrame_feeGrowthGlobal0 {v : PoolImmutables}
    (σ : AccountMap) (I : ExecutionEnv) :
    (burnModifyPositionAfterObserveSingleFrame v σ I).locals.get?
      "_feeGrowthGlobal0X128" = some (burnFeeGrowthGlobal0Value σ I) := by
  rw [burnModifyPositionAfterObserveSingleFrame]
  rw [store_get_ne (burnModifyPositionAfterTimeFrame v σ I).locals
    (k := "observedForUpdate") (a := "_feeGrowthGlobal0X128")
    (.tuple (burnObserveSingleTimestampEqualReturnValues σ I)) (by native_decide)]
  rw [burnModifyPositionAfterTimeFrame]
  rw [store_get_ne (burnModifyPositionAfterFeeGrowthGlobalsFrame v σ I).locals
    (k := "time") (a := "_feeGrowthGlobal0X128") (burnBlockTimestamp32Value I)
    (by native_decide)]
  exact burnAfterFeeGrowthGlobalsFrame_feeGrowthGlobal0 σ I

theorem burnAfterObserveSingleFrame_feeGrowthGlobal1 {v : PoolImmutables}
    (σ : AccountMap) (I : ExecutionEnv) :
    (burnModifyPositionAfterObserveSingleFrame v σ I).locals.get?
      "_feeGrowthGlobal1X128" = some (burnFeeGrowthGlobal1Value σ I) := by
  rw [burnModifyPositionAfterObserveSingleFrame]
  rw [store_get_ne (burnModifyPositionAfterTimeFrame v σ I).locals
    (k := "observedForUpdate") (a := "_feeGrowthGlobal1X128")
    (.tuple (burnObserveSingleTimestampEqualReturnValues σ I)) (by native_decide)]
  rw [burnModifyPositionAfterTimeFrame]
  rw [store_get_ne (burnModifyPositionAfterFeeGrowthGlobalsFrame v σ I).locals
    (k := "time") (a := "_feeGrowthGlobal1X128") (burnBlockTimestamp32Value I)
    (by native_decide)]
  exact burnAfterFeeGrowthGlobalsFrame_feeGrowthGlobal1 σ I

theorem burnModifyPosition_evalLowerTickUpdateArgsAfterObserveSingle
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExprs? (config v) (burnModifyPositionAfterObserveSingleFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      [ .var "tickLower", .var "_slot0tick", .var "liquidityDelta",
        .var "_feeGrowthGlobal0X128", .var "_feeGrowthGlobal1X128",
        tuple1 (.var "observedForUpdate"), tuple0 (.var "observedForUpdate"),
        .var "time", .boolLit false, .intLit v.maxLiquidityPerTick ] =
      .ok (burnTickUpdateLowerArgValues v σ I) := by
  simp only [burnTickUpdateLowerArgValues, evalExprs?, evalExpr?, tuple0, tuple1,
    EvalResult.bind, bind, pure]
  rw [burnAfterObserveSingleFrame_tickLower (v := v),
    burnAfterObserveSingleFrame_slot0tick (v := v),
    burnAfterObserveSingleFrame_liquidityDelta (v := v),
    burnAfterObserveSingleFrame_feeGrowthGlobal0 (v := v),
    burnAfterObserveSingleFrame_feeGrowthGlobal1 (v := v),
    burnAfterObserveSingleFrame_observedForUpdate (v := v),
    burnAfterObserveSingleFrame_time (v := v)]
  rfl

theorem uniswapV3PoolLookupTickUpdate (v : PoolImmutables) :
    lookupCallable? (contract v) "tickUpdate" =
      some tickUpdateFunction.toCallable := by
  simp [lookupCallable?, lookupFunction?, contract, functions, getSqrtRatioAtTickFunction,
    getTickAtSqrtRatioFunction, oracleLteFunction, oracleTransformFunction,
    getSurroundingObservationsFunction, observeSingleFunction, observeBodyFunction,
    liquidityAddDeltaFunction, oracleWriteFunction, tickGetFeeGrowthInsideFunction,
    tickUpdateFunction, tickClearFunction, tickBitmapFlipFunction, positionUpdateFunction,
    getAmount0DeltaUnsignedFunction, getAmount1DeltaUnsignedFunction,
    getAmount0DeltaSignedFunction, getAmount1DeltaSignedFunction, modifyPositionFunction]

end Benchmarks.UniswapV3Pool
