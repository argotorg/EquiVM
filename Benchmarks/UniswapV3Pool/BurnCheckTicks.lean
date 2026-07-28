import Benchmarks.UniswapV3Pool.BurnNoDelegate

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

abbrev burnModifyPositionMload (I : ExecutionEnv) (off : UInt256) : UInt256 :=
  if off.toNat ≥ (burnModifyPositionMem4 I).size ∨ off ≥ UInt256.ofNat 8 * ⟨32⟩ then
    ⟨0⟩
  else
    UInt256.ofNat
      (fromByteArrayBigEndian ((burnModifyPositionMem4 I).readWithPadding off.toNat 32))

abbrev burnModifyPositionTickLowerLoad (I : ExecutionEnv) : UInt256 :=
  burnModifyPositionMload I ⟨160⟩

abbrev burnModifyPositionTickUpperLoad (I : ExecutionEnv) : UInt256 :=
  burnModifyPositionMload I ⟨192⟩

abbrev burnModifyPositionFreePtrLoad (I : ExecutionEnv) : UInt256 :=
  burnModifyPositionMload I ⟨64⟩

private theorem burnModifyPositionMem0_size :
    burnModifyPositionMem0.size = 96 := by
  unfold burnModifyPositionMem0
  change ((UInt256.toByteArray (⟨256⟩ : UInt256)).write 0 solcFreePtrMem 64 32).size = 96
  exact toByteArray_write32_size_of_le solcFreePtrMem (⟨256⟩ : UInt256) 64 96 96
    solcFreePtrMem_size (by rw [solcFreePtrMem_size]; omega) (by omega)

private theorem burnModifyPositionMem0_read64 :
    burnModifyPositionMem0.readWithPadding 64 32 = UInt256.toByteArray ⟨256⟩ := by
  unfold burnModifyPositionMem0
  change ((UInt256.toByteArray (⟨256⟩ : UInt256)).write 0 solcFreePtrMem 64 32).readWithPadding 64 32 =
    UInt256.toByteArray ⟨256⟩
  exact toByteArray_write_read_back_of_gap (⟨256⟩ : UInt256) solcFreePtrMem 64
    (by rw [solcFreePtrMem_size]; native_decide)

private theorem burnModifyPositionMem4_cascadeFromMem0 (I : ExecutionEnv) :
    burnModifyPositionMem4 I =
      writeCascade burnModifyPositionMem0
        [(128, UInt256.ofNat I.source.val),
         (160, UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I)),
         (192, UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I)),
         (224, UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))] := by
  rfl

theorem burnModifyPositionMem4_size (I : ExecutionEnv) :
    (burnModifyPositionMem4 I).size = 256 := by
  rw [burnModifyPositionMem4_cascadeFromMem0]
  exact writeCascade_size_of_base burnModifyPositionMem0 _ burnModifyPositionMem0_size
    (by simp [WriteGapsOk]; native_decide) (by simp [writeCascadeSize])

theorem burnModifyPositionMem4_read64 (I : ExecutionEnv) :
    (burnModifyPositionMem4 I).readWithPadding 64 32 = UInt256.toByteArray ⟨256⟩ := by
  rw [burnModifyPositionMem4_cascadeFromMem0]
  rw [writeCascade_read_preserved_of_base burnModifyPositionMem0 (base := 96)]
  exact burnModifyPositionMem0_read64
  · exact burnModifyPositionMem0_size
  · simp [WindowDisjointFromWrites]
    native_decide

theorem burnModifyPositionFreePtrLoad_eq (I : ExecutionEnv) :
    burnModifyPositionFreePtrLoad I = ⟨256⟩ := by
  unfold burnModifyPositionFreePtrLoad burnModifyPositionMload
  exact mloadWordValue_of_readWithPadding
    (mem := burnModifyPositionMem4 I) (aw := UInt256.ofNat 8) (off := ⟨64⟩)
    (v := ⟨256⟩) (by rw [burnModifyPositionMem4_size I]; native_decide)
    (by native_decide) (burnModifyPositionMem4_read64 I)

private theorem writeCascade_size_ge_base
    (mem : ByteArray) (writes : List (Nat × UInt256))
    (hok : WriteGapsOk mem.size writes) :
    mem.size ≤ (writeCascade mem writes).size := by
  induction writes generalizing mem with
  | nil => simp [writeCascade]
  | cons write rest ih =>
      rcases write with ⟨off, word⟩
      rcases hok with ⟨hgap, hrest⟩
      rw [writeCascade_cons]
      have hsize : (writeWord mem off word).size = max mem.size (off + 32) :=
        writeWord_size mem off word hgap
      have hrec :
          (writeWord mem off word).size ≤
            (writeCascade (writeWord mem off word) rest).size := by
        exact ih (writeWord mem off word) (by simpa [hsize] using hrest)
      have hbase : mem.size ≤ (writeWord mem off word).size := by
        rw [hsize]
        exact Nat.le_max_left _ _
      exact le_trans hbase hrec

private theorem burnModifyPositionMem4_cascadeFromMem1 (I : ExecutionEnv) :
    burnModifyPositionMem4 I =
      writeCascade (burnModifyPositionMem1 I)
        [(160, UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I)),
         (192, UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I)),
         (224, UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))] := by
  rfl

private theorem burnModifyPositionMem4_cascadeFromMem2 (I : ExecutionEnv) :
    burnModifyPositionMem4 I =
      writeCascade (burnModifyPositionMem2 I)
        [(192, UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I)),
         (224, UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))] := by
  rfl

private theorem burnModifyPositionLaterWritesLowerDisjoint (I : ExecutionEnv) :
    WindowDisjointFromWrites
      (max (burnModifyPositionMem1 I).size (160 + 32)) 160 32
      [(192, UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I)),
       (224, UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))] := by
  simp [WindowDisjointFromWrites]

private theorem burnModifyPositionLaterWritesUpperDisjoint (I : ExecutionEnv) :
    WindowDisjointFromWrites
      (max (burnModifyPositionMem2 I).size (192 + 32)) 192 32
      [(224, UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))] := by
  simp [WindowDisjointFromWrites]

private theorem burnModifyPositionLowerRestGapsOk (I : ExecutionEnv) :
    WriteGapsOk
      (writeWord (burnModifyPositionMem1 I) 160
        (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I))).size
      [(192, UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I)),
       (224, UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))] := by
  have hsize :
      (writeWord (burnModifyPositionMem1 I) 160
        (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I))).size =
        max (burnModifyPositionMem1 I).size (160 + 32) := by
    exact writeWord_size _ _ _ (lt_usize _ (by omega))
  simp [WriteGapsOk, hsize]

private theorem burnModifyPositionUpperRestGapsOk (I : ExecutionEnv) :
    WriteGapsOk
      (writeWord (burnModifyPositionMem2 I) 192
        (UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I))).size
      [(224, UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))] := by
  have hsize :
      (writeWord (burnModifyPositionMem2 I) 192
        (UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I))).size =
        max (burnModifyPositionMem2 I).size (192 + 32) := by
    exact writeWord_size _ _ _ (lt_usize _ (by omega))
  simp [WriteGapsOk, hsize]

theorem burnModifyPositionTickLowerLoad_eq (I : ExecutionEnv) :
    burnModifyPositionTickLowerLoad I =
      UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I) := by
  unfold burnModifyPositionTickLowerLoad burnModifyPositionMload
  rw [burnModifyPositionMem4_cascadeFromMem1]
  exact writeCascade_mload_word_of_head (mem := burnModifyPositionMem1 I) (off := 160)
    (offWord := (⟨160⟩ : UInt256)) (aw := UInt256.ofNat 8)
    (word := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I))
    (rest := [(192, UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I)),
      (224, UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))])
    (lt_usize _ (by omega)) (burnModifyPositionLaterWritesLowerDisjoint I) (by decide)
    (by
      rw [writeCascade_cons]
      have hsize :
          (writeWord (burnModifyPositionMem1 I) 160
            (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I))).size =
            max (burnModifyPositionMem1 I).size (160 + 32) := by
        exact writeWord_size _ _ _ (lt_usize _ (by omega))
      have hhead :
          160 < (writeWord (burnModifyPositionMem1 I) 160
            (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I))).size := by
        rw [hsize]
        omega
      have hge := writeCascade_size_ge_base
        (writeWord (burnModifyPositionMem1 I) 160
          (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I)))
        [(192, UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I)),
         (224, UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))]
        (burnModifyPositionLowerRestGapsOk I)
      exact lt_of_lt_of_le hhead hge)
    (by native_decide)

theorem burnModifyPositionTickUpperLoad_eq (I : ExecutionEnv) :
    burnModifyPositionTickUpperLoad I =
      UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I) := by
  unfold burnModifyPositionTickUpperLoad burnModifyPositionMload
  rw [burnModifyPositionMem4_cascadeFromMem2]
  exact writeCascade_mload_word_of_head (mem := burnModifyPositionMem2 I) (off := 192)
    (offWord := (⟨192⟩ : UInt256)) (aw := UInt256.ofNat 8)
    (word := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I))
    (rest := [(224, UInt256.signextend ⟨15⟩
      (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))])
    (lt_usize _ (by omega)) (burnModifyPositionLaterWritesUpperDisjoint I) (by decide)
    (by
      rw [writeCascade_cons]
      have hsize :
          (writeWord (burnModifyPositionMem2 I) 192
            (UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I))).size =
            max (burnModifyPositionMem2 I).size (192 + 32) := by
        exact writeWord_size _ _ _ (lt_usize _ (by omega))
      have hhead :
          192 < (writeWord (burnModifyPositionMem2 I) 192
            (UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I))).size := by
        rw [hsize]
        omega
      have hge := writeCascade_size_ge_base
        (writeWord (burnModifyPositionMem2 I) 192
          (UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I)))
        [(224, UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))]
        (burnModifyPositionUpperRestGapsOk I)
      exact lt_of_lt_of_le hhead hge)
    (by native_decide)

private theorem uniswapV3PoolPatchPreservesJumpDest17313 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨17313⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolPatchPreservesJumpDest16264 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨16264⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched16264 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨16264⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest16264

private theorem uniswapV3PoolPatchPreservesJumpDest17377 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨17377⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolPatchPreservesJumpDest17444 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨17444⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolPatchPreservesJumpDest17510 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨17510⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched17313 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨17313⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest17313

theorem uniswapV3PoolJumpDestPatched17377 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨17377⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest17377

theorem uniswapV3PoolJumpDestPatched17444 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨17444⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest17444

theorem uniswapV3PoolJumpDestPatched17510 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨17510⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest17510

private theorem uniswapV3PoolBurnCheckTicksPatchDisjoint33 {v : PoolImmutables}
    {pc : UInt256}
    (hlo : 16246 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 19295) :
    ∀ p ∈ patches v, pc.toNat + 33 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals omega

private theorem uniswapV3PoolBurnCheckTicksDecodeEqTemplate {v : PoolImmutables}
    {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hlo : 16246 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 19295) :
    decode code pc = decode uniswapV3PoolBytecode pc := by
  exact uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch
    (by
      have hsize : 19295 ≤ uniswapV3PoolBytecode.size := by native_decide
      omega)
    (uniswapV3PoolBurnCheckTicksPatchDisjoint33 (v := v) (pc := pc) hlo hhi)

theorem uniswapV3PoolBurnEnterCheckTicks {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨16246⟩
      (⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        burnAmountCleanWord ee :: burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee ::
        ret :: R)
      (burnModifyPositionMem4 ee) (UInt256.ofNat 8) rdata (cA, σ) k C)
    (hov : R.length + 23 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨17313⟩
      (burnModifyPositionTickUpperLoad ee :: burnModifyPositionTickLowerLoad ee :: ⟨16264⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        burnAmountCleanWord ee :: burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee ::
        ret :: R)
      (burnModifyPositionMem4 ee) (UInt256.ofNat 8) rdata (cA, σ) k' C' := by
  have hd16246 : decode code ⟨16246⟩ = some (.JUMPDEST, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd16247 : decode code ⟨16247⟩ = some (.Push .PUSH2, some (⟨16264⟩, 2)) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd16250 : decode code ⟨16250⟩ = some (.DUP5, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd16251 : decode code ⟨16251⟩ = some (.Push .PUSH1, some (⟨32⟩, 1)) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd16253 : decode code ⟨16253⟩ = some (.ADD, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd16254 : decode code ⟨16254⟩ = some (.MLOAD, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd16255 : decode code ⟨16255⟩ = some (.DUP6, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd16256 : decode code ⟨16256⟩ = some (.Push .PUSH1, some (⟨64⟩, 1)) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd16258 : decode code ⟨16258⟩ = some (.ADD, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd16259 : decode code ⟨16259⟩ = some (.MLOAD, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd16260 : decode code ⟨16260⟩ = some (.Push .PUSH2, some (⟨17313⟩, 2)) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd16263 : decode code ⟨16263⟩ = some (.JUMP, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have rd16247 := by
    simpa using h.jumpdest hd16246
      (by simp only [List.length_cons]; omega)
  have rd16250 := by
    simpa using rd16247.push2 ⟨16264⟩ hd16247
      (by simp only [List.length_cons]; omega)
  have rd16251 := by
    simpa using rd16250.dup5 hd16250
      (by simp only [List.length_cons]; omega)
  have rd16253 := by
    simpa using rd16251.push1 ⟨32⟩ hd16251
      (by simp only [List.length_cons]; omega)
  have rd16254 := by
    simpa using rd16253.add hd16253
      (by simp only [List.length_cons]; omega)
  have rd16255 := by
    simpa [burnModifyPositionTickLowerLoad, burnModifyPositionMload] using
      rd16254.mload 0 (burnModifyPositionTickLowerLoad ee) (UInt256.ofNat 8)
        hd16254
        mem_cost
        (by rfl)
        (by native_decide)
        (by simp only [List.length_cons]; omega)
  have rd16256 := by
    simpa using rd16255.dup6 hd16255
      (by simp only [List.length_cons]; omega)
  have rd16258 := by
    simpa using rd16256.push1 ⟨64⟩ hd16256
      (by simp only [List.length_cons]; omega)
  have rd16259 := by
    simpa using rd16258.add hd16258
      (by simp only [List.length_cons]; omega)
  have rd16260 := by
    simpa [burnModifyPositionTickUpperLoad, burnModifyPositionMload] using
      rd16259.mload 0 (burnModifyPositionTickUpperLoad ee) (UInt256.ofNat 8)
        hd16259
        mem_cost
        (by rfl)
        (by native_decide)
        (by simp only [List.length_cons]; omega)
  have rd16263 := by
    simpa using rd16260.push2 ⟨17313⟩ hd16260
      (by simp only [List.length_cons]; omega)
  exact ⟨_, _, rd16263.jump hd16263 (uniswapV3PoolJumpDestPatched17313 hpatch)
    (by simp only [List.length_cons]; omega)⟩

theorem uniswapV3PoolBurnCheckTicksLtOk {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret lower upper : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨17313⟩ (upper :: lower :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hlt : UInt256.slt (UInt256.signextend ⟨2⟩ lower)
        (UInt256.signextend ⟨2⟩ upper) ≠ ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨17377⟩ (upper :: lower :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
  have hd17313 : decode code ⟨17313⟩ = some (.JUMPDEST, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17314 : decode code ⟨17314⟩ = some (.DUP1, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17315 : decode code ⟨17315⟩ = some (.Push .PUSH1, some (⟨2⟩, 1)) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17317 : decode code ⟨17317⟩ = some (.SIGNEXTEND, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17318 : decode code ⟨17318⟩ = some (.DUP3, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17319 : decode code ⟨17319⟩ = some (.Push .PUSH1, some (⟨2⟩, 1)) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17321 : decode code ⟨17321⟩ = some (.SIGNEXTEND, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17322 : decode code ⟨17322⟩ = some (.SLT, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17323 : decode code ⟨17323⟩ = some (.Push .PUSH2, some (⟨17377⟩, 2)) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17326 : decode code ⟨17326⟩ = some (.JUMPI, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have rd17314 := by
    simpa using h.jumpdest hd17313
      (by simp only [List.length_cons]; omega)
  have rd17315 := by
    simpa using rd17314.dup1 hd17314
      (by simp only [List.length_cons]; omega)
  have rd17317 := by
    simpa using rd17315.push1 ⟨2⟩ hd17315
      (by simp only [List.length_cons]; omega)
  have rd17318 := by
    simpa using burnRDSignextend rd17317 hd17317
      (by simp only [List.length_cons]; omega)
  have rd17319 := by
    simpa using rd17318.dup3 hd17318
      (by simp only [List.length_cons]; omega)
  have rd17321 := by
    simpa using rd17319.push1 ⟨2⟩ hd17319
      (by simp only [List.length_cons]; omega)
  have rd17322 := by
    simpa using burnRDSignextend rd17321 hd17321
      (by simp only [List.length_cons]; omega)
  have rd17323 := by
    simpa using rd17322.slt hd17322
      (by simp only [List.length_cons]; omega)
  have rd17326 := by
    simpa using rd17323.push2 ⟨17377⟩ hd17323
      (by simp only [List.length_cons]; omega)
  exact ⟨_, _, rd17326.jumpiT hd17326 hlt
    (uniswapV3PoolJumpDestPatched17377 hpatch)
    (by simp only [List.length_cons]; omega)⟩

private theorem uniswapV3PoolBurnTluRevertTailWf {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcErrorStringRevertTailWf code ⟨17327⟩ ⟨3⟩ ⟨5524565⟩ ⟨232⟩ .PUSH3 3 := by
  dsimp [solcErrorStringRevertTailWf]
  repeat' constructor
  all_goals
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide

def burnTluRevertWord : UInt256 :=
  UInt256.shiftLeft ⟨5524565⟩ ⟨232⟩

noncomputable def burnTluRevertMem0 (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray solcErrorStringSelector).write 0 (burnModifyPositionMem4 I) 256 32

noncomputable def burnTluRevertMem1 (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0 (burnTluRevertMem0 I) 260 32

noncomputable def burnTluRevertMem2 (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (⟨3⟩ : UInt256)).write 0 (burnTluRevertMem1 I) 292 32

noncomputable def burnTluRevertMem3 (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray burnTluRevertWord).write 0 (burnTluRevertMem2 I) 324 32

private theorem burnTluRevertMem0_size (I : ExecutionEnv) :
    (burnTluRevertMem0 I).size = 288 := by
  unfold burnTluRevertMem0
  exact toByteArray_write32_size_of_ge (burnModifyPositionMem4 I)
    solcErrorStringSelector 256 256 288 (burnModifyPositionMem4_size I)
    (by omega) (by native_decide) (by omega)

private theorem burnTluRevertMem1_size (I : ExecutionEnv) :
    (burnTluRevertMem1 I).size = 292 := by
  unfold burnTluRevertMem1
  exact toByteArray_write32_size_of_le (burnTluRevertMem0 I) (⟨32⟩ : UInt256)
    260 288 292 (burnTluRevertMem0_size I)
    (by rw [burnTluRevertMem0_size I]; omega) (by omega)

private theorem burnTluRevertMem2_size (I : ExecutionEnv) :
    (burnTluRevertMem2 I).size = 324 := by
  unfold burnTluRevertMem2
  exact toByteArray_write32_size_of_le (burnTluRevertMem1 I) (⟨3⟩ : UInt256)
    292 292 324 (burnTluRevertMem1_size I)
    (by rw [burnTluRevertMem1_size I]) (by omega)

private theorem burnTluRevertMem3_size (I : ExecutionEnv) :
    (burnTluRevertMem3 I).size = 356 := by
  unfold burnTluRevertMem3
  exact toByteArray_write32_size_of_ge (burnTluRevertMem2 I) burnTluRevertWord
    324 324 356 (burnTluRevertMem2_size I)
    (by omega) (by native_decide) (by omega)

private theorem burnTluRevertMem3_read64 (I : ExecutionEnv) :
    (burnTluRevertMem3 I).readWithPadding 64 32 = UInt256.toByteArray ⟨256⟩ := by
  unfold burnTluRevertMem3
  rw [toByteArray_write_read_below_of_gap burnTluRevertWord _ 324 64
    (by rw [burnTluRevertMem2_size I]; omega) (by omega)
    (by rw [burnTluRevertMem2_size I]; native_decide)]
  unfold burnTluRevertMem2
  rw [toByteArray_write_read_below_of_gap (⟨3⟩ : UInt256) _ 292 64
    (by rw [burnTluRevertMem1_size I]; omega) (by omega)
    (by rw [burnTluRevertMem1_size I]; native_decide)]
  unfold burnTluRevertMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 260 64
    (by rw [burnTluRevertMem0_size I]; omega) (by omega)
    (by rw [burnTluRevertMem0_size I]; native_decide)]
  unfold burnTluRevertMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 256 64
    (by rw [burnModifyPositionMem4_size I]; omega) (by omega)
    (by rw [burnModifyPositionMem4_size I]; native_decide)]
  exact burnModifyPositionMem4_read64 I

private theorem burnTluRevertMem3_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (burnTluRevertMem3 I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((burnTluRevertMem3 I).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨256⟩ :=
  mloadWordValue_of_readWithPadding (mem := burnTluRevertMem3 I)
    (aw := UInt256.ofNat 12) (off := ⟨64⟩) (v := ⟨256⟩)
    (by rw [burnTluRevertMem3_size I]; native_decide)
    (by native_decide) (burnTluRevertMem3_read64 I)

noncomputable def burnCheckTicksRevertMem3 (I : ExecutionEnv) (word : UInt256) : ByteArray :=
  (UInt256.toByteArray word).write 0 (burnTluRevertMem2 I) 324 32

private theorem burnCheckTicksRevertMem3_size (I : ExecutionEnv) (word : UInt256) :
    (burnCheckTicksRevertMem3 I word).size = 356 := by
  unfold burnCheckTicksRevertMem3
  exact toByteArray_write32_size_of_ge (burnTluRevertMem2 I) word
    324 324 356 (burnTluRevertMem2_size I)
    (by omega) (by native_decide) (by omega)

private theorem burnCheckTicksRevertMem3_read64 (I : ExecutionEnv) (word : UInt256) :
    (burnCheckTicksRevertMem3 I word).readWithPadding 64 32 =
      UInt256.toByteArray ⟨256⟩ := by
  unfold burnCheckTicksRevertMem3
  rw [toByteArray_write_read_below_of_gap word _ 324 64
    (by rw [burnTluRevertMem2_size I]; omega) (by omega)
    (by rw [burnTluRevertMem2_size I]; native_decide)]
  unfold burnTluRevertMem2
  rw [toByteArray_write_read_below_of_gap (⟨3⟩ : UInt256) _ 292 64
    (by rw [burnTluRevertMem1_size I]; omega) (by omega)
    (by rw [burnTluRevertMem1_size I]; native_decide)]
  unfold burnTluRevertMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 260 64
    (by rw [burnTluRevertMem0_size I]; omega) (by omega)
    (by rw [burnTluRevertMem0_size I]; native_decide)]
  unfold burnTluRevertMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 256 64
    (by rw [burnModifyPositionMem4_size I]; omega) (by omega)
    (by rw [burnModifyPositionMem4_size I]; native_decide)]
  exact burnModifyPositionMem4_read64 I

private theorem burnCheckTicksRevertMem3_mload64 (I : ExecutionEnv) (word : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (burnCheckTicksRevertMem3 I word).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((burnCheckTicksRevertMem3 I word).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨256⟩ :=
  mloadWordValue_of_readWithPadding (mem := burnCheckTicksRevertMem3 I word)
    (aw := UInt256.ofNat 12) (off := ⟨64⟩) (v := ⟨256⟩)
    (by rw [burnCheckTicksRevertMem3_size I word]; native_decide)
    (by native_decide) (burnCheckTicksRevertMem3_read64 I word)

theorem uniswapV3PoolBurnCheckTicksRevertTail {code : ByteArray}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc rawWord shift word : UInt256} {op : Operation.POp} {width : ℕ}
    {stk : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk
      (burnModifyPositionMem4 ee) (UInt256.ofNat 8) rdata (cA, σ) k C)
    (hwf : solcErrorStringRevertTailWf code pc ⟨3⟩ rawWord shift op width)
    (hpush : op ≠ .PUSH0)
    (hword : UInt256.shiftLeft rawWord shift = word)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with
    ⟨hd0, hd2, hd3, hd4, hd8, hd10, hd11, hd12, hd13, hd15, hd17, hd18,
      hd19, hd20, hd22, hd24, hd25, hd26, hd27, hdRawOut, hdShl, hd68,
      hdDup3, hdAdd, hdMstore3, hdSwap, hdMload, hdSwap2, hdDup2, hdSwap3,
      hdSub, hd100, hdAdd2, hdSwap4, hdRev⟩
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ hd0 (by evm_ov),
    raw dup1 hd2 (by evm_ov),
    raw mload 0 ⟨256⟩ (UInt256.ofNat 8) hd3
      mem_cost
      (by simpa [burnModifyPositionFreePtrLoad] using burnModifyPositionFreePtrLoad_eq ee)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4 (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ hd8 (by evm_ov),
    raw shl hd10 (by evm_ov),
    raw dup2 hd11 (by evm_ov),
    raw mstore 3 (burnTluRevertMem0 ee) (UInt256.ofNat 9)
      hd12 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw mstore 3 (burnTluRevertMem1 ee) (UInt256.ofNat 10)
      hd19 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨3⟩ hd20 (by evm_ov),
    raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw mstore 3 (burnTluRevertMem2 ee)
      (UInt256.ofNat 11) hd26 mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst rawWord (width := width) (op := op)
    hpush hd27 (by simp only [List.length_cons]; omega)
  have rdWord := evm_run rdRaw with [
    raw push1 shift hdRawOut (by evm_ov),
    raw shl hdShl (by evm_ov)]
  rw [hword] at rdWord
  exact evm_run rdWord with [
    raw push1 ⟨68⟩ hd68 (by evm_ov),
    raw dup3 hdDup3 (by evm_ov),
    raw add hdAdd (by evm_ov),
    raw mstore 3 (burnCheckTicksRevertMem3 ee word)
      (UInt256.ofNat 12) hdMstore3 mem_cost
      (by
        simp [burnCheckTicksRevertMem3]
        have hoff : ((⟨256⟩ : UInt256) + ⟨68⟩).toNat = 324 := by native_decide
        rw [hoff])
      (by decide) (by evm_ov),
    raw swap1 hdSwap (by evm_ov),
    raw mload 0 ⟨256⟩ (UInt256.ofNat 12) hdMload
      mem_cost
      (burnCheckTicksRevertMem3_mload64 ee word)
      (by decide) (by evm_ov),
    raw swap1 hdSwap2 (by evm_ov),
    raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap3 (by evm_ov),
    raw sub hdSub (by evm_ov),
    raw push1 ⟨100⟩ hd100 (by evm_ov),
    raw add hdAdd2 (by evm_ov),
    raw swap1 hdSwap4 (by evm_ov),
    raw rev 0 hdRev mem_cost (by evm_ov)]

theorem uniswapV3PoolBurnTluRevertTail {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {stk : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨17327⟩ stk
      (burnModifyPositionMem4 ee) (UInt256.ofNat 8) rdata (cA, σ) k C)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  rcases uniswapV3PoolBurnTluRevertTailWf hpatch with
    ⟨hd0, hd2, hd3, hd4, hd8, hd10, hd11, hd12, hd13, hd15, hd17, hd18,
      hd19, hd20, hd22, hd24, hd25, hd26, hd27, hdRawOut, hdShl, hd68,
      hdDup3, hdAdd, hdMstore3, hdSwap, hdMload, hdSwap2, hdDup2, hdSwap3,
      hdSub, hd100, hdAdd2, hdSwap4, hdRev⟩
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ hd0 (by evm_ov),
    raw dup1 hd2 (by evm_ov),
    raw mload 0 ⟨256⟩ (UInt256.ofNat 8) hd3
      mem_cost
      (by simpa [burnModifyPositionFreePtrLoad] using burnModifyPositionFreePtrLoad_eq ee)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4 (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ hd8 (by evm_ov),
    raw shl hd10 (by evm_ov),
    raw dup2 hd11 (by evm_ov),
    raw mstore 3 (burnTluRevertMem0 ee) (UInt256.ofNat 9)
      hd12 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw mstore 3 (burnTluRevertMem1 ee) (UInt256.ofNat 10)
      hd19 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨3⟩ hd20 (by evm_ov),
    raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw mstore 3 (burnTluRevertMem2 ee)
      (UInt256.ofNat 11) hd26 mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst (⟨5524565⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd27
    (by simp only [List.length_cons]; omega)
  have rdWord := evm_run rdRaw with [
    raw push1 ⟨232⟩ hdRawOut (by evm_ov),
    raw shl hdShl (by evm_ov)]
  exact evm_run rdWord with [
    raw push1 ⟨68⟩ hd68 (by evm_ov),
    raw dup3 hdDup3 (by evm_ov),
    raw add hdAdd (by evm_ov),
    raw mstore 3 (burnTluRevertMem3 ee)
      (UInt256.ofNat 12) hdMstore3 mem_cost
      (by
        simp [burnTluRevertMem3, burnTluRevertWord]
        have hoff : ((⟨256⟩ : UInt256) + ⟨68⟩).toNat = 324 := by native_decide
        rw [hoff])
      (by decide) (by evm_ov),
    raw swap1 hdSwap (by evm_ov),
    raw mload 0 ⟨256⟩ (UInt256.ofNat 12) hdMload
      mem_cost
      (burnTluRevertMem3_mload64 ee)
      (by decide) (by evm_ov),
    raw swap1 hdSwap2 (by evm_ov),
    raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap3 (by evm_ov),
    raw sub hdSub (by evm_ov),
    raw push1 ⟨100⟩ hd100 (by evm_ov),
    raw add hdAdd2 (by evm_ov),
    raw swap1 hdSwap4 (by evm_ov),
    raw rev 0 hdRev mem_cost (by evm_ov)]

private theorem uniswapV3PoolBurnTlmRevertTailWf {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcErrorStringRevertTailWf code ⟨17394⟩ ⟨3⟩ ⟨5524557⟩ ⟨232⟩ .PUSH3 3 := by
  dsimp [solcErrorStringRevertTailWf]
  repeat' constructor
  all_goals
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide

def burnTlmRevertWord : UInt256 :=
  UInt256.shiftLeft ⟨5524557⟩ ⟨232⟩

theorem uniswapV3PoolBurnTlmRevertTail {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {stk : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨17394⟩ stk
      (burnModifyPositionMem4 ee) (UInt256.ofNat 8) rdata (cA, σ) k C)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  exact uniswapV3PoolBurnCheckTicksRevertTail
    (pc := ⟨17394⟩) (rawWord := ⟨5524557⟩) (shift := ⟨232⟩)
    (word := burnTlmRevertWord) (op := .PUSH3) (width := 3)
    h (uniswapV3PoolBurnTlmRevertTailWf hpatch) (by native_decide) rfl hov

private theorem uniswapV3PoolBurnTumRevertTailWf {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcErrorStringRevertTailWf code ⟨17460⟩ ⟨3⟩ ⟨5526861⟩ ⟨232⟩ .PUSH3 3 := by
  dsimp [solcErrorStringRevertTailWf]
  repeat' constructor
  all_goals
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide

def burnTumRevertWord : UInt256 :=
  UInt256.shiftLeft ⟨5526861⟩ ⟨232⟩

theorem uniswapV3PoolBurnTumRevertTail {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {stk : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨17460⟩ stk
      (burnModifyPositionMem4 ee) (UInt256.ofNat 8) rdata (cA, σ) k C)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  exact uniswapV3PoolBurnCheckTicksRevertTail
    (pc := ⟨17460⟩) (rawWord := ⟨5526861⟩) (shift := ⟨232⟩)
    (word := burnTumRevertWord) (op := .PUSH3) (width := 3)
    h (uniswapV3PoolBurnTumRevertTailWf hpatch) (by native_decide) rfl hov

theorem uniswapV3PoolBurnCheckTicksLtRevert {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret lower upper : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨17313⟩ (upper :: lower :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hzero : UInt256.slt (UInt256.signextend ⟨2⟩ lower)
        (UInt256.signextend ⟨2⟩ upper) = ⟨0⟩)
    (hmem : mem = burnModifyPositionMem4 ee)
    (haw : aw = UInt256.ofNat 8)
    (hov : R.length + 8 ≤ 1024) :
    RDrev code g s0 := by
  subst hmem
  subst haw
  have hd17313 : decode code ⟨17313⟩ = some (.JUMPDEST, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17314 : decode code ⟨17314⟩ = some (.DUP1, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17315 : decode code ⟨17315⟩ = some (.Push .PUSH1, some (⟨2⟩, 1)) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17317 : decode code ⟨17317⟩ = some (.SIGNEXTEND, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17318 : decode code ⟨17318⟩ = some (.DUP3, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17319 : decode code ⟨17319⟩ = some (.Push .PUSH1, some (⟨2⟩, 1)) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17321 : decode code ⟨17321⟩ = some (.SIGNEXTEND, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17322 : decode code ⟨17322⟩ = some (.SLT, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17323 : decode code ⟨17323⟩ = some (.Push .PUSH2, some (⟨17377⟩, 2)) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17326 : decode code ⟨17326⟩ = some (.JUMPI, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have rd17314 := by
    simpa using h.jumpdest hd17313
      (by simp only [List.length_cons]; omega)
  have rd17315 := by
    simpa using rd17314.dup1 hd17314
      (by simp only [List.length_cons]; omega)
  have rd17317 := by
    simpa using rd17315.push1 ⟨2⟩ hd17315
      (by simp only [List.length_cons]; omega)
  have rd17318 := by
    simpa using burnRDSignextend rd17317 hd17317
      (by simp only [List.length_cons]; omega)
  have rd17319 := by
    simpa using rd17318.dup3 hd17318
      (by simp only [List.length_cons]; omega)
  have rd17321 := by
    simpa using rd17319.push1 ⟨2⟩ hd17319
      (by simp only [List.length_cons]; omega)
  have rd17322 := by
    simpa using burnRDSignextend rd17321 hd17321
      (by simp only [List.length_cons]; omega)
  have rd17323 := by
    simpa using rd17322.slt hd17322
      (by simp only [List.length_cons]; omega)
  have rd17326 := by
    simpa using rd17323.push2 ⟨17377⟩ hd17323
      (by simp only [List.length_cons]; omega)
  have rd17327 := rd17326.jumpiNT hd17326 hzero
    (by simp only [List.length_cons]; omega)
  exact uniswapV3PoolBurnTluRevertTail (v := v) (code := code) (ee := ee) (g := g)
    (s0 := s0) (stk := upper :: lower :: ret :: R) (rdata := rdata)
    (cA := cA) (σ := σ) hpatch rd17327
    (by simp only [List.length_cons]; omega)

theorem uniswapV3PoolModifyPositionSourceNoDelegateOk {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hguard : uniswapV3PoolNoDelegateCallGuard v I ≠ ⟨0⟩) :
    ExecBlock (config v) { contract := contract v, locals := burnModifyPositionStore I }
      (initState cA gh bl σ σ₀ g A I) (noDelegateCall v)
      (ExecResult.ok { contract := contract v, locals := burnModifyPositionStore I }
        (initState cA gh bl σ σ₀ g A I)) := by
  simpa [noDelegateCall, eqE] using
    (ExecBlock.consNormal
      (ExecStmt.requireTrue (uniswapV3PoolNoDelegateCallEvalTrue
        (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (L := burnModifyPositionStore I) (g := g) hguard))
      ExecBlock.nil)

theorem burnModifyPositionStore_tickLower (I : ExecutionEnv) :
    (burnModifyPositionStore I).get? "tickLower" = some (burnTickLowerValue I) := by
  rw [burnModifyPositionStore]
  rw [store_get_ne
    ((((∅ : Store).insert "liquidityDelta" (burnLiquidityDeltaValue I))
      |>.insert "tickUpper" (burnTickUpperValue I))
      |>.insert "tickLower" (burnTickLowerValue I))
    (k := "owner") (a := "tickLower") (.address I.source) (by native_decide)]
  exact store_get_self
    (((∅ : Store).insert "liquidityDelta" (burnLiquidityDeltaValue I))
      |>.insert "tickUpper" (burnTickUpperValue I))
    "tickLower" (burnTickLowerValue I)

theorem burnModifyPositionStore_tickUpper (I : ExecutionEnv) :
    (burnModifyPositionStore I).get? "tickUpper" = some (burnTickUpperValue I) := by
  rw [burnModifyPositionStore]
  rw [store_get_ne2
    (((∅ : Store).insert "liquidityDelta" (burnLiquidityDeltaValue I))
      |>.insert "tickUpper" (burnTickUpperValue I))
    (k1 := "tickLower") (k2 := "owner") (a := "tickUpper")
    (burnTickLowerValue I) (.address I.source) (by native_decide) (by native_decide)]
  exact store_get_self ((∅ : Store).insert "liquidityDelta" (burnLiquidityDeltaValue I))
    "tickUpper" (burnTickUpperValue I)

theorem burnTickLtSlt_eq (I : ExecutionEnv) :
    UInt256.slt
      (UInt256.signextend ⟨2⟩ (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I)))
      (UInt256.signextend ⟨2⟩ (UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I))) =
    if tickSpacingSint24Value (burnTickLowerWord I) <
        tickSpacingSint24Value (burnTickUpperWord I) then ⟨1⟩ else ⟨0⟩ := by
  simp only [burnTickLowerCleanWord, burnTickUpperCleanWord]
  rw [signextend_two_tickSpacing_idempotent (UInt256.signextend ⟨2⟩ (burnTickLowerWord I))]
  rw [signextend_two_tickSpacing_idempotent (UInt256.signextend ⟨2⟩ (burnTickUpperWord I))]
  rw [signextend_two_tickSpacing_idempotent (burnTickLowerWord I)]
  rw [signextend_two_tickSpacing_idempotent (burnTickUpperWord I)]
  rw [← wordOfInt_sint24Value_eq_signextend_two (burnTickLowerWord I)]
  rw [← wordOfInt_sint24Value_eq_signextend_two (burnTickUpperWord I)]
  exact slt_wordOfInt_int24 _ _ (tickSpacingSint24Value_ge _) (tickSpacingSint24Value_lt _)
    (tickSpacingSint24Value_ge _) (tickSpacingSint24Value_lt _)

theorem burnTickLtSlt_ne_zero (I : ExecutionEnv)
    (hlt :
      tickSpacingSint24Value (burnTickLowerWord I) <
        tickSpacingSint24Value (burnTickUpperWord I)) :
    UInt256.slt
      (UInt256.signextend ⟨2⟩ (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I)))
      (UInt256.signextend ⟨2⟩ (UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I))) ≠
        ⟨0⟩ := by
  rw [burnTickLtSlt_eq I, if_pos hlt]
  native_decide

theorem burnTickLtSlt_eq_zero (I : ExecutionEnv)
    (hlt :
      ¬ tickSpacingSint24Value (burnTickLowerWord I) <
        tickSpacingSint24Value (burnTickUpperWord I)) :
    UInt256.slt
      (UInt256.signextend ⟨2⟩ (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I)))
      (UInt256.signextend ⟨2⟩ (UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I))) =
        ⟨0⟩ := by
  rw [burnTickLtSlt_eq I, if_neg hlt]

def burnMinTickWord : UInt256 :=
  UInt256.lnot ⟨887271⟩

theorem burnMinTickWord_eq_wordOfInt :
    burnMinTickWord = EVM.wordOfInt (-887272) := by
  native_decide

theorem burnTickLowerMinSlt_eq (I : ExecutionEnv) :
    UInt256.slt
      (UInt256.signextend ⟨2⟩ (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I)))
      burnMinTickWord =
    if tickSpacingSint24Value (burnTickLowerWord I) < (-887272 : Int) then
      ⟨1⟩
    else
      ⟨0⟩ := by
  simp only [burnTickLowerCleanWord]
  rw [signextend_two_tickSpacing_idempotent (UInt256.signextend ⟨2⟩ (burnTickLowerWord I))]
  rw [signextend_two_tickSpacing_idempotent (burnTickLowerWord I)]
  rw [← wordOfInt_sint24Value_eq_signextend_two (burnTickLowerWord I)]
  rw [burnMinTickWord_eq_wordOfInt]
  exact slt_wordOfInt_int24 _ _ (tickSpacingSint24Value_ge _) (tickSpacingSint24Value_lt _)
    (by norm_num) (by norm_num)

theorem burnTickLowerMinSlt_ne_zero (I : ExecutionEnv)
    (hlt : tickSpacingSint24Value (burnTickLowerWord I) < (-887272 : Int)) :
    UInt256.slt
      (UInt256.signextend ⟨2⟩ (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I)))
      burnMinTickWord ≠ ⟨0⟩ := by
  rw [burnTickLowerMinSlt_eq I, if_pos hlt]
  native_decide

theorem burnTickLowerMinSlt_eq_zero (I : ExecutionEnv)
    (hlt : ¬ tickSpacingSint24Value (burnTickLowerWord I) < (-887272 : Int)) :
    UInt256.slt
      (UInt256.signextend ⟨2⟩ (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I)))
      burnMinTickWord = ⟨0⟩ := by
  rw [burnTickLowerMinSlt_eq I, if_neg hlt]

def burnMaxTickWord : UInt256 :=
  ⟨887272⟩

theorem burnMaxTickWord_eq_wordOfInt :
    burnMaxTickWord = EVM.wordOfInt (887272 : Int) := by
  native_decide

theorem burnTickUpperMaxSgt_eq (I : ExecutionEnv) :
    UInt256.sgt
      (UInt256.signextend ⟨2⟩ (UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I)))
      burnMaxTickWord =
    if (887272 : Int) < tickSpacingSint24Value (burnTickUpperWord I) then
      ⟨1⟩
    else
      ⟨0⟩ := by
  simp only [burnTickUpperCleanWord]
  rw [sgt_eq_slt_swap]
  rw [signextend_two_tickSpacing_idempotent (UInt256.signextend ⟨2⟩ (burnTickUpperWord I))]
  rw [signextend_two_tickSpacing_idempotent (burnTickUpperWord I)]
  rw [burnMaxTickWord_eq_wordOfInt]
  rw [← wordOfInt_sint24Value_eq_signextend_two (burnTickUpperWord I)]
  exact slt_wordOfInt_int24 _ _ (by norm_num) (by norm_num)
    (tickSpacingSint24Value_ge _) (tickSpacingSint24Value_lt _)

theorem burnTickUpperMaxSgt_ne_zero (I : ExecutionEnv)
    (hlt : (887272 : Int) < tickSpacingSint24Value (burnTickUpperWord I)) :
    UInt256.sgt
      (UInt256.signextend ⟨2⟩ (UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I)))
      burnMaxTickWord ≠ ⟨0⟩ := by
  rw [burnTickUpperMaxSgt_eq I, if_pos hlt]
  native_decide

theorem burnTickUpperMaxSgt_eq_zero (I : ExecutionEnv)
    (hlt : ¬ (887272 : Int) < tickSpacingSint24Value (burnTickUpperWord I)) :
    UInt256.sgt
      (UInt256.signextend ⟨2⟩ (UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I)))
      burnMaxTickWord = ⟨0⟩ := by
  rw [burnTickUpperMaxSgt_eq I, if_neg hlt]

theorem uniswapV3PoolBurnCheckTicksLowerOk {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret lower upper : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨17377⟩ (upper :: lower :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hge : UInt256.slt (UInt256.signextend ⟨2⟩ lower) burnMinTickWord = ⟨0⟩)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨17444⟩ (upper :: lower :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
  have hd17377 : decode code ⟨17377⟩ = some (.JUMPDEST, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17378 : decode code ⟨17378⟩ = some (.Push .PUSH3, some (⟨887271⟩, 3)) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17382 : decode code ⟨17382⟩ = some (.NOT, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17383 : decode code ⟨17383⟩ = some (.Push .PUSH1, some (⟨2⟩, 1)) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17385 : decode code ⟨17385⟩ = some (.DUP4, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17386 : decode code ⟨17386⟩ = some (.SWAP1, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17387 : decode code ⟨17387⟩ = some (.SIGNEXTEND, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17388 : decode code ⟨17388⟩ = some (.SLT, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17389 : decode code ⟨17389⟩ = some (.ISZERO, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17390 : decode code ⟨17390⟩ = some (.Push .PUSH2, some (⟨17444⟩, 2)) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17393 : decode code ⟨17393⟩ = some (.JUMPI, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have rd17378 := by
    simpa using h.jumpdest hd17377
      (by simp only [List.length_cons]; omega)
  have rd17382 := rd17378.pushConst (⟨887271⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd17378
    (by simp only [List.length_cons]; omega)
  have rd17383 := by
    simpa [burnMinTickWord] using rd17382.not hd17382
      (by simp only [List.length_cons]; omega)
  have rd17385 := by
    simpa using rd17383.push1 ⟨2⟩ hd17383
      (by simp only [List.length_cons]; omega)
  have rd17386 := by
    simpa using rd17385.dup4 hd17385
      (by simp only [List.length_cons]; omega)
  have rd17387 := by
    simpa using rd17386.swap1 hd17386
      (by simp only [List.length_cons]; omega)
  have rd17388 := by
    simpa using burnRDSignextend rd17387 hd17387
      (by simp only [List.length_cons]; omega)
  have rd17389 := by
    simpa [burnMinTickWord] using rd17388.slt hd17388
      (by simp only [List.length_cons]; omega)
  have rd17390 := by
    simpa using rd17389.iszero hd17389
      (by simp only [List.length_cons]; omega)
  have rd17393 := by
    simpa using rd17390.push2 ⟨17444⟩ hd17390
      (by simp only [List.length_cons]; omega)
  have hcond :
      UInt256.isZero (UInt256.slt (UInt256.signextend ⟨2⟩ lower) burnMinTickWord) ≠
        ⟨0⟩ := by
    rw [hge]
    native_decide
  exact ⟨_, _, rd17393.jumpiT hd17393 hcond
    (uniswapV3PoolJumpDestPatched17444 hpatch)
    (by simp only [List.length_cons]; omega)⟩

theorem uniswapV3PoolBurnCheckTicksLowerRevert {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret lower upper : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨17377⟩ (upper :: lower :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hlt : UInt256.slt (UInt256.signextend ⟨2⟩ lower) burnMinTickWord ≠ ⟨0⟩)
    (hmem : mem = burnModifyPositionMem4 ee)
    (haw : aw = UInt256.ofNat 8)
    (hov : R.length + 8 ≤ 1024) :
    RDrev code g s0 := by
  subst hmem
  subst haw
  have hd17377 : decode code ⟨17377⟩ = some (.JUMPDEST, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17378 : decode code ⟨17378⟩ = some (.Push .PUSH3, some (⟨887271⟩, 3)) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17382 : decode code ⟨17382⟩ = some (.NOT, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17383 : decode code ⟨17383⟩ = some (.Push .PUSH1, some (⟨2⟩, 1)) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17385 : decode code ⟨17385⟩ = some (.DUP4, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17386 : decode code ⟨17386⟩ = some (.SWAP1, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17387 : decode code ⟨17387⟩ = some (.SIGNEXTEND, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17388 : decode code ⟨17388⟩ = some (.SLT, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17389 : decode code ⟨17389⟩ = some (.ISZERO, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17390 : decode code ⟨17390⟩ = some (.Push .PUSH2, some (⟨17444⟩, 2)) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17393 : decode code ⟨17393⟩ = some (.JUMPI, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have rd17378 := by
    simpa using h.jumpdest hd17377
      (by simp only [List.length_cons]; omega)
  have rd17382 := rd17378.pushConst (⟨887271⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd17378
    (by simp only [List.length_cons]; omega)
  have rd17383 := by
    simpa [burnMinTickWord] using rd17382.not hd17382
      (by simp only [List.length_cons]; omega)
  have rd17385 := by
    simpa using rd17383.push1 ⟨2⟩ hd17383
      (by simp only [List.length_cons]; omega)
  have rd17386 := by
    simpa using rd17385.dup4 hd17385
      (by simp only [List.length_cons]; omega)
  have rd17387 := by
    simpa using rd17386.swap1 hd17386
      (by simp only [List.length_cons]; omega)
  have rd17388 := by
    simpa using burnRDSignextend rd17387 hd17387
      (by simp only [List.length_cons]; omega)
  have rd17389 := by
    simpa [burnMinTickWord] using rd17388.slt hd17388
      (by simp only [List.length_cons]; omega)
  have rd17390 := by
    simpa using rd17389.iszero hd17389
      (by simp only [List.length_cons]; omega)
  have rd17393 := by
    simpa using rd17390.push2 ⟨17444⟩ hd17390
      (by simp only [List.length_cons]; omega)
  have hcond :
      UInt256.isZero (UInt256.slt (UInt256.signextend ⟨2⟩ lower) burnMinTickWord) =
        ⟨0⟩ :=
    isZero_eq_zero_of_ne hlt
  have rd17394 := rd17393.jumpiNT hd17393 hcond
    (by simp only [List.length_cons]; omega)
  exact uniswapV3PoolBurnTlmRevertTail (v := v) (code := code) (ee := ee) (g := g)
    (s0 := s0) (stk := upper :: lower :: ret :: R) (rdata := rdata)
    (cA := cA) (σ := σ) hpatch rd17394
    (by simp only [List.length_cons]; omega)

theorem uniswapV3PoolBurnCheckTicksUpperOk {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret lower upper : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨17444⟩ (upper :: lower :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hle : UInt256.sgt (UInt256.signextend ⟨2⟩ upper) burnMaxTickWord = ⟨0⟩)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨17510⟩ (upper :: lower :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
  have hd17444 : decode code ⟨17444⟩ = some (.JUMPDEST, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17445 : decode code ⟨17445⟩ = some (.Push .PUSH3, some (⟨887272⟩, 3)) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17449 : decode code ⟨17449⟩ = some (.Push .PUSH1, some (⟨2⟩, 1)) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17451 : decode code ⟨17451⟩ = some (.DUP3, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17452 : decode code ⟨17452⟩ = some (.SWAP1, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17453 : decode code ⟨17453⟩ = some (.SIGNEXTEND, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17454 : decode code ⟨17454⟩ = some (.SGT, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17455 : decode code ⟨17455⟩ = some (.ISZERO, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17456 : decode code ⟨17456⟩ = some (.Push .PUSH2, some (⟨17510⟩, 2)) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17459 : decode code ⟨17459⟩ = some (.JUMPI, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have rd17445 := by
    simpa using h.jumpdest hd17444
      (by simp only [List.length_cons]; omega)
  have rd17449 := rd17445.pushConst (⟨887272⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd17445
    (by simp only [List.length_cons]; omega)
  have rd17451 := by
    simpa [burnMaxTickWord] using rd17449.push1 ⟨2⟩ hd17449
      (by simp only [List.length_cons]; omega)
  have rd17452 := by
    simpa using rd17451.dup3 hd17451
      (by simp only [List.length_cons]; omega)
  have rd17453 := by
    simpa using rd17452.swap1 hd17452
      (by simp only [List.length_cons]; omega)
  have rd17454 := by
    simpa using burnRDSignextend rd17453 hd17453
      (by simp only [List.length_cons]; omega)
  have rd17455 := by
    simpa [burnMaxTickWord] using rd17454.sgt hd17454
      (by simp only [List.length_cons]; omega)
  have rd17456 := by
    simpa using rd17455.iszero hd17455
      (by simp only [List.length_cons]; omega)
  have rd17459 := by
    simpa using rd17456.push2 ⟨17510⟩ hd17456
      (by simp only [List.length_cons]; omega)
  have hcond :
      UInt256.isZero (UInt256.sgt (UInt256.signextend ⟨2⟩ upper) burnMaxTickWord) ≠
        ⟨0⟩ := by
    rw [hle]
    native_decide
  exact ⟨_, _, rd17459.jumpiT hd17459 hcond
    (uniswapV3PoolJumpDestPatched17510 hpatch)
    (by simp only [List.length_cons]; omega)⟩

theorem uniswapV3PoolBurnCheckTicksReturn {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret lower upper : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨17510⟩ (upper :: lower :: ret :: R)
      mem aw rdata acc k C)
    (hjd : (D_J code 0).contains ret = true)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret R mem aw rdata acc k' C' := by
  have hd17510 : decode code ⟨17510⟩ = some (.JUMPDEST, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17511 : decode code ⟨17511⟩ = some (.POP, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17512 : decode code ⟨17512⟩ = some (.POP, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17513 : decode code ⟨17513⟩ = some (.JUMP, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have rd17511 := h.jumpdest hd17510 (by simp only [List.length_cons]; omega)
  have rd17512 := rd17511.pop hd17511 (by simp only [List.length_cons]; omega)
  have rd17513 := rd17512.pop hd17512 (by simp only [List.length_cons]; omega)
  exact ⟨_, _, rd17513.jump hd17513 hjd (by omega)⟩

theorem uniswapV3PoolBurnCheckTicksUpperRevert {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret lower upper : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨17444⟩ (upper :: lower :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hgt : UInt256.sgt (UInt256.signextend ⟨2⟩ upper) burnMaxTickWord ≠ ⟨0⟩)
    (hmem : mem = burnModifyPositionMem4 ee)
    (haw : aw = UInt256.ofNat 8)
    (hov : R.length + 8 ≤ 1024) :
    RDrev code g s0 := by
  subst hmem
  subst haw
  have hd17444 : decode code ⟨17444⟩ = some (.JUMPDEST, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17445 : decode code ⟨17445⟩ = some (.Push .PUSH3, some (⟨887272⟩, 3)) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17449 : decode code ⟨17449⟩ = some (.Push .PUSH1, some (⟨2⟩, 1)) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17451 : decode code ⟨17451⟩ = some (.DUP3, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17452 : decode code ⟨17452⟩ = some (.SWAP1, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17453 : decode code ⟨17453⟩ = some (.SIGNEXTEND, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17454 : decode code ⟨17454⟩ = some (.SGT, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17455 : decode code ⟨17455⟩ = some (.ISZERO, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17456 : decode code ⟨17456⟩ = some (.Push .PUSH2, some (⟨17510⟩, 2)) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd17459 : decode code ⟨17459⟩ = some (.JUMPI, .none) := by
    rw [uniswapV3PoolBurnCheckTicksDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have rd17445 := by
    simpa using h.jumpdest hd17444
      (by simp only [List.length_cons]; omega)
  have rd17449 := rd17445.pushConst (⟨887272⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd17445
    (by simp only [List.length_cons]; omega)
  have rd17451 := by
    simpa [burnMaxTickWord] using rd17449.push1 ⟨2⟩ hd17449
      (by simp only [List.length_cons]; omega)
  have rd17452 := by
    simpa using rd17451.dup3 hd17451
      (by simp only [List.length_cons]; omega)
  have rd17453 := by
    simpa using rd17452.swap1 hd17452
      (by simp only [List.length_cons]; omega)
  have rd17454 := by
    simpa using burnRDSignextend rd17453 hd17453
      (by simp only [List.length_cons]; omega)
  have rd17455 := by
    simpa [burnMaxTickWord] using rd17454.sgt hd17454
      (by simp only [List.length_cons]; omega)
  have rd17456 := by
    simpa using rd17455.iszero hd17455
      (by simp only [List.length_cons]; omega)
  have rd17459 := by
    simpa using rd17456.push2 ⟨17510⟩ hd17456
      (by simp only [List.length_cons]; omega)
  have hcond :
      UInt256.isZero (UInt256.sgt (UInt256.signextend ⟨2⟩ upper) burnMaxTickWord) =
        ⟨0⟩ :=
    isZero_eq_zero_of_ne hgt
  have rd17460 := rd17459.jumpiNT hd17459 hcond
    (by simp only [List.length_cons]; omega)
  exact uniswapV3PoolBurnTumRevertTail (v := v) (code := code) (ee := ee) (g := g)
    (s0 := s0) (stk := upper :: lower :: ret :: R) (rdata := rdata)
    (cA := cA) (σ := σ) hpatch rd17460
    (by simp only [List.length_cons]; omega)

theorem uniswapV3PoolModifyPositionEvalTickLtTrue {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hlt :
      tickSpacingSint24Value (burnTickLowerWord I) <
        tickSpacingSint24Value (burnTickUpperWord I)) :
    evalExpr? (config v) { contract := contract v, locals := burnModifyPositionStore I }
      (initState cA gh bl σ σ₀ g A I) (ltE (.var "tickLower") (.var "tickUpper")) =
        .ok (.bool true) := by
  have hLower := burnModifyPositionStore_tickLower I
  have hUpper := burnModifyPositionStore_tickUpper I
  simp only [ltE, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind]
  rw [hLower, hUpper]
  simp [evalBinaryOp?, hlt]

theorem uniswapV3PoolModifyPositionEvalTickLtFalse {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hlt :
      ¬ tickSpacingSint24Value (burnTickLowerWord I) <
        tickSpacingSint24Value (burnTickUpperWord I)) :
    evalExpr? (config v) { contract := contract v, locals := burnModifyPositionStore I }
      (initState cA gh bl σ σ₀ g A I) (ltE (.var "tickLower") (.var "tickUpper")) =
        .ok (.bool false) := by
  have hLower := burnModifyPositionStore_tickLower I
  have hUpper := burnModifyPositionStore_tickUpper I
  simp only [ltE, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind]
  rw [hLower, hUpper]
  simp [evalBinaryOp?, hlt]

theorem uniswapV3PoolModifyPositionEvalLowerGeTrue {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hge : ¬ tickSpacingSint24Value (burnTickLowerWord I) < (-887272 : Int)) :
    evalExpr? (config v) { contract := contract v, locals := burnModifyPositionStore I }
      (initState cA gh bl σ σ₀ g A I) (geE (.var "tickLower") minTick) =
        .ok (.bool true) := by
  have hLower := burnModifyPositionStore_tickLower I
  simp only [geE, minTick, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind]
  rw [hLower]
  have hge' : tickSpacingSint24Value (burnTickLowerWord I) >= (-887272 : Int) := by
    omega
  simp [evalBinaryOp?, hge']

theorem uniswapV3PoolModifyPositionEvalLowerGeFalse {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hlt : tickSpacingSint24Value (burnTickLowerWord I) < (-887272 : Int)) :
    evalExpr? (config v) { contract := contract v, locals := burnModifyPositionStore I }
      (initState cA gh bl σ σ₀ g A I) (geE (.var "tickLower") minTick) =
        .ok (.bool false) := by
  have hLower := burnModifyPositionStore_tickLower I
  simp only [geE, minTick, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind]
  rw [hLower]
  have hge' : ¬ tickSpacingSint24Value (burnTickLowerWord I) >= (-887272 : Int) := by
    omega
  simp [evalBinaryOp?, hge']

theorem uniswapV3PoolModifyPositionEvalUpperLeTrue {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hle : ¬ (887272 : Int) < tickSpacingSint24Value (burnTickUpperWord I)) :
    evalExpr? (config v) { contract := contract v, locals := burnModifyPositionStore I }
      (initState cA gh bl σ σ₀ g A I) (leE (.var "tickUpper") maxTick) =
        .ok (.bool true) := by
  have hUpper := burnModifyPositionStore_tickUpper I
  simp only [leE, maxTick, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind]
  rw [hUpper]
  have hle' : tickSpacingSint24Value (burnTickUpperWord I) <= (887272 : Int) := by
    omega
  simp [evalBinaryOp?, hle']

theorem uniswapV3PoolModifyPositionEvalUpperLeFalse {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hgt : (887272 : Int) < tickSpacingSint24Value (burnTickUpperWord I)) :
    evalExpr? (config v) { contract := contract v, locals := burnModifyPositionStore I }
      (initState cA gh bl σ σ₀ g A I) (leE (.var "tickUpper") maxTick) =
        .ok (.bool false) := by
  have hUpper := burnModifyPositionStore_tickUpper I
  simp only [leE, maxTick, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind]
  rw [hUpper]
  have hle' : ¬ tickSpacingSint24Value (burnTickUpperWord I) <= (887272 : Int) := by
    omega
  simp [evalBinaryOp?, hle']

theorem uniswapV3PoolModifyPositionSourceThroughTickLt {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hguard : uniswapV3PoolNoDelegateCallGuard v I ≠ ⟨0⟩)
    (hlt :
      tickSpacingSint24Value (burnTickLowerWord I) <
        tickSpacingSint24Value (burnTickUpperWord I)) :
    ExecBlock (config v) { contract := contract v, locals := burnModifyPositionStore I }
      (initState cA gh bl σ σ₀ g A I)
      (noDelegateCall v ++ [Stmt.require (ltE (.var "tickLower") (.var "tickUpper"))])
      (ExecResult.ok { contract := contract v, locals := burnModifyPositionStore I }
        (initState cA gh bl σ σ₀ g A I)) := by
  have hprefix := uniswapV3PoolModifyPositionSourceNoDelegateOk (v := v)
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) hguard
  have htail :
      ExecBlock (config v) { contract := contract v, locals := burnModifyPositionStore I }
        (initState cA gh bl σ σ₀ g A I)
        [Stmt.require (ltE (.var "tickLower") (.var "tickUpper"))]
        (ExecResult.ok { contract := contract v, locals := burnModifyPositionStore I }
          (initState cA gh bl σ σ₀ g A I)) := by
    exact ExecBlock.consNormal
      (ExecStmt.requireTrue (uniswapV3PoolModifyPositionEvalTickLtTrue
        (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hlt))
      ExecBlock.nil
  exact execBlock_append hprefix htail

theorem uniswapV3PoolModifyPositionSourceThroughLowerGe {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hguard : uniswapV3PoolNoDelegateCallGuard v I ≠ ⟨0⟩)
    (htickLt :
      tickSpacingSint24Value (burnTickLowerWord I) <
        tickSpacingSint24Value (burnTickUpperWord I))
    (hge : ¬ tickSpacingSint24Value (burnTickLowerWord I) < (-887272 : Int)) :
    ExecBlock (config v) { contract := contract v, locals := burnModifyPositionStore I }
      (initState cA gh bl σ σ₀ g A I)
      (noDelegateCall v ++
        [Stmt.require (ltE (.var "tickLower") (.var "tickUpper")),
         Stmt.require (geE (.var "tickLower") minTick)])
      (ExecResult.ok { contract := contract v, locals := burnModifyPositionStore I }
        (initState cA gh bl σ σ₀ g A I)) := by
  have hprefix := uniswapV3PoolModifyPositionSourceThroughTickLt (v := v)
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) hguard htickLt
  have htail :
      ExecBlock (config v) { contract := contract v, locals := burnModifyPositionStore I }
        (initState cA gh bl σ σ₀ g A I)
        [Stmt.require (geE (.var "tickLower") minTick)]
        (ExecResult.ok { contract := contract v, locals := burnModifyPositionStore I }
          (initState cA gh bl σ σ₀ g A I)) := by
    exact ExecBlock.consNormal
      (ExecStmt.requireTrue (uniswapV3PoolModifyPositionEvalLowerGeTrue
        (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hge))
      ExecBlock.nil
  simpa [List.append_assoc] using execBlock_append hprefix htail

theorem uniswapV3PoolModifyPositionSourceThroughUpperLe {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hguard : uniswapV3PoolNoDelegateCallGuard v I ≠ ⟨0⟩)
    (htickLt :
      tickSpacingSint24Value (burnTickLowerWord I) <
        tickSpacingSint24Value (burnTickUpperWord I))
    (hge : ¬ tickSpacingSint24Value (burnTickLowerWord I) < (-887272 : Int))
    (hle : ¬ (887272 : Int) < tickSpacingSint24Value (burnTickUpperWord I)) :
    ExecBlock (config v) { contract := contract v, locals := burnModifyPositionStore I }
      (initState cA gh bl σ σ₀ g A I)
      (noDelegateCall v ++ checkTicksBody (.var "tickLower") (.var "tickUpper"))
      (ExecResult.ok { contract := contract v, locals := burnModifyPositionStore I }
        (initState cA gh bl σ σ₀ g A I)) := by
  have hprefix := uniswapV3PoolModifyPositionSourceThroughLowerGe (v := v)
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) hguard htickLt hge
  have htail :
      ExecBlock (config v) { contract := contract v, locals := burnModifyPositionStore I }
        (initState cA gh bl σ σ₀ g A I)
        [Stmt.require (leE (.var "tickUpper") maxTick)]
        (ExecResult.ok { contract := contract v, locals := burnModifyPositionStore I }
          (initState cA gh bl σ σ₀ g A I)) := by
    exact ExecBlock.consNormal
      (ExecStmt.requireTrue (uniswapV3PoolModifyPositionEvalUpperLeTrue
        (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hle))
      ExecBlock.nil
  simpa [checkTicksBody, List.append_assoc] using execBlock_append hprefix htail

theorem uniswapV3PoolModifyPositionSourceTickLtRevertsPrefix {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hguard : uniswapV3PoolNoDelegateCallGuard v I ≠ ⟨0⟩)
    (hlt :
      ¬ tickSpacingSint24Value (burnTickLowerWord I) <
        tickSpacingSint24Value (burnTickUpperWord I))
    (rest : List Stmt) :
    ExecBlock (config v) { contract := contract v, locals := burnModifyPositionStore I }
      (initState cA gh bl σ σ₀ g A I)
      (noDelegateCall v ++ checkTicksBody (.var "tickLower") (.var "tickUpper") ++ rest)
      .reverted := by
  have hprefix := uniswapV3PoolModifyPositionSourceNoDelegateOk (v := v)
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) hguard
  have htail :
      ExecBlock (config v) { contract := contract v, locals := burnModifyPositionStore I }
        (initState cA gh bl σ σ₀ g A I)
        (Stmt.require (ltE (.var "tickLower") (.var "tickUpper")) ::
          Stmt.require (geE (.var "tickLower") minTick) ::
          Stmt.require (leE (.var "tickUpper") maxTick) :: rest)
        .reverted := by
    exact ExecBlock.consRevert
      (ExecStmt.requireFalse (uniswapV3PoolModifyPositionEvalTickLtFalse
        (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hlt))
  simpa [checkTicksBody, List.append_assoc] using execBlock_append hprefix htail

theorem uniswapV3PoolModifyPositionSourceLowerRevertsPrefix {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hguard : uniswapV3PoolNoDelegateCallGuard v I ≠ ⟨0⟩)
    (htickLt :
      tickSpacingSint24Value (burnTickLowerWord I) <
        tickSpacingSint24Value (burnTickUpperWord I))
    (hlt : tickSpacingSint24Value (burnTickLowerWord I) < (-887272 : Int))
    (rest : List Stmt) :
    ExecBlock (config v) { contract := contract v, locals := burnModifyPositionStore I }
      (initState cA gh bl σ σ₀ g A I)
      (noDelegateCall v ++ checkTicksBody (.var "tickLower") (.var "tickUpper") ++ rest)
      .reverted := by
  have hprefix := uniswapV3PoolModifyPositionSourceThroughTickLt (v := v)
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) hguard htickLt
  have htail :
      ExecBlock (config v) { contract := contract v, locals := burnModifyPositionStore I }
        (initState cA gh bl σ σ₀ g A I)
        (Stmt.require (geE (.var "tickLower") minTick) ::
          Stmt.require (leE (.var "tickUpper") maxTick) :: rest)
        .reverted := by
    exact ExecBlock.consRevert
      (ExecStmt.requireFalse (uniswapV3PoolModifyPositionEvalLowerGeFalse
        (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hlt))
  simpa [checkTicksBody, List.append_assoc] using execBlock_append hprefix htail

theorem uniswapV3PoolModifyPositionSourceUpperRevertsPrefix {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hguard : uniswapV3PoolNoDelegateCallGuard v I ≠ ⟨0⟩)
    (htickLt :
      tickSpacingSint24Value (burnTickLowerWord I) <
        tickSpacingSint24Value (burnTickUpperWord I))
    (hge : ¬ tickSpacingSint24Value (burnTickLowerWord I) < (-887272 : Int))
    (hgt : (887272 : Int) < tickSpacingSint24Value (burnTickUpperWord I))
    (rest : List Stmt) :
    ExecBlock (config v) { contract := contract v, locals := burnModifyPositionStore I }
      (initState cA gh bl σ σ₀ g A I)
      (noDelegateCall v ++ checkTicksBody (.var "tickLower") (.var "tickUpper") ++ rest)
      .reverted := by
  have hprefix := uniswapV3PoolModifyPositionSourceThroughLowerGe (v := v)
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) hguard htickLt hge
  have htail :
      ExecBlock (config v) { contract := contract v, locals := burnModifyPositionStore I }
        (initState cA gh bl σ σ₀ g A I)
        (Stmt.require (leE (.var "tickUpper") maxTick) :: rest)
        .reverted := by
    exact ExecBlock.consRevert
      (ExecStmt.requireFalse (uniswapV3PoolModifyPositionEvalUpperLeFalse
        (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hgt))
  simpa [checkTicksBody, List.append_assoc] using execBlock_append hprefix htail

theorem uniswapV3PoolModifyPositionSourceTickLtReverts {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hguard : uniswapV3PoolNoDelegateCallGuard v I ≠ ⟨0⟩)
    (hlt :
      ¬ tickSpacingSint24Value (burnTickLowerWord I) <
        tickSpacingSint24Value (burnTickUpperWord I)) :
    ExecFuncBody (config v) { contract := contract v, locals := burnModifyPositionStore I }
      (initState cA gh bl σ σ₀ g A I) (modifyPositionFunction v).body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [modifyPositionFunction, noDelegateCall, checkTicksBody, List.append_assoc] using
    uniswapV3PoolModifyPositionSourceTickLtRevertsPrefix (v := v)
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hguard hlt
      ((modifyPositionFunction v).body.drop
        (noDelegateCall v ++ checkTicksBody (.var "tickLower") (.var "tickUpper")).length)

theorem uniswapV3PoolModifyPositionSourceLowerReverts {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hguard : uniswapV3PoolNoDelegateCallGuard v I ≠ ⟨0⟩)
    (htickLt :
      tickSpacingSint24Value (burnTickLowerWord I) <
        tickSpacingSint24Value (burnTickUpperWord I))
    (hlt : tickSpacingSint24Value (burnTickLowerWord I) < (-887272 : Int)) :
    ExecFuncBody (config v) { contract := contract v, locals := burnModifyPositionStore I }
      (initState cA gh bl σ σ₀ g A I) (modifyPositionFunction v).body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [modifyPositionFunction, noDelegateCall, checkTicksBody, List.append_assoc] using
    uniswapV3PoolModifyPositionSourceLowerRevertsPrefix (v := v)
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hguard htickLt hlt
      ((modifyPositionFunction v).body.drop
        (noDelegateCall v ++ checkTicksBody (.var "tickLower") (.var "tickUpper")).length)

theorem uniswapV3PoolModifyPositionSourceUpperReverts {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hguard : uniswapV3PoolNoDelegateCallGuard v I ≠ ⟨0⟩)
    (htickLt :
      tickSpacingSint24Value (burnTickLowerWord I) <
        tickSpacingSint24Value (burnTickUpperWord I))
    (hge : ¬ tickSpacingSint24Value (burnTickLowerWord I) < (-887272 : Int))
    (hgt : (887272 : Int) < tickSpacingSint24Value (burnTickUpperWord I)) :
    ExecFuncBody (config v) { contract := contract v, locals := burnModifyPositionStore I }
      (initState cA gh bl σ σ₀ g A I) (modifyPositionFunction v).body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [modifyPositionFunction, noDelegateCall, checkTicksBody, List.append_assoc] using
    uniswapV3PoolModifyPositionSourceUpperRevertsPrefix (v := v)
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hguard htickLt hge hgt
      ((modifyPositionFunction v).body.drop
        (noDelegateCall v ++ checkTicksBody (.var "tickLower") (.var "tickUpper")).length)

theorem uniswapV3PoolBurnSourceTickLtReverts {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hunlocked : burnUnlockedByte σ I ≠ ⟨0⟩)
    (hcanon :
      UInt256.signextend ⟨15⟩ (burnAmountCleanWord I) = burnAmountCleanWord I)
    (hguard : uniswapV3PoolNoDelegateCallGuard v I ≠ ⟨0⟩)
    (hlt :
      ¬ tickSpacingSint24Value (burnTickLowerWord I) <
        tickSpacingSint24Value (burnTickUpperWord I)) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (burnStore I)
      burnTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hprefix := uniswapV3PoolBurnSourceThroughLiquidityDelta (v := v)
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) hwv hunlocked hcanon
  have hlockState :
      Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner ⟨0⟩
          (burnLockedSlotWord σ I) =
        initState cA gh bl
          (sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I))
          σ₀ g A I := by
    unfold Solm.EVM.storageStore State.lookupAccount sstoreAccountMap
    cases hlookup : σ.find? I.codeOwner with
    | none =>
        simp [initState, Option.option, hlookup]
    | some _ =>
        simp [initState, State.setAccount, Account.updateStorage, Option.option, hlookup]
  have hstmt :
      ExecStmt (config v) (burnLiquidityDeltaFrame v I)
        (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner ⟨0⟩
          (burnLockedSlotWord σ I))
        (.internalCall "modifyPosition"
          [.env .caller, .var "tickLower", .var "tickUpper", .var "liquidityDelta"]
          "modified")
        .reverted := by
    rw [hlockState]
    refine internalCallFunctionRevert (callee := modifyPositionFunction v)
      (argVals := burnModifyPositionArgValues I) (locals := burnModifyPositionStore I)
      ?_ ?_ ?_ ?_
    · have hLower := burnLiquidityDeltaFrame_tickLower (v := v) I
      have hUpper := burnLiquidityDeltaFrame_tickUpper (v := v) I
      have hDelta := burnLiquidityDeltaFrame_liquidityDelta (v := v) I
      simp only [burnModifyPositionArgValues, evalExprs?, evalExpr?, envValue, initState,
        EvalResult.bind, bind, pure]
      rw [hLower, hUpper, hDelta]
      rfl
    · simpa [burnLiquidityDeltaFrame] using uniswapV3PoolLookupModifyPosition v
    · rfl
    · exact uniswapV3PoolModifyPositionSourceTickLtReverts (v := v)
        (cA := cA) (gh := gh) (bl := bl)
        (σ := sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I))
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hguard hlt
  simpa [burnTransition, nonpayable, lockPrefix] using
    execBlock_append hprefix (ExecBlock.consRevert hstmt)

theorem uniswapV3PoolBurnSourceLowerReverts {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hunlocked : burnUnlockedByte σ I ≠ ⟨0⟩)
    (hcanon :
      UInt256.signextend ⟨15⟩ (burnAmountCleanWord I) = burnAmountCleanWord I)
    (hguard : uniswapV3PoolNoDelegateCallGuard v I ≠ ⟨0⟩)
    (htickLt :
      tickSpacingSint24Value (burnTickLowerWord I) <
        tickSpacingSint24Value (burnTickUpperWord I))
    (hlt : tickSpacingSint24Value (burnTickLowerWord I) < (-887272 : Int)) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (burnStore I)
      burnTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hprefix := uniswapV3PoolBurnSourceThroughLiquidityDelta (v := v)
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) hwv hunlocked hcanon
  have hlockState :
      Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner ⟨0⟩
          (burnLockedSlotWord σ I) =
        initState cA gh bl
          (sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I))
          σ₀ g A I := by
    unfold Solm.EVM.storageStore State.lookupAccount sstoreAccountMap
    cases hlookup : σ.find? I.codeOwner with
    | none =>
        simp [initState, Option.option, hlookup]
    | some _ =>
        simp [initState, State.setAccount, Account.updateStorage, Option.option, hlookup]
  have hstmt :
      ExecStmt (config v) (burnLiquidityDeltaFrame v I)
        (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner ⟨0⟩
          (burnLockedSlotWord σ I))
        (.internalCall "modifyPosition"
          [.env .caller, .var "tickLower", .var "tickUpper", .var "liquidityDelta"]
          "modified")
        .reverted := by
    rw [hlockState]
    refine internalCallFunctionRevert (callee := modifyPositionFunction v)
      (argVals := burnModifyPositionArgValues I) (locals := burnModifyPositionStore I)
      ?_ ?_ ?_ ?_
    · have hLower := burnLiquidityDeltaFrame_tickLower (v := v) I
      have hUpper := burnLiquidityDeltaFrame_tickUpper (v := v) I
      have hDelta := burnLiquidityDeltaFrame_liquidityDelta (v := v) I
      simp only [burnModifyPositionArgValues, evalExprs?, evalExpr?, envValue, initState,
        EvalResult.bind, bind, pure]
      rw [hLower, hUpper, hDelta]
      rfl
    · simpa [burnLiquidityDeltaFrame] using uniswapV3PoolLookupModifyPosition v
    · rfl
    · exact uniswapV3PoolModifyPositionSourceLowerReverts (v := v)
        (cA := cA) (gh := gh) (bl := bl)
        (σ := sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I))
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hguard htickLt hlt
  simpa [burnTransition, nonpayable, lockPrefix] using
    execBlock_append hprefix (ExecBlock.consRevert hstmt)

theorem uniswapV3PoolBurnSourceUpperReverts {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hunlocked : burnUnlockedByte σ I ≠ ⟨0⟩)
    (hcanon :
      UInt256.signextend ⟨15⟩ (burnAmountCleanWord I) = burnAmountCleanWord I)
    (hguard : uniswapV3PoolNoDelegateCallGuard v I ≠ ⟨0⟩)
    (htickLt :
      tickSpacingSint24Value (burnTickLowerWord I) <
        tickSpacingSint24Value (burnTickUpperWord I))
    (hge : ¬ tickSpacingSint24Value (burnTickLowerWord I) < (-887272 : Int))
    (hgt : (887272 : Int) < tickSpacingSint24Value (burnTickUpperWord I)) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (burnStore I)
      burnTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hprefix := uniswapV3PoolBurnSourceThroughLiquidityDelta (v := v)
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) hwv hunlocked hcanon
  have hlockState :
      Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner ⟨0⟩
          (burnLockedSlotWord σ I) =
        initState cA gh bl
          (sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I))
          σ₀ g A I := by
    unfold Solm.EVM.storageStore State.lookupAccount sstoreAccountMap
    cases hlookup : σ.find? I.codeOwner with
    | none =>
        simp [initState, Option.option, hlookup]
    | some _ =>
        simp [initState, State.setAccount, Account.updateStorage, Option.option, hlookup]
  have hstmt :
      ExecStmt (config v) (burnLiquidityDeltaFrame v I)
        (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner ⟨0⟩
          (burnLockedSlotWord σ I))
        (.internalCall "modifyPosition"
          [.env .caller, .var "tickLower", .var "tickUpper", .var "liquidityDelta"]
          "modified")
        .reverted := by
    rw [hlockState]
    refine internalCallFunctionRevert (callee := modifyPositionFunction v)
      (argVals := burnModifyPositionArgValues I) (locals := burnModifyPositionStore I)
      ?_ ?_ ?_ ?_
    · have hLower := burnLiquidityDeltaFrame_tickLower (v := v) I
      have hUpper := burnLiquidityDeltaFrame_tickUpper (v := v) I
      have hDelta := burnLiquidityDeltaFrame_liquidityDelta (v := v) I
      simp only [burnModifyPositionArgValues, evalExprs?, evalExpr?, envValue, initState,
        EvalResult.bind, bind, pure]
      rw [hLower, hUpper, hDelta]
      rfl
    · simpa [burnLiquidityDeltaFrame] using uniswapV3PoolLookupModifyPosition v
    · rfl
    · exact uniswapV3PoolModifyPositionSourceUpperReverts (v := v)
        (cA := cA) (gh := gh) (bl := bl)
        (σ := sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I))
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hguard htickLt hge hgt
  simpa [burnTransition, nonpayable, lockPrefix] using
    execBlock_append hprefix (ExecBlock.consRevert hstmt)

end Benchmarks.UniswapV3Pool
