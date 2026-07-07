import Benchmarks.UniswapV3Pool.Common

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.UniswapV3Pool

abbrev uniswapV3PoolNoDelegateCallGuard (v : PoolImmutables)
    (I : ExecutionEnv) : UInt256 :=
  UInt256.eq
    (UInt256.land (EVM.Word.ofNat v.original.toNat) solcAddrMask)
    (UInt256.ofNat I.codeOwner.val)

private theorem uniswapV3PoolNoDelegateCallPatchDisjointWidth
    {v : PoolImmutables} {pc : UInt256} {n : Nat}
    (h : (5486 ≤ pc.toNat ∧ pc.toNat + n ≤ 6603) ∨
      (10597 ≤ pc.toNat ∧ pc.toNat + n ≤ 11259) ∨
      (11291 ≤ pc.toNat ∧ pc.toNat + n ≤ 15650)) :
    ∀ p ∈ patches v, pc.toNat + n ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  rcases h with hlow | hmid | hhigh
  all_goals
    simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
    rcases hp with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl
    all_goals omega

private theorem uniswapV3PoolNoDelegateCallDecodePatchedPush1 {v : PoolImmutables}
    {code : ByteArray} {pc n : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hwin : pc.toNat + 2 ≤ uniswapV3PoolBytecode.size)
    (hdisj : ∀ p ∈ patches v, pc.toNat + 2 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat)
    (hgetTemplate : uniswapV3PoolBytecode.get? pc.toNat = some 0x60)
    (hval : uInt256OfByteArray
        (uniswapV3PoolBytecode.extract' pc.toNat.succ (pc.toNat.succ + 1)) = n) :
    decode code pc = some (.Push .PUSH1, some (n, 1)) := by
  have hsize := uniswapV3PoolPatchedSize hpatch
  have htemplate64 : uniswapV3PoolBytecode.size < 2 ^ 64 := by native_decide
  have hget : code.get? pc.toNat = uniswapV3PoolBytecode.get? pc.toNat := by
    apply get?_eq_of_extract_one
    · rw [hsize]
      omega
    · omega
    · exact patchRuntime_extract_eq (start := pc.toNat) (stop := pc.toNat + 1)
        (template := uniswapV3PoolBytecode) (out := code) (ps := patches v)
        (by omega) (by omega)
        (fun p hp => by
          rcases hdisj p hp with hbefore | hafter
          · exact Or.inl (by omega)
          · exact Or.inr hafter)
        hpatch
  have hextract :
      code.extract' pc.toNat.succ (pc.toNat.succ + 1) =
        uniswapV3PoolBytecode.extract' pc.toNat.succ (pc.toNat.succ + 1) := by
    unfold ByteArray.extract'
    have hguard :
        (decide (pc.toNat.succ < 2 ^ 64) && decide (pc.toNat.succ + 1 < 2 ^ 64)) =
          true := by
      rw [Bool.and_eq_true]
      constructor <;> rw [decide_eq_true_eq] <;> omega
    rw [if_pos hguard, if_pos hguard]
    exact patchRuntime_extract_eq (start := pc.toNat.succ) (stop := pc.toNat.succ + 1)
      (template := uniswapV3PoolBytecode) (out := code) (ps := patches v)
      (by omega) (by omega)
      (fun p hp => by
        rcases hdisj p hp with hbefore | hafter
        · exact Or.inl hbefore
        · exact Or.inr (by omega))
      hpatch
  have hgetSome : code.get? pc.toNat = some 0x60 := by
    rw [hget, hgetTemplate]
  have hparse : (some (0x60 : UInt8) >>= parseInstr) = some (.Push .PUSH1) := by
    native_decide
  unfold decode
  rw [hgetSome, hparse]
  change some (Operation.Push Operation.POp.PUSH1,
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 1)), 1)) =
    some (Operation.Push Operation.POp.PUSH1, some (n, 1))
  rw [hextract, hval]

private theorem uniswapV3PoolNoDelegateCallDecodePatchedPush2 {v : PoolImmutables}
    {code : ByteArray} {pc n : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hwin : pc.toNat + 3 ≤ uniswapV3PoolBytecode.size)
    (hdisj : ∀ p ∈ patches v, pc.toNat + 3 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat)
    (hgetTemplate : uniswapV3PoolBytecode.get? pc.toNat = some 0x61)
    (hval : uInt256OfByteArray
        (uniswapV3PoolBytecode.extract' pc.toNat.succ (pc.toNat.succ + 2)) = n) :
    decode code pc = some (.Push .PUSH2, some (n, 2)) := by
  have hsize := uniswapV3PoolPatchedSize hpatch
  have htemplate64 : uniswapV3PoolBytecode.size < 2 ^ 64 := by native_decide
  have hget : code.get? pc.toNat = uniswapV3PoolBytecode.get? pc.toNat := by
    apply get?_eq_of_extract_one
    · rw [hsize]
      omega
    · omega
    · exact patchRuntime_extract_eq (start := pc.toNat) (stop := pc.toNat + 1)
        (template := uniswapV3PoolBytecode) (out := code) (ps := patches v)
        (by omega) (by omega)
        (fun p hp => by
          rcases hdisj p hp with hbefore | hafter
          · exact Or.inl (by omega)
          · exact Or.inr hafter)
        hpatch
  have hextract :
      code.extract' pc.toNat.succ (pc.toNat.succ + 2) =
        uniswapV3PoolBytecode.extract' pc.toNat.succ (pc.toNat.succ + 2) := by
    unfold ByteArray.extract'
    have hguard :
        (decide (pc.toNat.succ < 2 ^ 64) && decide (pc.toNat.succ + 2 < 2 ^ 64)) =
          true := by
      rw [Bool.and_eq_true]
      constructor <;> rw [decide_eq_true_eq] <;> omega
    rw [if_pos hguard, if_pos hguard]
    exact patchRuntime_extract_eq (start := pc.toNat.succ) (stop := pc.toNat.succ + 2)
      (template := uniswapV3PoolBytecode) (out := code) (ps := patches v)
      (by omega) (by omega)
      (fun p hp => by
        rcases hdisj p hp with hbefore | hafter
        · exact Or.inl hbefore
        · exact Or.inr (by omega))
      hpatch
  have hgetSome : code.get? pc.toNat = some 0x61 := by
    rw [hget, hgetTemplate]
  have hparse : (some (0x61 : UInt8) >>= parseInstr) = some (.Push .PUSH2) := by
    native_decide
  unfold decode
  rw [hgetSome, hparse]
  change some (Operation.Push Operation.POp.PUSH2,
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 2)), 2)) =
    some (Operation.Push Operation.POp.PUSH2, some (n, 2))
  rw [hextract, hval]

theorem uniswapV3PoolOriginalPatchWord {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    code.extract 11259 11291 = UInt256.toByteArray (EVM.Word.ofNat v.original.toNat) := by
  let value := UInt256.toByteArray (EVM.Word.ofNat v.original.toNat)
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
     (8174, UInt256.toByteArray (EVM.wordOfInt v.maxLiquidityPerTick)),
     (19295, UInt256.toByteArray (EVM.wordOfInt v.maxLiquidityPerTick)),
     (19350, UInt256.toByteArray (EVM.wordOfInt v.maxLiquidityPerTick))]
  have hpatch' : patchRuntime uniswapV3PoolBytecode (pre ++ (11259, value) :: []) =
      some code := by
    dsimp [pre, value]
    simpa [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup,
      toByteArray_eq_toBytesBE] using hpatch
  have hpost : ∀ p ∈ ([] : List (Nat × ByteArray)),
      11259 + 32 ≤ p.1 ∨ p.1 + 32 ≤ 11259 := by
    simp
  have hsize : value.size = 32 := by
    dsimp [value]
    exact toByteArray_size _
  simpa [value] using
    (patchRuntime_extract_patch (template := uniswapV3PoolBytecode) (out := code)
      (value := value) (pre := pre) (post := []) (offset := 11259) hsize hpost hpatch')

theorem uniswapV3PoolOriginalConstDecode {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    decode code ⟨11258⟩ =
      some (.Push .PUSH32, some (EVM.Word.ofNat v.original.toNat, 32)) := by
  have hsize := uniswapV3PoolPatchedSize hpatch
  have hget : code.get? ({ val := 11258 } : UInt256).toNat =
      uniswapV3PoolBytecode.get? ({ val := 11258 } : UInt256).toNat := by
    change code.get? 11258 = uniswapV3PoolBytecode.get? 11258
    apply get?_eq_of_extract_one
    · rw [hsize]
      native_decide
    · native_decide
    · exact patchRuntime_extract_eq (start := 11258) (stop := 11259)
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
  have hextract : code.extract' ({ val := 11258 } : UInt256).toNat.succ
      (({ val := 11258 } : UInt256).toNat.succ + 32) =
      UInt256.toByteArray (EVM.Word.ofNat v.original.toNat) := by
    change code.extract' 11259 11291 =
      UInt256.toByteArray (EVM.Word.ofNat v.original.toNat)
    unfold ByteArray.extract'
    have hguard : (decide (11259 < 2 ^ 64) && decide (11291 < 2 ^ 64)) = true := by
      native_decide
    rw [if_pos hguard]
    exact uniswapV3PoolOriginalPatchWord hpatch
  have hgetSome : code.get? ({ val := 11258 } : UInt256).toNat = some 0x7f := by
    rw [hget]
    native_decide
  have hparse : (some (0x7f : UInt8) >>= parseInstr) = some (.Push .PUSH32) := by
    native_decide
  unfold decode
  rw [hgetSome, hparse]
  change some (Operation.Push Operation.POp.PUSH32,
      some (uInt256OfByteArray
        (code.extract' ({ val := 11258 } : UInt256).toNat.succ
          (({ val := 11258 } : UInt256).toNat.succ + 32)), 32)) =
    some (Operation.Push Operation.POp.PUSH32, some (EVM.Word.ofNat v.original.toNat, 32))
  rw [hextract, uInt256OfByteArray_eq, fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

private theorem uniswapV3PoolPatchPreservesJumpDest5493 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨5493⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolPatchPreservesJumpDest11248 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨11248⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolPatchPreservesJumpDest11301 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨11301⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched5493 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨5493⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest5493

theorem uniswapV3PoolJumpDestPatched11248 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨11248⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest11248

theorem uniswapV3PoolJumpDestPatched11301 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨11301⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest11301

private theorem uniswapV3PoolNoDelegateCallDecodeNoArg {v : PoolImmutables}
    {code : ByteArray} {pc : UInt256} {byte : UInt8} {op : Operation}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hdisj : (5486 ≤ pc.toNat ∧ pc.toNat + 1 ≤ 6603) ∨
      (10597 ≤ pc.toNat ∧ pc.toNat + 1 ≤ 11259) ∨
      (11291 ≤ pc.toNat ∧ pc.toNat + 1 ≤ 15650))
    (hgetTemplate : uniswapV3PoolBytecode.get? pc.toNat = some byte)
    (hparse : (some byte >>= parseInstr) = some op)
    (harg : argOnNBytesOfInstr op = 0) :
    decode code pc = some (op, .none) := by
  refine uniswapV3PoolDecodePatchedNoArg (pc := pc) (byte := byte) (op := op)
    hpatch (by
      have hsize : 15650 ≤ uniswapV3PoolBytecode.size := by native_decide
      rcases hdisj with hlow | hmid | hhigh <;> omega) ?_ hgetTemplate hparse harg
  exact uniswapV3PoolNoDelegateCallPatchDisjointWidth (n := 1) hdisj

private theorem uniswapV3PoolNoDelegateCallJumpInOk
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨5486⟩ R mem aw rdata acc k C)
    (hov : R.length + 2 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨11248⟩ (⟨5493⟩ :: R) mem aw rdata acc k' C' := by
  have hd5486 : decode code ⟨5486⟩ = some (.Push .PUSH2, some (⟨5493⟩, 2)) := by
    refine uniswapV3PoolNoDelegateCallDecodePatchedPush2 hpatch (by native_decide)
      ?_ (by native_decide) (by native_decide)
    exact uniswapV3PoolNoDelegateCallPatchDisjointWidth (n := 3)
      (Or.inl ⟨by native_decide, by native_decide⟩)
  have hd5489 : decode code ⟨5489⟩ = some (.Push .PUSH2, some (⟨11248⟩, 2)) := by
    refine uniswapV3PoolNoDelegateCallDecodePatchedPush2 hpatch (by native_decide)
      ?_ (by native_decide) (by native_decide)
    exact uniswapV3PoolNoDelegateCallPatchDisjointWidth (n := 3)
      (Or.inl ⟨by native_decide, by native_decide⟩)
  have hd5492 : decode code ⟨5492⟩ = some (.JUMP, .none) := by
    exact uniswapV3PoolNoDelegateCallDecodeNoArg (byte := 0x56) (op := .JUMP)
      hpatch (Or.inl ⟨by native_decide, by native_decide⟩)
      (by native_decide) (by native_decide) (by native_decide)
  have rd5489 := by
    simpa using h.push2 ⟨5493⟩ hd5486 (by omega)
  have rd5492 := by
    simpa using rd5489.push2 ⟨11248⟩ hd5489 (by simp only [List.length_cons]; omega)
  exact ⟨_, _, rd5492.jump hd5492 (uniswapV3PoolJumpDestPatched11248 hpatch)
    (by simp only [List.length_cons]; omega)⟩

theorem uniswapV3PoolNoDelegateCallReturnOk
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {R : List UInt256} {mem : ByteArray} {aw ret : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨11248⟩ (ret :: R) mem aw rdata acc k C)
    (hguard : uniswapV3PoolNoDelegateCallGuard v ee ≠ ⟨0⟩)
    (htarget : (D_J code 0).contains ret = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret R mem aw rdata acc k' C' := by
  have hd11248 : decode code ⟨11248⟩ = some (.JUMPDEST, .none) := by
    exact uniswapV3PoolNoDelegateCallDecodeNoArg (byte := 0x5b) (op := .JUMPDEST)
      hpatch (Or.inr (Or.inl ⟨by native_decide, by native_decide⟩))
      (by native_decide) (by native_decide) (by native_decide)
  have hd11249 : decode code ⟨11249⟩ = some (.ADDRESS, .none) := by
    exact uniswapV3PoolNoDelegateCallDecodeNoArg (byte := 0x30) (op := .ADDRESS)
      hpatch (Or.inr (Or.inl ⟨by native_decide, by native_decide⟩))
      (by native_decide) (by native_decide) (by native_decide)
  have hd11250 : decode code ⟨11250⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    refine uniswapV3PoolNoDelegateCallDecodePatchedPush1 hpatch (by native_decide)
      ?_ (by native_decide) (by native_decide)
    exact uniswapV3PoolNoDelegateCallPatchDisjointWidth (n := 2)
      (Or.inr (Or.inl ⟨by native_decide, by native_decide⟩))
  have hd11252 : decode code ⟨11252⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    refine uniswapV3PoolNoDelegateCallDecodePatchedPush1 hpatch (by native_decide)
      ?_ (by native_decide) (by native_decide)
    exact uniswapV3PoolNoDelegateCallPatchDisjointWidth (n := 2)
      (Or.inr (Or.inl ⟨by native_decide, by native_decide⟩))
  have hd11254 : decode code ⟨11254⟩ = some (.Push .PUSH1, some (⟨160⟩, 1)) := by
    refine uniswapV3PoolNoDelegateCallDecodePatchedPush1 hpatch (by native_decide)
      ?_ (by native_decide) (by native_decide)
    exact uniswapV3PoolNoDelegateCallPatchDisjointWidth (n := 2)
      (Or.inr (Or.inl ⟨by native_decide, by native_decide⟩))
  have hd11256 : decode code ⟨11256⟩ = some (.SHL, .none) := by
    exact uniswapV3PoolNoDelegateCallDecodeNoArg (byte := 0x1b) (op := .SHL)
      hpatch (Or.inr (Or.inl ⟨by native_decide, by native_decide⟩))
      (by native_decide) (by native_decide) (by native_decide)
  have hd11257 : decode code ⟨11257⟩ = some (.SUB, .none) := by
    exact uniswapV3PoolNoDelegateCallDecodeNoArg (byte := 0x03) (op := .SUB)
      hpatch (Or.inr (Or.inl ⟨by native_decide, by native_decide⟩))
      (by native_decide) (by native_decide) (by native_decide)
  have hd11258 : decode code ⟨11258⟩ =
      some (.Push .PUSH32, some (EVM.Word.ofNat v.original.toNat, 32)) :=
    uniswapV3PoolOriginalConstDecode hpatch
  have hd11291 : decode code ⟨11291⟩ = some (.AND, .none) := by
    exact uniswapV3PoolNoDelegateCallDecodeNoArg (byte := 0x16) (op := .AND)
      hpatch (Or.inr (Or.inr ⟨by native_decide, by native_decide⟩))
      (by native_decide) (by native_decide) (by native_decide)
  have hd11292 : decode code ⟨11292⟩ = some (.EQ, .none) := by
    exact uniswapV3PoolNoDelegateCallDecodeNoArg (byte := 0x14) (op := .EQ)
      hpatch (Or.inr (Or.inr ⟨by native_decide, by native_decide⟩))
      (by native_decide) (by native_decide) (by native_decide)
  have hd11293 : decode code ⟨11293⟩ = some (.Push .PUSH2, some (⟨11301⟩, 2)) := by
    refine uniswapV3PoolNoDelegateCallDecodePatchedPush2 hpatch (by native_decide)
      ?_ (by native_decide) (by native_decide)
    exact uniswapV3PoolNoDelegateCallPatchDisjointWidth (n := 3)
      (Or.inr (Or.inr ⟨by native_decide, by native_decide⟩))
  have hd11296 : decode code ⟨11296⟩ = some (.JUMPI, .none) := by
    exact uniswapV3PoolNoDelegateCallDecodeNoArg (byte := 0x57) (op := .JUMPI)
      hpatch (Or.inr (Or.inr ⟨by native_decide, by native_decide⟩))
      (by native_decide) (by native_decide) (by native_decide)
  have hd11301 : decode code ⟨11301⟩ = some (.JUMPDEST, .none) := by
    exact uniswapV3PoolNoDelegateCallDecodeNoArg (byte := 0x5b) (op := .JUMPDEST)
      hpatch (Or.inr (Or.inr ⟨by native_decide, by native_decide⟩))
      (by native_decide) (by native_decide) (by native_decide)
  have hd11302 : decode code ⟨11302⟩ = some (.JUMP, .none) := by
    exact uniswapV3PoolNoDelegateCallDecodeNoArg (byte := 0x56) (op := .JUMP)
      hpatch (Or.inr (Or.inr ⟨by native_decide, by native_decide⟩))
      (by native_decide) (by native_decide) (by native_decide)
  have rd11249 := by
    simpa using h.jumpdest hd11248 (by evm_ov)
  have rd11250 := by
    simpa using rd11249.uniswapAddress hd11249 (by simp only [List.length_cons]; omega)
  have rd11252 := by
    simpa using rd11250.push1 ⟨1⟩ hd11250 (by simp only [List.length_cons]; omega)
  have rd11254 := by
    simpa using rd11252.push1 ⟨1⟩ hd11252 (by simp only [List.length_cons]; omega)
  have rd11256 := by
    simpa using rd11254.push1 ⟨160⟩ hd11254 (by simp only [List.length_cons]; omega)
  have rd11257 := by
    simpa using rd11256.shl hd11256 (by simp only [List.length_cons]; omega)
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have rd11258 := by
    simpa [hmask] using rd11257.sub hd11257 (by simp only [List.length_cons]; omega)
  have rd11291 := by
    simpa using rd11258.pushConst (EVM.Word.ofNat v.original.toNat)
      (by native_decide : Operation.POp.PUSH32 ≠ .PUSH0) hd11258
      (by simp only [List.length_cons]; omega)
  have rd11292 := by
    simpa using rd11291.and hd11291 (by simp only [List.length_cons]; omega)
  have rd11293 := by
    simpa [uniswapV3PoolNoDelegateCallGuard] using rd11292.eq hd11292
      (by simp only [List.length_cons]; omega)
  have rd11296 := by
    simpa using rd11293.push2 ⟨11301⟩ hd11293 (by simp only [List.length_cons]; omega)
  have rd11301 := rd11296.jumpiT hd11296 hguard
    (uniswapV3PoolJumpDestPatched11301 hpatch) (by simp only [List.length_cons]; omega)
  have rd11302 := by
    simpa using rd11301.jumpdest hd11301 (by evm_ov)
  exact ⟨_, _, rd11302.jump hd11302 htarget (by omega)⟩

theorem uniswapV3PoolNoDelegateCallOk
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨5486⟩ R mem aw rdata acc k C)
    (hguard : uniswapV3PoolNoDelegateCallGuard v ee ≠ ⟨0⟩)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨5493⟩ R mem aw rdata acc k' C' := by
  obtain ⟨_, _, rd11248⟩ :=
    uniswapV3PoolNoDelegateCallJumpInOk (v := v) (code := code) (ee := ee) (g := g)
      (s0 := s0) (R := R) (mem := mem) (aw := aw) (rdata := rdata) (acc := acc)
      hpatch h (by omega)
  have hd11248 : decode code ⟨11248⟩ = some (.JUMPDEST, .none) := by
    exact uniswapV3PoolNoDelegateCallDecodeNoArg (byte := 0x5b) (op := .JUMPDEST)
      hpatch (Or.inr (Or.inl ⟨by native_decide, by native_decide⟩))
      (by native_decide) (by native_decide) (by native_decide)
  have hd11249 : decode code ⟨11249⟩ = some (.ADDRESS, .none) := by
    exact uniswapV3PoolNoDelegateCallDecodeNoArg (byte := 0x30) (op := .ADDRESS)
      hpatch (Or.inr (Or.inl ⟨by native_decide, by native_decide⟩))
      (by native_decide) (by native_decide) (by native_decide)
  have hd11250 : decode code ⟨11250⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    refine uniswapV3PoolNoDelegateCallDecodePatchedPush1 hpatch (by native_decide)
      ?_ (by native_decide) (by native_decide)
    exact uniswapV3PoolNoDelegateCallPatchDisjointWidth (n := 2)
      (Or.inr (Or.inl ⟨by native_decide, by native_decide⟩))
  have hd11252 : decode code ⟨11252⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    refine uniswapV3PoolNoDelegateCallDecodePatchedPush1 hpatch (by native_decide)
      ?_ (by native_decide) (by native_decide)
    exact uniswapV3PoolNoDelegateCallPatchDisjointWidth (n := 2)
      (Or.inr (Or.inl ⟨by native_decide, by native_decide⟩))
  have hd11254 : decode code ⟨11254⟩ = some (.Push .PUSH1, some (⟨160⟩, 1)) := by
    refine uniswapV3PoolNoDelegateCallDecodePatchedPush1 hpatch (by native_decide)
      ?_ (by native_decide) (by native_decide)
    exact uniswapV3PoolNoDelegateCallPatchDisjointWidth (n := 2)
      (Or.inr (Or.inl ⟨by native_decide, by native_decide⟩))
  have hd11256 : decode code ⟨11256⟩ = some (.SHL, .none) := by
    exact uniswapV3PoolNoDelegateCallDecodeNoArg (byte := 0x1b) (op := .SHL)
      hpatch (Or.inr (Or.inl ⟨by native_decide, by native_decide⟩))
      (by native_decide) (by native_decide) (by native_decide)
  have hd11257 : decode code ⟨11257⟩ = some (.SUB, .none) := by
    exact uniswapV3PoolNoDelegateCallDecodeNoArg (byte := 0x03) (op := .SUB)
      hpatch (Or.inr (Or.inl ⟨by native_decide, by native_decide⟩))
      (by native_decide) (by native_decide) (by native_decide)
  have hd11258 : decode code ⟨11258⟩ =
      some (.Push .PUSH32, some (EVM.Word.ofNat v.original.toNat, 32)) :=
    uniswapV3PoolOriginalConstDecode hpatch
  have hd11291 : decode code ⟨11291⟩ = some (.AND, .none) := by
    exact uniswapV3PoolNoDelegateCallDecodeNoArg (byte := 0x16) (op := .AND)
      hpatch (Or.inr (Or.inr ⟨by native_decide, by native_decide⟩))
      (by native_decide) (by native_decide) (by native_decide)
  have hd11292 : decode code ⟨11292⟩ = some (.EQ, .none) := by
    exact uniswapV3PoolNoDelegateCallDecodeNoArg (byte := 0x14) (op := .EQ)
      hpatch (Or.inr (Or.inr ⟨by native_decide, by native_decide⟩))
      (by native_decide) (by native_decide) (by native_decide)
  have hd11293 : decode code ⟨11293⟩ = some (.Push .PUSH2, some (⟨11301⟩, 2)) := by
    refine uniswapV3PoolNoDelegateCallDecodePatchedPush2 hpatch (by native_decide)
      ?_ (by native_decide) (by native_decide)
    exact uniswapV3PoolNoDelegateCallPatchDisjointWidth (n := 3)
      (Or.inr (Or.inr ⟨by native_decide, by native_decide⟩))
  have hd11296 : decode code ⟨11296⟩ = some (.JUMPI, .none) := by
    exact uniswapV3PoolNoDelegateCallDecodeNoArg (byte := 0x57) (op := .JUMPI)
      hpatch (Or.inr (Or.inr ⟨by native_decide, by native_decide⟩))
      (by native_decide) (by native_decide) (by native_decide)
  have hd11301 : decode code ⟨11301⟩ = some (.JUMPDEST, .none) := by
    exact uniswapV3PoolNoDelegateCallDecodeNoArg (byte := 0x5b) (op := .JUMPDEST)
      hpatch (Or.inr (Or.inr ⟨by native_decide, by native_decide⟩))
      (by native_decide) (by native_decide) (by native_decide)
  have hd11302 : decode code ⟨11302⟩ = some (.JUMP, .none) := by
    exact uniswapV3PoolNoDelegateCallDecodeNoArg (byte := 0x56) (op := .JUMP)
      hpatch (Or.inr (Or.inr ⟨by native_decide, by native_decide⟩))
      (by native_decide) (by native_decide) (by native_decide)
  have rd11249 := by
    simpa using rd11248.jumpdest hd11248 (by evm_ov)
  have rd11250 := by
    simpa using rd11249.uniswapAddress hd11249 (by simp only [List.length_cons]; omega)
  have rd11252 := by
    simpa using rd11250.push1 ⟨1⟩ hd11250 (by simp only [List.length_cons]; omega)
  have rd11254 := by
    simpa using rd11252.push1 ⟨1⟩ hd11252 (by simp only [List.length_cons]; omega)
  have rd11256 := by
    simpa using rd11254.push1 ⟨160⟩ hd11254 (by simp only [List.length_cons]; omega)
  have rd11257 := by
    simpa using rd11256.shl hd11256 (by simp only [List.length_cons]; omega)
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have rd11258 := by
    simpa [hmask] using rd11257.sub hd11257 (by simp only [List.length_cons]; omega)
  have rd11291 := by
    simpa using rd11258.pushConst (EVM.Word.ofNat v.original.toNat)
      (by native_decide : Operation.POp.PUSH32 ≠ .PUSH0) hd11258
      (by simp only [List.length_cons]; omega)
  have rd11292 := by
    simpa using rd11291.and hd11291 (by simp only [List.length_cons]; omega)
  have rd11293 := by
    simpa [uniswapV3PoolNoDelegateCallGuard] using rd11292.eq hd11292
      (by simp only [List.length_cons]; omega)
  have rd11296 := by
    simpa using rd11293.push2 ⟨11301⟩ hd11293 (by simp only [List.length_cons]; omega)
  have rd11301 := rd11296.jumpiT hd11296 hguard
    (uniswapV3PoolJumpDestPatched11301 hpatch) (by simp only [List.length_cons]; omega)
  have rd11302 := by
    simpa using rd11301.jumpdest hd11301 (by evm_ov)
  exact ⟨_, _, rd11302.jump hd11302 (uniswapV3PoolJumpDestPatched5493 hpatch)
    (by omega)⟩

theorem uniswapV3PoolNoDelegateCallReturnRevert
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {R : List UInt256} {mem : ByteArray} {aw ret : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨11248⟩ (ret :: R) mem aw rdata acc k C)
    (hguard : uniswapV3PoolNoDelegateCallGuard v ee = ⟨0⟩)
    (hov : R.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  let rd11248 := h
  have hd11248 : decode code ⟨11248⟩ = some (.JUMPDEST, .none) := by
    exact uniswapV3PoolNoDelegateCallDecodeNoArg (byte := 0x5b) (op := .JUMPDEST)
      hpatch (Or.inr (Or.inl ⟨by native_decide, by native_decide⟩))
      (by native_decide) (by native_decide) (by native_decide)
  have hd11249 : decode code ⟨11249⟩ = some (.ADDRESS, .none) := by
    exact uniswapV3PoolNoDelegateCallDecodeNoArg (byte := 0x30) (op := .ADDRESS)
      hpatch (Or.inr (Or.inl ⟨by native_decide, by native_decide⟩))
      (by native_decide) (by native_decide) (by native_decide)
  have hd11250 : decode code ⟨11250⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    refine uniswapV3PoolNoDelegateCallDecodePatchedPush1 hpatch (by native_decide)
      ?_ (by native_decide) (by native_decide)
    exact uniswapV3PoolNoDelegateCallPatchDisjointWidth (n := 2)
      (Or.inr (Or.inl ⟨by native_decide, by native_decide⟩))
  have hd11252 : decode code ⟨11252⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    refine uniswapV3PoolNoDelegateCallDecodePatchedPush1 hpatch (by native_decide)
      ?_ (by native_decide) (by native_decide)
    exact uniswapV3PoolNoDelegateCallPatchDisjointWidth (n := 2)
      (Or.inr (Or.inl ⟨by native_decide, by native_decide⟩))
  have hd11254 : decode code ⟨11254⟩ = some (.Push .PUSH1, some (⟨160⟩, 1)) := by
    refine uniswapV3PoolNoDelegateCallDecodePatchedPush1 hpatch (by native_decide)
      ?_ (by native_decide) (by native_decide)
    exact uniswapV3PoolNoDelegateCallPatchDisjointWidth (n := 2)
      (Or.inr (Or.inl ⟨by native_decide, by native_decide⟩))
  have hd11256 : decode code ⟨11256⟩ = some (.SHL, .none) := by
    exact uniswapV3PoolNoDelegateCallDecodeNoArg (byte := 0x1b) (op := .SHL)
      hpatch (Or.inr (Or.inl ⟨by native_decide, by native_decide⟩))
      (by native_decide) (by native_decide) (by native_decide)
  have hd11257 : decode code ⟨11257⟩ = some (.SUB, .none) := by
    exact uniswapV3PoolNoDelegateCallDecodeNoArg (byte := 0x03) (op := .SUB)
      hpatch (Or.inr (Or.inl ⟨by native_decide, by native_decide⟩))
      (by native_decide) (by native_decide) (by native_decide)
  have hd11258 : decode code ⟨11258⟩ =
      some (.Push .PUSH32, some (EVM.Word.ofNat v.original.toNat, 32)) :=
    uniswapV3PoolOriginalConstDecode hpatch
  have hd11291 : decode code ⟨11291⟩ = some (.AND, .none) := by
    exact uniswapV3PoolNoDelegateCallDecodeNoArg (byte := 0x16) (op := .AND)
      hpatch (Or.inr (Or.inr ⟨by native_decide, by native_decide⟩))
      (by native_decide) (by native_decide) (by native_decide)
  have hd11292 : decode code ⟨11292⟩ = some (.EQ, .none) := by
    exact uniswapV3PoolNoDelegateCallDecodeNoArg (byte := 0x14) (op := .EQ)
      hpatch (Or.inr (Or.inr ⟨by native_decide, by native_decide⟩))
      (by native_decide) (by native_decide) (by native_decide)
  have hd11293 : decode code ⟨11293⟩ = some (.Push .PUSH2, some (⟨11301⟩, 2)) := by
    refine uniswapV3PoolNoDelegateCallDecodePatchedPush2 hpatch (by native_decide)
      ?_ (by native_decide) (by native_decide)
    exact uniswapV3PoolNoDelegateCallPatchDisjointWidth (n := 3)
      (Or.inr (Or.inr ⟨by native_decide, by native_decide⟩))
  have hd11296 : decode code ⟨11296⟩ = some (.JUMPI, .none) := by
    exact uniswapV3PoolNoDelegateCallDecodeNoArg (byte := 0x57) (op := .JUMPI)
      hpatch (Or.inr (Or.inr ⟨by native_decide, by native_decide⟩))
      (by native_decide) (by native_decide) (by native_decide)
  have hd11297 : decode code ⟨11297⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    refine uniswapV3PoolNoDelegateCallDecodePatchedPush1 hpatch (by native_decide)
      ?_ (by native_decide) (by native_decide)
    exact uniswapV3PoolNoDelegateCallPatchDisjointWidth (n := 2)
      (Or.inr (Or.inr ⟨by native_decide, by native_decide⟩))
  have hd11299 : decode code ⟨11299⟩ = some (.DUP1, .none) := by
    exact uniswapV3PoolNoDelegateCallDecodeNoArg (byte := 0x80) (op := .DUP1)
      hpatch (Or.inr (Or.inr ⟨by native_decide, by native_decide⟩))
      (by native_decide) (by native_decide) (by native_decide)
  have hd11300 : decode code ⟨11300⟩ = some (.REVERT, .none) := by
    exact uniswapV3PoolNoDelegateCallDecodeNoArg (byte := 0xfd) (op := .REVERT)
      hpatch (Or.inr (Or.inr ⟨by native_decide, by native_decide⟩))
      (by native_decide) (by native_decide) (by native_decide)
  have rd11249 := by
    simpa using rd11248.jumpdest hd11248 (by evm_ov)
  have rd11250 := by
    simpa using rd11249.uniswapAddress hd11249 (by simp only [List.length_cons]; omega)
  have rd11252 := by
    simpa using rd11250.push1 ⟨1⟩ hd11250 (by simp only [List.length_cons]; omega)
  have rd11254 := by
    simpa using rd11252.push1 ⟨1⟩ hd11252 (by simp only [List.length_cons]; omega)
  have rd11256 := by
    simpa using rd11254.push1 ⟨160⟩ hd11254 (by simp only [List.length_cons]; omega)
  have rd11257 := by
    simpa using rd11256.shl hd11256 (by simp only [List.length_cons]; omega)
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have rd11258 := by
    simpa [hmask] using rd11257.sub hd11257 (by simp only [List.length_cons]; omega)
  have rd11291 := by
    simpa using rd11258.pushConst (EVM.Word.ofNat v.original.toNat)
      (by native_decide : Operation.POp.PUSH32 ≠ .PUSH0) hd11258
      (by simp only [List.length_cons]; omega)
  have rd11292 := by
    simpa using rd11291.and hd11291 (by simp only [List.length_cons]; omega)
  have rd11293 := by
    simpa [uniswapV3PoolNoDelegateCallGuard] using rd11292.eq hd11292
      (by simp only [List.length_cons]; omega)
  have rd11296 := by
    simpa using rd11293.push2 ⟨11301⟩ hd11293 (by simp only [List.length_cons]; omega)
  have rd11297 := rd11296.jumpiNT hd11296 hguard (by simp only [List.length_cons]; omega)
  exact RD.uniswapPush1Dup1Revert0 rd11297 hd11297 hd11299 hd11300
    (by simp only [List.length_cons]; omega)

theorem uniswapV3PoolNoDelegateCallRevert
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨5486⟩ R mem aw rdata acc k C)
    (hguard : uniswapV3PoolNoDelegateCallGuard v ee = ⟨0⟩)
    (hov : R.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  obtain ⟨_, _, rd11248⟩ :=
    uniswapV3PoolNoDelegateCallJumpInOk (v := v) (code := code) (ee := ee) (g := g)
      (s0 := s0) (R := R) (mem := mem) (aw := aw) (rdata := rdata) (acc := acc)
      hpatch h (by omega)
  exact uniswapV3PoolNoDelegateCallReturnRevert (v := v) (code := code) (ee := ee) (g := g)
    (s0 := s0) (ret := ⟨5493⟩) (R := R) (mem := mem) (aw := aw) (rdata := rdata)
    (acc := acc) hpatch rd11248 hguard (by omega)

theorem uniswapV3PoolNoDelegateCallOriginalClean (a : AccountAddress) :
    UInt256.land (EVM.Word.ofNat a.toNat) solcAddrMask = EVM.Word.ofNat a.toNat := by
  apply solcAddrMask_clean
  rw [accountAddressWord_toNat]
  simp [EVM.addressModulus, EVM.twoPow, AccountAddress.size]

theorem uniswapV3PoolAccountAddressOfNatToNat (a : AccountAddress) :
    AccountAddress.ofNat a.toNat = a := by
  ext
  simp [AccountAddress.ofNat]

theorem uniswapV3PoolNoDelegateCallGuard_word_eq_address_eq
    {v : PoolImmutables} {I : ExecutionEnv}
    (hword : UInt256.land (EVM.Word.ofNat v.original.toNat) solcAddrMask =
      UInt256.ofNat I.codeOwner.val) :
    I.codeOwner = v.original := by
  have hclean := uniswapV3PoolNoDelegateCallOriginalClean v.original
  have hword' : EVM.Word.ofNat v.original.toNat = UInt256.ofNat I.codeOwner.val := by
    rwa [hclean] at hword
  have hnat := congrArg UInt256.toNat hword'
  have horig := accountAddressWord_toNat v.original
  have hthis := accountAddressWord_toNat I.codeOwner
  rw [horig] at hnat
  change v.original.val = (UInt256.ofNat I.codeOwner.val).toNat at hnat
  rw [show (UInt256.ofNat I.codeOwner.val).toNat = I.codeOwner.val from by
    simpa [EVM.Word.ofNat] using hthis] at hnat
  ext
  exact hnat.symm

theorem uniswapV3PoolNoDelegateCallGuard_eq_zero_of_codeOwner_ne
    {v : PoolImmutables} {I : ExecutionEnv}
    (hne : I.codeOwner ≠ v.original) :
    uniswapV3PoolNoDelegateCallGuard v I = ⟨0⟩ := by
  unfold uniswapV3PoolNoDelegateCallGuard
  apply u256_eq_of_ne
  intro hword
  exact hne (uniswapV3PoolNoDelegateCallGuard_word_eq_address_eq hword)

theorem uniswapV3PoolNoDelegateCallGuard_eq_one_of_codeOwner_eq
    {v : PoolImmutables} {I : ExecutionEnv}
    (heq : I.codeOwner = v.original) :
    uniswapV3PoolNoDelegateCallGuard v I = ⟨1⟩ := by
  rw [uniswapV3PoolNoDelegateCallGuard]
  rw [uniswapV3PoolNoDelegateCallOriginalClean]
  rw [heq]
  simpa [EVM.Word.ofNat] using uInt256_eq_self (UInt256.ofNat v.original.val)

theorem uniswapV3PoolAddrLitEvalFrame {v : PoolImmutables}
    {cA gh bl σ σ₀ A I L} {g : Sat256} (a : EVM.Address) :
    evalExpr? (config v) { contract := contract v, locals := L }
      (initState cA gh bl σ σ₀ g A I) (addrLit a) =
      .ok (Value.address (AccountAddress.ofNat a.toNat)) := by
  dsimp [addrLit]
  have hint :
      evalExpr? (config v) { contract := contract v, locals := L }
        (initState cA gh bl σ σ₀ g A I) (.intLit (↑↑a)) =
        .ok (.int (↑↑a)) := by
    simp [evalExpr?, pure]
  unfold evalExpr?
  rw [hint]
  change (if (↑↑a : Int) < 0 then EvalResult.error EvalError.typeError
      else EvalResult.ok
        (Value.address (AccountAddress.ofNat (Int.toNat (↑↑a : Int))))) =
    EvalResult.ok (Value.address (AccountAddress.ofNat ↑a))
  rw [if_neg (by omega)]
  simp

theorem uniswapV3PoolNoDelegateCallEvalTrue
    {v : PoolImmutables} {cA gh bl σ σ₀ A I L} {g : Sat256}
    (hguard : uniswapV3PoolNoDelegateCallGuard v I ≠ ⟨0⟩) :
    evalExpr? (config v) { contract := contract v, locals := L }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .eq (.env .this) (addrLit v.original)) = .ok (.bool true) := by
  have haddr : I.codeOwner = v.original := by
    by_contra hne
    exact hguard (uniswapV3PoolNoDelegateCallGuard_eq_zero_of_codeOwner_ne hne)
  have hofNat := uniswapV3PoolAccountAddressOfNatToNat v.original
  have hbeq :
      (Value.address I.codeOwner == Value.address (AccountAddress.ofNat v.original.toNat)) =
        true := by
    rw [beq_iff_eq]
    rw [hofNat, haddr]
  have hthis :
      evalExpr? (config v) { contract := contract v, locals := L }
        (initState cA gh bl σ σ₀ g A I) (.env .this) =
        .ok (Value.address I.codeOwner) := by
    simp [evalExpr?, envValue, initState, pure]
  have horig := uniswapV3PoolAddrLitEvalFrame (v := v) (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (L := L) (g := g)
    v.original
  unfold evalExpr?
  rw [hthis, horig]
  simp [EvalResult.bind, bind, evalBinaryOp?, haddr]
  exact hofNat.symm

theorem uniswapV3PoolNoDelegateCallEvalFalse
    {v : PoolImmutables} {cA gh bl σ σ₀ A I L} {g : Sat256}
    (hguard : uniswapV3PoolNoDelegateCallGuard v I = ⟨0⟩) :
    evalExpr? (config v) { contract := contract v, locals := L }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .eq (.env .this) (addrLit v.original)) = .ok (.bool false) := by
  have hne : I.codeOwner ≠ v.original := by
    intro haddr
    have hone := uniswapV3PoolNoDelegateCallGuard_eq_one_of_codeOwner_eq
      (v := v) (I := I) haddr
    exact (by native_decide : (⟨0⟩ : UInt256) ≠ ⟨1⟩) (by simpa [hguard] using hone)
  have hofNat := uniswapV3PoolAccountAddressOfNatToNat v.original
  have hneValue :
      Value.address I.codeOwner ≠ Value.address (AccountAddress.ofNat v.original.toNat) := by
    intro hval
    rw [hofNat] at hval
    injection hval with haddr
    exact hne haddr
  have hbeq :
      (Value.address I.codeOwner == Value.address (AccountAddress.ofNat v.original.toNat)) =
        false := by
    rw [beq_eq_false_iff_ne]
    exact hneValue
  have hthis :
      evalExpr? (config v) { contract := contract v, locals := L }
        (initState cA gh bl σ σ₀ g A I) (.env .this) =
        .ok (Value.address I.codeOwner) := by
    simp [evalExpr?, envValue, initState, pure]
  have horig := uniswapV3PoolAddrLitEvalFrame (v := v) (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (L := L) (g := g)
    v.original
  unfold evalExpr?
  rw [hthis, horig]
  simp [EvalResult.bind, bind, evalBinaryOp?]
  intro h
  exact hne (h.trans hofNat)

end Benchmarks.UniswapV3Pool
