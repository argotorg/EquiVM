import Examples.Ripemd160Old.HashLeftRound0

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

namespace Ripemd160Old

open Ripemd160

theorem runtime_leftRoundHelper_10 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 10 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 0 10).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 0 10).aw
      rdata (cA, σ) k' C' := by
  simp only [oldLeftHelperStack] at rd
  have rd1 := evm_run_rfl rd with [jumpdest, push1 ⟨32⟩, swap2, push2 ⟨526⟩, push1 ⟨10⟩, push4 ⟨4294967295⟩, swap3, dup5]
  have rd2 := RD.runtimeMload rd1 (by old_decode) (by simp; omega)
  have rd3 := evm_run_rfl rd2 with [swap1, dup7, dup7, add]
  have rd4 := RD.runtimeMload rd3 (by old_decode) (by simp; omega)
  have rd5 := evm_run_rfl rd4 with [swap5, push1 ⟨64⟩, dup8, add]
  have rd6 := RD.runtimeMload rd5 (by old_decode) (by simp; omega)
  have rd7 := evm_run_rfl rd6 with [swap3, push2 ⟨511⟩, push1 ⟨96⟩, dup10, add]
  have rd8 := RD.runtimeMload rd7 (by old_decode) (by simp; omega)
  have rd9 := evm_run_rfl rd8 with [swap4, dup4, dup10, push1 ⟨128⟩, dup13, add]
  have rd10 := RD.runtimeMload rd9 (by old_decode) (by simp; omega)
  have rd11 := evm_run_rfl rd10 with [swap14, dup15, swap6, dup4, push1 ⟨16⟩, dup4, div, swap6, push0, swap4, dup13, dup13, push0, swap8, dup11, swap3, dup4, push0, eq, push2 ⟨4108⟩, jumpiT (by native_decide) jump_4108]
  have rd12 := evm_run_rfl rd11 with [jumpdest, swap4, swap9, pop, swap2, pop, swap3, swap6, pop, xor, xor, swap3, push0, swap5, push2 ⟨391⟩, jump jump_391]
  have rd13 := evm_run_rfl rd12 with [jumpdest, push0, swap1, push1 ⟨16⟩, dup2, lt, push2 ⟨4001⟩, jumpiT (by native_decide) jump_4001]
  have rd14 := evm_run_rfl rd13 with [jumpdest, dup1, swap2, pop, swap1, push2 ⟨402⟩, jump jump_402]
  have rd15 := evm_run_rfl rd14 with [jumpdest, push1 ⟨32⟩, dup2, lt, push1 ⟨15⟩, dup3, gt, and, push2 ⟨3693⟩, jumpiNT (by native_decide)]
  have rd16 := evm_run_rfl rd15 with [jumpdest, push1 ⟨48⟩, dup2, lt, push1 ⟨31⟩, dup3, gt, and, push2 ⟨3385⟩, jumpiNT (by native_decide)]
  have rd17 := evm_run_rfl rd16 with [jumpdest, push1 ⟨64⟩, dup2, lt, push1 ⟨47⟩, dup3, gt, and, push2 ⟨3077⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [jumpdest, push1 ⟨63⟩, dup2, gt, push2 ⟨2769⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiT (by native_decide) jump_2323]
  have rd20 := evm_run_rfl rd19 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨2750⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [dup1, push1 ⟨1⟩, eq, push2 ⟨2731⟩, jumpiNT (by native_decide)]
  have rd22 := evm_run_rfl rd21 with [dup1, push1 ⟨2⟩, eq, push2 ⟨2712⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨3⟩, eq, push2 ⟨2693⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup1, push1 ⟨4⟩, eq, push2 ⟨2674⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨5⟩, eq, push2 ⟨2655⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup1, push1 ⟨6⟩, eq, push2 ⟨2636⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨7⟩, eq, push2 ⟨2617⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨8⟩, eq, push2 ⟨2598⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [dup1, push1 ⟨9⟩, eq, push2 ⟨2579⟩, jumpiNT (by native_decide)]
  have rd30 := evm_run_rfl rd29 with [dup1, dup15, eq, push2 ⟨2560⟩, jumpiT (by native_decide) jump_2560]
  have rd31 := evm_run_rfl rd30 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨14⟩, swap8, swap2, swap3, pop, pop, push2 ⟨2457⟩, jump jump_2457]
  have rd32 := evm_run_rfl rd31 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨494⟩, jump jump_494]
  have rd33 := evm_run_rfl rd32 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd34 := RD.runtimeMload rd33 (by old_decode) (by simp; omega)
  have rd35 := evm_run_rfl rd34 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd36 := evm_run_rfl rd35 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_511]
  have rd37 := evm_run_rfl rd36 with [jumpdest, add, and, swap8, dup7]
  have rd38 := RD.runtimeMstore rd37 (by old_decode) (by simp; omega)
  have rd39 := evm_run_rfl rd38 with [push1 ⟨128⟩, dup7, add]
  have rd40 := RD.runtimeMstore rd39 (by old_decode) (by simp; omega)
  have rd41 := evm_run_rfl rd40 with [push2 ⟨268⟩, jump jump_268]
  have rd42 := evm_run_rfl rd41 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_526]
  have rd43 := evm_run_rfl rd42 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd44 := RD.runtimeMstore rd43 (by old_decode) (by simp; omega)
  have rd45 := evm_run_rfl rd44 with [push1 ⟨64⟩, dup3, add]
  have rd46 := RD.runtimeMstore rd45 (by old_decode) (by simp; omega)
  have rd47 := evm_run_rfl rd46 with [add]
  have rd48 := RD.runtimeMstore rd47 (by old_decode) (by simp; omega)
  have rd49 := evm_run_rfl rd48 with [jump jump_8991]
  exact ⟨_, _, by
    simpa [oldLeftHelperStack, oldLeftRoundCursor, runtimeRoundPreludeCursor,
      runtimePreludeB, runtimePreludeC, runtimePreludeD, runtimeRightPreludeCursor,
      runtimeRightPreludeB, runtimeRightPreludeC, runtimeRightPreludeD,
      runtimeRoundCursor, runtimeRoundNext, runtimeRoundSum, runtimeRol32,
      runtimeRoundX, runtimeRoundAwX, runtimeRoundMessageAddr, runtimeRowEntry,
      runtimeRoundA, runtimeRoundAwA, runtimeRoundB, runtimeRoundAwB,
      runtimeRoundC, runtimeRoundAwC, runtimeRoundD, runtimeRoundAwD,
      runtimeRoundE, runtimeRoundAwE, runtimeStoreCursor, runtimeLeftF,
      runtimeRightF, leftWordRowWord, leftRotationRowWord, leftConstantWord,
      rightWordRowWord, rightRotationRowWord, rightConstantWord, mask32Word,
      Model.leftWordRow, Model.leftRotationRow, Model.leftConstant,
      Model.rightWordRow, Model.rightRotationRow, Model.rightConstant,
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd49⟩

theorem runtime_leftRoundHelper_11 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 11 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 0 11).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 0 11).aw
      rdata (cA, σ) k' C' := by
  simp only [oldLeftHelperStack] at rd
  have rd1 := evm_run_rfl rd with [jumpdest, push1 ⟨32⟩, swap2, push2 ⟨526⟩, push1 ⟨10⟩, push4 ⟨4294967295⟩, swap3, dup5]
  have rd2 := RD.runtimeMload rd1 (by old_decode) (by simp; omega)
  have rd3 := evm_run_rfl rd2 with [swap1, dup7, dup7, add]
  have rd4 := RD.runtimeMload rd3 (by old_decode) (by simp; omega)
  have rd5 := evm_run_rfl rd4 with [swap5, push1 ⟨64⟩, dup8, add]
  have rd6 := RD.runtimeMload rd5 (by old_decode) (by simp; omega)
  have rd7 := evm_run_rfl rd6 with [swap3, push2 ⟨511⟩, push1 ⟨96⟩, dup10, add]
  have rd8 := RD.runtimeMload rd7 (by old_decode) (by simp; omega)
  have rd9 := evm_run_rfl rd8 with [swap4, dup4, dup10, push1 ⟨128⟩, dup13, add]
  have rd10 := RD.runtimeMload rd9 (by old_decode) (by simp; omega)
  have rd11 := evm_run_rfl rd10 with [swap14, dup15, swap6, dup4, push1 ⟨16⟩, dup4, div, swap6, push0, swap4, dup13, dup13, push0, swap8, dup11, swap3, dup4, push0, eq, push2 ⟨4108⟩, jumpiT (by native_decide) jump_4108]
  have rd12 := evm_run_rfl rd11 with [jumpdest, swap4, swap9, pop, swap2, pop, swap3, swap6, pop, xor, xor, swap3, push0, swap5, push2 ⟨391⟩, jump jump_391]
  have rd13 := evm_run_rfl rd12 with [jumpdest, push0, swap1, push1 ⟨16⟩, dup2, lt, push2 ⟨4001⟩, jumpiT (by native_decide) jump_4001]
  have rd14 := evm_run_rfl rd13 with [jumpdest, dup1, swap2, pop, swap1, push2 ⟨402⟩, jump jump_402]
  have rd15 := evm_run_rfl rd14 with [jumpdest, push1 ⟨32⟩, dup2, lt, push1 ⟨15⟩, dup3, gt, and, push2 ⟨3693⟩, jumpiNT (by native_decide)]
  have rd16 := evm_run_rfl rd15 with [jumpdest, push1 ⟨48⟩, dup2, lt, push1 ⟨31⟩, dup3, gt, and, push2 ⟨3385⟩, jumpiNT (by native_decide)]
  have rd17 := evm_run_rfl rd16 with [jumpdest, push1 ⟨64⟩, dup2, lt, push1 ⟨47⟩, dup3, gt, and, push2 ⟨3077⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [jumpdest, push1 ⟨63⟩, dup2, gt, push2 ⟨2769⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiT (by native_decide) jump_2323]
  have rd20 := evm_run_rfl rd19 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨2750⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [dup1, push1 ⟨1⟩, eq, push2 ⟨2731⟩, jumpiNT (by native_decide)]
  have rd22 := evm_run_rfl rd21 with [dup1, push1 ⟨2⟩, eq, push2 ⟨2712⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨3⟩, eq, push2 ⟨2693⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup1, push1 ⟨4⟩, eq, push2 ⟨2674⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨5⟩, eq, push2 ⟨2655⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup1, push1 ⟨6⟩, eq, push2 ⟨2636⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨7⟩, eq, push2 ⟨2617⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨8⟩, eq, push2 ⟨2598⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [dup1, push1 ⟨9⟩, eq, push2 ⟨2579⟩, jumpiNT (by native_decide)]
  have rd30 := evm_run_rfl rd29 with [dup1, dup15, eq, push2 ⟨2560⟩, jumpiNT (by native_decide)]
  have rd31 := evm_run_rfl rd30 with [dup1, push1 ⟨11⟩, eq, push2 ⟨2541⟩, jumpiT (by native_decide) jump_2541]
  have rd32 := evm_run_rfl rd31 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨15⟩, swap8, swap2, swap3, pop, pop, push2 ⟨2457⟩, jump jump_2457]
  have rd33 := evm_run_rfl rd32 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨494⟩, jump jump_494]
  have rd34 := evm_run_rfl rd33 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd35 := RD.runtimeMload rd34 (by old_decode) (by simp; omega)
  have rd36 := evm_run_rfl rd35 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd37 := evm_run_rfl rd36 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_511]
  have rd38 := evm_run_rfl rd37 with [jumpdest, add, and, swap8, dup7]
  have rd39 := RD.runtimeMstore rd38 (by old_decode) (by simp; omega)
  have rd40 := evm_run_rfl rd39 with [push1 ⟨128⟩, dup7, add]
  have rd41 := RD.runtimeMstore rd40 (by old_decode) (by simp; omega)
  have rd42 := evm_run_rfl rd41 with [push2 ⟨268⟩, jump jump_268]
  have rd43 := evm_run_rfl rd42 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_526]
  have rd44 := evm_run_rfl rd43 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd45 := RD.runtimeMstore rd44 (by old_decode) (by simp; omega)
  have rd46 := evm_run_rfl rd45 with [push1 ⟨64⟩, dup3, add]
  have rd47 := RD.runtimeMstore rd46 (by old_decode) (by simp; omega)
  have rd48 := evm_run_rfl rd47 with [add]
  have rd49 := RD.runtimeMstore rd48 (by old_decode) (by simp; omega)
  have rd50 := evm_run_rfl rd49 with [jump jump_8991]
  exact ⟨_, _, by
    simpa [oldLeftHelperStack, oldLeftRoundCursor, runtimeRoundPreludeCursor,
      runtimePreludeB, runtimePreludeC, runtimePreludeD, runtimeRightPreludeCursor,
      runtimeRightPreludeB, runtimeRightPreludeC, runtimeRightPreludeD,
      runtimeRoundCursor, runtimeRoundNext, runtimeRoundSum, runtimeRol32,
      runtimeRoundX, runtimeRoundAwX, runtimeRoundMessageAddr, runtimeRowEntry,
      runtimeRoundA, runtimeRoundAwA, runtimeRoundB, runtimeRoundAwB,
      runtimeRoundC, runtimeRoundAwC, runtimeRoundD, runtimeRoundAwD,
      runtimeRoundE, runtimeRoundAwE, runtimeStoreCursor, runtimeLeftF,
      runtimeRightF, leftWordRowWord, leftRotationRowWord, leftConstantWord,
      rightWordRowWord, rightRotationRowWord, rightConstantWord, mask32Word,
      Model.leftWordRow, Model.leftRotationRow, Model.leftConstant,
      Model.rightWordRow, Model.rightRotationRow, Model.rightConstant,
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd50⟩

theorem runtime_leftRoundHelper_12 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 12 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 0 12).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 0 12).aw
      rdata (cA, σ) k' C' := by
  simp only [oldLeftHelperStack] at rd
  have rd1 := evm_run_rfl rd with [jumpdest, push1 ⟨32⟩, swap2, push2 ⟨526⟩, push1 ⟨10⟩, push4 ⟨4294967295⟩, swap3, dup5]
  have rd2 := RD.runtimeMload rd1 (by old_decode) (by simp; omega)
  have rd3 := evm_run_rfl rd2 with [swap1, dup7, dup7, add]
  have rd4 := RD.runtimeMload rd3 (by old_decode) (by simp; omega)
  have rd5 := evm_run_rfl rd4 with [swap5, push1 ⟨64⟩, dup8, add]
  have rd6 := RD.runtimeMload rd5 (by old_decode) (by simp; omega)
  have rd7 := evm_run_rfl rd6 with [swap3, push2 ⟨511⟩, push1 ⟨96⟩, dup10, add]
  have rd8 := RD.runtimeMload rd7 (by old_decode) (by simp; omega)
  have rd9 := evm_run_rfl rd8 with [swap4, dup4, dup10, push1 ⟨128⟩, dup13, add]
  have rd10 := RD.runtimeMload rd9 (by old_decode) (by simp; omega)
  have rd11 := evm_run_rfl rd10 with [swap14, dup15, swap6, dup4, push1 ⟨16⟩, dup4, div, swap6, push0, swap4, dup13, dup13, push0, swap8, dup11, swap3, dup4, push0, eq, push2 ⟨4108⟩, jumpiT (by native_decide) jump_4108]
  have rd12 := evm_run_rfl rd11 with [jumpdest, swap4, swap9, pop, swap2, pop, swap3, swap6, pop, xor, xor, swap3, push0, swap5, push2 ⟨391⟩, jump jump_391]
  have rd13 := evm_run_rfl rd12 with [jumpdest, push0, swap1, push1 ⟨16⟩, dup2, lt, push2 ⟨4001⟩, jumpiT (by native_decide) jump_4001]
  have rd14 := evm_run_rfl rd13 with [jumpdest, dup1, swap2, pop, swap1, push2 ⟨402⟩, jump jump_402]
  have rd15 := evm_run_rfl rd14 with [jumpdest, push1 ⟨32⟩, dup2, lt, push1 ⟨15⟩, dup3, gt, and, push2 ⟨3693⟩, jumpiNT (by native_decide)]
  have rd16 := evm_run_rfl rd15 with [jumpdest, push1 ⟨48⟩, dup2, lt, push1 ⟨31⟩, dup3, gt, and, push2 ⟨3385⟩, jumpiNT (by native_decide)]
  have rd17 := evm_run_rfl rd16 with [jumpdest, push1 ⟨64⟩, dup2, lt, push1 ⟨47⟩, dup3, gt, and, push2 ⟨3077⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [jumpdest, push1 ⟨63⟩, dup2, gt, push2 ⟨2769⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiT (by native_decide) jump_2323]
  have rd20 := evm_run_rfl rd19 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨2750⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [dup1, push1 ⟨1⟩, eq, push2 ⟨2731⟩, jumpiNT (by native_decide)]
  have rd22 := evm_run_rfl rd21 with [dup1, push1 ⟨2⟩, eq, push2 ⟨2712⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨3⟩, eq, push2 ⟨2693⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup1, push1 ⟨4⟩, eq, push2 ⟨2674⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨5⟩, eq, push2 ⟨2655⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup1, push1 ⟨6⟩, eq, push2 ⟨2636⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨7⟩, eq, push2 ⟨2617⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨8⟩, eq, push2 ⟨2598⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [dup1, push1 ⟨9⟩, eq, push2 ⟨2579⟩, jumpiNT (by native_decide)]
  have rd30 := evm_run_rfl rd29 with [dup1, dup15, eq, push2 ⟨2560⟩, jumpiNT (by native_decide)]
  have rd31 := evm_run_rfl rd30 with [dup1, push1 ⟨11⟩, eq, push2 ⟨2541⟩, jumpiNT (by native_decide)]
  have rd32 := evm_run_rfl rd31 with [dup1, push1 ⟨12⟩, eq, push2 ⟨2522⟩, jumpiT (by native_decide) jump_2522]
  have rd33 := evm_run_rfl rd32 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨6⟩, swap8, swap2, swap3, pop, pop, push2 ⟨2457⟩, jump jump_2457]
  have rd34 := evm_run_rfl rd33 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨494⟩, jump jump_494]
  have rd35 := evm_run_rfl rd34 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd36 := RD.runtimeMload rd35 (by old_decode) (by simp; omega)
  have rd37 := evm_run_rfl rd36 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd38 := evm_run_rfl rd37 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_511]
  have rd39 := evm_run_rfl rd38 with [jumpdest, add, and, swap8, dup7]
  have rd40 := RD.runtimeMstore rd39 (by old_decode) (by simp; omega)
  have rd41 := evm_run_rfl rd40 with [push1 ⟨128⟩, dup7, add]
  have rd42 := RD.runtimeMstore rd41 (by old_decode) (by simp; omega)
  have rd43 := evm_run_rfl rd42 with [push2 ⟨268⟩, jump jump_268]
  have rd44 := evm_run_rfl rd43 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_526]
  have rd45 := evm_run_rfl rd44 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd46 := RD.runtimeMstore rd45 (by old_decode) (by simp; omega)
  have rd47 := evm_run_rfl rd46 with [push1 ⟨64⟩, dup3, add]
  have rd48 := RD.runtimeMstore rd47 (by old_decode) (by simp; omega)
  have rd49 := evm_run_rfl rd48 with [add]
  have rd50 := RD.runtimeMstore rd49 (by old_decode) (by simp; omega)
  have rd51 := evm_run_rfl rd50 with [jump jump_8991]
  exact ⟨_, _, by
    simpa [oldLeftHelperStack, oldLeftRoundCursor, runtimeRoundPreludeCursor,
      runtimePreludeB, runtimePreludeC, runtimePreludeD, runtimeRightPreludeCursor,
      runtimeRightPreludeB, runtimeRightPreludeC, runtimeRightPreludeD,
      runtimeRoundCursor, runtimeRoundNext, runtimeRoundSum, runtimeRol32,
      runtimeRoundX, runtimeRoundAwX, runtimeRoundMessageAddr, runtimeRowEntry,
      runtimeRoundA, runtimeRoundAwA, runtimeRoundB, runtimeRoundAwB,
      runtimeRoundC, runtimeRoundAwC, runtimeRoundD, runtimeRoundAwD,
      runtimeRoundE, runtimeRoundAwE, runtimeStoreCursor, runtimeLeftF,
      runtimeRightF, leftWordRowWord, leftRotationRowWord, leftConstantWord,
      rightWordRowWord, rightRotationRowWord, rightConstantWord, mask32Word,
      Model.leftWordRow, Model.leftRotationRow, Model.leftConstant,
      Model.rightWordRow, Model.rightRotationRow, Model.rightConstant,
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd51⟩

theorem runtime_leftRoundHelper_13 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 13 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 0 13).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 0 13).aw
      rdata (cA, σ) k' C' := by
  simp only [oldLeftHelperStack] at rd
  have rd1 := evm_run_rfl rd with [jumpdest, push1 ⟨32⟩, swap2, push2 ⟨526⟩, push1 ⟨10⟩, push4 ⟨4294967295⟩, swap3, dup5]
  have rd2 := RD.runtimeMload rd1 (by old_decode) (by simp; omega)
  have rd3 := evm_run_rfl rd2 with [swap1, dup7, dup7, add]
  have rd4 := RD.runtimeMload rd3 (by old_decode) (by simp; omega)
  have rd5 := evm_run_rfl rd4 with [swap5, push1 ⟨64⟩, dup8, add]
  have rd6 := RD.runtimeMload rd5 (by old_decode) (by simp; omega)
  have rd7 := evm_run_rfl rd6 with [swap3, push2 ⟨511⟩, push1 ⟨96⟩, dup10, add]
  have rd8 := RD.runtimeMload rd7 (by old_decode) (by simp; omega)
  have rd9 := evm_run_rfl rd8 with [swap4, dup4, dup10, push1 ⟨128⟩, dup13, add]
  have rd10 := RD.runtimeMload rd9 (by old_decode) (by simp; omega)
  have rd11 := evm_run_rfl rd10 with [swap14, dup15, swap6, dup4, push1 ⟨16⟩, dup4, div, swap6, push0, swap4, dup13, dup13, push0, swap8, dup11, swap3, dup4, push0, eq, push2 ⟨4108⟩, jumpiT (by native_decide) jump_4108]
  have rd12 := evm_run_rfl rd11 with [jumpdest, swap4, swap9, pop, swap2, pop, swap3, swap6, pop, xor, xor, swap3, push0, swap5, push2 ⟨391⟩, jump jump_391]
  have rd13 := evm_run_rfl rd12 with [jumpdest, push0, swap1, push1 ⟨16⟩, dup2, lt, push2 ⟨4001⟩, jumpiT (by native_decide) jump_4001]
  have rd14 := evm_run_rfl rd13 with [jumpdest, dup1, swap2, pop, swap1, push2 ⟨402⟩, jump jump_402]
  have rd15 := evm_run_rfl rd14 with [jumpdest, push1 ⟨32⟩, dup2, lt, push1 ⟨15⟩, dup3, gt, and, push2 ⟨3693⟩, jumpiNT (by native_decide)]
  have rd16 := evm_run_rfl rd15 with [jumpdest, push1 ⟨48⟩, dup2, lt, push1 ⟨31⟩, dup3, gt, and, push2 ⟨3385⟩, jumpiNT (by native_decide)]
  have rd17 := evm_run_rfl rd16 with [jumpdest, push1 ⟨64⟩, dup2, lt, push1 ⟨47⟩, dup3, gt, and, push2 ⟨3077⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [jumpdest, push1 ⟨63⟩, dup2, gt, push2 ⟨2769⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiT (by native_decide) jump_2323]
  have rd20 := evm_run_rfl rd19 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨2750⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [dup1, push1 ⟨1⟩, eq, push2 ⟨2731⟩, jumpiNT (by native_decide)]
  have rd22 := evm_run_rfl rd21 with [dup1, push1 ⟨2⟩, eq, push2 ⟨2712⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨3⟩, eq, push2 ⟨2693⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup1, push1 ⟨4⟩, eq, push2 ⟨2674⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨5⟩, eq, push2 ⟨2655⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup1, push1 ⟨6⟩, eq, push2 ⟨2636⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨7⟩, eq, push2 ⟨2617⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨8⟩, eq, push2 ⟨2598⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [dup1, push1 ⟨9⟩, eq, push2 ⟨2579⟩, jumpiNT (by native_decide)]
  have rd30 := evm_run_rfl rd29 with [dup1, dup15, eq, push2 ⟨2560⟩, jumpiNT (by native_decide)]
  have rd31 := evm_run_rfl rd30 with [dup1, push1 ⟨11⟩, eq, push2 ⟨2541⟩, jumpiNT (by native_decide)]
  have rd32 := evm_run_rfl rd31 with [dup1, push1 ⟨12⟩, eq, push2 ⟨2522⟩, jumpiNT (by native_decide)]
  have rd33 := evm_run_rfl rd32 with [dup1, push1 ⟨13⟩, eq, push2 ⟨2503⟩, jumpiT (by native_decide) jump_2503]
  have rd34 := evm_run_rfl rd33 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨7⟩, swap8, swap2, swap3, pop, pop, push2 ⟨2457⟩, jump jump_2457]
  have rd35 := evm_run_rfl rd34 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨494⟩, jump jump_494]
  have rd36 := evm_run_rfl rd35 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd37 := RD.runtimeMload rd36 (by old_decode) (by simp; omega)
  have rd38 := evm_run_rfl rd37 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd39 := evm_run_rfl rd38 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_511]
  have rd40 := evm_run_rfl rd39 with [jumpdest, add, and, swap8, dup7]
  have rd41 := RD.runtimeMstore rd40 (by old_decode) (by simp; omega)
  have rd42 := evm_run_rfl rd41 with [push1 ⟨128⟩, dup7, add]
  have rd43 := RD.runtimeMstore rd42 (by old_decode) (by simp; omega)
  have rd44 := evm_run_rfl rd43 with [push2 ⟨268⟩, jump jump_268]
  have rd45 := evm_run_rfl rd44 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_526]
  have rd46 := evm_run_rfl rd45 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd47 := RD.runtimeMstore rd46 (by old_decode) (by simp; omega)
  have rd48 := evm_run_rfl rd47 with [push1 ⟨64⟩, dup3, add]
  have rd49 := RD.runtimeMstore rd48 (by old_decode) (by simp; omega)
  have rd50 := evm_run_rfl rd49 with [add]
  have rd51 := RD.runtimeMstore rd50 (by old_decode) (by simp; omega)
  have rd52 := evm_run_rfl rd51 with [jump jump_8991]
  exact ⟨_, _, by
    simpa [oldLeftHelperStack, oldLeftRoundCursor, runtimeRoundPreludeCursor,
      runtimePreludeB, runtimePreludeC, runtimePreludeD, runtimeRightPreludeCursor,
      runtimeRightPreludeB, runtimeRightPreludeC, runtimeRightPreludeD,
      runtimeRoundCursor, runtimeRoundNext, runtimeRoundSum, runtimeRol32,
      runtimeRoundX, runtimeRoundAwX, runtimeRoundMessageAddr, runtimeRowEntry,
      runtimeRoundA, runtimeRoundAwA, runtimeRoundB, runtimeRoundAwB,
      runtimeRoundC, runtimeRoundAwC, runtimeRoundD, runtimeRoundAwD,
      runtimeRoundE, runtimeRoundAwE, runtimeStoreCursor, runtimeLeftF,
      runtimeRightF, leftWordRowWord, leftRotationRowWord, leftConstantWord,
      rightWordRowWord, rightRotationRowWord, rightConstantWord, mask32Word,
      Model.leftWordRow, Model.leftRotationRow, Model.leftConstant,
      Model.rightWordRow, Model.rightRotationRow, Model.rightConstant,
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd52⟩

theorem runtime_leftRoundHelper_14 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 14 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 0 14).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 0 14).aw
      rdata (cA, σ) k' C' := by
  simp only [oldLeftHelperStack] at rd
  have rd1 := evm_run_rfl rd with [jumpdest, push1 ⟨32⟩, swap2, push2 ⟨526⟩, push1 ⟨10⟩, push4 ⟨4294967295⟩, swap3, dup5]
  have rd2 := RD.runtimeMload rd1 (by old_decode) (by simp; omega)
  have rd3 := evm_run_rfl rd2 with [swap1, dup7, dup7, add]
  have rd4 := RD.runtimeMload rd3 (by old_decode) (by simp; omega)
  have rd5 := evm_run_rfl rd4 with [swap5, push1 ⟨64⟩, dup8, add]
  have rd6 := RD.runtimeMload rd5 (by old_decode) (by simp; omega)
  have rd7 := evm_run_rfl rd6 with [swap3, push2 ⟨511⟩, push1 ⟨96⟩, dup10, add]
  have rd8 := RD.runtimeMload rd7 (by old_decode) (by simp; omega)
  have rd9 := evm_run_rfl rd8 with [swap4, dup4, dup10, push1 ⟨128⟩, dup13, add]
  have rd10 := RD.runtimeMload rd9 (by old_decode) (by simp; omega)
  have rd11 := evm_run_rfl rd10 with [swap14, dup15, swap6, dup4, push1 ⟨16⟩, dup4, div, swap6, push0, swap4, dup13, dup13, push0, swap8, dup11, swap3, dup4, push0, eq, push2 ⟨4108⟩, jumpiT (by native_decide) jump_4108]
  have rd12 := evm_run_rfl rd11 with [jumpdest, swap4, swap9, pop, swap2, pop, swap3, swap6, pop, xor, xor, swap3, push0, swap5, push2 ⟨391⟩, jump jump_391]
  have rd13 := evm_run_rfl rd12 with [jumpdest, push0, swap1, push1 ⟨16⟩, dup2, lt, push2 ⟨4001⟩, jumpiT (by native_decide) jump_4001]
  have rd14 := evm_run_rfl rd13 with [jumpdest, dup1, swap2, pop, swap1, push2 ⟨402⟩, jump jump_402]
  have rd15 := evm_run_rfl rd14 with [jumpdest, push1 ⟨32⟩, dup2, lt, push1 ⟨15⟩, dup3, gt, and, push2 ⟨3693⟩, jumpiNT (by native_decide)]
  have rd16 := evm_run_rfl rd15 with [jumpdest, push1 ⟨48⟩, dup2, lt, push1 ⟨31⟩, dup3, gt, and, push2 ⟨3385⟩, jumpiNT (by native_decide)]
  have rd17 := evm_run_rfl rd16 with [jumpdest, push1 ⟨64⟩, dup2, lt, push1 ⟨47⟩, dup3, gt, and, push2 ⟨3077⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [jumpdest, push1 ⟨63⟩, dup2, gt, push2 ⟨2769⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiT (by native_decide) jump_2323]
  have rd20 := evm_run_rfl rd19 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨2750⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [dup1, push1 ⟨1⟩, eq, push2 ⟨2731⟩, jumpiNT (by native_decide)]
  have rd22 := evm_run_rfl rd21 with [dup1, push1 ⟨2⟩, eq, push2 ⟨2712⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨3⟩, eq, push2 ⟨2693⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup1, push1 ⟨4⟩, eq, push2 ⟨2674⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨5⟩, eq, push2 ⟨2655⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup1, push1 ⟨6⟩, eq, push2 ⟨2636⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨7⟩, eq, push2 ⟨2617⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨8⟩, eq, push2 ⟨2598⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [dup1, push1 ⟨9⟩, eq, push2 ⟨2579⟩, jumpiNT (by native_decide)]
  have rd30 := evm_run_rfl rd29 with [dup1, dup15, eq, push2 ⟨2560⟩, jumpiNT (by native_decide)]
  have rd31 := evm_run_rfl rd30 with [dup1, push1 ⟨11⟩, eq, push2 ⟨2541⟩, jumpiNT (by native_decide)]
  have rd32 := evm_run_rfl rd31 with [dup1, push1 ⟨12⟩, eq, push2 ⟨2522⟩, jumpiNT (by native_decide)]
  have rd33 := evm_run_rfl rd32 with [dup1, push1 ⟨13⟩, eq, push2 ⟨2503⟩, jumpiNT (by native_decide)]
  have rd34 := evm_run_rfl rd33 with [dup1, push1 ⟨14⟩, eq, push2 ⟨2484⟩, jumpiT (by native_decide) jump_2484]
  have rd35 := evm_run_rfl rd34 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨9⟩, swap8, swap2, swap3, pop, pop, push2 ⟨2457⟩, jump jump_2457]
  have rd36 := evm_run_rfl rd35 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨494⟩, jump jump_494]
  have rd37 := evm_run_rfl rd36 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd38 := RD.runtimeMload rd37 (by old_decode) (by simp; omega)
  have rd39 := evm_run_rfl rd38 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd40 := evm_run_rfl rd39 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_511]
  have rd41 := evm_run_rfl rd40 with [jumpdest, add, and, swap8, dup7]
  have rd42 := RD.runtimeMstore rd41 (by old_decode) (by simp; omega)
  have rd43 := evm_run_rfl rd42 with [push1 ⟨128⟩, dup7, add]
  have rd44 := RD.runtimeMstore rd43 (by old_decode) (by simp; omega)
  have rd45 := evm_run_rfl rd44 with [push2 ⟨268⟩, jump jump_268]
  have rd46 := evm_run_rfl rd45 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_526]
  have rd47 := evm_run_rfl rd46 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd48 := RD.runtimeMstore rd47 (by old_decode) (by simp; omega)
  have rd49 := evm_run_rfl rd48 with [push1 ⟨64⟩, dup3, add]
  have rd50 := RD.runtimeMstore rd49 (by old_decode) (by simp; omega)
  have rd51 := evm_run_rfl rd50 with [add]
  have rd52 := RD.runtimeMstore rd51 (by old_decode) (by simp; omega)
  have rd53 := evm_run_rfl rd52 with [jump jump_8991]
  exact ⟨_, _, by
    simpa [oldLeftHelperStack, oldLeftRoundCursor, runtimeRoundPreludeCursor,
      runtimePreludeB, runtimePreludeC, runtimePreludeD, runtimeRightPreludeCursor,
      runtimeRightPreludeB, runtimeRightPreludeC, runtimeRightPreludeD,
      runtimeRoundCursor, runtimeRoundNext, runtimeRoundSum, runtimeRol32,
      runtimeRoundX, runtimeRoundAwX, runtimeRoundMessageAddr, runtimeRowEntry,
      runtimeRoundA, runtimeRoundAwA, runtimeRoundB, runtimeRoundAwB,
      runtimeRoundC, runtimeRoundAwC, runtimeRoundD, runtimeRoundAwD,
      runtimeRoundE, runtimeRoundAwE, runtimeStoreCursor, runtimeLeftF,
      runtimeRightF, leftWordRowWord, leftRotationRowWord, leftConstantWord,
      rightWordRowWord, rightRotationRowWord, rightConstantWord, mask32Word,
      Model.leftWordRow, Model.leftRotationRow, Model.leftConstant,
      Model.rightWordRow, Model.rightRotationRow, Model.rightConstant,
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd53⟩

theorem runtime_leftRoundHelper_15 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 15 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 0 15).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 0 15).aw
      rdata (cA, σ) k' C' := by
  simp only [oldLeftHelperStack] at rd
  have rd1 := evm_run_rfl rd with [jumpdest, push1 ⟨32⟩, swap2, push2 ⟨526⟩, push1 ⟨10⟩, push4 ⟨4294967295⟩, swap3, dup5]
  have rd2 := RD.runtimeMload rd1 (by old_decode) (by simp; omega)
  have rd3 := evm_run_rfl rd2 with [swap1, dup7, dup7, add]
  have rd4 := RD.runtimeMload rd3 (by old_decode) (by simp; omega)
  have rd5 := evm_run_rfl rd4 with [swap5, push1 ⟨64⟩, dup8, add]
  have rd6 := RD.runtimeMload rd5 (by old_decode) (by simp; omega)
  have rd7 := evm_run_rfl rd6 with [swap3, push2 ⟨511⟩, push1 ⟨96⟩, dup10, add]
  have rd8 := RD.runtimeMload rd7 (by old_decode) (by simp; omega)
  have rd9 := evm_run_rfl rd8 with [swap4, dup4, dup10, push1 ⟨128⟩, dup13, add]
  have rd10 := RD.runtimeMload rd9 (by old_decode) (by simp; omega)
  have rd11 := evm_run_rfl rd10 with [swap14, dup15, swap6, dup4, push1 ⟨16⟩, dup4, div, swap6, push0, swap4, dup13, dup13, push0, swap8, dup11, swap3, dup4, push0, eq, push2 ⟨4108⟩, jumpiT (by native_decide) jump_4108]
  have rd12 := evm_run_rfl rd11 with [jumpdest, swap4, swap9, pop, swap2, pop, swap3, swap6, pop, xor, xor, swap3, push0, swap5, push2 ⟨391⟩, jump jump_391]
  have rd13 := evm_run_rfl rd12 with [jumpdest, push0, swap1, push1 ⟨16⟩, dup2, lt, push2 ⟨4001⟩, jumpiT (by native_decide) jump_4001]
  have rd14 := evm_run_rfl rd13 with [jumpdest, dup1, swap2, pop, swap1, push2 ⟨402⟩, jump jump_402]
  have rd15 := evm_run_rfl rd14 with [jumpdest, push1 ⟨32⟩, dup2, lt, push1 ⟨15⟩, dup3, gt, and, push2 ⟨3693⟩, jumpiNT (by native_decide)]
  have rd16 := evm_run_rfl rd15 with [jumpdest, push1 ⟨48⟩, dup2, lt, push1 ⟨31⟩, dup3, gt, and, push2 ⟨3385⟩, jumpiNT (by native_decide)]
  have rd17 := evm_run_rfl rd16 with [jumpdest, push1 ⟨64⟩, dup2, lt, push1 ⟨47⟩, dup3, gt, and, push2 ⟨3077⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [jumpdest, push1 ⟨63⟩, dup2, gt, push2 ⟨2769⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiT (by native_decide) jump_2323]
  have rd20 := evm_run_rfl rd19 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨2750⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [dup1, push1 ⟨1⟩, eq, push2 ⟨2731⟩, jumpiNT (by native_decide)]
  have rd22 := evm_run_rfl rd21 with [dup1, push1 ⟨2⟩, eq, push2 ⟨2712⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨3⟩, eq, push2 ⟨2693⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup1, push1 ⟨4⟩, eq, push2 ⟨2674⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨5⟩, eq, push2 ⟨2655⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup1, push1 ⟨6⟩, eq, push2 ⟨2636⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨7⟩, eq, push2 ⟨2617⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨8⟩, eq, push2 ⟨2598⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [dup1, push1 ⟨9⟩, eq, push2 ⟨2579⟩, jumpiNT (by native_decide)]
  have rd30 := evm_run_rfl rd29 with [dup1, dup15, eq, push2 ⟨2560⟩, jumpiNT (by native_decide)]
  have rd31 := evm_run_rfl rd30 with [dup1, push1 ⟨11⟩, eq, push2 ⟨2541⟩, jumpiNT (by native_decide)]
  have rd32 := evm_run_rfl rd31 with [dup1, push1 ⟨12⟩, eq, push2 ⟨2522⟩, jumpiNT (by native_decide)]
  have rd33 := evm_run_rfl rd32 with [dup1, push1 ⟨13⟩, eq, push2 ⟨2503⟩, jumpiNT (by native_decide)]
  have rd34 := evm_run_rfl rd33 with [dup1, push1 ⟨14⟩, eq, push2 ⟨2484⟩, jumpiNT (by native_decide)]
  have rd35 := evm_run_rfl rd34 with [push1 ⟨15⟩, eq, push2 ⟨2466⟩, jumpiT (by native_decide) jump_2466]
  have rd36 := evm_run_rfl rd35 with [jumpdest, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨8⟩, swap8, swap2, swap3, pop, pop, push2 ⟨2457⟩, jump jump_2457]
  have rd37 := evm_run_rfl rd36 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨494⟩, jump jump_494]
  have rd38 := evm_run_rfl rd37 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd39 := RD.runtimeMload rd38 (by old_decode) (by simp; omega)
  have rd40 := evm_run_rfl rd39 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd41 := evm_run_rfl rd40 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_511]
  have rd42 := evm_run_rfl rd41 with [jumpdest, add, and, swap8, dup7]
  have rd43 := RD.runtimeMstore rd42 (by old_decode) (by simp; omega)
  have rd44 := evm_run_rfl rd43 with [push1 ⟨128⟩, dup7, add]
  have rd45 := RD.runtimeMstore rd44 (by old_decode) (by simp; omega)
  have rd46 := evm_run_rfl rd45 with [push2 ⟨268⟩, jump jump_268]
  have rd47 := evm_run_rfl rd46 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_526]
  have rd48 := evm_run_rfl rd47 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd49 := RD.runtimeMstore rd48 (by old_decode) (by simp; omega)
  have rd50 := evm_run_rfl rd49 with [push1 ⟨64⟩, dup3, add]
  have rd51 := RD.runtimeMstore rd50 (by old_decode) (by simp; omega)
  have rd52 := evm_run_rfl rd51 with [add]
  have rd53 := RD.runtimeMstore rd52 (by old_decode) (by simp; omega)
  have rd54 := evm_run_rfl rd53 with [jump jump_8991]
  exact ⟨_, _, by
    simpa [oldLeftHelperStack, oldLeftRoundCursor, runtimeRoundPreludeCursor,
      runtimePreludeB, runtimePreludeC, runtimePreludeD, runtimeRightPreludeCursor,
      runtimeRightPreludeB, runtimeRightPreludeC, runtimeRightPreludeD,
      runtimeRoundCursor, runtimeRoundNext, runtimeRoundSum, runtimeRol32,
      runtimeRoundX, runtimeRoundAwX, runtimeRoundMessageAddr, runtimeRowEntry,
      runtimeRoundA, runtimeRoundAwA, runtimeRoundB, runtimeRoundAwB,
      runtimeRoundC, runtimeRoundAwC, runtimeRoundD, runtimeRoundAwD,
      runtimeRoundE, runtimeRoundAwE, runtimeStoreCursor, runtimeLeftF,
      runtimeRightF, leftWordRowWord, leftRotationRowWord, leftConstantWord,
      rightWordRowWord, rightRotationRowWord, rightConstantWord, mask32Word,
      Model.leftWordRow, Model.leftRotationRow, Model.leftConstant,
      Model.rightWordRow, Model.rightRotationRow, Model.rightConstant,
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd54⟩

theorem runtime_leftRoundHelper_16 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 16 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 1 0).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 1 0).aw
      rdata (cA, σ) k' C' := by
  simp only [oldLeftHelperStack] at rd
  have rd1 := evm_run_rfl rd with [jumpdest, push1 ⟨32⟩, swap2, push2 ⟨526⟩, push1 ⟨10⟩, push4 ⟨4294967295⟩, swap3, dup5]
  have rd2 := RD.runtimeMload rd1 (by old_decode) (by simp; omega)
  have rd3 := evm_run_rfl rd2 with [swap1, dup7, dup7, add]
  have rd4 := RD.runtimeMload rd3 (by old_decode) (by simp; omega)
  have rd5 := evm_run_rfl rd4 with [swap5, push1 ⟨64⟩, dup8, add]
  have rd6 := RD.runtimeMload rd5 (by old_decode) (by simp; omega)
  have rd7 := evm_run_rfl rd6 with [swap3, push2 ⟨511⟩, push1 ⟨96⟩, dup10, add]
  have rd8 := RD.runtimeMload rd7 (by old_decode) (by simp; omega)
  have rd9 := evm_run_rfl rd8 with [swap4, dup4, dup10, push1 ⟨128⟩, dup13, add]
  have rd10 := RD.runtimeMload rd9 (by old_decode) (by simp; omega)
  have rd11 := evm_run_rfl rd10 with [swap14, dup15, swap6, dup4, push1 ⟨16⟩, dup4, div, swap6, push0, swap4, dup13, dup13, push0, swap8, dup11, swap3, dup4, push0, eq, push2 ⟨4108⟩, jumpiNT (by native_decide)]
  have rd12 := evm_run_rfl rd11 with [pop, dup3, push1 ⟨1⟩, eq, push2 ⟨4081⟩, jumpiT (by native_decide) jump_4081]
  have rd13 := evm_run_rfl rd12 with [jumpdest, swap4, swap7, pop, swap1, pop, dup14, swap2, swap7, pop, dup3, not, and, swap2, and, or, swap3, push4 ⟨1518500249⟩, swap5, push2 ⟨391⟩, jump jump_391]
  have rd14 := evm_run_rfl rd13 with [jumpdest, push0, swap1, push1 ⟨16⟩, dup2, lt, push2 ⟨4001⟩, jumpiNT (by native_decide)]
  have rd15 := evm_run_rfl rd14 with [jumpdest, push1 ⟨32⟩, dup2, lt, push1 ⟨15⟩, dup3, gt, and, push2 ⟨3693⟩, jumpiT (by native_decide) jump_3693]
  have rd16 := evm_run_rfl rd15 with [jumpdest, push1 ⟨16⟩, dup2, sub, dup1, push0, eq, push2 ⟨3990⟩, jumpiT (by native_decide) jump_3990]
  have rd17 := evm_run_rfl rd16 with [jumpdest, pop, swap1, pop, push1 ⟨7⟩, swap1, push2 ⟨3823⟩, jump jump_3823]
  have rd18 := evm_run_rfl rd17 with [jumpdest, push2 ⟨416⟩, jump jump_416]
  have rd19 := evm_run_rfl rd18 with [jumpdest, push1 ⟨48⟩, dup2, lt, push1 ⟨31⟩, dup3, gt, and, push2 ⟨3385⟩, jumpiNT (by native_decide)]
  have rd20 := evm_run_rfl rd19 with [jumpdest, push1 ⟨64⟩, dup2, lt, push1 ⟨47⟩, dup3, gt, and, push2 ⟨3077⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [jumpdest, push1 ⟨63⟩, dup2, gt, push2 ⟨2769⟩, jumpiNT (by native_decide)]
  have rd22 := evm_run_rfl rd21 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1877⟩, jumpiT (by native_decide) jump_1877]
  have rd24 := evm_run_rfl rd23 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨2304⟩, jumpiT (by native_decide) jump_2304]
  have rd25 := evm_run_rfl rd24 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨7⟩, swap8, swap2, swap3, pop, pop, push2 ⟨2011⟩, jump jump_2011]
  have rd26 := evm_run_rfl rd25 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨494⟩, jump jump_494]
  have rd27 := evm_run_rfl rd26 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd28 := RD.runtimeMload rd27 (by old_decode) (by simp; omega)
  have rd29 := evm_run_rfl rd28 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd30 := evm_run_rfl rd29 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_511]
  have rd31 := evm_run_rfl rd30 with [jumpdest, add, and, swap8, dup7]
  have rd32 := RD.runtimeMstore rd31 (by old_decode) (by simp; omega)
  have rd33 := evm_run_rfl rd32 with [push1 ⟨128⟩, dup7, add]
  have rd34 := RD.runtimeMstore rd33 (by old_decode) (by simp; omega)
  have rd35 := evm_run_rfl rd34 with [push2 ⟨268⟩, jump jump_268]
  have rd36 := evm_run_rfl rd35 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_526]
  have rd37 := evm_run_rfl rd36 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd38 := RD.runtimeMstore rd37 (by old_decode) (by simp; omega)
  have rd39 := evm_run_rfl rd38 with [push1 ⟨64⟩, dup3, add]
  have rd40 := RD.runtimeMstore rd39 (by old_decode) (by simp; omega)
  have rd41 := evm_run_rfl rd40 with [add]
  have rd42 := RD.runtimeMstore rd41 (by old_decode) (by simp; omega)
  have rd43 := evm_run_rfl rd42 with [jump jump_8991]
  exact ⟨_, _, by
    simpa [oldLeftHelperStack, oldLeftRoundCursor, runtimeRoundPreludeCursor,
      runtimePreludeB, runtimePreludeC, runtimePreludeD, runtimeRightPreludeCursor,
      runtimeRightPreludeB, runtimeRightPreludeC, runtimeRightPreludeD,
      runtimeRoundCursor, runtimeRoundNext, runtimeRoundSum, runtimeRol32,
      runtimeRoundX, runtimeRoundAwX, runtimeRoundMessageAddr, runtimeRowEntry,
      runtimeRoundA, runtimeRoundAwA, runtimeRoundB, runtimeRoundAwB,
      runtimeRoundC, runtimeRoundAwC, runtimeRoundD, runtimeRoundAwD,
      runtimeRoundE, runtimeRoundAwE, runtimeStoreCursor, runtimeLeftF,
      runtimeRightF, leftWordRowWord, leftRotationRowWord, leftConstantWord,
      rightWordRowWord, rightRotationRowWord, rightConstantWord, mask32Word,
      Model.leftWordRow, Model.leftRotationRow, Model.leftConstant,
      Model.rightWordRow, Model.rightRotationRow, Model.rightConstant,
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd43⟩

theorem runtime_leftRoundHelper_17 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 17 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 1 1).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 1 1).aw
      rdata (cA, σ) k' C' := by
  simp only [oldLeftHelperStack] at rd
  have rd1 := evm_run_rfl rd with [jumpdest, push1 ⟨32⟩, swap2, push2 ⟨526⟩, push1 ⟨10⟩, push4 ⟨4294967295⟩, swap3, dup5]
  have rd2 := RD.runtimeMload rd1 (by old_decode) (by simp; omega)
  have rd3 := evm_run_rfl rd2 with [swap1, dup7, dup7, add]
  have rd4 := RD.runtimeMload rd3 (by old_decode) (by simp; omega)
  have rd5 := evm_run_rfl rd4 with [swap5, push1 ⟨64⟩, dup8, add]
  have rd6 := RD.runtimeMload rd5 (by old_decode) (by simp; omega)
  have rd7 := evm_run_rfl rd6 with [swap3, push2 ⟨511⟩, push1 ⟨96⟩, dup10, add]
  have rd8 := RD.runtimeMload rd7 (by old_decode) (by simp; omega)
  have rd9 := evm_run_rfl rd8 with [swap4, dup4, dup10, push1 ⟨128⟩, dup13, add]
  have rd10 := RD.runtimeMload rd9 (by old_decode) (by simp; omega)
  have rd11 := evm_run_rfl rd10 with [swap14, dup15, swap6, dup4, push1 ⟨16⟩, dup4, div, swap6, push0, swap4, dup13, dup13, push0, swap8, dup11, swap3, dup4, push0, eq, push2 ⟨4108⟩, jumpiNT (by native_decide)]
  have rd12 := evm_run_rfl rd11 with [pop, dup3, push1 ⟨1⟩, eq, push2 ⟨4081⟩, jumpiT (by native_decide) jump_4081]
  have rd13 := evm_run_rfl rd12 with [jumpdest, swap4, swap7, pop, swap1, pop, dup14, swap2, swap7, pop, dup3, not, and, swap2, and, or, swap3, push4 ⟨1518500249⟩, swap5, push2 ⟨391⟩, jump jump_391]
  have rd14 := evm_run_rfl rd13 with [jumpdest, push0, swap1, push1 ⟨16⟩, dup2, lt, push2 ⟨4001⟩, jumpiNT (by native_decide)]
  have rd15 := evm_run_rfl rd14 with [jumpdest, push1 ⟨32⟩, dup2, lt, push1 ⟨15⟩, dup3, gt, and, push2 ⟨3693⟩, jumpiT (by native_decide) jump_3693]
  have rd16 := evm_run_rfl rd15 with [jumpdest, push1 ⟨16⟩, dup2, sub, dup1, push0, eq, push2 ⟨3990⟩, jumpiNT (by native_decide)]
  have rd17 := evm_run_rfl rd16 with [dup1, push1 ⟨1⟩, eq, push2 ⟨3979⟩, jumpiT (by native_decide) jump_3979]
  have rd18 := evm_run_rfl rd17 with [jumpdest, pop, swap1, pop, push1 ⟨4⟩, swap1, push2 ⟨3823⟩, jump jump_3823]
  have rd19 := evm_run_rfl rd18 with [jumpdest, push2 ⟨416⟩, jump jump_416]
  have rd20 := evm_run_rfl rd19 with [jumpdest, push1 ⟨48⟩, dup2, lt, push1 ⟨31⟩, dup3, gt, and, push2 ⟨3385⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [jumpdest, push1 ⟨64⟩, dup2, lt, push1 ⟨47⟩, dup3, gt, and, push2 ⟨3077⟩, jumpiNT (by native_decide)]
  have rd22 := evm_run_rfl rd21 with [jumpdest, push1 ⟨63⟩, dup2, gt, push2 ⟨2769⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1877⟩, jumpiT (by native_decide) jump_1877]
  have rd25 := evm_run_rfl rd24 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨2304⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup1, push1 ⟨1⟩, eq, push2 ⟨2285⟩, jumpiT (by native_decide) jump_2285]
  have rd27 := evm_run_rfl rd26 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨6⟩, swap8, swap2, swap3, pop, pop, push2 ⟨2011⟩, jump jump_2011]
  have rd28 := evm_run_rfl rd27 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨494⟩, jump jump_494]
  have rd29 := evm_run_rfl rd28 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd30 := RD.runtimeMload rd29 (by old_decode) (by simp; omega)
  have rd31 := evm_run_rfl rd30 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd32 := evm_run_rfl rd31 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_511]
  have rd33 := evm_run_rfl rd32 with [jumpdest, add, and, swap8, dup7]
  have rd34 := RD.runtimeMstore rd33 (by old_decode) (by simp; omega)
  have rd35 := evm_run_rfl rd34 with [push1 ⟨128⟩, dup7, add]
  have rd36 := RD.runtimeMstore rd35 (by old_decode) (by simp; omega)
  have rd37 := evm_run_rfl rd36 with [push2 ⟨268⟩, jump jump_268]
  have rd38 := evm_run_rfl rd37 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_526]
  have rd39 := evm_run_rfl rd38 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd40 := RD.runtimeMstore rd39 (by old_decode) (by simp; omega)
  have rd41 := evm_run_rfl rd40 with [push1 ⟨64⟩, dup3, add]
  have rd42 := RD.runtimeMstore rd41 (by old_decode) (by simp; omega)
  have rd43 := evm_run_rfl rd42 with [add]
  have rd44 := RD.runtimeMstore rd43 (by old_decode) (by simp; omega)
  have rd45 := evm_run_rfl rd44 with [jump jump_8991]
  exact ⟨_, _, by
    simpa [oldLeftHelperStack, oldLeftRoundCursor, runtimeRoundPreludeCursor,
      runtimePreludeB, runtimePreludeC, runtimePreludeD, runtimeRightPreludeCursor,
      runtimeRightPreludeB, runtimeRightPreludeC, runtimeRightPreludeD,
      runtimeRoundCursor, runtimeRoundNext, runtimeRoundSum, runtimeRol32,
      runtimeRoundX, runtimeRoundAwX, runtimeRoundMessageAddr, runtimeRowEntry,
      runtimeRoundA, runtimeRoundAwA, runtimeRoundB, runtimeRoundAwB,
      runtimeRoundC, runtimeRoundAwC, runtimeRoundD, runtimeRoundAwD,
      runtimeRoundE, runtimeRoundAwE, runtimeStoreCursor, runtimeLeftF,
      runtimeRightF, leftWordRowWord, leftRotationRowWord, leftConstantWord,
      rightWordRowWord, rightRotationRowWord, rightConstantWord, mask32Word,
      Model.leftWordRow, Model.leftRotationRow, Model.leftConstant,
      Model.rightWordRow, Model.rightRotationRow, Model.rightConstant,
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd45⟩

theorem runtime_leftRoundHelper_18 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 18 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 1 2).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 1 2).aw
      rdata (cA, σ) k' C' := by
  simp only [oldLeftHelperStack] at rd
  have rd1 := evm_run_rfl rd with [jumpdest, push1 ⟨32⟩, swap2, push2 ⟨526⟩, push1 ⟨10⟩, push4 ⟨4294967295⟩, swap3, dup5]
  have rd2 := RD.runtimeMload rd1 (by old_decode) (by simp; omega)
  have rd3 := evm_run_rfl rd2 with [swap1, dup7, dup7, add]
  have rd4 := RD.runtimeMload rd3 (by old_decode) (by simp; omega)
  have rd5 := evm_run_rfl rd4 with [swap5, push1 ⟨64⟩, dup8, add]
  have rd6 := RD.runtimeMload rd5 (by old_decode) (by simp; omega)
  have rd7 := evm_run_rfl rd6 with [swap3, push2 ⟨511⟩, push1 ⟨96⟩, dup10, add]
  have rd8 := RD.runtimeMload rd7 (by old_decode) (by simp; omega)
  have rd9 := evm_run_rfl rd8 with [swap4, dup4, dup10, push1 ⟨128⟩, dup13, add]
  have rd10 := RD.runtimeMload rd9 (by old_decode) (by simp; omega)
  have rd11 := evm_run_rfl rd10 with [swap14, dup15, swap6, dup4, push1 ⟨16⟩, dup4, div, swap6, push0, swap4, dup13, dup13, push0, swap8, dup11, swap3, dup4, push0, eq, push2 ⟨4108⟩, jumpiNT (by native_decide)]
  have rd12 := evm_run_rfl rd11 with [pop, dup3, push1 ⟨1⟩, eq, push2 ⟨4081⟩, jumpiT (by native_decide) jump_4081]
  have rd13 := evm_run_rfl rd12 with [jumpdest, swap4, swap7, pop, swap1, pop, dup14, swap2, swap7, pop, dup3, not, and, swap2, and, or, swap3, push4 ⟨1518500249⟩, swap5, push2 ⟨391⟩, jump jump_391]
  have rd14 := evm_run_rfl rd13 with [jumpdest, push0, swap1, push1 ⟨16⟩, dup2, lt, push2 ⟨4001⟩, jumpiNT (by native_decide)]
  have rd15 := evm_run_rfl rd14 with [jumpdest, push1 ⟨32⟩, dup2, lt, push1 ⟨15⟩, dup3, gt, and, push2 ⟨3693⟩, jumpiT (by native_decide) jump_3693]
  have rd16 := evm_run_rfl rd15 with [jumpdest, push1 ⟨16⟩, dup2, sub, dup1, push0, eq, push2 ⟨3990⟩, jumpiNT (by native_decide)]
  have rd17 := evm_run_rfl rd16 with [dup1, push1 ⟨1⟩, eq, push2 ⟨3979⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [dup1, push1 ⟨2⟩, eq, push2 ⟨3968⟩, jumpiT (by native_decide) jump_3968]
  have rd19 := evm_run_rfl rd18 with [jumpdest, pop, swap1, pop, push1 ⟨13⟩, swap1, push2 ⟨3823⟩, jump jump_3823]
  have rd20 := evm_run_rfl rd19 with [jumpdest, push2 ⟨416⟩, jump jump_416]
  have rd21 := evm_run_rfl rd20 with [jumpdest, push1 ⟨48⟩, dup2, lt, push1 ⟨31⟩, dup3, gt, and, push2 ⟨3385⟩, jumpiNT (by native_decide)]
  have rd22 := evm_run_rfl rd21 with [jumpdest, push1 ⟨64⟩, dup2, lt, push1 ⟨47⟩, dup3, gt, and, push2 ⟨3077⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [jumpdest, push1 ⟨63⟩, dup2, gt, push2 ⟨2769⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1877⟩, jumpiT (by native_decide) jump_1877]
  have rd26 := evm_run_rfl rd25 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨2304⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨1⟩, eq, push2 ⟨2285⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨2⟩, eq, push2 ⟨2266⟩, jumpiT (by native_decide) jump_2266]
  have rd29 := evm_run_rfl rd28 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨8⟩, swap8, swap2, swap3, pop, pop, push2 ⟨2011⟩, jump jump_2011]
  have rd30 := evm_run_rfl rd29 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨494⟩, jump jump_494]
  have rd31 := evm_run_rfl rd30 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd32 := RD.runtimeMload rd31 (by old_decode) (by simp; omega)
  have rd33 := evm_run_rfl rd32 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd34 := evm_run_rfl rd33 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_511]
  have rd35 := evm_run_rfl rd34 with [jumpdest, add, and, swap8, dup7]
  have rd36 := RD.runtimeMstore rd35 (by old_decode) (by simp; omega)
  have rd37 := evm_run_rfl rd36 with [push1 ⟨128⟩, dup7, add]
  have rd38 := RD.runtimeMstore rd37 (by old_decode) (by simp; omega)
  have rd39 := evm_run_rfl rd38 with [push2 ⟨268⟩, jump jump_268]
  have rd40 := evm_run_rfl rd39 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_526]
  have rd41 := evm_run_rfl rd40 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd42 := RD.runtimeMstore rd41 (by old_decode) (by simp; omega)
  have rd43 := evm_run_rfl rd42 with [push1 ⟨64⟩, dup3, add]
  have rd44 := RD.runtimeMstore rd43 (by old_decode) (by simp; omega)
  have rd45 := evm_run_rfl rd44 with [add]
  have rd46 := RD.runtimeMstore rd45 (by old_decode) (by simp; omega)
  have rd47 := evm_run_rfl rd46 with [jump jump_8991]
  exact ⟨_, _, by
    simpa [oldLeftHelperStack, oldLeftRoundCursor, runtimeRoundPreludeCursor,
      runtimePreludeB, runtimePreludeC, runtimePreludeD, runtimeRightPreludeCursor,
      runtimeRightPreludeB, runtimeRightPreludeC, runtimeRightPreludeD,
      runtimeRoundCursor, runtimeRoundNext, runtimeRoundSum, runtimeRol32,
      runtimeRoundX, runtimeRoundAwX, runtimeRoundMessageAddr, runtimeRowEntry,
      runtimeRoundA, runtimeRoundAwA, runtimeRoundB, runtimeRoundAwB,
      runtimeRoundC, runtimeRoundAwC, runtimeRoundD, runtimeRoundAwD,
      runtimeRoundE, runtimeRoundAwE, runtimeStoreCursor, runtimeLeftF,
      runtimeRightF, leftWordRowWord, leftRotationRowWord, leftConstantWord,
      rightWordRowWord, rightRotationRowWord, rightConstantWord, mask32Word,
      Model.leftWordRow, Model.leftRotationRow, Model.leftConstant,
      Model.rightWordRow, Model.rightRotationRow, Model.rightConstant,
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd47⟩

theorem runtime_leftRoundHelper_19 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 19 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 1 3).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 1 3).aw
      rdata (cA, σ) k' C' := by
  simp only [oldLeftHelperStack] at rd
  have rd1 := evm_run_rfl rd with [jumpdest, push1 ⟨32⟩, swap2, push2 ⟨526⟩, push1 ⟨10⟩, push4 ⟨4294967295⟩, swap3, dup5]
  have rd2 := RD.runtimeMload rd1 (by old_decode) (by simp; omega)
  have rd3 := evm_run_rfl rd2 with [swap1, dup7, dup7, add]
  have rd4 := RD.runtimeMload rd3 (by old_decode) (by simp; omega)
  have rd5 := evm_run_rfl rd4 with [swap5, push1 ⟨64⟩, dup8, add]
  have rd6 := RD.runtimeMload rd5 (by old_decode) (by simp; omega)
  have rd7 := evm_run_rfl rd6 with [swap3, push2 ⟨511⟩, push1 ⟨96⟩, dup10, add]
  have rd8 := RD.runtimeMload rd7 (by old_decode) (by simp; omega)
  have rd9 := evm_run_rfl rd8 with [swap4, dup4, dup10, push1 ⟨128⟩, dup13, add]
  have rd10 := RD.runtimeMload rd9 (by old_decode) (by simp; omega)
  have rd11 := evm_run_rfl rd10 with [swap14, dup15, swap6, dup4, push1 ⟨16⟩, dup4, div, swap6, push0, swap4, dup13, dup13, push0, swap8, dup11, swap3, dup4, push0, eq, push2 ⟨4108⟩, jumpiNT (by native_decide)]
  have rd12 := evm_run_rfl rd11 with [pop, dup3, push1 ⟨1⟩, eq, push2 ⟨4081⟩, jumpiT (by native_decide) jump_4081]
  have rd13 := evm_run_rfl rd12 with [jumpdest, swap4, swap7, pop, swap1, pop, dup14, swap2, swap7, pop, dup3, not, and, swap2, and, or, swap3, push4 ⟨1518500249⟩, swap5, push2 ⟨391⟩, jump jump_391]
  have rd14 := evm_run_rfl rd13 with [jumpdest, push0, swap1, push1 ⟨16⟩, dup2, lt, push2 ⟨4001⟩, jumpiNT (by native_decide)]
  have rd15 := evm_run_rfl rd14 with [jumpdest, push1 ⟨32⟩, dup2, lt, push1 ⟨15⟩, dup3, gt, and, push2 ⟨3693⟩, jumpiT (by native_decide) jump_3693]
  have rd16 := evm_run_rfl rd15 with [jumpdest, push1 ⟨16⟩, dup2, sub, dup1, push0, eq, push2 ⟨3990⟩, jumpiNT (by native_decide)]
  have rd17 := evm_run_rfl rd16 with [dup1, push1 ⟨1⟩, eq, push2 ⟨3979⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [dup1, push1 ⟨2⟩, eq, push2 ⟨3968⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [dup1, push1 ⟨3⟩, eq, push2 ⟨3957⟩, jumpiT (by native_decide) jump_3957]
  have rd20 := evm_run_rfl rd19 with [jumpdest, pop, swap1, pop, push1 ⟨1⟩, swap1, push2 ⟨3823⟩, jump jump_3823]
  have rd21 := evm_run_rfl rd20 with [jumpdest, push2 ⟨416⟩, jump jump_416]
  have rd22 := evm_run_rfl rd21 with [jumpdest, push1 ⟨48⟩, dup2, lt, push1 ⟨31⟩, dup3, gt, and, push2 ⟨3385⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [jumpdest, push1 ⟨64⟩, dup2, lt, push1 ⟨47⟩, dup3, gt, and, push2 ⟨3077⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [jumpdest, push1 ⟨63⟩, dup2, gt, push2 ⟨2769⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1877⟩, jumpiT (by native_decide) jump_1877]
  have rd27 := evm_run_rfl rd26 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨2304⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨1⟩, eq, push2 ⟨2285⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [dup1, push1 ⟨2⟩, eq, push2 ⟨2266⟩, jumpiNT (by native_decide)]
  have rd30 := evm_run_rfl rd29 with [dup1, push1 ⟨3⟩, eq, push2 ⟨2247⟩, jumpiT (by native_decide) jump_2247]
  have rd31 := evm_run_rfl rd30 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨13⟩, swap8, swap2, swap3, pop, pop, push2 ⟨2011⟩, jump jump_2011]
  have rd32 := evm_run_rfl rd31 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨494⟩, jump jump_494]
  have rd33 := evm_run_rfl rd32 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd34 := RD.runtimeMload rd33 (by old_decode) (by simp; omega)
  have rd35 := evm_run_rfl rd34 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd36 := evm_run_rfl rd35 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_511]
  have rd37 := evm_run_rfl rd36 with [jumpdest, add, and, swap8, dup7]
  have rd38 := RD.runtimeMstore rd37 (by old_decode) (by simp; omega)
  have rd39 := evm_run_rfl rd38 with [push1 ⟨128⟩, dup7, add]
  have rd40 := RD.runtimeMstore rd39 (by old_decode) (by simp; omega)
  have rd41 := evm_run_rfl rd40 with [push2 ⟨268⟩, jump jump_268]
  have rd42 := evm_run_rfl rd41 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_526]
  have rd43 := evm_run_rfl rd42 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd44 := RD.runtimeMstore rd43 (by old_decode) (by simp; omega)
  have rd45 := evm_run_rfl rd44 with [push1 ⟨64⟩, dup3, add]
  have rd46 := RD.runtimeMstore rd45 (by old_decode) (by simp; omega)
  have rd47 := evm_run_rfl rd46 with [add]
  have rd48 := RD.runtimeMstore rd47 (by old_decode) (by simp; omega)
  have rd49 := evm_run_rfl rd48 with [jump jump_8991]
  exact ⟨_, _, by
    simpa [oldLeftHelperStack, oldLeftRoundCursor, runtimeRoundPreludeCursor,
      runtimePreludeB, runtimePreludeC, runtimePreludeD, runtimeRightPreludeCursor,
      runtimeRightPreludeB, runtimeRightPreludeC, runtimeRightPreludeD,
      runtimeRoundCursor, runtimeRoundNext, runtimeRoundSum, runtimeRol32,
      runtimeRoundX, runtimeRoundAwX, runtimeRoundMessageAddr, runtimeRowEntry,
      runtimeRoundA, runtimeRoundAwA, runtimeRoundB, runtimeRoundAwB,
      runtimeRoundC, runtimeRoundAwC, runtimeRoundD, runtimeRoundAwD,
      runtimeRoundE, runtimeRoundAwE, runtimeStoreCursor, runtimeLeftF,
      runtimeRightF, leftWordRowWord, leftRotationRowWord, leftConstantWord,
      rightWordRowWord, rightRotationRowWord, rightConstantWord, mask32Word,
      Model.leftWordRow, Model.leftRotationRow, Model.leftConstant,
      Model.rightWordRow, Model.rightRotationRow, Model.rightConstant,
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd49⟩


end Ripemd160Old
