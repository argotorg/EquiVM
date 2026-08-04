import Examples.Ripemd160Old.HashLeftRound0

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000
namespace Ripemd160Old
open Ripemd160

theorem runtime_leftRoundHelper_50 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 50 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 3 2).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 3 2).aw
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
  have rd12 := evm_run_rfl rd11 with [pop, dup3, push1 ⟨1⟩, eq, push2 ⟨4081⟩, jumpiNT (by native_decide)]
  have rd13 := evm_run_rfl rd12 with [dup3, push1 ⟨2⟩, eq, push2 ⟨4058⟩, jumpiNT (by native_decide)]
  have rd14 := evm_run_rfl rd13 with [pop, pop, dup1, push1 ⟨3⟩, eq, push2 ⟨4032⟩, jumpiT (by native_decide) jump_4032]
  have rd15 := evm_run_rfl rd14 with [jumpdest, pop, swap5, pop, swap3, pop, dup14, dup11, dup1, not, dup14, and, swap2, and, or, swap3, push4 ⟨2400959708⟩, swap5, push2 ⟨391⟩, jump jump_391]
  have rd16 := evm_run_rfl rd15 with [jumpdest, push0, swap1, push1 ⟨16⟩, dup2, lt, push2 ⟨4001⟩, jumpiNT (by native_decide)]
  have rd17 := evm_run_rfl rd16 with [jumpdest, push1 ⟨32⟩, dup2, lt, push1 ⟨15⟩, dup3, gt, and, push2 ⟨3693⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [jumpdest, push1 ⟨48⟩, dup2, lt, push1 ⟨31⟩, dup3, gt, and, push2 ⟨3385⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [jumpdest, push1 ⟨64⟩, dup2, lt, push1 ⟨47⟩, dup3, gt, and, push2 ⟨3077⟩, jumpiT (by native_decide) jump_3077]
  have rd20 := evm_run_rfl rd19 with [jumpdest, push1 ⟨48⟩, dup2, sub, dup1, push0, eq, push2 ⟨3374⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [dup1, push1 ⟨1⟩, eq, push2 ⟨3363⟩, jumpiNT (by native_decide)]
  have rd22 := evm_run_rfl rd21 with [dup1, push1 ⟨2⟩, eq, push2 ⟨3352⟩, jumpiT (by native_decide) jump_3352]
  have rd23 := evm_run_rfl rd22 with [jumpdest, pop, swap1, pop, push1 ⟨11⟩, swap1, push2 ⟨3207⟩, jump jump_3207]
  have rd24 := evm_run_rfl rd23 with [jumpdest, push2 ⟨444⟩, jump jump_444]
  have rd25 := evm_run_rfl rd24 with [jumpdest, push1 ⟨63⟩, dup2, gt, push2 ⟨2769⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1877⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1431⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [dup1, push1 ⟨3⟩, eq, push2 ⟨985⟩, jumpiT (by native_decide) jump_985]
  have rd30 := evm_run_rfl rd29 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨1412⟩, jumpiNT (by native_decide)]
  have rd31 := evm_run_rfl rd30 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1393⟩, jumpiNT (by native_decide)]
  have rd32 := evm_run_rfl rd31 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1374⟩, jumpiT (by native_decide) jump_1374]
  have rd33 := evm_run_rfl rd32 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨14⟩, swap8, swap2, swap3, pop, pop, push2 ⟨1119⟩, jump jump_1119]
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

theorem runtime_leftRoundHelper_51 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 51 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 3 3).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 3 3).aw
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
  have rd12 := evm_run_rfl rd11 with [pop, dup3, push1 ⟨1⟩, eq, push2 ⟨4081⟩, jumpiNT (by native_decide)]
  have rd13 := evm_run_rfl rd12 with [dup3, push1 ⟨2⟩, eq, push2 ⟨4058⟩, jumpiNT (by native_decide)]
  have rd14 := evm_run_rfl rd13 with [pop, pop, dup1, push1 ⟨3⟩, eq, push2 ⟨4032⟩, jumpiT (by native_decide) jump_4032]
  have rd15 := evm_run_rfl rd14 with [jumpdest, pop, swap5, pop, swap3, pop, dup14, dup11, dup1, not, dup14, and, swap2, and, or, swap3, push4 ⟨2400959708⟩, swap5, push2 ⟨391⟩, jump jump_391]
  have rd16 := evm_run_rfl rd15 with [jumpdest, push0, swap1, push1 ⟨16⟩, dup2, lt, push2 ⟨4001⟩, jumpiNT (by native_decide)]
  have rd17 := evm_run_rfl rd16 with [jumpdest, push1 ⟨32⟩, dup2, lt, push1 ⟨15⟩, dup3, gt, and, push2 ⟨3693⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [jumpdest, push1 ⟨48⟩, dup2, lt, push1 ⟨31⟩, dup3, gt, and, push2 ⟨3385⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [jumpdest, push1 ⟨64⟩, dup2, lt, push1 ⟨47⟩, dup3, gt, and, push2 ⟨3077⟩, jumpiT (by native_decide) jump_3077]
  have rd20 := evm_run_rfl rd19 with [jumpdest, push1 ⟨48⟩, dup2, sub, dup1, push0, eq, push2 ⟨3374⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [dup1, push1 ⟨1⟩, eq, push2 ⟨3363⟩, jumpiNT (by native_decide)]
  have rd22 := evm_run_rfl rd21 with [dup1, push1 ⟨2⟩, eq, push2 ⟨3352⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨3⟩, eq, push2 ⟨3342⟩, jumpiT (by native_decide) jump_3342]
  have rd24 := evm_run_rfl rd23 with [jumpdest, pop, swap1, pop, dup14, swap1, push2 ⟨3207⟩, jump jump_3207]
  have rd25 := evm_run_rfl rd24 with [jumpdest, push2 ⟨444⟩, jump jump_444]
  have rd26 := evm_run_rfl rd25 with [jumpdest, push1 ⟨63⟩, dup2, gt, push2 ⟨2769⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1877⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1431⟩, jumpiNT (by native_decide)]
  have rd30 := evm_run_rfl rd29 with [dup1, push1 ⟨3⟩, eq, push2 ⟨985⟩, jumpiT (by native_decide) jump_985]
  have rd31 := evm_run_rfl rd30 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨1412⟩, jumpiNT (by native_decide)]
  have rd32 := evm_run_rfl rd31 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1393⟩, jumpiNT (by native_decide)]
  have rd33 := evm_run_rfl rd32 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1374⟩, jumpiNT (by native_decide)]
  have rd34 := evm_run_rfl rd33 with [dup1, push1 ⟨3⟩, eq, push2 ⟨1355⟩, jumpiT (by native_decide) jump_1355]
  have rd35 := evm_run_rfl rd34 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨15⟩, swap8, swap2, swap3, pop, pop, push2 ⟨1119⟩, jump jump_1119]
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

theorem runtime_leftRoundHelper_52 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 52 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 3 4).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 3 4).aw
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
  have rd12 := evm_run_rfl rd11 with [pop, dup3, push1 ⟨1⟩, eq, push2 ⟨4081⟩, jumpiNT (by native_decide)]
  have rd13 := evm_run_rfl rd12 with [dup3, push1 ⟨2⟩, eq, push2 ⟨4058⟩, jumpiNT (by native_decide)]
  have rd14 := evm_run_rfl rd13 with [pop, pop, dup1, push1 ⟨3⟩, eq, push2 ⟨4032⟩, jumpiT (by native_decide) jump_4032]
  have rd15 := evm_run_rfl rd14 with [jumpdest, pop, swap5, pop, swap3, pop, dup14, dup11, dup1, not, dup14, and, swap2, and, or, swap3, push4 ⟨2400959708⟩, swap5, push2 ⟨391⟩, jump jump_391]
  have rd16 := evm_run_rfl rd15 with [jumpdest, push0, swap1, push1 ⟨16⟩, dup2, lt, push2 ⟨4001⟩, jumpiNT (by native_decide)]
  have rd17 := evm_run_rfl rd16 with [jumpdest, push1 ⟨32⟩, dup2, lt, push1 ⟨15⟩, dup3, gt, and, push2 ⟨3693⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [jumpdest, push1 ⟨48⟩, dup2, lt, push1 ⟨31⟩, dup3, gt, and, push2 ⟨3385⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [jumpdest, push1 ⟨64⟩, dup2, lt, push1 ⟨47⟩, dup3, gt, and, push2 ⟨3077⟩, jumpiT (by native_decide) jump_3077]
  have rd20 := evm_run_rfl rd19 with [jumpdest, push1 ⟨48⟩, dup2, sub, dup1, push0, eq, push2 ⟨3374⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [dup1, push1 ⟨1⟩, eq, push2 ⟨3363⟩, jumpiNT (by native_decide)]
  have rd22 := evm_run_rfl rd21 with [dup1, push1 ⟨2⟩, eq, push2 ⟨3352⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨3⟩, eq, push2 ⟨3342⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup1, push1 ⟨4⟩, eq, push2 ⟨3332⟩, jumpiT (by native_decide) jump_3332]
  have rd25 := evm_run_rfl rd24 with [jumpdest, pop, swap1, pop, push0, swap1, push2 ⟨3207⟩, jump jump_3207]
  have rd26 := evm_run_rfl rd25 with [jumpdest, push2 ⟨444⟩, jump jump_444]
  have rd27 := evm_run_rfl rd26 with [jumpdest, push1 ⟨63⟩, dup2, gt, push2 ⟨2769⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1877⟩, jumpiNT (by native_decide)]
  have rd30 := evm_run_rfl rd29 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1431⟩, jumpiNT (by native_decide)]
  have rd31 := evm_run_rfl rd30 with [dup1, push1 ⟨3⟩, eq, push2 ⟨985⟩, jumpiT (by native_decide) jump_985]
  have rd32 := evm_run_rfl rd31 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨1412⟩, jumpiNT (by native_decide)]
  have rd33 := evm_run_rfl rd32 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1393⟩, jumpiNT (by native_decide)]
  have rd34 := evm_run_rfl rd33 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1374⟩, jumpiNT (by native_decide)]
  have rd35 := evm_run_rfl rd34 with [dup1, push1 ⟨3⟩, eq, push2 ⟨1355⟩, jumpiNT (by native_decide)]
  have rd36 := evm_run_rfl rd35 with [dup1, push1 ⟨4⟩, eq, push2 ⟨1336⟩, jumpiT (by native_decide) jump_1336]
  have rd37 := evm_run_rfl rd36 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨14⟩, swap8, swap2, swap3, pop, pop, push2 ⟨1119⟩, jump jump_1119]
  have rd38 := evm_run_rfl rd37 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨494⟩, jump jump_494]
  have rd39 := evm_run_rfl rd38 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd40 := RD.runtimeMload rd39 (by old_decode) (by simp; omega)
  have rd41 := evm_run_rfl rd40 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd42 := evm_run_rfl rd41 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_511]
  have rd43 := evm_run_rfl rd42 with [jumpdest, add, and, swap8, dup7]
  have rd44 := RD.runtimeMstore rd43 (by old_decode) (by simp; omega)
  have rd45 := evm_run_rfl rd44 with [push1 ⟨128⟩, dup7, add]
  have rd46 := RD.runtimeMstore rd45 (by old_decode) (by simp; omega)
  have rd47 := evm_run_rfl rd46 with [push2 ⟨268⟩, jump jump_268]
  have rd48 := evm_run_rfl rd47 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_526]
  have rd49 := evm_run_rfl rd48 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd50 := RD.runtimeMstore rd49 (by old_decode) (by simp; omega)
  have rd51 := evm_run_rfl rd50 with [push1 ⟨64⟩, dup3, add]
  have rd52 := RD.runtimeMstore rd51 (by old_decode) (by simp; omega)
  have rd53 := evm_run_rfl rd52 with [add]
  have rd54 := RD.runtimeMstore rd53 (by old_decode) (by simp; omega)
  have rd55 := evm_run_rfl rd54 with [jump jump_8991]
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
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd55⟩

theorem runtime_leftRoundHelper_53 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 53 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 3 5).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 3 5).aw
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
  have rd12 := evm_run_rfl rd11 with [pop, dup3, push1 ⟨1⟩, eq, push2 ⟨4081⟩, jumpiNT (by native_decide)]
  have rd13 := evm_run_rfl rd12 with [dup3, push1 ⟨2⟩, eq, push2 ⟨4058⟩, jumpiNT (by native_decide)]
  have rd14 := evm_run_rfl rd13 with [pop, pop, dup1, push1 ⟨3⟩, eq, push2 ⟨4032⟩, jumpiT (by native_decide) jump_4032]
  have rd15 := evm_run_rfl rd14 with [jumpdest, pop, swap5, pop, swap3, pop, dup14, dup11, dup1, not, dup14, and, swap2, and, or, swap3, push4 ⟨2400959708⟩, swap5, push2 ⟨391⟩, jump jump_391]
  have rd16 := evm_run_rfl rd15 with [jumpdest, push0, swap1, push1 ⟨16⟩, dup2, lt, push2 ⟨4001⟩, jumpiNT (by native_decide)]
  have rd17 := evm_run_rfl rd16 with [jumpdest, push1 ⟨32⟩, dup2, lt, push1 ⟨15⟩, dup3, gt, and, push2 ⟨3693⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [jumpdest, push1 ⟨48⟩, dup2, lt, push1 ⟨31⟩, dup3, gt, and, push2 ⟨3385⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [jumpdest, push1 ⟨64⟩, dup2, lt, push1 ⟨47⟩, dup3, gt, and, push2 ⟨3077⟩, jumpiT (by native_decide) jump_3077]
  have rd20 := evm_run_rfl rd19 with [jumpdest, push1 ⟨48⟩, dup2, sub, dup1, push0, eq, push2 ⟨3374⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [dup1, push1 ⟨1⟩, eq, push2 ⟨3363⟩, jumpiNT (by native_decide)]
  have rd22 := evm_run_rfl rd21 with [dup1, push1 ⟨2⟩, eq, push2 ⟨3352⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨3⟩, eq, push2 ⟨3342⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup1, push1 ⟨4⟩, eq, push2 ⟨3332⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨5⟩, eq, push2 ⟨3321⟩, jumpiT (by native_decide) jump_3321]
  have rd26 := evm_run_rfl rd25 with [jumpdest, pop, swap1, pop, push1 ⟨8⟩, swap1, push2 ⟨3207⟩, jump jump_3207]
  have rd27 := evm_run_rfl rd26 with [jumpdest, push2 ⟨444⟩, jump jump_444]
  have rd28 := evm_run_rfl rd27 with [jumpdest, push1 ⟨63⟩, dup2, gt, push2 ⟨2769⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiNT (by native_decide)]
  have rd30 := evm_run_rfl rd29 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1877⟩, jumpiNT (by native_decide)]
  have rd31 := evm_run_rfl rd30 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1431⟩, jumpiNT (by native_decide)]
  have rd32 := evm_run_rfl rd31 with [dup1, push1 ⟨3⟩, eq, push2 ⟨985⟩, jumpiT (by native_decide) jump_985]
  have rd33 := evm_run_rfl rd32 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨1412⟩, jumpiNT (by native_decide)]
  have rd34 := evm_run_rfl rd33 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1393⟩, jumpiNT (by native_decide)]
  have rd35 := evm_run_rfl rd34 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1374⟩, jumpiNT (by native_decide)]
  have rd36 := evm_run_rfl rd35 with [dup1, push1 ⟨3⟩, eq, push2 ⟨1355⟩, jumpiNT (by native_decide)]
  have rd37 := evm_run_rfl rd36 with [dup1, push1 ⟨4⟩, eq, push2 ⟨1336⟩, jumpiNT (by native_decide)]
  have rd38 := evm_run_rfl rd37 with [dup1, push1 ⟨5⟩, eq, push2 ⟨1317⟩, jumpiT (by native_decide) jump_1317]
  have rd39 := evm_run_rfl rd38 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨15⟩, swap8, swap2, swap3, pop, pop, push2 ⟨1119⟩, jump jump_1119]
  have rd40 := evm_run_rfl rd39 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨494⟩, jump jump_494]
  have rd41 := evm_run_rfl rd40 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd42 := RD.runtimeMload rd41 (by old_decode) (by simp; omega)
  have rd43 := evm_run_rfl rd42 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd44 := evm_run_rfl rd43 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_511]
  have rd45 := evm_run_rfl rd44 with [jumpdest, add, and, swap8, dup7]
  have rd46 := RD.runtimeMstore rd45 (by old_decode) (by simp; omega)
  have rd47 := evm_run_rfl rd46 with [push1 ⟨128⟩, dup7, add]
  have rd48 := RD.runtimeMstore rd47 (by old_decode) (by simp; omega)
  have rd49 := evm_run_rfl rd48 with [push2 ⟨268⟩, jump jump_268]
  have rd50 := evm_run_rfl rd49 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_526]
  have rd51 := evm_run_rfl rd50 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd52 := RD.runtimeMstore rd51 (by old_decode) (by simp; omega)
  have rd53 := evm_run_rfl rd52 with [push1 ⟨64⟩, dup3, add]
  have rd54 := RD.runtimeMstore rd53 (by old_decode) (by simp; omega)
  have rd55 := evm_run_rfl rd54 with [add]
  have rd56 := RD.runtimeMstore rd55 (by old_decode) (by simp; omega)
  have rd57 := evm_run_rfl rd56 with [jump jump_8991]
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
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd57⟩

theorem runtime_leftRoundHelper_54 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 54 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 3 6).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 3 6).aw
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
  have rd12 := evm_run_rfl rd11 with [pop, dup3, push1 ⟨1⟩, eq, push2 ⟨4081⟩, jumpiNT (by native_decide)]
  have rd13 := evm_run_rfl rd12 with [dup3, push1 ⟨2⟩, eq, push2 ⟨4058⟩, jumpiNT (by native_decide)]
  have rd14 := evm_run_rfl rd13 with [pop, pop, dup1, push1 ⟨3⟩, eq, push2 ⟨4032⟩, jumpiT (by native_decide) jump_4032]
  have rd15 := evm_run_rfl rd14 with [jumpdest, pop, swap5, pop, swap3, pop, dup14, dup11, dup1, not, dup14, and, swap2, and, or, swap3, push4 ⟨2400959708⟩, swap5, push2 ⟨391⟩, jump jump_391]
  have rd16 := evm_run_rfl rd15 with [jumpdest, push0, swap1, push1 ⟨16⟩, dup2, lt, push2 ⟨4001⟩, jumpiNT (by native_decide)]
  have rd17 := evm_run_rfl rd16 with [jumpdest, push1 ⟨32⟩, dup2, lt, push1 ⟨15⟩, dup3, gt, and, push2 ⟨3693⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [jumpdest, push1 ⟨48⟩, dup2, lt, push1 ⟨31⟩, dup3, gt, and, push2 ⟨3385⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [jumpdest, push1 ⟨64⟩, dup2, lt, push1 ⟨47⟩, dup3, gt, and, push2 ⟨3077⟩, jumpiT (by native_decide) jump_3077]
  have rd20 := evm_run_rfl rd19 with [jumpdest, push1 ⟨48⟩, dup2, sub, dup1, push0, eq, push2 ⟨3374⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [dup1, push1 ⟨1⟩, eq, push2 ⟨3363⟩, jumpiNT (by native_decide)]
  have rd22 := evm_run_rfl rd21 with [dup1, push1 ⟨2⟩, eq, push2 ⟨3352⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨3⟩, eq, push2 ⟨3342⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup1, push1 ⟨4⟩, eq, push2 ⟨3332⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨5⟩, eq, push2 ⟨3321⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup1, push1 ⟨6⟩, eq, push2 ⟨3310⟩, jumpiT (by native_decide) jump_3310]
  have rd27 := evm_run_rfl rd26 with [jumpdest, pop, swap1, pop, push1 ⟨12⟩, swap1, push2 ⟨3207⟩, jump jump_3207]
  have rd28 := evm_run_rfl rd27 with [jumpdest, push2 ⟨444⟩, jump jump_444]
  have rd29 := evm_run_rfl rd28 with [jumpdest, push1 ⟨63⟩, dup2, gt, push2 ⟨2769⟩, jumpiNT (by native_decide)]
  have rd30 := evm_run_rfl rd29 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiNT (by native_decide)]
  have rd31 := evm_run_rfl rd30 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1877⟩, jumpiNT (by native_decide)]
  have rd32 := evm_run_rfl rd31 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1431⟩, jumpiNT (by native_decide)]
  have rd33 := evm_run_rfl rd32 with [dup1, push1 ⟨3⟩, eq, push2 ⟨985⟩, jumpiT (by native_decide) jump_985]
  have rd34 := evm_run_rfl rd33 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨1412⟩, jumpiNT (by native_decide)]
  have rd35 := evm_run_rfl rd34 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1393⟩, jumpiNT (by native_decide)]
  have rd36 := evm_run_rfl rd35 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1374⟩, jumpiNT (by native_decide)]
  have rd37 := evm_run_rfl rd36 with [dup1, push1 ⟨3⟩, eq, push2 ⟨1355⟩, jumpiNT (by native_decide)]
  have rd38 := evm_run_rfl rd37 with [dup1, push1 ⟨4⟩, eq, push2 ⟨1336⟩, jumpiNT (by native_decide)]
  have rd39 := evm_run_rfl rd38 with [dup1, push1 ⟨5⟩, eq, push2 ⟨1317⟩, jumpiNT (by native_decide)]
  have rd40 := evm_run_rfl rd39 with [dup1, push1 ⟨6⟩, eq, push2 ⟨1298⟩, jumpiT (by native_decide) jump_1298]
  have rd41 := evm_run_rfl rd40 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨9⟩, swap8, swap2, swap3, pop, pop, push2 ⟨1119⟩, jump jump_1119]
  have rd42 := evm_run_rfl rd41 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨494⟩, jump jump_494]
  have rd43 := evm_run_rfl rd42 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd44 := RD.runtimeMload rd43 (by old_decode) (by simp; omega)
  have rd45 := evm_run_rfl rd44 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd46 := evm_run_rfl rd45 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_511]
  have rd47 := evm_run_rfl rd46 with [jumpdest, add, and, swap8, dup7]
  have rd48 := RD.runtimeMstore rd47 (by old_decode) (by simp; omega)
  have rd49 := evm_run_rfl rd48 with [push1 ⟨128⟩, dup7, add]
  have rd50 := RD.runtimeMstore rd49 (by old_decode) (by simp; omega)
  have rd51 := evm_run_rfl rd50 with [push2 ⟨268⟩, jump jump_268]
  have rd52 := evm_run_rfl rd51 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_526]
  have rd53 := evm_run_rfl rd52 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd54 := RD.runtimeMstore rd53 (by old_decode) (by simp; omega)
  have rd55 := evm_run_rfl rd54 with [push1 ⟨64⟩, dup3, add]
  have rd56 := RD.runtimeMstore rd55 (by old_decode) (by simp; omega)
  have rd57 := evm_run_rfl rd56 with [add]
  have rd58 := RD.runtimeMstore rd57 (by old_decode) (by simp; omega)
  have rd59 := evm_run_rfl rd58 with [jump jump_8991]
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
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd59⟩

theorem runtime_leftRoundHelper_55 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 55 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 3 7).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 3 7).aw
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
  have rd12 := evm_run_rfl rd11 with [pop, dup3, push1 ⟨1⟩, eq, push2 ⟨4081⟩, jumpiNT (by native_decide)]
  have rd13 := evm_run_rfl rd12 with [dup3, push1 ⟨2⟩, eq, push2 ⟨4058⟩, jumpiNT (by native_decide)]
  have rd14 := evm_run_rfl rd13 with [pop, pop, dup1, push1 ⟨3⟩, eq, push2 ⟨4032⟩, jumpiT (by native_decide) jump_4032]
  have rd15 := evm_run_rfl rd14 with [jumpdest, pop, swap5, pop, swap3, pop, dup14, dup11, dup1, not, dup14, and, swap2, and, or, swap3, push4 ⟨2400959708⟩, swap5, push2 ⟨391⟩, jump jump_391]
  have rd16 := evm_run_rfl rd15 with [jumpdest, push0, swap1, push1 ⟨16⟩, dup2, lt, push2 ⟨4001⟩, jumpiNT (by native_decide)]
  have rd17 := evm_run_rfl rd16 with [jumpdest, push1 ⟨32⟩, dup2, lt, push1 ⟨15⟩, dup3, gt, and, push2 ⟨3693⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [jumpdest, push1 ⟨48⟩, dup2, lt, push1 ⟨31⟩, dup3, gt, and, push2 ⟨3385⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [jumpdest, push1 ⟨64⟩, dup2, lt, push1 ⟨47⟩, dup3, gt, and, push2 ⟨3077⟩, jumpiT (by native_decide) jump_3077]
  have rd20 := evm_run_rfl rd19 with [jumpdest, push1 ⟨48⟩, dup2, sub, dup1, push0, eq, push2 ⟨3374⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [dup1, push1 ⟨1⟩, eq, push2 ⟨3363⟩, jumpiNT (by native_decide)]
  have rd22 := evm_run_rfl rd21 with [dup1, push1 ⟨2⟩, eq, push2 ⟨3352⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨3⟩, eq, push2 ⟨3342⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup1, push1 ⟨4⟩, eq, push2 ⟨3332⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨5⟩, eq, push2 ⟨3321⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup1, push1 ⟨6⟩, eq, push2 ⟨3310⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨7⟩, eq, push2 ⟨3299⟩, jumpiT (by native_decide) jump_3299]
  have rd28 := evm_run_rfl rd27 with [jumpdest, pop, swap1, pop, push1 ⟨4⟩, swap1, push2 ⟨3207⟩, jump jump_3207]
  have rd29 := evm_run_rfl rd28 with [jumpdest, push2 ⟨444⟩, jump jump_444]
  have rd30 := evm_run_rfl rd29 with [jumpdest, push1 ⟨63⟩, dup2, gt, push2 ⟨2769⟩, jumpiNT (by native_decide)]
  have rd31 := evm_run_rfl rd30 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiNT (by native_decide)]
  have rd32 := evm_run_rfl rd31 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1877⟩, jumpiNT (by native_decide)]
  have rd33 := evm_run_rfl rd32 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1431⟩, jumpiNT (by native_decide)]
  have rd34 := evm_run_rfl rd33 with [dup1, push1 ⟨3⟩, eq, push2 ⟨985⟩, jumpiT (by native_decide) jump_985]
  have rd35 := evm_run_rfl rd34 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨1412⟩, jumpiNT (by native_decide)]
  have rd36 := evm_run_rfl rd35 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1393⟩, jumpiNT (by native_decide)]
  have rd37 := evm_run_rfl rd36 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1374⟩, jumpiNT (by native_decide)]
  have rd38 := evm_run_rfl rd37 with [dup1, push1 ⟨3⟩, eq, push2 ⟨1355⟩, jumpiNT (by native_decide)]
  have rd39 := evm_run_rfl rd38 with [dup1, push1 ⟨4⟩, eq, push2 ⟨1336⟩, jumpiNT (by native_decide)]
  have rd40 := evm_run_rfl rd39 with [dup1, push1 ⟨5⟩, eq, push2 ⟨1317⟩, jumpiNT (by native_decide)]
  have rd41 := evm_run_rfl rd40 with [dup1, push1 ⟨6⟩, eq, push2 ⟨1298⟩, jumpiNT (by native_decide)]
  have rd42 := evm_run_rfl rd41 with [dup1, push1 ⟨7⟩, eq, push2 ⟨1279⟩, jumpiT (by native_decide) jump_1279]
  have rd43 := evm_run_rfl rd42 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨8⟩, swap8, swap2, swap3, pop, pop, push2 ⟨1119⟩, jump jump_1119]
  have rd44 := evm_run_rfl rd43 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨494⟩, jump jump_494]
  have rd45 := evm_run_rfl rd44 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd46 := RD.runtimeMload rd45 (by old_decode) (by simp; omega)
  have rd47 := evm_run_rfl rd46 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd48 := evm_run_rfl rd47 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_511]
  have rd49 := evm_run_rfl rd48 with [jumpdest, add, and, swap8, dup7]
  have rd50 := RD.runtimeMstore rd49 (by old_decode) (by simp; omega)
  have rd51 := evm_run_rfl rd50 with [push1 ⟨128⟩, dup7, add]
  have rd52 := RD.runtimeMstore rd51 (by old_decode) (by simp; omega)
  have rd53 := evm_run_rfl rd52 with [push2 ⟨268⟩, jump jump_268]
  have rd54 := evm_run_rfl rd53 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_526]
  have rd55 := evm_run_rfl rd54 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd56 := RD.runtimeMstore rd55 (by old_decode) (by simp; omega)
  have rd57 := evm_run_rfl rd56 with [push1 ⟨64⟩, dup3, add]
  have rd58 := RD.runtimeMstore rd57 (by old_decode) (by simp; omega)
  have rd59 := evm_run_rfl rd58 with [add]
  have rd60 := RD.runtimeMstore rd59 (by old_decode) (by simp; omega)
  have rd61 := evm_run_rfl rd60 with [jump jump_8991]
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
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd61⟩

theorem runtime_leftRoundHelper_56 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 56 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 3 8).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 3 8).aw
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
  have rd12 := evm_run_rfl rd11 with [pop, dup3, push1 ⟨1⟩, eq, push2 ⟨4081⟩, jumpiNT (by native_decide)]
  have rd13 := evm_run_rfl rd12 with [dup3, push1 ⟨2⟩, eq, push2 ⟨4058⟩, jumpiNT (by native_decide)]
  have rd14 := evm_run_rfl rd13 with [pop, pop, dup1, push1 ⟨3⟩, eq, push2 ⟨4032⟩, jumpiT (by native_decide) jump_4032]
  have rd15 := evm_run_rfl rd14 with [jumpdest, pop, swap5, pop, swap3, pop, dup14, dup11, dup1, not, dup14, and, swap2, and, or, swap3, push4 ⟨2400959708⟩, swap5, push2 ⟨391⟩, jump jump_391]
  have rd16 := evm_run_rfl rd15 with [jumpdest, push0, swap1, push1 ⟨16⟩, dup2, lt, push2 ⟨4001⟩, jumpiNT (by native_decide)]
  have rd17 := evm_run_rfl rd16 with [jumpdest, push1 ⟨32⟩, dup2, lt, push1 ⟨15⟩, dup3, gt, and, push2 ⟨3693⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [jumpdest, push1 ⟨48⟩, dup2, lt, push1 ⟨31⟩, dup3, gt, and, push2 ⟨3385⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [jumpdest, push1 ⟨64⟩, dup2, lt, push1 ⟨47⟩, dup3, gt, and, push2 ⟨3077⟩, jumpiT (by native_decide) jump_3077]
  have rd20 := evm_run_rfl rd19 with [jumpdest, push1 ⟨48⟩, dup2, sub, dup1, push0, eq, push2 ⟨3374⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [dup1, push1 ⟨1⟩, eq, push2 ⟨3363⟩, jumpiNT (by native_decide)]
  have rd22 := evm_run_rfl rd21 with [dup1, push1 ⟨2⟩, eq, push2 ⟨3352⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨3⟩, eq, push2 ⟨3342⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup1, push1 ⟨4⟩, eq, push2 ⟨3332⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨5⟩, eq, push2 ⟨3321⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup1, push1 ⟨6⟩, eq, push2 ⟨3310⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨7⟩, eq, push2 ⟨3299⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨8⟩, eq, push2 ⟨3288⟩, jumpiT (by native_decide) jump_3288]
  have rd29 := evm_run_rfl rd28 with [jumpdest, pop, swap1, pop, push1 ⟨13⟩, swap1, push2 ⟨3207⟩, jump jump_3207]
  have rd30 := evm_run_rfl rd29 with [jumpdest, push2 ⟨444⟩, jump jump_444]
  have rd31 := evm_run_rfl rd30 with [jumpdest, push1 ⟨63⟩, dup2, gt, push2 ⟨2769⟩, jumpiNT (by native_decide)]
  have rd32 := evm_run_rfl rd31 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiNT (by native_decide)]
  have rd33 := evm_run_rfl rd32 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1877⟩, jumpiNT (by native_decide)]
  have rd34 := evm_run_rfl rd33 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1431⟩, jumpiNT (by native_decide)]
  have rd35 := evm_run_rfl rd34 with [dup1, push1 ⟨3⟩, eq, push2 ⟨985⟩, jumpiT (by native_decide) jump_985]
  have rd36 := evm_run_rfl rd35 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨1412⟩, jumpiNT (by native_decide)]
  have rd37 := evm_run_rfl rd36 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1393⟩, jumpiNT (by native_decide)]
  have rd38 := evm_run_rfl rd37 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1374⟩, jumpiNT (by native_decide)]
  have rd39 := evm_run_rfl rd38 with [dup1, push1 ⟨3⟩, eq, push2 ⟨1355⟩, jumpiNT (by native_decide)]
  have rd40 := evm_run_rfl rd39 with [dup1, push1 ⟨4⟩, eq, push2 ⟨1336⟩, jumpiNT (by native_decide)]
  have rd41 := evm_run_rfl rd40 with [dup1, push1 ⟨5⟩, eq, push2 ⟨1317⟩, jumpiNT (by native_decide)]
  have rd42 := evm_run_rfl rd41 with [dup1, push1 ⟨6⟩, eq, push2 ⟨1298⟩, jumpiNT (by native_decide)]
  have rd43 := evm_run_rfl rd42 with [dup1, push1 ⟨7⟩, eq, push2 ⟨1279⟩, jumpiNT (by native_decide)]
  have rd44 := evm_run_rfl rd43 with [dup1, push1 ⟨8⟩, eq, push2 ⟨1260⟩, jumpiT (by native_decide) jump_1260]
  have rd45 := evm_run_rfl rd44 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨9⟩, swap8, swap2, swap3, pop, pop, push2 ⟨1119⟩, jump jump_1119]
  have rd46 := evm_run_rfl rd45 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨494⟩, jump jump_494]
  have rd47 := evm_run_rfl rd46 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd48 := RD.runtimeMload rd47 (by old_decode) (by simp; omega)
  have rd49 := evm_run_rfl rd48 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd50 := evm_run_rfl rd49 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_511]
  have rd51 := evm_run_rfl rd50 with [jumpdest, add, and, swap8, dup7]
  have rd52 := RD.runtimeMstore rd51 (by old_decode) (by simp; omega)
  have rd53 := evm_run_rfl rd52 with [push1 ⟨128⟩, dup7, add]
  have rd54 := RD.runtimeMstore rd53 (by old_decode) (by simp; omega)
  have rd55 := evm_run_rfl rd54 with [push2 ⟨268⟩, jump jump_268]
  have rd56 := evm_run_rfl rd55 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_526]
  have rd57 := evm_run_rfl rd56 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd58 := RD.runtimeMstore rd57 (by old_decode) (by simp; omega)
  have rd59 := evm_run_rfl rd58 with [push1 ⟨64⟩, dup3, add]
  have rd60 := RD.runtimeMstore rd59 (by old_decode) (by simp; omega)
  have rd61 := evm_run_rfl rd60 with [add]
  have rd62 := RD.runtimeMstore rd61 (by old_decode) (by simp; omega)
  have rd63 := evm_run_rfl rd62 with [jump jump_8991]
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
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd63⟩

theorem runtime_leftRoundHelper_57 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 57 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 3 9).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 3 9).aw
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
  have rd12 := evm_run_rfl rd11 with [pop, dup3, push1 ⟨1⟩, eq, push2 ⟨4081⟩, jumpiNT (by native_decide)]
  have rd13 := evm_run_rfl rd12 with [dup3, push1 ⟨2⟩, eq, push2 ⟨4058⟩, jumpiNT (by native_decide)]
  have rd14 := evm_run_rfl rd13 with [pop, pop, dup1, push1 ⟨3⟩, eq, push2 ⟨4032⟩, jumpiT (by native_decide) jump_4032]
  have rd15 := evm_run_rfl rd14 with [jumpdest, pop, swap5, pop, swap3, pop, dup14, dup11, dup1, not, dup14, and, swap2, and, or, swap3, push4 ⟨2400959708⟩, swap5, push2 ⟨391⟩, jump jump_391]
  have rd16 := evm_run_rfl rd15 with [jumpdest, push0, swap1, push1 ⟨16⟩, dup2, lt, push2 ⟨4001⟩, jumpiNT (by native_decide)]
  have rd17 := evm_run_rfl rd16 with [jumpdest, push1 ⟨32⟩, dup2, lt, push1 ⟨15⟩, dup3, gt, and, push2 ⟨3693⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [jumpdest, push1 ⟨48⟩, dup2, lt, push1 ⟨31⟩, dup3, gt, and, push2 ⟨3385⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [jumpdest, push1 ⟨64⟩, dup2, lt, push1 ⟨47⟩, dup3, gt, and, push2 ⟨3077⟩, jumpiT (by native_decide) jump_3077]
  have rd20 := evm_run_rfl rd19 with [jumpdest, push1 ⟨48⟩, dup2, sub, dup1, push0, eq, push2 ⟨3374⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [dup1, push1 ⟨1⟩, eq, push2 ⟨3363⟩, jumpiNT (by native_decide)]
  have rd22 := evm_run_rfl rd21 with [dup1, push1 ⟨2⟩, eq, push2 ⟨3352⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨3⟩, eq, push2 ⟨3342⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup1, push1 ⟨4⟩, eq, push2 ⟨3332⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨5⟩, eq, push2 ⟨3321⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup1, push1 ⟨6⟩, eq, push2 ⟨3310⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨7⟩, eq, push2 ⟨3299⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨8⟩, eq, push2 ⟨3288⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [dup1, push1 ⟨9⟩, eq, push2 ⟨3277⟩, jumpiT (by native_decide) jump_3277]
  have rd30 := evm_run_rfl rd29 with [jumpdest, pop, swap1, pop, push1 ⟨3⟩, swap1, push2 ⟨3207⟩, jump jump_3207]
  have rd31 := evm_run_rfl rd30 with [jumpdest, push2 ⟨444⟩, jump jump_444]
  have rd32 := evm_run_rfl rd31 with [jumpdest, push1 ⟨63⟩, dup2, gt, push2 ⟨2769⟩, jumpiNT (by native_decide)]
  have rd33 := evm_run_rfl rd32 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiNT (by native_decide)]
  have rd34 := evm_run_rfl rd33 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1877⟩, jumpiNT (by native_decide)]
  have rd35 := evm_run_rfl rd34 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1431⟩, jumpiNT (by native_decide)]
  have rd36 := evm_run_rfl rd35 with [dup1, push1 ⟨3⟩, eq, push2 ⟨985⟩, jumpiT (by native_decide) jump_985]
  have rd37 := evm_run_rfl rd36 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨1412⟩, jumpiNT (by native_decide)]
  have rd38 := evm_run_rfl rd37 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1393⟩, jumpiNT (by native_decide)]
  have rd39 := evm_run_rfl rd38 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1374⟩, jumpiNT (by native_decide)]
  have rd40 := evm_run_rfl rd39 with [dup1, push1 ⟨3⟩, eq, push2 ⟨1355⟩, jumpiNT (by native_decide)]
  have rd41 := evm_run_rfl rd40 with [dup1, push1 ⟨4⟩, eq, push2 ⟨1336⟩, jumpiNT (by native_decide)]
  have rd42 := evm_run_rfl rd41 with [dup1, push1 ⟨5⟩, eq, push2 ⟨1317⟩, jumpiNT (by native_decide)]
  have rd43 := evm_run_rfl rd42 with [dup1, push1 ⟨6⟩, eq, push2 ⟨1298⟩, jumpiNT (by native_decide)]
  have rd44 := evm_run_rfl rd43 with [dup1, push1 ⟨7⟩, eq, push2 ⟨1279⟩, jumpiNT (by native_decide)]
  have rd45 := evm_run_rfl rd44 with [dup1, push1 ⟨8⟩, eq, push2 ⟨1260⟩, jumpiNT (by native_decide)]
  have rd46 := evm_run_rfl rd45 with [dup1, push1 ⟨9⟩, eq, push2 ⟨1241⟩, jumpiT (by native_decide) jump_1241]
  have rd47 := evm_run_rfl rd46 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨14⟩, swap8, swap2, swap3, pop, pop, push2 ⟨1119⟩, jump jump_1119]
  have rd48 := evm_run_rfl rd47 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨494⟩, jump jump_494]
  have rd49 := evm_run_rfl rd48 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd50 := RD.runtimeMload rd49 (by old_decode) (by simp; omega)
  have rd51 := evm_run_rfl rd50 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd52 := evm_run_rfl rd51 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_511]
  have rd53 := evm_run_rfl rd52 with [jumpdest, add, and, swap8, dup7]
  have rd54 := RD.runtimeMstore rd53 (by old_decode) (by simp; omega)
  have rd55 := evm_run_rfl rd54 with [push1 ⟨128⟩, dup7, add]
  have rd56 := RD.runtimeMstore rd55 (by old_decode) (by simp; omega)
  have rd57 := evm_run_rfl rd56 with [push2 ⟨268⟩, jump jump_268]
  have rd58 := evm_run_rfl rd57 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_526]
  have rd59 := evm_run_rfl rd58 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd60 := RD.runtimeMstore rd59 (by old_decode) (by simp; omega)
  have rd61 := evm_run_rfl rd60 with [push1 ⟨64⟩, dup3, add]
  have rd62 := RD.runtimeMstore rd61 (by old_decode) (by simp; omega)
  have rd63 := evm_run_rfl rd62 with [add]
  have rd64 := RD.runtimeMstore rd63 (by old_decode) (by simp; omega)
  have rd65 := evm_run_rfl rd64 with [jump jump_8991]
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
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd65⟩

theorem runtime_leftRoundHelper_58 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 58 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 3 10).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 3 10).aw
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
  have rd12 := evm_run_rfl rd11 with [pop, dup3, push1 ⟨1⟩, eq, push2 ⟨4081⟩, jumpiNT (by native_decide)]
  have rd13 := evm_run_rfl rd12 with [dup3, push1 ⟨2⟩, eq, push2 ⟨4058⟩, jumpiNT (by native_decide)]
  have rd14 := evm_run_rfl rd13 with [pop, pop, dup1, push1 ⟨3⟩, eq, push2 ⟨4032⟩, jumpiT (by native_decide) jump_4032]
  have rd15 := evm_run_rfl rd14 with [jumpdest, pop, swap5, pop, swap3, pop, dup14, dup11, dup1, not, dup14, and, swap2, and, or, swap3, push4 ⟨2400959708⟩, swap5, push2 ⟨391⟩, jump jump_391]
  have rd16 := evm_run_rfl rd15 with [jumpdest, push0, swap1, push1 ⟨16⟩, dup2, lt, push2 ⟨4001⟩, jumpiNT (by native_decide)]
  have rd17 := evm_run_rfl rd16 with [jumpdest, push1 ⟨32⟩, dup2, lt, push1 ⟨15⟩, dup3, gt, and, push2 ⟨3693⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [jumpdest, push1 ⟨48⟩, dup2, lt, push1 ⟨31⟩, dup3, gt, and, push2 ⟨3385⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [jumpdest, push1 ⟨64⟩, dup2, lt, push1 ⟨47⟩, dup3, gt, and, push2 ⟨3077⟩, jumpiT (by native_decide) jump_3077]
  have rd20 := evm_run_rfl rd19 with [jumpdest, push1 ⟨48⟩, dup2, sub, dup1, push0, eq, push2 ⟨3374⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [dup1, push1 ⟨1⟩, eq, push2 ⟨3363⟩, jumpiNT (by native_decide)]
  have rd22 := evm_run_rfl rd21 with [dup1, push1 ⟨2⟩, eq, push2 ⟨3352⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨3⟩, eq, push2 ⟨3342⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup1, push1 ⟨4⟩, eq, push2 ⟨3332⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨5⟩, eq, push2 ⟨3321⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup1, push1 ⟨6⟩, eq, push2 ⟨3310⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨7⟩, eq, push2 ⟨3299⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨8⟩, eq, push2 ⟨3288⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [dup1, push1 ⟨9⟩, eq, push2 ⟨3277⟩, jumpiNT (by native_decide)]
  have rd30 := evm_run_rfl rd29 with [dup16, dup2, eq, push2 ⟨3266⟩, jumpiT (by native_decide) jump_3266]
  have rd31 := evm_run_rfl rd30 with [jumpdest, pop, swap1, pop, push1 ⟨7⟩, swap1, push2 ⟨3207⟩, jump jump_3207]
  have rd32 := evm_run_rfl rd31 with [jumpdest, push2 ⟨444⟩, jump jump_444]
  have rd33 := evm_run_rfl rd32 with [jumpdest, push1 ⟨63⟩, dup2, gt, push2 ⟨2769⟩, jumpiNT (by native_decide)]
  have rd34 := evm_run_rfl rd33 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiNT (by native_decide)]
  have rd35 := evm_run_rfl rd34 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1877⟩, jumpiNT (by native_decide)]
  have rd36 := evm_run_rfl rd35 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1431⟩, jumpiNT (by native_decide)]
  have rd37 := evm_run_rfl rd36 with [dup1, push1 ⟨3⟩, eq, push2 ⟨985⟩, jumpiT (by native_decide) jump_985]
  have rd38 := evm_run_rfl rd37 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨1412⟩, jumpiNT (by native_decide)]
  have rd39 := evm_run_rfl rd38 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1393⟩, jumpiNT (by native_decide)]
  have rd40 := evm_run_rfl rd39 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1374⟩, jumpiNT (by native_decide)]
  have rd41 := evm_run_rfl rd40 with [dup1, push1 ⟨3⟩, eq, push2 ⟨1355⟩, jumpiNT (by native_decide)]
  have rd42 := evm_run_rfl rd41 with [dup1, push1 ⟨4⟩, eq, push2 ⟨1336⟩, jumpiNT (by native_decide)]
  have rd43 := evm_run_rfl rd42 with [dup1, push1 ⟨5⟩, eq, push2 ⟨1317⟩, jumpiNT (by native_decide)]
  have rd44 := evm_run_rfl rd43 with [dup1, push1 ⟨6⟩, eq, push2 ⟨1298⟩, jumpiNT (by native_decide)]
  have rd45 := evm_run_rfl rd44 with [dup1, push1 ⟨7⟩, eq, push2 ⟨1279⟩, jumpiNT (by native_decide)]
  have rd46 := evm_run_rfl rd45 with [dup1, push1 ⟨8⟩, eq, push2 ⟨1260⟩, jumpiNT (by native_decide)]
  have rd47 := evm_run_rfl rd46 with [dup1, push1 ⟨9⟩, eq, push2 ⟨1241⟩, jumpiNT (by native_decide)]
  have rd48 := evm_run_rfl rd47 with [dup1, dup15, eq, push2 ⟨1222⟩, jumpiT (by native_decide) jump_1222]
  have rd49 := evm_run_rfl rd48 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨5⟩, swap8, swap2, swap3, pop, pop, push2 ⟨1119⟩, jump jump_1119]
  have rd50 := evm_run_rfl rd49 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨494⟩, jump jump_494]
  have rd51 := evm_run_rfl rd50 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd52 := RD.runtimeMload rd51 (by old_decode) (by simp; omega)
  have rd53 := evm_run_rfl rd52 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd54 := evm_run_rfl rd53 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_511]
  have rd55 := evm_run_rfl rd54 with [jumpdest, add, and, swap8, dup7]
  have rd56 := RD.runtimeMstore rd55 (by old_decode) (by simp; omega)
  have rd57 := evm_run_rfl rd56 with [push1 ⟨128⟩, dup7, add]
  have rd58 := RD.runtimeMstore rd57 (by old_decode) (by simp; omega)
  have rd59 := evm_run_rfl rd58 with [push2 ⟨268⟩, jump jump_268]
  have rd60 := evm_run_rfl rd59 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_526]
  have rd61 := evm_run_rfl rd60 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd62 := RD.runtimeMstore rd61 (by old_decode) (by simp; omega)
  have rd63 := evm_run_rfl rd62 with [push1 ⟨64⟩, dup3, add]
  have rd64 := RD.runtimeMstore rd63 (by old_decode) (by simp; omega)
  have rd65 := evm_run_rfl rd64 with [add]
  have rd66 := RD.runtimeMstore rd65 (by old_decode) (by simp; omega)
  have rd67 := evm_run_rfl rd66 with [jump jump_8991]
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
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd67⟩

theorem runtime_leftRoundHelper_59 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 59 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 3 11).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 3 11).aw
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
  have rd12 := evm_run_rfl rd11 with [pop, dup3, push1 ⟨1⟩, eq, push2 ⟨4081⟩, jumpiNT (by native_decide)]
  have rd13 := evm_run_rfl rd12 with [dup3, push1 ⟨2⟩, eq, push2 ⟨4058⟩, jumpiNT (by native_decide)]
  have rd14 := evm_run_rfl rd13 with [pop, pop, dup1, push1 ⟨3⟩, eq, push2 ⟨4032⟩, jumpiT (by native_decide) jump_4032]
  have rd15 := evm_run_rfl rd14 with [jumpdest, pop, swap5, pop, swap3, pop, dup14, dup11, dup1, not, dup14, and, swap2, and, or, swap3, push4 ⟨2400959708⟩, swap5, push2 ⟨391⟩, jump jump_391]
  have rd16 := evm_run_rfl rd15 with [jumpdest, push0, swap1, push1 ⟨16⟩, dup2, lt, push2 ⟨4001⟩, jumpiNT (by native_decide)]
  have rd17 := evm_run_rfl rd16 with [jumpdest, push1 ⟨32⟩, dup2, lt, push1 ⟨15⟩, dup3, gt, and, push2 ⟨3693⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [jumpdest, push1 ⟨48⟩, dup2, lt, push1 ⟨31⟩, dup3, gt, and, push2 ⟨3385⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [jumpdest, push1 ⟨64⟩, dup2, lt, push1 ⟨47⟩, dup3, gt, and, push2 ⟨3077⟩, jumpiT (by native_decide) jump_3077]
  have rd20 := evm_run_rfl rd19 with [jumpdest, push1 ⟨48⟩, dup2, sub, dup1, push0, eq, push2 ⟨3374⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [dup1, push1 ⟨1⟩, eq, push2 ⟨3363⟩, jumpiNT (by native_decide)]
  have rd22 := evm_run_rfl rd21 with [dup1, push1 ⟨2⟩, eq, push2 ⟨3352⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨3⟩, eq, push2 ⟨3342⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup1, push1 ⟨4⟩, eq, push2 ⟨3332⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨5⟩, eq, push2 ⟨3321⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup1, push1 ⟨6⟩, eq, push2 ⟨3310⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨7⟩, eq, push2 ⟨3299⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨8⟩, eq, push2 ⟨3288⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [dup1, push1 ⟨9⟩, eq, push2 ⟨3277⟩, jumpiNT (by native_decide)]
  have rd30 := evm_run_rfl rd29 with [dup16, dup2, eq, push2 ⟨3266⟩, jumpiNT (by native_decide)]
  have rd31 := evm_run_rfl rd30 with [dup1, push1 ⟨11⟩, eq, push2 ⟨3255⟩, jumpiT (by native_decide) jump_3255]
  have rd32 := evm_run_rfl rd31 with [jumpdest, pop, swap1, pop, push1 ⟨15⟩, swap1, push2 ⟨3207⟩, jump jump_3207]
  have rd33 := evm_run_rfl rd32 with [jumpdest, push2 ⟨444⟩, jump jump_444]
  have rd34 := evm_run_rfl rd33 with [jumpdest, push1 ⟨63⟩, dup2, gt, push2 ⟨2769⟩, jumpiNT (by native_decide)]
  have rd35 := evm_run_rfl rd34 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiNT (by native_decide)]
  have rd36 := evm_run_rfl rd35 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1877⟩, jumpiNT (by native_decide)]
  have rd37 := evm_run_rfl rd36 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1431⟩, jumpiNT (by native_decide)]
  have rd38 := evm_run_rfl rd37 with [dup1, push1 ⟨3⟩, eq, push2 ⟨985⟩, jumpiT (by native_decide) jump_985]
  have rd39 := evm_run_rfl rd38 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨1412⟩, jumpiNT (by native_decide)]
  have rd40 := evm_run_rfl rd39 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1393⟩, jumpiNT (by native_decide)]
  have rd41 := evm_run_rfl rd40 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1374⟩, jumpiNT (by native_decide)]
  have rd42 := evm_run_rfl rd41 with [dup1, push1 ⟨3⟩, eq, push2 ⟨1355⟩, jumpiNT (by native_decide)]
  have rd43 := evm_run_rfl rd42 with [dup1, push1 ⟨4⟩, eq, push2 ⟨1336⟩, jumpiNT (by native_decide)]
  have rd44 := evm_run_rfl rd43 with [dup1, push1 ⟨5⟩, eq, push2 ⟨1317⟩, jumpiNT (by native_decide)]
  have rd45 := evm_run_rfl rd44 with [dup1, push1 ⟨6⟩, eq, push2 ⟨1298⟩, jumpiNT (by native_decide)]
  have rd46 := evm_run_rfl rd45 with [dup1, push1 ⟨7⟩, eq, push2 ⟨1279⟩, jumpiNT (by native_decide)]
  have rd47 := evm_run_rfl rd46 with [dup1, push1 ⟨8⟩, eq, push2 ⟨1260⟩, jumpiNT (by native_decide)]
  have rd48 := evm_run_rfl rd47 with [dup1, push1 ⟨9⟩, eq, push2 ⟨1241⟩, jumpiNT (by native_decide)]
  have rd49 := evm_run_rfl rd48 with [dup1, dup15, eq, push2 ⟨1222⟩, jumpiNT (by native_decide)]
  have rd50 := evm_run_rfl rd49 with [dup1, push1 ⟨11⟩, eq, push2 ⟨1203⟩, jumpiT (by native_decide) jump_1203]
  have rd51 := evm_run_rfl rd50 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨6⟩, swap8, swap2, swap3, pop, pop, push2 ⟨1119⟩, jump jump_1119]
  have rd52 := evm_run_rfl rd51 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨494⟩, jump jump_494]
  have rd53 := evm_run_rfl rd52 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd54 := RD.runtimeMload rd53 (by old_decode) (by simp; omega)
  have rd55 := evm_run_rfl rd54 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd56 := evm_run_rfl rd55 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_511]
  have rd57 := evm_run_rfl rd56 with [jumpdest, add, and, swap8, dup7]
  have rd58 := RD.runtimeMstore rd57 (by old_decode) (by simp; omega)
  have rd59 := evm_run_rfl rd58 with [push1 ⟨128⟩, dup7, add]
  have rd60 := RD.runtimeMstore rd59 (by old_decode) (by simp; omega)
  have rd61 := evm_run_rfl rd60 with [push2 ⟨268⟩, jump jump_268]
  have rd62 := evm_run_rfl rd61 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_526]
  have rd63 := evm_run_rfl rd62 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd64 := RD.runtimeMstore rd63 (by old_decode) (by simp; omega)
  have rd65 := evm_run_rfl rd64 with [push1 ⟨64⟩, dup3, add]
  have rd66 := RD.runtimeMstore rd65 (by old_decode) (by simp; omega)
  have rd67 := evm_run_rfl rd66 with [add]
  have rd68 := RD.runtimeMstore rd67 (by old_decode) (by simp; omega)
  have rd69 := evm_run_rfl rd68 with [jump jump_8991]
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
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd69⟩


end Ripemd160Old
