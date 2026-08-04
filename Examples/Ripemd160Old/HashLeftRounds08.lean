import Examples.Ripemd160Old.HashLeftRound0

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000
namespace Ripemd160Old
open Ripemd160

theorem runtime_leftRoundHelper_70 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 70 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 4 6).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 4 6).aw
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
  have rd14 := evm_run_rfl rd13 with [pop, pop, dup1, push1 ⟨3⟩, eq, push2 ⟨4032⟩, jumpiNT (by native_decide)]
  have rd15 := evm_run_rfl rd14 with [push1 ⟨4⟩, eq, push2 ⟨4010⟩, jumpiT (by native_decide) jump_4010]
  have rd16 := evm_run_rfl rd15 with [jumpdest, swap5, pop, swap3, pop, dup14, dup11, not, dup13, or, xor, swap3, push4 ⟨2840853838⟩, swap5, push2 ⟨391⟩, jump jump_391]
  have rd17 := evm_run_rfl rd16 with [jumpdest, push0, swap1, push1 ⟨16⟩, dup2, lt, push2 ⟨4001⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [jumpdest, push1 ⟨32⟩, dup2, lt, push1 ⟨15⟩, dup3, gt, and, push2 ⟨3693⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [jumpdest, push1 ⟨48⟩, dup2, lt, push1 ⟨31⟩, dup3, gt, and, push2 ⟨3385⟩, jumpiNT (by native_decide)]
  have rd20 := evm_run_rfl rd19 with [jumpdest, push1 ⟨64⟩, dup2, lt, push1 ⟨47⟩, dup3, gt, and, push2 ⟨3077⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [jumpdest, push1 ⟨63⟩, dup2, gt, push2 ⟨2769⟩, jumpiT (by native_decide) jump_2769]
  have rd22 := evm_run_rfl rd21 with [jumpdest, push1 ⟨64⟩, dup2, sub, dup1, push0, eq, push2 ⟨3066⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨1⟩, eq, push2 ⟨3056⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup1, push1 ⟨2⟩, eq, push2 ⟨3045⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨3⟩, eq, push2 ⟨3034⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup1, push1 ⟨4⟩, eq, push2 ⟨3023⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨5⟩, eq, push2 ⟨3012⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨6⟩, eq, push2 ⟨3001⟩, jumpiT (by native_decide) jump_3001]
  have rd29 := evm_run_rfl rd28 with [jumpdest, pop, swap1, pop, push1 ⟨2⟩, swap1, push2 ⟨2899⟩, jump jump_2899]
  have rd30 := evm_run_rfl rd29 with [jumpdest, push2 ⟨453⟩, jump jump_453]
  have rd31 := evm_run_rfl rd30 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiNT (by native_decide)]
  have rd32 := evm_run_rfl rd31 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1877⟩, jumpiNT (by native_decide)]
  have rd33 := evm_run_rfl rd32 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1431⟩, jumpiNT (by native_decide)]
  have rd34 := evm_run_rfl rd33 with [dup1, push1 ⟨3⟩, eq, push2 ⟨985⟩, jumpiNT (by native_decide)]
  have rd35 := evm_run_rfl rd34 with [push1 ⟨4⟩, eq, push2 ⟨540⟩, jumpiT (by native_decide) jump_540]
  have rd36 := evm_run_rfl rd35 with [jumpdest, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨966⟩, jumpiNT (by native_decide)]
  have rd37 := evm_run_rfl rd36 with [dup1, push1 ⟨1⟩, eq, push2 ⟨947⟩, jumpiNT (by native_decide)]
  have rd38 := evm_run_rfl rd37 with [dup1, push1 ⟨2⟩, eq, push2 ⟨928⟩, jumpiNT (by native_decide)]
  have rd39 := evm_run_rfl rd38 with [dup1, push1 ⟨3⟩, eq, push2 ⟨909⟩, jumpiNT (by native_decide)]
  have rd40 := evm_run_rfl rd39 with [dup1, push1 ⟨4⟩, eq, push2 ⟨890⟩, jumpiNT (by native_decide)]
  have rd41 := evm_run_rfl rd40 with [dup1, push1 ⟨5⟩, eq, push2 ⟨871⟩, jumpiNT (by native_decide)]
  have rd42 := evm_run_rfl rd41 with [dup1, push1 ⟨6⟩, eq, push2 ⟨852⟩, jumpiT (by native_decide) jump_852]
  have rd43 := evm_run_rfl rd42 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨13⟩, swap8, swap2, swap3, pop, pop, push2 ⟨673⟩, jump jump_673]
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

theorem runtime_leftRoundHelper_71 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 71 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 4 7).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 4 7).aw
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
  have rd14 := evm_run_rfl rd13 with [pop, pop, dup1, push1 ⟨3⟩, eq, push2 ⟨4032⟩, jumpiNT (by native_decide)]
  have rd15 := evm_run_rfl rd14 with [push1 ⟨4⟩, eq, push2 ⟨4010⟩, jumpiT (by native_decide) jump_4010]
  have rd16 := evm_run_rfl rd15 with [jumpdest, swap5, pop, swap3, pop, dup14, dup11, not, dup13, or, xor, swap3, push4 ⟨2840853838⟩, swap5, push2 ⟨391⟩, jump jump_391]
  have rd17 := evm_run_rfl rd16 with [jumpdest, push0, swap1, push1 ⟨16⟩, dup2, lt, push2 ⟨4001⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [jumpdest, push1 ⟨32⟩, dup2, lt, push1 ⟨15⟩, dup3, gt, and, push2 ⟨3693⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [jumpdest, push1 ⟨48⟩, dup2, lt, push1 ⟨31⟩, dup3, gt, and, push2 ⟨3385⟩, jumpiNT (by native_decide)]
  have rd20 := evm_run_rfl rd19 with [jumpdest, push1 ⟨64⟩, dup2, lt, push1 ⟨47⟩, dup3, gt, and, push2 ⟨3077⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [jumpdest, push1 ⟨63⟩, dup2, gt, push2 ⟨2769⟩, jumpiT (by native_decide) jump_2769]
  have rd22 := evm_run_rfl rd21 with [jumpdest, push1 ⟨64⟩, dup2, sub, dup1, push0, eq, push2 ⟨3066⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨1⟩, eq, push2 ⟨3056⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup1, push1 ⟨2⟩, eq, push2 ⟨3045⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨3⟩, eq, push2 ⟨3034⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup1, push1 ⟨4⟩, eq, push2 ⟨3023⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨5⟩, eq, push2 ⟨3012⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨6⟩, eq, push2 ⟨3001⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [dup1, push1 ⟨7⟩, eq, push2 ⟨2991⟩, jumpiT (by native_decide) jump_2991]
  have rd30 := evm_run_rfl rd29 with [jumpdest, pop, swap1, pop, dup14, swap1, push2 ⟨2899⟩, jump jump_2899]
  have rd31 := evm_run_rfl rd30 with [jumpdest, push2 ⟨453⟩, jump jump_453]
  have rd32 := evm_run_rfl rd31 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiNT (by native_decide)]
  have rd33 := evm_run_rfl rd32 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1877⟩, jumpiNT (by native_decide)]
  have rd34 := evm_run_rfl rd33 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1431⟩, jumpiNT (by native_decide)]
  have rd35 := evm_run_rfl rd34 with [dup1, push1 ⟨3⟩, eq, push2 ⟨985⟩, jumpiNT (by native_decide)]
  have rd36 := evm_run_rfl rd35 with [push1 ⟨4⟩, eq, push2 ⟨540⟩, jumpiT (by native_decide) jump_540]
  have rd37 := evm_run_rfl rd36 with [jumpdest, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨966⟩, jumpiNT (by native_decide)]
  have rd38 := evm_run_rfl rd37 with [dup1, push1 ⟨1⟩, eq, push2 ⟨947⟩, jumpiNT (by native_decide)]
  have rd39 := evm_run_rfl rd38 with [dup1, push1 ⟨2⟩, eq, push2 ⟨928⟩, jumpiNT (by native_decide)]
  have rd40 := evm_run_rfl rd39 with [dup1, push1 ⟨3⟩, eq, push2 ⟨909⟩, jumpiNT (by native_decide)]
  have rd41 := evm_run_rfl rd40 with [dup1, push1 ⟨4⟩, eq, push2 ⟨890⟩, jumpiNT (by native_decide)]
  have rd42 := evm_run_rfl rd41 with [dup1, push1 ⟨5⟩, eq, push2 ⟨871⟩, jumpiNT (by native_decide)]
  have rd43 := evm_run_rfl rd42 with [dup1, push1 ⟨6⟩, eq, push2 ⟨852⟩, jumpiNT (by native_decide)]
  have rd44 := evm_run_rfl rd43 with [dup1, push1 ⟨7⟩, eq, push2 ⟨833⟩, jumpiT (by native_decide) jump_833]
  have rd45 := evm_run_rfl rd44 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨12⟩, swap8, swap2, swap3, pop, pop, push2 ⟨673⟩, jump jump_673]
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

theorem runtime_leftRoundHelper_72 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 72 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 4 8).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 4 8).aw
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
  have rd14 := evm_run_rfl rd13 with [pop, pop, dup1, push1 ⟨3⟩, eq, push2 ⟨4032⟩, jumpiNT (by native_decide)]
  have rd15 := evm_run_rfl rd14 with [push1 ⟨4⟩, eq, push2 ⟨4010⟩, jumpiT (by native_decide) jump_4010]
  have rd16 := evm_run_rfl rd15 with [jumpdest, swap5, pop, swap3, pop, dup14, dup11, not, dup13, or, xor, swap3, push4 ⟨2840853838⟩, swap5, push2 ⟨391⟩, jump jump_391]
  have rd17 := evm_run_rfl rd16 with [jumpdest, push0, swap1, push1 ⟨16⟩, dup2, lt, push2 ⟨4001⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [jumpdest, push1 ⟨32⟩, dup2, lt, push1 ⟨15⟩, dup3, gt, and, push2 ⟨3693⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [jumpdest, push1 ⟨48⟩, dup2, lt, push1 ⟨31⟩, dup3, gt, and, push2 ⟨3385⟩, jumpiNT (by native_decide)]
  have rd20 := evm_run_rfl rd19 with [jumpdest, push1 ⟨64⟩, dup2, lt, push1 ⟨47⟩, dup3, gt, and, push2 ⟨3077⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [jumpdest, push1 ⟨63⟩, dup2, gt, push2 ⟨2769⟩, jumpiT (by native_decide) jump_2769]
  have rd22 := evm_run_rfl rd21 with [jumpdest, push1 ⟨64⟩, dup2, sub, dup1, push0, eq, push2 ⟨3066⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨1⟩, eq, push2 ⟨3056⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup1, push1 ⟨2⟩, eq, push2 ⟨3045⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨3⟩, eq, push2 ⟨3034⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup1, push1 ⟨4⟩, eq, push2 ⟨3023⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨5⟩, eq, push2 ⟨3012⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨6⟩, eq, push2 ⟨3001⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [dup1, push1 ⟨7⟩, eq, push2 ⟨2991⟩, jumpiNT (by native_decide)]
  have rd30 := evm_run_rfl rd29 with [dup1, push1 ⟨8⟩, eq, push2 ⟨2980⟩, jumpiT (by native_decide) jump_2980]
  have rd31 := evm_run_rfl rd30 with [jumpdest, pop, swap1, pop, push1 ⟨14⟩, swap1, push2 ⟨2899⟩, jump jump_2899]
  have rd32 := evm_run_rfl rd31 with [jumpdest, push2 ⟨453⟩, jump jump_453]
  have rd33 := evm_run_rfl rd32 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiNT (by native_decide)]
  have rd34 := evm_run_rfl rd33 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1877⟩, jumpiNT (by native_decide)]
  have rd35 := evm_run_rfl rd34 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1431⟩, jumpiNT (by native_decide)]
  have rd36 := evm_run_rfl rd35 with [dup1, push1 ⟨3⟩, eq, push2 ⟨985⟩, jumpiNT (by native_decide)]
  have rd37 := evm_run_rfl rd36 with [push1 ⟨4⟩, eq, push2 ⟨540⟩, jumpiT (by native_decide) jump_540]
  have rd38 := evm_run_rfl rd37 with [jumpdest, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨966⟩, jumpiNT (by native_decide)]
  have rd39 := evm_run_rfl rd38 with [dup1, push1 ⟨1⟩, eq, push2 ⟨947⟩, jumpiNT (by native_decide)]
  have rd40 := evm_run_rfl rd39 with [dup1, push1 ⟨2⟩, eq, push2 ⟨928⟩, jumpiNT (by native_decide)]
  have rd41 := evm_run_rfl rd40 with [dup1, push1 ⟨3⟩, eq, push2 ⟨909⟩, jumpiNT (by native_decide)]
  have rd42 := evm_run_rfl rd41 with [dup1, push1 ⟨4⟩, eq, push2 ⟨890⟩, jumpiNT (by native_decide)]
  have rd43 := evm_run_rfl rd42 with [dup1, push1 ⟨5⟩, eq, push2 ⟨871⟩, jumpiNT (by native_decide)]
  have rd44 := evm_run_rfl rd43 with [dup1, push1 ⟨6⟩, eq, push2 ⟨852⟩, jumpiNT (by native_decide)]
  have rd45 := evm_run_rfl rd44 with [dup1, push1 ⟨7⟩, eq, push2 ⟨833⟩, jumpiNT (by native_decide)]
  have rd46 := evm_run_rfl rd45 with [dup1, push1 ⟨8⟩, eq, push2 ⟨814⟩, jumpiT (by native_decide) jump_814]
  have rd47 := evm_run_rfl rd46 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨5⟩, swap8, swap2, swap3, pop, pop, push2 ⟨673⟩, jump jump_673]
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

theorem runtime_leftRoundHelper_73 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 73 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 4 9).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 4 9).aw
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
  have rd14 := evm_run_rfl rd13 with [pop, pop, dup1, push1 ⟨3⟩, eq, push2 ⟨4032⟩, jumpiNT (by native_decide)]
  have rd15 := evm_run_rfl rd14 with [push1 ⟨4⟩, eq, push2 ⟨4010⟩, jumpiT (by native_decide) jump_4010]
  have rd16 := evm_run_rfl rd15 with [jumpdest, swap5, pop, swap3, pop, dup14, dup11, not, dup13, or, xor, swap3, push4 ⟨2840853838⟩, swap5, push2 ⟨391⟩, jump jump_391]
  have rd17 := evm_run_rfl rd16 with [jumpdest, push0, swap1, push1 ⟨16⟩, dup2, lt, push2 ⟨4001⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [jumpdest, push1 ⟨32⟩, dup2, lt, push1 ⟨15⟩, dup3, gt, and, push2 ⟨3693⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [jumpdest, push1 ⟨48⟩, dup2, lt, push1 ⟨31⟩, dup3, gt, and, push2 ⟨3385⟩, jumpiNT (by native_decide)]
  have rd20 := evm_run_rfl rd19 with [jumpdest, push1 ⟨64⟩, dup2, lt, push1 ⟨47⟩, dup3, gt, and, push2 ⟨3077⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [jumpdest, push1 ⟨63⟩, dup2, gt, push2 ⟨2769⟩, jumpiT (by native_decide) jump_2769]
  have rd22 := evm_run_rfl rd21 with [jumpdest, push1 ⟨64⟩, dup2, sub, dup1, push0, eq, push2 ⟨3066⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨1⟩, eq, push2 ⟨3056⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup1, push1 ⟨2⟩, eq, push2 ⟨3045⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨3⟩, eq, push2 ⟨3034⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup1, push1 ⟨4⟩, eq, push2 ⟨3023⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨5⟩, eq, push2 ⟨3012⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨6⟩, eq, push2 ⟨3001⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [dup1, push1 ⟨7⟩, eq, push2 ⟨2991⟩, jumpiNT (by native_decide)]
  have rd30 := evm_run_rfl rd29 with [dup1, push1 ⟨8⟩, eq, push2 ⟨2980⟩, jumpiNT (by native_decide)]
  have rd31 := evm_run_rfl rd30 with [dup1, push1 ⟨9⟩, eq, push2 ⟨2969⟩, jumpiT (by native_decide) jump_2969]
  have rd32 := evm_run_rfl rd31 with [jumpdest, pop, swap1, pop, push1 ⟨1⟩, swap1, push2 ⟨2899⟩, jump jump_2899]
  have rd33 := evm_run_rfl rd32 with [jumpdest, push2 ⟨453⟩, jump jump_453]
  have rd34 := evm_run_rfl rd33 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiNT (by native_decide)]
  have rd35 := evm_run_rfl rd34 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1877⟩, jumpiNT (by native_decide)]
  have rd36 := evm_run_rfl rd35 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1431⟩, jumpiNT (by native_decide)]
  have rd37 := evm_run_rfl rd36 with [dup1, push1 ⟨3⟩, eq, push2 ⟨985⟩, jumpiNT (by native_decide)]
  have rd38 := evm_run_rfl rd37 with [push1 ⟨4⟩, eq, push2 ⟨540⟩, jumpiT (by native_decide) jump_540]
  have rd39 := evm_run_rfl rd38 with [jumpdest, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨966⟩, jumpiNT (by native_decide)]
  have rd40 := evm_run_rfl rd39 with [dup1, push1 ⟨1⟩, eq, push2 ⟨947⟩, jumpiNT (by native_decide)]
  have rd41 := evm_run_rfl rd40 with [dup1, push1 ⟨2⟩, eq, push2 ⟨928⟩, jumpiNT (by native_decide)]
  have rd42 := evm_run_rfl rd41 with [dup1, push1 ⟨3⟩, eq, push2 ⟨909⟩, jumpiNT (by native_decide)]
  have rd43 := evm_run_rfl rd42 with [dup1, push1 ⟨4⟩, eq, push2 ⟨890⟩, jumpiNT (by native_decide)]
  have rd44 := evm_run_rfl rd43 with [dup1, push1 ⟨5⟩, eq, push2 ⟨871⟩, jumpiNT (by native_decide)]
  have rd45 := evm_run_rfl rd44 with [dup1, push1 ⟨6⟩, eq, push2 ⟨852⟩, jumpiNT (by native_decide)]
  have rd46 := evm_run_rfl rd45 with [dup1, push1 ⟨7⟩, eq, push2 ⟨833⟩, jumpiNT (by native_decide)]
  have rd47 := evm_run_rfl rd46 with [dup1, push1 ⟨8⟩, eq, push2 ⟨814⟩, jumpiNT (by native_decide)]
  have rd48 := evm_run_rfl rd47 with [dup1, push1 ⟨9⟩, eq, push2 ⟨795⟩, jumpiT (by native_decide) jump_795]
  have rd49 := evm_run_rfl rd48 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨12⟩, swap8, swap2, swap3, pop, pop, push2 ⟨673⟩, jump jump_673]
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

theorem runtime_leftRoundHelper_74 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 74 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 4 10).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 4 10).aw
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
  have rd14 := evm_run_rfl rd13 with [pop, pop, dup1, push1 ⟨3⟩, eq, push2 ⟨4032⟩, jumpiNT (by native_decide)]
  have rd15 := evm_run_rfl rd14 with [push1 ⟨4⟩, eq, push2 ⟨4010⟩, jumpiT (by native_decide) jump_4010]
  have rd16 := evm_run_rfl rd15 with [jumpdest, swap5, pop, swap3, pop, dup14, dup11, not, dup13, or, xor, swap3, push4 ⟨2840853838⟩, swap5, push2 ⟨391⟩, jump jump_391]
  have rd17 := evm_run_rfl rd16 with [jumpdest, push0, swap1, push1 ⟨16⟩, dup2, lt, push2 ⟨4001⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [jumpdest, push1 ⟨32⟩, dup2, lt, push1 ⟨15⟩, dup3, gt, and, push2 ⟨3693⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [jumpdest, push1 ⟨48⟩, dup2, lt, push1 ⟨31⟩, dup3, gt, and, push2 ⟨3385⟩, jumpiNT (by native_decide)]
  have rd20 := evm_run_rfl rd19 with [jumpdest, push1 ⟨64⟩, dup2, lt, push1 ⟨47⟩, dup3, gt, and, push2 ⟨3077⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [jumpdest, push1 ⟨63⟩, dup2, gt, push2 ⟨2769⟩, jumpiT (by native_decide) jump_2769]
  have rd22 := evm_run_rfl rd21 with [jumpdest, push1 ⟨64⟩, dup2, sub, dup1, push0, eq, push2 ⟨3066⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨1⟩, eq, push2 ⟨3056⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup1, push1 ⟨2⟩, eq, push2 ⟨3045⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨3⟩, eq, push2 ⟨3034⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup1, push1 ⟨4⟩, eq, push2 ⟨3023⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨5⟩, eq, push2 ⟨3012⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨6⟩, eq, push2 ⟨3001⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [dup1, push1 ⟨7⟩, eq, push2 ⟨2991⟩, jumpiNT (by native_decide)]
  have rd30 := evm_run_rfl rd29 with [dup1, push1 ⟨8⟩, eq, push2 ⟨2980⟩, jumpiNT (by native_decide)]
  have rd31 := evm_run_rfl rd30 with [dup1, push1 ⟨9⟩, eq, push2 ⟨2969⟩, jumpiNT (by native_decide)]
  have rd32 := evm_run_rfl rd31 with [dup16, dup2, eq, push2 ⟨2958⟩, jumpiT (by native_decide) jump_2958]
  have rd33 := evm_run_rfl rd32 with [jumpdest, pop, swap1, pop, push1 ⟨3⟩, swap1, push2 ⟨2899⟩, jump jump_2899]
  have rd34 := evm_run_rfl rd33 with [jumpdest, push2 ⟨453⟩, jump jump_453]
  have rd35 := evm_run_rfl rd34 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiNT (by native_decide)]
  have rd36 := evm_run_rfl rd35 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1877⟩, jumpiNT (by native_decide)]
  have rd37 := evm_run_rfl rd36 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1431⟩, jumpiNT (by native_decide)]
  have rd38 := evm_run_rfl rd37 with [dup1, push1 ⟨3⟩, eq, push2 ⟨985⟩, jumpiNT (by native_decide)]
  have rd39 := evm_run_rfl rd38 with [push1 ⟨4⟩, eq, push2 ⟨540⟩, jumpiT (by native_decide) jump_540]
  have rd40 := evm_run_rfl rd39 with [jumpdest, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨966⟩, jumpiNT (by native_decide)]
  have rd41 := evm_run_rfl rd40 with [dup1, push1 ⟨1⟩, eq, push2 ⟨947⟩, jumpiNT (by native_decide)]
  have rd42 := evm_run_rfl rd41 with [dup1, push1 ⟨2⟩, eq, push2 ⟨928⟩, jumpiNT (by native_decide)]
  have rd43 := evm_run_rfl rd42 with [dup1, push1 ⟨3⟩, eq, push2 ⟨909⟩, jumpiNT (by native_decide)]
  have rd44 := evm_run_rfl rd43 with [dup1, push1 ⟨4⟩, eq, push2 ⟨890⟩, jumpiNT (by native_decide)]
  have rd45 := evm_run_rfl rd44 with [dup1, push1 ⟨5⟩, eq, push2 ⟨871⟩, jumpiNT (by native_decide)]
  have rd46 := evm_run_rfl rd45 with [dup1, push1 ⟨6⟩, eq, push2 ⟨852⟩, jumpiNT (by native_decide)]
  have rd47 := evm_run_rfl rd46 with [dup1, push1 ⟨7⟩, eq, push2 ⟨833⟩, jumpiNT (by native_decide)]
  have rd48 := evm_run_rfl rd47 with [dup1, push1 ⟨8⟩, eq, push2 ⟨814⟩, jumpiNT (by native_decide)]
  have rd49 := evm_run_rfl rd48 with [dup1, push1 ⟨9⟩, eq, push2 ⟨795⟩, jumpiNT (by native_decide)]
  have rd50 := evm_run_rfl rd49 with [dup1, dup15, eq, push2 ⟨776⟩, jumpiT (by native_decide) jump_776]
  have rd51 := evm_run_rfl rd50 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨13⟩, swap8, swap2, swap3, pop, pop, push2 ⟨673⟩, jump jump_673]
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

theorem runtime_leftRoundHelper_75 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 75 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 4 11).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 4 11).aw
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
  have rd14 := evm_run_rfl rd13 with [pop, pop, dup1, push1 ⟨3⟩, eq, push2 ⟨4032⟩, jumpiNT (by native_decide)]
  have rd15 := evm_run_rfl rd14 with [push1 ⟨4⟩, eq, push2 ⟨4010⟩, jumpiT (by native_decide) jump_4010]
  have rd16 := evm_run_rfl rd15 with [jumpdest, swap5, pop, swap3, pop, dup14, dup11, not, dup13, or, xor, swap3, push4 ⟨2840853838⟩, swap5, push2 ⟨391⟩, jump jump_391]
  have rd17 := evm_run_rfl rd16 with [jumpdest, push0, swap1, push1 ⟨16⟩, dup2, lt, push2 ⟨4001⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [jumpdest, push1 ⟨32⟩, dup2, lt, push1 ⟨15⟩, dup3, gt, and, push2 ⟨3693⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [jumpdest, push1 ⟨48⟩, dup2, lt, push1 ⟨31⟩, dup3, gt, and, push2 ⟨3385⟩, jumpiNT (by native_decide)]
  have rd20 := evm_run_rfl rd19 with [jumpdest, push1 ⟨64⟩, dup2, lt, push1 ⟨47⟩, dup3, gt, and, push2 ⟨3077⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [jumpdest, push1 ⟨63⟩, dup2, gt, push2 ⟨2769⟩, jumpiT (by native_decide) jump_2769]
  have rd22 := evm_run_rfl rd21 with [jumpdest, push1 ⟨64⟩, dup2, sub, dup1, push0, eq, push2 ⟨3066⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨1⟩, eq, push2 ⟨3056⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup1, push1 ⟨2⟩, eq, push2 ⟨3045⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨3⟩, eq, push2 ⟨3034⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup1, push1 ⟨4⟩, eq, push2 ⟨3023⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨5⟩, eq, push2 ⟨3012⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨6⟩, eq, push2 ⟨3001⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [dup1, push1 ⟨7⟩, eq, push2 ⟨2991⟩, jumpiNT (by native_decide)]
  have rd30 := evm_run_rfl rd29 with [dup1, push1 ⟨8⟩, eq, push2 ⟨2980⟩, jumpiNT (by native_decide)]
  have rd31 := evm_run_rfl rd30 with [dup1, push1 ⟨9⟩, eq, push2 ⟨2969⟩, jumpiNT (by native_decide)]
  have rd32 := evm_run_rfl rd31 with [dup16, dup2, eq, push2 ⟨2958⟩, jumpiNT (by native_decide)]
  have rd33 := evm_run_rfl rd32 with [dup1, push1 ⟨11⟩, eq, push2 ⟨2947⟩, jumpiT (by native_decide) jump_2947]
  have rd34 := evm_run_rfl rd33 with [jumpdest, pop, swap1, pop, push1 ⟨8⟩, swap1, push2 ⟨2899⟩, jump jump_2899]
  have rd35 := evm_run_rfl rd34 with [jumpdest, push2 ⟨453⟩, jump jump_453]
  have rd36 := evm_run_rfl rd35 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiNT (by native_decide)]
  have rd37 := evm_run_rfl rd36 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1877⟩, jumpiNT (by native_decide)]
  have rd38 := evm_run_rfl rd37 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1431⟩, jumpiNT (by native_decide)]
  have rd39 := evm_run_rfl rd38 with [dup1, push1 ⟨3⟩, eq, push2 ⟨985⟩, jumpiNT (by native_decide)]
  have rd40 := evm_run_rfl rd39 with [push1 ⟨4⟩, eq, push2 ⟨540⟩, jumpiT (by native_decide) jump_540]
  have rd41 := evm_run_rfl rd40 with [jumpdest, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨966⟩, jumpiNT (by native_decide)]
  have rd42 := evm_run_rfl rd41 with [dup1, push1 ⟨1⟩, eq, push2 ⟨947⟩, jumpiNT (by native_decide)]
  have rd43 := evm_run_rfl rd42 with [dup1, push1 ⟨2⟩, eq, push2 ⟨928⟩, jumpiNT (by native_decide)]
  have rd44 := evm_run_rfl rd43 with [dup1, push1 ⟨3⟩, eq, push2 ⟨909⟩, jumpiNT (by native_decide)]
  have rd45 := evm_run_rfl rd44 with [dup1, push1 ⟨4⟩, eq, push2 ⟨890⟩, jumpiNT (by native_decide)]
  have rd46 := evm_run_rfl rd45 with [dup1, push1 ⟨5⟩, eq, push2 ⟨871⟩, jumpiNT (by native_decide)]
  have rd47 := evm_run_rfl rd46 with [dup1, push1 ⟨6⟩, eq, push2 ⟨852⟩, jumpiNT (by native_decide)]
  have rd48 := evm_run_rfl rd47 with [dup1, push1 ⟨7⟩, eq, push2 ⟨833⟩, jumpiNT (by native_decide)]
  have rd49 := evm_run_rfl rd48 with [dup1, push1 ⟨8⟩, eq, push2 ⟨814⟩, jumpiNT (by native_decide)]
  have rd50 := evm_run_rfl rd49 with [dup1, push1 ⟨9⟩, eq, push2 ⟨795⟩, jumpiNT (by native_decide)]
  have rd51 := evm_run_rfl rd50 with [dup1, dup15, eq, push2 ⟨776⟩, jumpiNT (by native_decide)]
  have rd52 := evm_run_rfl rd51 with [dup1, push1 ⟨11⟩, eq, push2 ⟨757⟩, jumpiT (by native_decide) jump_757]
  have rd53 := evm_run_rfl rd52 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨14⟩, swap8, swap2, swap3, pop, pop, push2 ⟨673⟩, jump jump_673]
  have rd54 := evm_run_rfl rd53 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨494⟩, jump jump_494]
  have rd55 := evm_run_rfl rd54 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd56 := RD.runtimeMload rd55 (by old_decode) (by simp; omega)
  have rd57 := evm_run_rfl rd56 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd58 := evm_run_rfl rd57 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_511]
  have rd59 := evm_run_rfl rd58 with [jumpdest, add, and, swap8, dup7]
  have rd60 := RD.runtimeMstore rd59 (by old_decode) (by simp; omega)
  have rd61 := evm_run_rfl rd60 with [push1 ⟨128⟩, dup7, add]
  have rd62 := RD.runtimeMstore rd61 (by old_decode) (by simp; omega)
  have rd63 := evm_run_rfl rd62 with [push2 ⟨268⟩, jump jump_268]
  have rd64 := evm_run_rfl rd63 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_526]
  have rd65 := evm_run_rfl rd64 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd66 := RD.runtimeMstore rd65 (by old_decode) (by simp; omega)
  have rd67 := evm_run_rfl rd66 with [push1 ⟨64⟩, dup3, add]
  have rd68 := RD.runtimeMstore rd67 (by old_decode) (by simp; omega)
  have rd69 := evm_run_rfl rd68 with [add]
  have rd70 := RD.runtimeMstore rd69 (by old_decode) (by simp; omega)
  have rd71 := evm_run_rfl rd70 with [jump jump_8991]
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
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd71⟩

theorem runtime_leftRoundHelper_76 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 76 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 4 12).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 4 12).aw
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
  have rd14 := evm_run_rfl rd13 with [pop, pop, dup1, push1 ⟨3⟩, eq, push2 ⟨4032⟩, jumpiNT (by native_decide)]
  have rd15 := evm_run_rfl rd14 with [push1 ⟨4⟩, eq, push2 ⟨4010⟩, jumpiT (by native_decide) jump_4010]
  have rd16 := evm_run_rfl rd15 with [jumpdest, swap5, pop, swap3, pop, dup14, dup11, not, dup13, or, xor, swap3, push4 ⟨2840853838⟩, swap5, push2 ⟨391⟩, jump jump_391]
  have rd17 := evm_run_rfl rd16 with [jumpdest, push0, swap1, push1 ⟨16⟩, dup2, lt, push2 ⟨4001⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [jumpdest, push1 ⟨32⟩, dup2, lt, push1 ⟨15⟩, dup3, gt, and, push2 ⟨3693⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [jumpdest, push1 ⟨48⟩, dup2, lt, push1 ⟨31⟩, dup3, gt, and, push2 ⟨3385⟩, jumpiNT (by native_decide)]
  have rd20 := evm_run_rfl rd19 with [jumpdest, push1 ⟨64⟩, dup2, lt, push1 ⟨47⟩, dup3, gt, and, push2 ⟨3077⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [jumpdest, push1 ⟨63⟩, dup2, gt, push2 ⟨2769⟩, jumpiT (by native_decide) jump_2769]
  have rd22 := evm_run_rfl rd21 with [jumpdest, push1 ⟨64⟩, dup2, sub, dup1, push0, eq, push2 ⟨3066⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨1⟩, eq, push2 ⟨3056⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup1, push1 ⟨2⟩, eq, push2 ⟨3045⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨3⟩, eq, push2 ⟨3034⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup1, push1 ⟨4⟩, eq, push2 ⟨3023⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨5⟩, eq, push2 ⟨3012⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨6⟩, eq, push2 ⟨3001⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [dup1, push1 ⟨7⟩, eq, push2 ⟨2991⟩, jumpiNT (by native_decide)]
  have rd30 := evm_run_rfl rd29 with [dup1, push1 ⟨8⟩, eq, push2 ⟨2980⟩, jumpiNT (by native_decide)]
  have rd31 := evm_run_rfl rd30 with [dup1, push1 ⟨9⟩, eq, push2 ⟨2969⟩, jumpiNT (by native_decide)]
  have rd32 := evm_run_rfl rd31 with [dup16, dup2, eq, push2 ⟨2958⟩, jumpiNT (by native_decide)]
  have rd33 := evm_run_rfl rd32 with [dup1, push1 ⟨11⟩, eq, push2 ⟨2947⟩, jumpiNT (by native_decide)]
  have rd34 := evm_run_rfl rd33 with [dup1, push1 ⟨12⟩, eq, push2 ⟨2936⟩, jumpiT (by native_decide) jump_2936]
  have rd35 := evm_run_rfl rd34 with [jumpdest, pop, swap1, pop, push1 ⟨11⟩, swap1, push2 ⟨2899⟩, jump jump_2899]
  have rd36 := evm_run_rfl rd35 with [jumpdest, push2 ⟨453⟩, jump jump_453]
  have rd37 := evm_run_rfl rd36 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiNT (by native_decide)]
  have rd38 := evm_run_rfl rd37 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1877⟩, jumpiNT (by native_decide)]
  have rd39 := evm_run_rfl rd38 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1431⟩, jumpiNT (by native_decide)]
  have rd40 := evm_run_rfl rd39 with [dup1, push1 ⟨3⟩, eq, push2 ⟨985⟩, jumpiNT (by native_decide)]
  have rd41 := evm_run_rfl rd40 with [push1 ⟨4⟩, eq, push2 ⟨540⟩, jumpiT (by native_decide) jump_540]
  have rd42 := evm_run_rfl rd41 with [jumpdest, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨966⟩, jumpiNT (by native_decide)]
  have rd43 := evm_run_rfl rd42 with [dup1, push1 ⟨1⟩, eq, push2 ⟨947⟩, jumpiNT (by native_decide)]
  have rd44 := evm_run_rfl rd43 with [dup1, push1 ⟨2⟩, eq, push2 ⟨928⟩, jumpiNT (by native_decide)]
  have rd45 := evm_run_rfl rd44 with [dup1, push1 ⟨3⟩, eq, push2 ⟨909⟩, jumpiNT (by native_decide)]
  have rd46 := evm_run_rfl rd45 with [dup1, push1 ⟨4⟩, eq, push2 ⟨890⟩, jumpiNT (by native_decide)]
  have rd47 := evm_run_rfl rd46 with [dup1, push1 ⟨5⟩, eq, push2 ⟨871⟩, jumpiNT (by native_decide)]
  have rd48 := evm_run_rfl rd47 with [dup1, push1 ⟨6⟩, eq, push2 ⟨852⟩, jumpiNT (by native_decide)]
  have rd49 := evm_run_rfl rd48 with [dup1, push1 ⟨7⟩, eq, push2 ⟨833⟩, jumpiNT (by native_decide)]
  have rd50 := evm_run_rfl rd49 with [dup1, push1 ⟨8⟩, eq, push2 ⟨814⟩, jumpiNT (by native_decide)]
  have rd51 := evm_run_rfl rd50 with [dup1, push1 ⟨9⟩, eq, push2 ⟨795⟩, jumpiNT (by native_decide)]
  have rd52 := evm_run_rfl rd51 with [dup1, dup15, eq, push2 ⟨776⟩, jumpiNT (by native_decide)]
  have rd53 := evm_run_rfl rd52 with [dup1, push1 ⟨11⟩, eq, push2 ⟨757⟩, jumpiNT (by native_decide)]
  have rd54 := evm_run_rfl rd53 with [dup1, push1 ⟨12⟩, eq, push2 ⟨738⟩, jumpiT (by native_decide) jump_738]
  have rd55 := evm_run_rfl rd54 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨11⟩, swap8, swap2, swap3, pop, pop, push2 ⟨673⟩, jump jump_673]
  have rd56 := evm_run_rfl rd55 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨494⟩, jump jump_494]
  have rd57 := evm_run_rfl rd56 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd58 := RD.runtimeMload rd57 (by old_decode) (by simp; omega)
  have rd59 := evm_run_rfl rd58 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd60 := evm_run_rfl rd59 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_511]
  have rd61 := evm_run_rfl rd60 with [jumpdest, add, and, swap8, dup7]
  have rd62 := RD.runtimeMstore rd61 (by old_decode) (by simp; omega)
  have rd63 := evm_run_rfl rd62 with [push1 ⟨128⟩, dup7, add]
  have rd64 := RD.runtimeMstore rd63 (by old_decode) (by simp; omega)
  have rd65 := evm_run_rfl rd64 with [push2 ⟨268⟩, jump jump_268]
  have rd66 := evm_run_rfl rd65 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_526]
  have rd67 := evm_run_rfl rd66 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd68 := RD.runtimeMstore rd67 (by old_decode) (by simp; omega)
  have rd69 := evm_run_rfl rd68 with [push1 ⟨64⟩, dup3, add]
  have rd70 := RD.runtimeMstore rd69 (by old_decode) (by simp; omega)
  have rd71 := evm_run_rfl rd70 with [add]
  have rd72 := RD.runtimeMstore rd71 (by old_decode) (by simp; omega)
  have rd73 := evm_run_rfl rd72 with [jump jump_8991]
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
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd73⟩

theorem runtime_leftRoundHelper_77 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 77 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 4 13).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 4 13).aw
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
  have rd14 := evm_run_rfl rd13 with [pop, pop, dup1, push1 ⟨3⟩, eq, push2 ⟨4032⟩, jumpiNT (by native_decide)]
  have rd15 := evm_run_rfl rd14 with [push1 ⟨4⟩, eq, push2 ⟨4010⟩, jumpiT (by native_decide) jump_4010]
  have rd16 := evm_run_rfl rd15 with [jumpdest, swap5, pop, swap3, pop, dup14, dup11, not, dup13, or, xor, swap3, push4 ⟨2840853838⟩, swap5, push2 ⟨391⟩, jump jump_391]
  have rd17 := evm_run_rfl rd16 with [jumpdest, push0, swap1, push1 ⟨16⟩, dup2, lt, push2 ⟨4001⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [jumpdest, push1 ⟨32⟩, dup2, lt, push1 ⟨15⟩, dup3, gt, and, push2 ⟨3693⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [jumpdest, push1 ⟨48⟩, dup2, lt, push1 ⟨31⟩, dup3, gt, and, push2 ⟨3385⟩, jumpiNT (by native_decide)]
  have rd20 := evm_run_rfl rd19 with [jumpdest, push1 ⟨64⟩, dup2, lt, push1 ⟨47⟩, dup3, gt, and, push2 ⟨3077⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [jumpdest, push1 ⟨63⟩, dup2, gt, push2 ⟨2769⟩, jumpiT (by native_decide) jump_2769]
  have rd22 := evm_run_rfl rd21 with [jumpdest, push1 ⟨64⟩, dup2, sub, dup1, push0, eq, push2 ⟨3066⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨1⟩, eq, push2 ⟨3056⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup1, push1 ⟨2⟩, eq, push2 ⟨3045⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨3⟩, eq, push2 ⟨3034⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup1, push1 ⟨4⟩, eq, push2 ⟨3023⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨5⟩, eq, push2 ⟨3012⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨6⟩, eq, push2 ⟨3001⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [dup1, push1 ⟨7⟩, eq, push2 ⟨2991⟩, jumpiNT (by native_decide)]
  have rd30 := evm_run_rfl rd29 with [dup1, push1 ⟨8⟩, eq, push2 ⟨2980⟩, jumpiNT (by native_decide)]
  have rd31 := evm_run_rfl rd30 with [dup1, push1 ⟨9⟩, eq, push2 ⟨2969⟩, jumpiNT (by native_decide)]
  have rd32 := evm_run_rfl rd31 with [dup16, dup2, eq, push2 ⟨2958⟩, jumpiNT (by native_decide)]
  have rd33 := evm_run_rfl rd32 with [dup1, push1 ⟨11⟩, eq, push2 ⟨2947⟩, jumpiNT (by native_decide)]
  have rd34 := evm_run_rfl rd33 with [dup1, push1 ⟨12⟩, eq, push2 ⟨2936⟩, jumpiNT (by native_decide)]
  have rd35 := evm_run_rfl rd34 with [dup1, push1 ⟨13⟩, eq, push2 ⟨2925⟩, jumpiT (by native_decide) jump_2925]
  have rd36 := evm_run_rfl rd35 with [jumpdest, pop, swap1, pop, push1 ⟨6⟩, swap1, push2 ⟨2899⟩, jump jump_2899]
  have rd37 := evm_run_rfl rd36 with [jumpdest, push2 ⟨453⟩, jump jump_453]
  have rd38 := evm_run_rfl rd37 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiNT (by native_decide)]
  have rd39 := evm_run_rfl rd38 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1877⟩, jumpiNT (by native_decide)]
  have rd40 := evm_run_rfl rd39 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1431⟩, jumpiNT (by native_decide)]
  have rd41 := evm_run_rfl rd40 with [dup1, push1 ⟨3⟩, eq, push2 ⟨985⟩, jumpiNT (by native_decide)]
  have rd42 := evm_run_rfl rd41 with [push1 ⟨4⟩, eq, push2 ⟨540⟩, jumpiT (by native_decide) jump_540]
  have rd43 := evm_run_rfl rd42 with [jumpdest, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨966⟩, jumpiNT (by native_decide)]
  have rd44 := evm_run_rfl rd43 with [dup1, push1 ⟨1⟩, eq, push2 ⟨947⟩, jumpiNT (by native_decide)]
  have rd45 := evm_run_rfl rd44 with [dup1, push1 ⟨2⟩, eq, push2 ⟨928⟩, jumpiNT (by native_decide)]
  have rd46 := evm_run_rfl rd45 with [dup1, push1 ⟨3⟩, eq, push2 ⟨909⟩, jumpiNT (by native_decide)]
  have rd47 := evm_run_rfl rd46 with [dup1, push1 ⟨4⟩, eq, push2 ⟨890⟩, jumpiNT (by native_decide)]
  have rd48 := evm_run_rfl rd47 with [dup1, push1 ⟨5⟩, eq, push2 ⟨871⟩, jumpiNT (by native_decide)]
  have rd49 := evm_run_rfl rd48 with [dup1, push1 ⟨6⟩, eq, push2 ⟨852⟩, jumpiNT (by native_decide)]
  have rd50 := evm_run_rfl rd49 with [dup1, push1 ⟨7⟩, eq, push2 ⟨833⟩, jumpiNT (by native_decide)]
  have rd51 := evm_run_rfl rd50 with [dup1, push1 ⟨8⟩, eq, push2 ⟨814⟩, jumpiNT (by native_decide)]
  have rd52 := evm_run_rfl rd51 with [dup1, push1 ⟨9⟩, eq, push2 ⟨795⟩, jumpiNT (by native_decide)]
  have rd53 := evm_run_rfl rd52 with [dup1, dup15, eq, push2 ⟨776⟩, jumpiNT (by native_decide)]
  have rd54 := evm_run_rfl rd53 with [dup1, push1 ⟨11⟩, eq, push2 ⟨757⟩, jumpiNT (by native_decide)]
  have rd55 := evm_run_rfl rd54 with [dup1, push1 ⟨12⟩, eq, push2 ⟨738⟩, jumpiNT (by native_decide)]
  have rd56 := evm_run_rfl rd55 with [dup1, push1 ⟨13⟩, eq, push2 ⟨719⟩, jumpiT (by native_decide) jump_719]
  have rd57 := evm_run_rfl rd56 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨8⟩, swap8, swap2, swap3, pop, pop, push2 ⟨673⟩, jump jump_673]
  have rd58 := evm_run_rfl rd57 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨494⟩, jump jump_494]
  have rd59 := evm_run_rfl rd58 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd60 := RD.runtimeMload rd59 (by old_decode) (by simp; omega)
  have rd61 := evm_run_rfl rd60 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd62 := evm_run_rfl rd61 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_511]
  have rd63 := evm_run_rfl rd62 with [jumpdest, add, and, swap8, dup7]
  have rd64 := RD.runtimeMstore rd63 (by old_decode) (by simp; omega)
  have rd65 := evm_run_rfl rd64 with [push1 ⟨128⟩, dup7, add]
  have rd66 := RD.runtimeMstore rd65 (by old_decode) (by simp; omega)
  have rd67 := evm_run_rfl rd66 with [push2 ⟨268⟩, jump jump_268]
  have rd68 := evm_run_rfl rd67 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_526]
  have rd69 := evm_run_rfl rd68 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd70 := RD.runtimeMstore rd69 (by old_decode) (by simp; omega)
  have rd71 := evm_run_rfl rd70 with [push1 ⟨64⟩, dup3, add]
  have rd72 := RD.runtimeMstore rd71 (by old_decode) (by simp; omega)
  have rd73 := evm_run_rfl rd72 with [add]
  have rd74 := RD.runtimeMstore rd73 (by old_decode) (by simp; omega)
  have rd75 := evm_run_rfl rd74 with [jump jump_8991]
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
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd75⟩

theorem runtime_leftRoundHelper_78 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 78 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 4 14).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 4 14).aw
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
  have rd14 := evm_run_rfl rd13 with [pop, pop, dup1, push1 ⟨3⟩, eq, push2 ⟨4032⟩, jumpiNT (by native_decide)]
  have rd15 := evm_run_rfl rd14 with [push1 ⟨4⟩, eq, push2 ⟨4010⟩, jumpiT (by native_decide) jump_4010]
  have rd16 := evm_run_rfl rd15 with [jumpdest, swap5, pop, swap3, pop, dup14, dup11, not, dup13, or, xor, swap3, push4 ⟨2840853838⟩, swap5, push2 ⟨391⟩, jump jump_391]
  have rd17 := evm_run_rfl rd16 with [jumpdest, push0, swap1, push1 ⟨16⟩, dup2, lt, push2 ⟨4001⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [jumpdest, push1 ⟨32⟩, dup2, lt, push1 ⟨15⟩, dup3, gt, and, push2 ⟨3693⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [jumpdest, push1 ⟨48⟩, dup2, lt, push1 ⟨31⟩, dup3, gt, and, push2 ⟨3385⟩, jumpiNT (by native_decide)]
  have rd20 := evm_run_rfl rd19 with [jumpdest, push1 ⟨64⟩, dup2, lt, push1 ⟨47⟩, dup3, gt, and, push2 ⟨3077⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [jumpdest, push1 ⟨63⟩, dup2, gt, push2 ⟨2769⟩, jumpiT (by native_decide) jump_2769]
  have rd22 := evm_run_rfl rd21 with [jumpdest, push1 ⟨64⟩, dup2, sub, dup1, push0, eq, push2 ⟨3066⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨1⟩, eq, push2 ⟨3056⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup1, push1 ⟨2⟩, eq, push2 ⟨3045⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨3⟩, eq, push2 ⟨3034⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup1, push1 ⟨4⟩, eq, push2 ⟨3023⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨5⟩, eq, push2 ⟨3012⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨6⟩, eq, push2 ⟨3001⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [dup1, push1 ⟨7⟩, eq, push2 ⟨2991⟩, jumpiNT (by native_decide)]
  have rd30 := evm_run_rfl rd29 with [dup1, push1 ⟨8⟩, eq, push2 ⟨2980⟩, jumpiNT (by native_decide)]
  have rd31 := evm_run_rfl rd30 with [dup1, push1 ⟨9⟩, eq, push2 ⟨2969⟩, jumpiNT (by native_decide)]
  have rd32 := evm_run_rfl rd31 with [dup16, dup2, eq, push2 ⟨2958⟩, jumpiNT (by native_decide)]
  have rd33 := evm_run_rfl rd32 with [dup1, push1 ⟨11⟩, eq, push2 ⟨2947⟩, jumpiNT (by native_decide)]
  have rd34 := evm_run_rfl rd33 with [dup1, push1 ⟨12⟩, eq, push2 ⟨2936⟩, jumpiNT (by native_decide)]
  have rd35 := evm_run_rfl rd34 with [dup1, push1 ⟨13⟩, eq, push2 ⟨2925⟩, jumpiNT (by native_decide)]
  have rd36 := evm_run_rfl rd35 with [dup1, push1 ⟨14⟩, eq, push2 ⟨2914⟩, jumpiT (by native_decide) jump_2914]
  have rd37 := evm_run_rfl rd36 with [jumpdest, pop, swap1, pop, push1 ⟨15⟩, swap1, push2 ⟨2899⟩, jump jump_2899]
  have rd38 := evm_run_rfl rd37 with [jumpdest, push2 ⟨453⟩, jump jump_453]
  have rd39 := evm_run_rfl rd38 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiNT (by native_decide)]
  have rd40 := evm_run_rfl rd39 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1877⟩, jumpiNT (by native_decide)]
  have rd41 := evm_run_rfl rd40 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1431⟩, jumpiNT (by native_decide)]
  have rd42 := evm_run_rfl rd41 with [dup1, push1 ⟨3⟩, eq, push2 ⟨985⟩, jumpiNT (by native_decide)]
  have rd43 := evm_run_rfl rd42 with [push1 ⟨4⟩, eq, push2 ⟨540⟩, jumpiT (by native_decide) jump_540]
  have rd44 := evm_run_rfl rd43 with [jumpdest, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨966⟩, jumpiNT (by native_decide)]
  have rd45 := evm_run_rfl rd44 with [dup1, push1 ⟨1⟩, eq, push2 ⟨947⟩, jumpiNT (by native_decide)]
  have rd46 := evm_run_rfl rd45 with [dup1, push1 ⟨2⟩, eq, push2 ⟨928⟩, jumpiNT (by native_decide)]
  have rd47 := evm_run_rfl rd46 with [dup1, push1 ⟨3⟩, eq, push2 ⟨909⟩, jumpiNT (by native_decide)]
  have rd48 := evm_run_rfl rd47 with [dup1, push1 ⟨4⟩, eq, push2 ⟨890⟩, jumpiNT (by native_decide)]
  have rd49 := evm_run_rfl rd48 with [dup1, push1 ⟨5⟩, eq, push2 ⟨871⟩, jumpiNT (by native_decide)]
  have rd50 := evm_run_rfl rd49 with [dup1, push1 ⟨6⟩, eq, push2 ⟨852⟩, jumpiNT (by native_decide)]
  have rd51 := evm_run_rfl rd50 with [dup1, push1 ⟨7⟩, eq, push2 ⟨833⟩, jumpiNT (by native_decide)]
  have rd52 := evm_run_rfl rd51 with [dup1, push1 ⟨8⟩, eq, push2 ⟨814⟩, jumpiNT (by native_decide)]
  have rd53 := evm_run_rfl rd52 with [dup1, push1 ⟨9⟩, eq, push2 ⟨795⟩, jumpiNT (by native_decide)]
  have rd54 := evm_run_rfl rd53 with [dup1, dup15, eq, push2 ⟨776⟩, jumpiNT (by native_decide)]
  have rd55 := evm_run_rfl rd54 with [dup1, push1 ⟨11⟩, eq, push2 ⟨757⟩, jumpiNT (by native_decide)]
  have rd56 := evm_run_rfl rd55 with [dup1, push1 ⟨12⟩, eq, push2 ⟨738⟩, jumpiNT (by native_decide)]
  have rd57 := evm_run_rfl rd56 with [dup1, push1 ⟨13⟩, eq, push2 ⟨719⟩, jumpiNT (by native_decide)]
  have rd58 := evm_run_rfl rd57 with [dup1, push1 ⟨14⟩, eq, push2 ⟨700⟩, jumpiT (by native_decide) jump_700]
  have rd59 := evm_run_rfl rd58 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨5⟩, swap8, swap2, swap3, pop, pop, push2 ⟨673⟩, jump jump_673]
  have rd60 := evm_run_rfl rd59 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨494⟩, jump jump_494]
  have rd61 := evm_run_rfl rd60 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd62 := RD.runtimeMload rd61 (by old_decode) (by simp; omega)
  have rd63 := evm_run_rfl rd62 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd64 := evm_run_rfl rd63 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_511]
  have rd65 := evm_run_rfl rd64 with [jumpdest, add, and, swap8, dup7]
  have rd66 := RD.runtimeMstore rd65 (by old_decode) (by simp; omega)
  have rd67 := evm_run_rfl rd66 with [push1 ⟨128⟩, dup7, add]
  have rd68 := RD.runtimeMstore rd67 (by old_decode) (by simp; omega)
  have rd69 := evm_run_rfl rd68 with [push2 ⟨268⟩, jump jump_268]
  have rd70 := evm_run_rfl rd69 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_526]
  have rd71 := evm_run_rfl rd70 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd72 := RD.runtimeMstore rd71 (by old_decode) (by simp; omega)
  have rd73 := evm_run_rfl rd72 with [push1 ⟨64⟩, dup3, add]
  have rd74 := RD.runtimeMstore rd73 (by old_decode) (by simp; omega)
  have rd75 := evm_run_rfl rd74 with [add]
  have rd76 := RD.runtimeMstore rd75 (by old_decode) (by simp; omega)
  have rd77 := evm_run_rfl rd76 with [jump jump_8991]
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
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd77⟩

theorem runtime_leftRoundHelper_79 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 79 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 4 15).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 4 15).aw
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
  have rd14 := evm_run_rfl rd13 with [pop, pop, dup1, push1 ⟨3⟩, eq, push2 ⟨4032⟩, jumpiNT (by native_decide)]
  have rd15 := evm_run_rfl rd14 with [push1 ⟨4⟩, eq, push2 ⟨4010⟩, jumpiT (by native_decide) jump_4010]
  have rd16 := evm_run_rfl rd15 with [jumpdest, swap5, pop, swap3, pop, dup14, dup11, not, dup13, or, xor, swap3, push4 ⟨2840853838⟩, swap5, push2 ⟨391⟩, jump jump_391]
  have rd17 := evm_run_rfl rd16 with [jumpdest, push0, swap1, push1 ⟨16⟩, dup2, lt, push2 ⟨4001⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [jumpdest, push1 ⟨32⟩, dup2, lt, push1 ⟨15⟩, dup3, gt, and, push2 ⟨3693⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [jumpdest, push1 ⟨48⟩, dup2, lt, push1 ⟨31⟩, dup3, gt, and, push2 ⟨3385⟩, jumpiNT (by native_decide)]
  have rd20 := evm_run_rfl rd19 with [jumpdest, push1 ⟨64⟩, dup2, lt, push1 ⟨47⟩, dup3, gt, and, push2 ⟨3077⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [jumpdest, push1 ⟨63⟩, dup2, gt, push2 ⟨2769⟩, jumpiT (by native_decide) jump_2769]
  have rd22 := evm_run_rfl rd21 with [jumpdest, push1 ⟨64⟩, dup2, sub, dup1, push0, eq, push2 ⟨3066⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨1⟩, eq, push2 ⟨3056⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup1, push1 ⟨2⟩, eq, push2 ⟨3045⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨3⟩, eq, push2 ⟨3034⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup1, push1 ⟨4⟩, eq, push2 ⟨3023⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨5⟩, eq, push2 ⟨3012⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨6⟩, eq, push2 ⟨3001⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [dup1, push1 ⟨7⟩, eq, push2 ⟨2991⟩, jumpiNT (by native_decide)]
  have rd30 := evm_run_rfl rd29 with [dup1, push1 ⟨8⟩, eq, push2 ⟨2980⟩, jumpiNT (by native_decide)]
  have rd31 := evm_run_rfl rd30 with [dup1, push1 ⟨9⟩, eq, push2 ⟨2969⟩, jumpiNT (by native_decide)]
  have rd32 := evm_run_rfl rd31 with [dup16, dup2, eq, push2 ⟨2958⟩, jumpiNT (by native_decide)]
  have rd33 := evm_run_rfl rd32 with [dup1, push1 ⟨11⟩, eq, push2 ⟨2947⟩, jumpiNT (by native_decide)]
  have rd34 := evm_run_rfl rd33 with [dup1, push1 ⟨12⟩, eq, push2 ⟨2936⟩, jumpiNT (by native_decide)]
  have rd35 := evm_run_rfl rd34 with [dup1, push1 ⟨13⟩, eq, push2 ⟨2925⟩, jumpiNT (by native_decide)]
  have rd36 := evm_run_rfl rd35 with [dup1, push1 ⟨14⟩, eq, push2 ⟨2914⟩, jumpiNT (by native_decide)]
  have rd37 := evm_run_rfl rd36 with [push1 ⟨15⟩, eq, push2 ⟨2904⟩, jumpiT (by native_decide) jump_2904]
  have rd38 := evm_run_rfl rd37 with [jumpdest, swap1, pop, push1 ⟨13⟩, swap1, push2 ⟨2899⟩, jump jump_2899]
  have rd39 := evm_run_rfl rd38 with [jumpdest, push2 ⟨453⟩, jump jump_453]
  have rd40 := evm_run_rfl rd39 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiNT (by native_decide)]
  have rd41 := evm_run_rfl rd40 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1877⟩, jumpiNT (by native_decide)]
  have rd42 := evm_run_rfl rd41 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1431⟩, jumpiNT (by native_decide)]
  have rd43 := evm_run_rfl rd42 with [dup1, push1 ⟨3⟩, eq, push2 ⟨985⟩, jumpiNT (by native_decide)]
  have rd44 := evm_run_rfl rd43 with [push1 ⟨4⟩, eq, push2 ⟨540⟩, jumpiT (by native_decide) jump_540]
  have rd45 := evm_run_rfl rd44 with [jumpdest, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨966⟩, jumpiNT (by native_decide)]
  have rd46 := evm_run_rfl rd45 with [dup1, push1 ⟨1⟩, eq, push2 ⟨947⟩, jumpiNT (by native_decide)]
  have rd47 := evm_run_rfl rd46 with [dup1, push1 ⟨2⟩, eq, push2 ⟨928⟩, jumpiNT (by native_decide)]
  have rd48 := evm_run_rfl rd47 with [dup1, push1 ⟨3⟩, eq, push2 ⟨909⟩, jumpiNT (by native_decide)]
  have rd49 := evm_run_rfl rd48 with [dup1, push1 ⟨4⟩, eq, push2 ⟨890⟩, jumpiNT (by native_decide)]
  have rd50 := evm_run_rfl rd49 with [dup1, push1 ⟨5⟩, eq, push2 ⟨871⟩, jumpiNT (by native_decide)]
  have rd51 := evm_run_rfl rd50 with [dup1, push1 ⟨6⟩, eq, push2 ⟨852⟩, jumpiNT (by native_decide)]
  have rd52 := evm_run_rfl rd51 with [dup1, push1 ⟨7⟩, eq, push2 ⟨833⟩, jumpiNT (by native_decide)]
  have rd53 := evm_run_rfl rd52 with [dup1, push1 ⟨8⟩, eq, push2 ⟨814⟩, jumpiNT (by native_decide)]
  have rd54 := evm_run_rfl rd53 with [dup1, push1 ⟨9⟩, eq, push2 ⟨795⟩, jumpiNT (by native_decide)]
  have rd55 := evm_run_rfl rd54 with [dup1, dup15, eq, push2 ⟨776⟩, jumpiNT (by native_decide)]
  have rd56 := evm_run_rfl rd55 with [dup1, push1 ⟨11⟩, eq, push2 ⟨757⟩, jumpiNT (by native_decide)]
  have rd57 := evm_run_rfl rd56 with [dup1, push1 ⟨12⟩, eq, push2 ⟨738⟩, jumpiNT (by native_decide)]
  have rd58 := evm_run_rfl rd57 with [dup1, push1 ⟨13⟩, eq, push2 ⟨719⟩, jumpiNT (by native_decide)]
  have rd59 := evm_run_rfl rd58 with [dup1, push1 ⟨14⟩, eq, push2 ⟨700⟩, jumpiNT (by native_decide)]
  have rd60 := evm_run_rfl rd59 with [push1 ⟨15⟩, eq, push2 ⟨682⟩, jumpiT (by native_decide) jump_682]
  have rd61 := evm_run_rfl rd60 with [jumpdest, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨6⟩, swap8, swap2, swap3, pop, pop, push2 ⟨673⟩, jump jump_673]
  have rd62 := evm_run_rfl rd61 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨494⟩, jump jump_494]
  have rd63 := evm_run_rfl rd62 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd64 := RD.runtimeMload rd63 (by old_decode) (by simp; omega)
  have rd65 := evm_run_rfl rd64 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd66 := evm_run_rfl rd65 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_511]
  have rd67 := evm_run_rfl rd66 with [jumpdest, add, and, swap8, dup7]
  have rd68 := RD.runtimeMstore rd67 (by old_decode) (by simp; omega)
  have rd69 := evm_run_rfl rd68 with [push1 ⟨128⟩, dup7, add]
  have rd70 := RD.runtimeMstore rd69 (by old_decode) (by simp; omega)
  have rd71 := evm_run_rfl rd70 with [push2 ⟨268⟩, jump jump_268]
  have rd72 := evm_run_rfl rd71 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_526]
  have rd73 := evm_run_rfl rd72 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd74 := RD.runtimeMstore rd73 (by old_decode) (by simp; omega)
  have rd75 := evm_run_rfl rd74 with [push1 ⟨64⟩, dup3, add]
  have rd76 := RD.runtimeMstore rd75 (by old_decode) (by simp; omega)
  have rd77 := evm_run_rfl rd76 with [add]
  have rd78 := RD.runtimeMstore rd77 (by old_decode) (by simp; omega)
  have rd79 := evm_run_rfl rd78 with [jump jump_8991]
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
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd79⟩


end Ripemd160Old
