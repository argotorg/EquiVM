import Examples.Ripemd160Old.HashRightRound0
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000
namespace Ripemd160Old
open Ripemd160

theorem runtime_rightRoundHelper_1 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I 1 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) 0 1).mem
      (oldRightRoundCursor c (hashScratchPtr I) 0 1).aw
      rdata (cA, σ) k' C' := by
  simp only [oldRightHelperStack] at rd
  have rd1 := evm_run_rfl rd with [jumpdest, push1 ⟨32⟩, swap2, push2 ⟨4343⟩, push1 ⟨10⟩, push4 ⟨4294967295⟩, swap3, dup5]
  have rd2 := RD.runtimeMload rd1 (by old_decode) (by simp; omega)
  have rd3 := evm_run_rfl rd2 with [swap1, dup7, dup7, add]
  have rd4 := RD.runtimeMload rd3 (by old_decode) (by simp; omega)
  have rd5 := evm_run_rfl rd4 with [swap5, push1 ⟨64⟩, dup8, add]
  have rd6 := RD.runtimeMload rd5 (by old_decode) (by simp; omega)
  have rd7 := evm_run_rfl rd6 with [swap3, push2 ⟨4328⟩, push1 ⟨96⟩, dup10, add]
  have rd8 := RD.runtimeMload rd7 (by old_decode) (by simp; omega)
  have rd9 := evm_run_rfl rd8 with [swap4, dup4, dup10, push1 ⟨128⟩, dup13, add]
  have rd10 := RD.runtimeMload rd9 (by old_decode) (by simp; omega)
  have rd11 := evm_run_rfl rd10 with [swap14, dup15, swap6, dup4, push1 ⟨16⟩, dup4, div, swap6, push0, swap4, dup12, dup14, push0, swap8, dup11, dup1, push0, eq, push2 ⟨8238⟩, jumpiT (by native_decide) jump_8238]
  have rd12 := evm_run_rfl rd11 with [jumpdest, pop, swap4, swap7, pop, pop, swap1, swap6, pop, not, dup13, or, xor, swap3, push4 ⟨1352829926⟩, swap5, dup16, dup14, dup14, swap2, push2 ⟨4225⟩, jump jump_4225]
  have rd13 := evm_run_rfl rd12 with [jumpdest, pop, pop, pop, push0, swap1, dup9, dup1, push0, eq, push2 ⟨7821⟩, jumpiT (by native_decide) jump_7821]
  have rd14 := evm_run_rfl rd13 with [jumpdest, pop, push1 ⟨16⟩, dup2, mod, dup1, push0, eq, push2 ⟨8119⟩, jumpiNT (by native_decide)]
  have rd15 := evm_run_rfl rd14 with [dup1, push1 ⟨1⟩, eq, push2 ⟨8108⟩, jumpiT (by native_decide) jump_8108]
  have rd16 := evm_run_rfl rd15 with [jumpdest, pop, swap1, pop, push1 ⟨14⟩, swap1, push2 ⟨7952⟩, jump jump_7952]
  have rd17 := evm_run_rfl rd16 with [jumpdest, push2 ⟨4270⟩, jump jump_4270]
  have rd18 := evm_run_rfl rd17 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨6140⟩, jumpiT (by native_decide) jump_6140]
  have rd19 := evm_run_rfl rd18 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨6567⟩, jumpiNT (by native_decide)]
  have rd20 := evm_run_rfl rd19 with [dup1, push1 ⟨1⟩, eq, push2 ⟨6548⟩, jumpiT (by native_decide) jump_6548]
  have rd21 := evm_run_rfl rd20 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨9⟩, swap8, swap2, swap3, pop, pop, push2 ⟨6274⟩, jump jump_6274]
  have rd22 := evm_run_rfl rd21 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨4311⟩, jump jump_4311]
  have rd23 := evm_run_rfl rd22 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd24 := RD.runtimeMload rd23 (by old_decode) (by simp; omega)
  have rd25 := evm_run_rfl rd24 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd26 := evm_run_rfl rd25 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4328]
  have rd27 := evm_run_rfl rd26 with [jumpdest, add, and, swap8, dup7]
  have rd28 := RD.runtimeMstore rd27 (by old_decode) (by simp; omega)
  have rd29 := evm_run_rfl rd28 with [push1 ⟨128⟩, dup7, add]
  have rd30 := RD.runtimeMstore rd29 (by old_decode) (by simp; omega)
  have rd31 := evm_run_rfl rd30 with [push2 ⟨268⟩, jump jump_268]
  have rd32 := evm_run_rfl rd31 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4343]
  have rd33 := evm_run_rfl rd32 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd34 := RD.runtimeMstore rd33 (by old_decode) (by simp; omega)
  have rd35 := evm_run_rfl rd34 with [push1 ⟨64⟩, dup3, add]
  have rd36 := RD.runtimeMstore rd35 (by old_decode) (by simp; omega)
  have rd37 := evm_run_rfl rd36 with [add]
  have rd38 := RD.runtimeMstore rd37 (by old_decode) (by simp; omega)
  have rd39 := evm_run_rfl rd38 with [jump jump_8967]
  exact ⟨_, _, by
    simpa [oldRightHelperStack, oldRightRoundCursor, runtimeRoundPreludeCursor,
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
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd39⟩

theorem runtime_rightRoundHelper_2 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I 2 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) 0 2).mem
      (oldRightRoundCursor c (hashScratchPtr I) 0 2).aw
      rdata (cA, σ) k' C' := by
  simp only [oldRightHelperStack] at rd
  have rd1 := evm_run_rfl rd with [jumpdest, push1 ⟨32⟩, swap2, push2 ⟨4343⟩, push1 ⟨10⟩, push4 ⟨4294967295⟩, swap3, dup5]
  have rd2 := RD.runtimeMload rd1 (by old_decode) (by simp; omega)
  have rd3 := evm_run_rfl rd2 with [swap1, dup7, dup7, add]
  have rd4 := RD.runtimeMload rd3 (by old_decode) (by simp; omega)
  have rd5 := evm_run_rfl rd4 with [swap5, push1 ⟨64⟩, dup8, add]
  have rd6 := RD.runtimeMload rd5 (by old_decode) (by simp; omega)
  have rd7 := evm_run_rfl rd6 with [swap3, push2 ⟨4328⟩, push1 ⟨96⟩, dup10, add]
  have rd8 := RD.runtimeMload rd7 (by old_decode) (by simp; omega)
  have rd9 := evm_run_rfl rd8 with [swap4, dup4, dup10, push1 ⟨128⟩, dup13, add]
  have rd10 := RD.runtimeMload rd9 (by old_decode) (by simp; omega)
  have rd11 := evm_run_rfl rd10 with [swap14, dup15, swap6, dup4, push1 ⟨16⟩, dup4, div, swap6, push0, swap4, dup12, dup14, push0, swap8, dup11, dup1, push0, eq, push2 ⟨8238⟩, jumpiT (by native_decide) jump_8238]
  have rd12 := evm_run_rfl rd11 with [jumpdest, pop, swap4, swap7, pop, pop, swap1, swap6, pop, not, dup13, or, xor, swap3, push4 ⟨1352829926⟩, swap5, dup16, dup14, dup14, swap2, push2 ⟨4225⟩, jump jump_4225]
  have rd13 := evm_run_rfl rd12 with [jumpdest, pop, pop, pop, push0, swap1, dup9, dup1, push0, eq, push2 ⟨7821⟩, jumpiT (by native_decide) jump_7821]
  have rd14 := evm_run_rfl rd13 with [jumpdest, pop, push1 ⟨16⟩, dup2, mod, dup1, push0, eq, push2 ⟨8119⟩, jumpiNT (by native_decide)]
  have rd15 := evm_run_rfl rd14 with [dup1, push1 ⟨1⟩, eq, push2 ⟨8108⟩, jumpiNT (by native_decide)]
  have rd16 := evm_run_rfl rd15 with [dup1, push1 ⟨2⟩, eq, push2 ⟨8097⟩, jumpiT (by native_decide) jump_8097]
  have rd17 := evm_run_rfl rd16 with [jumpdest, pop, swap1, pop, push1 ⟨7⟩, swap1, push2 ⟨7952⟩, jump jump_7952]
  have rd18 := evm_run_rfl rd17 with [jumpdest, push2 ⟨4270⟩, jump jump_4270]
  have rd19 := evm_run_rfl rd18 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨6140⟩, jumpiT (by native_decide) jump_6140]
  have rd20 := evm_run_rfl rd19 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨6567⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [dup1, push1 ⟨1⟩, eq, push2 ⟨6548⟩, jumpiNT (by native_decide)]
  have rd22 := evm_run_rfl rd21 with [dup1, push1 ⟨2⟩, eq, push2 ⟨6529⟩, jumpiT (by native_decide) jump_6529]
  have rd23 := evm_run_rfl rd22 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨9⟩, swap8, swap2, swap3, pop, pop, push2 ⟨6274⟩, jump jump_6274]
  have rd24 := evm_run_rfl rd23 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨4311⟩, jump jump_4311]
  have rd25 := evm_run_rfl rd24 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd26 := RD.runtimeMload rd25 (by old_decode) (by simp; omega)
  have rd27 := evm_run_rfl rd26 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd28 := evm_run_rfl rd27 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4328]
  have rd29 := evm_run_rfl rd28 with [jumpdest, add, and, swap8, dup7]
  have rd30 := RD.runtimeMstore rd29 (by old_decode) (by simp; omega)
  have rd31 := evm_run_rfl rd30 with [push1 ⟨128⟩, dup7, add]
  have rd32 := RD.runtimeMstore rd31 (by old_decode) (by simp; omega)
  have rd33 := evm_run_rfl rd32 with [push2 ⟨268⟩, jump jump_268]
  have rd34 := evm_run_rfl rd33 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4343]
  have rd35 := evm_run_rfl rd34 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd36 := RD.runtimeMstore rd35 (by old_decode) (by simp; omega)
  have rd37 := evm_run_rfl rd36 with [push1 ⟨64⟩, dup3, add]
  have rd38 := RD.runtimeMstore rd37 (by old_decode) (by simp; omega)
  have rd39 := evm_run_rfl rd38 with [add]
  have rd40 := RD.runtimeMstore rd39 (by old_decode) (by simp; omega)
  have rd41 := evm_run_rfl rd40 with [jump jump_8967]
  exact ⟨_, _, by
    simpa [oldRightHelperStack, oldRightRoundCursor, runtimeRoundPreludeCursor,
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
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd41⟩

theorem runtime_rightRoundHelper_3 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I 3 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) 0 3).mem
      (oldRightRoundCursor c (hashScratchPtr I) 0 3).aw
      rdata (cA, σ) k' C' := by
  simp only [oldRightHelperStack] at rd
  have rd1 := evm_run_rfl rd with [jumpdest, push1 ⟨32⟩, swap2, push2 ⟨4343⟩, push1 ⟨10⟩, push4 ⟨4294967295⟩, swap3, dup5]
  have rd2 := RD.runtimeMload rd1 (by old_decode) (by simp; omega)
  have rd3 := evm_run_rfl rd2 with [swap1, dup7, dup7, add]
  have rd4 := RD.runtimeMload rd3 (by old_decode) (by simp; omega)
  have rd5 := evm_run_rfl rd4 with [swap5, push1 ⟨64⟩, dup8, add]
  have rd6 := RD.runtimeMload rd5 (by old_decode) (by simp; omega)
  have rd7 := evm_run_rfl rd6 with [swap3, push2 ⟨4328⟩, push1 ⟨96⟩, dup10, add]
  have rd8 := RD.runtimeMload rd7 (by old_decode) (by simp; omega)
  have rd9 := evm_run_rfl rd8 with [swap4, dup4, dup10, push1 ⟨128⟩, dup13, add]
  have rd10 := RD.runtimeMload rd9 (by old_decode) (by simp; omega)
  have rd11 := evm_run_rfl rd10 with [swap14, dup15, swap6, dup4, push1 ⟨16⟩, dup4, div, swap6, push0, swap4, dup12, dup14, push0, swap8, dup11, dup1, push0, eq, push2 ⟨8238⟩, jumpiT (by native_decide) jump_8238]
  have rd12 := evm_run_rfl rd11 with [jumpdest, pop, swap4, swap7, pop, pop, swap1, swap6, pop, not, dup13, or, xor, swap3, push4 ⟨1352829926⟩, swap5, dup16, dup14, dup14, swap2, push2 ⟨4225⟩, jump jump_4225]
  have rd13 := evm_run_rfl rd12 with [jumpdest, pop, pop, pop, push0, swap1, dup9, dup1, push0, eq, push2 ⟨7821⟩, jumpiT (by native_decide) jump_7821]
  have rd14 := evm_run_rfl rd13 with [jumpdest, pop, push1 ⟨16⟩, dup2, mod, dup1, push0, eq, push2 ⟨8119⟩, jumpiNT (by native_decide)]
  have rd15 := evm_run_rfl rd14 with [dup1, push1 ⟨1⟩, eq, push2 ⟨8108⟩, jumpiNT (by native_decide)]
  have rd16 := evm_run_rfl rd15 with [dup1, push1 ⟨2⟩, eq, push2 ⟨8097⟩, jumpiNT (by native_decide)]
  have rd17 := evm_run_rfl rd16 with [dup1, push1 ⟨3⟩, eq, push2 ⟨8087⟩, jumpiT (by native_decide) jump_8087]
  have rd18 := evm_run_rfl rd17 with [jumpdest, pop, swap1, pop, push0, swap1, push2 ⟨7952⟩, jump jump_7952]
  have rd19 := evm_run_rfl rd18 with [jumpdest, push2 ⟨4270⟩, jump jump_4270]
  have rd20 := evm_run_rfl rd19 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨6140⟩, jumpiT (by native_decide) jump_6140]
  have rd21 := evm_run_rfl rd20 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨6567⟩, jumpiNT (by native_decide)]
  have rd22 := evm_run_rfl rd21 with [dup1, push1 ⟨1⟩, eq, push2 ⟨6548⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨2⟩, eq, push2 ⟨6529⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup1, push1 ⟨3⟩, eq, push2 ⟨6510⟩, jumpiT (by native_decide) jump_6510]
  have rd25 := evm_run_rfl rd24 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨11⟩, swap8, swap2, swap3, pop, pop, push2 ⟨6274⟩, jump jump_6274]
  have rd26 := evm_run_rfl rd25 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨4311⟩, jump jump_4311]
  have rd27 := evm_run_rfl rd26 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd28 := RD.runtimeMload rd27 (by old_decode) (by simp; omega)
  have rd29 := evm_run_rfl rd28 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd30 := evm_run_rfl rd29 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4328]
  have rd31 := evm_run_rfl rd30 with [jumpdest, add, and, swap8, dup7]
  have rd32 := RD.runtimeMstore rd31 (by old_decode) (by simp; omega)
  have rd33 := evm_run_rfl rd32 with [push1 ⟨128⟩, dup7, add]
  have rd34 := RD.runtimeMstore rd33 (by old_decode) (by simp; omega)
  have rd35 := evm_run_rfl rd34 with [push2 ⟨268⟩, jump jump_268]
  have rd36 := evm_run_rfl rd35 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4343]
  have rd37 := evm_run_rfl rd36 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd38 := RD.runtimeMstore rd37 (by old_decode) (by simp; omega)
  have rd39 := evm_run_rfl rd38 with [push1 ⟨64⟩, dup3, add]
  have rd40 := RD.runtimeMstore rd39 (by old_decode) (by simp; omega)
  have rd41 := evm_run_rfl rd40 with [add]
  have rd42 := RD.runtimeMstore rd41 (by old_decode) (by simp; omega)
  have rd43 := evm_run_rfl rd42 with [jump jump_8967]
  exact ⟨_, _, by
    simpa [oldRightHelperStack, oldRightRoundCursor, runtimeRoundPreludeCursor,
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

theorem runtime_rightRoundHelper_4 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I 4 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) 0 4).mem
      (oldRightRoundCursor c (hashScratchPtr I) 0 4).aw
      rdata (cA, σ) k' C' := by
  simp only [oldRightHelperStack] at rd
  have rd1 := evm_run_rfl rd with [jumpdest, push1 ⟨32⟩, swap2, push2 ⟨4343⟩, push1 ⟨10⟩, push4 ⟨4294967295⟩, swap3, dup5]
  have rd2 := RD.runtimeMload rd1 (by old_decode) (by simp; omega)
  have rd3 := evm_run_rfl rd2 with [swap1, dup7, dup7, add]
  have rd4 := RD.runtimeMload rd3 (by old_decode) (by simp; omega)
  have rd5 := evm_run_rfl rd4 with [swap5, push1 ⟨64⟩, dup8, add]
  have rd6 := RD.runtimeMload rd5 (by old_decode) (by simp; omega)
  have rd7 := evm_run_rfl rd6 with [swap3, push2 ⟨4328⟩, push1 ⟨96⟩, dup10, add]
  have rd8 := RD.runtimeMload rd7 (by old_decode) (by simp; omega)
  have rd9 := evm_run_rfl rd8 with [swap4, dup4, dup10, push1 ⟨128⟩, dup13, add]
  have rd10 := RD.runtimeMload rd9 (by old_decode) (by simp; omega)
  have rd11 := evm_run_rfl rd10 with [swap14, dup15, swap6, dup4, push1 ⟨16⟩, dup4, div, swap6, push0, swap4, dup12, dup14, push0, swap8, dup11, dup1, push0, eq, push2 ⟨8238⟩, jumpiT (by native_decide) jump_8238]
  have rd12 := evm_run_rfl rd11 with [jumpdest, pop, swap4, swap7, pop, pop, swap1, swap6, pop, not, dup13, or, xor, swap3, push4 ⟨1352829926⟩, swap5, dup16, dup14, dup14, swap2, push2 ⟨4225⟩, jump jump_4225]
  have rd13 := evm_run_rfl rd12 with [jumpdest, pop, pop, pop, push0, swap1, dup9, dup1, push0, eq, push2 ⟨7821⟩, jumpiT (by native_decide) jump_7821]
  have rd14 := evm_run_rfl rd13 with [jumpdest, pop, push1 ⟨16⟩, dup2, mod, dup1, push0, eq, push2 ⟨8119⟩, jumpiNT (by native_decide)]
  have rd15 := evm_run_rfl rd14 with [dup1, push1 ⟨1⟩, eq, push2 ⟨8108⟩, jumpiNT (by native_decide)]
  have rd16 := evm_run_rfl rd15 with [dup1, push1 ⟨2⟩, eq, push2 ⟨8097⟩, jumpiNT (by native_decide)]
  have rd17 := evm_run_rfl rd16 with [dup1, push1 ⟨3⟩, eq, push2 ⟨8087⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [dup1, push1 ⟨4⟩, eq, push2 ⟨8076⟩, jumpiT (by native_decide) jump_8076]
  have rd19 := evm_run_rfl rd18 with [jumpdest, pop, swap1, pop, push1 ⟨9⟩, swap1, push2 ⟨7952⟩, jump jump_7952]
  have rd20 := evm_run_rfl rd19 with [jumpdest, push2 ⟨4270⟩, jump jump_4270]
  have rd21 := evm_run_rfl rd20 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨6140⟩, jumpiT (by native_decide) jump_6140]
  have rd22 := evm_run_rfl rd21 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨6567⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨1⟩, eq, push2 ⟨6548⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup1, push1 ⟨2⟩, eq, push2 ⟨6529⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨3⟩, eq, push2 ⟨6510⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup1, push1 ⟨4⟩, eq, push2 ⟨6491⟩, jumpiT (by native_decide) jump_6491]
  have rd27 := evm_run_rfl rd26 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨13⟩, swap8, swap2, swap3, pop, pop, push2 ⟨6274⟩, jump jump_6274]
  have rd28 := evm_run_rfl rd27 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨4311⟩, jump jump_4311]
  have rd29 := evm_run_rfl rd28 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd30 := RD.runtimeMload rd29 (by old_decode) (by simp; omega)
  have rd31 := evm_run_rfl rd30 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd32 := evm_run_rfl rd31 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4328]
  have rd33 := evm_run_rfl rd32 with [jumpdest, add, and, swap8, dup7]
  have rd34 := RD.runtimeMstore rd33 (by old_decode) (by simp; omega)
  have rd35 := evm_run_rfl rd34 with [push1 ⟨128⟩, dup7, add]
  have rd36 := RD.runtimeMstore rd35 (by old_decode) (by simp; omega)
  have rd37 := evm_run_rfl rd36 with [push2 ⟨268⟩, jump jump_268]
  have rd38 := evm_run_rfl rd37 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4343]
  have rd39 := evm_run_rfl rd38 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd40 := RD.runtimeMstore rd39 (by old_decode) (by simp; omega)
  have rd41 := evm_run_rfl rd40 with [push1 ⟨64⟩, dup3, add]
  have rd42 := RD.runtimeMstore rd41 (by old_decode) (by simp; omega)
  have rd43 := evm_run_rfl rd42 with [add]
  have rd44 := RD.runtimeMstore rd43 (by old_decode) (by simp; omega)
  have rd45 := evm_run_rfl rd44 with [jump jump_8967]
  exact ⟨_, _, by
    simpa [oldRightHelperStack, oldRightRoundCursor, runtimeRoundPreludeCursor,
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

theorem runtime_rightRoundHelper_5 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I 5 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) 0 5).mem
      (oldRightRoundCursor c (hashScratchPtr I) 0 5).aw
      rdata (cA, σ) k' C' := by
  simp only [oldRightHelperStack] at rd
  have rd1 := evm_run_rfl rd with [jumpdest, push1 ⟨32⟩, swap2, push2 ⟨4343⟩, push1 ⟨10⟩, push4 ⟨4294967295⟩, swap3, dup5]
  have rd2 := RD.runtimeMload rd1 (by old_decode) (by simp; omega)
  have rd3 := evm_run_rfl rd2 with [swap1, dup7, dup7, add]
  have rd4 := RD.runtimeMload rd3 (by old_decode) (by simp; omega)
  have rd5 := evm_run_rfl rd4 with [swap5, push1 ⟨64⟩, dup8, add]
  have rd6 := RD.runtimeMload rd5 (by old_decode) (by simp; omega)
  have rd7 := evm_run_rfl rd6 with [swap3, push2 ⟨4328⟩, push1 ⟨96⟩, dup10, add]
  have rd8 := RD.runtimeMload rd7 (by old_decode) (by simp; omega)
  have rd9 := evm_run_rfl rd8 with [swap4, dup4, dup10, push1 ⟨128⟩, dup13, add]
  have rd10 := RD.runtimeMload rd9 (by old_decode) (by simp; omega)
  have rd11 := evm_run_rfl rd10 with [swap14, dup15, swap6, dup4, push1 ⟨16⟩, dup4, div, swap6, push0, swap4, dup12, dup14, push0, swap8, dup11, dup1, push0, eq, push2 ⟨8238⟩, jumpiT (by native_decide) jump_8238]
  have rd12 := evm_run_rfl rd11 with [jumpdest, pop, swap4, swap7, pop, pop, swap1, swap6, pop, not, dup13, or, xor, swap3, push4 ⟨1352829926⟩, swap5, dup16, dup14, dup14, swap2, push2 ⟨4225⟩, jump jump_4225]
  have rd13 := evm_run_rfl rd12 with [jumpdest, pop, pop, pop, push0, swap1, dup9, dup1, push0, eq, push2 ⟨7821⟩, jumpiT (by native_decide) jump_7821]
  have rd14 := evm_run_rfl rd13 with [jumpdest, pop, push1 ⟨16⟩, dup2, mod, dup1, push0, eq, push2 ⟨8119⟩, jumpiNT (by native_decide)]
  have rd15 := evm_run_rfl rd14 with [dup1, push1 ⟨1⟩, eq, push2 ⟨8108⟩, jumpiNT (by native_decide)]
  have rd16 := evm_run_rfl rd15 with [dup1, push1 ⟨2⟩, eq, push2 ⟨8097⟩, jumpiNT (by native_decide)]
  have rd17 := evm_run_rfl rd16 with [dup1, push1 ⟨3⟩, eq, push2 ⟨8087⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [dup1, push1 ⟨4⟩, eq, push2 ⟨8076⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [dup1, push1 ⟨5⟩, eq, push2 ⟨8065⟩, jumpiT (by native_decide) jump_8065]
  have rd20 := evm_run_rfl rd19 with [jumpdest, pop, swap1, pop, push1 ⟨2⟩, swap1, push2 ⟨7952⟩, jump jump_7952]
  have rd21 := evm_run_rfl rd20 with [jumpdest, push2 ⟨4270⟩, jump jump_4270]
  have rd22 := evm_run_rfl rd21 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨6140⟩, jumpiT (by native_decide) jump_6140]
  have rd23 := evm_run_rfl rd22 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨6567⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup1, push1 ⟨1⟩, eq, push2 ⟨6548⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨2⟩, eq, push2 ⟨6529⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup1, push1 ⟨3⟩, eq, push2 ⟨6510⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨4⟩, eq, push2 ⟨6491⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨5⟩, eq, push2 ⟨6472⟩, jumpiT (by native_decide) jump_6472]
  have rd29 := evm_run_rfl rd28 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨15⟩, swap8, swap2, swap3, pop, pop, push2 ⟨6274⟩, jump jump_6274]
  have rd30 := evm_run_rfl rd29 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨4311⟩, jump jump_4311]
  have rd31 := evm_run_rfl rd30 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd32 := RD.runtimeMload rd31 (by old_decode) (by simp; omega)
  have rd33 := evm_run_rfl rd32 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd34 := evm_run_rfl rd33 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4328]
  have rd35 := evm_run_rfl rd34 with [jumpdest, add, and, swap8, dup7]
  have rd36 := RD.runtimeMstore rd35 (by old_decode) (by simp; omega)
  have rd37 := evm_run_rfl rd36 with [push1 ⟨128⟩, dup7, add]
  have rd38 := RD.runtimeMstore rd37 (by old_decode) (by simp; omega)
  have rd39 := evm_run_rfl rd38 with [push2 ⟨268⟩, jump jump_268]
  have rd40 := evm_run_rfl rd39 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4343]
  have rd41 := evm_run_rfl rd40 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd42 := RD.runtimeMstore rd41 (by old_decode) (by simp; omega)
  have rd43 := evm_run_rfl rd42 with [push1 ⟨64⟩, dup3, add]
  have rd44 := RD.runtimeMstore rd43 (by old_decode) (by simp; omega)
  have rd45 := evm_run_rfl rd44 with [add]
  have rd46 := RD.runtimeMstore rd45 (by old_decode) (by simp; omega)
  have rd47 := evm_run_rfl rd46 with [jump jump_8967]
  exact ⟨_, _, by
    simpa [oldRightHelperStack, oldRightRoundCursor, runtimeRoundPreludeCursor,
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

theorem runtime_rightRoundHelper_6 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I 6 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) 0 6).mem
      (oldRightRoundCursor c (hashScratchPtr I) 0 6).aw
      rdata (cA, σ) k' C' := by
  simp only [oldRightHelperStack] at rd
  have rd1 := evm_run_rfl rd with [jumpdest, push1 ⟨32⟩, swap2, push2 ⟨4343⟩, push1 ⟨10⟩, push4 ⟨4294967295⟩, swap3, dup5]
  have rd2 := RD.runtimeMload rd1 (by old_decode) (by simp; omega)
  have rd3 := evm_run_rfl rd2 with [swap1, dup7, dup7, add]
  have rd4 := RD.runtimeMload rd3 (by old_decode) (by simp; omega)
  have rd5 := evm_run_rfl rd4 with [swap5, push1 ⟨64⟩, dup8, add]
  have rd6 := RD.runtimeMload rd5 (by old_decode) (by simp; omega)
  have rd7 := evm_run_rfl rd6 with [swap3, push2 ⟨4328⟩, push1 ⟨96⟩, dup10, add]
  have rd8 := RD.runtimeMload rd7 (by old_decode) (by simp; omega)
  have rd9 := evm_run_rfl rd8 with [swap4, dup4, dup10, push1 ⟨128⟩, dup13, add]
  have rd10 := RD.runtimeMload rd9 (by old_decode) (by simp; omega)
  have rd11 := evm_run_rfl rd10 with [swap14, dup15, swap6, dup4, push1 ⟨16⟩, dup4, div, swap6, push0, swap4, dup12, dup14, push0, swap8, dup11, dup1, push0, eq, push2 ⟨8238⟩, jumpiT (by native_decide) jump_8238]
  have rd12 := evm_run_rfl rd11 with [jumpdest, pop, swap4, swap7, pop, pop, swap1, swap6, pop, not, dup13, or, xor, swap3, push4 ⟨1352829926⟩, swap5, dup16, dup14, dup14, swap2, push2 ⟨4225⟩, jump jump_4225]
  have rd13 := evm_run_rfl rd12 with [jumpdest, pop, pop, pop, push0, swap1, dup9, dup1, push0, eq, push2 ⟨7821⟩, jumpiT (by native_decide) jump_7821]
  have rd14 := evm_run_rfl rd13 with [jumpdest, pop, push1 ⟨16⟩, dup2, mod, dup1, push0, eq, push2 ⟨8119⟩, jumpiNT (by native_decide)]
  have rd15 := evm_run_rfl rd14 with [dup1, push1 ⟨1⟩, eq, push2 ⟨8108⟩, jumpiNT (by native_decide)]
  have rd16 := evm_run_rfl rd15 with [dup1, push1 ⟨2⟩, eq, push2 ⟨8097⟩, jumpiNT (by native_decide)]
  have rd17 := evm_run_rfl rd16 with [dup1, push1 ⟨3⟩, eq, push2 ⟨8087⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [dup1, push1 ⟨4⟩, eq, push2 ⟨8076⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [dup1, push1 ⟨5⟩, eq, push2 ⟨8065⟩, jumpiNT (by native_decide)]
  have rd20 := evm_run_rfl rd19 with [dup1, push1 ⟨6⟩, eq, push2 ⟨8054⟩, jumpiT (by native_decide) jump_8054]
  have rd21 := evm_run_rfl rd20 with [jumpdest, pop, swap1, pop, push1 ⟨11⟩, swap1, push2 ⟨7952⟩, jump jump_7952]
  have rd22 := evm_run_rfl rd21 with [jumpdest, push2 ⟨4270⟩, jump jump_4270]
  have rd23 := evm_run_rfl rd22 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨6140⟩, jumpiT (by native_decide) jump_6140]
  have rd24 := evm_run_rfl rd23 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨6567⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨1⟩, eq, push2 ⟨6548⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup1, push1 ⟨2⟩, eq, push2 ⟨6529⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨3⟩, eq, push2 ⟨6510⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨4⟩, eq, push2 ⟨6491⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [dup1, push1 ⟨5⟩, eq, push2 ⟨6472⟩, jumpiNT (by native_decide)]
  have rd30 := evm_run_rfl rd29 with [dup1, push1 ⟨6⟩, eq, push2 ⟨6453⟩, jumpiT (by native_decide) jump_6453]
  have rd31 := evm_run_rfl rd30 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨15⟩, swap8, swap2, swap3, pop, pop, push2 ⟨6274⟩, jump jump_6274]
  have rd32 := evm_run_rfl rd31 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨4311⟩, jump jump_4311]
  have rd33 := evm_run_rfl rd32 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd34 := RD.runtimeMload rd33 (by old_decode) (by simp; omega)
  have rd35 := evm_run_rfl rd34 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd36 := evm_run_rfl rd35 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4328]
  have rd37 := evm_run_rfl rd36 with [jumpdest, add, and, swap8, dup7]
  have rd38 := RD.runtimeMstore rd37 (by old_decode) (by simp; omega)
  have rd39 := evm_run_rfl rd38 with [push1 ⟨128⟩, dup7, add]
  have rd40 := RD.runtimeMstore rd39 (by old_decode) (by simp; omega)
  have rd41 := evm_run_rfl rd40 with [push2 ⟨268⟩, jump jump_268]
  have rd42 := evm_run_rfl rd41 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4343]
  have rd43 := evm_run_rfl rd42 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd44 := RD.runtimeMstore rd43 (by old_decode) (by simp; omega)
  have rd45 := evm_run_rfl rd44 with [push1 ⟨64⟩, dup3, add]
  have rd46 := RD.runtimeMstore rd45 (by old_decode) (by simp; omega)
  have rd47 := evm_run_rfl rd46 with [add]
  have rd48 := RD.runtimeMstore rd47 (by old_decode) (by simp; omega)
  have rd49 := evm_run_rfl rd48 with [jump jump_8967]
  exact ⟨_, _, by
    simpa [oldRightHelperStack, oldRightRoundCursor, runtimeRoundPreludeCursor,
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

theorem runtime_rightRoundHelper_7 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I 7 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) 0 7).mem
      (oldRightRoundCursor c (hashScratchPtr I) 0 7).aw
      rdata (cA, σ) k' C' := by
  simp only [oldRightHelperStack] at rd
  have rd1 := evm_run_rfl rd with [jumpdest, push1 ⟨32⟩, swap2, push2 ⟨4343⟩, push1 ⟨10⟩, push4 ⟨4294967295⟩, swap3, dup5]
  have rd2 := RD.runtimeMload rd1 (by old_decode) (by simp; omega)
  have rd3 := evm_run_rfl rd2 with [swap1, dup7, dup7, add]
  have rd4 := RD.runtimeMload rd3 (by old_decode) (by simp; omega)
  have rd5 := evm_run_rfl rd4 with [swap5, push1 ⟨64⟩, dup8, add]
  have rd6 := RD.runtimeMload rd5 (by old_decode) (by simp; omega)
  have rd7 := evm_run_rfl rd6 with [swap3, push2 ⟨4328⟩, push1 ⟨96⟩, dup10, add]
  have rd8 := RD.runtimeMload rd7 (by old_decode) (by simp; omega)
  have rd9 := evm_run_rfl rd8 with [swap4, dup4, dup10, push1 ⟨128⟩, dup13, add]
  have rd10 := RD.runtimeMload rd9 (by old_decode) (by simp; omega)
  have rd11 := evm_run_rfl rd10 with [swap14, dup15, swap6, dup4, push1 ⟨16⟩, dup4, div, swap6, push0, swap4, dup12, dup14, push0, swap8, dup11, dup1, push0, eq, push2 ⟨8238⟩, jumpiT (by native_decide) jump_8238]
  have rd12 := evm_run_rfl rd11 with [jumpdest, pop, swap4, swap7, pop, pop, swap1, swap6, pop, not, dup13, or, xor, swap3, push4 ⟨1352829926⟩, swap5, dup16, dup14, dup14, swap2, push2 ⟨4225⟩, jump jump_4225]
  have rd13 := evm_run_rfl rd12 with [jumpdest, pop, pop, pop, push0, swap1, dup9, dup1, push0, eq, push2 ⟨7821⟩, jumpiT (by native_decide) jump_7821]
  have rd14 := evm_run_rfl rd13 with [jumpdest, pop, push1 ⟨16⟩, dup2, mod, dup1, push0, eq, push2 ⟨8119⟩, jumpiNT (by native_decide)]
  have rd15 := evm_run_rfl rd14 with [dup1, push1 ⟨1⟩, eq, push2 ⟨8108⟩, jumpiNT (by native_decide)]
  have rd16 := evm_run_rfl rd15 with [dup1, push1 ⟨2⟩, eq, push2 ⟨8097⟩, jumpiNT (by native_decide)]
  have rd17 := evm_run_rfl rd16 with [dup1, push1 ⟨3⟩, eq, push2 ⟨8087⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [dup1, push1 ⟨4⟩, eq, push2 ⟨8076⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [dup1, push1 ⟨5⟩, eq, push2 ⟨8065⟩, jumpiNT (by native_decide)]
  have rd20 := evm_run_rfl rd19 with [dup1, push1 ⟨6⟩, eq, push2 ⟨8054⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [dup1, push1 ⟨7⟩, eq, push2 ⟨8043⟩, jumpiT (by native_decide) jump_8043]
  have rd22 := evm_run_rfl rd21 with [jumpdest, pop, swap1, pop, push1 ⟨4⟩, swap1, push2 ⟨7952⟩, jump jump_7952]
  have rd23 := evm_run_rfl rd22 with [jumpdest, push2 ⟨4270⟩, jump jump_4270]
  have rd24 := evm_run_rfl rd23 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨6140⟩, jumpiT (by native_decide) jump_6140]
  have rd25 := evm_run_rfl rd24 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨6567⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup1, push1 ⟨1⟩, eq, push2 ⟨6548⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨2⟩, eq, push2 ⟨6529⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨3⟩, eq, push2 ⟨6510⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [dup1, push1 ⟨4⟩, eq, push2 ⟨6491⟩, jumpiNT (by native_decide)]
  have rd30 := evm_run_rfl rd29 with [dup1, push1 ⟨5⟩, eq, push2 ⟨6472⟩, jumpiNT (by native_decide)]
  have rd31 := evm_run_rfl rd30 with [dup1, push1 ⟨6⟩, eq, push2 ⟨6453⟩, jumpiNT (by native_decide)]
  have rd32 := evm_run_rfl rd31 with [dup1, push1 ⟨7⟩, eq, push2 ⟨6434⟩, jumpiT (by native_decide) jump_6434]
  have rd33 := evm_run_rfl rd32 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨5⟩, swap8, swap2, swap3, pop, pop, push2 ⟨6274⟩, jump jump_6274]
  have rd34 := evm_run_rfl rd33 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨4311⟩, jump jump_4311]
  have rd35 := evm_run_rfl rd34 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd36 := RD.runtimeMload rd35 (by old_decode) (by simp; omega)
  have rd37 := evm_run_rfl rd36 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd38 := evm_run_rfl rd37 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4328]
  have rd39 := evm_run_rfl rd38 with [jumpdest, add, and, swap8, dup7]
  have rd40 := RD.runtimeMstore rd39 (by old_decode) (by simp; omega)
  have rd41 := evm_run_rfl rd40 with [push1 ⟨128⟩, dup7, add]
  have rd42 := RD.runtimeMstore rd41 (by old_decode) (by simp; omega)
  have rd43 := evm_run_rfl rd42 with [push2 ⟨268⟩, jump jump_268]
  have rd44 := evm_run_rfl rd43 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4343]
  have rd45 := evm_run_rfl rd44 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd46 := RD.runtimeMstore rd45 (by old_decode) (by simp; omega)
  have rd47 := evm_run_rfl rd46 with [push1 ⟨64⟩, dup3, add]
  have rd48 := RD.runtimeMstore rd47 (by old_decode) (by simp; omega)
  have rd49 := evm_run_rfl rd48 with [add]
  have rd50 := RD.runtimeMstore rd49 (by old_decode) (by simp; omega)
  have rd51 := evm_run_rfl rd50 with [jump jump_8967]
  exact ⟨_, _, by
    simpa [oldRightHelperStack, oldRightRoundCursor, runtimeRoundPreludeCursor,
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

theorem runtime_rightRoundHelper_8 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I 8 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) 0 8).mem
      (oldRightRoundCursor c (hashScratchPtr I) 0 8).aw
      rdata (cA, σ) k' C' := by
  simp only [oldRightHelperStack] at rd
  have rd1 := evm_run_rfl rd with [jumpdest, push1 ⟨32⟩, swap2, push2 ⟨4343⟩, push1 ⟨10⟩, push4 ⟨4294967295⟩, swap3, dup5]
  have rd2 := RD.runtimeMload rd1 (by old_decode) (by simp; omega)
  have rd3 := evm_run_rfl rd2 with [swap1, dup7, dup7, add]
  have rd4 := RD.runtimeMload rd3 (by old_decode) (by simp; omega)
  have rd5 := evm_run_rfl rd4 with [swap5, push1 ⟨64⟩, dup8, add]
  have rd6 := RD.runtimeMload rd5 (by old_decode) (by simp; omega)
  have rd7 := evm_run_rfl rd6 with [swap3, push2 ⟨4328⟩, push1 ⟨96⟩, dup10, add]
  have rd8 := RD.runtimeMload rd7 (by old_decode) (by simp; omega)
  have rd9 := evm_run_rfl rd8 with [swap4, dup4, dup10, push1 ⟨128⟩, dup13, add]
  have rd10 := RD.runtimeMload rd9 (by old_decode) (by simp; omega)
  have rd11 := evm_run_rfl rd10 with [swap14, dup15, swap6, dup4, push1 ⟨16⟩, dup4, div, swap6, push0, swap4, dup12, dup14, push0, swap8, dup11, dup1, push0, eq, push2 ⟨8238⟩, jumpiT (by native_decide) jump_8238]
  have rd12 := evm_run_rfl rd11 with [jumpdest, pop, swap4, swap7, pop, pop, swap1, swap6, pop, not, dup13, or, xor, swap3, push4 ⟨1352829926⟩, swap5, dup16, dup14, dup14, swap2, push2 ⟨4225⟩, jump jump_4225]
  have rd13 := evm_run_rfl rd12 with [jumpdest, pop, pop, pop, push0, swap1, dup9, dup1, push0, eq, push2 ⟨7821⟩, jumpiT (by native_decide) jump_7821]
  have rd14 := evm_run_rfl rd13 with [jumpdest, pop, push1 ⟨16⟩, dup2, mod, dup1, push0, eq, push2 ⟨8119⟩, jumpiNT (by native_decide)]
  have rd15 := evm_run_rfl rd14 with [dup1, push1 ⟨1⟩, eq, push2 ⟨8108⟩, jumpiNT (by native_decide)]
  have rd16 := evm_run_rfl rd15 with [dup1, push1 ⟨2⟩, eq, push2 ⟨8097⟩, jumpiNT (by native_decide)]
  have rd17 := evm_run_rfl rd16 with [dup1, push1 ⟨3⟩, eq, push2 ⟨8087⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [dup1, push1 ⟨4⟩, eq, push2 ⟨8076⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [dup1, push1 ⟨5⟩, eq, push2 ⟨8065⟩, jumpiNT (by native_decide)]
  have rd20 := evm_run_rfl rd19 with [dup1, push1 ⟨6⟩, eq, push2 ⟨8054⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [dup1, push1 ⟨7⟩, eq, push2 ⟨8043⟩, jumpiNT (by native_decide)]
  have rd22 := evm_run_rfl rd21 with [dup1, push1 ⟨8⟩, eq, push2 ⟨8032⟩, jumpiT (by native_decide) jump_8032]
  have rd23 := evm_run_rfl rd22 with [jumpdest, pop, swap1, pop, push1 ⟨13⟩, swap1, push2 ⟨7952⟩, jump jump_7952]
  have rd24 := evm_run_rfl rd23 with [jumpdest, push2 ⟨4270⟩, jump jump_4270]
  have rd25 := evm_run_rfl rd24 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨6140⟩, jumpiT (by native_decide) jump_6140]
  have rd26 := evm_run_rfl rd25 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨6567⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨1⟩, eq, push2 ⟨6548⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨2⟩, eq, push2 ⟨6529⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [dup1, push1 ⟨3⟩, eq, push2 ⟨6510⟩, jumpiNT (by native_decide)]
  have rd30 := evm_run_rfl rd29 with [dup1, push1 ⟨4⟩, eq, push2 ⟨6491⟩, jumpiNT (by native_decide)]
  have rd31 := evm_run_rfl rd30 with [dup1, push1 ⟨5⟩, eq, push2 ⟨6472⟩, jumpiNT (by native_decide)]
  have rd32 := evm_run_rfl rd31 with [dup1, push1 ⟨6⟩, eq, push2 ⟨6453⟩, jumpiNT (by native_decide)]
  have rd33 := evm_run_rfl rd32 with [dup1, push1 ⟨7⟩, eq, push2 ⟨6434⟩, jumpiNT (by native_decide)]
  have rd34 := evm_run_rfl rd33 with [dup1, push1 ⟨8⟩, eq, push2 ⟨6415⟩, jumpiT (by native_decide) jump_6415]
  have rd35 := evm_run_rfl rd34 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨7⟩, swap8, swap2, swap3, pop, pop, push2 ⟨6274⟩, jump jump_6274]
  have rd36 := evm_run_rfl rd35 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨4311⟩, jump jump_4311]
  have rd37 := evm_run_rfl rd36 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd38 := RD.runtimeMload rd37 (by old_decode) (by simp; omega)
  have rd39 := evm_run_rfl rd38 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd40 := evm_run_rfl rd39 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4328]
  have rd41 := evm_run_rfl rd40 with [jumpdest, add, and, swap8, dup7]
  have rd42 := RD.runtimeMstore rd41 (by old_decode) (by simp; omega)
  have rd43 := evm_run_rfl rd42 with [push1 ⟨128⟩, dup7, add]
  have rd44 := RD.runtimeMstore rd43 (by old_decode) (by simp; omega)
  have rd45 := evm_run_rfl rd44 with [push2 ⟨268⟩, jump jump_268]
  have rd46 := evm_run_rfl rd45 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4343]
  have rd47 := evm_run_rfl rd46 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd48 := RD.runtimeMstore rd47 (by old_decode) (by simp; omega)
  have rd49 := evm_run_rfl rd48 with [push1 ⟨64⟩, dup3, add]
  have rd50 := RD.runtimeMstore rd49 (by old_decode) (by simp; omega)
  have rd51 := evm_run_rfl rd50 with [add]
  have rd52 := RD.runtimeMstore rd51 (by old_decode) (by simp; omega)
  have rd53 := evm_run_rfl rd52 with [jump jump_8967]
  exact ⟨_, _, by
    simpa [oldRightHelperStack, oldRightRoundCursor, runtimeRoundPreludeCursor,
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

theorem runtime_rightRoundHelper_9 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I 9 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) 0 9).mem
      (oldRightRoundCursor c (hashScratchPtr I) 0 9).aw
      rdata (cA, σ) k' C' := by
  simp only [oldRightHelperStack] at rd
  have rd1 := evm_run_rfl rd with [jumpdest, push1 ⟨32⟩, swap2, push2 ⟨4343⟩, push1 ⟨10⟩, push4 ⟨4294967295⟩, swap3, dup5]
  have rd2 := RD.runtimeMload rd1 (by old_decode) (by simp; omega)
  have rd3 := evm_run_rfl rd2 with [swap1, dup7, dup7, add]
  have rd4 := RD.runtimeMload rd3 (by old_decode) (by simp; omega)
  have rd5 := evm_run_rfl rd4 with [swap5, push1 ⟨64⟩, dup8, add]
  have rd6 := RD.runtimeMload rd5 (by old_decode) (by simp; omega)
  have rd7 := evm_run_rfl rd6 with [swap3, push2 ⟨4328⟩, push1 ⟨96⟩, dup10, add]
  have rd8 := RD.runtimeMload rd7 (by old_decode) (by simp; omega)
  have rd9 := evm_run_rfl rd8 with [swap4, dup4, dup10, push1 ⟨128⟩, dup13, add]
  have rd10 := RD.runtimeMload rd9 (by old_decode) (by simp; omega)
  have rd11 := evm_run_rfl rd10 with [swap14, dup15, swap6, dup4, push1 ⟨16⟩, dup4, div, swap6, push0, swap4, dup12, dup14, push0, swap8, dup11, dup1, push0, eq, push2 ⟨8238⟩, jumpiT (by native_decide) jump_8238]
  have rd12 := evm_run_rfl rd11 with [jumpdest, pop, swap4, swap7, pop, pop, swap1, swap6, pop, not, dup13, or, xor, swap3, push4 ⟨1352829926⟩, swap5, dup16, dup14, dup14, swap2, push2 ⟨4225⟩, jump jump_4225]
  have rd13 := evm_run_rfl rd12 with [jumpdest, pop, pop, pop, push0, swap1, dup9, dup1, push0, eq, push2 ⟨7821⟩, jumpiT (by native_decide) jump_7821]
  have rd14 := evm_run_rfl rd13 with [jumpdest, pop, push1 ⟨16⟩, dup2, mod, dup1, push0, eq, push2 ⟨8119⟩, jumpiNT (by native_decide)]
  have rd15 := evm_run_rfl rd14 with [dup1, push1 ⟨1⟩, eq, push2 ⟨8108⟩, jumpiNT (by native_decide)]
  have rd16 := evm_run_rfl rd15 with [dup1, push1 ⟨2⟩, eq, push2 ⟨8097⟩, jumpiNT (by native_decide)]
  have rd17 := evm_run_rfl rd16 with [dup1, push1 ⟨3⟩, eq, push2 ⟨8087⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [dup1, push1 ⟨4⟩, eq, push2 ⟨8076⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [dup1, push1 ⟨5⟩, eq, push2 ⟨8065⟩, jumpiNT (by native_decide)]
  have rd20 := evm_run_rfl rd19 with [dup1, push1 ⟨6⟩, eq, push2 ⟨8054⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [dup1, push1 ⟨7⟩, eq, push2 ⟨8043⟩, jumpiNT (by native_decide)]
  have rd22 := evm_run_rfl rd21 with [dup1, push1 ⟨8⟩, eq, push2 ⟨8032⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨9⟩, eq, push2 ⟨8021⟩, jumpiT (by native_decide) jump_8021]
  have rd24 := evm_run_rfl rd23 with [jumpdest, pop, swap1, pop, push1 ⟨6⟩, swap1, push2 ⟨7952⟩, jump jump_7952]
  have rd25 := evm_run_rfl rd24 with [jumpdest, push2 ⟨4270⟩, jump jump_4270]
  have rd26 := evm_run_rfl rd25 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨6140⟩, jumpiT (by native_decide) jump_6140]
  have rd27 := evm_run_rfl rd26 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨6567⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨1⟩, eq, push2 ⟨6548⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [dup1, push1 ⟨2⟩, eq, push2 ⟨6529⟩, jumpiNT (by native_decide)]
  have rd30 := evm_run_rfl rd29 with [dup1, push1 ⟨3⟩, eq, push2 ⟨6510⟩, jumpiNT (by native_decide)]
  have rd31 := evm_run_rfl rd30 with [dup1, push1 ⟨4⟩, eq, push2 ⟨6491⟩, jumpiNT (by native_decide)]
  have rd32 := evm_run_rfl rd31 with [dup1, push1 ⟨5⟩, eq, push2 ⟨6472⟩, jumpiNT (by native_decide)]
  have rd33 := evm_run_rfl rd32 with [dup1, push1 ⟨6⟩, eq, push2 ⟨6453⟩, jumpiNT (by native_decide)]
  have rd34 := evm_run_rfl rd33 with [dup1, push1 ⟨7⟩, eq, push2 ⟨6434⟩, jumpiNT (by native_decide)]
  have rd35 := evm_run_rfl rd34 with [dup1, push1 ⟨8⟩, eq, push2 ⟨6415⟩, jumpiNT (by native_decide)]
  have rd36 := evm_run_rfl rd35 with [dup1, push1 ⟨9⟩, eq, push2 ⟨6396⟩, jumpiT (by native_decide) jump_6396]
  have rd37 := evm_run_rfl rd36 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨7⟩, swap8, swap2, swap3, pop, pop, push2 ⟨6274⟩, jump jump_6274]
  have rd38 := evm_run_rfl rd37 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨4311⟩, jump jump_4311]
  have rd39 := evm_run_rfl rd38 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd40 := RD.runtimeMload rd39 (by old_decode) (by simp; omega)
  have rd41 := evm_run_rfl rd40 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd42 := evm_run_rfl rd41 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4328]
  have rd43 := evm_run_rfl rd42 with [jumpdest, add, and, swap8, dup7]
  have rd44 := RD.runtimeMstore rd43 (by old_decode) (by simp; omega)
  have rd45 := evm_run_rfl rd44 with [push1 ⟨128⟩, dup7, add]
  have rd46 := RD.runtimeMstore rd45 (by old_decode) (by simp; omega)
  have rd47 := evm_run_rfl rd46 with [push2 ⟨268⟩, jump jump_268]
  have rd48 := evm_run_rfl rd47 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4343]
  have rd49 := evm_run_rfl rd48 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd50 := RD.runtimeMstore rd49 (by old_decode) (by simp; omega)
  have rd51 := evm_run_rfl rd50 with [push1 ⟨64⟩, dup3, add]
  have rd52 := RD.runtimeMstore rd51 (by old_decode) (by simp; omega)
  have rd53 := evm_run_rfl rd52 with [add]
  have rd54 := RD.runtimeMstore rd53 (by old_decode) (by simp; omega)
  have rd55 := evm_run_rfl rd54 with [jump jump_8967]
  exact ⟨_, _, by
    simpa [oldRightHelperStack, oldRightRoundCursor, runtimeRoundPreludeCursor,
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


end Ripemd160Old
