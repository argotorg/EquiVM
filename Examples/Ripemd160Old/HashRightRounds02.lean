import Examples.Ripemd160Old.HashRightRound0
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000
namespace Ripemd160Old
open Ripemd160

theorem runtime_rightRoundHelper_20 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I 20 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) 1 4).mem
      (oldRightRoundCursor c (hashScratchPtr I) 1 4).aw
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
  have rd11 := evm_run_rfl rd10 with [swap14, dup15, swap6, dup4, push1 ⟨16⟩, dup4, div, swap6, push0, swap4, dup12, dup14, push0, swap8, dup11, dup1, push0, eq, push2 ⟨8238⟩, jumpiNT (by native_decide)]
  have rd12 := evm_run_rfl rd11 with [dup1, push1 ⟨1⟩, eq, push2 ⟨8207⟩, jumpiT (by native_decide) jump_8207]
  have rd13 := evm_run_rfl rd12 with [jumpdest, pop, swap4, swap7, pop, pop, dup1, swap2, swap7, pop, not, dup14, and, swap2, and, or, swap3, push4 ⟨1548603684⟩, swap5, dup16, dup14, dup14, swap2, push2 ⟨4225⟩, jump jump_4225]
  have rd14 := evm_run_rfl rd13 with [jumpdest, pop, pop, pop, push0, swap1, dup9, dup1, push0, eq, push2 ⟨7821⟩, jumpiNT (by native_decide)]
  have rd15 := evm_run_rfl rd14 with [dup1, push1 ⟨1⟩, eq, push2 ⟨7512⟩, jumpiT (by native_decide) jump_7512]
  have rd16 := evm_run_rfl rd15 with [jumpdest, pop, push1 ⟨16⟩, dup2, mod, dup1, push0, eq, push2 ⟨7810⟩, jumpiNT (by native_decide)]
  have rd17 := evm_run_rfl rd16 with [dup1, push1 ⟨1⟩, eq, push2 ⟨7799⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [dup1, push1 ⟨2⟩, eq, push2 ⟨7788⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [dup1, push1 ⟨3⟩, eq, push2 ⟨7777⟩, jumpiNT (by native_decide)]
  have rd20 := evm_run_rfl rd19 with [dup1, push1 ⟨4⟩, eq, push2 ⟨7767⟩, jumpiT (by native_decide) jump_7767]
  have rd21 := evm_run_rfl rd20 with [jumpdest, pop, swap1, pop, push0, swap1, push2 ⟨7643⟩, jump jump_7643]
  have rd22 := evm_run_rfl rd21 with [jumpdest, push2 ⟨4270⟩, jump jump_4270]
  have rd23 := evm_run_rfl rd22 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨6140⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup1, push1 ⟨1⟩, eq, push2 ⟨5694⟩, jumpiT (by native_decide) jump_5694]
  have rd25 := evm_run_rfl rd24 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨6121⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup1, push1 ⟨1⟩, eq, push2 ⟨6102⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨2⟩, eq, push2 ⟨6083⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨3⟩, eq, push2 ⟨6064⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [dup1, push1 ⟨4⟩, eq, push2 ⟨6045⟩, jumpiT (by native_decide) jump_6045]
  have rd30 := evm_run_rfl rd29 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨12⟩, swap8, swap2, swap3, pop, pop, push2 ⟨5828⟩, jump jump_5828]
  have rd31 := evm_run_rfl rd30 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨4311⟩, jump jump_4311]
  have rd32 := evm_run_rfl rd31 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd33 := RD.runtimeMload rd32 (by old_decode) (by simp; omega)
  have rd34 := evm_run_rfl rd33 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd35 := evm_run_rfl rd34 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4328]
  have rd36 := evm_run_rfl rd35 with [jumpdest, add, and, swap8, dup7]
  have rd37 := RD.runtimeMstore rd36 (by old_decode) (by simp; omega)
  have rd38 := evm_run_rfl rd37 with [push1 ⟨128⟩, dup7, add]
  have rd39 := RD.runtimeMstore rd38 (by old_decode) (by simp; omega)
  have rd40 := evm_run_rfl rd39 with [push2 ⟨268⟩, jump jump_268]
  have rd41 := evm_run_rfl rd40 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4343]
  have rd42 := evm_run_rfl rd41 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd43 := RD.runtimeMstore rd42 (by old_decode) (by simp; omega)
  have rd44 := evm_run_rfl rd43 with [push1 ⟨64⟩, dup3, add]
  have rd45 := RD.runtimeMstore rd44 (by old_decode) (by simp; omega)
  have rd46 := evm_run_rfl rd45 with [add]
  have rd47 := RD.runtimeMstore rd46 (by old_decode) (by simp; omega)
  have rd48 := evm_run_rfl rd47 with [jump jump_8967]
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
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd48⟩

theorem runtime_rightRoundHelper_21 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I 21 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) 1 5).mem
      (oldRightRoundCursor c (hashScratchPtr I) 1 5).aw
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
  have rd11 := evm_run_rfl rd10 with [swap14, dup15, swap6, dup4, push1 ⟨16⟩, dup4, div, swap6, push0, swap4, dup12, dup14, push0, swap8, dup11, dup1, push0, eq, push2 ⟨8238⟩, jumpiNT (by native_decide)]
  have rd12 := evm_run_rfl rd11 with [dup1, push1 ⟨1⟩, eq, push2 ⟨8207⟩, jumpiT (by native_decide) jump_8207]
  have rd13 := evm_run_rfl rd12 with [jumpdest, pop, swap4, swap7, pop, pop, dup1, swap2, swap7, pop, not, dup14, and, swap2, and, or, swap3, push4 ⟨1548603684⟩, swap5, dup16, dup14, dup14, swap2, push2 ⟨4225⟩, jump jump_4225]
  have rd14 := evm_run_rfl rd13 with [jumpdest, pop, pop, pop, push0, swap1, dup9, dup1, push0, eq, push2 ⟨7821⟩, jumpiNT (by native_decide)]
  have rd15 := evm_run_rfl rd14 with [dup1, push1 ⟨1⟩, eq, push2 ⟨7512⟩, jumpiT (by native_decide) jump_7512]
  have rd16 := evm_run_rfl rd15 with [jumpdest, pop, push1 ⟨16⟩, dup2, mod, dup1, push0, eq, push2 ⟨7810⟩, jumpiNT (by native_decide)]
  have rd17 := evm_run_rfl rd16 with [dup1, push1 ⟨1⟩, eq, push2 ⟨7799⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [dup1, push1 ⟨2⟩, eq, push2 ⟨7788⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [dup1, push1 ⟨3⟩, eq, push2 ⟨7777⟩, jumpiNT (by native_decide)]
  have rd20 := evm_run_rfl rd19 with [dup1, push1 ⟨4⟩, eq, push2 ⟨7767⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [dup1, push1 ⟨5⟩, eq, push2 ⟨7756⟩, jumpiT (by native_decide) jump_7756]
  have rd22 := evm_run_rfl rd21 with [jumpdest, pop, swap1, pop, push1 ⟨13⟩, swap1, push2 ⟨7643⟩, jump jump_7643]
  have rd23 := evm_run_rfl rd22 with [jumpdest, push2 ⟨4270⟩, jump jump_4270]
  have rd24 := evm_run_rfl rd23 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨6140⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨1⟩, eq, push2 ⟨5694⟩, jumpiT (by native_decide) jump_5694]
  have rd26 := evm_run_rfl rd25 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨6121⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨1⟩, eq, push2 ⟨6102⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨2⟩, eq, push2 ⟨6083⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [dup1, push1 ⟨3⟩, eq, push2 ⟨6064⟩, jumpiNT (by native_decide)]
  have rd30 := evm_run_rfl rd29 with [dup1, push1 ⟨4⟩, eq, push2 ⟨6045⟩, jumpiNT (by native_decide)]
  have rd31 := evm_run_rfl rd30 with [dup1, push1 ⟨5⟩, eq, push2 ⟨6026⟩, jumpiT (by native_decide) jump_6026]
  have rd32 := evm_run_rfl rd31 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨8⟩, swap8, swap2, swap3, pop, pop, push2 ⟨5828⟩, jump jump_5828]
  have rd33 := evm_run_rfl rd32 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨4311⟩, jump jump_4311]
  have rd34 := evm_run_rfl rd33 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd35 := RD.runtimeMload rd34 (by old_decode) (by simp; omega)
  have rd36 := evm_run_rfl rd35 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd37 := evm_run_rfl rd36 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4328]
  have rd38 := evm_run_rfl rd37 with [jumpdest, add, and, swap8, dup7]
  have rd39 := RD.runtimeMstore rd38 (by old_decode) (by simp; omega)
  have rd40 := evm_run_rfl rd39 with [push1 ⟨128⟩, dup7, add]
  have rd41 := RD.runtimeMstore rd40 (by old_decode) (by simp; omega)
  have rd42 := evm_run_rfl rd41 with [push2 ⟨268⟩, jump jump_268]
  have rd43 := evm_run_rfl rd42 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4343]
  have rd44 := evm_run_rfl rd43 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd45 := RD.runtimeMstore rd44 (by old_decode) (by simp; omega)
  have rd46 := evm_run_rfl rd45 with [push1 ⟨64⟩, dup3, add]
  have rd47 := RD.runtimeMstore rd46 (by old_decode) (by simp; omega)
  have rd48 := evm_run_rfl rd47 with [add]
  have rd49 := RD.runtimeMstore rd48 (by old_decode) (by simp; omega)
  have rd50 := evm_run_rfl rd49 with [jump jump_8967]
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
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd50⟩

theorem runtime_rightRoundHelper_22 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I 22 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) 1 6).mem
      (oldRightRoundCursor c (hashScratchPtr I) 1 6).aw
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
  have rd11 := evm_run_rfl rd10 with [swap14, dup15, swap6, dup4, push1 ⟨16⟩, dup4, div, swap6, push0, swap4, dup12, dup14, push0, swap8, dup11, dup1, push0, eq, push2 ⟨8238⟩, jumpiNT (by native_decide)]
  have rd12 := evm_run_rfl rd11 with [dup1, push1 ⟨1⟩, eq, push2 ⟨8207⟩, jumpiT (by native_decide) jump_8207]
  have rd13 := evm_run_rfl rd12 with [jumpdest, pop, swap4, swap7, pop, pop, dup1, swap2, swap7, pop, not, dup14, and, swap2, and, or, swap3, push4 ⟨1548603684⟩, swap5, dup16, dup14, dup14, swap2, push2 ⟨4225⟩, jump jump_4225]
  have rd14 := evm_run_rfl rd13 with [jumpdest, pop, pop, pop, push0, swap1, dup9, dup1, push0, eq, push2 ⟨7821⟩, jumpiNT (by native_decide)]
  have rd15 := evm_run_rfl rd14 with [dup1, push1 ⟨1⟩, eq, push2 ⟨7512⟩, jumpiT (by native_decide) jump_7512]
  have rd16 := evm_run_rfl rd15 with [jumpdest, pop, push1 ⟨16⟩, dup2, mod, dup1, push0, eq, push2 ⟨7810⟩, jumpiNT (by native_decide)]
  have rd17 := evm_run_rfl rd16 with [dup1, push1 ⟨1⟩, eq, push2 ⟨7799⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [dup1, push1 ⟨2⟩, eq, push2 ⟨7788⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [dup1, push1 ⟨3⟩, eq, push2 ⟨7777⟩, jumpiNT (by native_decide)]
  have rd20 := evm_run_rfl rd19 with [dup1, push1 ⟨4⟩, eq, push2 ⟨7767⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [dup1, push1 ⟨5⟩, eq, push2 ⟨7756⟩, jumpiNT (by native_decide)]
  have rd22 := evm_run_rfl rd21 with [dup1, push1 ⟨6⟩, eq, push2 ⟨7745⟩, jumpiT (by native_decide) jump_7745]
  have rd23 := evm_run_rfl rd22 with [jumpdest, pop, swap1, pop, push1 ⟨5⟩, swap1, push2 ⟨7643⟩, jump jump_7643]
  have rd24 := evm_run_rfl rd23 with [jumpdest, push2 ⟨4270⟩, jump jump_4270]
  have rd25 := evm_run_rfl rd24 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨6140⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup1, push1 ⟨1⟩, eq, push2 ⟨5694⟩, jumpiT (by native_decide) jump_5694]
  have rd27 := evm_run_rfl rd26 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨6121⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨1⟩, eq, push2 ⟨6102⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [dup1, push1 ⟨2⟩, eq, push2 ⟨6083⟩, jumpiNT (by native_decide)]
  have rd30 := evm_run_rfl rd29 with [dup1, push1 ⟨3⟩, eq, push2 ⟨6064⟩, jumpiNT (by native_decide)]
  have rd31 := evm_run_rfl rd30 with [dup1, push1 ⟨4⟩, eq, push2 ⟨6045⟩, jumpiNT (by native_decide)]
  have rd32 := evm_run_rfl rd31 with [dup1, push1 ⟨5⟩, eq, push2 ⟨6026⟩, jumpiNT (by native_decide)]
  have rd33 := evm_run_rfl rd32 with [dup1, push1 ⟨6⟩, eq, push2 ⟨6007⟩, jumpiT (by native_decide) jump_6007]
  have rd34 := evm_run_rfl rd33 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨9⟩, swap8, swap2, swap3, pop, pop, push2 ⟨5828⟩, jump jump_5828]
  have rd35 := evm_run_rfl rd34 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨4311⟩, jump jump_4311]
  have rd36 := evm_run_rfl rd35 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd37 := RD.runtimeMload rd36 (by old_decode) (by simp; omega)
  have rd38 := evm_run_rfl rd37 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd39 := evm_run_rfl rd38 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4328]
  have rd40 := evm_run_rfl rd39 with [jumpdest, add, and, swap8, dup7]
  have rd41 := RD.runtimeMstore rd40 (by old_decode) (by simp; omega)
  have rd42 := evm_run_rfl rd41 with [push1 ⟨128⟩, dup7, add]
  have rd43 := RD.runtimeMstore rd42 (by old_decode) (by simp; omega)
  have rd44 := evm_run_rfl rd43 with [push2 ⟨268⟩, jump jump_268]
  have rd45 := evm_run_rfl rd44 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4343]
  have rd46 := evm_run_rfl rd45 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd47 := RD.runtimeMstore rd46 (by old_decode) (by simp; omega)
  have rd48 := evm_run_rfl rd47 with [push1 ⟨64⟩, dup3, add]
  have rd49 := RD.runtimeMstore rd48 (by old_decode) (by simp; omega)
  have rd50 := evm_run_rfl rd49 with [add]
  have rd51 := RD.runtimeMstore rd50 (by old_decode) (by simp; omega)
  have rd52 := evm_run_rfl rd51 with [jump jump_8967]
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
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd52⟩

theorem runtime_rightRoundHelper_23 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I 23 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) 1 7).mem
      (oldRightRoundCursor c (hashScratchPtr I) 1 7).aw
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
  have rd11 := evm_run_rfl rd10 with [swap14, dup15, swap6, dup4, push1 ⟨16⟩, dup4, div, swap6, push0, swap4, dup12, dup14, push0, swap8, dup11, dup1, push0, eq, push2 ⟨8238⟩, jumpiNT (by native_decide)]
  have rd12 := evm_run_rfl rd11 with [dup1, push1 ⟨1⟩, eq, push2 ⟨8207⟩, jumpiT (by native_decide) jump_8207]
  have rd13 := evm_run_rfl rd12 with [jumpdest, pop, swap4, swap7, pop, pop, dup1, swap2, swap7, pop, not, dup14, and, swap2, and, or, swap3, push4 ⟨1548603684⟩, swap5, dup16, dup14, dup14, swap2, push2 ⟨4225⟩, jump jump_4225]
  have rd14 := evm_run_rfl rd13 with [jumpdest, pop, pop, pop, push0, swap1, dup9, dup1, push0, eq, push2 ⟨7821⟩, jumpiNT (by native_decide)]
  have rd15 := evm_run_rfl rd14 with [dup1, push1 ⟨1⟩, eq, push2 ⟨7512⟩, jumpiT (by native_decide) jump_7512]
  have rd16 := evm_run_rfl rd15 with [jumpdest, pop, push1 ⟨16⟩, dup2, mod, dup1, push0, eq, push2 ⟨7810⟩, jumpiNT (by native_decide)]
  have rd17 := evm_run_rfl rd16 with [dup1, push1 ⟨1⟩, eq, push2 ⟨7799⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [dup1, push1 ⟨2⟩, eq, push2 ⟨7788⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [dup1, push1 ⟨3⟩, eq, push2 ⟨7777⟩, jumpiNT (by native_decide)]
  have rd20 := evm_run_rfl rd19 with [dup1, push1 ⟨4⟩, eq, push2 ⟨7767⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [dup1, push1 ⟨5⟩, eq, push2 ⟨7756⟩, jumpiNT (by native_decide)]
  have rd22 := evm_run_rfl rd21 with [dup1, push1 ⟨6⟩, eq, push2 ⟨7745⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨7⟩, eq, push2 ⟨7735⟩, jumpiT (by native_decide) jump_7735]
  have rd24 := evm_run_rfl rd23 with [jumpdest, pop, swap1, pop, dup14, swap1, push2 ⟨7643⟩, jump jump_7643]
  have rd25 := evm_run_rfl rd24 with [jumpdest, push2 ⟨4270⟩, jump jump_4270]
  have rd26 := evm_run_rfl rd25 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨6140⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨1⟩, eq, push2 ⟨5694⟩, jumpiT (by native_decide) jump_5694]
  have rd28 := evm_run_rfl rd27 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨6121⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [dup1, push1 ⟨1⟩, eq, push2 ⟨6102⟩, jumpiNT (by native_decide)]
  have rd30 := evm_run_rfl rd29 with [dup1, push1 ⟨2⟩, eq, push2 ⟨6083⟩, jumpiNT (by native_decide)]
  have rd31 := evm_run_rfl rd30 with [dup1, push1 ⟨3⟩, eq, push2 ⟨6064⟩, jumpiNT (by native_decide)]
  have rd32 := evm_run_rfl rd31 with [dup1, push1 ⟨4⟩, eq, push2 ⟨6045⟩, jumpiNT (by native_decide)]
  have rd33 := evm_run_rfl rd32 with [dup1, push1 ⟨5⟩, eq, push2 ⟨6026⟩, jumpiNT (by native_decide)]
  have rd34 := evm_run_rfl rd33 with [dup1, push1 ⟨6⟩, eq, push2 ⟨6007⟩, jumpiNT (by native_decide)]
  have rd35 := evm_run_rfl rd34 with [dup1, push1 ⟨7⟩, eq, push2 ⟨5988⟩, jumpiT (by native_decide) jump_5988]
  have rd36 := evm_run_rfl rd35 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨11⟩, swap8, swap2, swap3, pop, pop, push2 ⟨5828⟩, jump jump_5828]
  have rd37 := evm_run_rfl rd36 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨4311⟩, jump jump_4311]
  have rd38 := evm_run_rfl rd37 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd39 := RD.runtimeMload rd38 (by old_decode) (by simp; omega)
  have rd40 := evm_run_rfl rd39 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd41 := evm_run_rfl rd40 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4328]
  have rd42 := evm_run_rfl rd41 with [jumpdest, add, and, swap8, dup7]
  have rd43 := RD.runtimeMstore rd42 (by old_decode) (by simp; omega)
  have rd44 := evm_run_rfl rd43 with [push1 ⟨128⟩, dup7, add]
  have rd45 := RD.runtimeMstore rd44 (by old_decode) (by simp; omega)
  have rd46 := evm_run_rfl rd45 with [push2 ⟨268⟩, jump jump_268]
  have rd47 := evm_run_rfl rd46 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4343]
  have rd48 := evm_run_rfl rd47 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd49 := RD.runtimeMstore rd48 (by old_decode) (by simp; omega)
  have rd50 := evm_run_rfl rd49 with [push1 ⟨64⟩, dup3, add]
  have rd51 := RD.runtimeMstore rd50 (by old_decode) (by simp; omega)
  have rd52 := evm_run_rfl rd51 with [add]
  have rd53 := RD.runtimeMstore rd52 (by old_decode) (by simp; omega)
  have rd54 := evm_run_rfl rd53 with [jump jump_8967]
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
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd54⟩

theorem runtime_rightRoundHelper_24 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I 24 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) 1 8).mem
      (oldRightRoundCursor c (hashScratchPtr I) 1 8).aw
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
  have rd11 := evm_run_rfl rd10 with [swap14, dup15, swap6, dup4, push1 ⟨16⟩, dup4, div, swap6, push0, swap4, dup12, dup14, push0, swap8, dup11, dup1, push0, eq, push2 ⟨8238⟩, jumpiNT (by native_decide)]
  have rd12 := evm_run_rfl rd11 with [dup1, push1 ⟨1⟩, eq, push2 ⟨8207⟩, jumpiT (by native_decide) jump_8207]
  have rd13 := evm_run_rfl rd12 with [jumpdest, pop, swap4, swap7, pop, pop, dup1, swap2, swap7, pop, not, dup14, and, swap2, and, or, swap3, push4 ⟨1548603684⟩, swap5, dup16, dup14, dup14, swap2, push2 ⟨4225⟩, jump jump_4225]
  have rd14 := evm_run_rfl rd13 with [jumpdest, pop, pop, pop, push0, swap1, dup9, dup1, push0, eq, push2 ⟨7821⟩, jumpiNT (by native_decide)]
  have rd15 := evm_run_rfl rd14 with [dup1, push1 ⟨1⟩, eq, push2 ⟨7512⟩, jumpiT (by native_decide) jump_7512]
  have rd16 := evm_run_rfl rd15 with [jumpdest, pop, push1 ⟨16⟩, dup2, mod, dup1, push0, eq, push2 ⟨7810⟩, jumpiNT (by native_decide)]
  have rd17 := evm_run_rfl rd16 with [dup1, push1 ⟨1⟩, eq, push2 ⟨7799⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [dup1, push1 ⟨2⟩, eq, push2 ⟨7788⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [dup1, push1 ⟨3⟩, eq, push2 ⟨7777⟩, jumpiNT (by native_decide)]
  have rd20 := evm_run_rfl rd19 with [dup1, push1 ⟨4⟩, eq, push2 ⟨7767⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [dup1, push1 ⟨5⟩, eq, push2 ⟨7756⟩, jumpiNT (by native_decide)]
  have rd22 := evm_run_rfl rd21 with [dup1, push1 ⟨6⟩, eq, push2 ⟨7745⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨7⟩, eq, push2 ⟨7735⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup1, push1 ⟨8⟩, eq, push2 ⟨7724⟩, jumpiT (by native_decide) jump_7724]
  have rd25 := evm_run_rfl rd24 with [jumpdest, pop, swap1, pop, push1 ⟨14⟩, swap1, push2 ⟨7643⟩, jump jump_7643]
  have rd26 := evm_run_rfl rd25 with [jumpdest, push2 ⟨4270⟩, jump jump_4270]
  have rd27 := evm_run_rfl rd26 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨6140⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨1⟩, eq, push2 ⟨5694⟩, jumpiT (by native_decide) jump_5694]
  have rd29 := evm_run_rfl rd28 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨6121⟩, jumpiNT (by native_decide)]
  have rd30 := evm_run_rfl rd29 with [dup1, push1 ⟨1⟩, eq, push2 ⟨6102⟩, jumpiNT (by native_decide)]
  have rd31 := evm_run_rfl rd30 with [dup1, push1 ⟨2⟩, eq, push2 ⟨6083⟩, jumpiNT (by native_decide)]
  have rd32 := evm_run_rfl rd31 with [dup1, push1 ⟨3⟩, eq, push2 ⟨6064⟩, jumpiNT (by native_decide)]
  have rd33 := evm_run_rfl rd32 with [dup1, push1 ⟨4⟩, eq, push2 ⟨6045⟩, jumpiNT (by native_decide)]
  have rd34 := evm_run_rfl rd33 with [dup1, push1 ⟨5⟩, eq, push2 ⟨6026⟩, jumpiNT (by native_decide)]
  have rd35 := evm_run_rfl rd34 with [dup1, push1 ⟨6⟩, eq, push2 ⟨6007⟩, jumpiNT (by native_decide)]
  have rd36 := evm_run_rfl rd35 with [dup1, push1 ⟨7⟩, eq, push2 ⟨5988⟩, jumpiNT (by native_decide)]
  have rd37 := evm_run_rfl rd36 with [dup1, push1 ⟨8⟩, eq, push2 ⟨5969⟩, jumpiT (by native_decide) jump_5969]
  have rd38 := evm_run_rfl rd37 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨7⟩, swap8, swap2, swap3, pop, pop, push2 ⟨5828⟩, jump jump_5828]
  have rd39 := evm_run_rfl rd38 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨4311⟩, jump jump_4311]
  have rd40 := evm_run_rfl rd39 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd41 := RD.runtimeMload rd40 (by old_decode) (by simp; omega)
  have rd42 := evm_run_rfl rd41 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd43 := evm_run_rfl rd42 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4328]
  have rd44 := evm_run_rfl rd43 with [jumpdest, add, and, swap8, dup7]
  have rd45 := RD.runtimeMstore rd44 (by old_decode) (by simp; omega)
  have rd46 := evm_run_rfl rd45 with [push1 ⟨128⟩, dup7, add]
  have rd47 := RD.runtimeMstore rd46 (by old_decode) (by simp; omega)
  have rd48 := evm_run_rfl rd47 with [push2 ⟨268⟩, jump jump_268]
  have rd49 := evm_run_rfl rd48 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4343]
  have rd50 := evm_run_rfl rd49 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd51 := RD.runtimeMstore rd50 (by old_decode) (by simp; omega)
  have rd52 := evm_run_rfl rd51 with [push1 ⟨64⟩, dup3, add]
  have rd53 := RD.runtimeMstore rd52 (by old_decode) (by simp; omega)
  have rd54 := evm_run_rfl rd53 with [add]
  have rd55 := RD.runtimeMstore rd54 (by old_decode) (by simp; omega)
  have rd56 := evm_run_rfl rd55 with [jump jump_8967]
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
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd56⟩

theorem runtime_rightRoundHelper_25 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I 25 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) 1 9).mem
      (oldRightRoundCursor c (hashScratchPtr I) 1 9).aw
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
  have rd11 := evm_run_rfl rd10 with [swap14, dup15, swap6, dup4, push1 ⟨16⟩, dup4, div, swap6, push0, swap4, dup12, dup14, push0, swap8, dup11, dup1, push0, eq, push2 ⟨8238⟩, jumpiNT (by native_decide)]
  have rd12 := evm_run_rfl rd11 with [dup1, push1 ⟨1⟩, eq, push2 ⟨8207⟩, jumpiT (by native_decide) jump_8207]
  have rd13 := evm_run_rfl rd12 with [jumpdest, pop, swap4, swap7, pop, pop, dup1, swap2, swap7, pop, not, dup14, and, swap2, and, or, swap3, push4 ⟨1548603684⟩, swap5, dup16, dup14, dup14, swap2, push2 ⟨4225⟩, jump jump_4225]
  have rd14 := evm_run_rfl rd13 with [jumpdest, pop, pop, pop, push0, swap1, dup9, dup1, push0, eq, push2 ⟨7821⟩, jumpiNT (by native_decide)]
  have rd15 := evm_run_rfl rd14 with [dup1, push1 ⟨1⟩, eq, push2 ⟨7512⟩, jumpiT (by native_decide) jump_7512]
  have rd16 := evm_run_rfl rd15 with [jumpdest, pop, push1 ⟨16⟩, dup2, mod, dup1, push0, eq, push2 ⟨7810⟩, jumpiNT (by native_decide)]
  have rd17 := evm_run_rfl rd16 with [dup1, push1 ⟨1⟩, eq, push2 ⟨7799⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [dup1, push1 ⟨2⟩, eq, push2 ⟨7788⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [dup1, push1 ⟨3⟩, eq, push2 ⟨7777⟩, jumpiNT (by native_decide)]
  have rd20 := evm_run_rfl rd19 with [dup1, push1 ⟨4⟩, eq, push2 ⟨7767⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [dup1, push1 ⟨5⟩, eq, push2 ⟨7756⟩, jumpiNT (by native_decide)]
  have rd22 := evm_run_rfl rd21 with [dup1, push1 ⟨6⟩, eq, push2 ⟨7745⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨7⟩, eq, push2 ⟨7735⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup1, push1 ⟨8⟩, eq, push2 ⟨7724⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨9⟩, eq, push2 ⟨7713⟩, jumpiT (by native_decide) jump_7713]
  have rd26 := evm_run_rfl rd25 with [jumpdest, pop, swap1, pop, push1 ⟨15⟩, swap1, push2 ⟨7643⟩, jump jump_7643]
  have rd27 := evm_run_rfl rd26 with [jumpdest, push2 ⟨4270⟩, jump jump_4270]
  have rd28 := evm_run_rfl rd27 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨6140⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [dup1, push1 ⟨1⟩, eq, push2 ⟨5694⟩, jumpiT (by native_decide) jump_5694]
  have rd30 := evm_run_rfl rd29 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨6121⟩, jumpiNT (by native_decide)]
  have rd31 := evm_run_rfl rd30 with [dup1, push1 ⟨1⟩, eq, push2 ⟨6102⟩, jumpiNT (by native_decide)]
  have rd32 := evm_run_rfl rd31 with [dup1, push1 ⟨2⟩, eq, push2 ⟨6083⟩, jumpiNT (by native_decide)]
  have rd33 := evm_run_rfl rd32 with [dup1, push1 ⟨3⟩, eq, push2 ⟨6064⟩, jumpiNT (by native_decide)]
  have rd34 := evm_run_rfl rd33 with [dup1, push1 ⟨4⟩, eq, push2 ⟨6045⟩, jumpiNT (by native_decide)]
  have rd35 := evm_run_rfl rd34 with [dup1, push1 ⟨5⟩, eq, push2 ⟨6026⟩, jumpiNT (by native_decide)]
  have rd36 := evm_run_rfl rd35 with [dup1, push1 ⟨6⟩, eq, push2 ⟨6007⟩, jumpiNT (by native_decide)]
  have rd37 := evm_run_rfl rd36 with [dup1, push1 ⟨7⟩, eq, push2 ⟨5988⟩, jumpiNT (by native_decide)]
  have rd38 := evm_run_rfl rd37 with [dup1, push1 ⟨8⟩, eq, push2 ⟨5969⟩, jumpiNT (by native_decide)]
  have rd39 := evm_run_rfl rd38 with [dup1, push1 ⟨9⟩, eq, push2 ⟨5950⟩, jumpiT (by native_decide) jump_5950]
  have rd40 := evm_run_rfl rd39 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨7⟩, swap8, swap2, swap3, pop, pop, push2 ⟨5828⟩, jump jump_5828]
  have rd41 := evm_run_rfl rd40 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨4311⟩, jump jump_4311]
  have rd42 := evm_run_rfl rd41 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd43 := RD.runtimeMload rd42 (by old_decode) (by simp; omega)
  have rd44 := evm_run_rfl rd43 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd45 := evm_run_rfl rd44 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4328]
  have rd46 := evm_run_rfl rd45 with [jumpdest, add, and, swap8, dup7]
  have rd47 := RD.runtimeMstore rd46 (by old_decode) (by simp; omega)
  have rd48 := evm_run_rfl rd47 with [push1 ⟨128⟩, dup7, add]
  have rd49 := RD.runtimeMstore rd48 (by old_decode) (by simp; omega)
  have rd50 := evm_run_rfl rd49 with [push2 ⟨268⟩, jump jump_268]
  have rd51 := evm_run_rfl rd50 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4343]
  have rd52 := evm_run_rfl rd51 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd53 := RD.runtimeMstore rd52 (by old_decode) (by simp; omega)
  have rd54 := evm_run_rfl rd53 with [push1 ⟨64⟩, dup3, add]
  have rd55 := RD.runtimeMstore rd54 (by old_decode) (by simp; omega)
  have rd56 := evm_run_rfl rd55 with [add]
  have rd57 := RD.runtimeMstore rd56 (by old_decode) (by simp; omega)
  have rd58 := evm_run_rfl rd57 with [jump jump_8967]
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
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd58⟩

theorem runtime_rightRoundHelper_26 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I 26 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) 1 10).mem
      (oldRightRoundCursor c (hashScratchPtr I) 1 10).aw
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
  have rd11 := evm_run_rfl rd10 with [swap14, dup15, swap6, dup4, push1 ⟨16⟩, dup4, div, swap6, push0, swap4, dup12, dup14, push0, swap8, dup11, dup1, push0, eq, push2 ⟨8238⟩, jumpiNT (by native_decide)]
  have rd12 := evm_run_rfl rd11 with [dup1, push1 ⟨1⟩, eq, push2 ⟨8207⟩, jumpiT (by native_decide) jump_8207]
  have rd13 := evm_run_rfl rd12 with [jumpdest, pop, swap4, swap7, pop, pop, dup1, swap2, swap7, pop, not, dup14, and, swap2, and, or, swap3, push4 ⟨1548603684⟩, swap5, dup16, dup14, dup14, swap2, push2 ⟨4225⟩, jump jump_4225]
  have rd14 := evm_run_rfl rd13 with [jumpdest, pop, pop, pop, push0, swap1, dup9, dup1, push0, eq, push2 ⟨7821⟩, jumpiNT (by native_decide)]
  have rd15 := evm_run_rfl rd14 with [dup1, push1 ⟨1⟩, eq, push2 ⟨7512⟩, jumpiT (by native_decide) jump_7512]
  have rd16 := evm_run_rfl rd15 with [jumpdest, pop, push1 ⟨16⟩, dup2, mod, dup1, push0, eq, push2 ⟨7810⟩, jumpiNT (by native_decide)]
  have rd17 := evm_run_rfl rd16 with [dup1, push1 ⟨1⟩, eq, push2 ⟨7799⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [dup1, push1 ⟨2⟩, eq, push2 ⟨7788⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [dup1, push1 ⟨3⟩, eq, push2 ⟨7777⟩, jumpiNT (by native_decide)]
  have rd20 := evm_run_rfl rd19 with [dup1, push1 ⟨4⟩, eq, push2 ⟨7767⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [dup1, push1 ⟨5⟩, eq, push2 ⟨7756⟩, jumpiNT (by native_decide)]
  have rd22 := evm_run_rfl rd21 with [dup1, push1 ⟨6⟩, eq, push2 ⟨7745⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨7⟩, eq, push2 ⟨7735⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup1, push1 ⟨8⟩, eq, push2 ⟨7724⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨9⟩, eq, push2 ⟨7713⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup16, dup2, eq, push2 ⟨7702⟩, jumpiT (by native_decide) jump_7702]
  have rd27 := evm_run_rfl rd26 with [jumpdest, pop, swap1, pop, push1 ⟨8⟩, swap1, push2 ⟨7643⟩, jump jump_7643]
  have rd28 := evm_run_rfl rd27 with [jumpdest, push2 ⟨4270⟩, jump jump_4270]
  have rd29 := evm_run_rfl rd28 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨6140⟩, jumpiNT (by native_decide)]
  have rd30 := evm_run_rfl rd29 with [dup1, push1 ⟨1⟩, eq, push2 ⟨5694⟩, jumpiT (by native_decide) jump_5694]
  have rd31 := evm_run_rfl rd30 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨6121⟩, jumpiNT (by native_decide)]
  have rd32 := evm_run_rfl rd31 with [dup1, push1 ⟨1⟩, eq, push2 ⟨6102⟩, jumpiNT (by native_decide)]
  have rd33 := evm_run_rfl rd32 with [dup1, push1 ⟨2⟩, eq, push2 ⟨6083⟩, jumpiNT (by native_decide)]
  have rd34 := evm_run_rfl rd33 with [dup1, push1 ⟨3⟩, eq, push2 ⟨6064⟩, jumpiNT (by native_decide)]
  have rd35 := evm_run_rfl rd34 with [dup1, push1 ⟨4⟩, eq, push2 ⟨6045⟩, jumpiNT (by native_decide)]
  have rd36 := evm_run_rfl rd35 with [dup1, push1 ⟨5⟩, eq, push2 ⟨6026⟩, jumpiNT (by native_decide)]
  have rd37 := evm_run_rfl rd36 with [dup1, push1 ⟨6⟩, eq, push2 ⟨6007⟩, jumpiNT (by native_decide)]
  have rd38 := evm_run_rfl rd37 with [dup1, push1 ⟨7⟩, eq, push2 ⟨5988⟩, jumpiNT (by native_decide)]
  have rd39 := evm_run_rfl rd38 with [dup1, push1 ⟨8⟩, eq, push2 ⟨5969⟩, jumpiNT (by native_decide)]
  have rd40 := evm_run_rfl rd39 with [dup1, push1 ⟨9⟩, eq, push2 ⟨5950⟩, jumpiNT (by native_decide)]
  have rd41 := evm_run_rfl rd40 with [dup1, dup15, eq, push2 ⟨5931⟩, jumpiT (by native_decide) jump_5931]
  have rd42 := evm_run_rfl rd41 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨12⟩, swap8, swap2, swap3, pop, pop, push2 ⟨5828⟩, jump jump_5828]
  have rd43 := evm_run_rfl rd42 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨4311⟩, jump jump_4311]
  have rd44 := evm_run_rfl rd43 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd45 := RD.runtimeMload rd44 (by old_decode) (by simp; omega)
  have rd46 := evm_run_rfl rd45 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd47 := evm_run_rfl rd46 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4328]
  have rd48 := evm_run_rfl rd47 with [jumpdest, add, and, swap8, dup7]
  have rd49 := RD.runtimeMstore rd48 (by old_decode) (by simp; omega)
  have rd50 := evm_run_rfl rd49 with [push1 ⟨128⟩, dup7, add]
  have rd51 := RD.runtimeMstore rd50 (by old_decode) (by simp; omega)
  have rd52 := evm_run_rfl rd51 with [push2 ⟨268⟩, jump jump_268]
  have rd53 := evm_run_rfl rd52 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4343]
  have rd54 := evm_run_rfl rd53 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd55 := RD.runtimeMstore rd54 (by old_decode) (by simp; omega)
  have rd56 := evm_run_rfl rd55 with [push1 ⟨64⟩, dup3, add]
  have rd57 := RD.runtimeMstore rd56 (by old_decode) (by simp; omega)
  have rd58 := evm_run_rfl rd57 with [add]
  have rd59 := RD.runtimeMstore rd58 (by old_decode) (by simp; omega)
  have rd60 := evm_run_rfl rd59 with [jump jump_8967]
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
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd60⟩

theorem runtime_rightRoundHelper_27 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I 27 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) 1 11).mem
      (oldRightRoundCursor c (hashScratchPtr I) 1 11).aw
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
  have rd11 := evm_run_rfl rd10 with [swap14, dup15, swap6, dup4, push1 ⟨16⟩, dup4, div, swap6, push0, swap4, dup12, dup14, push0, swap8, dup11, dup1, push0, eq, push2 ⟨8238⟩, jumpiNT (by native_decide)]
  have rd12 := evm_run_rfl rd11 with [dup1, push1 ⟨1⟩, eq, push2 ⟨8207⟩, jumpiT (by native_decide) jump_8207]
  have rd13 := evm_run_rfl rd12 with [jumpdest, pop, swap4, swap7, pop, pop, dup1, swap2, swap7, pop, not, dup14, and, swap2, and, or, swap3, push4 ⟨1548603684⟩, swap5, dup16, dup14, dup14, swap2, push2 ⟨4225⟩, jump jump_4225]
  have rd14 := evm_run_rfl rd13 with [jumpdest, pop, pop, pop, push0, swap1, dup9, dup1, push0, eq, push2 ⟨7821⟩, jumpiNT (by native_decide)]
  have rd15 := evm_run_rfl rd14 with [dup1, push1 ⟨1⟩, eq, push2 ⟨7512⟩, jumpiT (by native_decide) jump_7512]
  have rd16 := evm_run_rfl rd15 with [jumpdest, pop, push1 ⟨16⟩, dup2, mod, dup1, push0, eq, push2 ⟨7810⟩, jumpiNT (by native_decide)]
  have rd17 := evm_run_rfl rd16 with [dup1, push1 ⟨1⟩, eq, push2 ⟨7799⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [dup1, push1 ⟨2⟩, eq, push2 ⟨7788⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [dup1, push1 ⟨3⟩, eq, push2 ⟨7777⟩, jumpiNT (by native_decide)]
  have rd20 := evm_run_rfl rd19 with [dup1, push1 ⟨4⟩, eq, push2 ⟨7767⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [dup1, push1 ⟨5⟩, eq, push2 ⟨7756⟩, jumpiNT (by native_decide)]
  have rd22 := evm_run_rfl rd21 with [dup1, push1 ⟨6⟩, eq, push2 ⟨7745⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨7⟩, eq, push2 ⟨7735⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup1, push1 ⟨8⟩, eq, push2 ⟨7724⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨9⟩, eq, push2 ⟨7713⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup16, dup2, eq, push2 ⟨7702⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨11⟩, eq, push2 ⟨7691⟩, jumpiT (by native_decide) jump_7691]
  have rd28 := evm_run_rfl rd27 with [jumpdest, pop, swap1, pop, push1 ⟨12⟩, swap1, push2 ⟨7643⟩, jump jump_7643]
  have rd29 := evm_run_rfl rd28 with [jumpdest, push2 ⟨4270⟩, jump jump_4270]
  have rd30 := evm_run_rfl rd29 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨6140⟩, jumpiNT (by native_decide)]
  have rd31 := evm_run_rfl rd30 with [dup1, push1 ⟨1⟩, eq, push2 ⟨5694⟩, jumpiT (by native_decide) jump_5694]
  have rd32 := evm_run_rfl rd31 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨6121⟩, jumpiNT (by native_decide)]
  have rd33 := evm_run_rfl rd32 with [dup1, push1 ⟨1⟩, eq, push2 ⟨6102⟩, jumpiNT (by native_decide)]
  have rd34 := evm_run_rfl rd33 with [dup1, push1 ⟨2⟩, eq, push2 ⟨6083⟩, jumpiNT (by native_decide)]
  have rd35 := evm_run_rfl rd34 with [dup1, push1 ⟨3⟩, eq, push2 ⟨6064⟩, jumpiNT (by native_decide)]
  have rd36 := evm_run_rfl rd35 with [dup1, push1 ⟨4⟩, eq, push2 ⟨6045⟩, jumpiNT (by native_decide)]
  have rd37 := evm_run_rfl rd36 with [dup1, push1 ⟨5⟩, eq, push2 ⟨6026⟩, jumpiNT (by native_decide)]
  have rd38 := evm_run_rfl rd37 with [dup1, push1 ⟨6⟩, eq, push2 ⟨6007⟩, jumpiNT (by native_decide)]
  have rd39 := evm_run_rfl rd38 with [dup1, push1 ⟨7⟩, eq, push2 ⟨5988⟩, jumpiNT (by native_decide)]
  have rd40 := evm_run_rfl rd39 with [dup1, push1 ⟨8⟩, eq, push2 ⟨5969⟩, jumpiNT (by native_decide)]
  have rd41 := evm_run_rfl rd40 with [dup1, push1 ⟨9⟩, eq, push2 ⟨5950⟩, jumpiNT (by native_decide)]
  have rd42 := evm_run_rfl rd41 with [dup1, dup15, eq, push2 ⟨5931⟩, jumpiNT (by native_decide)]
  have rd43 := evm_run_rfl rd42 with [dup1, push1 ⟨11⟩, eq, push2 ⟨5912⟩, jumpiT (by native_decide) jump_5912]
  have rd44 := evm_run_rfl rd43 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨7⟩, swap8, swap2, swap3, pop, pop, push2 ⟨5828⟩, jump jump_5828]
  have rd45 := evm_run_rfl rd44 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨4311⟩, jump jump_4311]
  have rd46 := evm_run_rfl rd45 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd47 := RD.runtimeMload rd46 (by old_decode) (by simp; omega)
  have rd48 := evm_run_rfl rd47 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd49 := evm_run_rfl rd48 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4328]
  have rd50 := evm_run_rfl rd49 with [jumpdest, add, and, swap8, dup7]
  have rd51 := RD.runtimeMstore rd50 (by old_decode) (by simp; omega)
  have rd52 := evm_run_rfl rd51 with [push1 ⟨128⟩, dup7, add]
  have rd53 := RD.runtimeMstore rd52 (by old_decode) (by simp; omega)
  have rd54 := evm_run_rfl rd53 with [push2 ⟨268⟩, jump jump_268]
  have rd55 := evm_run_rfl rd54 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4343]
  have rd56 := evm_run_rfl rd55 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd57 := RD.runtimeMstore rd56 (by old_decode) (by simp; omega)
  have rd58 := evm_run_rfl rd57 with [push1 ⟨64⟩, dup3, add]
  have rd59 := RD.runtimeMstore rd58 (by old_decode) (by simp; omega)
  have rd60 := evm_run_rfl rd59 with [add]
  have rd61 := RD.runtimeMstore rd60 (by old_decode) (by simp; omega)
  have rd62 := evm_run_rfl rd61 with [jump jump_8967]
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
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd62⟩

theorem runtime_rightRoundHelper_28 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I 28 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) 1 12).mem
      (oldRightRoundCursor c (hashScratchPtr I) 1 12).aw
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
  have rd11 := evm_run_rfl rd10 with [swap14, dup15, swap6, dup4, push1 ⟨16⟩, dup4, div, swap6, push0, swap4, dup12, dup14, push0, swap8, dup11, dup1, push0, eq, push2 ⟨8238⟩, jumpiNT (by native_decide)]
  have rd12 := evm_run_rfl rd11 with [dup1, push1 ⟨1⟩, eq, push2 ⟨8207⟩, jumpiT (by native_decide) jump_8207]
  have rd13 := evm_run_rfl rd12 with [jumpdest, pop, swap4, swap7, pop, pop, dup1, swap2, swap7, pop, not, dup14, and, swap2, and, or, swap3, push4 ⟨1548603684⟩, swap5, dup16, dup14, dup14, swap2, push2 ⟨4225⟩, jump jump_4225]
  have rd14 := evm_run_rfl rd13 with [jumpdest, pop, pop, pop, push0, swap1, dup9, dup1, push0, eq, push2 ⟨7821⟩, jumpiNT (by native_decide)]
  have rd15 := evm_run_rfl rd14 with [dup1, push1 ⟨1⟩, eq, push2 ⟨7512⟩, jumpiT (by native_decide) jump_7512]
  have rd16 := evm_run_rfl rd15 with [jumpdest, pop, push1 ⟨16⟩, dup2, mod, dup1, push0, eq, push2 ⟨7810⟩, jumpiNT (by native_decide)]
  have rd17 := evm_run_rfl rd16 with [dup1, push1 ⟨1⟩, eq, push2 ⟨7799⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [dup1, push1 ⟨2⟩, eq, push2 ⟨7788⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [dup1, push1 ⟨3⟩, eq, push2 ⟨7777⟩, jumpiNT (by native_decide)]
  have rd20 := evm_run_rfl rd19 with [dup1, push1 ⟨4⟩, eq, push2 ⟨7767⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [dup1, push1 ⟨5⟩, eq, push2 ⟨7756⟩, jumpiNT (by native_decide)]
  have rd22 := evm_run_rfl rd21 with [dup1, push1 ⟨6⟩, eq, push2 ⟨7745⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨7⟩, eq, push2 ⟨7735⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup1, push1 ⟨8⟩, eq, push2 ⟨7724⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨9⟩, eq, push2 ⟨7713⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup16, dup2, eq, push2 ⟨7702⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨11⟩, eq, push2 ⟨7691⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨12⟩, eq, push2 ⟨7680⟩, jumpiT (by native_decide) jump_7680]
  have rd29 := evm_run_rfl rd28 with [jumpdest, pop, swap1, pop, push1 ⟨4⟩, swap1, push2 ⟨7643⟩, jump jump_7643]
  have rd30 := evm_run_rfl rd29 with [jumpdest, push2 ⟨4270⟩, jump jump_4270]
  have rd31 := evm_run_rfl rd30 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨6140⟩, jumpiNT (by native_decide)]
  have rd32 := evm_run_rfl rd31 with [dup1, push1 ⟨1⟩, eq, push2 ⟨5694⟩, jumpiT (by native_decide) jump_5694]
  have rd33 := evm_run_rfl rd32 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨6121⟩, jumpiNT (by native_decide)]
  have rd34 := evm_run_rfl rd33 with [dup1, push1 ⟨1⟩, eq, push2 ⟨6102⟩, jumpiNT (by native_decide)]
  have rd35 := evm_run_rfl rd34 with [dup1, push1 ⟨2⟩, eq, push2 ⟨6083⟩, jumpiNT (by native_decide)]
  have rd36 := evm_run_rfl rd35 with [dup1, push1 ⟨3⟩, eq, push2 ⟨6064⟩, jumpiNT (by native_decide)]
  have rd37 := evm_run_rfl rd36 with [dup1, push1 ⟨4⟩, eq, push2 ⟨6045⟩, jumpiNT (by native_decide)]
  have rd38 := evm_run_rfl rd37 with [dup1, push1 ⟨5⟩, eq, push2 ⟨6026⟩, jumpiNT (by native_decide)]
  have rd39 := evm_run_rfl rd38 with [dup1, push1 ⟨6⟩, eq, push2 ⟨6007⟩, jumpiNT (by native_decide)]
  have rd40 := evm_run_rfl rd39 with [dup1, push1 ⟨7⟩, eq, push2 ⟨5988⟩, jumpiNT (by native_decide)]
  have rd41 := evm_run_rfl rd40 with [dup1, push1 ⟨8⟩, eq, push2 ⟨5969⟩, jumpiNT (by native_decide)]
  have rd42 := evm_run_rfl rd41 with [dup1, push1 ⟨9⟩, eq, push2 ⟨5950⟩, jumpiNT (by native_decide)]
  have rd43 := evm_run_rfl rd42 with [dup1, dup15, eq, push2 ⟨5931⟩, jumpiNT (by native_decide)]
  have rd44 := evm_run_rfl rd43 with [dup1, push1 ⟨11⟩, eq, push2 ⟨5912⟩, jumpiNT (by native_decide)]
  have rd45 := evm_run_rfl rd44 with [dup1, push1 ⟨12⟩, eq, push2 ⟨5893⟩, jumpiT (by native_decide) jump_5893]
  have rd46 := evm_run_rfl rd45 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨6⟩, swap8, swap2, swap3, pop, pop, push2 ⟨5828⟩, jump jump_5828]
  have rd47 := evm_run_rfl rd46 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨4311⟩, jump jump_4311]
  have rd48 := evm_run_rfl rd47 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd49 := RD.runtimeMload rd48 (by old_decode) (by simp; omega)
  have rd50 := evm_run_rfl rd49 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd51 := evm_run_rfl rd50 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4328]
  have rd52 := evm_run_rfl rd51 with [jumpdest, add, and, swap8, dup7]
  have rd53 := RD.runtimeMstore rd52 (by old_decode) (by simp; omega)
  have rd54 := evm_run_rfl rd53 with [push1 ⟨128⟩, dup7, add]
  have rd55 := RD.runtimeMstore rd54 (by old_decode) (by simp; omega)
  have rd56 := evm_run_rfl rd55 with [push2 ⟨268⟩, jump jump_268]
  have rd57 := evm_run_rfl rd56 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4343]
  have rd58 := evm_run_rfl rd57 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd59 := RD.runtimeMstore rd58 (by old_decode) (by simp; omega)
  have rd60 := evm_run_rfl rd59 with [push1 ⟨64⟩, dup3, add]
  have rd61 := RD.runtimeMstore rd60 (by old_decode) (by simp; omega)
  have rd62 := evm_run_rfl rd61 with [add]
  have rd63 := RD.runtimeMstore rd62 (by old_decode) (by simp; omega)
  have rd64 := evm_run_rfl rd63 with [jump jump_8967]
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
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd64⟩

theorem runtime_rightRoundHelper_29 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I 29 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) 1 13).mem
      (oldRightRoundCursor c (hashScratchPtr I) 1 13).aw
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
  have rd11 := evm_run_rfl rd10 with [swap14, dup15, swap6, dup4, push1 ⟨16⟩, dup4, div, swap6, push0, swap4, dup12, dup14, push0, swap8, dup11, dup1, push0, eq, push2 ⟨8238⟩, jumpiNT (by native_decide)]
  have rd12 := evm_run_rfl rd11 with [dup1, push1 ⟨1⟩, eq, push2 ⟨8207⟩, jumpiT (by native_decide) jump_8207]
  have rd13 := evm_run_rfl rd12 with [jumpdest, pop, swap4, swap7, pop, pop, dup1, swap2, swap7, pop, not, dup14, and, swap2, and, or, swap3, push4 ⟨1548603684⟩, swap5, dup16, dup14, dup14, swap2, push2 ⟨4225⟩, jump jump_4225]
  have rd14 := evm_run_rfl rd13 with [jumpdest, pop, pop, pop, push0, swap1, dup9, dup1, push0, eq, push2 ⟨7821⟩, jumpiNT (by native_decide)]
  have rd15 := evm_run_rfl rd14 with [dup1, push1 ⟨1⟩, eq, push2 ⟨7512⟩, jumpiT (by native_decide) jump_7512]
  have rd16 := evm_run_rfl rd15 with [jumpdest, pop, push1 ⟨16⟩, dup2, mod, dup1, push0, eq, push2 ⟨7810⟩, jumpiNT (by native_decide)]
  have rd17 := evm_run_rfl rd16 with [dup1, push1 ⟨1⟩, eq, push2 ⟨7799⟩, jumpiNT (by native_decide)]
  have rd18 := evm_run_rfl rd17 with [dup1, push1 ⟨2⟩, eq, push2 ⟨7788⟩, jumpiNT (by native_decide)]
  have rd19 := evm_run_rfl rd18 with [dup1, push1 ⟨3⟩, eq, push2 ⟨7777⟩, jumpiNT (by native_decide)]
  have rd20 := evm_run_rfl rd19 with [dup1, push1 ⟨4⟩, eq, push2 ⟨7767⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [dup1, push1 ⟨5⟩, eq, push2 ⟨7756⟩, jumpiNT (by native_decide)]
  have rd22 := evm_run_rfl rd21 with [dup1, push1 ⟨6⟩, eq, push2 ⟨7745⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨7⟩, eq, push2 ⟨7735⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup1, push1 ⟨8⟩, eq, push2 ⟨7724⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨9⟩, eq, push2 ⟨7713⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup16, dup2, eq, push2 ⟨7702⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨11⟩, eq, push2 ⟨7691⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨12⟩, eq, push2 ⟨7680⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [dup1, push1 ⟨13⟩, eq, push2 ⟨7669⟩, jumpiT (by native_decide) jump_7669]
  have rd30 := evm_run_rfl rd29 with [jumpdest, pop, swap1, pop, push1 ⟨9⟩, swap1, push2 ⟨7643⟩, jump jump_7643]
  have rd31 := evm_run_rfl rd30 with [jumpdest, push2 ⟨4270⟩, jump jump_4270]
  have rd32 := evm_run_rfl rd31 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨6140⟩, jumpiNT (by native_decide)]
  have rd33 := evm_run_rfl rd32 with [dup1, push1 ⟨1⟩, eq, push2 ⟨5694⟩, jumpiT (by native_decide) jump_5694]
  have rd34 := evm_run_rfl rd33 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨6121⟩, jumpiNT (by native_decide)]
  have rd35 := evm_run_rfl rd34 with [dup1, push1 ⟨1⟩, eq, push2 ⟨6102⟩, jumpiNT (by native_decide)]
  have rd36 := evm_run_rfl rd35 with [dup1, push1 ⟨2⟩, eq, push2 ⟨6083⟩, jumpiNT (by native_decide)]
  have rd37 := evm_run_rfl rd36 with [dup1, push1 ⟨3⟩, eq, push2 ⟨6064⟩, jumpiNT (by native_decide)]
  have rd38 := evm_run_rfl rd37 with [dup1, push1 ⟨4⟩, eq, push2 ⟨6045⟩, jumpiNT (by native_decide)]
  have rd39 := evm_run_rfl rd38 with [dup1, push1 ⟨5⟩, eq, push2 ⟨6026⟩, jumpiNT (by native_decide)]
  have rd40 := evm_run_rfl rd39 with [dup1, push1 ⟨6⟩, eq, push2 ⟨6007⟩, jumpiNT (by native_decide)]
  have rd41 := evm_run_rfl rd40 with [dup1, push1 ⟨7⟩, eq, push2 ⟨5988⟩, jumpiNT (by native_decide)]
  have rd42 := evm_run_rfl rd41 with [dup1, push1 ⟨8⟩, eq, push2 ⟨5969⟩, jumpiNT (by native_decide)]
  have rd43 := evm_run_rfl rd42 with [dup1, push1 ⟨9⟩, eq, push2 ⟨5950⟩, jumpiNT (by native_decide)]
  have rd44 := evm_run_rfl rd43 with [dup1, dup15, eq, push2 ⟨5931⟩, jumpiNT (by native_decide)]
  have rd45 := evm_run_rfl rd44 with [dup1, push1 ⟨11⟩, eq, push2 ⟨5912⟩, jumpiNT (by native_decide)]
  have rd46 := evm_run_rfl rd45 with [dup1, push1 ⟨12⟩, eq, push2 ⟨5893⟩, jumpiNT (by native_decide)]
  have rd47 := evm_run_rfl rd46 with [dup1, push1 ⟨13⟩, eq, push2 ⟨5874⟩, jumpiT (by native_decide) jump_5874]
  have rd48 := evm_run_rfl rd47 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨15⟩, swap8, swap2, swap3, pop, pop, push2 ⟨5828⟩, jump jump_5828]
  have rd49 := evm_run_rfl rd48 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨4311⟩, jump jump_4311]
  have rd50 := evm_run_rfl rd49 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd51 := RD.runtimeMload rd50 (by old_decode) (by simp; omega)
  have rd52 := evm_run_rfl rd51 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd53 := evm_run_rfl rd52 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4328]
  have rd54 := evm_run_rfl rd53 with [jumpdest, add, and, swap8, dup7]
  have rd55 := RD.runtimeMstore rd54 (by old_decode) (by simp; omega)
  have rd56 := evm_run_rfl rd55 with [push1 ⟨128⟩, dup7, add]
  have rd57 := RD.runtimeMstore rd56 (by old_decode) (by simp; omega)
  have rd58 := evm_run_rfl rd57 with [push2 ⟨268⟩, jump jump_268]
  have rd59 := evm_run_rfl rd58 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4343]
  have rd60 := evm_run_rfl rd59 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd61 := RD.runtimeMstore rd60 (by old_decode) (by simp; omega)
  have rd62 := evm_run_rfl rd61 with [push1 ⟨64⟩, dup3, add]
  have rd63 := RD.runtimeMstore rd62 (by old_decode) (by simp; omega)
  have rd64 := evm_run_rfl rd63 with [add]
  have rd65 := RD.runtimeMstore rd64 (by old_decode) (by simp; omega)
  have rd66 := evm_run_rfl rd65 with [jump jump_8967]
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
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd66⟩


end Ripemd160Old
