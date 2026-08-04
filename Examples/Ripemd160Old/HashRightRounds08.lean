import Examples.Ripemd160Old.HashRightRound0
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000
namespace Ripemd160Old
open Ripemd160

theorem runtime_rightRoundHelper_10 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I 10 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) 0 10).mem
      (oldRightRoundCursor c (hashScratchPtr I) 0 10).aw
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
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨9⟩, eq, push2 ⟨8021⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup16, dup2, eq, push2 ⟨8010⟩, jumpiT (by native_decide) jump_8010]
  have rd25 := evm_run_rfl rd24 with [jumpdest, pop, swap1, pop, push1 ⟨15⟩, swap1, push2 ⟨7952⟩, jump jump_7952]
  have rd26 := evm_run_rfl rd25 with [jumpdest, push2 ⟨4270⟩, jump jump_4270]
  have rd27 := evm_run_rfl rd26 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨6140⟩, jumpiT (by native_decide) jump_6140]
  have rd28 := evm_run_rfl rd27 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨6567⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [dup1, push1 ⟨1⟩, eq, push2 ⟨6548⟩, jumpiNT (by native_decide)]
  have rd30 := evm_run_rfl rd29 with [dup1, push1 ⟨2⟩, eq, push2 ⟨6529⟩, jumpiNT (by native_decide)]
  have rd31 := evm_run_rfl rd30 with [dup1, push1 ⟨3⟩, eq, push2 ⟨6510⟩, jumpiNT (by native_decide)]
  have rd32 := evm_run_rfl rd31 with [dup1, push1 ⟨4⟩, eq, push2 ⟨6491⟩, jumpiNT (by native_decide)]
  have rd33 := evm_run_rfl rd32 with [dup1, push1 ⟨5⟩, eq, push2 ⟨6472⟩, jumpiNT (by native_decide)]
  have rd34 := evm_run_rfl rd33 with [dup1, push1 ⟨6⟩, eq, push2 ⟨6453⟩, jumpiNT (by native_decide)]
  have rd35 := evm_run_rfl rd34 with [dup1, push1 ⟨7⟩, eq, push2 ⟨6434⟩, jumpiNT (by native_decide)]
  have rd36 := evm_run_rfl rd35 with [dup1, push1 ⟨8⟩, eq, push2 ⟨6415⟩, jumpiNT (by native_decide)]
  have rd37 := evm_run_rfl rd36 with [dup1, push1 ⟨9⟩, eq, push2 ⟨6396⟩, jumpiNT (by native_decide)]
  have rd38 := evm_run_rfl rd37 with [dup1, dup15, eq, push2 ⟨6377⟩, jumpiT (by native_decide) jump_6377]
  have rd39 := evm_run_rfl rd38 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨8⟩, swap8, swap2, swap3, pop, pop, push2 ⟨6274⟩, jump jump_6274]
  have rd40 := evm_run_rfl rd39 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨4311⟩, jump jump_4311]
  have rd41 := evm_run_rfl rd40 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd42 := RD.runtimeMload rd41 (by old_decode) (by simp; omega)
  have rd43 := evm_run_rfl rd42 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd44 := evm_run_rfl rd43 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4328]
  have rd45 := evm_run_rfl rd44 with [jumpdest, add, and, swap8, dup7]
  have rd46 := RD.runtimeMstore rd45 (by old_decode) (by simp; omega)
  have rd47 := evm_run_rfl rd46 with [push1 ⟨128⟩, dup7, add]
  have rd48 := RD.runtimeMstore rd47 (by old_decode) (by simp; omega)
  have rd49 := evm_run_rfl rd48 with [push2 ⟨268⟩, jump jump_268]
  have rd50 := evm_run_rfl rd49 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4343]
  have rd51 := evm_run_rfl rd50 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd52 := RD.runtimeMstore rd51 (by old_decode) (by simp; omega)
  have rd53 := evm_run_rfl rd52 with [push1 ⟨64⟩, dup3, add]
  have rd54 := RD.runtimeMstore rd53 (by old_decode) (by simp; omega)
  have rd55 := evm_run_rfl rd54 with [add]
  have rd56 := RD.runtimeMstore rd55 (by old_decode) (by simp; omega)
  have rd57 := evm_run_rfl rd56 with [jump jump_8967]
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
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd57⟩

theorem runtime_rightRoundHelper_11 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I 11 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) 0 11).mem
      (oldRightRoundCursor c (hashScratchPtr I) 0 11).aw
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
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨9⟩, eq, push2 ⟨8021⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup16, dup2, eq, push2 ⟨8010⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨11⟩, eq, push2 ⟨7999⟩, jumpiT (by native_decide) jump_7999]
  have rd26 := evm_run_rfl rd25 with [jumpdest, pop, swap1, pop, push1 ⟨8⟩, swap1, push2 ⟨7952⟩, jump jump_7952]
  have rd27 := evm_run_rfl rd26 with [jumpdest, push2 ⟨4270⟩, jump jump_4270]
  have rd28 := evm_run_rfl rd27 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨6140⟩, jumpiT (by native_decide) jump_6140]
  have rd29 := evm_run_rfl rd28 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨6567⟩, jumpiNT (by native_decide)]
  have rd30 := evm_run_rfl rd29 with [dup1, push1 ⟨1⟩, eq, push2 ⟨6548⟩, jumpiNT (by native_decide)]
  have rd31 := evm_run_rfl rd30 with [dup1, push1 ⟨2⟩, eq, push2 ⟨6529⟩, jumpiNT (by native_decide)]
  have rd32 := evm_run_rfl rd31 with [dup1, push1 ⟨3⟩, eq, push2 ⟨6510⟩, jumpiNT (by native_decide)]
  have rd33 := evm_run_rfl rd32 with [dup1, push1 ⟨4⟩, eq, push2 ⟨6491⟩, jumpiNT (by native_decide)]
  have rd34 := evm_run_rfl rd33 with [dup1, push1 ⟨5⟩, eq, push2 ⟨6472⟩, jumpiNT (by native_decide)]
  have rd35 := evm_run_rfl rd34 with [dup1, push1 ⟨6⟩, eq, push2 ⟨6453⟩, jumpiNT (by native_decide)]
  have rd36 := evm_run_rfl rd35 with [dup1, push1 ⟨7⟩, eq, push2 ⟨6434⟩, jumpiNT (by native_decide)]
  have rd37 := evm_run_rfl rd36 with [dup1, push1 ⟨8⟩, eq, push2 ⟨6415⟩, jumpiNT (by native_decide)]
  have rd38 := evm_run_rfl rd37 with [dup1, push1 ⟨9⟩, eq, push2 ⟨6396⟩, jumpiNT (by native_decide)]
  have rd39 := evm_run_rfl rd38 with [dup1, dup15, eq, push2 ⟨6377⟩, jumpiNT (by native_decide)]
  have rd40 := evm_run_rfl rd39 with [dup1, push1 ⟨11⟩, eq, push2 ⟨6358⟩, jumpiT (by native_decide) jump_6358]
  have rd41 := evm_run_rfl rd40 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨11⟩, swap8, swap2, swap3, pop, pop, push2 ⟨6274⟩, jump jump_6274]
  have rd42 := evm_run_rfl rd41 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨4311⟩, jump jump_4311]
  have rd43 := evm_run_rfl rd42 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd44 := RD.runtimeMload rd43 (by old_decode) (by simp; omega)
  have rd45 := evm_run_rfl rd44 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd46 := evm_run_rfl rd45 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4328]
  have rd47 := evm_run_rfl rd46 with [jumpdest, add, and, swap8, dup7]
  have rd48 := RD.runtimeMstore rd47 (by old_decode) (by simp; omega)
  have rd49 := evm_run_rfl rd48 with [push1 ⟨128⟩, dup7, add]
  have rd50 := RD.runtimeMstore rd49 (by old_decode) (by simp; omega)
  have rd51 := evm_run_rfl rd50 with [push2 ⟨268⟩, jump jump_268]
  have rd52 := evm_run_rfl rd51 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4343]
  have rd53 := evm_run_rfl rd52 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd54 := RD.runtimeMstore rd53 (by old_decode) (by simp; omega)
  have rd55 := evm_run_rfl rd54 with [push1 ⟨64⟩, dup3, add]
  have rd56 := RD.runtimeMstore rd55 (by old_decode) (by simp; omega)
  have rd57 := evm_run_rfl rd56 with [add]
  have rd58 := RD.runtimeMstore rd57 (by old_decode) (by simp; omega)
  have rd59 := evm_run_rfl rd58 with [jump jump_8967]
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
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd59⟩

theorem runtime_rightRoundHelper_12 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I 12 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) 0 12).mem
      (oldRightRoundCursor c (hashScratchPtr I) 0 12).aw
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
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨9⟩, eq, push2 ⟨8021⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup16, dup2, eq, push2 ⟨8010⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨11⟩, eq, push2 ⟨7999⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup1, push1 ⟨12⟩, eq, push2 ⟨7988⟩, jumpiT (by native_decide) jump_7988]
  have rd27 := evm_run_rfl rd26 with [jumpdest, pop, swap1, pop, push1 ⟨1⟩, swap1, push2 ⟨7952⟩, jump jump_7952]
  have rd28 := evm_run_rfl rd27 with [jumpdest, push2 ⟨4270⟩, jump jump_4270]
  have rd29 := evm_run_rfl rd28 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨6140⟩, jumpiT (by native_decide) jump_6140]
  have rd30 := evm_run_rfl rd29 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨6567⟩, jumpiNT (by native_decide)]
  have rd31 := evm_run_rfl rd30 with [dup1, push1 ⟨1⟩, eq, push2 ⟨6548⟩, jumpiNT (by native_decide)]
  have rd32 := evm_run_rfl rd31 with [dup1, push1 ⟨2⟩, eq, push2 ⟨6529⟩, jumpiNT (by native_decide)]
  have rd33 := evm_run_rfl rd32 with [dup1, push1 ⟨3⟩, eq, push2 ⟨6510⟩, jumpiNT (by native_decide)]
  have rd34 := evm_run_rfl rd33 with [dup1, push1 ⟨4⟩, eq, push2 ⟨6491⟩, jumpiNT (by native_decide)]
  have rd35 := evm_run_rfl rd34 with [dup1, push1 ⟨5⟩, eq, push2 ⟨6472⟩, jumpiNT (by native_decide)]
  have rd36 := evm_run_rfl rd35 with [dup1, push1 ⟨6⟩, eq, push2 ⟨6453⟩, jumpiNT (by native_decide)]
  have rd37 := evm_run_rfl rd36 with [dup1, push1 ⟨7⟩, eq, push2 ⟨6434⟩, jumpiNT (by native_decide)]
  have rd38 := evm_run_rfl rd37 with [dup1, push1 ⟨8⟩, eq, push2 ⟨6415⟩, jumpiNT (by native_decide)]
  have rd39 := evm_run_rfl rd38 with [dup1, push1 ⟨9⟩, eq, push2 ⟨6396⟩, jumpiNT (by native_decide)]
  have rd40 := evm_run_rfl rd39 with [dup1, dup15, eq, push2 ⟨6377⟩, jumpiNT (by native_decide)]
  have rd41 := evm_run_rfl rd40 with [dup1, push1 ⟨11⟩, eq, push2 ⟨6358⟩, jumpiNT (by native_decide)]
  have rd42 := evm_run_rfl rd41 with [dup1, push1 ⟨12⟩, eq, push2 ⟨6339⟩, jumpiT (by native_decide) jump_6339]
  have rd43 := evm_run_rfl rd42 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨14⟩, swap8, swap2, swap3, pop, pop, push2 ⟨6274⟩, jump jump_6274]
  have rd44 := evm_run_rfl rd43 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨4311⟩, jump jump_4311]
  have rd45 := evm_run_rfl rd44 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd46 := RD.runtimeMload rd45 (by old_decode) (by simp; omega)
  have rd47 := evm_run_rfl rd46 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd48 := evm_run_rfl rd47 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4328]
  have rd49 := evm_run_rfl rd48 with [jumpdest, add, and, swap8, dup7]
  have rd50 := RD.runtimeMstore rd49 (by old_decode) (by simp; omega)
  have rd51 := evm_run_rfl rd50 with [push1 ⟨128⟩, dup7, add]
  have rd52 := RD.runtimeMstore rd51 (by old_decode) (by simp; omega)
  have rd53 := evm_run_rfl rd52 with [push2 ⟨268⟩, jump jump_268]
  have rd54 := evm_run_rfl rd53 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4343]
  have rd55 := evm_run_rfl rd54 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd56 := RD.runtimeMstore rd55 (by old_decode) (by simp; omega)
  have rd57 := evm_run_rfl rd56 with [push1 ⟨64⟩, dup3, add]
  have rd58 := RD.runtimeMstore rd57 (by old_decode) (by simp; omega)
  have rd59 := evm_run_rfl rd58 with [add]
  have rd60 := RD.runtimeMstore rd59 (by old_decode) (by simp; omega)
  have rd61 := evm_run_rfl rd60 with [jump jump_8967]
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
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd61⟩

theorem runtime_rightRoundHelper_13 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I 13 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) 0 13).mem
      (oldRightRoundCursor c (hashScratchPtr I) 0 13).aw
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
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨9⟩, eq, push2 ⟨8021⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup16, dup2, eq, push2 ⟨8010⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨11⟩, eq, push2 ⟨7999⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup1, push1 ⟨12⟩, eq, push2 ⟨7988⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨13⟩, eq, push2 ⟨7978⟩, jumpiT (by native_decide) jump_7978]
  have rd28 := evm_run_rfl rd27 with [jumpdest, pop, swap1, pop, dup14, swap1, push2 ⟨7952⟩, jump jump_7952]
  have rd29 := evm_run_rfl rd28 with [jumpdest, push2 ⟨4270⟩, jump jump_4270]
  have rd30 := evm_run_rfl rd29 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨6140⟩, jumpiT (by native_decide) jump_6140]
  have rd31 := evm_run_rfl rd30 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨6567⟩, jumpiNT (by native_decide)]
  have rd32 := evm_run_rfl rd31 with [dup1, push1 ⟨1⟩, eq, push2 ⟨6548⟩, jumpiNT (by native_decide)]
  have rd33 := evm_run_rfl rd32 with [dup1, push1 ⟨2⟩, eq, push2 ⟨6529⟩, jumpiNT (by native_decide)]
  have rd34 := evm_run_rfl rd33 with [dup1, push1 ⟨3⟩, eq, push2 ⟨6510⟩, jumpiNT (by native_decide)]
  have rd35 := evm_run_rfl rd34 with [dup1, push1 ⟨4⟩, eq, push2 ⟨6491⟩, jumpiNT (by native_decide)]
  have rd36 := evm_run_rfl rd35 with [dup1, push1 ⟨5⟩, eq, push2 ⟨6472⟩, jumpiNT (by native_decide)]
  have rd37 := evm_run_rfl rd36 with [dup1, push1 ⟨6⟩, eq, push2 ⟨6453⟩, jumpiNT (by native_decide)]
  have rd38 := evm_run_rfl rd37 with [dup1, push1 ⟨7⟩, eq, push2 ⟨6434⟩, jumpiNT (by native_decide)]
  have rd39 := evm_run_rfl rd38 with [dup1, push1 ⟨8⟩, eq, push2 ⟨6415⟩, jumpiNT (by native_decide)]
  have rd40 := evm_run_rfl rd39 with [dup1, push1 ⟨9⟩, eq, push2 ⟨6396⟩, jumpiNT (by native_decide)]
  have rd41 := evm_run_rfl rd40 with [dup1, dup15, eq, push2 ⟨6377⟩, jumpiNT (by native_decide)]
  have rd42 := evm_run_rfl rd41 with [dup1, push1 ⟨11⟩, eq, push2 ⟨6358⟩, jumpiNT (by native_decide)]
  have rd43 := evm_run_rfl rd42 with [dup1, push1 ⟨12⟩, eq, push2 ⟨6339⟩, jumpiNT (by native_decide)]
  have rd44 := evm_run_rfl rd43 with [dup1, push1 ⟨13⟩, eq, push2 ⟨6320⟩, jumpiT (by native_decide) jump_6320]
  have rd45 := evm_run_rfl rd44 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨14⟩, swap8, swap2, swap3, pop, pop, push2 ⟨6274⟩, jump jump_6274]
  have rd46 := evm_run_rfl rd45 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨4311⟩, jump jump_4311]
  have rd47 := evm_run_rfl rd46 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd48 := RD.runtimeMload rd47 (by old_decode) (by simp; omega)
  have rd49 := evm_run_rfl rd48 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd50 := evm_run_rfl rd49 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4328]
  have rd51 := evm_run_rfl rd50 with [jumpdest, add, and, swap8, dup7]
  have rd52 := RD.runtimeMstore rd51 (by old_decode) (by simp; omega)
  have rd53 := evm_run_rfl rd52 with [push1 ⟨128⟩, dup7, add]
  have rd54 := RD.runtimeMstore rd53 (by old_decode) (by simp; omega)
  have rd55 := evm_run_rfl rd54 with [push2 ⟨268⟩, jump jump_268]
  have rd56 := evm_run_rfl rd55 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4343]
  have rd57 := evm_run_rfl rd56 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd58 := RD.runtimeMstore rd57 (by old_decode) (by simp; omega)
  have rd59 := evm_run_rfl rd58 with [push1 ⟨64⟩, dup3, add]
  have rd60 := RD.runtimeMstore rd59 (by old_decode) (by simp; omega)
  have rd61 := evm_run_rfl rd60 with [add]
  have rd62 := RD.runtimeMstore rd61 (by old_decode) (by simp; omega)
  have rd63 := evm_run_rfl rd62 with [jump jump_8967]
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
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd63⟩

theorem runtime_rightRoundHelper_14 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I 14 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) 0 14).mem
      (oldRightRoundCursor c (hashScratchPtr I) 0 14).aw
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
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨9⟩, eq, push2 ⟨8021⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup16, dup2, eq, push2 ⟨8010⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨11⟩, eq, push2 ⟨7999⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup1, push1 ⟨12⟩, eq, push2 ⟨7988⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨13⟩, eq, push2 ⟨7978⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨14⟩, eq, push2 ⟨7967⟩, jumpiT (by native_decide) jump_7967]
  have rd29 := evm_run_rfl rd28 with [jumpdest, pop, swap1, pop, push1 ⟨3⟩, swap1, push2 ⟨7952⟩, jump jump_7952]
  have rd30 := evm_run_rfl rd29 with [jumpdest, push2 ⟨4270⟩, jump jump_4270]
  have rd31 := evm_run_rfl rd30 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨6140⟩, jumpiT (by native_decide) jump_6140]
  have rd32 := evm_run_rfl rd31 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨6567⟩, jumpiNT (by native_decide)]
  have rd33 := evm_run_rfl rd32 with [dup1, push1 ⟨1⟩, eq, push2 ⟨6548⟩, jumpiNT (by native_decide)]
  have rd34 := evm_run_rfl rd33 with [dup1, push1 ⟨2⟩, eq, push2 ⟨6529⟩, jumpiNT (by native_decide)]
  have rd35 := evm_run_rfl rd34 with [dup1, push1 ⟨3⟩, eq, push2 ⟨6510⟩, jumpiNT (by native_decide)]
  have rd36 := evm_run_rfl rd35 with [dup1, push1 ⟨4⟩, eq, push2 ⟨6491⟩, jumpiNT (by native_decide)]
  have rd37 := evm_run_rfl rd36 with [dup1, push1 ⟨5⟩, eq, push2 ⟨6472⟩, jumpiNT (by native_decide)]
  have rd38 := evm_run_rfl rd37 with [dup1, push1 ⟨6⟩, eq, push2 ⟨6453⟩, jumpiNT (by native_decide)]
  have rd39 := evm_run_rfl rd38 with [dup1, push1 ⟨7⟩, eq, push2 ⟨6434⟩, jumpiNT (by native_decide)]
  have rd40 := evm_run_rfl rd39 with [dup1, push1 ⟨8⟩, eq, push2 ⟨6415⟩, jumpiNT (by native_decide)]
  have rd41 := evm_run_rfl rd40 with [dup1, push1 ⟨9⟩, eq, push2 ⟨6396⟩, jumpiNT (by native_decide)]
  have rd42 := evm_run_rfl rd41 with [dup1, dup15, eq, push2 ⟨6377⟩, jumpiNT (by native_decide)]
  have rd43 := evm_run_rfl rd42 with [dup1, push1 ⟨11⟩, eq, push2 ⟨6358⟩, jumpiNT (by native_decide)]
  have rd44 := evm_run_rfl rd43 with [dup1, push1 ⟨12⟩, eq, push2 ⟨6339⟩, jumpiNT (by native_decide)]
  have rd45 := evm_run_rfl rd44 with [dup1, push1 ⟨13⟩, eq, push2 ⟨6320⟩, jumpiNT (by native_decide)]
  have rd46 := evm_run_rfl rd45 with [dup1, push1 ⟨14⟩, eq, push2 ⟨6301⟩, jumpiT (by native_decide) jump_6301]
  have rd47 := evm_run_rfl rd46 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨12⟩, swap8, swap2, swap3, pop, pop, push2 ⟨6274⟩, jump jump_6274]
  have rd48 := evm_run_rfl rd47 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨4311⟩, jump jump_4311]
  have rd49 := evm_run_rfl rd48 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd50 := RD.runtimeMload rd49 (by old_decode) (by simp; omega)
  have rd51 := evm_run_rfl rd50 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd52 := evm_run_rfl rd51 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4328]
  have rd53 := evm_run_rfl rd52 with [jumpdest, add, and, swap8, dup7]
  have rd54 := RD.runtimeMstore rd53 (by old_decode) (by simp; omega)
  have rd55 := evm_run_rfl rd54 with [push1 ⟨128⟩, dup7, add]
  have rd56 := RD.runtimeMstore rd55 (by old_decode) (by simp; omega)
  have rd57 := evm_run_rfl rd56 with [push2 ⟨268⟩, jump jump_268]
  have rd58 := evm_run_rfl rd57 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4343]
  have rd59 := evm_run_rfl rd58 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd60 := RD.runtimeMstore rd59 (by old_decode) (by simp; omega)
  have rd61 := evm_run_rfl rd60 with [push1 ⟨64⟩, dup3, add]
  have rd62 := RD.runtimeMstore rd61 (by old_decode) (by simp; omega)
  have rd63 := evm_run_rfl rd62 with [add]
  have rd64 := RD.runtimeMstore rd63 (by old_decode) (by simp; omega)
  have rd65 := evm_run_rfl rd64 with [jump jump_8967]
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
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd65⟩

theorem runtime_rightRoundHelper_15 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I 15 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) 0 15).mem
      (oldRightRoundCursor c (hashScratchPtr I) 0 15).aw
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
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨9⟩, eq, push2 ⟨8021⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup16, dup2, eq, push2 ⟨8010⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨11⟩, eq, push2 ⟨7999⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup1, push1 ⟨12⟩, eq, push2 ⟨7988⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨13⟩, eq, push2 ⟨7978⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨14⟩, eq, push2 ⟨7967⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [push1 ⟨15⟩, eq, push2 ⟨7957⟩, jumpiT (by native_decide) jump_7957]
  have rd30 := evm_run_rfl rd29 with [jumpdest, swap1, pop, push1 ⟨12⟩, swap1, push2 ⟨7952⟩, jump jump_7952]
  have rd31 := evm_run_rfl rd30 with [jumpdest, push2 ⟨4270⟩, jump jump_4270]
  have rd32 := evm_run_rfl rd31 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨6140⟩, jumpiT (by native_decide) jump_6140]
  have rd33 := evm_run_rfl rd32 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨6567⟩, jumpiNT (by native_decide)]
  have rd34 := evm_run_rfl rd33 with [dup1, push1 ⟨1⟩, eq, push2 ⟨6548⟩, jumpiNT (by native_decide)]
  have rd35 := evm_run_rfl rd34 with [dup1, push1 ⟨2⟩, eq, push2 ⟨6529⟩, jumpiNT (by native_decide)]
  have rd36 := evm_run_rfl rd35 with [dup1, push1 ⟨3⟩, eq, push2 ⟨6510⟩, jumpiNT (by native_decide)]
  have rd37 := evm_run_rfl rd36 with [dup1, push1 ⟨4⟩, eq, push2 ⟨6491⟩, jumpiNT (by native_decide)]
  have rd38 := evm_run_rfl rd37 with [dup1, push1 ⟨5⟩, eq, push2 ⟨6472⟩, jumpiNT (by native_decide)]
  have rd39 := evm_run_rfl rd38 with [dup1, push1 ⟨6⟩, eq, push2 ⟨6453⟩, jumpiNT (by native_decide)]
  have rd40 := evm_run_rfl rd39 with [dup1, push1 ⟨7⟩, eq, push2 ⟨6434⟩, jumpiNT (by native_decide)]
  have rd41 := evm_run_rfl rd40 with [dup1, push1 ⟨8⟩, eq, push2 ⟨6415⟩, jumpiNT (by native_decide)]
  have rd42 := evm_run_rfl rd41 with [dup1, push1 ⟨9⟩, eq, push2 ⟨6396⟩, jumpiNT (by native_decide)]
  have rd43 := evm_run_rfl rd42 with [dup1, dup15, eq, push2 ⟨6377⟩, jumpiNT (by native_decide)]
  have rd44 := evm_run_rfl rd43 with [dup1, push1 ⟨11⟩, eq, push2 ⟨6358⟩, jumpiNT (by native_decide)]
  have rd45 := evm_run_rfl rd44 with [dup1, push1 ⟨12⟩, eq, push2 ⟨6339⟩, jumpiNT (by native_decide)]
  have rd46 := evm_run_rfl rd45 with [dup1, push1 ⟨13⟩, eq, push2 ⟨6320⟩, jumpiNT (by native_decide)]
  have rd47 := evm_run_rfl rd46 with [dup1, push1 ⟨14⟩, eq, push2 ⟨6301⟩, jumpiNT (by native_decide)]
  have rd48 := evm_run_rfl rd47 with [push1 ⟨15⟩, eq, push2 ⟨6283⟩, jumpiT (by native_decide) jump_6283]
  have rd49 := evm_run_rfl rd48 with [jumpdest, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨6⟩, swap8, swap2, swap3, pop, pop, push2 ⟨6274⟩, jump jump_6274]
  have rd50 := evm_run_rfl rd49 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨4311⟩, jump jump_4311]
  have rd51 := evm_run_rfl rd50 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd52 := RD.runtimeMload rd51 (by old_decode) (by simp; omega)
  have rd53 := evm_run_rfl rd52 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd54 := evm_run_rfl rd53 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4328]
  have rd55 := evm_run_rfl rd54 with [jumpdest, add, and, swap8, dup7]
  have rd56 := RD.runtimeMstore rd55 (by old_decode) (by simp; omega)
  have rd57 := evm_run_rfl rd56 with [push1 ⟨128⟩, dup7, add]
  have rd58 := RD.runtimeMstore rd57 (by old_decode) (by simp; omega)
  have rd59 := evm_run_rfl rd58 with [push2 ⟨268⟩, jump jump_268]
  have rd60 := evm_run_rfl rd59 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4343]
  have rd61 := evm_run_rfl rd60 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd62 := RD.runtimeMstore rd61 (by old_decode) (by simp; omega)
  have rd63 := evm_run_rfl rd62 with [push1 ⟨64⟩, dup3, add]
  have rd64 := RD.runtimeMstore rd63 (by old_decode) (by simp; omega)
  have rd65 := evm_run_rfl rd64 with [add]
  have rd66 := RD.runtimeMstore rd65 (by old_decode) (by simp; omega)
  have rd67 := evm_run_rfl rd66 with [jump jump_8967]
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
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd67⟩

theorem runtime_rightRoundHelper_16 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I 16 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) 1 0).mem
      (oldRightRoundCursor c (hashScratchPtr I) 1 0).aw
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
  have rd16 := evm_run_rfl rd15 with [jumpdest, pop, push1 ⟨16⟩, dup2, mod, dup1, push0, eq, push2 ⟨7810⟩, jumpiT (by native_decide) jump_7810]
  have rd17 := evm_run_rfl rd16 with [jumpdest, pop, swap1, pop, push1 ⟨6⟩, swap1, push2 ⟨7643⟩, jump jump_7643]
  have rd18 := evm_run_rfl rd17 with [jumpdest, push2 ⟨4270⟩, jump jump_4270]
  have rd19 := evm_run_rfl rd18 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨6140⟩, jumpiNT (by native_decide)]
  have rd20 := evm_run_rfl rd19 with [dup1, push1 ⟨1⟩, eq, push2 ⟨5694⟩, jumpiT (by native_decide) jump_5694]
  have rd21 := evm_run_rfl rd20 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨6121⟩, jumpiT (by native_decide) jump_6121]
  have rd22 := evm_run_rfl rd21 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨9⟩, swap8, swap2, swap3, pop, pop, push2 ⟨5828⟩, jump jump_5828]
  have rd23 := evm_run_rfl rd22 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨4311⟩, jump jump_4311]
  have rd24 := evm_run_rfl rd23 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd25 := RD.runtimeMload rd24 (by old_decode) (by simp; omega)
  have rd26 := evm_run_rfl rd25 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd27 := evm_run_rfl rd26 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4328]
  have rd28 := evm_run_rfl rd27 with [jumpdest, add, and, swap8, dup7]
  have rd29 := RD.runtimeMstore rd28 (by old_decode) (by simp; omega)
  have rd30 := evm_run_rfl rd29 with [push1 ⟨128⟩, dup7, add]
  have rd31 := RD.runtimeMstore rd30 (by old_decode) (by simp; omega)
  have rd32 := evm_run_rfl rd31 with [push2 ⟨268⟩, jump jump_268]
  have rd33 := evm_run_rfl rd32 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4343]
  have rd34 := evm_run_rfl rd33 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd35 := RD.runtimeMstore rd34 (by old_decode) (by simp; omega)
  have rd36 := evm_run_rfl rd35 with [push1 ⟨64⟩, dup3, add]
  have rd37 := RD.runtimeMstore rd36 (by old_decode) (by simp; omega)
  have rd38 := evm_run_rfl rd37 with [add]
  have rd39 := RD.runtimeMstore rd38 (by old_decode) (by simp; omega)
  have rd40 := evm_run_rfl rd39 with [jump jump_8967]
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
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd40⟩

theorem runtime_rightRoundHelper_17 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I 17 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) 1 1).mem
      (oldRightRoundCursor c (hashScratchPtr I) 1 1).aw
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
  have rd17 := evm_run_rfl rd16 with [dup1, push1 ⟨1⟩, eq, push2 ⟨7799⟩, jumpiT (by native_decide) jump_7799]
  have rd18 := evm_run_rfl rd17 with [jumpdest, pop, swap1, pop, push1 ⟨11⟩, swap1, push2 ⟨7643⟩, jump jump_7643]
  have rd19 := evm_run_rfl rd18 with [jumpdest, push2 ⟨4270⟩, jump jump_4270]
  have rd20 := evm_run_rfl rd19 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨6140⟩, jumpiNT (by native_decide)]
  have rd21 := evm_run_rfl rd20 with [dup1, push1 ⟨1⟩, eq, push2 ⟨5694⟩, jumpiT (by native_decide) jump_5694]
  have rd22 := evm_run_rfl rd21 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨6121⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨1⟩, eq, push2 ⟨6102⟩, jumpiT (by native_decide) jump_6102]
  have rd24 := evm_run_rfl rd23 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨13⟩, swap8, swap2, swap3, pop, pop, push2 ⟨5828⟩, jump jump_5828]
  have rd25 := evm_run_rfl rd24 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨4311⟩, jump jump_4311]
  have rd26 := evm_run_rfl rd25 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd27 := RD.runtimeMload rd26 (by old_decode) (by simp; omega)
  have rd28 := evm_run_rfl rd27 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd29 := evm_run_rfl rd28 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4328]
  have rd30 := evm_run_rfl rd29 with [jumpdest, add, and, swap8, dup7]
  have rd31 := RD.runtimeMstore rd30 (by old_decode) (by simp; omega)
  have rd32 := evm_run_rfl rd31 with [push1 ⟨128⟩, dup7, add]
  have rd33 := RD.runtimeMstore rd32 (by old_decode) (by simp; omega)
  have rd34 := evm_run_rfl rd33 with [push2 ⟨268⟩, jump jump_268]
  have rd35 := evm_run_rfl rd34 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4343]
  have rd36 := evm_run_rfl rd35 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd37 := RD.runtimeMstore rd36 (by old_decode) (by simp; omega)
  have rd38 := evm_run_rfl rd37 with [push1 ⟨64⟩, dup3, add]
  have rd39 := RD.runtimeMstore rd38 (by old_decode) (by simp; omega)
  have rd40 := evm_run_rfl rd39 with [add]
  have rd41 := RD.runtimeMstore rd40 (by old_decode) (by simp; omega)
  have rd42 := evm_run_rfl rd41 with [jump jump_8967]
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
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd42⟩

theorem runtime_rightRoundHelper_18 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I 18 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) 1 2).mem
      (oldRightRoundCursor c (hashScratchPtr I) 1 2).aw
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
  have rd18 := evm_run_rfl rd17 with [dup1, push1 ⟨2⟩, eq, push2 ⟨7788⟩, jumpiT (by native_decide) jump_7788]
  have rd19 := evm_run_rfl rd18 with [jumpdest, pop, swap1, pop, push1 ⟨3⟩, swap1, push2 ⟨7643⟩, jump jump_7643]
  have rd20 := evm_run_rfl rd19 with [jumpdest, push2 ⟨4270⟩, jump jump_4270]
  have rd21 := evm_run_rfl rd20 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨6140⟩, jumpiNT (by native_decide)]
  have rd22 := evm_run_rfl rd21 with [dup1, push1 ⟨1⟩, eq, push2 ⟨5694⟩, jumpiT (by native_decide) jump_5694]
  have rd23 := evm_run_rfl rd22 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨6121⟩, jumpiNT (by native_decide)]
  have rd24 := evm_run_rfl rd23 with [dup1, push1 ⟨1⟩, eq, push2 ⟨6102⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨2⟩, eq, push2 ⟨6083⟩, jumpiT (by native_decide) jump_6083]
  have rd26 := evm_run_rfl rd25 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨15⟩, swap8, swap2, swap3, pop, pop, push2 ⟨5828⟩, jump jump_5828]
  have rd27 := evm_run_rfl rd26 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨4311⟩, jump jump_4311]
  have rd28 := evm_run_rfl rd27 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd29 := RD.runtimeMload rd28 (by old_decode) (by simp; omega)
  have rd30 := evm_run_rfl rd29 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd31 := evm_run_rfl rd30 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4328]
  have rd32 := evm_run_rfl rd31 with [jumpdest, add, and, swap8, dup7]
  have rd33 := RD.runtimeMstore rd32 (by old_decode) (by simp; omega)
  have rd34 := evm_run_rfl rd33 with [push1 ⟨128⟩, dup7, add]
  have rd35 := RD.runtimeMstore rd34 (by old_decode) (by simp; omega)
  have rd36 := evm_run_rfl rd35 with [push2 ⟨268⟩, jump jump_268]
  have rd37 := evm_run_rfl rd36 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4343]
  have rd38 := evm_run_rfl rd37 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd39 := RD.runtimeMstore rd38 (by old_decode) (by simp; omega)
  have rd40 := evm_run_rfl rd39 with [push1 ⟨64⟩, dup3, add]
  have rd41 := RD.runtimeMstore rd40 (by old_decode) (by simp; omega)
  have rd42 := evm_run_rfl rd41 with [add]
  have rd43 := RD.runtimeMstore rd42 (by old_decode) (by simp; omega)
  have rd44 := evm_run_rfl rd43 with [jump jump_8967]
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
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd44⟩

theorem runtime_rightRoundHelper_19 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I 19 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) 1 3).mem
      (oldRightRoundCursor c (hashScratchPtr I) 1 3).aw
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
  have rd19 := evm_run_rfl rd18 with [dup1, push1 ⟨3⟩, eq, push2 ⟨7777⟩, jumpiT (by native_decide) jump_7777]
  have rd20 := evm_run_rfl rd19 with [jumpdest, pop, swap1, pop, push1 ⟨7⟩, swap1, push2 ⟨7643⟩, jump jump_7643]
  have rd21 := evm_run_rfl rd20 with [jumpdest, push2 ⟨4270⟩, jump jump_4270]
  have rd22 := evm_run_rfl rd21 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨6140⟩, jumpiNT (by native_decide)]
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨1⟩, eq, push2 ⟨5694⟩, jumpiT (by native_decide) jump_5694]
  have rd24 := evm_run_rfl rd23 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨6121⟩, jumpiNT (by native_decide)]
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨1⟩, eq, push2 ⟨6102⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup1, push1 ⟨2⟩, eq, push2 ⟨6083⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨3⟩, eq, push2 ⟨6064⟩, jumpiT (by native_decide) jump_6064]
  have rd28 := evm_run_rfl rd27 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨7⟩, swap8, swap2, swap3, pop, pop, push2 ⟨5828⟩, jump jump_5828]
  have rd29 := evm_run_rfl rd28 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨4311⟩, jump jump_4311]
  have rd30 := evm_run_rfl rd29 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd31 := RD.runtimeMload rd30 (by old_decode) (by simp; omega)
  have rd32 := evm_run_rfl rd31 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd33 := evm_run_rfl rd32 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4328]
  have rd34 := evm_run_rfl rd33 with [jumpdest, add, and, swap8, dup7]
  have rd35 := RD.runtimeMstore rd34 (by old_decode) (by simp; omega)
  have rd36 := evm_run_rfl rd35 with [push1 ⟨128⟩, dup7, add]
  have rd37 := RD.runtimeMstore rd36 (by old_decode) (by simp; omega)
  have rd38 := evm_run_rfl rd37 with [push2 ⟨268⟩, jump jump_268]
  have rd39 := evm_run_rfl rd38 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4343]
  have rd40 := evm_run_rfl rd39 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd41 := RD.runtimeMstore rd40 (by old_decode) (by simp; omega)
  have rd42 := evm_run_rfl rd41 with [push1 ⟨64⟩, dup3, add]
  have rd43 := RD.runtimeMstore rd42 (by old_decode) (by simp; omega)
  have rd44 := evm_run_rfl rd43 with [add]
  have rd45 := RD.runtimeMstore rd44 (by old_decode) (by simp; omega)
  have rd46 := evm_run_rfl rd45 with [jump jump_8967]
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
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd46⟩


end Ripemd160Old
