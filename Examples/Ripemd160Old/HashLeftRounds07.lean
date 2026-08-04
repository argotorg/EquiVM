import Examples.Ripemd160Old.HashLeftRound0

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000
namespace Ripemd160Old
open Ripemd160

theorem runtime_leftRoundHelper_60 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 60 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 3 12).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 3 12).aw
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
  have rd31 := evm_run_rfl rd30 with [dup1, push1 ⟨11⟩, eq, push2 ⟨3255⟩, jumpiNT (by native_decide)]
  have rd32 := evm_run_rfl rd31 with [dup1, push1 ⟨12⟩, eq, push2 ⟨3244⟩, jumpiT (by native_decide) jump_3244]
  have rd33 := evm_run_rfl rd32 with [jumpdest, pop, swap1, pop, push1 ⟨14⟩, swap1, push2 ⟨3207⟩, jump jump_3207]
  have rd34 := evm_run_rfl rd33 with [jumpdest, push2 ⟨444⟩, jump jump_444]
  have rd35 := evm_run_rfl rd34 with [jumpdest, push1 ⟨63⟩, dup2, gt, push2 ⟨2769⟩, jumpiNT (by native_decide)]
  have rd36 := evm_run_rfl rd35 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiNT (by native_decide)]
  have rd37 := evm_run_rfl rd36 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1877⟩, jumpiNT (by native_decide)]
  have rd38 := evm_run_rfl rd37 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1431⟩, jumpiNT (by native_decide)]
  have rd39 := evm_run_rfl rd38 with [dup1, push1 ⟨3⟩, eq, push2 ⟨985⟩, jumpiT (by native_decide) jump_985]
  have rd40 := evm_run_rfl rd39 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨1412⟩, jumpiNT (by native_decide)]
  have rd41 := evm_run_rfl rd40 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1393⟩, jumpiNT (by native_decide)]
  have rd42 := evm_run_rfl rd41 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1374⟩, jumpiNT (by native_decide)]
  have rd43 := evm_run_rfl rd42 with [dup1, push1 ⟨3⟩, eq, push2 ⟨1355⟩, jumpiNT (by native_decide)]
  have rd44 := evm_run_rfl rd43 with [dup1, push1 ⟨4⟩, eq, push2 ⟨1336⟩, jumpiNT (by native_decide)]
  have rd45 := evm_run_rfl rd44 with [dup1, push1 ⟨5⟩, eq, push2 ⟨1317⟩, jumpiNT (by native_decide)]
  have rd46 := evm_run_rfl rd45 with [dup1, push1 ⟨6⟩, eq, push2 ⟨1298⟩, jumpiNT (by native_decide)]
  have rd47 := evm_run_rfl rd46 with [dup1, push1 ⟨7⟩, eq, push2 ⟨1279⟩, jumpiNT (by native_decide)]
  have rd48 := evm_run_rfl rd47 with [dup1, push1 ⟨8⟩, eq, push2 ⟨1260⟩, jumpiNT (by native_decide)]
  have rd49 := evm_run_rfl rd48 with [dup1, push1 ⟨9⟩, eq, push2 ⟨1241⟩, jumpiNT (by native_decide)]
  have rd50 := evm_run_rfl rd49 with [dup1, dup15, eq, push2 ⟨1222⟩, jumpiNT (by native_decide)]
  have rd51 := evm_run_rfl rd50 with [dup1, push1 ⟨11⟩, eq, push2 ⟨1203⟩, jumpiNT (by native_decide)]
  have rd52 := evm_run_rfl rd51 with [dup1, push1 ⟨12⟩, eq, push2 ⟨1184⟩, jumpiT (by native_decide) jump_1184]
  have rd53 := evm_run_rfl rd52 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨8⟩, swap8, swap2, swap3, pop, pop, push2 ⟨1119⟩, jump jump_1119]
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

theorem runtime_leftRoundHelper_61 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 61 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 3 13).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 3 13).aw
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
  have rd31 := evm_run_rfl rd30 with [dup1, push1 ⟨11⟩, eq, push2 ⟨3255⟩, jumpiNT (by native_decide)]
  have rd32 := evm_run_rfl rd31 with [dup1, push1 ⟨12⟩, eq, push2 ⟨3244⟩, jumpiNT (by native_decide)]
  have rd33 := evm_run_rfl rd32 with [dup1, push1 ⟨13⟩, eq, push2 ⟨3233⟩, jumpiT (by native_decide) jump_3233]
  have rd34 := evm_run_rfl rd33 with [jumpdest, pop, swap1, pop, push1 ⟨5⟩, swap1, push2 ⟨3207⟩, jump jump_3207]
  have rd35 := evm_run_rfl rd34 with [jumpdest, push2 ⟨444⟩, jump jump_444]
  have rd36 := evm_run_rfl rd35 with [jumpdest, push1 ⟨63⟩, dup2, gt, push2 ⟨2769⟩, jumpiNT (by native_decide)]
  have rd37 := evm_run_rfl rd36 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiNT (by native_decide)]
  have rd38 := evm_run_rfl rd37 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1877⟩, jumpiNT (by native_decide)]
  have rd39 := evm_run_rfl rd38 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1431⟩, jumpiNT (by native_decide)]
  have rd40 := evm_run_rfl rd39 with [dup1, push1 ⟨3⟩, eq, push2 ⟨985⟩, jumpiT (by native_decide) jump_985]
  have rd41 := evm_run_rfl rd40 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨1412⟩, jumpiNT (by native_decide)]
  have rd42 := evm_run_rfl rd41 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1393⟩, jumpiNT (by native_decide)]
  have rd43 := evm_run_rfl rd42 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1374⟩, jumpiNT (by native_decide)]
  have rd44 := evm_run_rfl rd43 with [dup1, push1 ⟨3⟩, eq, push2 ⟨1355⟩, jumpiNT (by native_decide)]
  have rd45 := evm_run_rfl rd44 with [dup1, push1 ⟨4⟩, eq, push2 ⟨1336⟩, jumpiNT (by native_decide)]
  have rd46 := evm_run_rfl rd45 with [dup1, push1 ⟨5⟩, eq, push2 ⟨1317⟩, jumpiNT (by native_decide)]
  have rd47 := evm_run_rfl rd46 with [dup1, push1 ⟨6⟩, eq, push2 ⟨1298⟩, jumpiNT (by native_decide)]
  have rd48 := evm_run_rfl rd47 with [dup1, push1 ⟨7⟩, eq, push2 ⟨1279⟩, jumpiNT (by native_decide)]
  have rd49 := evm_run_rfl rd48 with [dup1, push1 ⟨8⟩, eq, push2 ⟨1260⟩, jumpiNT (by native_decide)]
  have rd50 := evm_run_rfl rd49 with [dup1, push1 ⟨9⟩, eq, push2 ⟨1241⟩, jumpiNT (by native_decide)]
  have rd51 := evm_run_rfl rd50 with [dup1, dup15, eq, push2 ⟨1222⟩, jumpiNT (by native_decide)]
  have rd52 := evm_run_rfl rd51 with [dup1, push1 ⟨11⟩, eq, push2 ⟨1203⟩, jumpiNT (by native_decide)]
  have rd53 := evm_run_rfl rd52 with [dup1, push1 ⟨12⟩, eq, push2 ⟨1184⟩, jumpiNT (by native_decide)]
  have rd54 := evm_run_rfl rd53 with [dup1, push1 ⟨13⟩, eq, push2 ⟨1165⟩, jumpiT (by native_decide) jump_1165]
  have rd55 := evm_run_rfl rd54 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨6⟩, swap8, swap2, swap3, pop, pop, push2 ⟨1119⟩, jump jump_1119]
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

theorem runtime_leftRoundHelper_62 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 62 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 3 14).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 3 14).aw
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
  have rd31 := evm_run_rfl rd30 with [dup1, push1 ⟨11⟩, eq, push2 ⟨3255⟩, jumpiNT (by native_decide)]
  have rd32 := evm_run_rfl rd31 with [dup1, push1 ⟨12⟩, eq, push2 ⟨3244⟩, jumpiNT (by native_decide)]
  have rd33 := evm_run_rfl rd32 with [dup1, push1 ⟨13⟩, eq, push2 ⟨3233⟩, jumpiNT (by native_decide)]
  have rd34 := evm_run_rfl rd33 with [dup1, push1 ⟨14⟩, eq, push2 ⟨3222⟩, jumpiT (by native_decide) jump_3222]
  have rd35 := evm_run_rfl rd34 with [jumpdest, pop, swap1, pop, push1 ⟨6⟩, swap1, push2 ⟨3207⟩, jump jump_3207]
  have rd36 := evm_run_rfl rd35 with [jumpdest, push2 ⟨444⟩, jump jump_444]
  have rd37 := evm_run_rfl rd36 with [jumpdest, push1 ⟨63⟩, dup2, gt, push2 ⟨2769⟩, jumpiNT (by native_decide)]
  have rd38 := evm_run_rfl rd37 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiNT (by native_decide)]
  have rd39 := evm_run_rfl rd38 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1877⟩, jumpiNT (by native_decide)]
  have rd40 := evm_run_rfl rd39 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1431⟩, jumpiNT (by native_decide)]
  have rd41 := evm_run_rfl rd40 with [dup1, push1 ⟨3⟩, eq, push2 ⟨985⟩, jumpiT (by native_decide) jump_985]
  have rd42 := evm_run_rfl rd41 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨1412⟩, jumpiNT (by native_decide)]
  have rd43 := evm_run_rfl rd42 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1393⟩, jumpiNT (by native_decide)]
  have rd44 := evm_run_rfl rd43 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1374⟩, jumpiNT (by native_decide)]
  have rd45 := evm_run_rfl rd44 with [dup1, push1 ⟨3⟩, eq, push2 ⟨1355⟩, jumpiNT (by native_decide)]
  have rd46 := evm_run_rfl rd45 with [dup1, push1 ⟨4⟩, eq, push2 ⟨1336⟩, jumpiNT (by native_decide)]
  have rd47 := evm_run_rfl rd46 with [dup1, push1 ⟨5⟩, eq, push2 ⟨1317⟩, jumpiNT (by native_decide)]
  have rd48 := evm_run_rfl rd47 with [dup1, push1 ⟨6⟩, eq, push2 ⟨1298⟩, jumpiNT (by native_decide)]
  have rd49 := evm_run_rfl rd48 with [dup1, push1 ⟨7⟩, eq, push2 ⟨1279⟩, jumpiNT (by native_decide)]
  have rd50 := evm_run_rfl rd49 with [dup1, push1 ⟨8⟩, eq, push2 ⟨1260⟩, jumpiNT (by native_decide)]
  have rd51 := evm_run_rfl rd50 with [dup1, push1 ⟨9⟩, eq, push2 ⟨1241⟩, jumpiNT (by native_decide)]
  have rd52 := evm_run_rfl rd51 with [dup1, dup15, eq, push2 ⟨1222⟩, jumpiNT (by native_decide)]
  have rd53 := evm_run_rfl rd52 with [dup1, push1 ⟨11⟩, eq, push2 ⟨1203⟩, jumpiNT (by native_decide)]
  have rd54 := evm_run_rfl rd53 with [dup1, push1 ⟨12⟩, eq, push2 ⟨1184⟩, jumpiNT (by native_decide)]
  have rd55 := evm_run_rfl rd54 with [dup1, push1 ⟨13⟩, eq, push2 ⟨1165⟩, jumpiNT (by native_decide)]
  have rd56 := evm_run_rfl rd55 with [dup1, push1 ⟨14⟩, eq, push2 ⟨1146⟩, jumpiT (by native_decide) jump_1146]
  have rd57 := evm_run_rfl rd56 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨5⟩, swap8, swap2, swap3, pop, pop, push2 ⟨1119⟩, jump jump_1119]
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

theorem runtime_leftRoundHelper_63 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 63 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 3 15).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 3 15).aw
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
  have rd31 := evm_run_rfl rd30 with [dup1, push1 ⟨11⟩, eq, push2 ⟨3255⟩, jumpiNT (by native_decide)]
  have rd32 := evm_run_rfl rd31 with [dup1, push1 ⟨12⟩, eq, push2 ⟨3244⟩, jumpiNT (by native_decide)]
  have rd33 := evm_run_rfl rd32 with [dup1, push1 ⟨13⟩, eq, push2 ⟨3233⟩, jumpiNT (by native_decide)]
  have rd34 := evm_run_rfl rd33 with [dup1, push1 ⟨14⟩, eq, push2 ⟨3222⟩, jumpiNT (by native_decide)]
  have rd35 := evm_run_rfl rd34 with [push1 ⟨15⟩, eq, push2 ⟨3212⟩, jumpiT (by native_decide) jump_3212]
  have rd36 := evm_run_rfl rd35 with [jumpdest, swap1, pop, push1 ⟨2⟩, swap1, push2 ⟨3207⟩, jump jump_3207]
  have rd37 := evm_run_rfl rd36 with [jumpdest, push2 ⟨444⟩, jump jump_444]
  have rd38 := evm_run_rfl rd37 with [jumpdest, push1 ⟨63⟩, dup2, gt, push2 ⟨2769⟩, jumpiNT (by native_decide)]
  have rd39 := evm_run_rfl rd38 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiNT (by native_decide)]
  have rd40 := evm_run_rfl rd39 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1877⟩, jumpiNT (by native_decide)]
  have rd41 := evm_run_rfl rd40 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1431⟩, jumpiNT (by native_decide)]
  have rd42 := evm_run_rfl rd41 with [dup1, push1 ⟨3⟩, eq, push2 ⟨985⟩, jumpiT (by native_decide) jump_985]
  have rd43 := evm_run_rfl rd42 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨1412⟩, jumpiNT (by native_decide)]
  have rd44 := evm_run_rfl rd43 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1393⟩, jumpiNT (by native_decide)]
  have rd45 := evm_run_rfl rd44 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1374⟩, jumpiNT (by native_decide)]
  have rd46 := evm_run_rfl rd45 with [dup1, push1 ⟨3⟩, eq, push2 ⟨1355⟩, jumpiNT (by native_decide)]
  have rd47 := evm_run_rfl rd46 with [dup1, push1 ⟨4⟩, eq, push2 ⟨1336⟩, jumpiNT (by native_decide)]
  have rd48 := evm_run_rfl rd47 with [dup1, push1 ⟨5⟩, eq, push2 ⟨1317⟩, jumpiNT (by native_decide)]
  have rd49 := evm_run_rfl rd48 with [dup1, push1 ⟨6⟩, eq, push2 ⟨1298⟩, jumpiNT (by native_decide)]
  have rd50 := evm_run_rfl rd49 with [dup1, push1 ⟨7⟩, eq, push2 ⟨1279⟩, jumpiNT (by native_decide)]
  have rd51 := evm_run_rfl rd50 with [dup1, push1 ⟨8⟩, eq, push2 ⟨1260⟩, jumpiNT (by native_decide)]
  have rd52 := evm_run_rfl rd51 with [dup1, push1 ⟨9⟩, eq, push2 ⟨1241⟩, jumpiNT (by native_decide)]
  have rd53 := evm_run_rfl rd52 with [dup1, dup15, eq, push2 ⟨1222⟩, jumpiNT (by native_decide)]
  have rd54 := evm_run_rfl rd53 with [dup1, push1 ⟨11⟩, eq, push2 ⟨1203⟩, jumpiNT (by native_decide)]
  have rd55 := evm_run_rfl rd54 with [dup1, push1 ⟨12⟩, eq, push2 ⟨1184⟩, jumpiNT (by native_decide)]
  have rd56 := evm_run_rfl rd55 with [dup1, push1 ⟨13⟩, eq, push2 ⟨1165⟩, jumpiNT (by native_decide)]
  have rd57 := evm_run_rfl rd56 with [dup1, push1 ⟨14⟩, eq, push2 ⟨1146⟩, jumpiNT (by native_decide)]
  have rd58 := evm_run_rfl rd57 with [push1 ⟨15⟩, eq, push2 ⟨1128⟩, jumpiT (by native_decide) jump_1128]
  have rd59 := evm_run_rfl rd58 with [jumpdest, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨12⟩, swap8, swap2, swap3, pop, pop, push2 ⟨1119⟩, jump jump_1119]
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

theorem runtime_leftRoundHelper_64 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 64 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 4 0).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 4 0).aw
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
  have rd22 := evm_run_rfl rd21 with [jumpdest, push1 ⟨64⟩, dup2, sub, dup1, push0, eq, push2 ⟨3066⟩, jumpiT (by native_decide) jump_3066]
  have rd23 := evm_run_rfl rd22 with [jumpdest, pop, swap1, pop, push1 ⟨4⟩, swap1, push2 ⟨2899⟩, jump jump_2899]
  have rd24 := evm_run_rfl rd23 with [jumpdest, push2 ⟨453⟩, jump jump_453]
  have rd25 := evm_run_rfl rd24 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiNT (by native_decide)]
  have rd26 := evm_run_rfl rd25 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1877⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1431⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨3⟩, eq, push2 ⟨985⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [push1 ⟨4⟩, eq, push2 ⟨540⟩, jumpiT (by native_decide) jump_540]
  have rd30 := evm_run_rfl rd29 with [jumpdest, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨966⟩, jumpiT (by native_decide) jump_966]
  have rd31 := evm_run_rfl rd30 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨9⟩, swap8, swap2, swap3, pop, pop, push2 ⟨673⟩, jump jump_673]
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

theorem runtime_leftRoundHelper_65 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 65 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 4 1).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 4 1).aw
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
  have rd23 := evm_run_rfl rd22 with [dup1, push1 ⟨1⟩, eq, push2 ⟨3056⟩, jumpiT (by native_decide) jump_3056]
  have rd24 := evm_run_rfl rd23 with [jumpdest, pop, swap1, pop, push0, swap1, push2 ⟨2899⟩, jump jump_2899]
  have rd25 := evm_run_rfl rd24 with [jumpdest, push2 ⟨453⟩, jump jump_453]
  have rd26 := evm_run_rfl rd25 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiNT (by native_decide)]
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1877⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1431⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [dup1, push1 ⟨3⟩, eq, push2 ⟨985⟩, jumpiNT (by native_decide)]
  have rd30 := evm_run_rfl rd29 with [push1 ⟨4⟩, eq, push2 ⟨540⟩, jumpiT (by native_decide) jump_540]
  have rd31 := evm_run_rfl rd30 with [jumpdest, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨966⟩, jumpiNT (by native_decide)]
  have rd32 := evm_run_rfl rd31 with [dup1, push1 ⟨1⟩, eq, push2 ⟨947⟩, jumpiT (by native_decide) jump_947]
  have rd33 := evm_run_rfl rd32 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨15⟩, swap8, swap2, swap3, pop, pop, push2 ⟨673⟩, jump jump_673]
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

theorem runtime_leftRoundHelper_66 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 66 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 4 2).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 4 2).aw
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
  have rd24 := evm_run_rfl rd23 with [dup1, push1 ⟨2⟩, eq, push2 ⟨3045⟩, jumpiT (by native_decide) jump_3045]
  have rd25 := evm_run_rfl rd24 with [jumpdest, pop, swap1, pop, push1 ⟨5⟩, swap1, push2 ⟨2899⟩, jump jump_2899]
  have rd26 := evm_run_rfl rd25 with [jumpdest, push2 ⟨453⟩, jump jump_453]
  have rd27 := evm_run_rfl rd26 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiNT (by native_decide)]
  have rd28 := evm_run_rfl rd27 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1877⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1431⟩, jumpiNT (by native_decide)]
  have rd30 := evm_run_rfl rd29 with [dup1, push1 ⟨3⟩, eq, push2 ⟨985⟩, jumpiNT (by native_decide)]
  have rd31 := evm_run_rfl rd30 with [push1 ⟨4⟩, eq, push2 ⟨540⟩, jumpiT (by native_decide) jump_540]
  have rd32 := evm_run_rfl rd31 with [jumpdest, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨966⟩, jumpiNT (by native_decide)]
  have rd33 := evm_run_rfl rd32 with [dup1, push1 ⟨1⟩, eq, push2 ⟨947⟩, jumpiNT (by native_decide)]
  have rd34 := evm_run_rfl rd33 with [dup1, push1 ⟨2⟩, eq, push2 ⟨928⟩, jumpiT (by native_decide) jump_928]
  have rd35 := evm_run_rfl rd34 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨5⟩, swap8, swap2, swap3, pop, pop, push2 ⟨673⟩, jump jump_673]
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

theorem runtime_leftRoundHelper_67 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 67 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 4 3).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 4 3).aw
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
  have rd25 := evm_run_rfl rd24 with [dup1, push1 ⟨3⟩, eq, push2 ⟨3034⟩, jumpiT (by native_decide) jump_3034]
  have rd26 := evm_run_rfl rd25 with [jumpdest, pop, swap1, pop, push1 ⟨9⟩, swap1, push2 ⟨2899⟩, jump jump_2899]
  have rd27 := evm_run_rfl rd26 with [jumpdest, push2 ⟨453⟩, jump jump_453]
  have rd28 := evm_run_rfl rd27 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiNT (by native_decide)]
  have rd29 := evm_run_rfl rd28 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1877⟩, jumpiNT (by native_decide)]
  have rd30 := evm_run_rfl rd29 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1431⟩, jumpiNT (by native_decide)]
  have rd31 := evm_run_rfl rd30 with [dup1, push1 ⟨3⟩, eq, push2 ⟨985⟩, jumpiNT (by native_decide)]
  have rd32 := evm_run_rfl rd31 with [push1 ⟨4⟩, eq, push2 ⟨540⟩, jumpiT (by native_decide) jump_540]
  have rd33 := evm_run_rfl rd32 with [jumpdest, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨966⟩, jumpiNT (by native_decide)]
  have rd34 := evm_run_rfl rd33 with [dup1, push1 ⟨1⟩, eq, push2 ⟨947⟩, jumpiNT (by native_decide)]
  have rd35 := evm_run_rfl rd34 with [dup1, push1 ⟨2⟩, eq, push2 ⟨928⟩, jumpiNT (by native_decide)]
  have rd36 := evm_run_rfl rd35 with [dup1, push1 ⟨3⟩, eq, push2 ⟨909⟩, jumpiT (by native_decide) jump_909]
  have rd37 := evm_run_rfl rd36 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨11⟩, swap8, swap2, swap3, pop, pop, push2 ⟨673⟩, jump jump_673]
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

theorem runtime_leftRoundHelper_68 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 68 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 4 4).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 4 4).aw
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
  have rd26 := evm_run_rfl rd25 with [dup1, push1 ⟨4⟩, eq, push2 ⟨3023⟩, jumpiT (by native_decide) jump_3023]
  have rd27 := evm_run_rfl rd26 with [jumpdest, pop, swap1, pop, push1 ⟨7⟩, swap1, push2 ⟨2899⟩, jump jump_2899]
  have rd28 := evm_run_rfl rd27 with [jumpdest, push2 ⟨453⟩, jump jump_453]
  have rd29 := evm_run_rfl rd28 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiNT (by native_decide)]
  have rd30 := evm_run_rfl rd29 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1877⟩, jumpiNT (by native_decide)]
  have rd31 := evm_run_rfl rd30 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1431⟩, jumpiNT (by native_decide)]
  have rd32 := evm_run_rfl rd31 with [dup1, push1 ⟨3⟩, eq, push2 ⟨985⟩, jumpiNT (by native_decide)]
  have rd33 := evm_run_rfl rd32 with [push1 ⟨4⟩, eq, push2 ⟨540⟩, jumpiT (by native_decide) jump_540]
  have rd34 := evm_run_rfl rd33 with [jumpdest, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨966⟩, jumpiNT (by native_decide)]
  have rd35 := evm_run_rfl rd34 with [dup1, push1 ⟨1⟩, eq, push2 ⟨947⟩, jumpiNT (by native_decide)]
  have rd36 := evm_run_rfl rd35 with [dup1, push1 ⟨2⟩, eq, push2 ⟨928⟩, jumpiNT (by native_decide)]
  have rd37 := evm_run_rfl rd36 with [dup1, push1 ⟨3⟩, eq, push2 ⟨909⟩, jumpiNT (by native_decide)]
  have rd38 := evm_run_rfl rd37 with [dup1, push1 ⟨4⟩, eq, push2 ⟨890⟩, jumpiT (by native_decide) jump_890]
  have rd39 := evm_run_rfl rd38 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨6⟩, swap8, swap2, swap3, pop, pop, push2 ⟨673⟩, jump jump_673]
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

theorem runtime_leftRoundHelper_69 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 69 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 4 5).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 4 5).aw
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
  have rd27 := evm_run_rfl rd26 with [dup1, push1 ⟨5⟩, eq, push2 ⟨3012⟩, jumpiT (by native_decide) jump_3012]
  have rd28 := evm_run_rfl rd27 with [jumpdest, pop, swap1, pop, push1 ⟨12⟩, swap1, push2 ⟨2899⟩, jump jump_2899]
  have rd29 := evm_run_rfl rd28 with [jumpdest, push2 ⟨453⟩, jump jump_453]
  have rd30 := evm_run_rfl rd29 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨2323⟩, jumpiNT (by native_decide)]
  have rd31 := evm_run_rfl rd30 with [dup1, push1 ⟨1⟩, eq, push2 ⟨1877⟩, jumpiNT (by native_decide)]
  have rd32 := evm_run_rfl rd31 with [dup1, push1 ⟨2⟩, eq, push2 ⟨1431⟩, jumpiNT (by native_decide)]
  have rd33 := evm_run_rfl rd32 with [dup1, push1 ⟨3⟩, eq, push2 ⟨985⟩, jumpiNT (by native_decide)]
  have rd34 := evm_run_rfl rd33 with [push1 ⟨4⟩, eq, push2 ⟨540⟩, jumpiT (by native_decide) jump_540]
  have rd35 := evm_run_rfl rd34 with [jumpdest, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨966⟩, jumpiNT (by native_decide)]
  have rd36 := evm_run_rfl rd35 with [dup1, push1 ⟨1⟩, eq, push2 ⟨947⟩, jumpiNT (by native_decide)]
  have rd37 := evm_run_rfl rd36 with [dup1, push1 ⟨2⟩, eq, push2 ⟨928⟩, jumpiNT (by native_decide)]
  have rd38 := evm_run_rfl rd37 with [dup1, push1 ⟨3⟩, eq, push2 ⟨909⟩, jumpiNT (by native_decide)]
  have rd39 := evm_run_rfl rd38 with [dup1, push1 ⟨4⟩, eq, push2 ⟨890⟩, jumpiNT (by native_decide)]
  have rd40 := evm_run_rfl rd39 with [dup1, push1 ⟨5⟩, eq, push2 ⟨871⟩, jumpiT (by native_decide) jump_871]
  have rd41 := evm_run_rfl rd40 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨8⟩, swap8, swap2, swap3, pop, pop, push2 ⟨673⟩, jump jump_673]
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


end Ripemd160Old
