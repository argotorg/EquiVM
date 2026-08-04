import Examples.Ripemd160Old.HashLeftInit

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

namespace Ripemd160Old

open Ripemd160

def oldLeftHelperStack (I : ExecutionEnv) (round : Nat)
    (t : List UInt256) : List UInt256 :=
  (hashScratchPtr I + ⟨512⟩) :: hashScratchPtr I ::
    UInt256.ofNat round :: ⟨8991⟩ :: t

/-- Memory transition performed by one old-runtime left round. -/
def oldLeftRoundCursor (c : RuntimeMemCursor) (messageBase : UInt256)
    (group round : Nat) : RuntimeMemCursor :=
  let lineBase := messageBase + ⟨512⟩
  runtimeRoundCursor c lineBase messageBase (UInt256.ofNat round)
    (leftWordRowWord group) (leftRotationRowWord group)
    (runtimeLeftF group (runtimeRoundB c lineBase) (runtimeRoundC c lineBase)
      (runtimeRoundD c lineBase)) (leftConstantWord group)

theorem runtime_leftRoundHelper_0 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I 0 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) 0 0).mem
      (oldLeftRoundCursor c (hashScratchPtr I) 0 0).aw
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
  have rd20 := evm_run_rfl rd19 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨2750⟩, jumpiT (by native_decide) jump_2750]
  have rd21 := evm_run_rfl rd20 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨11⟩, swap8, swap2, swap3, pop, pop, push2 ⟨2457⟩, jump jump_2457]
  have rd22 := evm_run_rfl rd21 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨494⟩, jump jump_494]
  have rd23 := evm_run_rfl rd22 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd24 := RD.runtimeMload rd23 (by old_decode) (by simp; omega)
  have rd25 := evm_run_rfl rd24 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd26 := evm_run_rfl rd25 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_511]
  have rd27 := evm_run_rfl rd26 with [jumpdest, add, and, swap8, dup7]
  have rd28 := RD.runtimeMstore rd27 (by old_decode) (by simp; omega)
  have rd29 := evm_run_rfl rd28 with [push1 ⟨128⟩, dup7, add]
  have rd30 := RD.runtimeMstore rd29 (by old_decode) (by simp; omega)
  have rd31 := evm_run_rfl rd30 with [push2 ⟨268⟩, jump jump_268]
  have rd32 := evm_run_rfl rd31 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_526]
  have rd33 := evm_run_rfl rd32 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd34 := RD.runtimeMstore rd33 (by old_decode) (by simp; omega)
  have rd35 := evm_run_rfl rd34 with [push1 ⟨64⟩, dup3, add]
  have rd36 := RD.runtimeMstore rd35 (by old_decode) (by simp; omega)
  have rd37 := evm_run_rfl rd36 with [add]
  have rd38 := RD.runtimeMstore rd37 (by old_decode) (by simp; omega)
  have rd39 := evm_run_rfl rd38 with [jump jump_8991]
  exact ⟨_, _, by
    simpa [oldLeftHelperStack, oldLeftRoundCursor, runtimeLeftRoundCursor,
      runtimeRoundPreludeCursor,
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


end Ripemd160Old
