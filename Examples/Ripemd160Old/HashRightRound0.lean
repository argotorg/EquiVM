import Examples.Ripemd160Old.HashLeftRound0

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

namespace Ripemd160Old

open Ripemd160

def oldRightHelperStack (I : ExecutionEnv) (round : Nat)
    (t : List UInt256) : List UInt256 :=
  (hashScratchPtr I + ⟨672⟩) :: hashScratchPtr I ::
    UInt256.ofNat round :: ⟨8967⟩ :: t

/-- Memory transition performed by one old-runtime right round. -/
def oldRightRoundCursor (c : RuntimeMemCursor) (messageBase : UInt256)
    (group round : Nat) : RuntimeMemCursor :=
  let lineBase := messageBase + ⟨672⟩
  runtimeRoundCursor c lineBase messageBase (UInt256.ofNat round)
    (rightWordRowWord group) (rightRotationRowWord group)
    (runtimeRightF group (runtimeRoundB c lineBase) (runtimeRoundC c lineBase)
      (runtimeRoundD c lineBase)) (rightConstantWord group)

theorem runtime_rightRoundHelper_0 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I 0 t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) 0 0).mem
      (oldRightRoundCursor c (hashScratchPtr I) 0 0).aw
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
  have rd14 := evm_run_rfl rd13 with [jumpdest, pop, push1 ⟨16⟩, dup2, mod, dup1, push0, eq, push2 ⟨8119⟩, jumpiT (by native_decide) jump_8119]
  have rd15 := evm_run_rfl rd14 with [jumpdest, pop, swap1, pop, push1 ⟨5⟩, swap1, push2 ⟨7952⟩, jump jump_7952]
  have rd16 := evm_run_rfl rd15 with [jumpdest, push2 ⟨4270⟩, jump jump_4270]
  have rd17 := evm_run_rfl rd16 with [jumpdest, push0, swap9, dup1, push0, eq, push2 ⟨6140⟩, jumpiT (by native_decide) jump_6140]
  have rd18 := evm_run_rfl rd17 with [jumpdest, pop, push1 ⟨16⟩, swap2, swap3, swap4, pop, mod, dup1, push0, eq, push2 ⟨6567⟩, jumpiT (by native_decide) jump_6567]
  have rd19 := evm_run_rfl rd18 with [jumpdest, pop, swap6, pop, dup16, swap1, dup6, swap2, push1 ⟨8⟩, swap8, swap2, swap3, pop, pop, push2 ⟨6274⟩, jump jump_6274]
  have rd20 := evm_run_rfl rd19 with [jumpdest, swap1, dup6, swap2, push0, push2 ⟨4311⟩, jump jump_4311]
  have rd21 := evm_run_rfl rd20 with [jumpdest, pop, push1 ⟨32⟩, mul, add]
  have rd22 := RD.runtimeMload rd21 (by old_decode) (by simp; omega)
  have rd23 := evm_run_rfl rd22 with [swap3, and, add, add, add, and, push2 ⟨268⟩, jump jump_268]
  have rd24 := evm_run_rfl rd23 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4328]
  have rd25 := evm_run_rfl rd24 with [jumpdest, add, and, swap8, dup7]
  have rd26 := RD.runtimeMstore rd25 (by old_decode) (by simp; omega)
  have rd27 := evm_run_rfl rd26 with [push1 ⟨128⟩, dup7, add]
  have rd28 := RD.runtimeMstore rd27 (by old_decode) (by simp; omega)
  have rd29 := evm_run_rfl rd28 with [push2 ⟨268⟩, jump jump_268]
  have rd30 := evm_run_rfl rd29 with [jumpdest, swap1, push4 ⟨4294967295⟩, swap2, dup1, dup3, push1 ⟨32⟩, sub, shr, swap2, shl, or, and, swap1, jump jump_4343]
  have rd31 := evm_run_rfl rd30 with [jumpdest, push1 ⟨96⟩, dup4, add]
  have rd32 := RD.runtimeMstore rd31 (by old_decode) (by simp; omega)
  have rd33 := evm_run_rfl rd32 with [push1 ⟨64⟩, dup3, add]
  have rd34 := RD.runtimeMstore rd33 (by old_decode) (by simp; omega)
  have rd35 := evm_run_rfl rd34 with [add]
  have rd36 := RD.runtimeMstore rd35 (by old_decode) (by simp; omega)
  have rd37 := evm_run_rfl rd36 with [jump jump_8967]
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
      u256_add_comm, u256_land_comm, u256_lor_comm] using rd37⟩


end Ripemd160Old
