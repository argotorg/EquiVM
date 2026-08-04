import Examples.Ripemd160Old.HashLines
import Examples.Precompiles.Ripemd160.HashWideRecombine

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

namespace Ripemd160Old

open Ripemd160

theorem runtime_recombine {cA σ I} {g : Sat256} {s0 : State}
    {c : RuntimeMemCursor} {rdata : ByteArray} {k C n block : Nat}
    {h : RuntimeChain} {left right : RuntimeLineState} {X : Fin 16 → UInt256}
    (hinv : RuntimeRightWideInvariant I c n X left right)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (rd8777 : RD runtimeBytecode I g s0 ⟨8777⟩
      (oldCompressionStack I block h) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8533⟩
      (oldBlockLoopStack I (UInt256.ofNat block + ⟨1⟩)
        (runtimeRecombineChain h left right))
      c.mem c.aw rdata (cA, σ) k' C' := by
  have hcover := hinv.activeCover hsmall
  have addrNat (m : UInt256) (hm : m.toNat ≤ 832) :
      (hashScratchPtr I + m).toNat = (hashScratchPtr I).toNat + m.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt]
    have hu := hashScratchPtr_add_uint I hsmall
    omega
  have awEq (m : UInt256) (hm : m.toNat ≤ 800) :
      runtimeMloadAw c.aw (hashScratchPtr I + m) = c.aw := by
    apply runtimeMloadAw_eq_of_covers_wide hinv.padded.awSmall
    · have hw := hashScratchPtr_add_wide I hsmall
      rw [show UInt256.size = 2 ^ 256 from by decide]
      rw [addrNat m (by omega)]
      norm_num at hw ⊢
      omega
    · rw [addrNat m (by omega)]
      omega
  have lv512 : runtimeMloadValue c.mem c.aw (hashScratchPtr I + ⟨512⟩) = left.a :=
    hinv.leftLine.1.load
  have lv544 : runtimeMloadValue c.mem c.aw (hashScratchPtr I + ⟨544⟩) = left.b := by
    rw [← show (⟨512⟩ : UInt256) + ⟨32⟩ = ⟨544⟩ by native_decide,
      ← u256_add_assoc]
    exact hinv.leftLine.2.1.load
  have lv576 : runtimeMloadValue c.mem c.aw (hashScratchPtr I + ⟨576⟩) = left.c := by
    rw [← show (⟨512⟩ : UInt256) + ⟨64⟩ = ⟨576⟩ by native_decide,
      ← u256_add_assoc]
    exact hinv.leftLine.2.2.1.load
  have lv608 : runtimeMloadValue c.mem c.aw (hashScratchPtr I + ⟨608⟩) = left.d := by
    rw [← show (⟨512⟩ : UInt256) + ⟨96⟩ = ⟨608⟩ by native_decide,
      ← u256_add_assoc]
    exact hinv.leftLine.2.2.2.1.load
  have lv640 : runtimeMloadValue c.mem c.aw (hashScratchPtr I + ⟨640⟩) = left.e := by
    rw [← show (⟨512⟩ : UInt256) + ⟨128⟩ = ⟨640⟩ by native_decide,
      ← u256_add_assoc]
    exact hinv.leftLine.2.2.2.2.load
  have rv672 : runtimeMloadValue c.mem c.aw (hashScratchPtr I + ⟨672⟩) = right.a :=
    hinv.rightLine.1.load
  have rv704 : runtimeMloadValue c.mem c.aw (hashScratchPtr I + ⟨704⟩) = right.b := by
    rw [← show (⟨672⟩ : UInt256) + ⟨32⟩ = ⟨704⟩ by native_decide,
      ← u256_add_assoc]
    exact hinv.rightLine.2.1.load
  have rv736 : runtimeMloadValue c.mem c.aw (hashScratchPtr I + ⟨736⟩) = right.c := by
    rw [← show (⟨672⟩ : UInt256) + ⟨64⟩ = ⟨736⟩ by native_decide,
      ← u256_add_assoc]
    exact hinv.rightLine.2.2.1.load
  have rv768 : runtimeMloadValue c.mem c.aw (hashScratchPtr I + ⟨768⟩) = right.d := by
    rw [← show (⟨672⟩ : UInt256) + ⟨96⟩ = ⟨768⟩ by native_decide,
      ← u256_add_assoc]
    exact hinv.rightLine.2.2.2.1.load
  have rv800 : runtimeMloadValue c.mem c.aw (hashScratchPtr I + ⟨800⟩) = right.e := by
    rw [← show (⟨672⟩ : UInt256) + ⟨128⟩ = ⟨800⟩ by native_decide,
      ← u256_add_assoc]
    exact hinv.rightLine.2.2.2.2.load
  simp only [oldCompressionStack] at rd8777
  have rd1p := evm_run_rfl rd8777 with [push2 ⟨512⟩, dup5, add]
  have rd1 := RD.runtimeMload rd1p (by old_decode) (by simp)
  rw [awEq ⟨512⟩ (by decide), lv512] at rd1
  have rd2p := evm_run_rfl rd1 with [swap1, push2 ⟨512⟩, dup6, add, push1 ⟨32⟩, add]
  have rd2 := RD.runtimeMload rd2p (by old_decode) (by simp)
  rw [show ⟨32⟩ + (hashScratchPtr I + ⟨512⟩) = hashScratchPtr I + ⟨544⟩ by
    rw [u256_add_comm ⟨32⟩, u256_add_assoc]; congr 1,
    awEq ⟨544⟩ (by decide), lv544] at rd2
  have rd3p := evm_run_rfl rd2 with [swap1, push2 ⟨512⟩, dup7, add, push1 ⟨64⟩, add]
  have rd3 := RD.runtimeMload rd3p (by old_decode) (by simp)
  rw [show ⟨64⟩ + (hashScratchPtr I + ⟨512⟩) = hashScratchPtr I + ⟨576⟩ by
    rw [u256_add_comm ⟨64⟩, u256_add_assoc]; congr 1,
    awEq ⟨576⟩ (by decide), lv576] at rd3
  have rd4p := evm_run_rfl rd3 with [swap3, push2 ⟨512⟩, dup8, add, push1 ⟨96⟩, add]
  have rd4 := RD.runtimeMload rd4p (by old_decode) (by simp)
  rw [show ⟨96⟩ + (hashScratchPtr I + ⟨512⟩) = hashScratchPtr I + ⟨608⟩ by
    rw [u256_add_comm ⟨96⟩, u256_add_assoc]; congr 1,
    awEq ⟨608⟩ (by decide), lv608] at rd4
  have rd5p := evm_run_rfl rd4 with [swap2, push2 ⟨512⟩, dup9, add, push1 ⟨128⟩, add]
  have rd5 := RD.runtimeMload rd5p (by old_decode) (by simp)
  rw [show ⟨128⟩ + (hashScratchPtr I + ⟨512⟩) = hashScratchPtr I + ⟨640⟩ by
    rw [u256_add_comm ⟨128⟩, u256_add_assoc]; congr 1,
    awEq ⟨640⟩ (by decide), lv640] at rd5
  have rd6p := evm_run_rfl rd5 with [push2 ⟨512⟩, dup10, add, push1 ⟨160⟩, add]
  have rd6 := RD.runtimeMload rd6p (by old_decode) (by simp)
  rw [show ⟨160⟩ + (hashScratchPtr I + ⟨512⟩) = hashScratchPtr I + ⟨672⟩ by
    rw [u256_add_comm ⟨160⟩, u256_add_assoc]; congr 1,
    awEq ⟨672⟩ (by decide), rv672] at rd6
  have rd7p := evm_run_rfl rd6 with [swap2, push2 ⟨512⟩, dup11, add,
    push1 ⟨160⟩, add, push1 ⟨32⟩, add]
  have rd7 := RD.runtimeMload rd7p (by old_decode) (by simp)
  rw [show ⟨32⟩ + (⟨160⟩ + (hashScratchPtr I + ⟨512⟩)) =
      hashScratchPtr I + ⟨704⟩ by
    rw [u256_add_comm ⟨32⟩, u256_add_comm ⟨160⟩,
      u256_add_assoc, u256_add_assoc]; congr 1,
    awEq ⟨704⟩ (by decide), rv704] at rd7
  have rd8p := evm_run_rfl rd7 with [swap5, push2 ⟨512⟩, dup12, add,
    push1 ⟨160⟩, add, push1 ⟨64⟩, add]
  have rd8 := RD.runtimeMload rd8p (by old_decode) (by simp)
  rw [show ⟨64⟩ + (⟨160⟩ + (hashScratchPtr I + ⟨512⟩)) =
      hashScratchPtr I + ⟨736⟩ by
    rw [u256_add_comm ⟨64⟩, u256_add_comm ⟨160⟩,
      u256_add_assoc, u256_add_assoc]; congr 1,
    awEq ⟨736⟩ (by decide), rv736] at rd8
  have rd9p := evm_run_rfl rd8 with [swap8, push2 ⟨512⟩, dup13, add,
    push1 ⟨160⟩, add, push1 ⟨96⟩, add]
  have rd9 := RD.runtimeMload rd9p (by old_decode) (by simp)
  rw [show ⟨96⟩ + (⟨160⟩ + (hashScratchPtr I + ⟨512⟩)) =
      hashScratchPtr I + ⟨768⟩ by
    rw [u256_add_comm ⟨96⟩, u256_add_comm ⟨160⟩,
      u256_add_assoc, u256_add_assoc]; congr 1,
    awEq ⟨768⟩ (by decide), rv768] at rd9
  have rd10p := evm_run_rfl rd9 with [swap1, push2 ⟨512⟩, dup14, add,
    push1 ⟨160⟩, add, push1 ⟨128⟩, add]
  have rd10 := RD.runtimeMload rd10p (by old_decode) (by simp)
  rw [show ⟨128⟩ + (⟨160⟩ + (hashScratchPtr I + ⟨512⟩)) =
      hashScratchPtr I + ⟨800⟩ by
    rw [u256_add_comm ⟨128⟩, u256_add_comm ⟨160⟩,
      u256_add_assoc, u256_add_assoc]; congr 1,
    awEq ⟨800⟩ (by decide), rv800] at rd10
  have rd8533 := evm_run_rfl rd10 with [
    swap4, add, add, push4 ⟨4294967295⟩, and, swap13,
    add, add, push4 ⟨4294967295⟩, and, swap14,
    add, add, push4 ⟨4294967295⟩, and, swap11,
    add, add, push4 ⟨4294967295⟩, and, swap8,
    add, add, push4 ⟨4294967295⟩, and, swap5,
    swap4, push1 ⟨1⟩, push1 ⟨64⟩, swap2, add,
    swap4, swap3, swap2, swap1, pop,
    push2 ⟨8533⟩, jump jump_8533 ]
  exact ⟨_, _, by
    simpa [oldBlockLoopStack, runtimeRecombineChain, mask32Word,
      u256_add_comm, u256_add_assoc] using rd8533⟩

end Ripemd160Old
