import Examples.Ripemd160Old.HashRoundDispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

namespace Ripemd160Old

open Ripemd160

theorem runtime_leftLoopBody {cA gh bl σ σ₀ A I} {g : Sat256}
    {block round : Nat} {h : RuntimeChain} {c : RuntimeMemCursor} {k C : Nat}
    (hround : round < 80)
    (rd8694 : RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8694⟩ (oldLeftLoopStack I block round h)
      c.mem c.aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8694⟩ (oldLeftLoopStack I block (round + 1) h)
      (oldLeftRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).mem
      (oldLeftRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).aw
      ByteArray.empty (cA, σ) k' C' := by
  simp only [oldLeftLoopStack, oldCompressionStack] at rd8694
  have hlt : UInt256.lt (UInt256.ofNat round) ⟨80⟩ = ⟨1⟩ := by
    apply ult_one
    rw [ulit_toNat' round (lt_trans hround (by decide)),
      show (⟨80⟩ : UInt256).toNat = 80 from by decide]
    exact hround
  have rd8973 := evm_run_rfl rd8694 with [
    jumpdest, push1 ⟨80⟩, dup2, lt, push2 ⟨8973⟩,
    jumpiT (by rw [hlt]; decide) jump_8973 ]
  have rd288 := evm_run_rfl rd8973 with [
    jumpdest, dup1, push2 ⟨8991⟩, push1 ⟨1⟩, swap3, dup8,
    push2 ⟨512⟩, dup2, add, push2 ⟨288⟩, jump jump_288 ]
  obtain ⟨_, _, rd8991⟩ := runtime_leftRoundHelper
    (t := UInt256.ofNat round :: ⟨1⟩ :: oldCompressionStack I block h)
    hround (by simp [oldCompressionStack])
    (by simpa [oldLeftHelperStack, oldCompressionStack] using rd288)
  simp only [oldCompressionStack] at rd8991
  have rdNext := evm_run_rfl rd8991 with [
    jumpdest, add, push2 ⟨8694⟩, jump jump_8694 ]
  exact ⟨_, _, by
    simpa [oldLeftLoopStack, oldCompressionStack, u256_one_add_ofNat,
      u256_add_comm] using rdNext⟩

theorem runtime_leftLoop {cA gh bl σ σ₀ A I} {g : Sat256}
    {block rounds : Nat} {h : RuntimeChain} {initial : RuntimeMemCursor} {k C : Nat}
    (hrounds : rounds ≤ 80)
    (rd8694 : RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8694⟩ (oldLeftLoopStack I block 0 h)
      initial.mem initial.aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8694⟩ (oldLeftLoopStack I block rounds h)
      (oldLeftLineCursor initial (hashScratchPtr I) rounds).mem
      (oldLeftLineCursor initial (hashScratchPtr I) rounds).aw
      ByteArray.empty (cA, σ) k' C' := by
  induction rounds with
  | zero => exact ⟨_, _, by simpa [oldLeftLineCursor] using rd8694⟩
  | succ round ih =>
      obtain ⟨_, _, rdRound⟩ := ih (by omega)
      obtain ⟨_, _, rdNext⟩ := runtime_leftLoopBody (by omega) rdRound
      exact ⟨_, _, by simpa [oldLeftLineCursor] using rdNext⟩

theorem runtime_leftLoopExit {cA gh bl σ σ₀ A I} {g : Sat256}
    {block : Nat} {h : RuntimeChain} {c : RuntimeMemCursor} {k C : Nat}
    (rd8694 : RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8694⟩ (oldLeftLoopStack I block 80 h)
      c.mem c.aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8704⟩ (oldCompressionStack I block h)
      c.mem c.aw ByteArray.empty (cA, σ) k' C' := by
  simp only [oldLeftLoopStack, oldCompressionStack] at rd8694
  have rd8704 := evm_run_rfl rd8694 with [
    jumpdest, push1 ⟨80⟩, dup2, lt, push2 ⟨8973⟩,
    jumpiNT (by native_decide), pop ]
  exact ⟨_, _, by simpa [oldCompressionStack] using rd8704⟩

def oldRightLoopStack (I : ExecutionEnv) (block round : Nat)
    (h : RuntimeChain) : List UInt256 :=
  UInt256.ofNat round :: oldCompressionStack I block h

theorem runtime_reachRightLoop {cA gh bl σ σ₀ A I} {g : Sat256}
    {block : Nat} {h : RuntimeChain} {c : RuntimeMemCursor} {k C : Nat}
    (rd8704 : RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8704⟩ (oldCompressionStack I block h)
      c.mem c.aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8767⟩ (oldRightLoopStack I block 0 h)
      (hashRightInitCursor I h c).mem (hashRightInitCursor I h c).aw
      ByteArray.empty (cA, σ) k' C' := by
  simp only [oldCompressionStack] at rd8704
  let c1 := runtimeStoreCursor c (hashScratchPtr I + ⟨672⟩) h.h0
  have rd8713pre := evm_run_rfl rd8704 with [
    dup7, push1 ⟨160⟩, push2 ⟨512⟩, dup7, add, add]
  have rd8714 := RD.runtimeMstore rd8713pre (by old_decode) (by simp)
  have h672 : (hashScratchPtr I + ⟨512⟩) + ⟨160⟩ =
      hashScratchPtr I + ⟨672⟩ := by rw [u256_add_assoc]; congr 1
  rw [h672] at rd8714
  obtain ⟨_, _, rd8714'⟩ : ∃ k1 C1,
      RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨8714⟩ (oldCompressionStack I block h) c1.mem c1.aw
        ByteArray.empty (cA, σ) k1 C1 :=
    ⟨_, _, by simpa [c1, oldCompressionStack, runtimeStoreCursor] using rd8714⟩
  let c2 := runtimeStoreCursor c1 (hashScratchPtr I + ⟨704⟩) h.h1
  have rd8726pre := evm_run_rfl rd8714' with [
    dup1, push1 ⟨32⟩, push1 ⟨160⟩, push2 ⟨512⟩, dup8, add, add, add]
  have rd8727 := RD.runtimeMstore rd8726pre (by old_decode) (by simp)
  have h704 : ((hashScratchPtr I + ⟨512⟩) + ⟨160⟩) + ⟨32⟩ =
      hashScratchPtr I + ⟨704⟩ := by rw [u256_add_assoc, u256_add_assoc]; congr 1
  rw [h704] at rd8727
  obtain ⟨_, _, rd8727'⟩ : ∃ k2 C2,
      RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨8727⟩ (oldCompressionStack I block h) c2.mem c2.aw
        ByteArray.empty (cA, σ) k2 C2 :=
    ⟨_, _, by simpa [c2, oldCompressionStack, runtimeStoreCursor] using rd8727⟩
  let c3 := runtimeStoreCursor c2 (hashScratchPtr I + ⟨736⟩) h.h2
  have rd8739pre := evm_run_rfl rd8727' with [
    dup6, push1 ⟨64⟩, push1 ⟨160⟩, push2 ⟨512⟩, dup8, add, add, add]
  have rd8740 := RD.runtimeMstore rd8739pre (by old_decode) (by simp)
  have h736 : ((hashScratchPtr I + ⟨512⟩) + ⟨160⟩) + ⟨64⟩ =
      hashScratchPtr I + ⟨736⟩ := by rw [u256_add_assoc, u256_add_assoc]; congr 1
  rw [h736] at rd8740
  obtain ⟨_, _, rd8740'⟩ : ∃ k3 C3,
      RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨8740⟩ (oldCompressionStack I block h) c3.mem c3.aw
        ByteArray.empty (cA, σ) k3 C3 :=
    ⟨_, _, by simpa [c3, oldCompressionStack, runtimeStoreCursor] using rd8740⟩
  let c4 := runtimeStoreCursor c3 (hashScratchPtr I + ⟨768⟩) h.h3
  have rd8752pre := evm_run_rfl rd8740' with [
    dup9, push1 ⟨96⟩, push1 ⟨160⟩, push2 ⟨512⟩, dup8, add, add, add]
  have rd8753 := RD.runtimeMstore rd8752pre (by old_decode) (by simp)
  have h768 : ((hashScratchPtr I + ⟨512⟩) + ⟨160⟩) + ⟨96⟩ =
      hashScratchPtr I + ⟨768⟩ := by rw [u256_add_assoc, u256_add_assoc]; congr 1
  rw [h768] at rd8753
  obtain ⟨_, _, rd8753'⟩ : ∃ k4 C4,
      RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨8753⟩ (oldCompressionStack I block h) c4.mem c4.aw
        ByteArray.empty (cA, σ) k4 C4 :=
    ⟨_, _, by simpa [c4, oldCompressionStack, runtimeStoreCursor] using rd8753⟩
  let c5 := runtimeStoreCursor c4 (hashScratchPtr I + ⟨800⟩) h.h4
  have rd8765pre := evm_run_rfl rd8753' with [
    dup8, push1 ⟨128⟩, push1 ⟨160⟩, push2 ⟨512⟩, dup8, add, add, add]
  have rd8766 := RD.runtimeMstore rd8765pre (by old_decode) (by simp)
  have h800 : ((hashScratchPtr I + ⟨512⟩) + ⟨160⟩) + ⟨128⟩ =
      hashScratchPtr I + ⟨800⟩ := by rw [u256_add_assoc, u256_add_assoc]; congr 1
  rw [h800] at rd8766
  obtain ⟨_, _, rd8766'⟩ : ∃ k5 C5,
      RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨8766⟩ (oldCompressionStack I block h) c5.mem c5.aw
        ByteArray.empty (cA, σ) k5 C5 :=
    ⟨_, _, by simpa [c5, oldCompressionStack, runtimeStoreCursor] using rd8766⟩
  simp only [oldCompressionStack] at rd8766'
  have rd8767 := evm_run_rfl rd8766' with [push0]
  exact ⟨_, _, by
    simpa [oldRightLoopStack, c5, c4, c3, c2, c1, hashRightInitCursor] using rd8767⟩

theorem runtime_rightLoopBody {cA gh bl σ σ₀ A I} {g : Sat256}
    {block round : Nat} {h : RuntimeChain} {c : RuntimeMemCursor} {k C : Nat}
    (hround : round < 80)
    (rd8767 : RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8767⟩ (oldRightLoopStack I block round h)
      c.mem c.aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8767⟩ (oldRightLoopStack I block (round + 1) h)
      (oldRightRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).mem
      (oldRightRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).aw
      ByteArray.empty (cA, σ) k' C' := by
  simp only [oldRightLoopStack, oldCompressionStack] at rd8767
  have hlt : UInt256.lt (UInt256.ofNat round) ⟨80⟩ = ⟨1⟩ := by
    apply ult_one
    rw [ulit_toNat' round (lt_trans hround (by decide)),
      show (⟨80⟩ : UInt256).toNat = 80 from by decide]
    exact hround
  have rd8946 := evm_run_rfl rd8767 with [
    jumpdest, push1 ⟨80⟩, dup2, lt, push2 ⟨8946⟩,
    jumpiT (by rw [hlt]; decide) jump_8946 ]
  have rd4126 := evm_run_rfl rd8946 with [
    jumpdest, dup1, push2 ⟨8967⟩, push1 ⟨1⟩, swap3, dup8,
    push1 ⟨160⟩, push2 ⟨512⟩, dup3, add, add,
    push2 ⟨4126⟩, jump jump_4126 ]
  obtain ⟨_, _, rd8967⟩ := runtime_rightRoundHelper
    (t := UInt256.ofNat round :: ⟨1⟩ :: oldCompressionStack I block h)
    hround (by simp [oldCompressionStack])
    (by simpa [oldRightHelperStack, oldCompressionStack, u256_add_assoc] using rd4126)
  simp only [oldCompressionStack] at rd8967
  have rdNext := evm_run_rfl rd8967 with [
    jumpdest, add, push2 ⟨8767⟩, jump jump_8767 ]
  exact ⟨_, _, by
    simpa [oldRightLoopStack, oldCompressionStack, u256_one_add_ofNat,
      u256_add_comm] using rdNext⟩

theorem runtime_rightLoop {cA gh bl σ σ₀ A I} {g : Sat256}
    {block rounds : Nat} {h : RuntimeChain} {initial : RuntimeMemCursor} {k C : Nat}
    (hrounds : rounds ≤ 80)
    (rd8767 : RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8767⟩ (oldRightLoopStack I block 0 h)
      initial.mem initial.aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8767⟩ (oldRightLoopStack I block rounds h)
      (oldRightLineCursor initial (hashScratchPtr I) rounds).mem
      (oldRightLineCursor initial (hashScratchPtr I) rounds).aw
      ByteArray.empty (cA, σ) k' C' := by
  induction rounds with
  | zero => exact ⟨_, _, by simpa [oldRightLineCursor] using rd8767⟩
  | succ round ih =>
      obtain ⟨_, _, rdRound⟩ := ih (by omega)
      obtain ⟨_, _, rdNext⟩ := runtime_rightLoopBody (by omega) rdRound
      exact ⟨_, _, by simpa [oldRightLineCursor] using rdNext⟩

theorem runtime_rightLoopExit {cA gh bl σ σ₀ A I} {g : Sat256}
    {block : Nat} {h : RuntimeChain} {c : RuntimeMemCursor} {k C : Nat}
    (rd8767 : RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8767⟩ (oldRightLoopStack I block 80 h)
      c.mem c.aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8777⟩ (oldCompressionStack I block h)
      c.mem c.aw ByteArray.empty (cA, σ) k' C' := by
  simp only [oldRightLoopStack, oldCompressionStack] at rd8767
  have rd8777 := evm_run_rfl rd8767 with [
    jumpdest, push1 ⟨80⟩, dup2, lt, push2 ⟨8946⟩,
    jumpiNT (by native_decide), pop ]
  exact ⟨_, _, by simpa [oldCompressionStack] using rd8777⟩

theorem oldPureLeftLine_80 (X : Fin 16 → UInt256) (s : RuntimeLineState) :
    oldPureLeftLine X 80 s = runtimePureLeftLine X 5 s := by rfl

theorem oldPureRightLine_80 (X : Fin 16 → UInt256) (s : RuntimeLineState) :
    oldPureRightLine X 80 s = runtimePureRightLine X 5 s := by rfl

end Ripemd160Old
