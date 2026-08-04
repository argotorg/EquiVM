import Examples.Ripemd160Old.HashParser

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Ripemd160Old

open Ripemd160

def oldCompressionStack (I : ExecutionEnv) (block : Nat)
    (h : RuntimeChain) : List UInt256 :=
  [h.h1, hashPadPtr I, hashPaddedLengthWord I, hashScratchPtr I,
    UInt256.ofNat block, h.h2, h.h0, h.h4, h.h3, ⟨254⟩]

def oldLeftLoopStack (I : ExecutionEnv) (block round : Nat)
    (h : RuntimeChain) : List UInt256 :=
  UInt256.ofNat round :: oldCompressionStack I block h

theorem runtime_parseLoopExit {cA gh bl σ σ₀ A I} {g : Sat256}
    {block : Nat} {h : RuntimeChain} {c : RuntimeMemCursor} {k C : Nat}
    (rd8635 : RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8635⟩ (oldParseLoopStack I block 16 h)
      c.mem c.aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8646⟩ (oldCompressionStack I block h)
      c.mem c.aw ByteArray.empty (cA, σ) k' C' := by
  simp only [oldParseLoopStack] at rd8635
  have rd8646 := evm_run_rfl rd8635 with [
    jumpdest, push1 ⟨16⟩, dup2, lt, push2 ⟨8997⟩,
    jumpiNT (by native_decide), pop, pop ]
  exact ⟨_, _, by simpa [oldCompressionStack] using rd8646⟩

theorem runtime_parseBlock {cA gh bl σ σ₀ A I} {g : Sat256}
    {block : Nat} {h : RuntimeChain} {initial : RuntimeMemCursor} {k C : Nat}
    (hblock : block < Model.paddedLength I.calldata.size / 64)
    (rd8635 : RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8635⟩ (oldParseLoopStack I block 0 h)
      initial.mem initial.aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8646⟩ (oldCompressionStack I block h)
      (hashParseCursor I (UInt256.ofNat block) initial 16).mem
      (hashParseCursor I (UInt256.ofNat block) initial 16).aw
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd16⟩ := runtime_parseLoop (n := 16) hblock (by decide) rd8635
  exact runtime_parseLoopExit rd16

/-- Initialize the old runtime's left line and reach its 80-round loop. -/
theorem runtime_reachLeftLoop {cA gh bl σ σ₀ A I} {g : Sat256}
    {block : Nat} {h : RuntimeChain} {c : RuntimeMemCursor} {k C : Nat}
    (rd8646 : RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8646⟩ (oldCompressionStack I block h)
      c.mem c.aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8694⟩ (oldLeftLoopStack I block 0 h)
      (hashLeftInitCursor I h c).mem (hashLeftInitCursor I h c).aw
      ByteArray.empty (cA, σ) k' C' := by
  simp only [oldCompressionStack] at rd8646
  let c1 := runtimeStoreCursor c (hashScratchPtr I + ⟨512⟩) h.h0
  have rd8652pre := evm_run_rfl rd8646 with [dup7, push2 ⟨512⟩, dup6, add]
  have rd8653 := RD.runtimeMstore rd8652pre (by old_decode) (by simp)
  obtain ⟨_, _, rd8653'⟩ : ∃ k1 C1,
      RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨8653⟩ (oldCompressionStack I block h) c1.mem c1.aw
        ByteArray.empty (cA, σ) k1 C1 :=
    ⟨_, _, by simpa [c1, oldCompressionStack, runtimeStoreCursor,
      u256_add_comm] using rd8653⟩
  let c2 := runtimeStoreCursor c1 (hashScratchPtr I + ⟨544⟩) h.h1
  have rd8662pre := evm_run_rfl rd8653' with [
    dup1, push1 ⟨32⟩, push2 ⟨512⟩, dup7, add, add]
  have rd8663 := RD.runtimeMstore rd8662pre (by old_decode) (by simp)
  have h544 : (hashScratchPtr I + ⟨512⟩) + ⟨32⟩ =
      hashScratchPtr I + ⟨544⟩ := by
    rw [u256_add_assoc]
    congr 1
  rw [h544] at rd8663
  obtain ⟨_, _, rd8663'⟩ : ∃ k2 C2,
      RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨8663⟩ (oldCompressionStack I block h) c2.mem c2.aw
        ByteArray.empty (cA, σ) k2 C2 :=
    ⟨_, _, by simpa [c2, oldCompressionStack, runtimeStoreCursor] using rd8663⟩
  let c3 := runtimeStoreCursor c2 (hashScratchPtr I + ⟨576⟩) h.h2
  have rd8672pre := evm_run_rfl rd8663' with [
    dup6, push1 ⟨64⟩, push2 ⟨512⟩, dup7, add, add]
  have rd8673 := RD.runtimeMstore rd8672pre (by old_decode) (by simp)
  have h576 : (hashScratchPtr I + ⟨512⟩) + ⟨64⟩ =
      hashScratchPtr I + ⟨576⟩ := by
    rw [u256_add_assoc]
    congr 1
  rw [h576] at rd8673
  obtain ⟨_, _, rd8673'⟩ : ∃ k3 C3,
      RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨8673⟩ (oldCompressionStack I block h) c3.mem c3.aw
        ByteArray.empty (cA, σ) k3 C3 :=
    ⟨_, _, by simpa [c3, oldCompressionStack, runtimeStoreCursor] using rd8673⟩
  let c4 := runtimeStoreCursor c3 (hashScratchPtr I + ⟨608⟩) h.h3
  have rd8682pre := evm_run_rfl rd8673' with [
    dup9, push1 ⟨96⟩, push2 ⟨512⟩, dup7, add, add]
  have rd8683 := RD.runtimeMstore rd8682pre (by old_decode) (by simp)
  have h608 : (hashScratchPtr I + ⟨512⟩) + ⟨96⟩ =
      hashScratchPtr I + ⟨608⟩ := by
    rw [u256_add_assoc]
    congr 1
  rw [h608] at rd8683
  obtain ⟨_, _, rd8683'⟩ : ∃ k4 C4,
      RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨8683⟩ (oldCompressionStack I block h) c4.mem c4.aw
        ByteArray.empty (cA, σ) k4 C4 :=
    ⟨_, _, by simpa [c4, oldCompressionStack, runtimeStoreCursor] using rd8683⟩
  let c5 := runtimeStoreCursor c4 (hashScratchPtr I + ⟨640⟩) h.h4
  have rd8692pre := evm_run_rfl rd8683' with [
    dup8, push1 ⟨128⟩, push2 ⟨512⟩, dup7, add, add]
  have rd8693 := RD.runtimeMstore rd8692pre (by old_decode) (by simp)
  have h640 : (hashScratchPtr I + ⟨512⟩) + ⟨128⟩ =
      hashScratchPtr I + ⟨640⟩ := by
    rw [u256_add_assoc]
    congr 1
  rw [h640] at rd8693
  obtain ⟨_, _, rd8693'⟩ : ∃ k5 C5,
      RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨8693⟩ (oldCompressionStack I block h) c5.mem c5.aw
        ByteArray.empty (cA, σ) k5 C5 :=
    ⟨_, _, by simpa [c5, oldCompressionStack, runtimeStoreCursor] using rd8693⟩
  simp only [oldCompressionStack] at rd8693'
  have rd8694 := evm_run_rfl rd8693' with [push0]
  exact ⟨_, _, by
    simpa [oldLeftLoopStack, c5, c4, c3, c2, c1, hashLeftInitCursor] using rd8694⟩

end Ripemd160Old
