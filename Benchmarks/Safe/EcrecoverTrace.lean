import Benchmarks.Safe.EcrecoverPrepare
import Benchmarks.Safe.RawStaticCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000 in
theorem safeEcrecoverFinish (plain z : Bool) {I g s0 σ k C aw mem out ptr}
    {p : EcrecoverInput} {a b c d e x y : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 (if plain then ⟨2652⟩ else ⟨2555⟩)
      ((if z then ⟨1⟩ else ⟨0⟩) :: x :: y :: a :: b :: c :: d :: e :: R)
      (ecrecoverOutputMemory mem ptr p out) aw out σ k C)
    (hp : 96 ≤ ptr) (hb : ptr + 160 < UInt256.size) (ho : EcrecoverOutput out)
    (hov : R.length + 11 ≤ 1024) :
    if z then ∃ aw' k' C', RD safeBytecode I g s0 ⟨2679⟩
      (a :: b :: c :: d :: calldataWord out 0 :: R)
      (ecrecoverOutputMemory mem ptr p out) aw' out σ k' C'
    else RDrev safeBytecode g s0 := by
  have hfree := ecrecoverOutputMemory_free mem out ptr p hp
  change memLoad (UInt256.ofNat 64) _ = _ at hfree
  have hword := ecrecoverOutputMemory_word mem out ptr p hp (by omega) ho
  have hsub := (ecrecoverPointerArithmetic hb).2.2
  cases z with
  | false =>
      cases plain with
      | false =>
          have h₁ := safeRuntime_block_2555_fallthrough (by simp; omega) (by decide) h
          exact safeRuntime_block_2562 (by
            simp only [safeRuntime_block_2555_fallthrough_stack, List.length_cons]; omega) h₁
      | true =>
          have h₁ := safeRuntime_block_2652_fallthrough (by simp; omega) (by decide) h
          exact safeRuntime_block_2659 (by
            simp only [safeRuntime_block_2652_fallthrough_stack, List.length_cons]; omega) h₁
  | true =>
      cases plain with
      | false =>
          have h₁ := safeRuntime_block_2555_taken (by simp; omega) (by decide) (by jump_dest) h
          obtain ⟨aw', k', C', h₂⟩ := safeRuntime_block_2569_packed (by omega) (by jump_dest) h₁
          simp only [safeRuntime_block_2569_stack, hfree, hsub, hword] at h₂
          exact ⟨aw', k', C', h₂⟩
      | true =>
          have h₁ := safeRuntime_block_2652_taken (by simp; omega) (by decide) (by jump_dest) h
          obtain ⟨aw', k', C', h₂⟩ := safeRuntime_block_2666_packed (by omega) h₁
          simp only [safeRuntime_block_2666_stack, hfree, hsub, hword] at h₂
          exact ⟨aw', k', C', h₂⟩

theorem safeEcrecoverCall (plain : Bool) (evm : EVM.State) {I g s0 σ k C aw mem rdata ptr}
    {p : EcrecoverInput} {gasArg a b c d e : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 (if plain then ⟨2651⟩ else ⟨2554⟩)
      (gasArg :: ⟨1⟩ :: UInt256.ofNat (ptr + 32) :: ⟨128⟩ :: UInt256.ofNat ptr :: ⟨32⟩ ::
        UInt256.ofNat (ptr + 160) :: ⟨1⟩ :: a :: b :: c :: d :: e :: R)
      (ecrecoverInputMemory mem ptr p) aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hp : 96 ≤ ptr) (hb : ptr + 160 < UInt256.size) (hov : R.length + 11 ≤ 1024) :
    (RDrev safeBytecode g s0 ∧
      ExecFuncBody config (ecrecoverFrame p) evm ecrecoverAddressFunction.body .reverted) ∨
    ∃ evm' σ' out aw' k' C',
      ExecFuncBody config (ecrecoverFrame p) evm ecrecoverAddressFunction.body
        (.returned (ecrecoverFinalFrame p true out) evm'
          (some [.address (AccountAddress.ofUInt256 (calldataWord out 0))])) ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RD safeBytecode I g s0 ⟨2679⟩ (a :: b :: c :: d :: calldataWord out 0 :: R)
        (ecrecoverOutputMemory mem ptr p out) aw' out σ' k' C' ∧ EcrecoverOutput out := by
  obtain ⟨evm', σ', z, out, aw', k', C', hc, he, ha, hw, h₁, hout, _⟩ :=
    rawStaticCallTraceFrom evm h hee hacc hworld (by cases plain <;> native_decide)
      (by simp; omega)
  have hm : callOutputMem (ecrecoverInputMemory mem ptr p) out (UInt256.ofNat ptr) ⟨32⟩ =
      ecrecoverOutputMemory mem ptr p out := by
    change out.write 0 (ecrecoverInputMemory mem ptr p) (UInt256.ofNat ptr).toNat
      (min (UInt256.ofNat 32) (UInt256.ofNat out.size)).toNat = _
    rw [callOutputLength hout, ulit_toNat' ptr (by omega)]
    rfl
  rw [hm] at h₁
  have hc' : callViaEVM evm (AccountAddress.ofNat 1) 0 (wordBytes (ecrecoverWords p))
      (z, evm', out) false := by
    simpa only [ulit_toNat' (ptr + 32) (by omega),
      show (⟨128⟩ : UInt256).toNat = 128 from rfl, ecrecoverInputMemory_read] using hc
  have ho := callEcrecoverOutput hc'
  have hpc : (if plain then (⟨2651⟩ : UInt256) else ⟨2554⟩) + ⟨1⟩ =
      (if plain then ⟨2652⟩ else ⟨2555⟩) := by cases plain <;> decide
  rw [hpc] at h₁
  have hfinish := safeEcrecoverFinish plain z h₁ hp hb ho hov
  have hs := safeEcrecoverSource hc'
  cases z with
  | false => exact .inl ⟨hfinish, hs⟩
  | true =>
      obtain ⟨aw'', k'', C'', h₂⟩ := hfinish
      exact .inr ⟨evm', σ', out, aw'', k'', C'', hs, he, ha, hw, h₂, ho⟩

end Benchmarks.Safe
