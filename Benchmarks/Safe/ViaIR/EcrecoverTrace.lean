import Benchmarks.Safe.ViaIR.EcrecoverPrepare
import Benchmarks.Safe.ViaIR.RawStaticCall
import Benchmarks.Safe.ViaIR.Blocks.Runtime_027

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

theorem safeEcrecoverFinish (z : Bool) {I g s0 σ k C aw mem out ptr}
    {p : EcrecoverInput} {last : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8679⟩ ((if z then ⟨1⟩ else ⟨0⟩) :: last :: R)
      (ecrecoverOutputMemory mem ptr p out) aw out σ k C)
    (ho : EcrecoverOutput out) (hov : R.length + 8 ≤ 1024) :
    if z then ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨7803⟩
      (last :: calldataWord out 0 :: R)
      (ecrecoverOutputMemory mem ptr p out) aw' out σ k' C'
    else RDrev fork safeBytecode g s0 := by
  cases z with
  | false =>
      have h₁ := safeRuntime_block_8679_taken (by simp; omega) (by decide) (by jump_dest) h
      exact safeRuntime_block_5682 (by
        simp [safeRuntime_block_8679_taken_stack]; omega) (by
        simpa only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.zero_add] using
          Nat.mod_le out.size UInt256.size) h₁
  | true =>
      have h₁ := safeRuntime_block_8679_fallthrough (by simp; omega) (by decide) h
      obtain ⟨aw', k', C', h₂⟩ := safeRuntime_block_8684_packed (by simp; omega)
        (by jump_dest) h₁
      simp only [safeRuntime_block_8684_stack, ecrecoverOutputMemory_word _ _ _ _ ho] at h₂
      exact ⟨aw', k', C', h₂⟩

theorem safeEcrecoverCall (evm : EVM.State) {I g s0 σ k C aw mem rdata ptr}
    {p : EcrecoverInput} {gasArg last : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8678⟩
      (gasArg :: ⟨1⟩ :: UInt256.ofNat ptr :: ⟨128⟩ :: ⟨0⟩ :: ⟨32⟩ :: last :: R)
      (ecrecoverInputMemory mem ptr p) aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hp : 32 ≤ ptr) (hb : ptr + 128 < UInt256.size) (hov : R.length + 8 ≤ 1024) :
    (RDrev fork safeBytecode g s0 ∧
      ExecFuncBody fork config (ecrecoverFrame p) evm ecrecoverAddressFunction.body .reverted) ∨
    ∃ evm' σ' out aw' k' C',
      ExecFuncBody fork config (ecrecoverFrame p) evm ecrecoverAddressFunction.body
        (.returned (ecrecoverFinalFrame p true out) evm'
          (some [.address (AccountAddress.ofUInt256 (calldataWord out 0))])) ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RD fork safeBytecode I g s0 ⟨7803⟩ (last :: calldataWord out 0 :: R)
        (ecrecoverOutputMemory mem ptr p out) aw' out σ' k' C' ∧ EcrecoverOutput out := by
  obtain ⟨evm', σ', z, out, aw', k', C', hc, he, ha, hw, h₁, hout, _⟩ :=
    rawStaticCallTraceFrom evm h hee hacc hworld (by native_decide) (by simp; omega)
  have hm : callOutputMem (ecrecoverInputMemory mem ptr p) out ⟨0⟩ ⟨32⟩ =
      ecrecoverOutputMemory mem ptr p out := by
    change out.write 0 (ecrecoverInputMemory mem ptr p) 0
      (min (UInt256.ofNat 32) (UInt256.ofNat out.size)).toNat = _
    rw [callOutputLength hout]
    rfl
  rw [hm] at h₁
  have hc' : callViaEVM fork evm (AccountAddress.ofNat 1) 0 (wordBytes (ecrecoverWords p))
      (z, evm', out) false := by
    simpa only [ulit_toNat' ptr (by omega), show (⟨128⟩ : UInt256).toNat = 128 from rfl,
      ecrecoverInputMemory_read _ _ _ hp] using hc
  have ho := callEcrecoverOutput hc'
  have hfinish := safeEcrecoverFinish z h₁ ho hov
  have hs := safeEcrecoverSource hc'
  cases z with
  | false => exact .inl ⟨hfinish, hs⟩
  | true =>
      obtain ⟨aw'', k'', C'', h₂⟩ := hfinish
      exact .inr ⟨evm', σ', out, aw'', k'', C'', hs, he, ha, hw, h₂, ho⟩

end Benchmarks.Safe.ViaIR
