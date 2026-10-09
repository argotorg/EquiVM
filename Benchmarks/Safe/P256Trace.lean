import Benchmarks.Safe.P256Memory
import Benchmarks.Safe.RawStaticCall
import Benchmarks.Safe.Blocks.Runtime_031

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

theorem safeP256InputMemory {mem : ByteArray} {ptr : Nat} {p : P256Input}
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hb : ptr + 160 < UInt256.size) :
    safeRuntime_block_7108_memory (mem := mem) (x0 := p.qy) (x1 := p.qx)
      (x2 := p.s) (x3 := p.r) (x4 := p.h) = p256InputMemory mem ptr p := by
  have hadd (j : Nat) (hj : j ≤ 160) :
      (UInt256.ofNat ptr + UInt256.ofNat j).toNat = ptr + j :=
    uadd_ofNat_toNat (by omega) (by omega) (by omega)
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
  simp only [safeRuntime_block_7108_memory, hf, hadd 32 (by decide), hadd 64 (by decide),
    hadd 96 (by decide), hadd 128 (by decide), ulit_toNat' ptr (by omega),
    p256InputMemory, p256Words, writeWords, Reasoning.Theory.writeWord, Nat.add_assoc]

theorem safeP256Prepare {I g s0 σ k C aw mem rdata ptr} {p : P256Input}
    {ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨7108⟩ (p.qy :: p.qx :: p.s :: p.r :: p.h :: ret :: R)
      mem aw rdata σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hb : ptr + 160 < UInt256.size)
    (hov : R.length + 14 ≤ 1024) :
    ∃ gasArg aw' k' C', RD safeBytecode I g s0 ⟨7150⟩
      (gasArg :: ⟨256⟩ :: UInt256.ofNat ptr :: ⟨160⟩ :: ⟨0⟩ :: ⟨32⟩ ::
        UInt256.ofNat ptr :: ⟨0⟩ :: p.qy :: p.qx :: p.s :: p.r :: p.h :: ret :: R)
      (p256InputMemory mem ptr p) aw' rdata σ k' C' := by
  obtain ⟨aw', k', C', hr⟩ := safeRuntime_block_7108_packed (by simp; omega) h
  rw [safeP256InputMemory hf hb] at hr
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
  simp only [safeRuntime_block_7108_stack, hf] at hr
  exact ⟨_, aw', k', C', hr⟩

theorem safeP256ResultStack {mem out : ByteArray} {ptr : Nat} {p : P256Input}
    {z : Bool} {R : List UInt256} (hb : out.size < UInt256.size) :
    safeRuntime_block_7151_stack (mem := p256OutputMemory mem ptr p out)
      (rdata := out) (x0 := if z then ⟨1⟩ else ⟨0⟩) (R := R) =
      (if p256Result z out then ⟨1⟩ else ⟨0⟩) :: R := by
  have hs : (UInt256.ofNat out.size = UInt256.ofNat 32) ↔ out.size = 32 := by
    constructor
    · intro he
      have hh := congrArg UInt256.toNat he
      simpa only [ulit_toNat' out.size hb, show (UInt256.ofNat 32).toNat = 32 from rfl]
        using hh
    · intro he
      rw [he]
  cases z with
  | false => simp [safeRuntime_block_7151_stack, p256Result, u256_land_zero_right]
  | true =>
      by_cases ho : out.size = 32
      · rw [safeRuntime_block_7151_stack, p256OutputMemory_word _ _ _ _ (by omega)]
        by_cases hw : calldataWord out 0 = ⟨1⟩
        · simp [p256Result, ho, hw, UInt256.eq, UInt256.fromBool]
          rfl
        · have hw' : UInt256.ofNat 1 ≠ calldataWord out 0 := fun h ↦ hw h.symm
          simp [p256Result, ho, hw, hw', UInt256.eq, UInt256.fromBool]
          rfl
      · have hn : UInt256.ofNat out.size ≠ UInt256.ofNat 32 := fun h ↦ ho (hs.mp h)
        simp [safeRuntime_block_7151_stack, p256Result, ho, hn, UInt256.eq,
          UInt256.fromBool, u256_land_zero_left]
        change UInt256.land (UInt256.land ⟨0⟩ _) ⟨1⟩ = ⟨0⟩
        rw [u256_land_zero_left, u256_land_zero_left]

theorem safeP256Trace {I g s0 σ k C aw mem rdata ptr} {p : P256Input}
    {ret : UInt256} {R : List UInt256} (evm : EVM.State)
    (h : RD safeBytecode I g s0 ⟨7108⟩ (p.qy :: p.qx :: p.s :: p.r :: p.h :: ret :: R)
      mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hb : ptr + 160 < UInt256.size)
    (hov : R.length + 14 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ evm' σ' z out aw' k' C',
      callViaEVM evm (AccountAddress.ofNat 256) 0 (wordBytes (p256Words p))
        (z, evm', out) false ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RD safeBytecode I g s0 ret ((if p256Result z out then ⟨1⟩ else ⟨0⟩) :: R)
        (p256OutputMemory mem ptr p out) aw' out σ' k' C' := by
  obtain ⟨_, _, _, _, h₁⟩ := safeP256Prepare h hf hb hov
  obtain ⟨evm', σ', z, out, aw', k', C', hc, he, ha, hw, h₂, hout, _⟩ :=
    rawStaticCallTraceFrom evm h₁ hee hacc hworld (by native_decide) (by simp; omega)
  have hm : callOutputMem (p256InputMemory mem ptr p) out ⟨0⟩ ⟨32⟩ =
      p256OutputMemory mem ptr p out := by
    change out.write 0 (p256InputMemory mem ptr p) 0
      (min (UInt256.ofNat 32) (UInt256.ofNat out.size)).toNat = _
    rw [callOutputLength hout]
    rfl
  rw [hm] at h₂
  obtain ⟨aw'', k'', C'', h₃⟩ := safeRuntime_block_7151_packed (by omega) hret h₂
  rw [safeP256ResultStack hout] at h₃
  refine ⟨evm', σ', z, out, aw'', k'', C'', ?_, he, ha, hw, h₃⟩
  simpa only [ulit_toNat' ptr (by omega), show (⟨160⟩ : UInt256).toNat = 160 from rfl,
    p256InputMemory_read] using hc

end Benchmarks.Safe
