import Benchmarks.Safe.V2_0e91d99.P256Memory
import Benchmarks.Safe.V2_0e91d99.RawStaticCall
import Benchmarks.Safe.V2_0e91d99.Blocks.Runtime_031

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V2_0e91d99.RuntimeBlocks

namespace Benchmarks.Safe.V2_0e91d99

theorem safeP256InputMemory {mem : ByteArray} {ptr : Nat} {p : P256Input}
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hb : ptr + 160 < UInt256.size) :
    safeRuntime_block_7219_memory (mem := mem) (x0 := p.qy) (x1 := p.qx)
      (x2 := p.s) (x3 := p.r) (x4 := p.hash) = p256InputMemory mem ptr p := by
  have hadd (j : Nat) (hj : j ≤ 160) :
      (UInt256.ofNat ptr + UInt256.ofNat j).toNat = ptr + j :=
    uadd_ofNat_toNat (by omega) (by omega) (by omega)
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
  simp only [safeRuntime_block_7219_memory, hf, hadd 32 (by decide), hadd 64 (by decide),
    hadd 96 (by decide), hadd 128 (by decide), ulit_toNat' ptr (by omega),
    p256InputMemory, P256Input.words, writeWords, Reasoning.Theory.writeWord, Nat.add_assoc]

theorem p256OutputResultWord (mem out : ByteArray) (ptr : Nat) (p : P256Input) (z : Bool)
    (hout : out.size < UInt256.size) :
    UInt256.land
      (UInt256.land (UInt256.eq (UInt256.ofNat out.size) (UInt256.ofNat 32))
        (UInt256.eq (UInt256.ofNat 1) (memLoad ⟨0⟩ (p256OutputMemory mem ptr p out))))
      z.toUInt256 = (p256Result z out).toUInt256 := by
  by_cases hs : out.size = 32
  · rw [p256OutputMemory_word _ _ _ _ (by omega), hs]
    by_cases hw : calldataWord out 0 = ⟨1⟩
    · rw [hw]
      cases z <;> simp [p256Result, hs, hw] <;> decide +kernel
    · have he : UInt256.eq (UInt256.ofNat 1) (calldataWord out 0) = ⟨0⟩ :=
        u256_eq_of_ne (fun h ↦ hw h.symm)
      rw [he]
      cases z <;> simp [p256Result, hs, hw] <;> decide +kernel
  · have hn : UInt256.ofNat out.size ≠ UInt256.ofNat 32 := by
      intro he
      have hh := congrArg UInt256.toNat he
      rw [ulit_toNat' out.size hout] at hh
      exact hs hh
    rw [u256_eq_of_ne hn, u256_land_zero_left, u256_land_zero_left]
    simp [p256Result, hs, Bool.toUInt256]
    rfl

set_option maxRecDepth 100000 in
theorem safeP256Trace (p : P256Input) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata ptr ret} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7219⟩
      (p.qy :: p.qx :: p.s :: p.r :: p.hash :: ret :: R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hb : ptr + 160 < UInt256.size)
    (hov : R.length + 14 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ evm' σ' out z aw' k' C',
      ExecFuncBody fork config p.frame evm p256VerifyFunction.body
        (.returned (p.finalFrame z out) evm' (some [.bool (p256Result z out)])) ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RD fork safeBytecode I g s0 ret ((p256Result z out).toUInt256 :: R)
        (p256OutputMemory mem ptr p out) aw' out σ' k' C' := by
  obtain ⟨aw₁, k₁, C₁, h₁⟩ := safeRuntime_block_7219_packed (by simp; omega) h
  have hm := safeP256InputMemory (p := p) hf hb
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
  simp only [safeRuntime_block_7219_stack] at h₁
  rw [hm] at h₁
  simp only [hf] at h₁
  obtain ⟨evm', σ', z, out, aw₂, k₂, C₂, hc, he, ha, hw, h₂, hout, _⟩ :=
    rawStaticCallTraceFrom evm h₁ hee hacc hworld (by native_decide) (by simp; omega)
  have hmem : callOutputMem (p256InputMemory mem ptr p) out ⟨0⟩ (UInt256.ofNat 32) =
      p256OutputMemory mem ptr p out := by
    change out.write 0 (p256InputMemory mem ptr p) 0
      (min (UInt256.ofNat 32) (UInt256.ofNat out.size)).toNat = _
    rw [callOutputLength hout]
    rfl
  rw [hmem] at h₂
  have hc' : callViaEVM fork evm (AccountAddress.ofNat 256) 0 (wordBytes p.words)
      (z, evm', out) false := by
    simpa only [ulit_toNat' ptr (by omega),
      show (UInt256.ofNat 160).toNat = 160 from rfl, p256InputMemory_read] using hc
  change RD fork safeBytecode I g s0 ⟨7262⟩
    (z.toUInt256 :: UInt256.ofNat ptr :: ⟨0⟩ :: p.qy :: p.qx :: p.s :: p.r :: p.hash :: ret :: R)
    (p256OutputMemory mem ptr p out) aw₂ out σ' k₂ C₂ at h₂
  obtain ⟨aw₃, k₃, C₃, h₃⟩ := safeRuntime_block_7262_packed (by omega) hret h₂
  simp only [safeRuntime_block_7262_stack, p256OutputResultWord _ _ _ _ _ hout] at h₃
  exact ⟨evm', σ', out, z, aw₃, k₃, C₃, safeP256Source hc', he, ha, hw, h₃⟩

end Benchmarks.Safe.V2_0e91d99
