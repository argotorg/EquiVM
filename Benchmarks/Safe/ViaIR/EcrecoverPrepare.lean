import Benchmarks.Safe.ViaIR.EcrecoverMemory
import Benchmarks.Safe.ViaIR.Blocks.Runtime_040

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

theorem safeEcrecoverInputMemory {mem : ByteArray} {ptr : Nat} {p : EcrecoverInput}
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hb : ptr + 128 < UInt256.size)
    (hv : p.v.toNat < 256) :
    safeRuntime_block_8669_memory
      (mem := safeRuntime_block_8619_memory (mem := mem) (x0 := p.v) (x1 := p.r)
        (x2 := p.s) (x3 := p.digest)) (x3 := ⟨0⟩) = ecrecoverInputMemory mem ptr p := by
  have hadd (j : Nat) (hj : j ≤ 128) :
      (UInt256.ofNat ptr + UInt256.ofNat j).toNat = ptr + j :=
    uadd_ofNat_toNat (by omega) (by omega) (by omega)
  have hmask : UInt256.land p.v (UInt256.ofNat 255) = p.v := lowByteClean hv
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
  simp only [safeRuntime_block_8669_memory, safeRuntime_block_8619_memory, hf, hmask,
    hadd 32 (by decide), hadd 64 (by decide), hadd 96 (by decide),
    ulit_toNat' ptr (by omega), ecrecoverInputMemory, ecrecoverWords, writeWords,
    Reasoning.Theory.writeWord, Nat.add_assoc]
  rfl

theorem ecrecoverPointerArithmetic {ptr : Nat} (_hb : ptr + 128 < UInt256.size) :
    UInt256.sub (UInt256.ofNat ptr + UInt256.ofNat 128) (UInt256.ofNat ptr) = ⟨128⟩ := by
  exact word_add_sub_left _ _

theorem safeEcrecoverEthSignPrepare {I g s0 σ k C aw mem rdata ptr} {p : EcrecoverInput}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8619⟩ (p.v :: p.r :: p.s :: p.digest :: R)
      mem aw rdata σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hb : ptr + 128 < UInt256.size) (hv : p.v.toNat < 256) (hov : R.length + 14 ≤ 1024) :
    ∃ gasArg aw' k' C', RD fork safeBytecode I g s0 ⟨8678⟩
      (gasArg :: ⟨1⟩ :: UInt256.ofNat ptr :: ⟨128⟩ :: ⟨0⟩ :: ⟨32⟩ :: R)
      (ecrecoverInputMemory mem ptr p) aw' rdata σ k' C' := by
  obtain ⟨aw', k', C', h₁⟩ := safeRuntime_block_8619_packed hov (by jump_dest) h
  obtain ⟨aw'', k'', C'', h₂⟩ := safeRuntime_block_8669_packed (by simp; omega) h₁
  rw [safeEcrecoverInputMemory (p := p) hf hb hv] at h₂
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
  simp only [safeRuntime_block_8669_stack, hf, ecrecoverPointerArithmetic hb] at h₂
  exact ⟨_, aw'', k'', C'', h₂⟩

theorem safeEcrecoverPlainPrepare {I g s0 σ k C aw mem rdata ptr} {p : EcrecoverInput}
    {last src : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8691⟩
      (p.r :: p.s :: p.v :: last :: src :: p.digest :: R) mem aw rdata σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hb : ptr + 128 < UInt256.size) (hv : p.v.toNat < 256) (hov : R.length + 17 ≤ 1024) :
    ∃ gasArg aw' k' C', RD fork safeBytecode I g s0 ⟨8678⟩
      (gasArg :: ⟨1⟩ :: UInt256.ofNat ptr :: ⟨128⟩ :: ⟨0⟩ :: ⟨32⟩ ::
        last :: src :: p.digest :: R) (ecrecoverInputMemory mem ptr p) aw' rdata σ k' C' := by
  obtain ⟨aw', k', C', h₁⟩ := safeRuntime_block_8691_packed hov (by jump_dest) h
  obtain ⟨aw'', k'', C'', h₂⟩ := safeRuntime_block_8669_packed (by simp; omega) h₁
  have hmemory : safeRuntime_block_8669_memory
      (mem := safeRuntime_block_8691_memory (mem := mem) (x0 := p.r) (x1 := p.s)
        (x2 := p.v) (x5 := p.digest)) (x3 := ⟨0⟩) = ecrecoverInputMemory mem ptr p := by
    have hm := safeEcrecoverInputMemory (p := p) hf hb hv
    have hmask : UInt256.land p.v (UInt256.ofNat 255) = p.v := lowByteClean hv
    simpa only [safeRuntime_block_8669_memory, safeRuntime_block_8619_memory,
      safeRuntime_block_8691_memory, hmask] using hm
  rw [hmemory] at h₂
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
  simp only [safeRuntime_block_8669_stack, hf, ecrecoverPointerArithmetic hb] at h₂
  exact ⟨_, aw'', k'', C'', h₂⟩

end Benchmarks.Safe.ViaIR
