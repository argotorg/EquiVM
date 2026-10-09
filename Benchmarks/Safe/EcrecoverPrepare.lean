import Benchmarks.Safe.EcrecoverMemory
import Benchmarks.Safe.Blocks.Runtime_016

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

theorem safeEcrecoverInputMemory {mem : ByteArray} {ptr : Nat} {p : EcrecoverInput}
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hb : ptr + 160 < UInt256.size)
    (hv : p.v.toNat < 256) :
    safeRuntime_block_2493_memory (mem := mem) (x0 := p.v) (x1 := p.digest)
      (x4 := p.s) (x5 := p.r) = ecrecoverInputMemory mem ptr p := by
  have hadd (j : Nat) (hj : j ≤ 160) :
      (UInt256.ofNat ptr + UInt256.ofNat j).toNat = ptr + j :=
    uadd_ofNat_toNat (by omega) (by omega) (by omega)
  have h32 : UInt256.ofNat ptr + UInt256.ofNat 32 = UInt256.ofNat (ptr + 32) := by
    rw [u256_add_comm]
    exact u256_32_add_ofNat ptr
  have hmask : UInt256.land p.v (UInt256.ofNat 255) = p.v := lowByteClean hv
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
  simp only [safeRuntime_block_2493_memory, hf, hmask, hadd 32 (by decide),
    hadd 64 (by decide), hadd 96 (by decide), hadd 128 (by decide), h32,
    ulit_toNat' ptr (by omega), ulit_toNat' (ptr + 32) (by omega), ecrecoverInputMemory,
    ecrecoverWords, writeWords, Reasoning.Theory.writeWord, Nat.add_assoc]
  rfl

theorem ecrecoverPointerArithmetic {ptr : Nat} (hb : ptr + 160 < UInt256.size) :
    UInt256.ofNat 160 + UInt256.ofNat ptr = UInt256.ofNat (ptr + 160) ∧
    UInt256.sub (UInt256.ofNat (ptr + 160)) (UInt256.ofNat (ptr + 32)) = ⟨128⟩ ∧
    UInt256.sub (UInt256.ofNat (ptr + 32)) (UInt256.ofNat 32) = UInt256.ofNat ptr := by
  refine ⟨?_, ?_, ?_⟩
  · apply u256_inj
    rw [ulit_toNat' _ hb]
    simpa only [Nat.add_comm] using
      (uadd_ofNat_toNat (a := 160) (b := ptr) (by omega) (by omega) (by omega))
  · apply u256_inj
    rw [usub_ofNat_lit_toNat (by omega) hb]
    change ptr + 160 - (ptr + 32) = 128
    omega
  · apply u256_inj
    rw [usub_ofNat_lit_toNat (by omega) (by omega), ulit_toNat' ptr (by omega)]
    omega

theorem safeEcrecoverEthSignPrepare {I g s0 σ k C aw mem rdata ptr} {p : EcrecoverInput}
    {x : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨2493⟩
      (p.v :: p.digest :: ⟨1⟩ :: x :: p.s :: p.r :: R) mem aw rdata σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hp : 96 ≤ ptr)
    (hb : ptr + 160 < UInt256.size) (hv : p.v.toNat < 256) (hov : R.length + 11 ≤ 1024) :
    ∃ gasArg aw' k' C', RD safeBytecode I g s0 ⟨2554⟩
      (gasArg :: ⟨1⟩ :: UInt256.ofNat (ptr + 32) :: ⟨128⟩ :: UInt256.ofNat ptr :: ⟨32⟩ ::
        UInt256.ofNat (ptr + 160) :: ⟨1⟩ :: x :: p.s :: p.r :: R)
      (ecrecoverInputMemory mem ptr p) aw' rdata σ k' C' := by
  obtain ⟨aw', k', C', hr⟩ := safeRuntime_block_2493_packed hov h
  have hm := safeEcrecoverInputMemory hf hb hv
  have hfree := ecrecoverInputMemory_free mem ptr p hp
  change memLoad (UInt256.ofNat 64) _ = _ at hfree
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
  rcases ecrecoverPointerArithmetic hb with ⟨h160, h128, h32⟩
  simp only [safeRuntime_block_2493_stack] at hr
  rw [← safeRuntime_block_2493_memory, hm] at hr
  simp only [hfree, hf, h160, h128, h32] at hr
  exact ⟨_, aw', k', C', hr⟩

theorem safeEcrecoverPlainPrepare {I g s0 σ k C aw mem rdata ptr} {p : EcrecoverInput}
    {x y a b c : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨2586⟩
      (x :: p.s :: p.r :: p.v :: y :: a :: b :: c :: p.digest :: R) mem aw rdata σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hp : 96 ≤ ptr)
    (hb : ptr + 160 < UInt256.size) (hv : p.v.toNat < 256) (hov : R.length + 17 ≤ 1024) :
    ∃ gasArg aw' k' C', RD safeBytecode I g s0 ⟨2651⟩
      (gasArg :: ⟨1⟩ :: UInt256.ofNat (ptr + 32) :: ⟨128⟩ :: UInt256.ofNat ptr :: ⟨32⟩ ::
        UInt256.ofNat (ptr + 160) :: ⟨1⟩ :: x :: p.s :: p.r :: p.v :: y :: a :: b :: c ::
        p.digest :: R) (ecrecoverInputMemory mem ptr p) aw' rdata σ k' C' := by
  obtain ⟨aw', k', C', hr⟩ := safeRuntime_block_2586_packed hov h
  have hm := safeEcrecoverInputMemory hf hb hv
  have hfree := ecrecoverInputMemory_free mem ptr p hp
  change memLoad (UInt256.ofNat 64) _ = _ at hfree
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
  rcases ecrecoverPointerArithmetic hb with ⟨h160, h128, h32⟩
  change safeRuntime_block_2586_memory (mem := mem) (x1 := p.s) (x2 := p.r)
    (x3 := p.v) (x8 := p.digest) = _ at hm
  simp only [safeRuntime_block_2586_stack] at hr
  rw [← safeRuntime_block_2586_memory, hm] at hr
  simp only [hfree, hf, h160, h128, h32] at hr
  exact ⟨_, aw', k', C', hr⟩

end Benchmarks.Safe
