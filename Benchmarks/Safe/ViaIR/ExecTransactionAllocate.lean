import Benchmarks.Safe.ViaIR.ExecTransactionExecuteSource
import Benchmarks.Safe.ViaIR.CalldataBufferMemory
import Benchmarks.Safe.ViaIR.IRMemoryAllocation
import Benchmarks.Safe.ViaIR.Blocks.Runtime_034

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

def execCallSaved (p : ExecTransactionInput) (before guard hash : UInt256)
    (R : List UInt256) : List UInt256 :=
  [UInt256.isZero p.tx.gasPrice, UInt256.ofNat p.tx.refundReceiver.val,
    UInt256.land guard solcAddrMask, UInt256.ofNat p.tx.gasToken.val, hash, before, ⟨0⟩] ++ R

def execAllocatedStack (p : ExecTransactionInput) (ptr : Nat)
    (before gasLeft guard hash : UInt256) (R : List UInt256) : List UInt256 :=
  [UInt256.ofNat ptr, execCallGas p gasLeft, UInt256.ofNat p.tx.target.val, ⟨0⟩, ⟨0⟩] ++
    execCallSaved p before guard hash R

set_option maxRecDepth 2000 in
theorem safeCalldataBufferAllocateEvidence (len : Nat)
    {I g s0 σ k C aw mem rdata src ptr} {ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7208⟩
      (UInt256.ofNat src :: UInt256.ofNat len ::
        UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hp : ptr + 64 + len < UInt256.size)
    (hn : len < 2 ^ 64) (hd : src + len ≤ I.calldata.size)
    (hcd : I.calldata.size < UInt256.size)
    (hov : R.length + 12 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    (¬ptr + 32 + ABI.paddedSize len < 2 ^ 64 ∧ RDrev fork safeBytecode g s0) ∨ ∃ aw' k' C',
      ptr + 32 + ABI.paddedSize len < 2 ^ 64 ∧
      RD fork safeBytecode I g s0 ret (UInt256.ofNat ptr :: R)
        (calldataBufferMemory I.calldata mem src ptr len len
          (ptr + 32 + ABI.paddedSize len)) aw' rdata σ k' C' := by
  have hpad : ABI.paddedSize len ≤ len + 31 := by
    unfold ABI.paddedSize; omega
  have hadd (a b : Nat) (hh : a + b < UInt256.size) :
      UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) := wordOfNatAdd _ _ hh
  have ht (n : Nat) (hh : n < UInt256.size) : (UInt256.ofNat n).toNat = n :=
    ulit_toNat' _ hh
  have hmax : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have hround : ABI.paddedSize (32 + ABI.paddedSize len) =
      32 + ABI.paddedSize len := by unfold ABI.paddedSize; omega
  have h₁ := safeRuntime_block_7208 (by simp; omega) (by jump_dest) h
  have h₂ := safeRuntime_block_7181_fallthrough (by simp; omega) (by
    rw [hmax, ugt_zero (by rw [ht len (by omega), ht _ (by decide)]; omega)]
    rfl) h₁
  have h₃ := safeRuntime_block_7196 (by simp; omega) (by jump_dest) h₂
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
  have h₄ := safeRuntime_block_7220 (by simp; omega) (by jump_dest) h₃
  simp only [safeRuntime_block_7220_stack,
    u256_add_comm (UInt256.ofNat 31), u256_land_comm (UInt256.lnot (UInt256.ofNat 31)),
    roundedCalldataLengthMask len (by omega), hf,
    hadd 32 (ABI.paddedSize len) (by omega)] at h₄
  by_cases hcap : ptr + 32 + ABI.paddedSize len < 2 ^ 64
  swap
  · obtain hr | ⟨_, _, _, hc, _⟩ := safeIRAllocateTrace h₄
      (by change 32 + ABI.paddedSize len + 31 < 2 ^ 256; omega)
      (by rw [hround]; omega) (by simp; omega) (by jump_dest)
    · exact .inl ⟨hcap, hr⟩
    · rw [hround, ← Nat.add_assoc] at hc
      exact False.elim (hcap hc)
  obtain ⟨aw₅, k₅, C₅, h₅⟩ := safeIRAllocateValidTrace h₄
    (by change 32 + ABI.paddedSize len + 31 < 2 ^ 256; omega)
    (by rw [hround, ← Nat.add_assoc]; exact hcap) (by simp; omega) (by jump_dest)
  rw [hround, ← Nat.add_assoc] at h₅
  obtain ⟨aw₆, k₆, C₆, h₆⟩ := safeRuntime_block_7234_fallthrough_packed (by simp; omega)
    (by rw [hadd src len (by omega),
      ugt_zero (by rw [ht _ (by omega), ht _ hcd]; exact hd)]; rfl) h₅
  obtain ⟨aw₇, k₇, C₇, h₇⟩ := safeRuntime_block_7248_packed (by simp; omega) hret h₆
  simp only [safeRuntime_block_7248_stack, safeRuntime_block_7248_memory,
    safeRuntime_block_7234_fallthrough_memory,
    hadd ptr 32 (by omega), hadd ptr len (by omega),
    hadd (ptr + len) 32 (by omega), ht src (by omega),
    ht len (by omega), ht ptr (by omega), ht (ptr + 32) (by omega),
    ht (ptr + len + 32) (by omega)] at h₇
  refine .inr ⟨aw₇, k₇, C₇, hcap, ?_⟩
  simpa only [calldataBufferMemory, calldataBufferHeader, Reasoning.Theory.writeWord,
    Nat.add_right_comm ptr len 32] using h₇

theorem safeCalldataBufferAllocate (len : Nat)
    {I g s0 σ k C aw mem rdata src ptr} {ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7208⟩
      (UInt256.ofNat src :: UInt256.ofNat len ::
        UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hp : ptr + 64 + len < UInt256.size)
    (hn : len < 2 ^ 64) (hd : src + len ≤ I.calldata.size)
    (hcd : I.calldata.size < UInt256.size)
    (hov : R.length + 12 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    RDrev fork safeBytecode g s0 ∨ ∃ aw' k' C',
      ptr + 32 + ABI.paddedSize len < 2 ^ 64 ∧
      RD fork safeBytecode I g s0 ret (UInt256.ofNat ptr :: R)
        (calldataBufferMemory I.calldata mem src ptr len len
          (ptr + 32 + ABI.paddedSize len)) aw' rdata σ k' C' := by
  exact (safeCalldataBufferAllocateEvidence len h hf hp hn hd hcd hov hret).imp And.right id


set_option maxRecDepth 2000 in
theorem safeExecAllocate (p : ExecTransactionInput)
    {I g s0 σ k C aw mem rdata src ptr} {ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7208⟩
      (UInt256.ofNat src :: UInt256.ofNat p.tx.payload.size ::
        UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hp : ptr + 64 + p.tx.payload.size < UInt256.size)
    (hn : p.tx.payload.size < 2 ^ 64) (hd : src + p.tx.payload.size ≤ I.calldata.size)
    (hcd : I.calldata.size < UInt256.size)
    (hov : R.length + 12 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    RDrev fork safeBytecode g s0 ∨ ∃ aw' k' C',
      ptr + 32 + ABI.paddedSize p.tx.payload.size < 2 ^ 64 ∧
      RD fork safeBytecode I g s0 ret (UInt256.ofNat ptr :: R)
        (calldataBufferMemory I.calldata mem src ptr p.tx.payload.size p.tx.payload.size
          (ptr + 32 + ABI.paddedSize p.tx.payload.size)) aw' rdata σ k' C' :=
  safeCalldataBufferAllocate p.tx.payload.size h hf hp hn hd hcd hov hret

end Benchmarks.Safe.ViaIR
