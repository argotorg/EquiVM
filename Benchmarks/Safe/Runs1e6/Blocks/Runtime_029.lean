import Reasoning.Reach
import Benchmarks.Safe.Runs1e6.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.Runs1e6.RuntimeBlocks

/-- Final stack for bytecode block summary `safeRuntime_block_7990_fallthrough`. -/
def safeRuntime_block_7990_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 7990. -/
theorem safeRuntime_block_7990_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero (UInt256.lt x0 x3)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 7990) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8002) (safeRuntime_block_7990_fallthrough_stack (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ x2 x0) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap2 (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r5⟩ := RD.sstore r4 hperm (by native_decide) (by evm_ov)
  have r6 := r5.pop (by native_decide) (by evm_ov)
  have r7 := r6.lt (by native_decide) (by evm_ov)
  have r8 := r7.iszero (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 8042) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8002)) r10 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_7990_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero (UInt256.lt x0 x3)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 7990) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8002) (safeRuntime_block_7990_fallthrough_stack (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ x2 x0) k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_7990_fallthrough hstack hperm hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8002`. -/
def safeRuntime_block_8002_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 32261206942343601317040813096072770565208774546709327032244551300047664316416) :: (UInt256.ofNat 8042) :: R)

/-- Automatically generated RD summary for bytecode block at pc 8002. -/
theorem safeRuntime_block_8002 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 8421) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8002) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8421) (safeRuntime_block_8002_stack (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 8042) (by native_decide) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 32261206942343601317040813096072770565208774546709327032244551300047664316416) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 8421) (by native_decide) (by evm_ov)
  have r4 := r3.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8421)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8002_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 8421) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8002) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8421) (safeRuntime_block_8002_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8002 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8042`. -/
def safeRuntime_block_8042_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x2 :: (UInt256.ofNat 8052) :: x0 :: x1 :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 8042. -/
theorem safeRuntime_block_8042 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 10761) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8042) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 10761) (safeRuntime_block_8042_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 6) (C + ((21))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 8052) (by native_decide) (by evm_ov)
  have r3 := r2.dup4 (by native_decide) (by evm_ov)
  have r4 := r3.dup4 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 10761) (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10761)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8042_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 10761) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8042) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 10761) (safeRuntime_block_8042_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8042 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `safeRuntime_block_8052_taken`. -/
def safeRuntime_block_8052_taken_memory {mem : ByteArray} {x1 : UInt256} {x2 : UInt256} : ByteArray :=
  ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x2).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8052. -/
theorem safeRuntime_block_8052_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.eq ((sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x2).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (UInt256.lor (UInt256.land (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x2).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) (UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))))) (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.land (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960) ((sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x2).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (UInt256.lor (UInt256.land (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x2).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) (UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 4) (⟨0⟩ : UInt256))) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 8214) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8052) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8214) (x0 :: x1 :: x2 :: R) (safeRuntime_block_8052_taken_memory (mem := mem) (x1 := x1) (x2 := x2)) (M (M (M (M (M (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x2).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x2).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (UInt256.lor (UInt256.land (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x2).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) (UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))))) (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.land (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960) ((sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x2).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (UInt256.lor (UInt256.land (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x2).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) (UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.and (by native_decide) (by evm_ov)
  have r6 := r5.push0 (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := RD.genMstore r8 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r12 := RD.genMstore r11 (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r14 := r13.dup1 (by native_decide) (by evm_ov)
  have r15 := r14.dup3 (by native_decide) (by evm_ov)
  have r16 := RD.genKeccak256 r15 (by native_decide) (by evm_ov)
  have r17 := r16.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r18⟩ := RD.sload r17 (by native_decide) (by evm_ov)
  have r19 := r18.dup9 (by native_decide) (by evm_ov)
  have r20 := r19.dup7 (by native_decide) (by evm_ov)
  have r21 := r20.and (by native_decide) (by evm_ov)
  have r22 := r21.dup5 (by native_decide) (by evm_ov)
  have r23 := RD.genMstore r22 (by native_decide) (by evm_ov)
  have r24 := r23.dup3 (by native_decide) (by evm_ov)
  have r25 := r24.dup5 (by native_decide) (by evm_ov)
  have r26 := RD.genKeccak256 r25 (by native_decide) (by evm_ov)
  have r27 := r26.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r28⟩ := RD.sload r27 (by native_decide) (by evm_ov)
  have r29 := r28.swap2 (by native_decide) (by evm_ov)
  have r30 := r29.swap1 (by native_decide) (by evm_ov)
  have r31 := r30.swap7 (by native_decide) (by evm_ov)
  have r32 := r31.and (by native_decide) (by evm_ov)
  have r33 := r32.pushConst (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r34 := r33.swap2 (by native_decide) (by evm_ov)
  have r35 := r34.dup3 (by native_decide) (by evm_ov)
  have r36 := r35.and (by native_decide) (by evm_ov)
  have r37 := r36.or (by native_decide) (by evm_ov)
  have r38 := r37.swap1 (by native_decide) (by evm_ov)
  have r39 := r38.swap6 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r40⟩ := RD.sstore r39 hperm (by native_decide) (by evm_ov)
  have r41 := r40.dup4 (by native_decide) (by evm_ov)
  have r42 := r41.dup4 (by native_decide) (by evm_ov)
  have r43 := RD.genMstore r42 (by native_decide) (by evm_ov)
  have r44 := r43.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r45⟩ := RD.sload r44 (by native_decide) (by evm_ov)
  have r46 := r45.swap1 (by native_decide) (by evm_ov)
  have r47 := r46.swap5 (by native_decide) (by evm_ov)
  have r48 := r47.and (by native_decide) (by evm_ov)
  have r49 := r48.swap1 (by native_decide) (by evm_ov)
  have r50 := r49.swap4 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r51⟩ := RD.sstore r50 hperm (by native_decide) (by evm_ov)
  have r52 := r51.swap2 (by native_decide) (by evm_ov)
  have r53 := RD.genMload r52 (by native_decide) (by evm_ov)
  have r54 := r53.swap1 (by native_decide) (by evm_ov)
  have r55 := r54.swap2 (by native_decide) (by evm_ov)
  have r56 := r55.pushConst (UInt256.ofNat 112549260719532661292031762456511781745355494859329508612328448226810028203695) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r57 := r56.swap2 (by native_decide) (by evm_ov)
  have r58 := RD.genLog2 r57 (by native_decide) hperm (by evm_ov)
  have r59 := r58.dup1 (by native_decide) (by evm_ov)
  have r60 := r59.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r61⟩ := RD.sload r60 (by native_decide) (by evm_ov)
  have r62 := r61.eq (by native_decide) (by evm_ov)
  have r63 := r62.push2 (UInt256.ofNat 8214) (by native_decide) (by evm_ov)
  have r64 := r63.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8214)) r64 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8052_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.eq ((sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x2).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (UInt256.lor (UInt256.land (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x2).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) (UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))))) (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.land (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960) ((sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x2).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (UInt256.lor (UInt256.land (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x2).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) (UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 4) (⟨0⟩ : UInt256))) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 8214) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8052) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8214) (x0 :: x1 :: x2 :: R) (safeRuntime_block_8052_taken_memory (mem := mem) (x1 := x1) (x2 := x2)) aw' rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x2).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (UInt256.lor (UInt256.land (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x2).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) (UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))))) (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.land (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960) ((sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x2).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (UInt256.lor (UInt256.land (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x2).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) (UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_8052_taken hstack hperm hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `safeRuntime_block_8052_fallthrough`. -/
def safeRuntime_block_8052_fallthrough_memory {mem : ByteArray} {x1 : UInt256} {x2 : UInt256} : ByteArray :=
  ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x2).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8052. -/
theorem safeRuntime_block_8052_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.eq ((sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x2).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (UInt256.lor (UInt256.land (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x2).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) (UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))))) (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.land (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960) ((sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x2).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (UInt256.lor (UInt256.land (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x2).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) (UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 4) (⟨0⟩ : UInt256))) x0) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8052) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8206) (x0 :: x1 :: x2 :: R) (safeRuntime_block_8052_fallthrough_memory (mem := mem) (x1 := x1) (x2 := x2)) (M (M (M (M (M (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x2).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x2).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (UInt256.lor (UInt256.land (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x2).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) (UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))))) (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.land (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960) ((sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x2).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (UInt256.lor (UInt256.land (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x2).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) (UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.and (by native_decide) (by evm_ov)
  have r6 := r5.push0 (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := RD.genMstore r8 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r12 := RD.genMstore r11 (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r14 := r13.dup1 (by native_decide) (by evm_ov)
  have r15 := r14.dup3 (by native_decide) (by evm_ov)
  have r16 := RD.genKeccak256 r15 (by native_decide) (by evm_ov)
  have r17 := r16.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r18⟩ := RD.sload r17 (by native_decide) (by evm_ov)
  have r19 := r18.dup9 (by native_decide) (by evm_ov)
  have r20 := r19.dup7 (by native_decide) (by evm_ov)
  have r21 := r20.and (by native_decide) (by evm_ov)
  have r22 := r21.dup5 (by native_decide) (by evm_ov)
  have r23 := RD.genMstore r22 (by native_decide) (by evm_ov)
  have r24 := r23.dup3 (by native_decide) (by evm_ov)
  have r25 := r24.dup5 (by native_decide) (by evm_ov)
  have r26 := RD.genKeccak256 r25 (by native_decide) (by evm_ov)
  have r27 := r26.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r28⟩ := RD.sload r27 (by native_decide) (by evm_ov)
  have r29 := r28.swap2 (by native_decide) (by evm_ov)
  have r30 := r29.swap1 (by native_decide) (by evm_ov)
  have r31 := r30.swap7 (by native_decide) (by evm_ov)
  have r32 := r31.and (by native_decide) (by evm_ov)
  have r33 := r32.pushConst (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r34 := r33.swap2 (by native_decide) (by evm_ov)
  have r35 := r34.dup3 (by native_decide) (by evm_ov)
  have r36 := r35.and (by native_decide) (by evm_ov)
  have r37 := r36.or (by native_decide) (by evm_ov)
  have r38 := r37.swap1 (by native_decide) (by evm_ov)
  have r39 := r38.swap6 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r40⟩ := RD.sstore r39 hperm (by native_decide) (by evm_ov)
  have r41 := r40.dup4 (by native_decide) (by evm_ov)
  have r42 := r41.dup4 (by native_decide) (by evm_ov)
  have r43 := RD.genMstore r42 (by native_decide) (by evm_ov)
  have r44 := r43.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r45⟩ := RD.sload r44 (by native_decide) (by evm_ov)
  have r46 := r45.swap1 (by native_decide) (by evm_ov)
  have r47 := r46.swap5 (by native_decide) (by evm_ov)
  have r48 := r47.and (by native_decide) (by evm_ov)
  have r49 := r48.swap1 (by native_decide) (by evm_ov)
  have r50 := r49.swap4 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r51⟩ := RD.sstore r50 hperm (by native_decide) (by evm_ov)
  have r52 := r51.swap2 (by native_decide) (by evm_ov)
  have r53 := RD.genMload r52 (by native_decide) (by evm_ov)
  have r54 := r53.swap1 (by native_decide) (by evm_ov)
  have r55 := r54.swap2 (by native_decide) (by evm_ov)
  have r56 := r55.pushConst (UInt256.ofNat 112549260719532661292031762456511781745355494859329508612328448226810028203695) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r57 := r56.swap2 (by native_decide) (by evm_ov)
  have r58 := RD.genLog2 r57 (by native_decide) hperm (by evm_ov)
  have r59 := r58.dup1 (by native_decide) (by evm_ov)
  have r60 := r59.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r61⟩ := RD.sload r60 (by native_decide) (by evm_ov)
  have r62 := r61.eq (by native_decide) (by evm_ov)
  have r63 := r62.push2 (UInt256.ofNat 8214) (by native_decide) (by evm_ov)
  have r64 := r63.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8206)) r64 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8052_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.eq ((sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x2).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (UInt256.lor (UInt256.land (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x2).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) (UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))))) (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.land (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960) ((sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x2).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (UInt256.lor (UInt256.land (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x2).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) (UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 4) (⟨0⟩ : UInt256))) x0) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8052) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8206) (x0 :: x1 :: x2 :: R) (safeRuntime_block_8052_fallthrough_memory (mem := mem) (x1 := x1) (x2 := x2)) aw' rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x2).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (UInt256.lor (UInt256.land (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x2).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) (UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))))) (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.land (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960) ((sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x2).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (UInt256.lor (UInt256.land (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x2).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) (UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x1).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_8052_fallthrough hstack hperm hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8206`. -/
def safeRuntime_block_8206_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.ofNat 8214) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 8206. -/
theorem safeRuntime_block_8206 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 4000) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8206) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4000) (safeRuntime_block_8206_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 8214) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 4000) (by native_decide) (by evm_ov)
  have r4 := r3.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4000)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8206_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 4000) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8206) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 4000) (safeRuntime_block_8206_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8206 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8214`. -/
def safeRuntime_block_8214_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 8214. -/
theorem safeRuntime_block_8214 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains x3 = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8214) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 x3 (safeRuntime_block_8214_stack (R := R)) mem aw rdata σ (k + 5) (C + ((15))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r5 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8214_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains x3 = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8214) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 x3 (safeRuntime_block_8214_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8214 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 8219. -/
theorem safeRuntime_block_8219_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat ee.codeOwner.val) (UInt256.ofNat ee.source.val)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 8267) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8219) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8267) R mem aw rdata σ (k + 6) (C + ((21))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.caller (by native_decide) (by evm_ov)
  have r3 := r2.address (by native_decide) (by evm_ov)
  have r4 := r3.eq (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 8267) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8267)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8219_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat ee.codeOwner.val) (UInt256.ofNat ee.source.val)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 8267) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8219) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8267) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8219_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 8219. -/
theorem safeRuntime_block_8219_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat ee.codeOwner.val) (UInt256.ofNat ee.source.val)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8219) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8227) R mem aw rdata σ (k + 6) (C + ((21))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.caller (by native_decide) (by evm_ov)
  have r3 := r2.address (by native_decide) (by evm_ov)
  have r4 := r3.eq (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 8267) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8227)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8219_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat ee.codeOwner.val) (UInt256.ofNat ee.source.val)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8219) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8227) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8219_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8227`. -/
def safeRuntime_block_8227_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 32261193219730747737365157610562091272216761665402815959093158418310047465472) :: (UInt256.ofNat 8267) :: R)

/-- Automatically generated RD summary for bytecode block at pc 8227. -/
theorem safeRuntime_block_8227 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 8421) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8227) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8421) (safeRuntime_block_8227_stack (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 8267) (by native_decide) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 32261193219730747737365157610562091272216761665402815959093158418310047465472) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 8421) (by native_decide) (by evm_ov)
  have r4 := r3.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8421)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8227_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 8421) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8227) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8421) (safeRuntime_block_8227_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8227 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8267`. -/
def safeRuntime_block_8267_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 8267. -/
theorem safeRuntime_block_8267 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains x0 = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8267) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 x0 (safeRuntime_block_8267_stack (R := R)) mem aw rdata σ (k + 2) (C + ((9))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r2 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8267_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains x0 = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8267) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 x0 (safeRuntime_block_8267_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8267 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8269`. -/
def safeRuntime_block_8269_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.ofNat 8278) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 8269. -/
theorem safeRuntime_block_8269 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 10859) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8269) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 10859) (safeRuntime_block_8269_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 8278) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 10859) (by native_decide) (by evm_ov)
  have r5 := r4.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10859)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8269_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 10859) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8269) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 10859) (safeRuntime_block_8269_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8269 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `safeRuntime_block_8278_taken`. -/
def safeRuntime_block_8278_taken_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x0).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8278. -/
theorem safeRuntime_block_8278_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x0).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 8363) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8278) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8363) (x0 :: R) (safeRuntime_block_8278_taken_memory (mem := mem) (x0 := x0)) (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.and (by native_decide) (by evm_ov)
  have r6 := r5.push0 (by native_decide) (by evm_ov)
  have r7 := r6.swap1 (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := RD.genMstore r8 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r12 := RD.genMstore r11 (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r14 := r13.swap1 (by native_decide) (by evm_ov)
  have r15 := RD.genKeccak256 r14 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r16⟩ := RD.sload r15 (by native_decide) (by evm_ov)
  have r17 := r16.and (by native_decide) (by evm_ov)
  have r18 := r17.iszero (by native_decide) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 8363) (by native_decide) (by evm_ov)
  have r20 := r19.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8363)) r20 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8278_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x0).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 8363) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8278) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8363) (x0 :: R) (safeRuntime_block_8278_taken_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_8278_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `safeRuntime_block_8278_fallthrough`. -/
def safeRuntime_block_8278_fallthrough_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x0).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8278. -/
theorem safeRuntime_block_8278_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x0).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8278) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8323) (x0 :: R) (safeRuntime_block_8278_fallthrough_memory (mem := mem) (x0 := x0)) (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.and (by native_decide) (by evm_ov)
  have r6 := r5.push0 (by native_decide) (by evm_ov)
  have r7 := r6.swap1 (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := RD.genMstore r8 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r12 := RD.genMstore r11 (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r14 := r13.swap1 (by native_decide) (by evm_ov)
  have r15 := RD.genKeccak256 r14 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r16⟩ := RD.sload r15 (by native_decide) (by evm_ov)
  have r17 := r16.and (by native_decide) (by evm_ov)
  have r18 := r17.iszero (by native_decide) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 8363) (by native_decide) (by evm_ov)
  have r20 := r19.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8323)) r20 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8278_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x0).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8278) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8323) (x0 :: R) (safeRuntime_block_8278_fallthrough_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_8278_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8323`. -/
def safeRuntime_block_8323_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 32261206942659538192046484656166524648259785843666012318446198633810597249024) :: (UInt256.ofNat 8363) :: R)

/-- Automatically generated RD summary for bytecode block at pc 8323. -/
theorem safeRuntime_block_8323 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 8421) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8323) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8421) (safeRuntime_block_8323_stack (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 8363) (by native_decide) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 32261206942659538192046484656166524648259785843666012318446198633810597249024) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 8421) (by native_decide) (by evm_ov)
  have r4 := r3.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8421)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8323_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 8421) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8323) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8421) (safeRuntime_block_8323_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8323 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8363`. -/
def safeRuntime_block_8363_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 8363. -/
theorem safeRuntime_block_8363 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains x1 = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8363) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 x1 (safeRuntime_block_8363_stack (R := R)) mem aw rdata σ (k + 3) (C + ((11))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r3 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8363_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains x1 = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8363) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 x1 (safeRuntime_block_8363_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8363 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8366_taken`. -/
def safeRuntime_block_8366_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 8366. -/
theorem safeRuntime_block_8366_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (⟨0⟩ : UInt256) x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 8381) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8366) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8381) (safeRuntime_block_8366_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 7) (C + ((24))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.push0 (by native_decide) (by evm_ov)
  have r5 := r4.sub (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 8381) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8381)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8366_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (⟨0⟩ : UInt256) x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 8381) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8366) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8381) (safeRuntime_block_8366_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8366_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8366_fallthrough`. -/
def safeRuntime_block_8366_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 8366. -/
theorem safeRuntime_block_8366_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (⟨0⟩ : UInt256) x1) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8366) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8375) (safeRuntime_block_8366_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 7) (C + ((24))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.push0 (by native_decide) (by evm_ov)
  have r5 := r4.sub (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 8381) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8375)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8366_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (⟨0⟩ : UInt256) x1) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8366) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8375) (safeRuntime_block_8366_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8366_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8375`. -/
def safeRuntime_block_8375_stack {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: R)

/-- Automatically generated RD summary for bytecode block at pc 8375. -/
theorem safeRuntime_block_8375 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 3225) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8375) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 3225) (safeRuntime_block_8375_stack (R := R)) mem aw rdata σ (k + 4) (C + ((15))) := by
  let r0 := h
  have r1 := r0.pop (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 3225) (by native_decide) (by evm_ov)
  have r4 := r3.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3225)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8375_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 3225) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8375) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 3225) (safeRuntime_block_8375_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8375 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_8381`. -/
def safeRuntime_block_8381_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x1 :: (UInt256.ofNat 8392) :: (⟨0⟩ : UInt256) :: x0 :: x1 :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 8381. -/
theorem safeRuntime_block_8381 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 14623) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8381) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 14623) (safeRuntime_block_8381_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 7) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 8392) (by native_decide) (by evm_ov)
  have r4 := r3.dup4 (by native_decide) (by evm_ov)
  have r5 := r4.dup6 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 14623) (by native_decide) (by evm_ov)
  have r7 := r6.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14623)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_8381_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 14623) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 8381) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 14623) (safeRuntime_block_8381_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_8381 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

end Benchmarks.Safe.Runs1e6.RuntimeBlocks
