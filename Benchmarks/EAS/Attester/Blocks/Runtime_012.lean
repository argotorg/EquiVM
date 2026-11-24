import Reasoning.Reach
import Reasoning.Immutables
import Benchmarks.EAS.Attester.Immutables
import Reasoning.Listing.Run
import Benchmarks.EAS.Attester.Bytecode

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace attesterRuntimeBlocks

open Reasoning.Immutables
set_option maxRecDepth 10000

/-- Final stack for bytecode block summary `attesterRuntime_block_3304`. -/
def attesterRuntime_block_3304_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: (x1 + (UInt256.ofNat 32)) :: (memLoad x1 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32)) :: (x0 + (UInt256.ofNat 64)) :: ((x0 + (UInt256.shiftLeft (memLoad x1 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 5))) + (UInt256.ofNat 64)) :: (UInt256.ofNat 0) :: x0 :: x1 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_3304`. -/
def attesterRuntime_block_3304_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((memLoad x1 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32)).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3304. -/
theorem attesterRuntime_block_3304 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3304) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3344) (attesterRuntime_block_3304_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (attesterRuntime_block_3304_memory (mem := mem) (x0 := x0) (x1 := x1)) (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 32) (C + ((92) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3304) rfl) 0 3304 rfl [x0, x1] h
  have r := e.run 32 [] 9 rfl rfl hstack trivial
  exact RD.normalizeCounters r.rd (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3304_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3304) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3344) (attesterRuntime_block_3304_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (attesterRuntime_block_3304_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3304 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3344. -/
theorem attesterRuntime_block_3344_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x2)) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3344) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3097) (x0 :: x1 :: x2 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3344) rfl) 0 3344 rfl [x0, x1, x2] h
  have r := e.run 6 [] 5 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiTX hcond (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 3097) rfl rfl) 5 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3344_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x2)) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3344) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3097) (x0 :: x1 :: x2 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3344_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3344. -/
theorem attesterRuntime_block_3344_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x2)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3344) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3353) (x0 :: x1 :: x2 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3344) rfl) 0 3344 rfl [x0, x1, x2] h
  have r := e.run 6 [] 5 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiNTX hcond 5 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3344_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x2)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3344) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3353) (x0 :: x1 :: x2 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3344_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3353`. -/
def attesterRuntime_block_3353_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: (memLoad (memLoad ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32))) ((memLoad (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32)) ((UInt256.ofNat 64).toByteArray.write 0 ((memLoad (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32) (x4 + (UInt256.ofNat 32)).toNat 32)) :: (x4 + (UInt256.ofNat 96)) :: ((UInt256.ofNat 96) + (x4 + (UInt256.shiftLeft (memLoad (memLoad ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32))) ((memLoad (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32)) ((UInt256.ofNat 64).toByteArray.write 0 ((memLoad (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32) (x4 + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 5)))) :: ((UInt256.ofNat 32) + (memLoad ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32))) ((memLoad (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32))) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_3353`. -/
def attesterRuntime_block_3353_memory {mem : ByteArray} {x1 : UInt256} {x3 : UInt256} {x4 : UInt256} {x6 : UInt256} : ByteArray :=
  ((memLoad (memLoad ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32))) ((memLoad (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32)) ((UInt256.ofNat 64).toByteArray.write 0 ((memLoad (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32) (x4 + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 64).toByteArray.write 0 ((memLoad (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32) (x4 + (UInt256.ofNat 32)).toNat 32) (x4 + (UInt256.ofNat 64)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3353. -/
theorem attesterRuntime_block_3353 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3353) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3441) (attesterRuntime_block_3353_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) (attesterRuntime_block_3353_memory (mem := mem) (x1 := x1) (x3 := x3) (x4 := x4) (x6 := x6)) (M (M (M (M (M (M (M (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32))) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (memLoad ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32))) ((memLoad (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) rdata σ (k + 51) (C + ((153) + (memExpansionCost aw x3 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32))) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32))) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32))) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (memLoad ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32))) ((memLoad (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32))) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (memLoad ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32))) ((memLoad (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3344) rfl) 7 3353 rfl [x0, x1, x2, x3, x4, x5, x6] h
  have r := e.run 51 [] 12 rfl rfl hstack trivial
  exact RD.normalizeCounters r.rd (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3353_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3353) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3441) (attesterRuntime_block_3353_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) (attesterRuntime_block_3353_memory (mem := mem) (x1 := x1) (x3 := x3) (x4 := x4) (x6 := x6)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3353 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3441. -/
theorem attesterRuntime_block_3441_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x1)) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3441) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3521) (x0 :: x1 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3441) rfl) 0 3441 rfl [x0, x1] h
  have r := e.run 6 [] 4 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiTX hcond (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 3521) rfl rfl) 4 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3441_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x1)) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3441) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3521) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3441_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3441. -/
theorem attesterRuntime_block_3441_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x1)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3441) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3450) (x0 :: x1 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3441) rfl) 0 3441 rfl [x0, x1] h
  have r := e.run 6 [] 4 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiNTX hcond 4 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3441_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x1)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3441) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3450) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3441_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3450`. -/
def attesterRuntime_block_3450_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad x4 (((UInt256.sub x3 x9) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639840)).toByteArray.write 0 mem x2.toNat 32)) :: x3 :: (UInt256.ofNat 3499) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_3450`. -/
def attesterRuntime_block_3450_memory {mem : ByteArray} {x2 : UInt256} {x3 : UInt256} {x9 : UInt256} : ByteArray :=
  (((UInt256.sub x3 x9) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639840)).toByteArray.write 0 mem x2.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3450. -/
theorem attesterRuntime_block_3450 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3450) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3109) (attesterRuntime_block_3450_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (R := R)) (attesterRuntime_block_3450_memory (mem := mem) (x2 := x2) (x3 := x3) (x9 := x9)) (M (M aw x2 (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)) rdata σ (k + 13) (C + ((44) + (memExpansionCost aw x2 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x2 (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3441) rfl) 7 3450 rfl [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9] h
  have r := e.run 12 [] 14 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpX (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 3109) rfl rfl) 14 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3450_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3450) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3109) (attesterRuntime_block_3450_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (R := R)) (attesterRuntime_block_3450_memory (mem := mem) (x2 := x2) (x3 := x3) (x9 := x9)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3450 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3499`. -/
def attesterRuntime_block_3499_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 1) + x1) :: x2 :: ((UInt256.ofNat 32) + x3) :: x0 :: ((UInt256.ofNat 32) + x5) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3499. -/
theorem attesterRuntime_block_3499 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3499) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3441) (attesterRuntime_block_3499_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x5 := x5) (R := R)) mem aw rdata σ (k + 18) (C + ((56))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3499) rfl) 0 3499 rfl [x0, x1, x2, x3, x4, x5] h
  have r := e.run 17 [] 8 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpX (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 3441) rfl rfl) 8 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3499_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3499) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3441) (attesterRuntime_block_3499_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x5 := x5) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3499 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3521`. -/
def attesterRuntime_block_3521_stack {x3 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 1) + x5) :: ((UInt256.ofNat 32) + x6) :: x7 :: ((UInt256.ofNat 32) + x8) :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3521. -/
theorem attesterRuntime_block_3521 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3521) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3344) (attesterRuntime_block_3521_stack (x3 := x3) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) mem aw rdata σ (k + 22) (C + ((64))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3521) rfl) 0 3521 rfl [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9] h
  have r := e.run 21 [] 10 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpX (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 3344) rfl rfl) 10 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3521_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3521) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3344) (attesterRuntime_block_3521_stack (x3 := x3) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3521 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3547_taken`. -/
def attesterRuntime_block_3547_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3547. -/
theorem attesterRuntime_block_3547_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3547) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3565) (attesterRuntime_block_3547_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((35))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3547) rfl) 0 3547 rfl [x0, x1] h
  have r := e.run 9 [] 6 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiTX hcond (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 3565) rfl rfl) 6 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3547_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3547) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3565) (attesterRuntime_block_3547_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3547_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3547_fallthrough`. -/
def attesterRuntime_block_3547_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3547. -/
theorem attesterRuntime_block_3547_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3547) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3561) (attesterRuntime_block_3547_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((35))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3547) rfl) 0 3547 rfl [x0, x1] h
  have r := e.run 9 [] 6 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiNTX hcond 6 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3547_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3547) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3561) (attesterRuntime_block_3547_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3547_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3561. -/
theorem attesterRuntime_block_3561 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3561) R mem aw rdata σ k C)
    : RDrev (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) g s0 := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3547) rfl) 10 3561 rfl [] h
  have r := e.run 2 [] 2 rfl rfl hstack trivial
  exact r.rev 2 rfl hstack

/-- Final stack for bytecode block summary `attesterRuntime_block_3565_taken`. -/
def attesterRuntime_block_3565_taken_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad x1 mem) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3565. -/
theorem attesterRuntime_block_3565_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (memLoad x1 mem) (UInt256.ofNat 18446744073709551615))) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3565) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3588) (attesterRuntime_block_3565_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem (M aw x1 (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((32) + (memExpansionCost aw x1 (⟨32⟩ : UInt256)))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3565) rfl) 0 3565 rfl [x0, x1] h
  have r := e.run 8 [] 5 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiTX hcond (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 3588) rfl rfl) 5 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3565_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (memLoad x1 mem) (UInt256.ofNat 18446744073709551615))) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3565) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3588) (attesterRuntime_block_3565_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3565_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3565_fallthrough`. -/
def attesterRuntime_block_3565_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad x1 mem) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3565. -/
theorem attesterRuntime_block_3565_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (memLoad x1 mem) (UInt256.ofNat 18446744073709551615))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3565) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3584) (attesterRuntime_block_3565_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem (M aw x1 (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((32) + (memExpansionCost aw x1 (⟨32⟩ : UInt256)))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3565) rfl) 0 3565 rfl [x0, x1] h
  have r := e.run 8 [] 5 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiNTX hcond 5 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3565_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (memLoad x1 mem) (UInt256.ofNat 18446744073709551615))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3565) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3584) (attesterRuntime_block_3565_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3565_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3584. -/
theorem attesterRuntime_block_3584 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3584) R mem aw rdata σ k C)
    : RDrev (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) g s0 := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3565) rfl) 9 3584 rfl [] h
  have r := e.run 2 [] 2 rfl rfl hstack trivial
  exact r.rev 2 rfl hstack

/-- Final stack for bytecode block summary `attesterRuntime_block_3588_taken`. -/
def attesterRuntime_block_3588_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x2 + x0) :: x1 :: x2 :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3588. -/
theorem attesterRuntime_block_3588_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sgt x3 ((x2 + x0) + (UInt256.ofNat 31))) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3588) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3605) (attesterRuntime_block_3588_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 10) (C + ((35))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3588) rfl) 0 3588 rfl [x0, x1, x2, x3] h
  have r := e.run 9 [] 6 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiTX hcond (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 3605) rfl rfl) 6 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3588_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sgt x3 ((x2 + x0) + (UInt256.ofNat 31))) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3588) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3605) (attesterRuntime_block_3588_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3588_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3588_fallthrough`. -/
def attesterRuntime_block_3588_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x2 + x0) :: x1 :: x2 :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3588. -/
theorem attesterRuntime_block_3588_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sgt x3 ((x2 + x0) + (UInt256.ofNat 31))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3588) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3601) (attesterRuntime_block_3588_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 10) (C + ((35))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3588) rfl) 0 3588 rfl [x0, x1, x2, x3] h
  have r := e.run 9 [] 6 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiNTX hcond 6 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3588_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sgt x3 ((x2 + x0) + (UInt256.ofNat 31))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3588) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3601) (attesterRuntime_block_3588_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3588_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3601. -/
theorem attesterRuntime_block_3601 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3601) R mem aw rdata σ k C)
    : RDrev (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) g s0 := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3588) rfl) 10 3601 rfl [] h
  have r := e.run 2 [] 2 rfl rfl hstack trivial
  exact r.rev 2 rfl hstack

/-- Final stack for bytecode block summary `attesterRuntime_block_3605_taken`. -/
def attesterRuntime_block_3605_taken_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad x0 mem) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3605. -/
theorem attesterRuntime_block_3605_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (memLoad x0 mem) (UInt256.ofNat 18446744073709551615))) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3605) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3631) (attesterRuntime_block_3605_taken_stack (mem := mem) (x0 := x0) (R := R)) mem (M aw x0 (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((32) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3605) rfl) 0 3605 rfl [x0] h
  have r := e.run 8 [] 4 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiTX hcond (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 3631) rfl rfl) 4 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3605_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (memLoad x0 mem) (UInt256.ofNat 18446744073709551615))) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3605) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3631) (attesterRuntime_block_3605_taken_stack (mem := mem) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3605_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3605_fallthrough`. -/
def attesterRuntime_block_3605_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad x0 mem) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3605. -/
theorem attesterRuntime_block_3605_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (memLoad x0 mem) (UInt256.ofNat 18446744073709551615))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3605) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3624) (attesterRuntime_block_3605_fallthrough_stack (mem := mem) (x0 := x0) (R := R)) mem (M aw x0 (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((32) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3605) rfl) 0 3605 rfl [x0] h
  have r := e.run 8 [] 4 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiNTX hcond 4 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3605_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (memLoad x0 mem) (UInt256.ofNat 18446744073709551615))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3605) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3624) (attesterRuntime_block_3605_fallthrough_stack (mem := mem) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3605_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

end attesterRuntimeBlocks
