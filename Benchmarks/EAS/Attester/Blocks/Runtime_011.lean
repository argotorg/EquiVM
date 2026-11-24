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

/-- Final stack for bytecode block summary `attesterRuntime_block_2843_fallthrough`. -/
def attesterRuntime_block_2843_fallthrough_stack {ee : ExecutionEnv} {x0 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x3 + x0) :: (uInt256OfByteArray (ee.calldata.readBytes (x3 + x0).toNat 32)) :: x2 :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2843. -/
theorem attesterRuntime_block_2843_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (x3 + x0).toNat 32)) (UInt256.ofNat 18446744073709551615))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2843) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2866) (attesterRuntime_block_2843_fallthrough_stack (ee := ee) (x0 := x0) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 13) (C + ((43))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 2843) rfl) 0 2843 rfl [x0, x1, x2, x3] h
  have r := e.run 12 [] 6 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiNTX hcond 6 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_2843_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (x3 + x0).toNat 32)) (UInt256.ofNat 18446744073709551615))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2843) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2866) (attesterRuntime_block_2843_fallthrough_stack (ee := ee) (x0 := x0) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_2843_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2866. -/
theorem attesterRuntime_block_2866 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2866) R mem aw rdata σ k C)
    : RDrev (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) g s0 := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 2843) rfl) 13 2866 rfl [] h
  have r := e.run 2 [] 2 rfl rfl hstack trivial
  exact r.rev 2 rfl hstack

/-- Final stack for bytecode block summary `attesterRuntime_block_2870_taken`. -/
def attesterRuntime_block_2870_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: ((UInt256.ofNat 32) + x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 2870. -/
theorem attesterRuntime_block_2870_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.sgt ((UInt256.ofNat 32) + x0) (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.shiftLeft x1 (UInt256.ofNat 5))))) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2870) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2475) (attesterRuntime_block_2870_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 16) (C + ((51))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 2870) rfl) 0 2870 rfl [x0, x1, x2] h
  have r := e.run 15 [] 4 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiTX hcond (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 2475) rfl rfl) 4 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_2870_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.sgt ((UInt256.ofNat 32) + x0) (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.shiftLeft x1 (UInt256.ofNat 5))))) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2870) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2475) (attesterRuntime_block_2870_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_2870_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_2870_fallthrough`. -/
def attesterRuntime_block_2870_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: ((UInt256.ofNat 32) + x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 2870. -/
theorem attesterRuntime_block_2870_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.sgt ((UInt256.ofNat 32) + x0) (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.shiftLeft x1 (UInt256.ofNat 5))))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2870) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2890) (attesterRuntime_block_2870_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 16) (C + ((51))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 2870) rfl) 0 2870 rfl [x0, x1, x2] h
  have r := e.run 15 [] 4 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiNTX hcond 4 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_2870_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.sgt ((UInt256.ofNat 32) + x0) (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.shiftLeft x1 (UInt256.ofNat 5))))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2870) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2890) (attesterRuntime_block_2870_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_2870_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2890. -/
theorem attesterRuntime_block_2890 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2890) R mem aw rdata σ k C)
    : RDrev (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) g s0 := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 2870) rfl) 16 2890 rfl [] h
  have r := e.run 2 [] 2 rfl rfl hstack trivial
  exact r.rev 2 rfl hstack

/-- Final stack for bytecode block summary `attesterRuntime_block_2894`. -/
def attesterRuntime_block_2894_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: (x1 + (UInt256.ofNat 32)) :: (memLoad x1 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32)) :: (x0 + (UInt256.ofNat 64)) :: ((x0 + (UInt256.shiftLeft (memLoad x1 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 5))) + (UInt256.ofNat 64)) :: (UInt256.ofNat 0) :: x0 :: x1 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_2894`. -/
def attesterRuntime_block_2894_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((memLoad x1 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32)).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 2894. -/
theorem attesterRuntime_block_2894 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2894) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2934) (attesterRuntime_block_2894_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (attesterRuntime_block_2894_memory (mem := mem) (x0 := x0) (x1 := x1)) (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 32) (C + ((92) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 2894) rfl) 0 2894 rfl [x0, x1] h
  have r := e.run 32 [] 9 rfl rfl hstack trivial
  exact RD.normalizeCounters r.rd (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_2894_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2894) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2934) (attesterRuntime_block_2894_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (attesterRuntime_block_2894_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_2894 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2934. -/
theorem attesterRuntime_block_2934_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x2)) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2934) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3097) (x0 :: x1 :: x2 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 2934) rfl) 0 2934 rfl [x0, x1, x2] h
  have r := e.run 6 [] 5 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiTX hcond (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 3097) rfl rfl) 5 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_2934_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x2)) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2934) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3097) (x0 :: x1 :: x2 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_2934_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2934. -/
theorem attesterRuntime_block_2934_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x2)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2934) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2943) (x0 :: x1 :: x2 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 2934) rfl) 0 2934 rfl [x0, x1, x2] h
  have r := e.run 6 [] 5 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiNTX hcond 5 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_2934_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x2)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2934) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2943) (x0 :: x1 :: x2 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_2934_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_2943`. -/
def attesterRuntime_block_2943_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (memLoad ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32))) ((memLoad (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32)) ((UInt256.ofNat 64).toByteArray.write 0 ((memLoad (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32) (x4 + (UInt256.ofNat 32)).toNat 32)) :: (x4 + (UInt256.ofNat 96)) :: (UInt256.ofNat 0) :: ((UInt256.ofNat 32) + (memLoad ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32))) ((memLoad (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32))) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_2943`. -/
def attesterRuntime_block_2943_memory {mem : ByteArray} {x1 : UInt256} {x3 : UInt256} {x4 : UInt256} {x6 : UInt256} : ByteArray :=
  ((memLoad (memLoad ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32))) ((memLoad (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32)) ((UInt256.ofNat 64).toByteArray.write 0 ((memLoad (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32) (x4 + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 64).toByteArray.write 0 ((memLoad (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32) (x4 + (UInt256.ofNat 32)).toNat 32) (x4 + (UInt256.ofNat 64)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 2943. -/
theorem attesterRuntime_block_2943 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2943) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3021) (attesterRuntime_block_2943_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) (attesterRuntime_block_2943_memory (mem := mem) (x1 := x1) (x3 := x3) (x4 := x4) (x6 := x6)) (M (M (M (M (M (M (M (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)) (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32))) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (memLoad ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32))) ((memLoad (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) rdata σ (k + 42) (C + ((126) + (memExpansionCost aw x3 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)) (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)) (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32))) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)) (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32))) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)) (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32))) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (memLoad ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32))) ((memLoad (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)) (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32))) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (memLoad ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32))) ((memLoad (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 2934) rfl) 7 2943 rfl [x0, x1, x2, x3, x4, x5, x6] h
  have r := e.run 42 [] 12 rfl rfl hstack trivial
  exact RD.normalizeCounters r.rd (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_2943_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2943) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3021) (attesterRuntime_block_2943_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) (attesterRuntime_block_2943_memory (mem := mem) (x1 := x1) (x3 := x3) (x4 := x4) (x6 := x6)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_2943 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3021. -/
theorem attesterRuntime_block_3021_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x2 x0)) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3021) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3073) (x0 :: x1 :: x2 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3021) rfl) 0 3021 rfl [x0, x1, x2] h
  have r := e.run 6 [] 5 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiTX hcond (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 3073) rfl rfl) 5 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3021_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x2 x0)) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3021) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3073) (x0 :: x1 :: x2 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3021_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3021. -/
theorem attesterRuntime_block_3021_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x2 x0)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3021) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3030) (x0 :: x1 :: x2 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3021) rfl) 0 3021 rfl [x0, x1, x2] h
  have r := e.run 6 [] 5 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiNTX hcond 5 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3021_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x2 x0)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3021) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3030) (x0 :: x1 :: x2 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3021_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `attesterRuntime_block_3030`. -/
def attesterRuntime_block_3030_memory {mem : ByteArray} {x1 : UInt256} {x3 : UInt256} : ByteArray :=
  ((memLoad ((UInt256.ofNat 32) + (memLoad x3 mem)) ((memLoad (memLoad x3 mem) mem).toByteArray.write 0 mem x1.toNat 32)).toByteArray.write 0 ((memLoad (memLoad x3 mem) mem).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3030. -/
theorem attesterRuntime_block_3030 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3030) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3050) (x0 :: x1 :: x2 :: x3 :: R) (attesterRuntime_block_3030_memory (mem := mem) (x1 := x1) (x3 := x3)) (M (M (M (M (M aw x3 (⟨32⟩ : UInt256)) (memLoad x3 mem) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad x3 mem)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 17) (C + ((56) + (memExpansionCost aw x3 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x3 (⟨32⟩ : UInt256)) (memLoad x3 mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x3 (⟨32⟩ : UInt256)) (memLoad x3 mem) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw x3 (⟨32⟩ : UInt256)) (memLoad x3 mem) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad x3 mem)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw x3 (⟨32⟩ : UInt256)) (memLoad x3 mem) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad x3 mem)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3021) rfl) 7 3030 rfl [x0, x1, x2, x3] h
  have r := e.run 16 [] 9 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpX (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 3050) rfl rfl) 9 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3030_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3030) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3050) (x0 :: x1 :: x2 :: x3 :: R) (attesterRuntime_block_3030_memory (mem := mem) (x1 := x1) (x3 := x3)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3030 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3050`. -/
def attesterRuntime_block_3050_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (x1 + (UInt256.ofNat 64)) :: (x2 + (UInt256.ofNat 1)) :: (x3 + (UInt256.ofNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3050. -/
theorem attesterRuntime_block_3050 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3050) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3021) (attesterRuntime_block_3050_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 18) (C + ((54))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3050) rfl) 0 3050 rfl [x0, x1, x2, x3] h
  have r := e.run 17 [] 6 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpX (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 3021) rfl rfl) 6 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3050_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3050) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3021) (attesterRuntime_block_3050_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3050 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3073`. -/
def attesterRuntime_block_3073_stack {x1 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 1) + x4) :: ((UInt256.ofNat 32) + x5) :: x6 :: ((UInt256.ofNat 32) + x7) :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3073. -/
theorem attesterRuntime_block_3073 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3073) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2934) (attesterRuntime_block_3073_stack (x1 := x1) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw rdata σ (k + 20) (C + ((59))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3073) rfl) 0 3073 rfl [x0, x1, x2, x3, x4, x5, x6, x7, x8] h
  have r := e.run 19 [] 9 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpX (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 2934) rfl rfl) 9 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3073_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3073) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2934) (attesterRuntime_block_3073_stack (x1 := x1) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3073 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3097`. -/
def attesterRuntime_block_3097_stack {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3097. -/
theorem attesterRuntime_block_3097 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains x8 = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3097) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 x8 (attesterRuntime_block_3097_stack (x4 := x4) (R := R)) mem aw rdata σ (k + 12) (C + ((32))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3097) rfl) 0 3097 rfl [x0, x1, x2, x3, x4, x5, x6, x7, x8] h
  have r := e.run 11 [] 9 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpX hvalid 9 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3097_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains x8 = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3097) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 x8 (attesterRuntime_block_3097_stack (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3097 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3109`. -/
def attesterRuntime_block_3109_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: (memLoad (memLoad (x0 + (UInt256.ofNat 128)) ((memLoad (x0 + (UInt256.ofNat 96)) ((UInt256.isZero (UInt256.isZero (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32)).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32) (x1 + (UInt256.ofNat 96)).toNat 32)) ((UInt256.ofNat 192).toByteArray.write 0 ((memLoad (x0 + (UInt256.ofNat 96)) ((UInt256.isZero (UInt256.isZero (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32)).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32) (x1 + (UInt256.ofNat 96)).toNat 32) (x1 + (UInt256.ofNat 128)).toNat 32)) :: (memLoad (x0 + (UInt256.ofNat 128)) ((memLoad (x0 + (UInt256.ofNat 96)) ((UInt256.isZero (UInt256.isZero (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32)).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32) (x1 + (UInt256.ofNat 96)).toNat 32)) :: (UInt256.ofNat 0) :: x0 :: x1 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_3109`. -/
def attesterRuntime_block_3109_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((memLoad (memLoad (x0 + (UInt256.ofNat 128)) ((memLoad (x0 + (UInt256.ofNat 96)) ((UInt256.isZero (UInt256.isZero (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32)).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32) (x1 + (UInt256.ofNat 96)).toNat 32)) ((UInt256.ofNat 192).toByteArray.write 0 ((memLoad (x0 + (UInt256.ofNat 96)) ((UInt256.isZero (UInt256.isZero (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32)).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32) (x1 + (UInt256.ofNat 96)).toNat 32) (x1 + (UInt256.ofNat 128)).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 192).toByteArray.write 0 ((memLoad (x0 + (UInt256.ofNat 96)) ((UInt256.isZero (UInt256.isZero (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32)).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32) (x1 + (UInt256.ofNat 96)).toNat 32) (x1 + (UInt256.ofNat 128)).toNat 32) (x1 + (UInt256.ofNat 192)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3109. -/
theorem attesterRuntime_block_3109 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3109) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3202) (attesterRuntime_block_3109_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (attesterRuntime_block_3109_memory (mem := mem) (x0 := x0) (x1 := x1)) (M (M (M (M (M (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (memLoad (x0 + (UInt256.ofNat 128)) ((memLoad (x0 + (UInt256.ofNat 96)) ((UInt256.isZero (UInt256.isZero (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32)).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32) (x1 + (UInt256.ofNat 96)).toNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) rdata σ (k + 53) (C + ((157) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (memLoad (x0 + (UInt256.ofNat 128)) ((memLoad (x0 + (UInt256.ofNat 96)) ((UInt256.isZero (UInt256.isZero (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32)).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32) (x1 + (UInt256.ofNat 96)).toNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (memLoad (x0 + (UInt256.ofNat 128)) ((memLoad (x0 + (UInt256.ofNat 96)) ((UInt256.isZero (UInt256.isZero (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32)).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32) (x1 + (UInt256.ofNat 96)).toNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3109) rfl) 0 3109 rfl [x0, x1] h
  have r := e.run 53 [] 8 rfl rfl hstack trivial
  exact RD.normalizeCounters r.rd (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3109_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3109) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3202) (attesterRuntime_block_3109_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (attesterRuntime_block_3109_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3109 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3202. -/
theorem attesterRuntime_block_3202_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x1)) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3202) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3231) (x0 :: x1 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3202) rfl) 0 3202 rfl [x0, x1] h
  have r := e.run 6 [] 4 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiTX hcond (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 3231) rfl rfl) 4 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3202_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x1)) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3202) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3231) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3202_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3202. -/
theorem attesterRuntime_block_3202_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x1)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3202) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3211) (x0 :: x1 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3202) rfl) 0 3202 rfl [x0, x1] h
  have r := e.run 6 [] 4 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiNTX hcond 4 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3202_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x1)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3202) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3211) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3202_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3211`. -/
def attesterRuntime_block_3211_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 32) + x0) :: x1 :: x2 :: x3 :: x4 :: x5 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_3211`. -/
def attesterRuntime_block_3211_memory {mem : ByteArray} {x0 : UInt256} {x2 : UInt256} {x5 : UInt256} : ByteArray :=
  ((memLoad ((UInt256.ofNat 32) + (x2 + x0)) mem).toByteArray.write 0 mem ((x0 + x5) + (UInt256.ofNat 224)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3211. -/
theorem attesterRuntime_block_3211 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3211) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3202) (attesterRuntime_block_3211_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) (attesterRuntime_block_3211_memory (mem := mem) (x0 := x0) (x2 := x2) (x5 := x5)) (M (M aw ((UInt256.ofNat 32) + (x2 + x0)) (⟨32⟩ : UInt256)) ((x0 + x5) + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) rdata σ (k + 16) (C + ((53) + (memExpansionCost aw ((UInt256.ofNat 32) + (x2 + x0)) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw ((UInt256.ofNat 32) + (x2 + x0)) (⟨32⟩ : UInt256)) ((x0 + x5) + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3202) rfl) 7 3211 rfl [x0, x1, x2, x3, x4, x5] h
  have r := e.run 15 [] 11 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpX (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 3202) rfl rfl) 11 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3211_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3211) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3202) (attesterRuntime_block_3211_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) (attesterRuntime_block_3211_memory (mem := mem) (x0 := x0) (x2 := x2) (x5 := x5)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3211 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3231`. -/
def attesterRuntime_block_3231_stack {x1 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (((x5 + (UInt256.land (x1 + (UInt256.ofNat 31)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) + (UInt256.ofNat 224)) :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_3231`. -/
def attesterRuntime_block_3231_memory {mem : ByteArray} {x1 : UInt256} {x4 : UInt256} {x5 : UInt256} : ByteArray :=
  ((memLoad (x4 + (UInt256.ofNat 160)) ((UInt256.ofNat 0).toByteArray.write 0 mem ((x5 + x1) + (UInt256.ofNat 224)).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 0).toByteArray.write 0 mem ((x5 + x1) + (UInt256.ofNat 224)).toNat 32) (x5 + (UInt256.ofNat 160)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3231. -/
theorem attesterRuntime_block_3231 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains x6 = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3231) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 x6 (attesterRuntime_block_3231_stack (x1 := x1) (x5 := x5) (R := R)) (attesterRuntime_block_3231_memory (mem := mem) (x1 := x1) (x4 := x4) (x5 := x5)) (M (M (M aw ((x5 + x1) + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) rdata σ (k + 35) (C + ((102) + (memExpansionCost aw ((x5 + x1) + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw ((x5 + x1) + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw ((x5 + x1) + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3231) rfl) 0 3231 rfl [x0, x1, x2, x3, x4, x5, x6] h
  have r := e.run 34 [] 10 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpX hvalid 10 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3231_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains x6 = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3231) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 x6 (attesterRuntime_block_3231_stack (x1 := x1) (x5 := x5) (R := R)) (attesterRuntime_block_3231_memory (mem := mem) (x1 := x1) (x4 := x4) (x5 := x5)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3231 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

end attesterRuntimeBlocks
