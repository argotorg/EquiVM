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

/-- Final stack for bytecode block summary `attesterRuntime_block_359`. -/
def attesterRuntime_block_359_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 359. -/
theorem attesterRuntime_block_359 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 359) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 361) (attesterRuntime_block_359_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 2) (C + ((5))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 321) rfl) 30 359 rfl [x0, x1] h
  have r := e.run 2 [] 2 rfl rfl hstack trivial
  exact RD.normalizeCounters r.rd (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_359_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 359) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 361) (attesterRuntime_block_359_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_359 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_361`. -/
def attesterRuntime_block_361_stack {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 361. -/
theorem attesterRuntime_block_361 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 361) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 367) (attesterRuntime_block_361_stack (x1 := x1) (R := R)) mem aw rdata σ (k + 5) (C + ((11))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 361) rfl) 0 361 rfl [x0, x1, x2] h
  have r := e.run 5 [] 3 rfl rfl hstack trivial
  exact RD.normalizeCounters r.rd (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_361_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 361) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 367) (attesterRuntime_block_361_stack (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_361 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 367. -/
theorem attesterRuntime_block_367_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x2)) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 367) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 762) (x0 :: x1 :: x2 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 367) rfl) 0 367 rfl [x0, x1, x2] h
  have r := e.run 6 [] 5 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiTX hcond (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 762) rfl rfl) 5 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_367_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x2)) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 367) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 762) (x0 :: x1 :: x2 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_367_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 367. -/
theorem attesterRuntime_block_367_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x2)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 367) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 376) (x0 :: x1 :: x2 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 367) rfl) 0 367 rfl [x0, x1, x2] h
  have r := e.run 6 [] 5 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiNTX hcond 5 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_367_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x2)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 367) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 376) (x0 :: x1 :: x2 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_367_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_376_taken`. -/
def attesterRuntime_block_376_taken_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x3 :: x4 :: (UInt256.ofNat 0) :: (UInt256.ofNat ee.calldata.size) :: x0 :: x1 :: x2 :: x3 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 376. -/
theorem attesterRuntime_block_376_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.lt x0 x3) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 376) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 396) (attesterRuntime_block_376_taken_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ (k + 10) (C + ((36))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 367) rfl) 7 376 rfl [x0, x1, x2, x3, x4] h
  have r := e.run 9 [] 12 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiTX hcond (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 396) rfl rfl) 12 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_376_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.lt x0 x3) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 376) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 396) (attesterRuntime_block_376_taken_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_376_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_376_fallthrough`. -/
def attesterRuntime_block_376_fallthrough_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x3 :: x4 :: (UInt256.ofNat 0) :: (UInt256.ofNat ee.calldata.size) :: x0 :: x1 :: x2 :: x3 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 376. -/
theorem attesterRuntime_block_376_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.lt x0 x3) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 376) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 389) (attesterRuntime_block_376_fallthrough_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ (k + 10) (C + ((36))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 367) rfl) 7 376 rfl [x0, x1, x2, x3, x4] h
  have r := e.run 9 [] 12 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiNTX hcond 12 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_376_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.lt x0 x3) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 376) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 389) (attesterRuntime_block_376_fallthrough_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_376_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_389`. -/
def attesterRuntime_block_389_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 396) :: R)

/-- Automatically generated RD summary for bytecode block at pc 389. -/
theorem attesterRuntime_block_389 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 389) R mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2743) (attesterRuntime_block_389_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 367) rfl) 17 389 rfl [] h
  have r := e.run 2 [] 2 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpX (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 2743) rfl rfl) 2 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_389_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 389) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2743) (attesterRuntime_block_389_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_389 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_396`. -/
def attesterRuntime_block_396_stack {x0 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: (x2 + (UInt256.mul (UInt256.ofNat 32) x0)) :: (UInt256.ofNat 414) :: R)

/-- Automatically generated RD summary for bytecode block at pc 396. -/
theorem attesterRuntime_block_396 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 396) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2790) (attesterRuntime_block_396_stack (x0 := x0) (x2 := x2) (R := R)) mem aw rdata σ (k + 13) (C + ((43))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 396) rfl) 0 396 rfl [x0, x1, x2] h
  have r := e.run 12 [] 4 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpX (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 2790) rfl rfl) 4 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_396_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 396) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2790) (attesterRuntime_block_396_stack (x0 := x0) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_396 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_414_taken`. -/
def attesterRuntime_block_414_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 414. -/
theorem attesterRuntime_block_414_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.ofNat 0) x0) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 414) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 479) (attesterRuntime_block_414_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 13) (C + ((42))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 414) rfl) 0 414 rfl [x0, x1, x2, x3] h
  have r := e.run 12 [] 5 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiTX hcond (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 479) rfl rfl) 5 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_414_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.ofNat 0) x0) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 414) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 479) (attesterRuntime_block_414_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_414_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_414_fallthrough`. -/
def attesterRuntime_block_414_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 414. -/
theorem attesterRuntime_block_414_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.ofNat 0) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 414) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 430) (attesterRuntime_block_414_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 13) (C + ((42))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 414) rfl) 0 414 rfl [x0, x1, x2, x3] h
  have r := e.run 12 [] 5 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiNTX hcond 5 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_414_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.ofNat 0) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 414) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 430) (attesterRuntime_block_414_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_414_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 430. -/
theorem attesterRuntime_block_430 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 430) R mem aw rdata σ k C)
    : RDrev (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) g s0 := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 414) rfl) 13 430 rfl [] h
  have r := e.run 13 [] 3 rfl rfl hstack trivial
  exact r.rev 3 rfl hstack

/-- Final stack for bytecode block summary `attesterRuntime_block_479_taken`. -/
def attesterRuntime_block_479_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.ofNat 0) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 479. -/
theorem attesterRuntime_block_479_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt x0 (UInt256.ofNat 18446744073709551615))) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 479) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 506) (attesterRuntime_block_479_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 9) (C + ((32))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 479) rfl) 0 479 rfl [x0] h
  have r := e.run 8 [] 5 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiTX hcond (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 506) rfl rfl) 5 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_479_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt x0 (UInt256.ofNat 18446744073709551615))) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 479) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 506) (attesterRuntime_block_479_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_479_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_479_fallthrough`. -/
def attesterRuntime_block_479_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.ofNat 0) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 479. -/
theorem attesterRuntime_block_479_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt x0 (UInt256.ofNat 18446744073709551615))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 479) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 499) (attesterRuntime_block_479_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 9) (C + ((32))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 479) rfl) 0 479 rfl [x0] h
  have r := e.run 8 [] 5 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiNTX hcond 5 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_479_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt x0 (UInt256.ofNat 18446744073709551615))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 479) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 499) (attesterRuntime_block_479_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_479_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_499`. -/
def attesterRuntime_block_499_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 506) :: R)

/-- Automatically generated RD summary for bytecode block at pc 499. -/
theorem attesterRuntime_block_499 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 499) R mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2696) (attesterRuntime_block_499_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 479) rfl) 9 499 rfl [] h
  have r := e.run 2 [] 2 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpX (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 2696) rfl rfl) 2 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_499_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 499) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2696) (attesterRuntime_block_499_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_499 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_506_taken`. -/
def attesterRuntime_block_506_taken_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (memLoad (UInt256.ofNat 64) mem) :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_506_taken`. -/
def attesterRuntime_block_506_taken_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (((memLoad (UInt256.ofNat 64) mem) + ((UInt256.ofNat 32) + (UInt256.mul (UInt256.ofNat 32) x0))).toByteArray.write 0 (x0.toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 506. -/
theorem attesterRuntime_block_506_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 506) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 575) (attesterRuntime_block_506_taken_stack (mem := mem) (x0 := x0) (R := R)) (attesterRuntime_block_506_taken_memory (mem := mem) (x0 := x0)) (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 20) (C + ((67) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 506) rfl) 0 506 rfl [x0] h
  have r := e.run 19 [] 4 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiTX hcond (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 575) rfl rfl) 4 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_506_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 506) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 575) (attesterRuntime_block_506_taken_stack (mem := mem) (x0 := x0) (R := R)) (attesterRuntime_block_506_taken_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_506_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_506_fallthrough`. -/
def attesterRuntime_block_506_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (memLoad (UInt256.ofNat 64) mem) :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_506_fallthrough`. -/
def attesterRuntime_block_506_fallthrough_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (((memLoad (UInt256.ofNat 64) mem) + ((UInt256.ofNat 32) + (UInt256.mul (UInt256.ofNat 32) x0))).toByteArray.write 0 (x0.toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 506. -/
theorem attesterRuntime_block_506_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 506) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 532) (attesterRuntime_block_506_fallthrough_stack (mem := mem) (x0 := x0) (R := R)) (attesterRuntime_block_506_fallthrough_memory (mem := mem) (x0 := x0)) (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 20) (C + ((67) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 506) rfl) 0 506 rfl [x0] h
  have r := e.run 19 [] 4 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiNTX hcond 4 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_506_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 506) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 532) (attesterRuntime_block_506_fallthrough_stack (mem := mem) (x0 := x0) (R := R)) (attesterRuntime_block_506_fallthrough_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_506_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_532`. -/
def attesterRuntime_block_532_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 32) + x1) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 532. -/
theorem attesterRuntime_block_532 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 532) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 536) (attesterRuntime_block_532_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 3) (C + ((9))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 506) rfl) 20 532 rfl [x0, x1] h
  have r := e.run 3 [] 4 rfl rfl hstack trivial
  exact RD.normalizeCounters r.rd (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_532_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 532) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 536) (attesterRuntime_block_532_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_532 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_536_taken`. -/
def attesterRuntime_block_536_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 32) + x0) :: (UInt256.sub x1 (UInt256.ofNat 1)) :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_536_taken`. -/
def attesterRuntime_block_536_taken_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((memLoad (UInt256.ofNat 64) mem).toByteArray.write 0 ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.ofNat 0).toByteArray.write 0 (((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 64) mem)).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) x0.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 536. -/
theorem attesterRuntime_block_536_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sub x1 (UInt256.ofNat 1)) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 536) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 536) (attesterRuntime_block_536_taken_stack (x0 := x0) (x1 := x1) (R := R)) (attesterRuntime_block_536_taken_memory (mem := mem) (x0 := x0)) (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)) rdata σ (k + 30) (C + ((95) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 536) rfl) 0 536 rfl [x0, x1] h
  have r := e.run 29 [] 6 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiTX hcond (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 536) rfl rfl) 6 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_536_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sub x1 (UInt256.ofNat 1)) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 536) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 536) (attesterRuntime_block_536_taken_stack (x0 := x0) (x1 := x1) (R := R)) (attesterRuntime_block_536_taken_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_536_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_536_fallthrough`. -/
def attesterRuntime_block_536_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 32) + x0) :: (UInt256.sub x1 (UInt256.ofNat 1)) :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_536_fallthrough`. -/
def attesterRuntime_block_536_fallthrough_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((memLoad (UInt256.ofNat 64) mem).toByteArray.write 0 ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.ofNat 0).toByteArray.write 0 (((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 64) mem)).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) x0.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 536. -/
theorem attesterRuntime_block_536_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sub x1 (UInt256.ofNat 1)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 536) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 573) (attesterRuntime_block_536_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) (attesterRuntime_block_536_fallthrough_memory (mem := mem) (x0 := x0)) (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)) rdata σ (k + 30) (C + ((95) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 536) rfl) 0 536 rfl [x0, x1] h
  have r := e.run 29 [] 6 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiNTX hcond 6 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_536_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sub x1 (UInt256.ofNat 1)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 536) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 573) (attesterRuntime_block_536_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) (attesterRuntime_block_536_fallthrough_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_536_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_573`. -/
def attesterRuntime_block_573_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 573. -/
theorem attesterRuntime_block_573 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 573) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 575) (attesterRuntime_block_573_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 2) (C + ((5))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 536) rfl) 30 573 rfl [x0, x1] h
  have r := e.run 2 [] 2 rfl rfl hstack trivial
  exact RD.normalizeCounters r.rd (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_573_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 573) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 575) (attesterRuntime_block_573_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_573 hstack h)
  exact ⟨_, k', C', h'⟩

end attesterRuntimeBlocks
