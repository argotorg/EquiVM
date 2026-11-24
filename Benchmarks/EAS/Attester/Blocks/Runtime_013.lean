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

/-- Final stack for bytecode block summary `attesterRuntime_block_3624`. -/
def attesterRuntime_block_3624_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 3631) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3624. -/
theorem attesterRuntime_block_3624 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3624) R mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2696) (attesterRuntime_block_3624_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3605) rfl) 9 3624 rfl [] h
  have r := e.run 2 [] 2 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpX (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 2696) rfl rfl) 2 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3624_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3624) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2696) (attesterRuntime_block_3624_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3624 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3631_taken`. -/
def attesterRuntime_block_3631_taken_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (((memLoad (UInt256.ofNat 64) mem) + (UInt256.land ((UInt256.shiftLeft x0 (UInt256.ofNat 5)) + (UInt256.ofNat 63)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) :: (memLoad (UInt256.ofNat 64) mem) :: (UInt256.shiftLeft x0 (UInt256.ofNat 5)) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3631. -/
theorem attesterRuntime_block_3631_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.gt ((memLoad (UInt256.ofNat 64) mem) + (UInt256.land ((UInt256.shiftLeft x0 (UInt256.ofNat 5)) + (UInt256.ofNat 63)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) (UInt256.ofNat 18446744073709551615)) (UInt256.lt ((memLoad (UInt256.ofNat 64) mem) + (UInt256.land ((UInt256.shiftLeft x0 (UInt256.ofNat 5)) + (UInt256.ofNat 63)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) (memLoad (UInt256.ofNat 64) mem)))) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3631) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3706) (attesterRuntime_block_3631_taken_stack (mem := mem) (x0 := x0) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 23) (C + ((74) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3631) rfl) 0 3631 rfl [x0] h
  have r := e.run 22 [] 7 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiTX hcond (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 3706) rfl rfl) 7 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3631_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.gt ((memLoad (UInt256.ofNat 64) mem) + (UInt256.land ((UInt256.shiftLeft x0 (UInt256.ofNat 5)) + (UInt256.ofNat 63)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) (UInt256.ofNat 18446744073709551615)) (UInt256.lt ((memLoad (UInt256.ofNat 64) mem) + (UInt256.land ((UInt256.shiftLeft x0 (UInt256.ofNat 5)) + (UInt256.ofNat 63)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) (memLoad (UInt256.ofNat 64) mem)))) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3631) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3706) (attesterRuntime_block_3631_taken_stack (mem := mem) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3631_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3631_fallthrough`. -/
def attesterRuntime_block_3631_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (((memLoad (UInt256.ofNat 64) mem) + (UInt256.land ((UInt256.shiftLeft x0 (UInt256.ofNat 5)) + (UInt256.ofNat 63)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) :: (memLoad (UInt256.ofNat 64) mem) :: (UInt256.shiftLeft x0 (UInt256.ofNat 5)) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3631. -/
theorem attesterRuntime_block_3631_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.gt ((memLoad (UInt256.ofNat 64) mem) + (UInt256.land ((UInt256.shiftLeft x0 (UInt256.ofNat 5)) + (UInt256.ofNat 63)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) (UInt256.ofNat 18446744073709551615)) (UInt256.lt ((memLoad (UInt256.ofNat 64) mem) + (UInt256.land ((UInt256.shiftLeft x0 (UInt256.ofNat 5)) + (UInt256.ofNat 63)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) (memLoad (UInt256.ofNat 64) mem)))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3631) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3699) (attesterRuntime_block_3631_fallthrough_stack (mem := mem) (x0 := x0) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 23) (C + ((74) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3631) rfl) 0 3631 rfl [x0] h
  have r := e.run 22 [] 7 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiNTX hcond 7 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3631_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.gt ((memLoad (UInt256.ofNat 64) mem) + (UInt256.land ((UInt256.shiftLeft x0 (UInt256.ofNat 5)) + (UInt256.ofNat 63)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) (UInt256.ofNat 18446744073709551615)) (UInt256.lt ((memLoad (UInt256.ofNat 64) mem) + (UInt256.land ((UInt256.shiftLeft x0 (UInt256.ofNat 5)) + (UInt256.ofNat 63)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) (memLoad (UInt256.ofNat 64) mem)))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3631) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3699) (attesterRuntime_block_3631_fallthrough_stack (mem := mem) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3631_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3699`. -/
def attesterRuntime_block_3699_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 3706) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3699. -/
theorem attesterRuntime_block_3699 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3699) R mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2696) (attesterRuntime_block_3699_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3631) rfl) 23 3699 rfl [] h
  have r := e.run 2 [] 2 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpX (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 2696) rfl rfl) 2 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3699_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3699) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2696) (attesterRuntime_block_3699_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3699 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3706_taken`. -/
def attesterRuntime_block_3706_taken_stack {x1 : UInt256} {x2 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x1 + (UInt256.ofNat 32)) :: x1 :: x2 :: ((UInt256.ofNat 32) + (x4 + x2)) :: x4 :: x5 :: x6 :: x7 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_3706_taken`. -/
def attesterRuntime_block_3706_taken_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x3 : UInt256} : ByteArray :=
  (x3.toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) x1.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3706. -/
theorem attesterRuntime_block_3706_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt ((UInt256.ofNat 32) + (x4 + x2)) x7)) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3706) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3736) (attesterRuntime_block_3706_taken_stack (x1 := x1) (x2 := x2) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) (attesterRuntime_block_3706_taken_memory (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) rdata σ (k + 22) (C + ((71) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3706) rfl) 0 3706 rfl [x0, x1, x2, x3, x4, x5, x6, x7] h
  have r := e.run 21 [] 10 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiTX hcond (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 3736) rfl rfl) 10 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3706_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt ((UInt256.ofNat 32) + (x4 + x2)) x7)) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3706) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3736) (attesterRuntime_block_3706_taken_stack (x1 := x1) (x2 := x2) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) (attesterRuntime_block_3706_taken_memory (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3706_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3706_fallthrough`. -/
def attesterRuntime_block_3706_fallthrough_stack {x1 : UInt256} {x2 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x1 + (UInt256.ofNat 32)) :: x1 :: x2 :: ((UInt256.ofNat 32) + (x4 + x2)) :: x4 :: x5 :: x6 :: x7 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_3706_fallthrough`. -/
def attesterRuntime_block_3706_fallthrough_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x3 : UInt256} : ByteArray :=
  (x3.toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) x1.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3706. -/
theorem attesterRuntime_block_3706_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt ((UInt256.ofNat 32) + (x4 + x2)) x7)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3706) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3732) (attesterRuntime_block_3706_fallthrough_stack (x1 := x1) (x2 := x2) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) (attesterRuntime_block_3706_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) rdata σ (k + 22) (C + ((71) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3706) rfl) 0 3706 rfl [x0, x1, x2, x3, x4, x5, x6, x7] h
  have r := e.run 21 [] 10 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiNTX hcond 10 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3706_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt ((UInt256.ofNat 32) + (x4 + x2)) x7)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3706) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3732) (attesterRuntime_block_3706_fallthrough_stack (x1 := x1) (x2 := x2) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) (attesterRuntime_block_3706_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3706_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3732. -/
theorem attesterRuntime_block_3732 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3732) R mem aw rdata σ k C)
    : RDrev (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) g s0 := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3706) rfl) 22 3732 rfl [] h
  have r := e.run 2 [] 2 rfl rfl hstack trivial
  exact r.rev 2 rfl hstack

/-- Final stack for bytecode block summary `attesterRuntime_block_3736`. -/
def attesterRuntime_block_3736_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x1 :: x2 :: x3 :: (x4 + (UInt256.ofNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3736. -/
theorem attesterRuntime_block_3736 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3736) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3743) (attesterRuntime_block_3736_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ (k + 6) (C + ((15))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3736) rfl) 0 3736 rfl [x0, x1, x2, x3, x4] h
  have r := e.run 6 [] 7 rfl rfl hstack trivial
  exact RD.normalizeCounters r.rd (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3736_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3736) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3743) (attesterRuntime_block_3736_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3736 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3743. -/
theorem attesterRuntime_block_3743_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x4 x3)) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3743) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3771) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3743) rfl) 0 3743 rfl [x0, x1, x2, x3, x4] h
  have r := e.run 6 [] 7 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiTX hcond (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 3771) rfl rfl) 7 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3743_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x4 x3)) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3743) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3771) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3743_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3743. -/
theorem attesterRuntime_block_3743_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x4 x3)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3743) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3752) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3743) rfl) 0 3743 rfl [x0, x1, x2, x3, x4] h
  have r := e.run 6 [] 7 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiNTX hcond 7 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3743_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x4 x3)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3743) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3752) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3743_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3752`. -/
def attesterRuntime_block_3752_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 32) + x0) :: x1 :: (memLoad x4 mem) :: x3 :: ((UInt256.ofNat 32) + x4) :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_3752`. -/
def attesterRuntime_block_3752_memory {mem : ByteArray} {x0 : UInt256} {x4 : UInt256} : ByteArray :=
  ((memLoad x4 mem).toByteArray.write 0 mem x0.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3752. -/
theorem attesterRuntime_block_3752 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3752) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3743) (attesterRuntime_block_3752_stack (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3) (x4 := x4) (R := R)) (attesterRuntime_block_3752_memory (mem := mem) (x0 := x0) (x4 := x4)) (M (M aw x4 (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)) rdata σ (k + 16) (C + ((52) + (memExpansionCost aw x4 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x4 (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3743) rfl) 7 3752 rfl [x0, x1, x2, x3, x4] h
  have r := e.run 15 [] 8 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpX (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 3743) rfl rfl) 8 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3752_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3752) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3743) (attesterRuntime_block_3752_stack (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3) (x4 := x4) (R := R)) (attesterRuntime_block_3752_memory (mem := mem) (x0 := x0) (x4 := x4)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3752 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3771`. -/
def attesterRuntime_block_3771_stack {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3771. -/
theorem attesterRuntime_block_3771 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains x8 = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3771) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 x8 (attesterRuntime_block_3771_stack (x1 := x1) (R := R)) mem aw rdata σ (k + 11) (C + ((29))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3771) rfl) 0 3771 rfl [x0, x1, x2, x3, x4, x5, x6, x7, x8] h
  have r := e.run 10 [] 9 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpX hvalid 9 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3771_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains x8 = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3771) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 x8 (attesterRuntime_block_3771_stack (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3771 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3782`. -/
def attesterRuntime_block_3782_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (x1 + (UInt256.ofNat 32)) ((memLoad x1 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32)).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)) :: (x0 + (UInt256.ofNat 96)) :: (UInt256.ofNat 3819) :: (memLoad (x1 + (UInt256.ofNat 32)) ((memLoad x1 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32)).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)) :: (UInt256.ofNat 0) :: x0 :: x1 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_3782`. -/
def attesterRuntime_block_3782_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((UInt256.ofNat 64).toByteArray.write 0 ((memLoad x1 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32)).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32) (x0 + (UInt256.ofNat 64)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3782. -/
theorem attesterRuntime_block_3782 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3782) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3109) (attesterRuntime_block_3782_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (attesterRuntime_block_3782_memory (mem := mem) (x0 := x0) (x1 := x1)) (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) rdata σ (k + 27) (C + ((84) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3782) rfl) 0 3782 rfl [x0, x1] h
  have r := e.run 26 [] 8 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpX (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 3109) rfl rfl) 8 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3782_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3782) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3109) (attesterRuntime_block_3782_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (attesterRuntime_block_3782_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3782 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3819`. -/
def attesterRuntime_block_3819_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3819. -/
theorem attesterRuntime_block_3819 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains x5 = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3819) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 x5 (attesterRuntime_block_3819_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 8) (C + ((23))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3819) rfl) 0 3819 rfl [x0, x1, x2, x3, x4, x5] h
  have r := e.run 7 [] 6 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpX hvalid 6 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3819_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains x5 = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3819) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 x5 (attesterRuntime_block_3819_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3819 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3827_taken`. -/
def attesterRuntime_block_3827_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3827. -/
theorem attesterRuntime_block_3827_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3827) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3845) (attesterRuntime_block_3827_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((35))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3827) rfl) 0 3827 rfl [x0, x1] h
  have r := e.run 9 [] 6 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiTX hcond (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 3845) rfl rfl) 6 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3827_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3827) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3845) (attesterRuntime_block_3827_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3827_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3827_fallthrough`. -/
def attesterRuntime_block_3827_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3827. -/
theorem attesterRuntime_block_3827_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3827) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3841) (attesterRuntime_block_3827_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((35))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3827) rfl) 0 3827 rfl [x0, x1] h
  have r := e.run 9 [] 6 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiNTX hcond 6 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3827_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3827) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3841) (attesterRuntime_block_3827_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3827_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3841. -/
theorem attesterRuntime_block_3841 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3841) R mem aw rdata σ k C)
    : RDrev (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) g s0 := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3827) rfl) 10 3841 rfl [] h
  have r := e.run 2 [] 2 rfl rfl hstack trivial
  exact r.rev 2 rfl hstack

/-- Final stack for bytecode block summary `attesterRuntime_block_3845`. -/
def attesterRuntime_block_3845_stack {mem : ByteArray} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad x1 mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3845. -/
theorem attesterRuntime_block_3845 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains x3 = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3845) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 x3 (attesterRuntime_block_3845_stack (mem := mem) (x1 := x1) (R := R)) mem (M aw x1 (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((22) + (memExpansionCost aw x1 (⟨32⟩ : UInt256)))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3845) rfl) 0 3845 rfl [x0, x1, x2, x3] h
  have r := e.run 6 [] 4 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpX hvalid 4 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3845_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains x3 = true)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3845) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 x3 (attesterRuntime_block_3845_stack (mem := mem) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3845 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3852. -/
theorem attesterRuntime_block_3852 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3852) R mem aw rdata σ k C)
    : RDinvalid (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) g s0 := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 3845) rfl) 7 3852 rfl [] h
  exact e.invalid

end attesterRuntimeBlocks
