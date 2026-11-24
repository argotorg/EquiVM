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

/-- Automatically generated RD summary for bytecode block at pc 134. -/
theorem attesterRuntime_block_134 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 134) (x0 :: R) mem aw rdata σ k C)
    : RDret (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) g s0 σ (mem.readWithPadding (memLoad (UInt256.ofNat 64) mem).toNat (UInt256.sub x0 (memLoad (UInt256.ofNat 64) mem)).toNat) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 134) rfl) 0 134 rfl [x0] h
  have r := e.run 7 [] 3 rfl rfl hstack trivial
  exact r.ret 3 rfl hstack

/-- Final stack for bytecode block summary `attesterRuntime_block_143`. -/
def attesterRuntime_block_143_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 4) :: (UInt256.ofNat ee.calldata.size) :: (UInt256.ofNat 157) :: (UInt256.ofNat 162) :: R)

/-- Automatically generated RD summary for bytecode block at pc 143. -/
theorem attesterRuntime_block_143 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 143) R mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2662) (attesterRuntime_block_143_stack (ee := ee) (R := R)) mem aw rdata σ (k + 7) (C + ((23))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 143) rfl) 0 143 rfl [] h
  have r := e.run 6 [] 5 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpX (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 2662) rfl rfl) 5 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_143_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 143) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2662) (attesterRuntime_block_143_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_143 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 157. -/
theorem attesterRuntime_block_157 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 157) R mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1884) R mem aw rdata σ (k + 3) (C + ((12))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 157) rfl) 0 157 rfl [] h
  have r := e.run 2 [] 1 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpX (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 1884) rfl rfl) 1 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_157_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 157) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1884) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_157 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_162`. -/
def attesterRuntime_block_162_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)) :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_162`. -/
def attesterRuntime_block_162_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 162. -/
theorem attesterRuntime_block_162 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 162) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 134) (attesterRuntime_block_162_stack (mem := mem) (R := R)) (attesterRuntime_block_162_memory (mem := mem) (x0 := x0)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) rdata σ (k + 10) (C + ((33) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 162) rfl) 0 162 rfl [x0] h
  have r := e.run 9 [] 3 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpX (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 134) rfl rfl) 3 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_162_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 162) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 134) (attesterRuntime_block_162_stack (mem := mem) (R := R)) (attesterRuntime_block_162_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_162 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_176`. -/
def attesterRuntime_block_176_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 4) :: (UInt256.ofNat ee.calldata.size) :: (UInt256.ofNat 190) :: (UInt256.ofNat 100) :: R)

/-- Automatically generated RD summary for bytecode block at pc 176. -/
theorem attesterRuntime_block_176 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 176) R mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2662) (attesterRuntime_block_176_stack (ee := ee) (R := R)) mem aw rdata σ (k + 7) (C + ((23))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 176) rfl) 0 176 rfl [] h
  have r := e.run 6 [] 5 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpX (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 2662) rfl rfl) 5 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_176_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 176) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2662) (attesterRuntime_block_176_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_176 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 190. -/
theorem attesterRuntime_block_190 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 190) R mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2187) R mem aw rdata σ (k + 3) (C + ((12))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 190) rfl) 0 190 rfl [] h
  have r := e.run 2 [] 1 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpX (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 2187) rfl rfl) 1 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_190_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 190) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2187) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_190 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_195_taken`. -/
def attesterRuntime_block_195_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x2) :: x2 :: x0 :: x1 :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 195. -/
theorem attesterRuntime_block_195_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero x2) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 195) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 209) (attesterRuntime_block_195_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 7) (C + ((26))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 195) rfl) 0 195 rfl [x0, x1, x2] h
  have r := e.run 6 [] 7 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiTX hcond (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 209) rfl rfl) 7 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_195_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero x2) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 195) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 209) (attesterRuntime_block_195_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_195_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_195_fallthrough`. -/
def attesterRuntime_block_195_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x2) :: x2 :: x0 :: x1 :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 195. -/
theorem attesterRuntime_block_195_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero x2) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 195) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 204) (attesterRuntime_block_195_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 7) (C + ((26))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 195) rfl) 0 195 rfl [x0, x1, x2] h
  have r := e.run 6 [] 7 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiNTX hcond 7 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_195_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero x2) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 195) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 204) (attesterRuntime_block_195_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_195_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_204`. -/
def attesterRuntime_block_204_stack {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (UInt256.eq x2 x1)) :: x1 :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 204. -/
theorem attesterRuntime_block_204 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 204) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 209) (attesterRuntime_block_204_stack (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 5) (C + ((14))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 195) rfl) 7 204 rfl [x0, x1, x2] h
  have r := e.run 5 [] 4 rfl rfl hstack trivial
  exact RD.normalizeCounters r.rd (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_204_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 204) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 209) (attesterRuntime_block_204_stack (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_204 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_209_taken`. -/
def attesterRuntime_block_209_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 209. -/
theorem attesterRuntime_block_209_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 209) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 264) (attesterRuntime_block_209_taken_stack (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 209) rfl) 0 209 rfl [x0] h
  have r := e.run 3 [] 2 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiTX hcond (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 264) rfl rfl) 2 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_209_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 209) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 264) (attesterRuntime_block_209_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_209_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_209_fallthrough`. -/
def attesterRuntime_block_209_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 209. -/
theorem attesterRuntime_block_209_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 209) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 215) (attesterRuntime_block_209_fallthrough_stack (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 209) rfl) 0 209 rfl [x0] h
  have r := e.run 3 [] 2 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiNTX hcond 2 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_209_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 209) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 215) (attesterRuntime_block_209_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_209_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 215. -/
theorem attesterRuntime_block_215 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 215) R mem aw rdata σ k C)
    : RDrev (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) g s0 := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 209) rfl) 4 215 rfl [] h
  have r := e.run 13 [] 3 rfl rfl hstack trivial
  exact r.rev 3 rfl hstack

/-- Final stack for bytecode block summary `attesterRuntime_block_264_taken`. -/
def attesterRuntime_block_264_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.ofNat 0) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 264. -/
theorem attesterRuntime_block_264_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt x0 (UInt256.ofNat 18446744073709551615))) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 264) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 291) (attesterRuntime_block_264_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 9) (C + ((32))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 264) rfl) 0 264 rfl [x0] h
  have r := e.run 8 [] 5 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiTX hcond (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 291) rfl rfl) 5 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_264_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt x0 (UInt256.ofNat 18446744073709551615))) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 264) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 291) (attesterRuntime_block_264_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_264_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_264_fallthrough`. -/
def attesterRuntime_block_264_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.ofNat 0) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 264. -/
theorem attesterRuntime_block_264_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt x0 (UInt256.ofNat 18446744073709551615))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 264) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 284) (attesterRuntime_block_264_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 9) (C + ((32))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 264) rfl) 0 264 rfl [x0] h
  have r := e.run 8 [] 5 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiNTX hcond 5 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_264_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt x0 (UInt256.ofNat 18446744073709551615))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 264) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 284) (attesterRuntime_block_264_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_264_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_284`. -/
def attesterRuntime_block_284_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 291) :: R)

/-- Automatically generated RD summary for bytecode block at pc 284. -/
theorem attesterRuntime_block_284 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 284) R mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2696) (attesterRuntime_block_284_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 264) rfl) 9 284 rfl [] h
  have r := e.run 2 [] 2 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpX (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 2696) rfl rfl) 2 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_284_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 284) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2696) (attesterRuntime_block_284_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_284 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_291_taken`. -/
def attesterRuntime_block_291_taken_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (memLoad (UInt256.ofNat 64) mem) :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_291_taken`. -/
def attesterRuntime_block_291_taken_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (((memLoad (UInt256.ofNat 64) mem) + ((UInt256.ofNat 32) + (UInt256.mul (UInt256.ofNat 32) x0))).toByteArray.write 0 (x0.toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 291. -/
theorem attesterRuntime_block_291_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 291) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 361) (attesterRuntime_block_291_taken_stack (mem := mem) (x0 := x0) (R := R)) (attesterRuntime_block_291_taken_memory (mem := mem) (x0 := x0)) (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 20) (C + ((67) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 291) rfl) 0 291 rfl [x0] h
  have r := e.run 19 [] 4 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiTX hcond (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 361) rfl rfl) 4 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_291_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 291) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 361) (attesterRuntime_block_291_taken_stack (mem := mem) (x0 := x0) (R := R)) (attesterRuntime_block_291_taken_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_291_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_291_fallthrough`. -/
def attesterRuntime_block_291_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (memLoad (UInt256.ofNat 64) mem) :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_291_fallthrough`. -/
def attesterRuntime_block_291_fallthrough_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (((memLoad (UInt256.ofNat 64) mem) + ((UInt256.ofNat 32) + (UInt256.mul (UInt256.ofNat 32) x0))).toByteArray.write 0 (x0.toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 291. -/
theorem attesterRuntime_block_291_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 291) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 317) (attesterRuntime_block_291_fallthrough_stack (mem := mem) (x0 := x0) (R := R)) (attesterRuntime_block_291_fallthrough_memory (mem := mem) (x0 := x0)) (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 20) (C + ((67) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 291) rfl) 0 291 rfl [x0] h
  have r := e.run 19 [] 4 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiNTX hcond 4 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_291_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 291) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 317) (attesterRuntime_block_291_fallthrough_stack (mem := mem) (x0 := x0) (R := R)) (attesterRuntime_block_291_fallthrough_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_291_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_317`. -/
def attesterRuntime_block_317_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 32) + x1) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 317. -/
theorem attesterRuntime_block_317 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 317) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 321) (attesterRuntime_block_317_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 3) (C + ((9))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 291) rfl) 20 317 rfl [x0, x1] h
  have r := e.run 3 [] 4 rfl rfl hstack trivial
  exact RD.normalizeCounters r.rd (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_317_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 317) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 321) (attesterRuntime_block_317_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_317 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_321_taken`. -/
def attesterRuntime_block_321_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 32) + x0) :: (UInt256.sub x1 (UInt256.ofNat 1)) :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_321_taken`. -/
def attesterRuntime_block_321_taken_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((memLoad (UInt256.ofNat 64) mem).toByteArray.write 0 ((UInt256.ofNat 96).toByteArray.write 0 ((UInt256.ofNat 0).toByteArray.write 0 (((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 64) mem)).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) x0.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 321. -/
theorem attesterRuntime_block_321_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sub x1 (UInt256.ofNat 1)) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 321) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 321) (attesterRuntime_block_321_taken_stack (x0 := x0) (x1 := x1) (R := R)) (attesterRuntime_block_321_taken_memory (mem := mem) (x0 := x0)) (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)) rdata σ (k + 30) (C + ((95) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 321) rfl) 0 321 rfl [x0, x1] h
  have r := e.run 29 [] 6 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiTX hcond (Benchmarks.EAS.Attester.Listing.jumpdest_code immWords (t := 321) rfl rfl) 6 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_321_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sub x1 (UInt256.ofNat 1)) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 321) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 321) (attesterRuntime_block_321_taken_stack (x0 := x0) (x1 := x1) (R := R)) (attesterRuntime_block_321_taken_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_321_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_321_fallthrough`. -/
def attesterRuntime_block_321_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 32) + x0) :: (UInt256.sub x1 (UInt256.ofNat 1)) :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_321_fallthrough`. -/
def attesterRuntime_block_321_fallthrough_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((memLoad (UInt256.ofNat 64) mem).toByteArray.write 0 ((UInt256.ofNat 96).toByteArray.write 0 ((UInt256.ofNat 0).toByteArray.write 0 (((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 64) mem)).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) x0.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 321. -/
theorem attesterRuntime_block_321_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sub x1 (UInt256.ofNat 1)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 321) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 359) (attesterRuntime_block_321_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) (attesterRuntime_block_321_fallthrough_memory (mem := mem) (x0 := x0)) (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)) rdata σ (k + 30) (C + ((95) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.Listing.decodes_code immWords (t := 321) rfl) 0 321 rfl [x0, x1] h
  have r := e.run 29 [] 6 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiNTX hcond 6 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_321_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sub x1 (UInt256.ofNat 1)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 321) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 359) (attesterRuntime_block_321_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) (attesterRuntime_block_321_fallthrough_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_321_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

end attesterRuntimeBlocks
