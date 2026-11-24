import Reasoning.Reach
import Reasoning.Initcode
import Benchmarks.EAS.Attester.Immutables
import Reasoning.Listing.Run
import Benchmarks.EAS.Attester.CreationBytecode

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace attesterCreationBlocks

set_option maxRecDepth 10000

private abbrev d := Reasoning.Theory.decode_append_left_of_decode Benchmarks.EAS.Attester.attesterCreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left Benchmarks.EAS.Attester.attesterCreationBytecode

/-- Final stack for bytecode block summary `attesterCreation_block_0_taken`. -/
def attesterCreation_block_0_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  (ee.weiValue :: R)

/-- Final memory for bytecode block summary `attesterCreation_block_0_taken`. -/
def attesterCreation_block_0_taken_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 160).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem attesterCreation_block_0_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15) (attesterCreation_block_0_taken_stack (ee := ee) (R := R)) (attesterCreation_block_0_taken_memory (mem := mem)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((30) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.CreationListing.decodes_code tail (t := 0) rfl) 0 0 rfl [] h
  have r := e.run 7 [] 3 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiTX hcond (Benchmarks.EAS.Attester.CreationListing.jumpdest_code tail (t := 15) rfl rfl) 3 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterCreation_block_0_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15) (attesterCreation_block_0_taken_stack (ee := ee) (R := R)) (attesterCreation_block_0_taken_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterCreation_block_0_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterCreation_block_0_fallthrough`. -/
def attesterCreation_block_0_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  (ee.weiValue :: R)

/-- Final memory for bytecode block summary `attesterCreation_block_0_fallthrough`. -/
def attesterCreation_block_0_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 160).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem attesterCreation_block_0_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 11) (attesterCreation_block_0_fallthrough_stack (ee := ee) (R := R)) (attesterCreation_block_0_fallthrough_memory (mem := mem)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((30) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.CreationListing.decodes_code tail (t := 0) rfl) 0 0 rfl [] h
  have r := e.run 7 [] 3 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiNTX hcond 3 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterCreation_block_0_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 11) (attesterCreation_block_0_fallthrough_stack (ee := ee) (R := R)) (attesterCreation_block_0_fallthrough_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterCreation_block_0_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 11. -/
theorem attesterCreation_block_11 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 11) R mem aw rdata σ k C)
    : RDrev (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) g s0 := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.CreationListing.decodes_code tail (t := 0) rfl) 8 11 rfl [] h
  have r := e.run 2 [] 2 rfl rfl hstack trivial
  exact r.rev 2 rfl hstack

/-- Final stack for bytecode block summary `attesterCreation_block_15`. -/
def attesterCreation_block_15_stack {tail : ByteArray} {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 64) mem) :: ((memLoad (UInt256.ofNat 64) mem) + (UInt256.sub (UInt256.ofNat (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail).size) (UInt256.ofNat 4057))) :: (UInt256.ofNat 44) :: R)

/-- Final memory for bytecode block summary `attesterCreation_block_15`. -/
def attesterCreation_block_15_memory {tail : ByteArray} {mem : ByteArray} : ByteArray :=
  (((memLoad (UInt256.ofNat 64) mem) + (UInt256.sub (UInt256.ofNat (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail).size) (UInt256.ofNat 4057))).toByteArray.write 0 ((Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail).write (UInt256.ofNat 4057).toNat mem (memLoad (UInt256.ofNat 64) mem).toNat (UInt256.sub (UInt256.ofNat (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail).size) (UInt256.ofNat 4057)).toNat) (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 15. -/
theorem attesterCreation_block_15 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 98) (attesterCreation_block_15_stack (tail := tail) (mem := mem) (R := R)) (attesterCreation_block_15_memory (tail := tail) (mem := mem)) (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (UInt256.sub (UInt256.ofNat (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail).size) (UInt256.ofNat 4057))) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 21) (C + ((61) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (UInt256.sub (UInt256.ofNat (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail).size) (UInt256.ofNat 4057))) + (3 + 3 * (((UInt256.sub (UInt256.ofNat (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail).size) (UInt256.ofNat 4057)).toNat + 31) / 32)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (UInt256.sub (UInt256.ofNat (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail).size) (UInt256.ofNat 4057))) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.CreationListing.decodes_code tail (t := 15) rfl) 0 15 rfl [x0] h
  have r := e.run 20 [] 5 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpX (Benchmarks.EAS.Attester.CreationListing.jumpdest_code tail (t := 98) rfl rfl) 5 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterCreation_block_15_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 98) (attesterCreation_block_15_stack (tail := tail) (mem := mem) (R := R)) (attesterCreation_block_15_memory (tail := tail) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterCreation_block_15 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 44. -/
theorem attesterCreation_block_44_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 44) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 82) (x0 :: R) mem aw rdata σ (k + 10) (C + ((35))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.CreationListing.decodes_code tail (t := 44) rfl) 0 44 rfl [x0] h
  have r := e.run 9 [] 4 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiTX hcond (Benchmarks.EAS.Attester.CreationListing.jumpdest_code tail (t := 82) rfl rfl) 4 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterCreation_block_44_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 44) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 82) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterCreation_block_44_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 44. -/
theorem attesterCreation_block_44_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 44) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 58) (x0 :: R) mem aw rdata σ (k + 10) (C + ((35))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.CreationListing.decodes_code tail (t := 44) rfl) 0 44 rfl [x0] h
  have r := e.run 9 [] 4 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiNTX hcond 4 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterCreation_block_44_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 44) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 58) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterCreation_block_44_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 58. -/
theorem attesterCreation_block_58 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 58) R mem aw rdata σ k C)
    : RDrev (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) g s0 := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.CreationListing.decodes_code tail (t := 44) rfl) 10 58 rfl [] h
  have r := e.run 15 [] 3 rfl rfl hstack trivial
  exact r.rev 3 rfl hstack

/-- Final stack for bytecode block summary `attesterCreation_block_82`. -/
def attesterCreation_block_82_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `attesterCreation_block_82`. -/
def attesterCreation_block_82_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x0).toByteArray.write 0 mem (UInt256.ofNat 128).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 82. -/
theorem attesterCreation_block_82 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 82) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 144) (attesterCreation_block_82_stack (R := R)) (attesterCreation_block_82_memory (mem := mem) (x0 := x0)) (M aw (UInt256.ofNat 128) (⟨32⟩ : UInt256)) rdata σ (k + 11) (C + ((36) + (memExpansionCost aw (UInt256.ofNat 128) (⟨32⟩ : UInt256)))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.CreationListing.decodes_code tail (t := 82) rfl) 0 82 rfl [x0] h
  have r := e.run 10 [] 4 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpX (Benchmarks.EAS.Attester.CreationListing.jumpdest_code tail (t := 144) rfl rfl) 4 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterCreation_block_82_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 82) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 144) (attesterCreation_block_82_stack (R := R)) (attesterCreation_block_82_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterCreation_block_82 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterCreation_block_98_taken`. -/
def attesterCreation_block_98_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 98. -/
theorem attesterCreation_block_98_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 98) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 115) (attesterCreation_block_98_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((35))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.CreationListing.decodes_code tail (t := 98) rfl) 0 98 rfl [x0, x1] h
  have r := e.run 9 [] 6 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiTX hcond (Benchmarks.EAS.Attester.CreationListing.jumpdest_code tail (t := 115) rfl rfl) 6 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterCreation_block_98_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 98) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 115) (attesterCreation_block_98_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterCreation_block_98_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterCreation_block_98_fallthrough`. -/
def attesterCreation_block_98_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 98. -/
theorem attesterCreation_block_98_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 98) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 111) (attesterCreation_block_98_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((35))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.CreationListing.decodes_code tail (t := 98) rfl) 0 98 rfl [x0, x1] h
  have r := e.run 9 [] 6 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiNTX hcond 6 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterCreation_block_98_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 98) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 111) (attesterCreation_block_98_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterCreation_block_98_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 111. -/
theorem attesterCreation_block_111 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 111) R mem aw rdata σ k C)
    : RDrev (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) g s0 := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.CreationListing.decodes_code tail (t := 98) rfl) 10 111 rfl [] h
  have r := e.run 2 [] 2 rfl rfl hstack trivial
  exact r.rev 2 rfl hstack

/-- Final stack for bytecode block summary `attesterCreation_block_115_taken`. -/
def attesterCreation_block_115_taken_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad x1 mem) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 115. -/
theorem attesterCreation_block_115_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.eq (memLoad x1 mem) (UInt256.land (memLoad x1 mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 115) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 137) (attesterCreation_block_115_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem (M aw x1 (⟨32⟩ : UInt256)) rdata σ (k + 14) (C + ((47) + (memExpansionCost aw x1 (⟨32⟩ : UInt256)))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.CreationListing.decodes_code tail (t := 115) rfl) 0 115 rfl [x0, x1] h
  have r := e.run 13 [] 6 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiTX hcond (Benchmarks.EAS.Attester.CreationListing.jumpdest_code tail (t := 137) rfl rfl) 6 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterCreation_block_115_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.eq (memLoad x1 mem) (UInt256.land (memLoad x1 mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 115) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 137) (attesterCreation_block_115_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterCreation_block_115_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterCreation_block_115_fallthrough`. -/
def attesterCreation_block_115_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad x1 mem) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 115. -/
theorem attesterCreation_block_115_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.eq (memLoad x1 mem) (UInt256.land (memLoad x1 mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 115) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 133) (attesterCreation_block_115_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem (M aw x1 (⟨32⟩ : UInt256)) rdata σ (k + 14) (C + ((47) + (memExpansionCost aw x1 (⟨32⟩ : UInt256)))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.CreationListing.decodes_code tail (t := 115) rfl) 0 115 rfl [x0, x1] h
  have r := e.run 13 [] 6 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpiNTX hcond 6 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterCreation_block_115_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.eq (memLoad x1 mem) (UInt256.land (memLoad x1 mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 115) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 133) (attesterCreation_block_115_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterCreation_block_115_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 133. -/
theorem attesterCreation_block_133 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 133) R mem aw rdata σ k C)
    : RDrev (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) g s0 := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.CreationListing.decodes_code tail (t := 115) rfl) 14 133 rfl [] h
  have r := e.run 2 [] 2 rfl rfl hstack trivial
  exact r.rev 2 rfl hstack

/-- Final stack for bytecode block summary `attesterCreation_block_137`. -/
def attesterCreation_block_137_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 137. -/
theorem attesterCreation_block_137 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.EAS.Attester.attesterCreationBytecode 0).contains x4 = true)
    (h : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 137) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 x4 (attesterCreation_block_137_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 7) (C + ((21))) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.CreationListing.decodes_code tail (t := 137) rfl) 0 137 rfl [x0, x1, x2, x3, x4] h
  have r := e.run 6 [] 5 rfl rfl hstack trivial
  exact RD.normalizeCounters (r.jumpX (j tail x4 hvalid) 5 rfl hstack) (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterCreation_block_137_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.EAS.Attester.attesterCreationBytecode 0).contains x4 = true)
    (h : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 137) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 x4 (attesterCreation_block_137_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterCreation_block_137 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 144. -/
theorem attesterCreation_block_144 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 144) R mem aw rdata σ k C)
    : RDret (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) g s0 σ (((memLoad (UInt256.ofNat 128) mem).toByteArray.write 0 ((memLoad (UInt256.ofNat 128) mem).toByteArray.write 0 ((memLoad (UInt256.ofNat 128) mem).toByteArray.write 0 ((memLoad (UInt256.ofNat 128) mem).toByteArray.write 0 ((Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail).write (UInt256.ofNat 192).toNat mem (UInt256.ofNat 0).toNat (UInt256.ofNat 3865).toNat) ((UInt256.ofNat 824) + (UInt256.ofNat 0)).toNat 32) ((UInt256.ofNat 1719) + (UInt256.ofNat 0)).toNat 32) ((UInt256.ofNat 1888) + (UInt256.ofNat 0)).toNat 32) ((UInt256.ofNat 2289) + (UInt256.ofNat 0)).toNat 32).readWithPadding (UInt256.ofNat 0).toNat (UInt256.ofNat 3865).toNat) := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.CreationListing.decodes_code tail (t := 144) rfl) 0 144 rfl [] h
  have r := e.run 28 [] 5 rfl rfl hstack trivial
  exact r.ret 5 rfl hstack

/-- Automatically generated RD summary for bytecode block at pc 191. -/
theorem attesterCreation_block_191 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (h : RD (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 191) R mem aw rdata σ k C)
    : RDinvalid (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) g s0 := by
  have e := Reasoning.Listing.RDL.enter (Benchmarks.EAS.Attester.CreationListing.decodes_code tail (t := 144) rfl) 29 191 rfl [] h
  exact e.invalid

end attesterCreationBlocks
