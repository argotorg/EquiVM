import Reasoning.Reach
import Reasoning.Initcode
import Benchmarks.CompoundIII.Comet.Bytecode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace cometWithExtendedAssetListCreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_17093`. -/
def cometWithExtendedAssetListCreation_block_17093_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 17093. -/
theorem cometWithExtendedAssetListCreation_block_17093 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains x2 = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17093) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 x2 (cometWithExtendedAssetListCreation_block_17093_stack (R := R)) mem aw rdata σ (k + 3) (C + ((12))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x2 hvalid) (by evm_ov)
  exact RD.normalizeCounters r3 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_17093_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains x2 = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17093) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 x2 (cometWithExtendedAssetListCreation_block_17093_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_17093 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_17096`. -/
def cometWithExtendedAssetListCreation_block_17096_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: (UInt256.ofNat 16) :: (UInt256.ofNat 14290) :: (UInt256.ofNat 14224) :: (UInt256.ofNat 14302) :: x0 :: (UInt256.ofNat 3121) :: R)

/-- Automatically generated RD summary for bytecode block at pc 17096. -/
theorem cometWithExtendedAssetListCreation_block_17096 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 11438) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17096) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 11438) (cometWithExtendedAssetListCreation_block_17096_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 9) (C + ((30))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 14302) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 14224) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 14290) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 16) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 3121) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.swap6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 11438) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 11438) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11438)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_17096_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 11438) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17096) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 11438) (cometWithExtendedAssetListCreation_block_17096_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_17096 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_17116`. -/
def cometWithExtendedAssetListCreation_block_17116_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.land (UInt256.ofNat 255) x0)) (UInt256.ofNat 255)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 17116. -/
theorem cometWithExtendedAssetListCreation_block_17116 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains x1 = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17116) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 x1 (cometWithExtendedAssetListCreation_block_17116_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 10) (C + ((33))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 255) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x1 hvalid) (by evm_ov)
  exact RD.normalizeCounters r10 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_17116_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains x1 = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17116) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 x1 (cometWithExtendedAssetListCreation_block_17116_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_17116 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_17128`. -/
def cometWithExtendedAssetListCreation_block_17128_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x0 (⟨0⟩ : UInt256))) (UInt256.ofNat 248)) :: x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 17128. -/
theorem cometWithExtendedAssetListCreation_block_17128 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 14314) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17128) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14314) (cometWithExtendedAssetListCreation_block_17128_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 14314) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r5⟩ := RD.sload r4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 248) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.shr (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 14314) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14314)) r9 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_17128_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 14314) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17128) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14314) (cometWithExtendedAssetListCreation_block_17128_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := cometWithExtendedAssetListCreation_block_17128 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_17140`. -/
def cometWithExtendedAssetListCreation_block_17140_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: (UInt256.lor x0 x1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 17140. -/
theorem cometWithExtendedAssetListCreation_block_17140 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 11083) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17140) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 11083) (cometWithExtendedAssetListCreation_block_17140_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.or (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 11083) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 11083) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11083)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_17140_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 11083) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17140) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 11083) (cometWithExtendedAssetListCreation_block_17140_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_17140 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_17147_taken`. -/
def cometWithExtendedAssetListCreation_block_17147_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x1 :: (UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 17147. -/
theorem cometWithExtendedAssetListCreation_block_17147_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 14474) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17147) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14474) (cometWithExtendedAssetListCreation_block_17147_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 14474) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 14474) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14474)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_17147_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 14474) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17147) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14474) (cometWithExtendedAssetListCreation_block_17147_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_17147_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_17147_fallthrough`. -/
def cometWithExtendedAssetListCreation_block_17147_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x1 :: (UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 17147. -/
theorem cometWithExtendedAssetListCreation_block_17147_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17147) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17155) (cometWithExtendedAssetListCreation_block_17147_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 14474) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 17155)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_17147_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17147) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17155) (cometWithExtendedAssetListCreation_block_17147_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_17147_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_17155_taken`. -/
def cometWithExtendedAssetListCreation_block_17155_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 17155. -/
theorem cometWithExtendedAssetListCreation_block_17155_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : x2 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 14339) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17155) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14339) (cometWithExtendedAssetListCreation_block_17155_taken_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 14339) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 14339) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14339)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_17155_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : x2 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 14339) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17155) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14339) (cometWithExtendedAssetListCreation_block_17155_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_17155_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_17155_fallthrough`. -/
def cometWithExtendedAssetListCreation_block_17155_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 17155. -/
theorem cometWithExtendedAssetListCreation_block_17155_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : x2 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17155) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17162) (cometWithExtendedAssetListCreation_block_17155_fallthrough_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 14339) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 17162)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_17155_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : x2 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17155) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17162) (cometWithExtendedAssetListCreation_block_17155_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_17155_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_17162`. -/
def cometWithExtendedAssetListCreation_block_17162_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 17162. -/
theorem cometWithExtendedAssetListCreation_block_17162 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains x2 = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17162) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 x2 (cometWithExtendedAssetListCreation_block_17162_stack (R := R)) mem aw rdata σ (k + 3) (C + ((12))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x2 hvalid) (by evm_ov)
  exact RD.normalizeCounters r3 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_17162_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains x2 = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17162) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 x2 (cometWithExtendedAssetListCreation_block_17162_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_17162 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_17165_taken`. -/
def cometWithExtendedAssetListCreation_block_17165_taken_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (UInt256.ofNat 255) (memLoad x1 mem)) :: (UInt256.land (UInt256.ofNat 255) (memLoad x1 mem)) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 17165. -/
theorem cometWithExtendedAssetListCreation_block_17165_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.land (UInt256.ofNat 255) (memLoad x1 mem)) (UInt256.ofNat 16))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 14411) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17165) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14411) (cometWithExtendedAssetListCreation_block_17165_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem (M aw x1 (⟨32⟩ : UInt256)) rdata σ (k + 12) (C + ((41) + (memExpansionCost aw x1 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := RD.genMload r2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 255) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 16) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 14411) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 14411) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14411)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_17165_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.land (UInt256.ofNat 255) (memLoad x1 mem)) (UInt256.ofNat 16))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 14411) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17165) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14411) (cometWithExtendedAssetListCreation_block_17165_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_17165_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_17165_fallthrough`. -/
def cometWithExtendedAssetListCreation_block_17165_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (UInt256.ofNat 255) (memLoad x1 mem)) :: (UInt256.land (UInt256.ofNat 255) (memLoad x1 mem)) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 17165. -/
theorem cometWithExtendedAssetListCreation_block_17165_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.land (UInt256.ofNat 255) (memLoad x1 mem)) (UInt256.ofNat 16))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17165) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17181) (cometWithExtendedAssetListCreation_block_17165_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem (M aw x1 (⟨32⟩ : UInt256)) rdata σ (k + 12) (C + ((41) + (memExpansionCost aw x1 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := RD.genMload r2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 255) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 16) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 14411) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 17181)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_17165_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.land (UInt256.ofNat 255) (memLoad x1 mem)) (UInt256.ofNat 16))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17165) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17181) (cometWithExtendedAssetListCreation_block_17165_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_17165_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_17181`. -/
def cometWithExtendedAssetListCreation_block_17181_stack {mem : ByteArray} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (UInt256.ofNat 255) (memLoad x3 mem)) :: (UInt256.ofNat 14379) :: (UInt256.ofNat 14224) :: (UInt256.ofNat 14387) :: x2 :: (UInt256.ofNat 3121) :: R)

/-- Automatically generated RD summary for bytecode block at pc 17181. -/
theorem cometWithExtendedAssetListCreation_block_17181 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 14209) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17181) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14209) (cometWithExtendedAssetListCreation_block_17181_stack (mem := mem) (x2 := x2) (x3 := x3) (R := R)) mem (M aw x3 (⟨32⟩ : UInt256)) rdata σ (k + 13) (C + ((42) + (memExpansionCost aw x3 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 14387) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 14224) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 14379) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 14209) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 3121) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.swap6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := RD.genMload r8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 255) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 14209) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14209)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_17181_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 14209) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17181) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14209) (cometWithExtendedAssetListCreation_block_17181_stack (mem := mem) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_17181 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_17205`. -/
def cometWithExtendedAssetListCreation_block_17205_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (UInt256.ofNat 65535) (UInt256.lnot x0)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 17205. -/
theorem cometWithExtendedAssetListCreation_block_17205 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains x1 = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17205) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 x1 (cometWithExtendedAssetListCreation_block_17205_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 6) (C + ((21))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 65535) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x1 hvalid) (by evm_ov)
  exact RD.normalizeCounters r6 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_17205_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains x1 = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17205) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 x1 (cometWithExtendedAssetListCreation_block_17205_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_17205 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_17213`. -/
def cometWithExtendedAssetListCreation_block_17213_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x0 (⟨0⟩ : UInt256))) (UInt256.ofNat 232)) (UInt256.ofNat 65535)) :: x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 17213. -/
theorem cometWithExtendedAssetListCreation_block_17213 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 14404) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17213) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14404) (cometWithExtendedAssetListCreation_block_17213_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 14404) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r5⟩ := RD.sload r4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 65535) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 232) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.shr (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 14404) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14404)) r12 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_17213_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 14404) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17213) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14404) (cometWithExtendedAssetListCreation_block_17213_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := cometWithExtendedAssetListCreation_block_17213 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_17230`. -/
def cometWithExtendedAssetListCreation_block_17230_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: (UInt256.land x0 x1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 17230. -/
theorem cometWithExtendedAssetListCreation_block_17230 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 11547) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17230) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 11547) (cometWithExtendedAssetListCreation_block_17230_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 11547) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 11547) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11547)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_17230_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 11547) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17230) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 11547) (cometWithExtendedAssetListCreation_block_17230_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_17230 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_17237_taken`. -/
def cometWithExtendedAssetListCreation_block_17237_taken_stack {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 17237. -/
theorem cometWithExtendedAssetListCreation_block_17237_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.lt x0 (UInt256.ofNat 24)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 14425) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17237) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14425) (cometWithExtendedAssetListCreation_block_17237_taken_stack (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 8) (C + ((28))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 24) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 14425) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 14425) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14425)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_17237_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.lt x0 (UInt256.ofNat 24)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 14425) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17237) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14425) (cometWithExtendedAssetListCreation_block_17237_taken_stack (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_17237_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_17237_fallthrough`. -/
def cometWithExtendedAssetListCreation_block_17237_fallthrough_stack {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 17237. -/
theorem cometWithExtendedAssetListCreation_block_17237_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.lt x0 (UInt256.ofNat 24)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17237) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17248) (cometWithExtendedAssetListCreation_block_17237_fallthrough_stack (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 8) (C + ((28))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 24) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 14425) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 17248)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_17237_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.lt x0 (UInt256.ofNat 24)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17237) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17248) (cometWithExtendedAssetListCreation_block_17237_fallthrough_stack (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_17237_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_17248`. -/
def cometWithExtendedAssetListCreation_block_17248_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 17248. -/
theorem cometWithExtendedAssetListCreation_block_17248 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains x2 = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17248) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 x2 (cometWithExtendedAssetListCreation_block_17248_stack (R := R)) mem aw rdata σ (k + 3) (C + ((12))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x2 hvalid) (by evm_ov)
  exact RD.normalizeCounters r3 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_17248_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains x2 = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17248) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 x2 (cometWithExtendedAssetListCreation_block_17248_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_17248 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetListCreation_block_17251`. -/
def cometWithExtendedAssetListCreation_block_17251_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: (UInt256.ofNat 16) :: (UInt256.ofNat 14290) :: (UInt256.ofNat 14448) :: (UInt256.ofNat 14224) :: (UInt256.ofNat 14455) :: x0 :: (UInt256.ofNat 3121) :: R)

/-- Automatically generated RD summary for bytecode block at pc 17251. -/
theorem cometWithExtendedAssetListCreation_block_17251 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 11438) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17251) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 11438) (cometWithExtendedAssetListCreation_block_17251_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((33))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode.size = 21425 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 14455) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 14224) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 14448) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 14290) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 16) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 3121) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.swap7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 11438) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 11438) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11438)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetListCreation_block_17251_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode 0).contains (UInt256.ofNat 11438) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 17251) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 11438) (cometWithExtendedAssetListCreation_block_17251_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetListCreation_block_17251 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

end cometWithExtendedAssetListCreationBlocks
