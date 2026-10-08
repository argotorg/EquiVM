import Reasoning.Reach
import Reasoning.Immutables
import Benchmarks.Morpho.MorphoBlue.Bytecode
import Benchmarks.Morpho.MorphoBlue.ImmutableCode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace morphoBlocks

open Reasoning.Immutables
set_option maxRecDepth 10000

theorem immutableLayout_sites :
    Benchmarks.Morpho.MorphoBlue.immutableLayout.sites = [(6282, 32, "DOMAIN_SEPARATOR"), (9401, 32, "DOMAIN_SEPARATOR")] := by native_decide

theorem immutableLayout_inBounds :
    Benchmarks.Morpho.MorphoBlue.immutableLayout.inBounds Benchmarks.Morpho.MorphoBlue.morphoBytecode = true := by native_decide

theorem immutableTemplate_size64 :
    Benchmarks.Morpho.MorphoBlue.morphoBytecode.size < 2 ^ 64 := by native_decide

theorem immutableRuntime_size (immWords : String → UInt256) :
    (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords).size = Benchmarks.Morpho.MorphoBlue.morphoBytecode.size := by
  exact Layout.runtime_size_of_bounds immutableLayout_inBounds

/-- Automatically generated RD summary for bytecode block at pc 11311. -/
theorem morpho_block_11311 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11311) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RDret (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) g s0 (sstoreAccountMap ee.codeOwner σ x4 (UInt256.lor (UInt256.land x0 x1) x2)) (mem.readWithPadding x4.toNat x4.toNat) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11311⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.and (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11312⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.or (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11313⟩ : UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup3 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11314⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r5⟩ := RD.sstore r4 hperm (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11315⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.pushConst (UInt256.ofNat 10172170667648662213130535590167641847319026078236184582386542448283198574517) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11316⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 10172170667648662213130535590167641847319026078236184582386542448283198574517), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.dup3 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11349⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11350⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := RD.genLog2 r8 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11351⟩ : UInt256), UInt8.ofNat 162, .LOG2, none, immutableLayout_inBounds, immutableTemplate_size64)) hperm (by evm_ov)
  have r10 := r9.dup1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11352⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRet r10 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11353⟩ : UInt256), UInt8.ofNat 243, .RETURN, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Final stack for bytecode block summary `morpho_block_11354_taken`. -/
def morpho_block_11354_taken_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 11354. -/
theorem morpho_block_11354_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 712) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11354) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 712) (morpho_block_11354_taken_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 11) (C + ((38))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11354⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11355⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.calldataload (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11357⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11358⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11359⟩ : UInt256), UInt8.ofNat 115, .Push .PUSH20, some ((UInt256.ofNat 1461501637330902918203684832716283019655932542975), 20), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup3 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11380⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.and (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11381⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup3 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11382⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.sub (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11383⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 712) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11384⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 712), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.jumpiT (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11387⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 712)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_11354_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 712) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11354) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 712) (morpho_block_11354_taken_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morpho_block_11354_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morpho_block_11354_fallthrough`. -/
def morpho_block_11354_fallthrough_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 11354. -/
theorem morpho_block_11354_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11354) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11388) (morpho_block_11354_fallthrough_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 11) (C + ((38))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11354⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11355⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.calldataload (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11357⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11358⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11359⟩ : UInt256), UInt8.ofNat 115, .Push .PUSH20, some ((UInt256.ofNat 1461501637330902918203684832716283019655932542975), 20), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup3 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11380⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.and (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11381⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup3 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11382⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.sub (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11383⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 712) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11384⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 712), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.jumpiNT (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11387⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11388)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_11354_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11354) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11388) (morpho_block_11354_fallthrough_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morpho_block_11354_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morpho_block_11388`. -/
def morpho_block_11388_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 11388. -/
theorem morpho_block_11388 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains x0 = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11388) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 x0 (morpho_block_11388_stack (R := R)) mem aw rdata σ (k + 1) (C + ((8))) := by
  let r0 := h
  have r1 := r0.jump (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11388⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  exact RD.normalizeCounters r1 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_11388_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains x0 = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11388) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 x0 (morpho_block_11388_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morpho_block_11388 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morpho_block_11389_taken`. -/
def morpho_block_11389_taken_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 196).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 11389. -/
theorem morpho_block_11389_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 196).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 196).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 712) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11389) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 712) (morpho_block_11389_taken_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 11) (C + ((38))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11389⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 196) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11390⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 196), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.calldataload (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11392⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11393⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11394⟩ : UInt256), UInt8.ofNat 115, .Push .PUSH20, some ((UInt256.ofNat 1461501637330902918203684832716283019655932542975), 20), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup3 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11415⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.and (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11416⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup3 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11417⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.sub (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11418⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 712) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11419⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 712), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.jumpiT (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11422⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 712)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_11389_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 196).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 196).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 712) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11389) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 712) (morpho_block_11389_taken_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morpho_block_11389_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morpho_block_11389_fallthrough`. -/
def morpho_block_11389_fallthrough_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 196).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 11389. -/
theorem morpho_block_11389_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 196).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 196).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11389) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11423) (morpho_block_11389_fallthrough_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 11) (C + ((38))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11389⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 196) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11390⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 196), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.calldataload (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11392⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11393⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11394⟩ : UInt256), UInt8.ofNat 115, .Push .PUSH20, some ((UInt256.ofNat 1461501637330902918203684832716283019655932542975), 20), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup3 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11415⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.and (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11416⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup3 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11417⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.sub (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11418⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 712) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11419⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 712), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.jumpiNT (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11422⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11423)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_11389_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 196).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 196).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11389) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11423) (morpho_block_11389_fallthrough_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morpho_block_11389_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morpho_block_11423`. -/
def morpho_block_11423_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 11423. -/
theorem morpho_block_11423 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains x0 = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11423) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 x0 (morpho_block_11423_stack (R := R)) mem aw rdata σ (k + 1) (C + ((8))) := by
  let r0 := h
  have r1 := r0.jump (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11423⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  exact RD.normalizeCounters r1 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_11423_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains x0 = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11423) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 x0 (morpho_block_11423_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morpho_block_11423 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morpho_block_11424_taken`. -/
def morpho_block_11424_taken_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 11424. -/
theorem morpho_block_11424_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 712) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11424) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 712) (morpho_block_11424_taken_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 11) (C + ((38))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11424⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 36) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11425⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 36), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.calldataload (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11427⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11428⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11429⟩ : UInt256), UInt8.ofNat 115, .Push .PUSH20, some ((UInt256.ofNat 1461501637330902918203684832716283019655932542975), 20), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup3 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11450⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.and (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11451⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup3 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11452⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.sub (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11453⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 712) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11454⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 712), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.jumpiT (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11457⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 712)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_11424_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 712) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11424) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 712) (morpho_block_11424_taken_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morpho_block_11424_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morpho_block_11424_fallthrough`. -/
def morpho_block_11424_fallthrough_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 11424. -/
theorem morpho_block_11424_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11424) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11458) (morpho_block_11424_fallthrough_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 11) (C + ((38))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11424⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 36) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11425⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 36), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.calldataload (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11427⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11428⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11429⟩ : UInt256), UInt8.ofNat 115, .Push .PUSH20, some ((UInt256.ofNat 1461501637330902918203684832716283019655932542975), 20), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup3 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11450⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.and (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11451⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup3 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11452⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.sub (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11453⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 712) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11454⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 712), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.jumpiNT (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11457⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11458)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_11424_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11424) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11458) (morpho_block_11424_fallthrough_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morpho_block_11424_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morpho_block_11458`. -/
def morpho_block_11458_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 11458. -/
theorem morpho_block_11458 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains x0 = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11458) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 x0 (morpho_block_11458_stack (R := R)) mem aw rdata σ (k + 1) (C + ((8))) := by
  let r0 := h
  have r1 := r0.jump (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11458⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  exact RD.normalizeCounters r1 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_11458_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains x0 = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11458) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 x0 (morpho_block_11458_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morpho_block_11458 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 11459. -/
theorem morpho_block_11459_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt x0 (UInt256.ofNat 18446744073709551615)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 6709) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11459) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 6709) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11459⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11460⟩ : UInt256), UInt8.ofNat 103, .Push .PUSH8, some ((UInt256.ofNat 18446744073709551615), 8), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup2 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11469⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.gt (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11470⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 6709) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11471⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 6709), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.jumpiT (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11474⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6709)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_11459_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt x0 (UInt256.ofNat 18446744073709551615)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 6709) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11459) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 6709) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morpho_block_11459_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 11459. -/
theorem morpho_block_11459_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt x0 (UInt256.ofNat 18446744073709551615)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11459) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11475) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11459⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11460⟩ : UInt256), UInt8.ofNat 103, .Push .PUSH8, some ((UInt256.ofNat 18446744073709551615), 8), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup2 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11469⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.gt (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11470⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 6709) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11471⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 6709), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.jumpiNT (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11474⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11475)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_11459_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt x0 (UInt256.ofNat 18446744073709551615)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11459) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11475) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morpho_block_11459_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morpho_block_11475`. -/
def morpho_block_11475_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `morpho_block_11475`. -/
def morpho_block_11475_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11475. -/
theorem morpho_block_11475 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains x1 = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11475) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 x1 (morpho_block_11475_stack (R := R)) (morpho_block_11475_memory (mem := mem) (x0 := x0)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 3) (C + ((14) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11475⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := RD.genMstore r1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11477⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.jump (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11478⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  exact RD.normalizeCounters r3 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_11475_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains x1 = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11475) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 x1 (morpho_block_11475_stack (R := R)) (morpho_block_11475_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morpho_block_11475 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morpho_block_11479_taken`. -/
def morpho_block_11479_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x0 + (UInt256.ofNat 160)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 11479. -/
theorem morpho_block_11479_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lor (UInt256.gt (x0 + (UInt256.ofNat 160)) (UInt256.ofNat 18446744073709551615)) (UInt256.lt (x0 + (UInt256.ofNat 160)) x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 6709) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11479) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 6709) (morpho_block_11479_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 13) (C + ((44))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11479⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 160) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11480⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup2 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11482⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.add (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11483⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11484⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup2 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11485⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.lt (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11486⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11487⟩ : UInt256), UInt8.ofNat 103, .Push .PUSH8, some ((UInt256.ofNat 18446744073709551615), 8), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup3 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11496⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.gt (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11497⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.or (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11498⟩ : UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 6709) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11499⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 6709), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.jumpiT (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11502⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6709)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_11479_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lor (UInt256.gt (x0 + (UInt256.ofNat 160)) (UInt256.ofNat 18446744073709551615)) (UInt256.lt (x0 + (UInt256.ofNat 160)) x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 6709) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11479) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 6709) (morpho_block_11479_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morpho_block_11479_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morpho_block_11479_fallthrough`. -/
def morpho_block_11479_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x0 + (UInt256.ofNat 160)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 11479. -/
theorem morpho_block_11479_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lor (UInt256.gt (x0 + (UInt256.ofNat 160)) (UInt256.ofNat 18446744073709551615)) (UInt256.lt (x0 + (UInt256.ofNat 160)) x0)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11479) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11503) (morpho_block_11479_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 13) (C + ((44))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11479⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 160) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11480⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup2 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11482⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.add (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11483⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11484⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup2 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11485⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.lt (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11486⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11487⟩ : UInt256), UInt8.ofNat 103, .Push .PUSH8, some ((UInt256.ofNat 18446744073709551615), 8), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup3 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11496⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.gt (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11497⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.or (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11498⟩ : UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 6709) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11499⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 6709), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.jumpiNT (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11502⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11503)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_11479_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lor (UInt256.gt (x0 + (UInt256.ofNat 160)) (UInt256.ofNat 18446744073709551615)) (UInt256.lt (x0 + (UInt256.ofNat 160)) x0)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11479) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11503) (morpho_block_11479_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morpho_block_11479_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morpho_block_11503`. -/
def morpho_block_11503_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `morpho_block_11503`. -/
def morpho_block_11503_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11503. -/
theorem morpho_block_11503 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains x1 = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11503) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 x1 (morpho_block_11503_stack (R := R)) (morpho_block_11503_memory (mem := mem) (x0 := x0)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 3) (C + ((14) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11503⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := RD.genMstore r1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11505⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.jump (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11506⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  exact RD.normalizeCounters r3 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_11503_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains x1 = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11503) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 x1 (morpho_block_11503_stack (R := R)) (morpho_block_11503_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morpho_block_11503 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morpho_block_11507_taken`. -/
def morpho_block_11507_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x0 + (UInt256.ofNat 64)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 11507. -/
theorem morpho_block_11507_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lor (UInt256.gt (x0 + (UInt256.ofNat 64)) (UInt256.ofNat 18446744073709551615)) (UInt256.lt (x0 + (UInt256.ofNat 64)) x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 6709) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11507) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 6709) (morpho_block_11507_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 13) (C + ((44))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11507⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11508⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup2 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11510⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.add (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11511⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11512⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup2 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11513⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.lt (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11514⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11515⟩ : UInt256), UInt8.ofNat 103, .Push .PUSH8, some ((UInt256.ofNat 18446744073709551615), 8), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup3 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11524⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.gt (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11525⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.or (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11526⟩ : UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 6709) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11527⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 6709), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.jumpiT (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11530⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6709)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_11507_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lor (UInt256.gt (x0 + (UInt256.ofNat 64)) (UInt256.ofNat 18446744073709551615)) (UInt256.lt (x0 + (UInt256.ofNat 64)) x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 6709) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11507) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 6709) (morpho_block_11507_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morpho_block_11507_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morpho_block_11507_fallthrough`. -/
def morpho_block_11507_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x0 + (UInt256.ofNat 64)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 11507. -/
theorem morpho_block_11507_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lor (UInt256.gt (x0 + (UInt256.ofNat 64)) (UInt256.ofNat 18446744073709551615)) (UInt256.lt (x0 + (UInt256.ofNat 64)) x0)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11507) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11531) (morpho_block_11507_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 13) (C + ((44))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11507⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11508⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup2 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11510⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.add (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11511⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11512⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup2 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11513⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.lt (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11514⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11515⟩ : UInt256), UInt8.ofNat 103, .Push .PUSH8, some ((UInt256.ofNat 18446744073709551615), 8), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup3 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11524⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.gt (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11525⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.or (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11526⟩ : UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 6709) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11527⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 6709), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.jumpiNT (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11530⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11531)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_11507_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lor (UInt256.gt (x0 + (UInt256.ofNat 64)) (UInt256.ofNat 18446744073709551615)) (UInt256.lt (x0 + (UInt256.ofNat 64)) x0)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11507) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11531) (morpho_block_11507_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morpho_block_11507_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morpho_block_11531`. -/
def morpho_block_11531_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `morpho_block_11531`. -/
def morpho_block_11531_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11531. -/
theorem morpho_block_11531 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains x1 = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11531) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 x1 (morpho_block_11531_stack (R := R)) (morpho_block_11531_memory (mem := mem) (x0 := x0)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 3) (C + ((14) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11531⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := RD.genMstore r1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11533⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.jump (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11534⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  exact RD.normalizeCounters r3 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_11531_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains x1 = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11531) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 x1 (morpho_block_11531_stack (R := R)) (morpho_block_11531_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morpho_block_11531 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morpho_block_11535_taken`. -/
def morpho_block_11535_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x0 + (UInt256.land (x1 + (UInt256.ofNat 31)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 11535. -/
theorem morpho_block_11535_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lor (UInt256.gt (x0 + (UInt256.land (x1 + (UInt256.ofNat 31)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) (UInt256.ofNat 18446744073709551615)) (UInt256.lt (x0 + (UInt256.land (x1 + (UInt256.ofNat 31)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 6709) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11535) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 6709) (morpho_block_11535_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 18) (C + ((59))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11535⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11536⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 31) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11537⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 31), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11539⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap2 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11572⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.add (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11573⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.and (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11574⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup2 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11575⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.add (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11576⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.swap1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11577⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup2 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11578⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.lt (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11579⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11580⟩ : UInt256), UInt8.ofNat 103, .Push .PUSH8, some ((UInt256.ofNat 18446744073709551615), 8), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.dup3 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11589⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.gt (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11590⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.or (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11591⟩ : UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 6709) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11592⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 6709), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.jumpiT (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨11595⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6709)) r18 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_11535_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lor (UInt256.gt (x0 + (UInt256.land (x1 + (UInt256.ofNat 31)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) (UInt256.ofNat 18446744073709551615)) (UInt256.lt (x0 + (UInt256.land (x1 + (UInt256.ofNat 31)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 6709) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 11535) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 6709) (morpho_block_11535_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morpho_block_11535_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

end morphoBlocks
