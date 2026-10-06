import Reasoning.Reach
import Reasoning.Immutables
import Examples.TinyImmutable.Bytecode
import Examples.TinyImmutable.ImmutableCode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace tinyImmutableBlocks

open Reasoning.Immutables
set_option maxRecDepth 10000

theorem immutableLayout_sites :
    TinyImmutable.immutableLayout.sites = [(186, 32, "scale"), (361, 32, "scale"), (72, 32, "owner"), (245, 32, "owner")] := by native_decide

theorem immutableLayout_inBounds :
    TinyImmutable.immutableLayout.inBounds TinyImmutable.tinyImmutableBytecode = true := by native_decide

theorem immutableTemplate_size64 :
    TinyImmutable.tinyImmutableBytecode.size < 2 ^ 64 := by native_decide

theorem immutableRuntime_size (immWords : String → UInt256) :
    (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords).size = TinyImmutable.tinyImmutableBytecode.size := by
  exact Layout.runtime_size_of_bounds immutableLayout_inBounds

theorem immutableDecode_71 (immWords : String → UInt256) :
    decode (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) (⟨71⟩ : UInt256) =
      some (.Push .PUSH32, some (immWords "owner", 32)) := by
  exact Layout.decodeSite (pc := (⟨71⟩ : UInt256)) (words := immWords)
    72 "owner" [(186, immWords "scale"), (361, immWords "scale")] [(245, immWords "owner")]
    (by native_decide) (immutableRuntime_size immWords)
    (by native_decide) (by native_decide)
    (by simp [Layout.writes, immutableLayout_sites, WindowDisjointFromWrites,
      UInt256.toNat, UInt256.size] <;> native_decide)
    (by native_decide) (by rfl)
    (by
      rw [writeCascade_size]
      · simp [writeCascadeSize] <;> native_decide
      · simp [WriteGapsOk] <;> native_decide)
    (by simp [WindowDisjointFromWrites] <;> native_decide)

theorem immutableDecode_185 (immWords : String → UInt256) :
    decode (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) (⟨185⟩ : UInt256) =
      some (.Push .PUSH32, some (immWords "scale", 32)) := by
  exact Layout.decodeSite (pc := (⟨185⟩ : UInt256)) (words := immWords)
    186 "scale" [] [(361, immWords "scale"), (72, immWords "owner"), (245, immWords "owner")]
    (by native_decide) (immutableRuntime_size immWords)
    (by native_decide) (by native_decide)
    (by simp [Layout.writes, immutableLayout_sites, WindowDisjointFromWrites,
      UInt256.toNat, UInt256.size] <;> native_decide)
    (by native_decide) (by rfl)
    (by
      rw [writeCascade_size]
      · simp [writeCascadeSize] <;> native_decide
      · simp [WriteGapsOk] <;> native_decide)
    (by simp [WindowDisjointFromWrites] <;> native_decide)

theorem immutableDecode_244 (immWords : String → UInt256) :
    decode (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) (⟨244⟩ : UInt256) =
      some (.Push .PUSH32, some (immWords "owner", 32)) := by
  exact Layout.decodeSite (pc := (⟨244⟩ : UInt256)) (words := immWords)
    245 "owner" [(186, immWords "scale"), (361, immWords "scale"), (72, immWords "owner")] []
    (by native_decide) (immutableRuntime_size immWords)
    (by native_decide) (by native_decide)
    (by simp [Layout.writes, immutableLayout_sites, WindowDisjointFromWrites,
      UInt256.toNat, UInt256.size] <;> native_decide)
    (by native_decide) (by rfl)
    (by
      rw [writeCascade_size]
      · simp [writeCascadeSize] <;> native_decide
      · simp [WriteGapsOk] <;> native_decide)
    (by simp [WindowDisjointFromWrites] <;> native_decide)

theorem immutableDecode_360 (immWords : String → UInt256) :
    decode (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) (⟨360⟩ : UInt256) =
      some (.Push .PUSH32, some (immWords "scale", 32)) := by
  exact Layout.decodeSite (pc := (⟨360⟩ : UInt256)) (words := immWords)
    361 "scale" [(186, immWords "scale")] [(72, immWords "owner"), (245, immWords "owner")]
    (by native_decide) (immutableRuntime_size immWords)
    (by native_decide) (by native_decide)
    (by simp [Layout.writes, immutableLayout_sites, WindowDisjointFromWrites,
      UInt256.toNat, UInt256.size] <;> native_decide)
    (by native_decide) (by rfl)
    (by
      rw [writeCascade_size]
      · simp [writeCascadeSize] <;> native_decide
      · simp [WriteGapsOk] <;> native_decide)
    (by simp [WindowDisjointFromWrites] <;> native_decide)

/-- Final stack for bytecode block summary `tinyImmutable_block_0_taken`. -/
def tinyImmutable_block_0_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  (ee.weiValue :: R)

/-- Final memory for bytecode block summary `tinyImmutable_block_0_taken`. -/
def tinyImmutable_block_0_taken_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 128).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem tinyImmutable_block_0_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) 0).contains (UInt256.ofNat 15) = true)
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 15) (tinyImmutable_block_0_taken_stack (ee := ee) (R := R)) (tinyImmutable_block_0_taken_memory (mem := mem)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((30) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 128) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨0⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨2⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := RD.genMstore r2 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨4⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.callvalue (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨5⟩ : UInt256), UInt8.ofNat 52, .CALLVALUE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup1 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨6⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.iszero (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨7⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 15) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨8⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 15), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiT (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨11⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 15)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tinyImmutable_block_0_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) 0).contains (UInt256.ofNat 15) = true)
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 15) (tinyImmutable_block_0_taken_stack (ee := ee) (R := R)) (tinyImmutable_block_0_taken_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tinyImmutable_block_0_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `tinyImmutable_block_0_fallthrough`. -/
def tinyImmutable_block_0_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  (ee.weiValue :: R)

/-- Final memory for bytecode block summary `tinyImmutable_block_0_fallthrough`. -/
def tinyImmutable_block_0_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 128).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem tinyImmutable_block_0_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) = (UInt256.ofNat 0))
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 12) (tinyImmutable_block_0_fallthrough_stack (ee := ee) (R := R)) (tinyImmutable_block_0_fallthrough_memory (mem := mem)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((30) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 128) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨0⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨2⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := RD.genMstore r2 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨4⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.callvalue (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨5⟩ : UInt256), UInt8.ofNat 52, .CALLVALUE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup1 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨6⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.iszero (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨7⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 15) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨8⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 15), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiNT (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨11⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tinyImmutable_block_0_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) = (UInt256.ofNat 0))
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 12) (tinyImmutable_block_0_fallthrough_stack (ee := ee) (R := R)) (tinyImmutable_block_0_fallthrough_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tinyImmutable_block_0_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 12. -/
theorem tinyImmutable_block_12 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 12) R mem aw rdata σ k C)
    : RDrev (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.push0 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨12⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨13⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRev r2 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨14⟩ : UInt256), UInt8.ofNat 253, .REVERT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Final stack for bytecode block summary `tinyImmutable_block_15_taken`. -/
def tinyImmutable_block_15_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 15. -/
theorem tinyImmutable_block_15_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) 0).contains (UInt256.ofNat 63) = true)
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 15) (x0 :: R) mem aw rdata σ k C)
    : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 63) (tinyImmutable_block_15_taken_stack (R := R)) mem aw rdata σ (k + 7) (C + ((24))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨15⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨16⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 4) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨17⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.calldatasize (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨19⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.lt (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨20⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 63) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨21⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 63), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jumpiT (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨24⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 63)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tinyImmutable_block_15_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) 0).contains (UInt256.ofNat 63) = true)
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 15) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 63) (tinyImmutable_block_15_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tinyImmutable_block_15_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `tinyImmutable_block_15_fallthrough`. -/
def tinyImmutable_block_15_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 15. -/
theorem tinyImmutable_block_15_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) = (UInt256.ofNat 0))
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 15) (x0 :: R) mem aw rdata σ k C)
    : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 25) (tinyImmutable_block_15_fallthrough_stack (R := R)) mem aw rdata σ (k + 7) (C + ((24))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨15⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨16⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 4) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨17⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.calldatasize (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨19⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.lt (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨20⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 63) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨21⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 63), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jumpiNT (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨24⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 25)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tinyImmutable_block_15_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) = (UInt256.ofNat 0))
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 15) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 25) (tinyImmutable_block_15_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tinyImmutable_block_15_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `tinyImmutable_block_25_taken`. -/
def tinyImmutable_block_25_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 25. -/
theorem tinyImmutable_block_25_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2376452955) (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) 0).contains (UInt256.ofNat 67) = true)
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 25) R mem aw rdata σ k C)
    : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 67) (tinyImmutable_block_25_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 9) (C + ((33))) := by
  let r0 := h
  have r1 := r0.push0 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨25⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.calldataload (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨26⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 224) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨27⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 224), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.shr (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨29⟩ : UInt256), UInt8.ofNat 28, .SHR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup1 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨30⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push4 (UInt256.ofNat 2376452955) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨31⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 2376452955), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.eq (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨36⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 67) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨37⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 67), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.jumpiT (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨40⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 67)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tinyImmutable_block_25_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2376452955) (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) 0).contains (UInt256.ofNat 67) = true)
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 25) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 67) (tinyImmutable_block_25_taken_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tinyImmutable_block_25_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `tinyImmutable_block_25_fallthrough`. -/
def tinyImmutable_block_25_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 25. -/
theorem tinyImmutable_block_25_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2376452955) (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))) = (UInt256.ofNat 0))
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 25) R mem aw rdata σ k C)
    : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 41) (tinyImmutable_block_25_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 9) (C + ((33))) := by
  let r0 := h
  have r1 := r0.push0 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨25⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.calldataload (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨26⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 224) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨27⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 224), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.shr (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨29⟩ : UInt256), UInt8.ofNat 28, .SHR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup1 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨30⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push4 (UInt256.ofNat 2376452955) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨31⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 2376452955), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.eq (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨36⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 67) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨37⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 67), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.jumpiNT (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨40⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 41)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tinyImmutable_block_25_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2376452955) (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))) = (UInt256.ofNat 0))
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 25) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 41) (tinyImmutable_block_25_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tinyImmutable_block_25_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 41. -/
theorem tinyImmutable_block_41_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3978024812) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) 0).contains (UInt256.ofNat 148) = true)
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 41) (x0 :: R) mem aw rdata σ k C)
    : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 148) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨41⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 3978024812) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨42⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 3978024812), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨47⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 148) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨48⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 148), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨51⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 148)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tinyImmutable_block_41_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3978024812) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) 0).contains (UInt256.ofNat 148) = true)
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 41) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 148) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tinyImmutable_block_41_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 41. -/
theorem tinyImmutable_block_41_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3978024812) x0) = (UInt256.ofNat 0))
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 41) (x0 :: R) mem aw rdata σ k C)
    : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 52) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨41⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 3978024812) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨42⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 3978024812), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨47⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 148) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨48⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 148), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨51⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 52)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tinyImmutable_block_41_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3978024812) x0) = (UInt256.ofNat 0))
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 41) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 52) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tinyImmutable_block_41_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 52. -/
theorem tinyImmutable_block_52_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 4112390170) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) 0).contains (UInt256.ofNat 181) = true)
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 52) (x0 :: R) mem aw rdata σ k C)
    : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 181) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨52⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 4112390170) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨53⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 4112390170), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨58⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 181) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨59⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 181), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨62⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 181)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tinyImmutable_block_52_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 4112390170) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) 0).contains (UInt256.ofNat 181) = true)
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 52) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 181) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tinyImmutable_block_52_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 52. -/
theorem tinyImmutable_block_52_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 4112390170) x0) = (UInt256.ofNat 0))
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 52) (x0 :: R) mem aw rdata σ k C)
    : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 63) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨52⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 4112390170) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨53⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 4112390170), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨58⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 181) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨59⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 181), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨62⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 63)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tinyImmutable_block_52_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 4112390170) x0) = (UInt256.ofNat 0))
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 52) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 63) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tinyImmutable_block_52_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 63. -/
theorem tinyImmutable_block_63 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 63) R mem aw rdata σ k C)
    : RDrev (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨63⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨64⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push0 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨65⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRev r3 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨66⟩ : UInt256), UInt8.ofNat 253, .REVERT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Final stack for bytecode block summary `tinyImmutable_block_67`. -/
def tinyImmutable_block_67_stack {immWords : String → UInt256} {R : List UInt256} : List UInt256 :=
  ((immWords "owner") :: (UInt256.ofNat 106) :: R)

/-- Automatically generated RD summary for bytecode block at pc 67. -/
theorem tinyImmutable_block_67 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) 0).contains (UInt256.ofNat 106) = true)
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 67) R mem aw rdata σ k C)
    : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 106) (tinyImmutable_block_67_stack (immWords := immWords) (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨67⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 106) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨68⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 106), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pushConst (immWords "owner") (width := 32) (op := .PUSH32) (by decide) (by
    conv_lhs => arg 2; change (⟨71⟩ : UInt256)
    exact immutableDecode_71 immWords) (by evm_ov)
  have r4 := r3.dup2 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨104⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jump (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨105⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 106)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tinyImmutable_block_67_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) 0).contains (UInt256.ofNat 106) = true)
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 67) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 106) (tinyImmutable_block_67_stack (immWords := immWords) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tinyImmutable_block_67 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `tinyImmutable_block_106`. -/
def tinyImmutable_block_106_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)) :: R)

/-- Final memory for bytecode block summary `tinyImmutable_block_106`. -/
def tinyImmutable_block_106_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((UInt256.land x0 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 106. -/
theorem tinyImmutable_block_106 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 106) (x0 :: R) mem aw rdata σ k C)
    : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 139) (tinyImmutable_block_106_stack (mem := mem) (R := R)) (tinyImmutable_block_106_memory (mem := mem) (x0 := x0)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) rdata σ (k + 11) (C + ((31) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨106⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨107⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := RD.genMload r2 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨109⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨110⟩ : UInt256), UInt8.ofNat 115, .Push .PUSH20, some ((UInt256.ofNat 1461501637330902918203684832716283019655932542975), 20), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap1 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨131⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.swap2 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨132⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.and (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨133⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup2 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨134⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := RD.genMstore r8 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨135⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 32) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨136⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.add (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨138⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 139)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tinyImmutable_block_106_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 106) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 139) (tinyImmutable_block_106_stack (mem := mem) (R := R)) (tinyImmutable_block_106_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tinyImmutable_block_106 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 139. -/
theorem tinyImmutable_block_139 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 139) (x0 :: R) mem aw rdata σ k C)
    : RDret (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) g s0 σ (mem.readWithPadding (memLoad (UInt256.ofNat 64) mem).toNat (UInt256.sub x0 (memLoad (UInt256.ofNat 64) mem)).toNat) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨139⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨140⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := RD.genMload r2 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨142⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup1 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨143⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap2 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨144⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.sub (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨145⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap1 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨146⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRet r7 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨147⟩ : UInt256), UInt8.ofNat 243, .RETURN, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Final stack for bytecode block summary `tinyImmutable_block_148`. -/
def tinyImmutable_block_148_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 4) :: (UInt256.ofNat ee.calldata.size) :: (UInt256.ofNat 162) :: (UInt256.ofNat 167) :: R)

/-- Automatically generated RD summary for bytecode block at pc 148. -/
theorem tinyImmutable_block_148 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) 0).contains (UInt256.ofNat 396) = true)
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 148) R mem aw rdata σ k C)
    : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 396) (tinyImmutable_block_148_stack (ee := ee) (R := R)) mem aw rdata σ (k + 7) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨148⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 167) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨149⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 167), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 162) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨152⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 162), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.calldatasize (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨155⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 4) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨156⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 396) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨158⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 396), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jump (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨161⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 396)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tinyImmutable_block_148_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) 0).contains (UInt256.ofNat 396) = true)
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 148) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 396) (tinyImmutable_block_148_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tinyImmutable_block_148 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 162. -/
theorem tinyImmutable_block_162 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) 0).contains (UInt256.ofNat 220) = true)
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 162) R mem aw rdata σ k C)
    : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 220) R mem aw rdata σ (k + 3) (C + ((12))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨162⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 220) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨163⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 220), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.jump (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨166⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 220)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tinyImmutable_block_162_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) 0).contains (UInt256.ofNat 220) = true)
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 162) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 220) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tinyImmutable_block_162 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `tinyImmutable_block_167`. -/
def tinyImmutable_block_167_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)) :: R)

/-- Final memory for bytecode block summary `tinyImmutable_block_167`. -/
def tinyImmutable_block_167_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 167. -/
theorem tinyImmutable_block_167 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) 0).contains (UInt256.ofNat 139) = true)
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 167) (x0 :: R) mem aw rdata σ k C)
    : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 139) (tinyImmutable_block_167_stack (mem := mem) (R := R)) (tinyImmutable_block_167_memory (mem := mem) (x0 := x0)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) rdata σ (k + 10) (C + ((33) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨167⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨168⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := RD.genMload r2 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨170⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap1 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨171⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup2 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨172⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMstore r5 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨173⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨174⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.add (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨176⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 139) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨177⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 139), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.jump (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨180⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 139)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tinyImmutable_block_167_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) 0).contains (UInt256.ofNat 139) = true)
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 167) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 139) (tinyImmutable_block_167_stack (mem := mem) (R := R)) (tinyImmutable_block_167_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tinyImmutable_block_167 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `tinyImmutable_block_181`. -/
def tinyImmutable_block_181_stack {immWords : String → UInt256} {R : List UInt256} : List UInt256 :=
  ((immWords "scale") :: (UInt256.ofNat 167) :: R)

/-- Automatically generated RD summary for bytecode block at pc 181. -/
theorem tinyImmutable_block_181 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) 0).contains (UInt256.ofNat 167) = true)
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 181) R mem aw rdata σ k C)
    : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 167) (tinyImmutable_block_181_stack (immWords := immWords) (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨181⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 167) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨182⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 167), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pushConst (immWords "scale") (width := 32) (op := .PUSH32) (by decide) (by
    conv_lhs => arg 2; change (⟨185⟩ : UInt256)
    exact immutableDecode_185 immWords) (by evm_ov)
  have r4 := r3.dup2 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨218⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jump (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨219⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 167)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tinyImmutable_block_181_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) 0).contains (UInt256.ofNat 167) = true)
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 181) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 167) (tinyImmutable_block_181_stack (immWords := immWords) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tinyImmutable_block_181 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `tinyImmutable_block_220_taken`. -/
def tinyImmutable_block_220_taken_stack {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: R)

/-- Automatically generated RD summary for bytecode block at pc 220. -/
theorem tinyImmutable_block_220_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.land (immWords "owner") (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) (UInt256.ofNat ee.source.val)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) 0).contains (UInt256.ofNat 358) = true)
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 220) R mem aw rdata σ k C)
    : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 358) (tinyImmutable_block_220_taken_stack (R := R)) mem aw rdata σ (k + 9) (C + ((30))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨220⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨221⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.caller (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨222⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨223⟩ : UInt256), UInt8.ofNat 115, .Push .PUSH20, some ((UInt256.ofNat 1461501637330902918203684832716283019655932542975), 20), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.pushConst (immWords "owner") (width := 32) (op := .PUSH32) (by decide) (by
    conv_lhs => arg 2; change (⟨244⟩ : UInt256)
    exact immutableDecode_244 immWords) (by evm_ov)
  have r6 := r5.and (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨277⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.eq (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨278⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 358) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨279⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 358), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.jumpiT (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨282⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 358)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tinyImmutable_block_220_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.land (immWords "owner") (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) (UInt256.ofNat ee.source.val)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) 0).contains (UInt256.ofNat 358) = true)
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 220) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 358) (tinyImmutable_block_220_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tinyImmutable_block_220_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `tinyImmutable_block_220_fallthrough`. -/
def tinyImmutable_block_220_fallthrough_stack {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: R)

/-- Automatically generated RD summary for bytecode block at pc 220. -/
theorem tinyImmutable_block_220_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.land (immWords "owner") (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) (UInt256.ofNat ee.source.val)) = (UInt256.ofNat 0))
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 220) R mem aw rdata σ k C)
    : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 283) (tinyImmutable_block_220_fallthrough_stack (R := R)) mem aw rdata σ (k + 9) (C + ((30))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨220⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨221⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.caller (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨222⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨223⟩ : UInt256), UInt8.ofNat 115, .Push .PUSH20, some ((UInt256.ofNat 1461501637330902918203684832716283019655932542975), 20), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.pushConst (immWords "owner") (width := 32) (op := .PUSH32) (by decide) (by
    conv_lhs => arg 2; change (⟨244⟩ : UInt256)
    exact immutableDecode_244 immWords) (by evm_ov)
  have r6 := r5.and (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨277⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.eq (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨278⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 358) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨279⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 358), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.jumpiNT (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨282⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 283)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tinyImmutable_block_220_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.land (immWords "owner") (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) (UInt256.ofNat ee.source.val)) = (UInt256.ofNat 0))
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 220) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 283) (tinyImmutable_block_220_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tinyImmutable_block_220_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 283. -/
theorem tinyImmutable_block_283 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 283) R mem aw rdata σ k C)
    : RDrev (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨283⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := RD.genMload r1 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨285⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 4594637) (width := 3) (op := .PUSH3) (by decide) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨286⟩ : UInt256), UInt8.ofNat 98, .Push .PUSH3, some ((UInt256.ofNat 4594637), 3), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 229) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨290⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 229), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.shl (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨292⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup2 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨293⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMstore r6 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨294⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨295⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 4) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨297⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.dup3 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨299⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.add (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨300⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := RD.genMstore r11 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨301⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 5) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨302⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 5), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 36) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨304⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 36), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.dup3 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨306⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.add (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨307⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := RD.genMstore r16 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨308⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.pushConst (UInt256.ofNat 50417742920509558439106150551775209266858149941038353264781520106005609840640) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨309⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 50417742920509558439106150551775209266858149941038353264781520106005609840640), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 68) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨342⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 68), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.dup3 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨344⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.add (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨345⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := RD.genMstore r21 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨346⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 100) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨347⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 100), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.add (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨349⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 64) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨350⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := RD.genMload r25 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨352⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.dup1 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨353⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.swap2 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨354⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r29 := r28.sub (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨355⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r30 := r29.swap1 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨356⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRev r30 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨357⟩ : UInt256), UInt8.ofNat 253, .REVERT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Final stack for bytecode block summary `tinyImmutable_block_358`. -/
def tinyImmutable_block_358_stack {immWords : String → UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.mul (immWords "scale") x1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 358. -/
theorem tinyImmutable_block_358 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) 0).contains x2 = true)
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 358) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 x2 (tinyImmutable_block_358_stack (immWords := immWords) (x1 := x1) (R := R)) mem aw rdata σ (k + 6) (C + ((22))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨358⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨359⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pushConst (immWords "scale") (width := 32) (op := .PUSH32) (by decide) (by
    conv_lhs => arg 2; change (⟨360⟩ : UInt256)
    exact immutableDecode_360 immWords) (by evm_ov)
  have r4 := r3.mul (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨393⟩ : UInt256), UInt8.ofNat 2, .MUL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap1 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨394⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.jump (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨395⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  exact RD.normalizeCounters r6 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tinyImmutable_block_358_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) 0).contains x2 = true)
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 358) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 x2 (tinyImmutable_block_358_stack (immWords := immWords) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tinyImmutable_block_358 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `tinyImmutable_block_396_taken`. -/
def tinyImmutable_block_396_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 396. -/
theorem tinyImmutable_block_396_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) 0).contains (UInt256.ofNat 412) = true)
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 396) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 412) (tinyImmutable_block_396_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((34))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨396⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨397⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨398⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup3 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨400⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup5 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨401⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.sub (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨402⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.slt (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨403⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.iszero (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨404⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 412) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨405⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 412), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.jumpiT (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨408⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 412)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tinyImmutable_block_396_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) 0).contains (UInt256.ofNat 412) = true)
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 396) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 412) (tinyImmutable_block_396_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tinyImmutable_block_396_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `tinyImmutable_block_396_fallthrough`. -/
def tinyImmutable_block_396_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 396. -/
theorem tinyImmutable_block_396_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 396) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 409) (tinyImmutable_block_396_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((34))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨396⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨397⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨398⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup3 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨400⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup5 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨401⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.sub (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨402⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.slt (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨403⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.iszero (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨404⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 412) (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨405⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 412), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.jumpiNT (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨408⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 409)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tinyImmutable_block_396_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 396) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 409) (tinyImmutable_block_396_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tinyImmutable_block_396_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 409. -/
theorem tinyImmutable_block_409 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 409) R mem aw rdata σ k C)
    : RDrev (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.push0 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨409⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨410⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRev r2 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨411⟩ : UInt256), UInt8.ofNat 253, .REVERT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Final stack for bytecode block summary `tinyImmutable_block_412`. -/
def tinyImmutable_block_412_stack {ee : ExecutionEnv} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes x1.toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 412. -/
theorem tinyImmutable_block_412 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) 0).contains x3 = true)
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 412) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 x3 (tinyImmutable_block_412_stack (ee := ee) (x1 := x1) (R := R)) mem aw rdata σ (k + 7) (C + ((22))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨412⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨413⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.calldataload (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨414⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap2 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨415⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap1 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨416⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.pop (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨417⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jump (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨418⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  exact RD.normalizeCounters r7 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tinyImmutable_block_412_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) 0).contains x3 = true)
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 412) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 x3 (tinyImmutable_block_412_stack (ee := ee) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tinyImmutable_block_412 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 419. -/
theorem tinyImmutable_block_419 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (h : RD (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) ee g s0 (UInt256.ofNat 419) R mem aw rdata σ k C)
    : RDinvalid (TinyImmutable.immutableLayout.runtime TinyImmutable.tinyImmutableBytecode immWords) g s0 := by
  let r0 := h
  exact RD.invalid r0 (by immutable_decode(TinyImmutable.immutableLayout, TinyImmutable.tinyImmutableBytecode, immWords, (⟨419⟩ : UInt256), UInt8.ofNat 254, .INVALID, none, immutableLayout_inBounds, immutableTemplate_size64))

end tinyImmutableBlocks
