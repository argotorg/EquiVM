import Benchmarks.EAS.Attester.Common
import Benchmarks.EAS.Attester.Memory
import Reasoning.ABIViews

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

def attestMemory0 (schema input : UInt256) : ByteArray :=
  writeCascade solcFreePtrMem
    [(64, ⟨192⟩), (128, schema), (64, ⟨384⟩), (192, ⟨0⟩), (224, ⟨0⟩),
      (256, ⟨1⟩), (288, ⟨0⟩), (416, input)]

theorem attestMemory0_summary (schema input : UInt256) :
    attesterRuntime_block_1884_memory (mem := solcFreePtrMem) (x0 := input) (x1 := schema) =
      attestMemory0 schema input := by
  simp only [attesterRuntime_block_1884_memory]
  simp (disch := (first | decide +kernel |
    (simp only [wordWrite_size, solcFreePtrMem_size] <;> decide +kernel))) only
    [memLoad_write_same, memLoad_write_disjoint,
      show memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ from solcFreePtrMem_mload64]
  rfl

theorem attestMemory0_stack (schema input : UInt256) (words : String → UInt256)
    (R : List UInt256) :
    attesterRuntime_block_1884_stack (immWords := words) (mem := solcFreePtrMem)
      (x0 := input) (x1 := schema) (R := R) =
      [⟨416⟩, ⟨2057⟩, ⟨320⟩, ⟨192⟩, ⟨160⟩, ⟨128⟩, ⟨4050855399⟩,
        UInt256.land solcAddrMask (words "_eas"), ⟨0⟩, input, schema] ++ R := by
  simp only [attesterRuntime_block_1884_stack]
  simp (disch := (first | decide +kernel |
    (simp only [wordWrite_size, solcFreePtrMem_size] <;> decide +kernel))) only
    [memLoad_write_same, memLoad_write_disjoint,
      show memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ from solcFreePtrMem_mload64]
  rfl

def attestMemory1 (schema input : UInt256) : ByteArray :=
  writeCascade (attestMemory0 schema input)
    [(384, ⟨32⟩), (64, ⟨448⟩), (320, ⟨384⟩), (352, ⟨0⟩), (160, ⟨192⟩),
      (448, ⟨0xf17325e700000000000000000000000000000000000000000000000000000000⟩)]

theorem attestMemory1_summary (schema input : UInt256) :
    attesterRuntime_block_2057_memory (mem := attestMemory0 schema input)
      (x0 := ⟨448⟩) (x1 := ⟨320⟩) (x2 := ⟨192⟩) (x3 := ⟨160⟩) (x5 := ⟨4050855399⟩) =
      attestMemory1 schema input := by
  simp only [attesterRuntime_block_2057_memory, attestMemory0, writeCascade,
    Reasoning.Theory.writeWord]
  simp (disch := (first | decide +kernel |
    (simp only [wordWrite_size, solcFreePtrMem_size] <;> decide +kernel))) only
    [memLoad_write_same, memLoad_write_disjoint,
      show memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ from solcFreePtrMem_mload64]
  rfl

theorem attestMemory1_stack (schema input : UInt256) (R : List UInt256) :
    attesterRuntime_block_2057_stack (mem := attestMemory0 schema input)
      (x0 := ⟨448⟩) (x1 := ⟨320⟩) (x2 := ⟨192⟩) (x3 := ⟨160⟩) (x4 := ⟨128⟩)
      (x5 := ⟨4050855399⟩) (R := R) = [⟨452⟩, ⟨128⟩, ⟨2113⟩, ⟨4050855399⟩] ++ R := by
  simp only [attesterRuntime_block_2057_stack, attestMemory0, writeCascade,
    Reasoning.Theory.writeWord]
  simp (disch := (first | decide +kernel |
    (simp only [wordWrite_size, solcFreePtrMem_size] <;> decide +kernel))) only
    [memLoad_write_same, memLoad_write_disjoint,
      show memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ from solcFreePtrMem_mload64]
  rfl

def attestMemory2 (schema input : UInt256) : ByteArray :=
  writeCascade (attestMemory1 schema input) [(452, ⟨32⟩), (484, schema), (516, ⟨64⟩)]

theorem attestMemory2_summary (schema input : UInt256) :
    attesterRuntime_block_3782_memory (mem := attestMemory1 schema input)
      (x0 := ⟨452⟩) (x1 := ⟨128⟩) = attestMemory2 schema input := by
  simp only [attesterRuntime_block_3782_memory, attestMemory1, attestMemory0, writeCascade,
    Reasoning.Theory.writeWord]
  simp (disch := (first | decide +kernel |
    (simp only [wordWrite_size, solcFreePtrMem_size] <;> decide +kernel))) only
    [memLoad_write_same, memLoad_write_disjoint]
  rfl

theorem attestMemory2_stack (schema input : UInt256) (R : List UInt256) :
    attesterRuntime_block_3782_stack (mem := attestMemory1 schema input)
      (x0 := ⟨452⟩) (x1 := ⟨128⟩) (R := R) =
      [⟨192⟩, ⟨548⟩, ⟨3819⟩, ⟨192⟩, ⟨0⟩, ⟨452⟩, ⟨128⟩] ++ R := by
  simp only [attesterRuntime_block_3782_stack, attestMemory1, attestMemory0, writeCascade,
    Reasoning.Theory.writeWord]
  simp (disch := (first | decide +kernel |
    (simp only [wordWrite_size, solcFreePtrMem_size] <;> decide +kernel))) only
    [memLoad_write_same, memLoad_write_disjoint]
  rfl

def attestMemory3 (schema input : UInt256) : ByteArray :=
  writeCascade (attestMemory2 schema input)
    [(548, ⟨0⟩), (580, ⟨0⟩), (612, ⟨1⟩), (644, ⟨0⟩), (676, ⟨192⟩), (740, ⟨32⟩)]

set_option maxHeartbeats 1000000 in
theorem attestMemory3_summary (schema input : UInt256) :
    attesterRuntime_block_3109_memory (mem := attestMemory2 schema input)
      (x0 := ⟨192⟩) (x1 := ⟨548⟩) = attestMemory3 schema input := by
  simp only [attesterRuntime_block_3109_memory, attestMemory2, attestMemory1, attestMemory0,
    writeCascade, Reasoning.Theory.writeWord]
  simp (disch := (first | decide +kernel |
    (simp only [wordWrite_size, solcFreePtrMem_size] <;> decide +kernel))) only
    [memLoad_write_same, memLoad_write_disjoint]
  rfl

set_option maxHeartbeats 1000000 in
theorem attestMemory3_stack (schema input : UInt256) (R : List UInt256) :
    attesterRuntime_block_3109_stack (mem := attestMemory2 schema input)
      (x0 := ⟨192⟩) (x1 := ⟨548⟩) (R := R) =
      [⟨0⟩, ⟨32⟩, ⟨384⟩, ⟨0⟩, ⟨192⟩, ⟨548⟩] ++ R := by
  simp only [attesterRuntime_block_3109_stack, attestMemory2, attestMemory1, attestMemory0,
    writeCascade, Reasoning.Theory.writeWord]
  simp (disch := (first | decide +kernel |
    (simp only [wordWrite_size, solcFreePtrMem_size] <;> decide +kernel))) only
    [memLoad_write_same, memLoad_write_disjoint]
  rfl

def attestMemory4 (schema input : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord (attestMemory3 schema input) 772 input

theorem attestMemory4_summary (schema input : UInt256) :
    attesterRuntime_block_3211_memory (mem := attestMemory3 schema input)
      (x0 := ⟨0⟩) (x2 := ⟨384⟩) (x5 := ⟨548⟩) = attestMemory4 schema input := by
  simp only [attesterRuntime_block_3211_memory, attestMemory3, attestMemory2, attestMemory1,
    attestMemory0, writeCascade, Reasoning.Theory.writeWord]
  simp (disch := (first | decide +kernel |
    (simp only [wordWrite_size, solcFreePtrMem_size] <;> decide +kernel))) only
    [memLoad_write_same, memLoad_write_disjoint]
  rfl

def attestMemory (schema input : UInt256) : ByteArray :=
  writeCascade (attestMemory4 schema input) [(804, ⟨0⟩), (708, ⟨0⟩)]

theorem attestMemory_summary (schema input : UInt256) :
    attesterRuntime_block_3231_memory (mem := attestMemory4 schema input)
      (x1 := ⟨32⟩) (x4 := ⟨192⟩) (x5 := ⟨548⟩) = attestMemory schema input := by
  simp only [attesterRuntime_block_3231_memory, attestMemory4, attestMemory3, attestMemory2,
    attestMemory1, attestMemory0, writeCascade, Reasoning.Theory.writeWord]
  simp (disch := (first | decide +kernel |
    (simp only [wordWrite_size, solcFreePtrMem_size] <;> decide +kernel))) only
    [memLoad_write_same, memLoad_write_disjoint]
  rfl

theorem attestMemory_size (schema input : UInt256) : (attestMemory schema input).size = 836 := by
  simp only [attestMemory, attestMemory4, attestMemory3, attestMemory2, attestMemory1,
    attestMemory0, writeCascade, Reasoning.Theory.writeWord, wordWrite_size, solcFreePtrMem_size]
  rfl

theorem attestMemory_freePtr (schema input : UInt256) :
    memLoad (UInt256.ofNat 64) (attestMemory schema input) = ⟨448⟩ := by
  simp only [attestMemory, attestMemory4, attestMemory3, attestMemory2, attestMemory1,
    attestMemory0, writeCascade, Reasoning.Theory.writeWord]
  simp (disch := (first | decide +kernel |
    (simp only [wordWrite_size, solcFreePtrMem_size] <;> decide +kernel))) only
    [memLoad_write_same, memLoad_write_disjoint]

end Benchmarks.EAS.Attester
