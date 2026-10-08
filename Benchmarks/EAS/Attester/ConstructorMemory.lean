import Benchmarks.EAS.Attester.ConstructorSource
import Benchmarks.EAS.Attester.PairAllocMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.EAS.Attester.Immutables attesterCreationBlocks

namespace Benchmarks.EAS.Attester

def constructorCode (eas : AccountAddress) : ByteArray :=
  attesterCreationBytecode ++ (UInt256.ofNat eas.val).toByteArray

def constructorFreeMemory : ByteArray := writeWord ByteArray.empty 64 ⟨160⟩

def constructorABIMemory (eas : AccountAddress) : ByteArray :=
  writeWord (writeWord constructorFreeMemory 160 (UInt256.ofNat eas.val)) 64 ⟨192⟩

def constructorMemory (eas : AccountAddress) : ByteArray :=
  writeWord (constructorABIMemory eas) 128 (UInt256.ofNat eas.val)

def constructorPatchedMemory (eas : AccountAddress) : ByteArray :=
  writeCascade attesterBytecode [(824, UInt256.ofNat eas.val), (1719, UInt256.ofNat eas.val),
    (1888, UInt256.ofNat eas.val), (2289, UInt256.ofNat eas.val)]

theorem constructorCreation_size : attesterCreationBytecode.size = 4057 := by native_decide
theorem constructorRuntime_size : attesterBytecode.size = 3865 := by native_decide

theorem constructorCode_size (eas : AccountAddress) : (constructorCode eas).size = 4089 := by
  rw [constructorCode, ByteArray.size_append, constructorCreation_size, toByteArray_size]

theorem constructorCode_tail (eas : AccountAddress) :
    (constructorCode eas).extract 4057 (4057 + 32) = (UInt256.ofNat eas.val).toByteArray :=
  extract_append_right' _ _ _ _ constructorCreation_size.symm
    (by rw [constructorCreation_size, toByteArray_size])

theorem constructorCode_runtime (eas : AccountAddress) :
    (constructorCode eas).extract 192 (192 + 3865) = attesterBytecode := by
  rw [constructorCode, extract_append_left _ _ _ _ (by rw [constructorCreation_size])]
  native_decide

theorem constructorFreeMemory_size : constructorFreeMemory.size = 96 := by
  rw [constructorFreeMemory, writeWord_sparse_size]; rfl

theorem constructorFreeMemory_load : memLoad (UInt256.ofNat 64) constructorFreeMemory = ⟨160⟩ :=
  memLoad_write_same _ _ _ _ rfl

theorem constructorCode_copyArg (eas : AccountAddress) :
    (constructorCode eas).write 4057 constructorFreeMemory 160 32 =
      writeWord constructorFreeMemory 160 (UInt256.ofNat eas.val) := by
  rw [write_from_gap_eq _ _ _ _ _ (by decide) (by rw [constructorCode_size])
    (by rw [constructorFreeMemory_size]; decide)
    (by rw [constructorFreeMemory_size]; exact lt_usize _ (by decide)), constructorCode_tail,
    Reasoning.Theory.writeWord, toByteArray_write_eq _ _ _
      (by rw [constructorFreeMemory_size]; decide)
      (by rw [constructorFreeMemory_size]; exact lt_usize _ (by decide))]

theorem constructorABIMemory_size (eas : AccountAddress) :
    (constructorABIMemory eas).size = 192 := by
  rw [constructorABIMemory, writeWord_sparse_size, writeWord_sparse_size,
      constructorFreeMemory_size]
  rfl

theorem constructorABIMemory_load (eas : AccountAddress) :
    memLoad (UInt256.ofNat 160) (constructorABIMemory eas) = UInt256.ofNat eas.val := by
  simp only [constructorABIMemory, Reasoning.Theory.writeWord]
  rw [memLoad_write_disjoint _ _ _ _ (by rw [wordWrite_size, constructorFreeMemory_size]; decide)
    (.inr (by decide))]
  exact memLoad_write_same _ _ _ _ rfl

theorem constructorMemory_size (eas : AccountAddress) : (constructorMemory eas).size = 192 := by
  rw [constructorMemory, writeWord_sparse_size, constructorABIMemory_size]
  rfl

theorem constructorMemory_load (eas : AccountAddress) :
    memLoad (UInt256.ofNat 128) (constructorMemory eas) = UInt256.ofNat eas.val :=
  memLoad_write_same _ _ _ _ rfl

theorem constructorCode_copyRuntime (eas : AccountAddress) :
    (constructorCode eas).write 192 (constructorMemory eas) 0 3865 = attesterBytecode := by
  rw [write0_eq_extract_from_of_base_le _ _ _ _ (by decide)
    (by rw [constructorCode_size]; decide) (by rw [constructorMemory_size]; decide),
    constructorCode_runtime]

theorem constructorPatchedMemory_size (eas : AccountAddress) :
    (constructorPatchedMemory eas).size = 3865 := by
  simp only [constructorPatchedMemory, writeCascade, writeWord_sparse_size, constructorRuntime_size]
  rfl

theorem constructorPatchedMemory_deployed (eas : AccountAddress) :
    constructorPatchedMemory eas = deployedRuntime attesterBytecode (constructorFinalImms eas) := by
  rw [deployedRuntime_eq_layout (constructorFinalImms_fit eas)]
  simp only [constructorPatchedMemory, Layout.deployed, Layout.runtime, Layout.writes,
    immutableLayout, offsets, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.append_nil,
    wordsOf_of_get (constructorFinalImms_get eas) (show valueToWord (.address eas) =
      some (UInt256.ofNat eas.val) from rfl)]

theorem constructorPatchedMemory_read (eas : AccountAddress) :
    (constructorPatchedMemory eas).readWithPadding 0 3865 =
      deployedRuntime attesterBytecode (constructorFinalImms eas) := by
  rw [readWithPadding_eq_extract' _ _ _ (by decide) (by decide)
      (by rw [constructorPatchedMemory_size]),
    show 0 + 3865 = (constructorPatchedMemory eas).size by rw [constructorPatchedMemory_size],
    byteArray_extract_self, constructorPatchedMemory_deployed]

end Benchmarks.EAS.Attester
