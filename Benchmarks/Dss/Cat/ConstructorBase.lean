import Reasoning.WordArithmetic
import Reasoning.MemoryShapes
import Reasoning.Memory
import Benchmarks.Dss.Cat.Common
import Reasoning.ExternalCall
import Reasoning.Initcode
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Cat constructor shared helpers

Shared bytecode, memory, and storage-slot facts used by the Cat constructor trace and source
semantics proofs.  Ported from the sibling `Benchmarks/Dss/Pot`; Cat's constructor stores three
slots — `wards[sender] = 1`, `vat = vat_` (address slot 3), `live = 1` (scalar slot 2) — so it drops
Pot's four extra scalar stores and packs `vat` into slot 3 (not slot 5).
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Cat

set_option maxRecDepth 2000000

/-- ABI-encoded constructor argument appended to `catCreationBytecode`. -/
def catCtorArgsTail (vat : AccountAddress) : ByteArray :=
  (EVM.Word.toBytesBE (EVM.word vat.val)).toByteArray

def catCtorCode (vat : AccountAddress) : ByteArray :=
  catCreationBytecode ++ catCtorArgsTail vat

theorem catCtorDeployment_shape {args : List Value} {deployedInitcode : ByteArray}
    (hdeploy : config.selfDeployment catCreationBytecode args = some deployedInitcode) :
    ∃ vat : AccountAddress,
      args = [.address vat] ∧ deployedInitcode = catCtorCode vat := by
  simp [config, contract, constructorDecl, Solm.genSolidityConstructorDeployment] at hdeploy
  cases args with
  | nil =>
      simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, addr] at hdeploy
  | cons a rest =>
      cases rest with
      | cons _ _ =>
          cases a <;> simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, addr,
            ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
            ABI.encodeABIValue?, ABI.encodeABIWord?] at hdeploy
      | nil =>
          cases a <;> simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, addr,
            ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
            ABI.encodeABIValue?, ABI.encodeABIWord?] at hdeploy
          rename_i vat
          refine ⟨vat, rfl, ?_⟩
          simpa [catCtorCode, catCtorArgsTail] using hdeploy.symm

macro "cat_ctor_decode" : tactic =>
  `(tactic|
    (first
      | rw [Reasoning.Theory.decode_append_left_window
          catCreationBytecode _ _ (by native_decide) (by native_decide)]
      | (unfold catCtorCode
         rw [Reasoning.Theory.decode_append_left_window
          catCreationBytecode _ _ (by native_decide) (by native_decide)]);
     native_decide))

macro "cat_ctor_jd" : tactic =>
  `(tactic|
    (first
      | exact Reasoning.Theory.D_J_contains_append_left catCreationBytecode _ _ (by jump_dest)
      | (unfold catCtorCode
         exact Reasoning.Theory.D_J_contains_append_left catCreationBytecode _ _ (by jump_dest))))

open Lean in
macro "cat_ctor_run " base:term " with " "[" steps:evmStep,* "]" : term => do
  let mut acc := base
  for s in steps.getElems do
    match s with
    | `(evmStep| raw $op:ident $args*) =>
        acc ← `($(acc).$op $args*)
    | `(evmStep| $op:ident $args*) =>
        match op.getId with
        | `jump    => acc ← `($(acc).jump (by cat_ctor_decode) $(args[0]!) (by evm_ov))
        | `jumpiT  => acc ← `($(acc).jumpiT (by cat_ctor_decode) $(args[0]!) $(args[1]!)
                            (by evm_ov))
        | `jumpiNT => acc ← `($(acc).jumpiNT (by cat_ctor_decode) $(args[0]!) (by evm_ov))
        | _        => acc ← `($(acc).$op $args* (by cat_ctor_decode) (by evm_ov))
    | _ => Macro.throwUnsupported
  return acc

theorem catCreationBytecode_size : catCreationBytecode.size = 3999 := by
  native_decide

theorem catBytecode_size : catBytecode.size = 3873 := by
  native_decide

theorem catCtorArgsTail_size (vat : AccountAddress) : (catCtorArgsTail vat).size = 32 := by
  simpa [catCtorArgsTail] using word_toBytesBE_toByteArray_size (EVM.word vat.val)

theorem catCtorCode_size (vat : AccountAddress) : (catCtorCode vat).size = 4031 := by
  unfold catCtorCode
  rw [ByteArray.size_append, catCreationBytecode_size, catCtorArgsTail_size]

theorem catCtorArgLen_eq (vat : AccountAddress) :
    (UInt256.ofNat (catCtorCode vat).size).sub ⟨3999⟩ = (⟨32⟩ : UInt256) := by
  rw [catCtorCode_size]
  native_decide

theorem catCreationBytecode_runtime_window :
    catCreationBytecode.extract 126 (126 + 3873) = catBytecode := by
  native_decide


def catCtorArgMem (vat : AccountAddress) : ByteArray :=
  (catCtorCode vat).write 3999 solcFreePtrMem 128 32

def catCtorArgFreeMem (vat : AccountAddress) : ByteArray :=
  (UInt256.toByteArray ⟨160⟩).write 0 (catCtorArgMem vat) 64 32

theorem catCtorArgMem_eq (vat : AccountAddress) :
    catCtorArgMem vat =
      solcFreePtrMem ++ ByteArray.zeroes 32 ++ catCtorArgsTail vat := by
  rw [catCtorArgMem, catCtorCode, byteArray_write_from_ge_eq]
  · rw [extract_append_right' catCreationBytecode (catCtorArgsTail vat) 3999 (3999 + 32)]
    · rw [solcFreePtrMem_size]
    · exact catCreationBytecode_size.symm
    · rw [catCtorArgsTail_size]
      native_decide
  · decide
  · rw [ByteArray.size_append, catCreationBytecode_size, catCtorArgsTail_size]
  · rw [solcFreePtrMem_size]
    decide
  · rw [solcFreePtrMem_size]
    exact lt_usize 32 (by norm_num)

theorem catCtorArgMem_size (vat : AccountAddress) : (catCtorArgMem vat).size = 160 := by
  rw [catCtorArgMem_eq, ByteArray.size_append, ByteArray.size_append, solcFreePtrMem_size,
    zeroes_ofNat_size 32 (by norm_num), catCtorArgsTail_size]

theorem catCtorArgFreeMem_size (vat : AccountAddress) :
    (catCtorArgFreeMem vat).size = 160 := by
  unfold catCtorArgFreeMem
  exact toByteArray_write32_size_of_le (base := catCtorArgMem vat) (word := (⟨160⟩ : UInt256))
    (off := 64) (baseSize := 160) (finalSize := 160) (catCtorArgMem_size vat)
    (by rw [catCtorArgMem_size]; omega) (by omega)

theorem catCtorArgMem_read128 (vat : AccountAddress) :
    (catCtorArgMem vat).readWithPadding 128 32 =
      UInt256.toByteArray (EVM.word vat.val) := by
  rw [catCtorArgMem_eq]
  have hprefix :
      (solcFreePtrMem ++ ByteArray.zeroes 32).size = 128 := by
    rw [ByteArray.size_append, solcFreePtrMem_size, zeroes_ofNat_size 32 (by norm_num)]
  rw [readWithPadding_eq_extract'
    (solcFreePtrMem ++ ByteArray.zeroes 32 ++ catCtorArgsTail vat)
    128 32 (by norm_num) (by norm_num) (by
      rw [ByteArray.size_append, hprefix, catCtorArgsTail_size])]
  rw [extract_append_right_window
    (solcFreePtrMem ++ ByteArray.zeroes 32) (catCtorArgsTail vat) 128
    (128 + 32) (by rw [hprefix]), hprefix]
  rw [show 128 - 128 = 0 by omega, show 128 + 32 - 128 = 32 by omega]
  simp [catCtorArgsTail, word_toBytesBE_toByteArray_eq_toByteArray, toByteArray_extract_all]

theorem catCtorArgFreeMem_read128 (vat : AccountAddress) :
    (catCtorArgFreeMem vat).readWithPadding 128 32 =
      UInt256.toByteArray (EVM.word vat.val) := by
  unfold catCtorArgFreeMem
  rw [write32_read_above _ _ 64 128 (by rw [toByteArray_size])
    (by rw [catCtorArgMem_size]; omega) (by omega) (by rw [catCtorArgMem_size])]
  exact catCtorArgMem_read128 vat

theorem catCtorArgFreeMem_mload128 (vat : AccountAddress) :
    (if (⟨128⟩ : UInt256).toNat ≥ (catCtorArgFreeMem vat).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((catCtorArgFreeMem vat).readWithPadding 128 32))) =
      EVM.word vat.val := by
  exact mloadWordValue_of_readWithPadding
    (mem := catCtorArgFreeMem vat) (off := ⟨128⟩)
    (v := EVM.word vat.val)
    (by rw [catCtorArgFreeMem_size]; decide)
    (catCtorArgFreeMem_read128 vat)

abbrev catCtorCallerWardsSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨0⟩ (solcSourceWord I)

def catCtorWardsHashMem (I : ExecutionEnv) (vat : AccountAddress) : ByteArray :=
  twoWordHashMem (solcSourceWord I) ⟨0⟩ (catCtorArgFreeMem vat)


theorem catCtorWardsHashMem_size (I : ExecutionEnv) (vat : AccountAddress) :
    (catCtorWardsHashMem I vat).size = 160 := by
  unfold catCtorWardsHashMem twoWordHashMem
  exact wordAt32Mem_size_160 ⟨0⟩
    (wordAt0Mem_size_160 (solcSourceWord I) (catCtorArgFreeMem_size vat))


theorem catCtorWardsHashSlot (I : ExecutionEnv) (vat : AccountAddress) :
    UInt256.ofNat (fromByteArrayBigEndian
        (KEC ((catCtorWardsHashMem I vat).readWithPadding 0 64))) =
      catCtorCallerWardsSlot I := by
  unfold catCtorWardsHashMem catCtorCallerWardsSlot solcMappingSlot
  rw [twoWordHashMem_read0_64_160]
  · exact mappingSlot_single (solcSourceWord I) ⟨0⟩
  · exact catCtorArgFreeMem_size vat

def catCtorReturnMem (I : ExecutionEnv) (vat : AccountAddress) : ByteArray :=
  (catCtorCode vat).write 126 (catCtorWardsHashMem I vat) 0 3873

theorem catCtorReturnMem_read (I : ExecutionEnv) (vat : AccountAddress) :
    (catCtorReturnMem I vat).readWithPadding 0 3873 = catBytecode := by
  unfold catCtorReturnMem
  rw [write0_read_back_from_gen (catCtorCode vat) (catCtorWardsHashMem I vat) 126 3873
    (by decide) (by
      unfold catCtorCode
      rw [ByteArray.size_append, catCreationBytecode_size, catCtorArgsTail_size]
      omega) (by decide)]
  have hleft :
      (catCtorCode vat).extract 126 (126 + 3873) =
        catCreationBytecode.extract 126 (126 + 3873) := by
    unfold catCtorCode
    exact extract_append_left catCreationBytecode (catCtorArgsTail vat) 126 (126 + 3873)
      (by rw [catCreationBytecode_size])
  rw [hleft, catCreationBytecode_runtime_window]


abbrev catCtorVatStored (σ : AccountMap) (I : ExecutionEnv) (vat : AccountAddress) : UInt256 :=
  setAddressOffset0Word (solcSlotWord σ I ⟨3⟩) (EVM.word vat.val)

end Benchmarks.Dss.Cat
