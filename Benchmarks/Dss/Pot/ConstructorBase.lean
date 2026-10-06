import Reasoning.WordArithmetic
import Reasoning.MemoryShapes
import Reasoning.Memory
import Benchmarks.Dss.Pot.Common
import Reasoning.ExternalCall
import Reasoning.Initcode
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Pot constructor shared helpers

Shared bytecode, memory, and storage-slot facts used by the Pot constructor trace and source
semantics proofs.  Ported from the fully-proved sibling `Benchmarks/Dss/Jug`; Pot's constructor adds
four scalar stores (`dsr`, `chi`, `rho`, `live`) on top of Jug's `wards`/`vat` pattern and its `vat`
address lives in slot 5 (not slot 2).
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Pot

set_option maxRecDepth 2000000

/-- ABI-encoded constructor argument appended to `potCreationBytecode`. -/
def potCtorArgsTail (vat : AccountAddress) : ByteArray :=
  (EVM.Word.toBytesBE (EVM.word vat.val)).toByteArray

def potCtorCode (vat : AccountAddress) : ByteArray :=
  potCreationBytecode ++ potCtorArgsTail vat

theorem potCtorDeployment_shape {args : List Value} {deployedInitcode : ByteArray}
    (hdeploy : config.selfDeployment potCreationBytecode args = some deployedInitcode) :
    ∃ vat : AccountAddress,
      args = [.address vat] ∧ deployedInitcode = potCtorCode vat := by
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
          simpa [potCtorCode, potCtorArgsTail] using hdeploy.symm

macro "pot_ctor_decode" : tactic =>
  `(tactic|
    (first
      | rw [Reasoning.Theory.decode_append_left_window
          potCreationBytecode _ _ (by native_decide) (by native_decide)]
      | (unfold potCtorCode
         rw [Reasoning.Theory.decode_append_left_window
          potCreationBytecode _ _ (by native_decide) (by native_decide)]);
     native_decide))

macro "pot_ctor_jd" : tactic =>
  `(tactic|
    (first
      | exact Reasoning.Theory.D_J_contains_append_left potCreationBytecode _ _ (by jump_dest)
      | (unfold potCtorCode
         exact Reasoning.Theory.D_J_contains_append_left potCreationBytecode _ _ (by jump_dest))))

open Lean in
macro "pot_ctor_run " base:term " with " "[" steps:evmStep,* "]" : term => do
  let mut acc := base
  for s in steps.getElems do
    match s with
    | `(evmStep| raw $op:ident $args*) =>
        acc ← `($(acc).$op $args*)
    | `(evmStep| $op:ident $args*) =>
        match op.getId with
        | `jump    => acc ← `($(acc).jump (by pot_ctor_decode) $(args[0]!) (by evm_ov))
        | `jumpiT  => acc ← `($(acc).jumpiT (by pot_ctor_decode) $(args[0]!) $(args[1]!)
                            (by evm_ov))
        | `jumpiNT => acc ← `($(acc).jumpiNT (by pot_ctor_decode) $(args[0]!) (by evm_ov))
        | _        => acc ← `($(acc).$op $args* (by pot_ctor_decode) (by evm_ov))
    | _ => Macro.throwUnsupported
  return acc

theorem potCreationBytecode_size : potCreationBytecode.size = 2746 := by
  native_decide

theorem potBytecode_size : potBytecode.size = 2595 := by
  native_decide

theorem potCtorArgsTail_size (vat : AccountAddress) : (potCtorArgsTail vat).size = 32 := by
  simpa [potCtorArgsTail] using word_toBytesBE_toByteArray_size (EVM.word vat.val)

theorem potCtorCode_size (vat : AccountAddress) : (potCtorCode vat).size = 2778 := by
  unfold potCtorCode
  rw [ByteArray.size_append, potCreationBytecode_size, potCtorArgsTail_size]

theorem potCtorArgLen_eq (vat : AccountAddress) :
    (UInt256.ofNat (potCtorCode vat).size).sub ⟨2746⟩ = (⟨32⟩ : UInt256) := by
  rw [potCtorCode_size]
  native_decide

theorem potCreationBytecode_runtime_window :
    potCreationBytecode.extract 151 (151 + 2595) = potBytecode := by
  native_decide


def potCtorArgMem (vat : AccountAddress) : ByteArray :=
  (potCtorCode vat).write 2746 solcFreePtrMem 128 32

def potCtorArgFreeMem (vat : AccountAddress) : ByteArray :=
  (UInt256.toByteArray ⟨160⟩).write 0 (potCtorArgMem vat) 64 32

theorem potCtorArgMem_eq (vat : AccountAddress) :
    potCtorArgMem vat =
      solcFreePtrMem ++ ByteArray.zeroes 32 ++ potCtorArgsTail vat := by
  rw [potCtorArgMem, potCtorCode, byteArray_write_from_ge_eq]
  · rw [extract_append_right' potCreationBytecode (potCtorArgsTail vat) 2746 (2746 + 32)]
    · rw [solcFreePtrMem_size]
    · exact potCreationBytecode_size.symm
    · rw [potCtorArgsTail_size]
      native_decide
  · decide
  · rw [ByteArray.size_append, potCreationBytecode_size, potCtorArgsTail_size]
  · rw [solcFreePtrMem_size]
    decide
  · rw [solcFreePtrMem_size]
    exact lt_usize 32 (by norm_num)

theorem potCtorArgMem_size (vat : AccountAddress) : (potCtorArgMem vat).size = 160 := by
  rw [potCtorArgMem_eq, ByteArray.size_append, ByteArray.size_append, solcFreePtrMem_size,
    zeroes_ofNat_size 32 (by norm_num), potCtorArgsTail_size]

theorem potCtorArgFreeMem_size (vat : AccountAddress) :
    (potCtorArgFreeMem vat).size = 160 := by
  unfold potCtorArgFreeMem
  exact toByteArray_write32_size_of_le (base := potCtorArgMem vat) (word := (⟨160⟩ : UInt256))
    (off := 64) (baseSize := 160) (finalSize := 160) (potCtorArgMem_size vat)
    (by rw [potCtorArgMem_size]; omega) (by omega)

theorem potCtorArgMem_read128 (vat : AccountAddress) :
    (potCtorArgMem vat).readWithPadding 128 32 =
      UInt256.toByteArray (EVM.word vat.val) := by
  rw [potCtorArgMem_eq]
  have hprefix :
      (solcFreePtrMem ++ ByteArray.zeroes 32).size = 128 := by
    rw [ByteArray.size_append, solcFreePtrMem_size, zeroes_ofNat_size 32 (by norm_num)]
  rw [readWithPadding_eq_extract'
    (solcFreePtrMem ++ ByteArray.zeroes 32 ++ potCtorArgsTail vat)
    128 32 (by norm_num) (by norm_num) (by
      rw [ByteArray.size_append, hprefix, potCtorArgsTail_size])]
  rw [extract_append_right_window
    (solcFreePtrMem ++ ByteArray.zeroes 32) (potCtorArgsTail vat) 128
    (128 + 32) (by rw [hprefix]), hprefix]
  rw [show 128 - 128 = 0 by omega, show 128 + 32 - 128 = 32 by omega]
  simp [potCtorArgsTail, word_toBytesBE_toByteArray_eq_toByteArray, toByteArray_extract_all]

theorem potCtorArgFreeMem_read128 (vat : AccountAddress) :
    (potCtorArgFreeMem vat).readWithPadding 128 32 =
      UInt256.toByteArray (EVM.word vat.val) := by
  unfold potCtorArgFreeMem
  rw [write32_read_above _ _ 64 128 (by rw [toByteArray_size])
    (by rw [potCtorArgMem_size]; omega) (by omega) (by rw [potCtorArgMem_size])]
  exact potCtorArgMem_read128 vat

theorem potCtorArgFreeMem_mload128 (vat : AccountAddress) :
    (if (⟨128⟩ : UInt256).toNat ≥ (potCtorArgFreeMem vat).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((potCtorArgFreeMem vat).readWithPadding 128 32))) =
      EVM.word vat.val := by
  exact mloadWordValue_of_readWithPadding
    (mem := potCtorArgFreeMem vat) (off := ⟨128⟩)
    (v := EVM.word vat.val)
    (by rw [potCtorArgFreeMem_size]; decide)
    (potCtorArgFreeMem_read128 vat)

abbrev potCtorCallerWardsSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨0⟩ (solcSourceWord I)

def potCtorWardsHashMem (I : ExecutionEnv) (vat : AccountAddress) : ByteArray :=
  twoWordHashMem (solcSourceWord I) ⟨0⟩ (potCtorArgFreeMem vat)


theorem potCtorWardsHashMem_size (I : ExecutionEnv) (vat : AccountAddress) :
    (potCtorWardsHashMem I vat).size = 160 := by
  unfold potCtorWardsHashMem twoWordHashMem
  exact wordAt32Mem_size_160 ⟨0⟩
    (wordAt0Mem_size_160 (solcSourceWord I) (potCtorArgFreeMem_size vat))


theorem potCtorWardsHashSlot (I : ExecutionEnv) (vat : AccountAddress) :
    UInt256.ofNat (fromByteArrayBigEndian
        (KEC ((potCtorWardsHashMem I vat).readWithPadding 0 64))) =
      potCtorCallerWardsSlot I := by
  unfold potCtorWardsHashMem potCtorCallerWardsSlot solcMappingSlot
  rw [twoWordHashMem_read0_64_160]
  · exact mappingSlot_single (solcSourceWord I) ⟨0⟩
  · exact potCtorArgFreeMem_size vat

def potCtorReturnMem (I : ExecutionEnv) (vat : AccountAddress) : ByteArray :=
  (potCtorCode vat).write 151 (potCtorWardsHashMem I vat) 0 2595

theorem potCtorReturnMem_read (I : ExecutionEnv) (vat : AccountAddress) :
    (potCtorReturnMem I vat).readWithPadding 0 2595 = potBytecode := by
  unfold potCtorReturnMem
  rw [write0_read_back_from_gen (potCtorCode vat) (potCtorWardsHashMem I vat) 151 2595
    (by decide) (by
      unfold potCtorCode
      rw [ByteArray.size_append, potCreationBytecode_size, potCtorArgsTail_size]
      omega) (by decide)]
  have hleft :
      (potCtorCode vat).extract 151 (151 + 2595) =
        potCreationBytecode.extract 151 (151 + 2595) := by
    unfold potCtorCode
    exact extract_append_left potCreationBytecode (potCtorArgsTail vat) 151 (151 + 2595)
      (by rw [potCreationBytecode_size])
  rw [hleft, potCreationBytecode_runtime_window]


abbrev potCtorVatStored (σ : AccountMap) (I : ExecutionEnv) (vat : AccountAddress) : UInt256 :=
  setAddressOffset0Word (solcSlotWord σ I ⟨5⟩) (EVM.word vat.val)

/-- `ONE = 10^27` word stored by the constructor into `dsr` and `chi`. -/
abbrev potCtorOne : UInt256 := ⟨1000000000000000000000000000⟩

theorem potCtorOne_eq_one : (one : Int) = Int.ofNat potCtorOne.toNat := by
  native_decide

end Benchmarks.Dss.Pot
