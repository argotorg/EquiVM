import Reasoning.WordArithmetic
import Reasoning.MemoryShapes
import Reasoning.Memory
import Benchmarks.Dss.GemJoin.Common
import Reasoning.ExternalCall
import Reasoning.Initcode
import Solm.Equiv

/-!
# MakerDAO/Sky DSS GemJoin constructor shared helpers
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.GemJoin

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

/-! ## Deployment and runtime window -/

def gemJoinCtorArgsTail (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress) :
    ByteArray :=
  (EVM.Word.toBytesBE (EVM.word vat.val)).toByteArray ++
  (EVM.Word.toBytesBE ilk).toByteArray ++
  (EVM.Word.toBytesBE (EVM.word gem.val)).toByteArray

def gemJoinCtorCode (vat : AccountAddress) (ilk : UInt256)
    (gem : AccountAddress) : ByteArray :=
  gemJoinCreationBytecode ++ gemJoinCtorArgsTail vat ilk gem

macro "gem_ctor_decode" : tactic =>
  `(tactic|
    (first
      | rw [Reasoning.Theory.decode_append_left_window
          gemJoinCreationBytecode _ _ (by native_decide) (by native_decide)]
      | (unfold gemJoinCtorCode
         rw [Reasoning.Theory.decode_append_left_window
          gemJoinCreationBytecode _ _ (by native_decide) (by native_decide)]);
     native_decide))

macro "gem_ctor_jd" : tactic =>
  `(tactic|
    (first
      | exact Reasoning.Theory.D_J_contains_append_left gemJoinCreationBytecode _ _ (by jump_dest)
      | (unfold gemJoinCtorCode
         exact Reasoning.Theory.D_J_contains_append_left gemJoinCreationBytecode _ _ (by jump_dest))))

open Lean in
macro "gem_ctor_run " base:term " with " "[" steps:evmStep,* "]" : term => do
  let mut acc := base
  for s in steps.getElems do
    match s with
    | `(evmStep| raw $op:ident $args*) =>
        acc ← `($(acc).$op $args*)
    | `(evmStep| $op:ident $args*) =>
        match op.getId with
        | `jump    => acc ← `($(acc).jump (by gem_ctor_decode) $(args[0]!) (by evm_ov))
        | `jumpiT  => acc ← `($(acc).jumpiT (by gem_ctor_decode) $(args[0]!) $(args[1]!)
                            (by evm_ov))
        | `jumpiNT => acc ← `($(acc).jumpiNT (by gem_ctor_decode) $(args[0]!) (by evm_ov))
        | _        => acc ← `($(acc).$op $args* (by gem_ctor_decode) (by evm_ov))
    | _ => Macro.throwUnsupported
  return acc

theorem gemJoinCtorDeployment_shape {args : List Value} {deployedInitcode : ByteArray}
    (hdeploy : config.selfDeployment gemJoinCreationBytecode args = some deployedInitcode) :
    ∃ (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress),
      args = [.address vat, .fixedBytes bytes32Width (EVM.Word.toBytesBE ilk), .address gem] ∧
        deployedInitcode = gemJoinCtorCode vat ilk gem := by
  simp [config, contract, constructorDecl, Solm.genSolidityConstructorDeployment] at hdeploy
  cases args with
  | nil =>
      simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, addr, bytes32] at hdeploy
  | cons a rest =>
      cases rest with
      | nil =>
          cases a <;> simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, addr, bytes32,
            ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
            ABI.encodeABIValue?, ABI.encodeABIWord?] at hdeploy
      | cons b rest2 =>
          cases rest2 with
          | nil =>
              cases a <;> cases b <;>
                simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, addr, bytes32,
                  ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
                  ABI.encodeABIValue?, ABI.encodeABIWord?] at hdeploy
          | cons c rest3 =>
              cases rest3 with
              | cons _ _ =>
                  cases a <;> cases b <;> cases c <;>
                    simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, addr, bytes32,
                      ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
                      ABI.encodeABIValue?, ABI.encodeABIWord?] at hdeploy
              | nil =>
                  cases a <;> cases b <;> cases c <;>
                    simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, addr, bytes32,
                      ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
                      ABI.encodeABIValue?, ABI.encodeABIWord?] at hdeploy
                  rename_i vat n bs gem
                  by_cases hcond : n = bytes32Width ∧ bs.length = ↑bytes32Width + 1
                  · rcases hcond with ⟨hwidth, hlen⟩
                    subst hwidth
                    simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, addr, bytes32,
                      ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
                      ABI.encodeABIValue?, ABI.encodeABIWord?, zeroBytes, bytes32Width] at hdeploy
                    have hlen32 : bs.length = 32 := by
                      simpa [bytes32Width] using hlen
                    have hdeployEq : deployedInitcode =
                        gemJoinCreationBytecode ++
                          ((EVM.Word.toBytesBE (EVM.word vat.val)).toByteArray ++
                            (bs.toByteArray ++
                              (EVM.Word.toBytesBE (EVM.word gem.val)).toByteArray)) := by
                      simpa [hlen32, EVM.word] using hdeploy.symm
                    let ilk : UInt256 := ABI.bytesToWord bs
                    have hbs : EVM.Word.toBytesBE ilk = bs := by
                      simpa [ilk] using toBytesBE_bytesToWord_of_length (bs := bs) hlen32
                    refine ⟨vat, ilk, gem, ?_, ?_⟩
                    · simp [hbs]
                    · rw [hdeployEq]
                      simp [gemJoinCtorCode, gemJoinCtorArgsTail, hbs, ByteArray.append_assoc]
                  · simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, addr, bytes32,
                      ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
                      ABI.encodeABIValue?, ABI.encodeABIWord?, hcond] at hdeploy


theorem gemJoinCreationBytecode_size : gemJoinCreationBytecode.size = 2326 := by
  native_decide

theorem gemJoinBytecode_size : gemJoinBytecode.size = 2022 := by
  native_decide

theorem gemJoinCreationBytecode_runtime_window :
    gemJoinCreationBytecode.extract 304 (304 + 2022) = gemJoinBytecode := by
  native_decide

theorem gemJoinCtorArgsTail_size (vat : AccountAddress) (ilk : UInt256)
    (gem : AccountAddress) :
    (gemJoinCtorArgsTail vat ilk gem).size = 96 := by
  simp [gemJoinCtorArgsTail, ByteArray.size_append, word_toBytesBE_length_32]

theorem gemJoinCtorCode_size (vat : AccountAddress) (ilk : UInt256)
    (gem : AccountAddress) :
    (gemJoinCtorCode vat ilk gem).size = 2422 := by
  rw [gemJoinCtorCode, ByteArray.size_append, gemJoinCreationBytecode_size,
    gemJoinCtorArgsTail_size]

def gemJoinCtorRuntimeReturnMem (vat : AccountAddress) (ilk : UInt256)
    (gem : AccountAddress) (mem : ByteArray) : ByteArray :=
  (gemJoinCtorCode vat ilk gem).write 304 mem 0 2022

theorem gemJoinCtorRuntimeReturnMem_read (vat : AccountAddress) (ilk : UInt256)
    (gem : AccountAddress) (mem : ByteArray) :
    (gemJoinCtorRuntimeReturnMem vat ilk gem mem).readWithPadding 0 2022 =
      gemJoinBytecode := by
  unfold gemJoinCtorRuntimeReturnMem
  rw [write0_read_back_from_gen (gemJoinCtorCode vat ilk gem) mem 304 2022
    (by decide)
    (by rw [gemJoinCtorCode_size]; omega)
    (by norm_num)]
  unfold gemJoinCtorCode
  rw [extract_append_left gemJoinCreationBytecode (gemJoinCtorArgsTail vat ilk gem)
    304 (304 + 2022) (by native_decide)]
  exact gemJoinCreationBytecode_runtime_window

theorem gemJoinCtorArgLen_eq (vat : AccountAddress) (ilk : UInt256)
    (gem : AccountAddress) :
    (UInt256.ofNat (gemJoinCtorCode vat ilk gem).size).sub ⟨2326⟩ =
      (⟨96⟩ : UInt256) := by
  rw [gemJoinCtorCode_size]
  native_decide


def gemJoinCtorArgMem (vat : AccountAddress) (ilk : UInt256)
    (gem : AccountAddress) : ByteArray :=
  (gemJoinCtorCode vat ilk gem).write 2326 solcFreePtrMem 128 96

def gemJoinCtorArgFreeMem (vat : AccountAddress) (ilk : UInt256)
    (gem : AccountAddress) : ByteArray :=
  (UInt256.toByteArray ⟨224⟩).write 0 (gemJoinCtorArgMem vat ilk gem) 64 32

theorem gemJoinCtorArgMem_eq (vat : AccountAddress) (ilk : UInt256)
    (gem : AccountAddress) :
    gemJoinCtorArgMem vat ilk gem =
      solcFreePtrMem ++ ByteArray.zeroes 32 ++
        gemJoinCtorArgsTail vat ilk gem := by
  rw [gemJoinCtorArgMem, gemJoinCtorCode, byteArray_write_from_ge_eq_no_gap_bound]
  · rw [extract_append_right' gemJoinCreationBytecode (gemJoinCtorArgsTail vat ilk gem) 2326
      (2326 + 96)]
    · rw [solcFreePtrMem_size]
    · exact gemJoinCreationBytecode_size.symm
    · rw [gemJoinCtorArgsTail_size]
      native_decide
  · decide
  · rw [ByteArray.size_append, gemJoinCreationBytecode_size, gemJoinCtorArgsTail_size]
  · rw [solcFreePtrMem_size]
    decide

theorem gemJoinCtorArgMem_size (vat : AccountAddress) (ilk : UInt256)
    (gem : AccountAddress) : (gemJoinCtorArgMem vat ilk gem).size = 224 := by
  rw [gemJoinCtorArgMem_eq, ByteArray.size_append, ByteArray.size_append, solcFreePtrMem_size,
    zeroes_ofNat_size 32 (by norm_num), gemJoinCtorArgsTail_size]

theorem gemJoinCtorArgFreeMem_size (vat : AccountAddress) (ilk : UInt256)
    (gem : AccountAddress) :
    (gemJoinCtorArgFreeMem vat ilk gem).size = 224 := by
  unfold gemJoinCtorArgFreeMem
  exact toByteArray_write32_size_of_le
    (base := gemJoinCtorArgMem vat ilk gem) (word := (⟨224⟩ : UInt256))
    (off := 64) (baseSize := 224) (finalSize := 224)
    (gemJoinCtorArgMem_size vat ilk gem)
    (by rw [gemJoinCtorArgMem_size]; omega) (by omega)

theorem gemJoinCtorArgFreeMem_read64 (vat : AccountAddress) (ilk : UInt256)
    (gem : AccountAddress) :
    (gemJoinCtorArgFreeMem vat ilk gem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨224⟩ := by
  unfold gemJoinCtorArgFreeMem
  exact toByteArray_write_read_back_of_gap ⟨224⟩ (gemJoinCtorArgMem vat ilk gem) 64
    (by rw [gemJoinCtorArgMem_size]; native_decide)

theorem gemJoinCtorArgFreeMem_mload64 (vat : AccountAddress) (ilk : UInt256)
    (gem : AccountAddress) :
    (if (⟨64⟩ : UInt256).toNat ≥ (gemJoinCtorArgFreeMem vat ilk gem).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((gemJoinCtorArgFreeMem vat ilk gem).readWithPadding 64 32))) =
      ⟨224⟩ := by
  exact mloadWordValue_of_readWithPadding
    (mem := gemJoinCtorArgFreeMem vat ilk gem) (off := ⟨64⟩)
    (v := ⟨224⟩)
    (by rw [gemJoinCtorArgFreeMem_size]; decide)
    (gemJoinCtorArgFreeMem_read64 vat ilk gem)

theorem gemJoinCtorArgMem_read128 (vat : AccountAddress) (ilk : UInt256)
    (gem : AccountAddress) :
    (gemJoinCtorArgMem vat ilk gem).readWithPadding 128 32 =
      UInt256.toByteArray (EVM.word vat.val) := by
  rw [gemJoinCtorArgMem_eq]
  have hprefix : (solcFreePtrMem ++ ByteArray.zeroes 32).size = 128 := by
    rw [ByteArray.size_append, solcFreePtrMem_size, zeroes_ofNat_size 32 (by norm_num)]
  rw [readWithPadding_eq_extract'
    (solcFreePtrMem ++ ByteArray.zeroes 32 ++ gemJoinCtorArgsTail vat ilk gem)
    128 32 (by norm_num) (by norm_num) (by
      rw [ByteArray.size_append, hprefix, gemJoinCtorArgsTail_size]
      omega)]
  rw [extract_append_right_window
    (solcFreePtrMem ++ ByteArray.zeroes 32) (gemJoinCtorArgsTail vat ilk gem) 128
    (128 + 32) (by rw [hprefix]), hprefix]
  rw [show 128 - 128 = 0 by omega, show 128 + 32 - 128 = 32 by omega]
  rw [gemJoinCtorArgsTail]
  rw [extract_append_left
    ((EVM.word vat.val).toBytesBE.toByteArray ++ (EVM.Word.toBytesBE ilk).toByteArray)
    ((EVM.word gem.val).toBytesBE.toByteArray) 0 32 (by
      rw [ByteArray.size_append]
      have hvat := word_toBytesBE_toByteArray_size (EVM.word vat.val)
      have hilk := word_toBytesBE_toByteArray_size ilk
      omega)]
  rw [extract_append_left
    ((EVM.word vat.val).toBytesBE.toByteArray) ((EVM.Word.toBytesBE ilk).toByteArray) 0 32
    (by
      have hvat : ((EVM.word vat.val).toBytesBE.toByteArray).size = 32 := by
        simpa using word_toBytesBE_toByteArray_size (EVM.word vat.val)
      omega)]
  rw [word_toBytesBE_toByteArray_eq_toByteArray, toByteArray_extract_all]

theorem gemJoinCtorArgMem_read160 (vat : AccountAddress) (ilk : UInt256)
    (gem : AccountAddress) :
    (gemJoinCtorArgMem vat ilk gem).readWithPadding 160 32 =
      UInt256.toByteArray ilk := by
  rw [gemJoinCtorArgMem_eq]
  have hprefix : (solcFreePtrMem ++ ByteArray.zeroes 32).size = 128 := by
    rw [ByteArray.size_append, solcFreePtrMem_size, zeroes_ofNat_size 32 (by norm_num)]
  rw [readWithPadding_eq_extract'
    (solcFreePtrMem ++ ByteArray.zeroes 32 ++ gemJoinCtorArgsTail vat ilk gem)
    160 32 (by norm_num) (by norm_num) (by
      rw [ByteArray.size_append, hprefix, gemJoinCtorArgsTail_size]
      omega)]
  rw [extract_append_right_window
    (solcFreePtrMem ++ ByteArray.zeroes 32) (gemJoinCtorArgsTail vat ilk gem) 160
    (160 + 32) (by rw [hprefix]; omega), hprefix]
  rw [show 160 - 128 = 32 by omega, show 160 + 32 - 128 = 64 by omega]
  rw [gemJoinCtorArgsTail]
  rw [extract_append_left
    ((EVM.word vat.val).toBytesBE.toByteArray ++ (EVM.Word.toBytesBE ilk).toByteArray)
    ((EVM.word gem.val).toBytesBE.toByteArray) 32 64 (by
      rw [ByteArray.size_append]
      have hvat := word_toBytesBE_toByteArray_size (EVM.word vat.val)
      have hilk := word_toBytesBE_toByteArray_size ilk
      omega)]
  rw [extract_append_right_window
    ((EVM.word vat.val).toBytesBE.toByteArray) ((EVM.Word.toBytesBE ilk).toByteArray) 32 64
    (by
      have hvat : ((EVM.word vat.val).toBytesBE.toByteArray).size = 32 := by
        simpa using word_toBytesBE_toByteArray_size (EVM.word vat.val)
      omega)]
  have hvatSize : ((EVM.word vat.val).toBytesBE.toByteArray).size = 32 := by
    simpa using word_toBytesBE_toByteArray_size (EVM.word vat.val)
  rw [hvatSize, show 32 - 32 = 0 by omega, show 64 - 32 = 32 by omega]
  rw [word_toBytesBE_toByteArray_eq_toByteArray, toByteArray_extract_all]

theorem gemJoinCtorArgMem_read192 (vat : AccountAddress) (ilk : UInt256)
    (gem : AccountAddress) :
    (gemJoinCtorArgMem vat ilk gem).readWithPadding 192 32 =
      UInt256.toByteArray (EVM.word gem.val) := by
  rw [gemJoinCtorArgMem_eq]
  have hprefix : (solcFreePtrMem ++ ByteArray.zeroes 32).size = 128 := by
    rw [ByteArray.size_append, solcFreePtrMem_size, zeroes_ofNat_size 32 (by norm_num)]
  rw [readWithPadding_eq_extract'
    (solcFreePtrMem ++ ByteArray.zeroes 32 ++ gemJoinCtorArgsTail vat ilk gem)
    192 32 (by norm_num) (by norm_num) (by
      rw [ByteArray.size_append, hprefix, gemJoinCtorArgsTail_size])]
  rw [extract_append_right_window
    (solcFreePtrMem ++ ByteArray.zeroes 32) (gemJoinCtorArgsTail vat ilk gem) 192
    (192 + 32) (by rw [hprefix]; omega), hprefix]
  rw [show 192 - 128 = 64 by omega, show 192 + 32 - 128 = 96 by omega]
  rw [gemJoinCtorArgsTail]
  rw [extract_append_right_window
    ((EVM.word vat.val).toBytesBE.toByteArray ++ (EVM.Word.toBytesBE ilk).toByteArray)
    ((EVM.word gem.val).toBytesBE.toByteArray) 64 96
    (by
      rw [ByteArray.size_append]
      have hvat := word_toBytesBE_toByteArray_size (EVM.word vat.val)
      have hilk := word_toBytesBE_toByteArray_size ilk
      omega)]
  have htailPrefix :
      ((EVM.word vat.val).toBytesBE.toByteArray ++ (EVM.Word.toBytesBE ilk).toByteArray).size =
        64 := by
    rw [ByteArray.size_append]
    have hvat := word_toBytesBE_toByteArray_size (EVM.word vat.val)
    have hilk := word_toBytesBE_toByteArray_size ilk
    omega
  rw [htailPrefix, show 64 - 64 = 0 by omega, show 96 - 64 = 32 by omega]
  rw [word_toBytesBE_toByteArray_eq_toByteArray, toByteArray_extract_all]

theorem gemJoinCtorArgFreeMem_read128 (vat : AccountAddress) (ilk : UInt256)
    (gem : AccountAddress) :
    (gemJoinCtorArgFreeMem vat ilk gem).readWithPadding 128 32 =
      UInt256.toByteArray (EVM.word vat.val) := by
  unfold gemJoinCtorArgFreeMem
  rw [write32_read_above _ _ 64 128 (by rw [toByteArray_size])
    (by rw [gemJoinCtorArgMem_size]; omega) (by omega) (by rw [gemJoinCtorArgMem_size]; omega)]
  exact gemJoinCtorArgMem_read128 vat ilk gem

theorem gemJoinCtorArgFreeMem_read160 (vat : AccountAddress) (ilk : UInt256)
    (gem : AccountAddress) :
    (gemJoinCtorArgFreeMem vat ilk gem).readWithPadding 160 32 =
      UInt256.toByteArray ilk := by
  unfold gemJoinCtorArgFreeMem
  rw [write32_read_above _ _ 64 160 (by rw [toByteArray_size])
    (by rw [gemJoinCtorArgMem_size]; omega) (by omega) (by rw [gemJoinCtorArgMem_size]; omega)]
  exact gemJoinCtorArgMem_read160 vat ilk gem

theorem gemJoinCtorArgFreeMem_read192 (vat : AccountAddress) (ilk : UInt256)
    (gem : AccountAddress) :
    (gemJoinCtorArgFreeMem vat ilk gem).readWithPadding 192 32 =
      UInt256.toByteArray (EVM.word gem.val) := by
  unfold gemJoinCtorArgFreeMem
  rw [write32_read_above _ _ 64 192 (by rw [toByteArray_size])
    (by rw [gemJoinCtorArgMem_size]; omega) (by omega) (by rw [gemJoinCtorArgMem_size])]
  exact gemJoinCtorArgMem_read192 vat ilk gem

theorem gemJoinCtorArgFreeMem_mload128 (vat : AccountAddress) (ilk : UInt256)
    (gem : AccountAddress) :
    (if (⟨128⟩ : UInt256).toNat ≥ (gemJoinCtorArgFreeMem vat ilk gem).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((gemJoinCtorArgFreeMem vat ilk gem).readWithPadding 128 32))) =
      EVM.word vat.val := by
  exact mloadWordValue_of_readWithPadding
    (mem := gemJoinCtorArgFreeMem vat ilk gem) (off := ⟨128⟩)
    (v := EVM.word vat.val)
    (by rw [gemJoinCtorArgFreeMem_size]; decide)
    (gemJoinCtorArgFreeMem_read128 vat ilk gem)

theorem gemJoinCtorArgFreeMem_mload160 (vat : AccountAddress) (ilk : UInt256)
    (gem : AccountAddress) :
    (if (⟨160⟩ : UInt256).toNat ≥ (gemJoinCtorArgFreeMem vat ilk gem).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((gemJoinCtorArgFreeMem vat ilk gem).readWithPadding 160 32))) =
      ilk := by
  exact mloadWordValue_of_readWithPadding
    (mem := gemJoinCtorArgFreeMem vat ilk gem) (off := ⟨160⟩)
    (v := ilk)
    (by rw [gemJoinCtorArgFreeMem_size]; decide)
    (gemJoinCtorArgFreeMem_read160 vat ilk gem)

theorem gemJoinCtorArgFreeMem_mload192 (vat : AccountAddress) (ilk : UInt256)
    (gem : AccountAddress) :
    (if (⟨192⟩ : UInt256).toNat ≥ (gemJoinCtorArgFreeMem vat ilk gem).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((gemJoinCtorArgFreeMem vat ilk gem).readWithPadding 192 32))) =
      EVM.word gem.val := by
  exact mloadWordValue_of_readWithPadding
    (mem := gemJoinCtorArgFreeMem vat ilk gem) (off := ⟨192⟩)
    (v := EVM.word gem.val)
    (by rw [gemJoinCtorArgFreeMem_size]; decide)
    (gemJoinCtorArgFreeMem_read192 vat ilk gem)

abbrev gemJoinCtorCallerWardsSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨0⟩ (solcSourceWord I)

def gemJoinCtorWardsHashMem (I : ExecutionEnv) (vat : AccountAddress)
    (ilk : UInt256) (gem : AccountAddress) : ByteArray :=
  twoWordHashMem (solcSourceWord I) ⟨0⟩ (gemJoinCtorArgFreeMem vat ilk gem)


theorem gemJoinCtorWardsHashMem_size (I : ExecutionEnv) (vat : AccountAddress)
    (ilk : UInt256) (gem : AccountAddress) :
    (gemJoinCtorWardsHashMem I vat ilk gem).size = 224 := by
  unfold gemJoinCtorWardsHashMem twoWordHashMem
  exact wordAt32Mem_size_224 ⟨0⟩
    (wordAt0Mem_size_224 (solcSourceWord I) (gemJoinCtorArgFreeMem_size vat ilk gem))


theorem gemJoinCtorWardsHashSlot (I : ExecutionEnv) (vat : AccountAddress)
    (ilk : UInt256) (gem : AccountAddress) :
    UInt256.ofNat
        (fromByteArrayBigEndian
          (KEC ((gemJoinCtorWardsHashMem I vat ilk gem).readWithPadding 0 64))) =
      gemJoinCtorCallerWardsSlot I := by
  unfold gemJoinCtorWardsHashMem gemJoinCtorCallerWardsSlot solcMappingSlot
  rw [twoWordHashMem_read0_64_224 (solcSourceWord I) ⟨0⟩
    (gemJoinCtorArgFreeMem_size vat ilk gem)]
  exact mappingSlot_single (solcSourceWord I) ⟨0⟩

theorem gemJoinCtorWardsHashMem_read64 (I : ExecutionEnv) (vat : AccountAddress)
    (ilk : UInt256) (gem : AccountAddress) :
    (gemJoinCtorWardsHashMem I vat ilk gem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨224⟩ := by
  unfold gemJoinCtorWardsHashMem twoWordHashMem wordAt32Mem
  have hword0sz :
      (wordAt0Mem (solcSourceWord I) (gemJoinCtorArgFreeMem vat ilk gem)).size = 224 :=
    wordAt0Mem_size_224 (solcSourceWord I) (gemJoinCtorArgFreeMem_size vat ilk gem)
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [hword0sz]; omega)
      (by omega)
      (by rw [hword0sz]; omega)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by rw [gemJoinCtorArgFreeMem_size]; omega)
      (by omega)
      (by rw [gemJoinCtorArgFreeMem_size]; omega)]
  exact gemJoinCtorArgFreeMem_read64 vat ilk gem

theorem gemJoinCtorWardsHashMem_mload64 (I : ExecutionEnv) (vat : AccountAddress)
    (ilk : UInt256) (gem : AccountAddress) :
    (if (⟨64⟩ : UInt256).toNat ≥ (gemJoinCtorWardsHashMem I vat ilk gem).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((gemJoinCtorWardsHashMem I vat ilk gem).readWithPadding 64 32))) =
      ⟨224⟩ := by
  exact mloadWordValue_of_readWithPadding
    (mem := gemJoinCtorWardsHashMem I vat ilk gem) (off := ⟨64⟩)
    (v := ⟨224⟩)
    (by rw [gemJoinCtorWardsHashMem_size]; decide)
    (gemJoinCtorWardsHashMem_read64 I vat ilk gem)

abbrev gemJoinCtorDecimalsSelectorShifted : UInt256 :=
  UInt256.shiftLeft ⟨826074471⟩ ⟨224⟩

def gemJoinCtorDecimalsCalldataMem (I : ExecutionEnv) (vat : AccountAddress)
    (ilk : UInt256) (gem : AccountAddress) : ByteArray :=
  (UInt256.toByteArray gemJoinCtorDecimalsSelectorShifted).write 0
    (gemJoinCtorWardsHashMem I vat ilk gem) 224 32

theorem gemJoinCtorDecimalsCalldataMem_size (I : ExecutionEnv) (vat : AccountAddress)
    (ilk : UInt256) (gem : AccountAddress) :
    (gemJoinCtorDecimalsCalldataMem I vat ilk gem).size = 256 := by
  unfold gemJoinCtorDecimalsCalldataMem
  exact toByteArray_write32_size_of_le
    (base := gemJoinCtorWardsHashMem I vat ilk gem)
      (word := gemJoinCtorDecimalsSelectorShifted)
      (off := 224) (baseSize := 224) (finalSize := 256)
      (gemJoinCtorWardsHashMem_size I vat ilk gem)
      (by rw [gemJoinCtorWardsHashMem_size]) (by omega)

theorem gemJoinCtorDecimalsCalldataMem_read64 (I : ExecutionEnv) (vat : AccountAddress)
    (ilk : UInt256) (gem : AccountAddress) :
    (gemJoinCtorDecimalsCalldataMem I vat ilk gem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨224⟩ := by
  unfold gemJoinCtorDecimalsCalldataMem
  rw [toByteArray_write_read_below_of_gap gemJoinCtorDecimalsSelectorShifted
    (gemJoinCtorWardsHashMem I vat ilk gem) 224 64
    (by rw [gemJoinCtorWardsHashMem_size]; omega)
    (by omega)
    (by rw [gemJoinCtorWardsHashMem_size]; native_decide)]
  exact gemJoinCtorWardsHashMem_read64 I vat ilk gem

theorem gemJoinCtorDecimalsCalldataMem_read224_4 (I : ExecutionEnv)
    (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress) :
    (gemJoinCtorDecimalsCalldataMem I vat ilk gem).readWithPadding 224 4 =
      gemDecimalsSelector := by
  unfold gemJoinCtorDecimalsCalldataMem
  rw [toByteArray_write_read_window_of_gap gemJoinCtorDecimalsSelectorShifted
    (gemJoinCtorWardsHashMem I vat ilk gem) 224 0 4
    (by norm_num) (by norm_num) (by norm_num)
    (by rw [gemJoinCtorWardsHashMem_size]; native_decide)]
  native_decide

theorem gemJoinCtorDecimalsCalldataMem_encode (I : ExecutionEnv)
    (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress) :
    config.externalABI.encode? "decimals" [] =
      some ((gemJoinCtorDecimalsCalldataMem I vat ilk gem).readWithPadding 224 4) := by
  rw [gemJoinCtorDecimalsCalldataMem_read224_4]
  rfl

/-! ## Constructor source-state abbreviations -/

abbrev gemJoinCtorLocals (vat : AccountAddress) (ilk : UInt256)
    (gem : AccountAddress) : Store :=
  (((∅ : Store).insert "vat_" (.address vat)).insert "ilk_"
    (.fixedBytes bytes32Width (EVM.Word.toBytesBE ilk))).insert "gem_" (.address gem)

abbrev gemJoinCtorVatStored (σ : AccountMap) (I : ExecutionEnv)
    (vat : AccountAddress) : UInt256 :=
  setAddressOffset0Word (solcSlotWord σ I ⟨1⟩) (EVM.word vat.val)

abbrev gemJoinCtorGemStored (σ : AccountMap) (I : ExecutionEnv)
    (gem : AccountAddress) : UInt256 :=
  setAddressOffset0Word (solcSlotWord σ I ⟨3⟩) (EVM.word gem.val)


theorem gemJoinCtorGemTargetAddress_eq (σ : AccountMap) (I : ExecutionEnv)
    (gem : AccountAddress) :
    AccountAddress.ofUInt256 (UInt256.land solcAddrMask (gemJoinCtorGemStored σ I gem)) =
      gem := by
  unfold gemJoinCtorGemStored
  rw [ctorSetAddressOffset0Word_low_address]
  exact accountAddress_roundtrip gem

abbrev gemJoinCtorAfterWardsState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (wardsSlot (.address evm.executionEnv.source)) ⟨1⟩

abbrev gemJoinCtorAfterLiveState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩ ⟨1⟩

abbrev gemJoinCtorAfterVatState (evm : EVM.State) (vat : AccountAddress) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
      (EVM.word vat.val))

abbrev gemJoinCtorAfterIlkState (evm : EVM.State) (ilk : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩ ilk

abbrev gemJoinCtorAfterGemState (evm : EVM.State) (gem : AccountAddress) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨3⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
      (EVM.word gem.val))

abbrev gemJoinCtorAfterDecState (evm : EVM.State) (dec : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨4⟩ dec

theorem gemJoinCtorCallerWardsSlot_eq (I : ExecutionEnv) :
    wardsSlot (.address I.source) = gemJoinCtorCallerWardsSlot I := by
  unfold wardsSlot mapSlot gemJoinCtorCallerWardsSlot solcMappingSlot solcSourceWord
  rw [keyValueToWord_address]


end Benchmarks.Dss.GemJoin
