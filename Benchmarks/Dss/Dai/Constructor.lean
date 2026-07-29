import Benchmarks.Dss.Dai.Bytecode
import Benchmarks.Dss.Dai.Storage
import Benchmarks.Dss.Dai.Trusted
import Reasoning.Initcode
import Reasoning.MemCascade
import Reasoning.Memory
import Reasoning.SolmBody
import Reasoning.Stepping
import Solm.Equiv

/-!
# MakerDAO DSS Dai constructor correctness stub

The optimized creation bytecode, deployed runtime bytecode, and Solm constructor specification are
present.  The constructor-equivalence proof is intentionally left as the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Dai

set_option maxRecDepth 2000000

/-- Solidity deployment accepts exactly one `uint256 chainId_` constructor argument. -/
theorem daiDeployment_shape {args : List Value} {deployedInitcode : ByteArray} :
    config.selfDeployment daiCreationBytecode args = some deployedInitcode →
    ∃ chainId : Int,
      args = [.int chainId]
        ∧ 0 ≤ chainId
        ∧ chainId < Int.ofNat (EVM.twoPow 256)
        ∧ deployedInitcode =
          daiCreationBytecode ++ (EVM.Word.toBytesBE (EVM.word chainId.toNat)).toByteArray := by
  intro h
  cases args with
  | nil =>
      simp [config, genSolidityConstructorDeployment, contract, constructorDecl,
        encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, uint256, uint256Int] at h
  | cons arg rest =>
      cases rest with
      | cons arg2 rest =>
          cases arg <;>
            simp [config, genSolidityConstructorDeployment, contract, constructorDecl,
              encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, uint256, uint256Int,
              staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
      | nil =>
          cases arg with
          | int chainId =>
              by_cases hbounds : 0 ≤ chainId ∧ chainId < Int.ofNat (EVM.twoPow 256)
              · simp [config, genSolidityConstructorDeployment, contract, constructorDecl,
                  encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, uint256, uint256Int,
                  staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
                change (((if 0 ≤ chainId ∧ chainId < Int.ofNat (EVM.twoPow 256) then
                    some (EVM.word chainId.toNat) else none).bind
                    fun word => some word.toBytesBE).bind
                    fun args => some (daiCreationBytecode ++ args.toByteArray)) =
                  some deployedInitcode at h
                split at h
                · simp at h
                  exact ⟨chainId, rfl, hbounds.1, hbounds.2, h.symm⟩
                · rename_i hnot
                  exact False.elim (hnot hbounds)
              · simp [config, genSolidityConstructorDeployment, contract, constructorDecl,
                  encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, uint256, uint256Int,
                  staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
                change (((if 0 ≤ chainId ∧ chainId < Int.ofNat (EVM.twoPow 256) then
                    some (EVM.word chainId.toNat) else none).bind
                    fun word => some word.toBytesBE).bind
                    fun args => some (daiCreationBytecode ++ args.toByteArray)) =
                  some deployedInitcode at h
                split at h
                · rename_i hpos
                  exact False.elim (hbounds hpos)
                · simp at h
          | bool b =>
              simp [config, genSolidityConstructorDeployment, contract, constructorDecl,
                encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, uint256,
                staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | address a =>
              simp [config, genSolidityConstructorDeployment, contract, constructorDecl,
                encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, uint256,
                staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | array xs =>
              simp [config, genSolidityConstructorDeployment, contract, constructorDecl,
                encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, uint256,
                staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | tuple xs =>
              simp [config, genSolidityConstructorDeployment, contract, constructorDecl,
                encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, uint256,
                staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | fixedBytes n bs =>
              simp [config, genSolidityConstructorDeployment, contract, constructorDecl,
                encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, uint256,
                staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | bytes =>
              simp [config, genSolidityConstructorDeployment, contract, constructorDecl,
                encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, uint256,
                staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | struct name fields =>
              simp [config, genSolidityConstructorDeployment, contract, constructorDecl,
                encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, uint256,
                staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | unit =>
              simp [config, genSolidityConstructorDeployment, contract, constructorDecl,
                encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, uint256,
                staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | storageRef er ty =>
              simp [config, genSolidityConstructorDeployment, contract, constructorDecl,
                encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, uint256,
                staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h

theorem daiCreationBytecode_size : daiCreationBytecode.size = 4312 := by
  native_decide

theorem daiBytecode_size : daiBytecode.size = 4011 := by
  native_decide

theorem daiCreationBytecode_runtime_window :
    daiCreationBytecode.extract 301 (301 + 4011) = daiBytecode := by
  native_decide

noncomputable def daiCtorCode (chainIdWord : UInt256) : ByteArray :=
  daiCreationBytecode ++ (EVM.Word.toBytesBE chainIdWord).toByteArray

theorem daiCreationBytecode_decode_append (tail : ByteArray) (pc : UInt256)
    (hpc : pc.toNat < 301) :
    decode (daiCreationBytecode ++ tail) pc = decode daiCreationBytecode pc :=
  Reasoning.Theory.decode_append_left_window daiCreationBytecode tail pc
    (by rw [daiCreationBytecode_size]; omega) (by rw [daiCreationBytecode_size]; norm_num)

macro "dai_ctor_decode" : tactic =>
  `(tactic|
    (first
      | rw [daiCreationBytecode_decode_append _ _ (by decide)]
      | (unfold daiCtorCode; rw [daiCreationBytecode_decode_append _ _ (by decide)]);
     native_decide))

macro "dai_ctor_jd" : tactic =>
  `(tactic|
    (first
      | (apply Reasoning.Theory.D_J_contains_append_left; native_decide)
      | (unfold daiCtorCode; apply Reasoning.Theory.D_J_contains_append_left; native_decide)))

open Lean in
macro "dai_ctor_run " base:term " with " "[" steps:evmStep,* "]" : term => do
  let mut acc := base
  for s in steps.getElems do
    match s with
    | `(evmStep| raw $op:ident $args*) =>
        acc ← `($(acc).$op $args*)
    | `(evmStep| $op:ident $args*) =>
        match op.getId with
        | `jump    => acc ← `($(acc).jump (by dai_ctor_decode) $(args[0]!) (by evm_ov))
        | `jumpiT  => acc ← `($(acc).jumpiT (by dai_ctor_decode) $(args[0]!) $(args[1]!)
                            (by evm_ov))
        | `jumpiNT => acc ← `($(acc).jumpiNT (by dai_ctor_decode) $(args[0]!) (by evm_ov))
        | _        => acc ← `($(acc).$op $args* (by dai_ctor_decode) (by evm_ov))
    | _ => Macro.throwUnsupported
  return acc

noncomputable def daiCtorRuntimeMem : ByteArray :=
  daiCreationBytecode.write 301 ByteArray.empty 0 4011

theorem daiCtorRuntimeMem_read :
    daiCtorRuntimeMem.readWithPadding 0 4011 = daiBytecode := by
  unfold daiCtorRuntimeMem
  calc
    (daiCreationBytecode.write 301 ByteArray.empty 0 4011).readWithPadding 0 4011
        = daiCreationBytecode.extract 301 (301 + 4011) :=
      write0_read_back_from_gen daiCreationBytecode ByteArray.empty 301 4011
        (by norm_num) (by rw [daiCreationBytecode_size]) (by norm_num)
    _ = daiBytecode := daiCreationBytecode_runtime_window

theorem daiCtorCode_size (chainIdWord : UInt256) :
    (daiCtorCode chainIdWord).size = 4344 := by
  unfold daiCtorCode
  rw [ByteArray.size_append, daiCreationBytecode_size, word_toBytesBE_toByteArray_size]

theorem daiCtorArgLen_eq (chainIdWord : UInt256) :
    (UInt256.ofNat (daiCtorCode chainIdWord).size).sub ⟨4312⟩ = (⟨32⟩ : UInt256) := by
  rw [daiCtorCode_size]
  native_decide

noncomputable def daiCtorArgMem (chainIdWord : UInt256) : ByteArray :=
  solcFreePtrMem ++ ffi.ByteArray.zeroes 32 ++ UInt256.toByteArray chainIdWord

theorem daiCtorArg_codecopy_mem (chainIdWord : UInt256) :
    (daiCtorCode chainIdWord).write 4312 solcFreePtrMem 128 32 =
      daiCtorArgMem chainIdWord := by
  unfold daiCtorArgMem daiCtorCode
  have hctorD : daiCreationBytecode.data.size = 4312 := daiCreationBytecode_size
  have hsfpD : solcFreePtrMem.data.size = 96 := solcFreePtrMem_size
  apply ByteArray.ext
  unfold ByteArray.write
  rw [if_neg (by norm_num : ¬ (32 : Nat) = 0),
    if_neg (show ¬ 4312 ≥ (daiCreationBytecode ++
      (EVM.Word.toBytesBE chainIdWord).toByteArray).size by
        rw [ByteArray.size_append, daiCreationBytecode_size, word_toBytesBE_toByteArray_size]
        norm_num)]
  have e1 :
      min 32 ((daiCreationBytecode ++ (EVM.Word.toBytesBE chainIdWord).toByteArray).size -
        4312) = 32 := by
    rw [ByteArray.size_append, daiCreationBytecode_size, word_toBytesBE_toByteArray_size]
    norm_num
  have e2 : min solcFreePtrMem.size (128 + 32) = 96 := by
    rw [solcFreePtrMem_size]
    norm_num
  simp only [ByteArray.data_copySlice, ByteArray.data_append, e1, solcFreePtrMem_size,
    show (128 : Nat) - 96 = 32 from by norm_num,
    show min 96 (128 + 32) - (128 + 32) = 0 from by norm_num]
  rw [show (ffi.ByteArray.zeroes 0).data = (#[] : Array UInt8) from by
    rw [zeroes_zero (n := 0) (by rfl)]
    rfl]
  have hz32 : (ffi.ByteArray.zeroes 32).data.size = 32 := by
    show (ffi.ByteArray.zeroes 32).size = 32
    exact zeroes_ofNat_size 32 (by norm_num)
  simp only [Array.append_empty, Nat.add_zero]
  have ext1 :
      (solcFreePtrMem.data ++ (ffi.ByteArray.zeroes 32).data).extract
          0 128 =
        solcFreePtrMem.data ++ (ffi.ByteArray.zeroes 32).data :=
    Array.extract_eq_self_of_le (by rw [Array.size_append, hsfpD, hz32])
  have ext2 :
      (daiCreationBytecode.data ++ (EVM.Word.toBytesBE chainIdWord).toByteArray.data).extract
          4312 (4312 + 32) =
        (UInt256.toByteArray chainIdWord).data := by
    rw [show (4312 : Nat) = daiCreationBytecode.data.size from hctorD.symm,
      Array.extract_append_right]
    rw [word_toBytesBE_toByteArray_eq_toByteArray]
    apply Array.extract_eq_self_of_le
    change (UInt256.toByteArray chainIdWord).size ≤ 32
    rw [toByteArray_size]
  rw [ext1, ext2,
    Array.extract_empty_of_size_le_start (by rw [Array.size_append, hsfpD, hz32]; norm_num),
    Array.append_empty]

theorem daiCtorArgMem_size (chainIdWord : UInt256) :
    (daiCtorArgMem chainIdWord).size = 160 := by
  unfold daiCtorArgMem
  simp [solcFreePtrMem_size, zeroes_ofNat_size 32 (by norm_num), toByteArray_size]

theorem daiCtorArgMem_read128 (chainIdWord : UInt256) :
    (daiCtorArgMem chainIdWord).readWithPadding 128 32 =
      UInt256.toByteArray chainIdWord := by
  unfold daiCtorArgMem
  rw [readWithPadding_eq_extract]
  · rw [extract_append_right_window]
    · rw [ByteArray.size_append, solcFreePtrMem_size,
        zeroes_ofNat_size 32 (by norm_num)]
      rw [show 128 - (96 + 32) = 0 by norm_num]
      rw [show 128 + 32 - (96 + 32) = 32 by norm_num]
      rw [toByteArray_extract_all]
    · rw [ByteArray.size_append, solcFreePtrMem_size,
        zeroes_ofNat_size 32 (by norm_num)]
  · rw [ByteArray.size_append, ByteArray.size_append, solcFreePtrMem_size,
      zeroes_ofNat_size 32 (by norm_num), toByteArray_size]

theorem daiCtorArgMem_mload128 (chainIdWord : UInt256) :
    (if (⟨128⟩ : UInt256).toNat ≥ (daiCtorArgMem chainIdWord).size
        ∨ (⟨128⟩ : UInt256) ≥ (UInt256.ofNat 5) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian ((daiCtorArgMem chainIdWord).readWithPadding 128 32))) =
      chainIdWord := by
  exact mloadWordValue_of_readWithPadding
    (mem := daiCtorArgMem chainIdWord) (aw := UInt256.ofNat 5) (off := ⟨128⟩)
    (v := chainIdWord)
    (by rw [daiCtorArgMem_size]; decide)
    (by decide)
    (daiCtorArgMem_read128 chainIdWord)

noncomputable def daiCtorArgFreeMem (chainIdWord : UInt256) : ByteArray :=
  (UInt256.toByteArray ⟨160⟩).write 0 (daiCtorArgMem chainIdWord) 64 32

theorem daiCtorArgFreeMem_size (chainIdWord : UInt256) :
    (daiCtorArgFreeMem chainIdWord).size = 160 := by
  unfold daiCtorArgFreeMem
  simp [daiCtorArgMem_size, write32_eq, ByteArray.size_append, ByteArray.size_extract,
    toByteArray_size]

theorem daiCtorArgFreeMem_read64 (chainIdWord : UInt256) :
    (daiCtorArgFreeMem chainIdWord).readWithPadding 64 32 =
      UInt256.toByteArray ⟨160⟩ := by
  unfold daiCtorArgFreeMem
  rw [toByteArray_write32_read_back]
  rw [daiCtorArgMem_size]
  decide

theorem daiCtorArgFreeMem_read128 (chainIdWord : UInt256) :
    (daiCtorArgFreeMem chainIdWord).readWithPadding 128 32 =
      UInt256.toByteArray chainIdWord := by
  unfold daiCtorArgFreeMem
  rw [write32_read_above _ _ 64 128 (by rw [toByteArray_size])
      (by rw [daiCtorArgMem_size]; omega) (by omega)
      (by rw [daiCtorArgMem_size])]
  exact daiCtorArgMem_read128 chainIdWord

theorem daiCtorArgFreeMem_mload128 (chainIdWord : UInt256) :
    (if (⟨128⟩ : UInt256).toNat ≥ (daiCtorArgFreeMem chainIdWord).size
        ∨ (⟨128⟩ : UInt256) ≥ (UInt256.ofNat 5) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian ((daiCtorArgFreeMem chainIdWord).readWithPadding 128 32))) =
      chainIdWord := by
  exact mloadWordValue_of_readWithPadding
    (mem := daiCtorArgFreeMem chainIdWord) (aw := UInt256.ofNat 5) (off := ⟨128⟩)
    (v := chainIdWord)
    (by rw [daiCtorArgFreeMem_size]; decide)
    (by decide)
    (daiCtorArgFreeMem_read128 chainIdWord)

abbrev daiCtorLocals (chainId : Int) : Store :=
  (∅ : Store).insert "chainId_" (.int chainId)

abbrev daiCtorFrame (chainId : Int) : Frame :=
  { contract := contract, locals := daiCtorLocals chainId }

abbrev daiCtorSourceKey (I : ExecutionEnv) : KeyValue :=
  .address I.source

abbrev daiCtorWardsSlot (I : ExecutionEnv) : UInt256 :=
  wardsSlot (daiCtorSourceKey I)

abbrev daiCtorDomainSlot : UInt256 :=
  ⟨5⟩

abbrev daiCtorThisWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.codeOwner.val

abbrev daiCtorSourceWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

abbrev daiCtorDomainPackedByteArray (chainIdWord : UInt256) (thisWord : UInt256) :
    ByteArray :=
  (ffi.KEC
    (String.toByteArray
      "EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)")).toList.toByteArray ++
    ((ffi.KEC (String.toByteArray "Dai Stablecoin")).toList.toByteArray ++
      ((ffi.KEC (String.toByteArray "1")).toList.toByteArray ++
        ((EVM.Word.toBytesBE chainIdWord).toByteArray ++
          (EVM.Word.toBytesBE thisWord).toByteArray)))

abbrev daiCtorDomainBytes (chainIdWord : UInt256) (thisWord : UInt256) : List UInt8 :=
  (ffi.KEC (daiCtorDomainPackedByteArray chainIdWord thisWord)).toList

abbrev daiCtorDomainWord (chainIdWord : UInt256) (thisWord : UInt256) : UInt256 :=
  uInt256OfByteArray (ffi.KEC (daiCtorDomainPackedByteArray chainIdWord thisWord))

abbrev daiCtorTypeHashWord : UInt256 :=
  ⟨63076024560530113402979550242307453568063438748328787417531900361828837441551⟩

abbrev daiCtorNameHashWord : UInt256 :=
  ⟨5011453723555049355537294002125739255229783229906611468909068372094763020939⟩

abbrev daiCtorVersionHashWord : UInt256 :=
  ⟨90743482286830539503240959006302832933333810038750515972785732718729991261126⟩

abbrev daiCtorNameMemoryWord : UInt256 :=
  UInt256.shiftLeft (⟨693460759908978978078209758180535⟩ : UInt256) ⟨145⟩

abbrev daiCtorVersionMemoryWord : UInt256 :=
  UInt256.shiftLeft (⟨49⟩ : UInt256) ⟨248⟩

theorem daiCtorTypeHashBytes :
    UInt256.toByteArray daiCtorTypeHashWord =
      (ffi.KEC
        (String.toByteArray
          "EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)")).toList.toByteArray := by
  simpa [daiCtorTypeHashWord] using daiCtorTypeHashBytes_trusted

theorem daiCtorNameHashBytes :
    UInt256.toByteArray daiCtorNameHashWord =
      (ffi.KEC (String.toByteArray "Dai Stablecoin")).toList.toByteArray := by
  simpa [daiCtorNameHashWord] using daiCtorNameHashBytes_trusted

theorem daiCtorVersionHashBytes :
    UInt256.toByteArray daiCtorVersionHashWord =
      (ffi.KEC (String.toByteArray "1")).toList.toByteArray := by
  simpa [daiCtorVersionHashWord] using daiCtorVersionHashBytes_trusted

noncomputable abbrev daiCtorWardsHashMem (I : ExecutionEnv) (chainIdWord : UInt256) :
    ByteArray :=
  twoWordHashMem (daiCtorSourceWord I) ⟨0⟩ (daiCtorArgFreeMem chainIdWord)

theorem wordAt0Mem_size_160 {mem : ByteArray} (word : UInt256) (hmem : mem.size = 160) :
    (wordAt0Mem word mem).size = 160 := by
  unfold wordAt0Mem
  exact toByteArray_write32_size_of_le mem word 0 160 160 hmem
    (by rw [hmem]; omega) (by omega)

theorem wordAt32Mem_size_160 {mem : ByteArray} (word : UInt256) (hmem : mem.size = 160) :
    (wordAt32Mem word mem).size = 160 := by
  unfold wordAt32Mem
  exact toByteArray_write32_size_of_le mem word 32 160 160 hmem
    (by rw [hmem]; omega) (by omega)

theorem twoWordHashMem_size_160 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 160) :
    (twoWordHashMem key slot mem).size = 160 := by
  unfold twoWordHashMem
  exact wordAt32Mem_size_160 slot (wordAt0Mem_size_160 key hmem)

theorem twoWordHashMem_read0_160 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 160) :
    (twoWordHashMem key slot mem).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_160 key hmem]; omega) (by omega)]
  exact wordAt0Mem_read0 key mem

theorem twoWordHashMem_read32_160 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 160) :
    (twoWordHashMem key slot mem).readWithPadding 32 32 =
      UInt256.toByteArray slot := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_160 key hmem]; omega)]
  exact toByteArray_extract_all slot

theorem twoWordHashMem_read64_160 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 160) (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨160⟩) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨160⟩ := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_160 key hmem]; omega) (by omega)
      (by rw [wordAt0Mem_size_160 key hmem]; omega)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by rw [hmem]; omega)
      (by omega) (by rw [hmem]; omega)]
  exact hread64

theorem twoWordHashMem_read0_64_160 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 160) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [twoWordHashMem_size_160 key slot hmem]; omega)]
  have hleft :
      (twoWordHashMem key slot mem).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [twoWordHashMem_size_160 key slot hmem]; omega),
      twoWordHashMem_read0_160 key slot hmem]
  have hright :
      (twoWordHashMem key slot mem).extract 32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [twoWordHashMem_size_160 key slot hmem]; omega),
      twoWordHashMem_read32_160 key slot hmem]
  rw [show (twoWordHashMem key slot mem).extract 0 64 =
      (twoWordHashMem key slot mem).extract 0 32 ++
        (twoWordHashMem key slot mem).extract 32 64 by
    rw [ByteArray.extract_append_extract]
    norm_num]
  rw [hleft, hright]

theorem daiCtorWardsHashMem_size (I : ExecutionEnv) (chainIdWord : UInt256) :
    (daiCtorWardsHashMem I chainIdWord).size = 160 := by
  exact twoWordHashMem_size_160 (daiCtorSourceWord I) ⟨0⟩
    (daiCtorArgFreeMem_size chainIdWord)

theorem daiCtorWardsHashMem_read64 (I : ExecutionEnv) (chainIdWord : UInt256) :
    (daiCtorWardsHashMem I chainIdWord).readWithPadding 64 32 =
      UInt256.toByteArray ⟨160⟩ := by
  exact twoWordHashMem_read64_160 (daiCtorSourceWord I) ⟨0⟩
    (daiCtorArgFreeMem_size chainIdWord) (daiCtorArgFreeMem_read64 chainIdWord)

theorem daiCtorWardsHashMem_mload64 (I : ExecutionEnv) (chainIdWord : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (daiCtorWardsHashMem I chainIdWord).size
        ∨ (⟨64⟩ : UInt256) ≥ (UInt256.ofNat 5) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((daiCtorWardsHashMem I chainIdWord).readWithPadding 64 32))) =
      ⟨160⟩ := by
  exact mloadWordValue_of_readWithPadding
    (mem := daiCtorWardsHashMem I chainIdWord) (aw := UInt256.ofNat 5) (off := ⟨64⟩)
    (v := ⟨160⟩)
    (by rw [daiCtorWardsHashMem_size]; decide)
    (by decide)
    (daiCtorWardsHashMem_read64 I chainIdWord)

theorem daiCtorWardsKeccakSlot (I : ExecutionEnv) (chainIdWord : UInt256) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((daiCtorWardsHashMem I chainIdWord).readWithPadding 0 64))) =
      daiCtorWardsSlot I := by
  unfold daiCtorWardsHashMem daiCtorWardsSlot wardsSlot mapSlot
  rw [twoWordHashMem_read0_64_160]
  · rw [keyValueToWord_address]
    exact mappingSlot_single (daiCtorSourceWord I) ⟨0⟩
  · exact daiCtorArgFreeMem_size chainIdWord

noncomputable abbrev daiCtorDomainNameMem (I : ExecutionEnv) (chainIdWord : UInt256) :
    ByteArray :=
  writeCascade (daiCtorWardsHashMem I chainIdWord)
    [(64, (⟨224⟩ : UInt256)), (160, (⟨14⟩ : UInt256)), (192, daiCtorNameMemoryWord)]

noncomputable abbrev daiCtorDomainPreMem (I : ExecutionEnv) (chainIdWord : UInt256) :
    ByteArray :=
  writeCascade (daiCtorDomainNameMem I chainIdWord)
    [(64, (⟨288⟩ : UInt256)), (224, (⟨1⟩ : UInt256)),
      (256, daiCtorVersionMemoryWord)]

noncomputable abbrev daiCtorDomainWordsMem (I : ExecutionEnv) (chainIdWord : UInt256) :
    ByteArray :=
  writeCascade (daiCtorDomainPreMem I chainIdWord)
    [(320, daiCtorTypeHashWord), (352, daiCtorNameHashWord),
      (384, daiCtorVersionHashWord), (416, chainIdWord), (448, daiCtorThisWord I)]

noncomputable abbrev daiCtorDomainHashMem (I : ExecutionEnv) (chainIdWord : UInt256) :
    ByteArray :=
  writeCascade (daiCtorDomainWordsMem I chainIdWord)
    [(288, (⟨160⟩ : UInt256)), (64, (⟨480⟩ : UInt256))]

noncomputable abbrev daiCtorDomainNameFreeMem (I : ExecutionEnv) (chainIdWord : UInt256) :
    ByteArray :=
  writeWord (daiCtorWardsHashMem I chainIdWord) 64 ⟨224⟩

noncomputable abbrev daiCtorDomainNameLenMem (I : ExecutionEnv) (chainIdWord : UInt256) :
    ByteArray :=
  writeWord (daiCtorDomainNameFreeMem I chainIdWord) 160 ⟨14⟩

noncomputable abbrev daiCtorDomainPreFreeMem (I : ExecutionEnv) (chainIdWord : UInt256) :
    ByteArray :=
  writeWord (daiCtorDomainNameMem I chainIdWord) 64 ⟨288⟩

noncomputable abbrev daiCtorDomainVersionLenMem (I : ExecutionEnv) (chainIdWord : UInt256) :
    ByteArray :=
  writeWord (daiCtorDomainPreFreeMem I chainIdWord) 224 ⟨1⟩

noncomputable abbrev daiCtorDomainTypeMem (I : ExecutionEnv) (chainIdWord : UInt256) :
    ByteArray :=
  writeWord (daiCtorDomainPreMem I chainIdWord) 320 daiCtorTypeHashWord

noncomputable abbrev daiCtorDomainNameHashMem (I : ExecutionEnv) (chainIdWord : UInt256) :
    ByteArray :=
  writeWord (daiCtorDomainTypeMem I chainIdWord) 352 daiCtorNameHashWord

noncomputable abbrev daiCtorDomainVersionHashMem (I : ExecutionEnv) (chainIdWord : UInt256) :
    ByteArray :=
  writeWord (daiCtorDomainNameHashMem I chainIdWord) 384 daiCtorVersionHashWord

noncomputable abbrev daiCtorDomainChainMem (I : ExecutionEnv) (chainIdWord : UInt256) :
    ByteArray :=
  writeWord (daiCtorDomainVersionHashMem I chainIdWord) 416 chainIdWord

noncomputable abbrev daiCtorDomainLenMem (I : ExecutionEnv) (chainIdWord : UInt256) :
    ByteArray :=
  writeWord (daiCtorDomainWordsMem I chainIdWord) 288 ⟨160⟩

noncomputable abbrev daiCtorReturnMem (I : ExecutionEnv) (chainIdWord : UInt256) :
    ByteArray :=
  (daiCtorCode chainIdWord).write 301 (daiCtorDomainHashMem I chainIdWord) 0 4011

theorem daiCtorDomainNameMem_size (I : ExecutionEnv) (chainIdWord : UInt256) :
    (daiCtorDomainNameMem I chainIdWord).size = 224 := by
  refine writeCascade_size_of_base _ _ (daiCtorWardsHashMem_size I chainIdWord) ?_ ?_
  · simp [WriteGapsOk]
    all_goals exact lt_usize _ (by norm_num)
  · simp [writeCascadeSize]

theorem daiCtorDomainPreMem_size (I : ExecutionEnv) (chainIdWord : UInt256) :
    (daiCtorDomainPreMem I chainIdWord).size = 288 := by
  refine writeCascade_size_of_base _ _ (daiCtorDomainNameMem_size I chainIdWord) ?_ ?_
  · simp [WriteGapsOk]
    all_goals exact lt_usize _ (by norm_num)
  · simp [writeCascadeSize]

theorem daiCtorDomainWordsMem_size (I : ExecutionEnv) (chainIdWord : UInt256) :
    (daiCtorDomainWordsMem I chainIdWord).size = 480 := by
  refine writeCascade_size_of_base _ _ (daiCtorDomainPreMem_size I chainIdWord) ?_ ?_
  · simp [WriteGapsOk]
    all_goals exact lt_usize _ (by norm_num)
  · simp [writeCascadeSize]

theorem daiCtorDomainHashMem_size (I : ExecutionEnv) (chainIdWord : UInt256) :
    (daiCtorDomainHashMem I chainIdWord).size = 480 := by
  refine writeCascade_size_of_base _ _ (daiCtorDomainWordsMem_size I chainIdWord) ?_ ?_
  · simp [WriteGapsOk]
    all_goals exact lt_usize _ (by norm_num)
  · simp [writeCascadeSize]

theorem daiCtorDomainNameMem_read64 (I : ExecutionEnv) (chainIdWord : UInt256) :
    (daiCtorDomainNameMem I chainIdWord).readWithPadding 64 32 =
      UInt256.toByteArray ⟨224⟩ := by
  exact writeCascade_read_word_of_head_of_base (daiCtorWardsHashMem I chainIdWord) ⟨224⟩
    [(160, (⟨14⟩ : UInt256)), (192, daiCtorNameMemoryWord)]
    (daiCtorWardsHashMem_size I chainIdWord)
    (by exact lt_usize _ (by norm_num))
    (by simp [WindowDisjointFromWrites])

theorem daiCtorDomainNameMem_mload64 (I : ExecutionEnv) (chainIdWord : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (daiCtorDomainNameMem I chainIdWord).size
        ∨ (⟨64⟩ : UInt256) ≥ (UInt256.ofNat 7) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((daiCtorDomainNameMem I chainIdWord).readWithPadding 64 32))) =
      ⟨224⟩ := by
  exact mloadWordValue_of_readWithPadding
    (mem := daiCtorDomainNameMem I chainIdWord) (aw := UInt256.ofNat 7) (off := ⟨64⟩)
    (v := ⟨224⟩)
    (by rw [daiCtorDomainNameMem_size]; decide)
    (by decide)
    (daiCtorDomainNameMem_read64 I chainIdWord)

theorem daiCtorDomainPreMem_read64 (I : ExecutionEnv) (chainIdWord : UInt256) :
    (daiCtorDomainPreMem I chainIdWord).readWithPadding 64 32 =
      UInt256.toByteArray ⟨288⟩ := by
  exact writeCascade_read_word_of_head_of_base (daiCtorDomainNameMem I chainIdWord) ⟨288⟩
    [(224, (⟨1⟩ : UInt256)), (256, daiCtorVersionMemoryWord)]
    (daiCtorDomainNameMem_size I chainIdWord)
    (by exact lt_usize _ (by norm_num))
    (by simp [WindowDisjointFromWrites])

theorem daiCtorDomainPreMem_mload64 (I : ExecutionEnv) (chainIdWord : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (daiCtorDomainPreMem I chainIdWord).size
        ∨ (⟨64⟩ : UInt256) ≥ (UInt256.ofNat 9) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((daiCtorDomainPreMem I chainIdWord).readWithPadding 64 32))) =
      ⟨288⟩ := by
  exact mloadWordValue_of_readWithPadding
    (mem := daiCtorDomainPreMem I chainIdWord) (aw := UInt256.ofNat 9) (off := ⟨64⟩)
    (v := ⟨288⟩)
    (by rw [daiCtorDomainPreMem_size]; decide)
    (by decide)
    (daiCtorDomainPreMem_read64 I chainIdWord)

theorem daiCtorDomainWordsMem_read64 (I : ExecutionEnv) (chainIdWord : UInt256) :
    (daiCtorDomainWordsMem I chainIdWord).readWithPadding 64 32 =
      UInt256.toByteArray ⟨288⟩ := by
  rw [daiCtorDomainWordsMem]
  rw [writeCascade_read_preserved_of_base _ _
      (daiCtorDomainPreMem_size I chainIdWord)
      (by
        simp [WindowDisjointFromWrites]
        exact lt_usize _ (by norm_num))]
  exact daiCtorDomainPreMem_read64 I chainIdWord

theorem daiCtorDomainWordsMem_mload64 (I : ExecutionEnv) (chainIdWord : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (daiCtorDomainWordsMem I chainIdWord).size
        ∨ (⟨64⟩ : UInt256) ≥ (UInt256.ofNat 15) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((daiCtorDomainWordsMem I chainIdWord).readWithPadding 64 32))) =
      ⟨288⟩ := by
  exact mloadWordValue_of_readWithPadding
    (mem := daiCtorDomainWordsMem I chainIdWord) (aw := UInt256.ofNat 15) (off := ⟨64⟩)
    (v := ⟨288⟩)
    (by rw [daiCtorDomainWordsMem_size]; decide)
    (by decide)
    (daiCtorDomainWordsMem_read64 I chainIdWord)

theorem daiCtorDomainHashMem_read288 (I : ExecutionEnv) (chainIdWord : UInt256) :
    (daiCtorDomainHashMem I chainIdWord).readWithPadding 288 32 =
      UInt256.toByteArray ⟨160⟩ := by
  exact writeCascade_read_word_of_head_of_base (daiCtorDomainWordsMem I chainIdWord) ⟨160⟩
    [(64, (⟨480⟩ : UInt256))]
    (daiCtorDomainWordsMem_size I chainIdWord)
    (by exact lt_usize _ (by norm_num))
    (by simp [WindowDisjointFromWrites])

theorem daiCtorDomainHashMem_mload288 (I : ExecutionEnv) (chainIdWord : UInt256) :
    (if (⟨288⟩ : UInt256).toNat ≥ (daiCtorDomainHashMem I chainIdWord).size
        ∨ (⟨288⟩ : UInt256) ≥ (UInt256.ofNat 15) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((daiCtorDomainHashMem I chainIdWord).readWithPadding 288 32))) =
      ⟨160⟩ := by
  exact mloadWordValue_of_readWithPadding
    (mem := daiCtorDomainHashMem I chainIdWord) (aw := UInt256.ofNat 15) (off := ⟨288⟩)
    (v := ⟨160⟩)
    (by rw [daiCtorDomainHashMem_size]; decide)
    (by decide)
    (daiCtorDomainHashMem_read288 I chainIdWord)

theorem daiCtorDomainWordsMem_read320 (I : ExecutionEnv) (chainIdWord : UInt256) :
    (daiCtorDomainWordsMem I chainIdWord).readWithPadding 320 160 =
      UInt256.toByteArray daiCtorTypeHashWord ++
        (UInt256.toByteArray daiCtorNameHashWord ++
          (UInt256.toByteArray daiCtorVersionHashWord ++
            (UInt256.toByteArray chainIdWord ++ UInt256.toByteArray (daiCtorThisWord I)))) := by
  let mem := daiCtorDomainWordsMem I chainIdWord
  have hsize : mem.size = 480 := daiCtorDomainWordsMem_size I chainIdWord
  have h320 : mem.readWithPadding 320 32 = UInt256.toByteArray daiCtorTypeHashWord := by
    exact writeCascade_read_word_of_head_of_base (daiCtorDomainPreMem I chainIdWord)
      daiCtorTypeHashWord
      [(352, daiCtorNameHashWord), (384, daiCtorVersionHashWord), (416, chainIdWord),
        (448, daiCtorThisWord I)]
      (daiCtorDomainPreMem_size I chainIdWord)
      (by exact lt_usize _ (by norm_num))
      (by simp [WindowDisjointFromWrites])
  have h352 : mem.readWithPadding 352 32 = UInt256.toByteArray daiCtorNameHashWord := by
    unfold mem daiCtorDomainWordsMem
    rw [writeCascade_cons]
    have hbase : (writeWord (daiCtorDomainPreMem I chainIdWord) 320
        daiCtorTypeHashWord).size = 352 := by
      rw [writeWord_size]
      · rw [daiCtorDomainPreMem_size]
        norm_num
      · rw [daiCtorDomainPreMem_size]
        exact lt_usize _ (by norm_num)
    exact writeCascade_read_word_of_head_of_base
      (writeWord (daiCtorDomainPreMem I chainIdWord) 320 daiCtorTypeHashWord)
      daiCtorNameHashWord
      [(384, daiCtorVersionHashWord), (416, chainIdWord), (448, daiCtorThisWord I)]
      hbase (by exact lt_usize _ (by norm_num))
      (by simp [WindowDisjointFromWrites])
  have h384 : mem.readWithPadding 384 32 = UInt256.toByteArray daiCtorVersionHashWord := by
    unfold mem daiCtorDomainWordsMem
    rw [writeCascade_cons, writeCascade_cons]
    have hbase320 :
        (writeWord (daiCtorDomainPreMem I chainIdWord) 320 daiCtorTypeHashWord).size =
          352 := by
      rw [writeWord_size]
      · rw [daiCtorDomainPreMem_size]
        norm_num
      · rw [daiCtorDomainPreMem_size]
        exact lt_usize _ (by norm_num)
    have hbase :
        (writeWord (writeWord (daiCtorDomainPreMem I chainIdWord) 320
          daiCtorTypeHashWord) 352 daiCtorNameHashWord).size = 384 := by
      rw [writeWord_size]
      · rw [hbase320]
        norm_num
      · rw [hbase320]
        exact lt_usize _ (by norm_num)
    exact writeCascade_read_word_of_head_of_base
      (writeWord (writeWord (daiCtorDomainPreMem I chainIdWord) 320
        daiCtorTypeHashWord) 352 daiCtorNameHashWord)
      daiCtorVersionHashWord
      [(416, chainIdWord), (448, daiCtorThisWord I)]
      hbase (by exact lt_usize _ (by norm_num))
      (by simp [WindowDisjointFromWrites])
  have h416 : mem.readWithPadding 416 32 = UInt256.toByteArray chainIdWord := by
    unfold mem daiCtorDomainWordsMem
    rw [writeCascade_cons, writeCascade_cons, writeCascade_cons]
    have hbase320 :
        (writeWord (daiCtorDomainPreMem I chainIdWord) 320 daiCtorTypeHashWord).size =
          352 := by
      rw [writeWord_size]
      · rw [daiCtorDomainPreMem_size]
        norm_num
      · rw [daiCtorDomainPreMem_size]
        exact lt_usize _ (by norm_num)
    have hbase352 :
        (writeWord (writeWord (daiCtorDomainPreMem I chainIdWord) 320
          daiCtorTypeHashWord) 352 daiCtorNameHashWord).size = 384 := by
      rw [writeWord_size]
      · rw [hbase320]
        norm_num
      · rw [hbase320]
        exact lt_usize _ (by norm_num)
    have hbase :
        (writeWord (writeWord (writeWord (daiCtorDomainPreMem I chainIdWord) 320
          daiCtorTypeHashWord) 352 daiCtorNameHashWord) 384
          daiCtorVersionHashWord).size = 416 := by
      rw [writeWord_size]
      · rw [hbase352]
        norm_num
      · rw [hbase352]
        exact lt_usize _ (by norm_num)
    exact writeCascade_read_word_of_head_of_base
      (writeWord (writeWord (writeWord (daiCtorDomainPreMem I chainIdWord) 320
        daiCtorTypeHashWord) 352 daiCtorNameHashWord) 384 daiCtorVersionHashWord)
      chainIdWord [(448, daiCtorThisWord I)]
      hbase (by exact lt_usize _ (by norm_num))
      (by simp [WindowDisjointFromWrites])
  have h448 : mem.readWithPadding 448 32 = UInt256.toByteArray (daiCtorThisWord I) := by
    unfold mem daiCtorDomainWordsMem
    rw [writeCascade_cons, writeCascade_cons, writeCascade_cons, writeCascade_cons]
    have hbase320 :
        (writeWord (daiCtorDomainPreMem I chainIdWord) 320 daiCtorTypeHashWord).size =
          352 := by
      rw [writeWord_size]
      · rw [daiCtorDomainPreMem_size]
        norm_num
      · rw [daiCtorDomainPreMem_size]
        exact lt_usize _ (by norm_num)
    have hbase352 :
        (writeWord (writeWord (daiCtorDomainPreMem I chainIdWord) 320
          daiCtorTypeHashWord) 352 daiCtorNameHashWord).size = 384 := by
      rw [writeWord_size]
      · rw [hbase320]
        norm_num
      · rw [hbase320]
        exact lt_usize _ (by norm_num)
    have hbase384 :
        (writeWord (writeWord (writeWord (daiCtorDomainPreMem I chainIdWord) 320
          daiCtorTypeHashWord) 352 daiCtorNameHashWord) 384
          daiCtorVersionHashWord).size = 416 := by
      rw [writeWord_size]
      · rw [hbase352]
        norm_num
      · rw [hbase352]
        exact lt_usize _ (by norm_num)
    have hbase :
        (writeWord (writeWord (writeWord (writeWord (daiCtorDomainPreMem I chainIdWord)
          320 daiCtorTypeHashWord) 352 daiCtorNameHashWord) 384
          daiCtorVersionHashWord) 416 chainIdWord).size = 448 := by
      rw [writeWord_size]
      · rw [hbase384]
        norm_num
      · rw [hbase384]
        exact lt_usize _ (by norm_num)
    exact writeCascade_read_word_of_head_of_base
      (writeWord (writeWord (writeWord (writeWord (daiCtorDomainPreMem I chainIdWord)
        320 daiCtorTypeHashWord) 352 daiCtorNameHashWord) 384 daiCtorVersionHashWord)
        416 chainIdWord)
      (daiCtorThisWord I) [] hbase (by exact lt_usize _ (by norm_num)) trivial
  unfold mem at hsize h320 h352 h384 h416 h448
  rw [byteArray_readWithPadding_split _ 320 32 128 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by rw [hsize]),
    h320]
  rw [byteArray_readWithPadding_split _ 352 32 96 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by rw [hsize]),
    h352]
  rw [byteArray_readWithPadding_split _ 384 32 64 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by rw [hsize]),
    h384]
  rw [byteArray_readWithPadding_split _ 416 32 32 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by rw [hsize]),
    h416, h448]

theorem daiCtorDomainHashMem_read320 (I : ExecutionEnv) (chainIdWord : UInt256) :
    (daiCtorDomainHashMem I chainIdWord).readWithPadding 320 160 =
      UInt256.toByteArray daiCtorTypeHashWord ++
        (UInt256.toByteArray daiCtorNameHashWord ++
          (UInt256.toByteArray daiCtorVersionHashWord ++
            (UInt256.toByteArray chainIdWord ++ UInt256.toByteArray (daiCtorThisWord I)))) := by
  unfold daiCtorDomainHashMem
  rw [writeCascade_read_preserved_len _ _ 320 160
      (by
        rw [daiCtorDomainWordsMem_size]
        simp [WindowDisjointFromWrites]) (by norm_num) (by norm_num)]
  exact daiCtorDomainWordsMem_read320 I chainIdWord

theorem daiCtorDomainKeccakWord (I : ExecutionEnv) (chainIdWord : UInt256) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((daiCtorDomainHashMem I chainIdWord).readWithPadding 320 160))) =
      daiCtorDomainWord chainIdWord (daiCtorThisWord I) := by
  rw [daiCtorDomainHashMem_read320]
  unfold daiCtorDomainWord daiCtorDomainPackedByteArray
  rw [daiCtorTypeHashBytes, daiCtorNameHashBytes, daiCtorVersionHashBytes,
    word_toBytesBE_toByteArray_eq_toByteArray,
    word_toBytesBE_toByteArray_eq_toByteArray]
  exact keccakSlot_eq _

theorem daiCtorReturnMem_read (I : ExecutionEnv) (chainIdWord : UInt256) :
    (daiCtorReturnMem I chainIdWord).readWithPadding 0 4011 =
      daiBytecode := by
  unfold daiCtorReturnMem
  rw [write0_read_back_from_gen (daiCtorCode chainIdWord) (daiCtorDomainHashMem I chainIdWord)
    301 4011 (by decide) (by rw [daiCtorCode_size]; omega) (by decide)]
  have hleft :
      (daiCtorCode chainIdWord).extract 301 (301 + 4011) =
        daiCreationBytecode.extract 301 (301 + 4011) := by
    unfold daiCtorCode
    exact extract_append_left daiCreationBytecode (EVM.Word.toBytesBE chainIdWord).toByteArray
      301 (301 + 4011) (by rw [daiCreationBytecode_size])
  rw [hleft, daiCreationBytecode_runtime_window]

theorem daiCtorLocals_get_chainId (chainId : Int) :
    (daiCtorLocals chainId).get? "chainId_" = some (.int chainId) := by
  unfold daiCtorLocals
  simp

theorem daiCtorLocals_get_wards (chainId : Int) :
    (daiCtorLocals chainId).get? "wards" = none := by
  unfold daiCtorLocals
  rw [store_get_ne _ _ (by native_decide)]
  simp

theorem daiCtorLocals_get_DOMAIN_SEPARATOR (chainId : Int) :
    (daiCtorLocals chainId).get? "DOMAIN_SEPARATOR" = none := by
  unfold daiCtorLocals
  rw [store_get_ne _ _ (by native_decide)]
  simp

theorem evalStorageRef_daiCtor_wards (evm : EVM.State) (I : ExecutionEnv) (chainId : Int)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config (daiCtorFrame chainId) evm (wardsRef sender) =
      .ok { base := "wards", steps := [.mindex (daiCtorSourceKey I)] } := by
  simp [evalStorageRef, evalStorageRefStep, wardsRef, sender, envValue, daiCtorFrame,
    daiCtorSourceKey, valueToKey?, EvalResult.bind, bind, pure, evalExpr?, hsrc]
  rfl

theorem evalStorageRef_daiCtor_domain (evm : EVM.State) (chainId : Int) :
    evalStorageRef config (daiCtorFrame chainId) evm domainSeparatorRef =
      .ok { base := "DOMAIN_SEPARATOR", steps := [] } := by
  simp [evalStorageRef, domainSeparatorRef, daiCtorFrame, EvalResult.bind, bind, pure]

theorem byteArray_mk_toArray_eq_toByteArray (xs : List UInt8) :
    ByteArray.mk xs.toArray = xs.toByteArray := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  change xs.toArray.toList = xs.toByteArray.data.toList
  rw [show xs.toArray.toList = xs by simp]
  rw [List.toList_data_toByteArray]

theorem keccak_toList_length (bytes : ByteArray) : (ffi.KEC bytes).toList.length = 32 := by
  rw [byteArray_toList_eq, Array.length_toList]
  exact keccak_size bytes

theorem encodePacked_bytes32_of_length {bytes : List UInt8}
    (hlen : bytes.length = fixedBytesSize bytes32Width) :
    encodePackedValue? bytes32 (.fixedBytes bytes32Width bytes) = some bytes := by
  simp [encodePackedValue?, bytes32, fixedBytesSize, hlen]

theorem encodePacked_uint256_word (value : UInt256) :
    encodePackedValue? uint256 (.int (Int.ofNat value.toNat)) =
      some (EVM.Word.toBytesBE value) := by
  have hword : EVM.word value.toNat = value := u256_ofNat_toNat value
  have hlt : value.toNat < EVM.twoPow 256 := by
    change value.val.val < EVM.twoPow 256
    exact value.val.isLt
  simp [encodePackedValue?, uint256, uint256Int, encodeABIWord?, hword, hlt]

theorem evalPackedArgs_cons_ok {cfg : Config} {solm : Frame} {evm : EVM.State}
    {ty : ABIType} {e : Expr} {v : Value} {head tailBytes : List UInt8}
    {rest : List (ABIType × Expr)}
    (heval : evalExpr? cfg solm evm e = .ok v)
    (henc : encodePackedValue? ty v = some head)
    (htail : evalPackedArgs? cfg solm evm rest = .ok tailBytes) :
    evalPackedArgs? cfg solm evm ((ty, e) :: rest) = .ok (head ++ tailBytes) := by
  rw [evalPackedArgs?]
  simp only [heval, henc, htail, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem evalExpr_daiCtor_chainId (evm : EVM.State) (chainId : Int) :
    evalExpr? config (daiCtorFrame chainId) evm (.var "chainId_") = .ok (.int chainId) := by
  rw [evalExpr?]
  rw [daiCtorLocals_get_chainId]
  simp [EvalResult.ofOption]

theorem evalExpr_daiCtor_this_uint256 (evm : EVM.State) (chainId : Int) :
    evalExpr? config (daiCtorFrame chainId) evm (addressAsUint256 (.env .this)) =
      .ok (.int (Int.ofNat (UInt256.ofNat evm.executionEnv.codeOwner.val).toNat)) := by
  unfold addressAsUint256
  rw [evalExpr?]
  simp only [evalExpr?, envValue, EvalResult.bind, bind, EvalResult.ofOption, pure]
  unfold castValue? uint256St uint256Int
  simp only
  have haddr : evm.executionEnv.codeOwner.val < EVM.twoPow 256 := by
    exact lt_of_lt_of_le evm.executionEnv.codeOwner.isLt (by decide)
  simp [haddr]
  rw [UInt256.toNat_ofNat_of_lt]
  exact haddr

theorem evalExpr_daiCtor_domain (evm : EVM.State) (chainId : Int)
    (h0 : 0 ≤ chainId) (hlt : chainId < Int.ofNat (EVM.twoPow 256)) :
    evalExpr? config (daiCtorFrame chainId) evm domainSeparatorExpr =
      .ok (.fixedBytes bytes32Width
        (daiCtorDomainBytes (EVM.word chainId.toNat)
          (UInt256.ofNat evm.executionEnv.codeOwner.val))) := by
  let typeHash := (ffi.KEC
    (String.toByteArray
      "EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)")).toList
  let nameHash := (ffi.KEC (String.toByteArray "Dai Stablecoin")).toList
  let versionHash := (ffi.KEC (String.toByteArray "1")).toList
  let chainWord := EVM.word chainId.toNat
  let thisWord := UInt256.ofNat evm.executionEnv.codeOwner.val
  have hpacked :
      evalPackedArgs? config (daiCtorFrame chainId) evm
        [ (bytes32, .keccak256
            (.bytesLit
              (String.toByteArray
                "EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"))),
          (bytes32, .keccak256 (.bytesLit (String.toByteArray "Dai Stablecoin"))),
          (bytes32, .keccak256 (.bytesLit (String.toByteArray "1"))),
          (uint256, .var "chainId_"),
          (uint256, addressAsUint256 (.env .this)) ] =
        .ok (typeHash ++ (nameHash ++ (versionHash ++
          (EVM.Word.toBytesBE chainWord ++ EVM.Word.toBytesBE thisWord)))) := by
    refine evalPackedArgs_cons_ok
      (v := .fixedBytes bytes32Width typeHash) (head := typeHash)
      (tailBytes := nameHash ++ (versionHash ++
        (EVM.Word.toBytesBE chainWord ++ EVM.Word.toBytesBE thisWord)))
      ?_ ?_ ?_
    · unfold typeHash
      rw [evalExpr?]
      simp [evalExpr?, EvalResult.bind, bind, pure, bytes32Width]
    · exact encodePacked_bytes32_of_length (by unfold typeHash; simp [fixedBytesSize,
        bytes32Width, keccak_toList_length])
    · refine evalPackedArgs_cons_ok
        (v := .fixedBytes bytes32Width nameHash) (head := nameHash)
        (tailBytes := versionHash ++
          (EVM.Word.toBytesBE chainWord ++ EVM.Word.toBytesBE thisWord))
        ?_ ?_ ?_
      · unfold nameHash
        rw [evalExpr?]
        simp [evalExpr?, EvalResult.bind, bind, pure, bytes32Width]
      · exact encodePacked_bytes32_of_length (by unfold nameHash; simp [fixedBytesSize,
          bytes32Width, keccak_toList_length])
      · refine evalPackedArgs_cons_ok
          (v := .fixedBytes bytes32Width versionHash) (head := versionHash)
          (tailBytes := EVM.Word.toBytesBE chainWord ++ EVM.Word.toBytesBE thisWord)
          ?_ ?_ ?_
        · unfold versionHash
          rw [evalExpr?]
          simp [evalExpr?, EvalResult.bind, bind, pure, bytes32Width]
        · exact encodePacked_bytes32_of_length (by unfold versionHash; simp [fixedBytesSize,
            bytes32Width, keccak_toList_length])
        · refine evalPackedArgs_cons_ok
            (v := .int (Int.ofNat chainWord.toNat)) (head := EVM.Word.toBytesBE chainWord)
            (tailBytes := EVM.Word.toBytesBE thisWord)
            ?_ ?_ ?_
          · have hword : chainWord.toNat = chainId.toNat := by
              unfold chainWord
              exact constructorUInt256Word_toNat chainId h0 hlt
            rw [show Int.ofNat chainWord.toNat = chainId by
              rw [hword]
              exact Int.toNat_of_nonneg h0]
            exact evalExpr_daiCtor_chainId evm chainId
          · exact encodePacked_uint256_word chainWord
          · simpa using
              evalPackedArgs_cons_ok
                (cfg := config) (solm := daiCtorFrame chainId) (evm := evm)
                (ty := uint256) (e := addressAsUint256 (.env .this))
                (v := .int (Int.ofNat thisWord.toNat))
                (head := EVM.Word.toBytesBE thisWord) (tailBytes := []) (rest := [])
                (by simpa [thisWord] using evalExpr_daiCtor_this_uint256 evm chainId)
                (encodePacked_uint256_word thisWord)
                (by rw [evalPackedArgs?]; rfl)
  unfold domainSeparatorExpr daiCtorDomainBytes daiCtorDomainPackedByteArray
  rw [evalExpr?]
  rw [evalExpr?]
  rw [hpacked]
  change EvalResult.ok (Value.fixedBytes bytes32Width
      (ffi.KEC (ByteArray.mk
        (typeHash ++ (nameHash ++ (versionHash ++
          (EVM.Word.toBytesBE chainWord ++ EVM.Word.toBytesBE thisWord)))).toArray)).toList) =
    EvalResult.ok (Value.fixedBytes bytes32Width
      (ffi.KEC
        (typeHash.toByteArray ++ (nameHash.toByteArray ++
          (versionHash.toByteArray ++
            ((EVM.Word.toBytesBE chainWord).toByteArray ++
              (EVM.Word.toBytesBE thisWord).toByteArray))))).toList)
  rw [byteArray_mk_toArray_eq_toByteArray]
  simp only [List.toByteArray_append, ByteArray.append_assoc]

theorem daiCtorDomainValueToWord (chainIdWord thisWord : UInt256) :
    valueToWord (.fixedBytes bytes32Width (daiCtorDomainBytes chainIdWord thisWord)) =
      some (daiCtorDomainWord chainIdWord thisWord) := by
  unfold daiCtorDomainWord daiCtorDomainBytes
  simp [valueToWord, fixedBytesToNat?, fixedBytesValid, fixedBytesSize, bytes32Width, keccak_size,
    uInt256OfByteArray_eq, fromByteArrayBigEndian, byteArray_toList_eq]
  rfl

def daiCtorPostState (evm : EVM.State) (I : ExecutionEnv)
    (chainIdWord : UInt256) : EVM.State :=
  Solm.EVM.storageStore
    (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (daiCtorWardsSlot I) ⟨1⟩)
    evm.executionEnv.codeOwner daiCtorDomainSlot
    (daiCtorDomainWord chainIdWord (daiCtorThisWord I))

theorem daiCtorAssignWards (evm : EVM.State) (I : ExecutionEnv) (chainId : Int)
    (hsrc : evm.executionEnv.source = I.source) :
    assignStorageRef? config (daiCtorFrame chainId) evm
      .storage (wardsRef sender) (.int 1) =
        .ok (daiCtorFrame chainId,
          Solm.EVM.storageStore evm evm.executionEnv.codeOwner (daiCtorWardsSlot I) ⟨1⟩) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (loc := wordLoc (daiCtorWardsSlot I) (.int uint256Int))
      (hbase := daiCtorLocals_get_wards chainId)
      (her := evalStorageRef_daiCtor_wards evm I chainId hsrc)
      (hty := by
        simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, daiCtorSourceKey,
          uint256St])
      (hloc := by rfl)
  simpa [wordLoc, uint256Loc, uint256Int] using
    storageLocStore_uint256 evm (daiCtorWardsSlot I) ⟨1⟩

theorem daiCtorAssignDomain (evm : EVM.State) (I : ExecutionEnv) (chainId : Int)
    (chainIdWord : UInt256) :
    assignStorageRef? config (daiCtorFrame chainId) evm
      .storage domainSeparatorRef
      (.fixedBytes bytes32Width (daiCtorDomainBytes chainIdWord (daiCtorThisWord I))) =
        .ok (daiCtorFrame chainId,
          Solm.EVM.storageStore evm evm.executionEnv.codeOwner daiCtorDomainSlot
            (daiCtorDomainWord chainIdWord (daiCtorThisWord I))) := by
  apply assignStorageRef_storage_scalar_value
      (ty := bytes32St)
      (loc := wordLoc daiCtorDomainSlot (.bytes bytes32Width))
      (hbase := daiCtorLocals_get_DOMAIN_SEPARATOR chainId)
      (her := evalStorageRef_daiCtor_domain evm chainId)
      (hty := by simp [storageTypeAt?, contract, storageDecls, bytes32St])
      (hloc := by rfl)
      (hscalar := by trivial)
  simpa [wordLoc, bytes32Loc, bytes32Width] using
    storageLocStore_bytes32 evm daiCtorDomainSlot
      (daiCtorDomainWord chainIdWord (daiCtorThisWord I))
      (.fixedBytes bytes32Width (daiCtorDomainBytes chainIdWord (daiCtorThisWord I)))
      (daiCtorDomainValueToWord chainIdWord (daiCtorThisWord I))

theorem daiSolmCtorExecReverts_nonpayable
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (chainId : Int)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    solmCtorExec config contract [.int chainId] createdAccounts genesisBlockHeader blocks
      σ σ₀ g A I .reverted := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I)
    (argsStore := daiCtorLocals chainId)
    ?_ rfl ?_ ?_
  · rfl
  · simp [daiCtorLocals, contract, constructorDecl]
  · exact bodyReverts_nonPayable (cfg := config) (contract := contract)
      (locals := daiCtorLocals chainId) hwv

theorem daiInitcodeNonpayableRevert
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (tail : ByteArray)
    (hcode : I.code = daiCreationBytecode ++ tail)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev (daiCreationBytecode ++ tail) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  have rd0 :
      RD (daiCreationBytecode ++ tail) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨0⟩ []
        ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (createdAccounts, σ) 0 0 :=
    RD.initState hcode
  have rd11 := dai_ctor_run rd0 with [
    push1 ⟨128⟩, push1 ⟨64⟩,
    raw mstore 9 solcFreePtrMem (UInt256.ofNat 3)
      (by dai_ctor_decode)
      mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by evm_ov),
    callvalue, dup1, iszero, push2 ⟨16⟩, jumpiNT (isZero_eq_zero_of_ne hwv)]
  exact dai_ctor_run rd11 with [
    push1 ⟨0⟩, dup1,
    raw rev 0 (by dai_ctor_decode) mem_cost (by evm_ov)]

theorem daiCtorPayableGuardTrace
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (chainIdWord : UInt256)
    (hcode : I.code = daiCtorCode chainIdWord)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD (daiCtorCode chainIdWord) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨18⟩
      [] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (createdAccounts, σ) k C := by
  have rd0 :
      RD (daiCtorCode chainIdWord) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨0⟩ []
        ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (createdAccounts, σ) 0 0 :=
    RD.initState hcode
  have rd16 := dai_ctor_run rd0 with [
    push1 ⟨128⟩, push1 ⟨64⟩,
    raw mstore 9 solcFreePtrMem (UInt256.ofNat 3)
      (by dai_ctor_decode)
      mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by evm_ov),
    callvalue, dup1, iszero, push2 ⟨16⟩,
    jumpiT (by rw [hwv]; decide) (by dai_ctor_jd),
    jumpdest, pop]
  exact ⟨_, _, rd16⟩

set_option maxHeartbeats 3000000 in
theorem daiCtorArgCodecopyTrace
    {I : ExecutionEnv}
    {g : Sat256}
    {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (chainIdWord : UInt256)
    (h : RD (daiCtorCode chainIdWord) I g s0 ⟨18⟩ []
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C) :
    ∃ k' C', RD (daiCtorCode chainIdWord) I g s0 ⟨32⟩
      [⟨32⟩, ⟨128⟩] (daiCtorArgMem chainIdWord) (UInt256.ofNat 5)
      rdata acc k' C' := by
  have rd := dai_ctor_run h with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3)
      (by dai_ctor_decode) mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push2 ⟨4312⟩, codesize, sub, dup1, push2 ⟨4312⟩, dup4,
    raw codecopy 6 (daiCtorArgMem chainIdWord) (UInt256.ofNat 5)
      (by dai_ctor_decode)
      (fun s haws hstks => by
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
          List.getElem!_cons_zero, List.getElem!_cons_succ]
        rw [daiCtorArgLen_eq]
        decide)
      (by
        rw [daiCtorArgLen_eq]
        exact daiCtorArg_codecopy_mem chainIdWord)
      (by rw [daiCtorArgLen_eq]; decide) (by evm_ov)]
  have rd' : RD (daiCtorCode chainIdWord) I g s0 ⟨32⟩
      [⟨32⟩, ⟨128⟩] (daiCtorArgMem chainIdWord) (UInt256.ofNat 5) rdata acc
      (k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
      (C + 3 + (0 + 3) + 3 + 2 + 3 + 3 + 3 + 3 +
        (6 + (GasConstants.Gverylow + GasConstants.Gcopy * ((32 + 31) / 32)))) := by
    simpa [daiCtorArgLen_eq] using rd
  exact ⟨_, _, rd'⟩

theorem daiCtorArgFreePtrTrace
    {I : ExecutionEnv}
    {g : Sat256}
    {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (chainIdWord : UInt256)
    (h : RD (daiCtorCode chainIdWord) I g s0 ⟨32⟩
      [⟨32⟩, ⟨128⟩] (daiCtorArgMem chainIdWord) (UInt256.ofNat 5) rdata acc k C) :
    ∃ k' C', RD (daiCtorCode chainIdWord) I g s0 ⟨38⟩
      [⟨32⟩, ⟨128⟩] (daiCtorArgFreeMem chainIdWord) (UInt256.ofNat 5)
      rdata acc k' C' := by
  have rd := dai_ctor_run h with [
    dup2, dup2, add, push1 ⟨64⟩,
    raw mstore 0 (daiCtorArgFreeMem chainIdWord) (UInt256.ofNat 5)
      (by dai_ctor_decode) mem_cost rfl (by decide) (by evm_ov)]
  exact ⟨_, _, rd⟩

theorem daiCtorArgCopyTrace
    {I : ExecutionEnv}
    {g : Sat256}
    {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (chainIdWord : UInt256)
    (h : RD (daiCtorCode chainIdWord) I g s0 ⟨18⟩ []
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C) :
    ∃ k' C', RD (daiCtorCode chainIdWord) I g s0 ⟨38⟩
      [⟨32⟩, ⟨128⟩] (daiCtorArgFreeMem chainIdWord) (UInt256.ofNat 5)
      rdata acc k' C' := by
  obtain ⟨_, _, rd32⟩ := daiCtorArgCodecopyTrace (I := I) chainIdWord h
  exact daiCtorArgFreePtrTrace (I := I) chainIdWord rd32

theorem daiCtorArgLengthCheckTrace
    {I : ExecutionEnv}
    {g : Sat256}
    {s0 : State}
    {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    {chainIdWord : UInt256}
    (h : RD (daiCtorCode chainIdWord) I g s0 ⟨38⟩
      [⟨32⟩, ⟨128⟩] mem (UInt256.ofNat 5) rdata acc k C) :
    ∃ k' C', RD (daiCtorCode chainIdWord) I g s0 ⟨53⟩
      [⟨128⟩] mem (UInt256.ofNat 5) rdata acc k' C' := by
  have rd := dai_ctor_run h with [
    push1 ⟨32⟩, dup2, lt, iszero, push2 ⟨51⟩,
    jumpiT (by native_decide) (by dai_ctor_jd),
    jumpdest, pop]
  exact ⟨_, _, rd⟩

theorem daiInitcodePrologueSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (chainIdWord : UInt256)
    (hcode : I.code = daiCtorCode chainIdWord)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD (daiCtorCode chainIdWord) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨53⟩
      [⟨128⟩] (daiCtorArgFreeMem chainIdWord) (UInt256.ofNat 5) ByteArray.empty
      (createdAccounts, σ) k C := by
  obtain ⟨_, _, rd18⟩ :=
    daiCtorPayableGuardTrace
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      chainIdWord hcode hwv
  obtain ⟨_, _, rd38⟩ := daiCtorArgCopyTrace (I := I) chainIdWord rd18
  exact daiCtorArgLengthCheckTrace (I := I) (chainIdWord := chainIdWord) rd38

set_option maxHeartbeats 900000 in
theorem daiCtorWardsStoreTrace
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {σ : AccountMap}
    {I : ExecutionEnv}
    {g : Sat256}
    {s0 : State}
    {rdata : ByteArray}
    {k C : Nat}
    (chainIdWord : UInt256)
    (h : RD (daiCtorCode chainIdWord) I g s0 ⟨53⟩
      [⟨128⟩] (daiCtorArgFreeMem chainIdWord) (UInt256.ofNat 5) rdata
      (createdAccounts, σ) k C)
    (hperm : I.perm = true) :
    ∃ k' C', RD (daiCtorCode chainIdWord) I g s0 ⟨77⟩
      [⟨1⟩, ⟨32⟩, ⟨64⟩, chainIdWord]
      (daiCtorWardsHashMem I chainIdWord) (UInt256.ofNat 5) rdata
      (createdAccounts, sstoreAccountMap I.codeOwner σ (daiCtorWardsSlot I) ⟨1⟩) k' C' := by
  have rdBeforeWardsStore := dai_ctor_run h with [
    raw mload 0 chainIdWord (UInt256.ofNat 5)
      (by dai_ctor_decode) mem_cost (daiCtorArgFreeMem_mload128 chainIdWord) (by decide)
      (by evm_ov),
    caller, push1 ⟨0⟩, swap1, dup2,
    raw mstore 0 (wordAt0Mem (daiCtorSourceWord I) (daiCtorArgFreeMem chainIdWord))
      (UInt256.ofNat 5) (by dai_ctor_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨32⟩, dup2, dup2,
    raw mstore 0 (daiCtorWardsHashMem I chainIdWord) (UInt256.ofNat 5)
      (by dai_ctor_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨64⟩, swap2, dup3, swap1,
    raw keccak256 0 (daiCtorWardsSlot I) (UInt256.ofNat 5)
      (by dai_ctor_decode) mem_cost (daiCtorWardsKeccakSlot I chainIdWord)
      (by decide) (by evm_ov),
    push1 ⟨1⟩, swap1, dup2, swap1]
  obtain ⟨_, _, rdAfterWardsStore⟩ :=
    rdBeforeWardsStore.sstore hperm (by dai_ctor_decode) (by evm_ov)
  exact ⟨_, _, rdAfterWardsStore⟩

theorem daiInitcodeAfterWardsStore
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (chainIdWord : UInt256)
    (hcode : I.code = daiCtorCode chainIdWord)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD (daiCtorCode chainIdWord) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨77⟩
      [⟨1⟩, ⟨32⟩, ⟨64⟩, chainIdWord]
      (daiCtorWardsHashMem I chainIdWord) (UInt256.ofNat 5) ByteArray.empty
      (createdAccounts, sstoreAccountMap I.codeOwner σ (daiCtorWardsSlot I) ⟨1⟩) k C := by
  obtain ⟨_, _, rd53⟩ :=
    daiInitcodePrologueSuccess
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      chainIdWord hcode hwv
  exact daiCtorWardsStoreTrace
    (createdAccounts := createdAccounts) (σ := σ) (I := I) chainIdWord rd53 hperm

set_option maxHeartbeats 1500000 in
theorem daiCtorDomainWordsTrace
    {I : ExecutionEnv}
    {g : Sat256}
    {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (chainIdWord : UInt256)
    (h : RD (daiCtorCode chainIdWord) I g s0 ⟨77⟩
      [⟨1⟩, ⟨32⟩, ⟨64⟩, chainIdWord]
      (daiCtorWardsHashMem I chainIdWord) (UInt256.ofNat 5) rdata acc k C) :
    ∃ k' C', RD (daiCtorCode chainIdWord) I g s0 ⟨261⟩
      [⟨160⟩, ⟨32⟩, ⟨64⟩, ⟨288⟩]
      (daiCtorDomainWordsMem I chainIdWord) (UInt256.ofNat 15) rdata acc k' C' := by
  have rdNameLen := dai_ctor_run h with [
    dup3,
    raw mload 0 ⟨160⟩ (UInt256.ofNat 5)
      (by dai_ctor_decode) mem_cost (daiCtorWardsHashMem_mload64 I chainIdWord)
      (by decide) (by evm_ov),
    dup1, dup5, add, dup5,
    raw mstore 0 (daiCtorDomainNameFreeMem I chainIdWord) (UInt256.ofNat 5)
      (by dai_ctor_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨14⟩, dup2,
    raw mstore 3 (daiCtorDomainNameLenMem I chainIdWord) (UInt256.ofNat 6)
      (by dai_ctor_decode) mem_cost rfl (by decide) (by evm_ov)]
  have rdNameRaw := rdNameLen.pushConst
    (⟨693460759908978978078209758180535⟩ : UInt256)
    (width := 14) (op := .PUSH14)
    (by native_decide) (by dai_ctor_decode) (by evm_ov)
  have rdPreHash := dai_ctor_run rdNameRaw with [
    push1 ⟨145⟩, shl, swap1, dup4, add,
    raw mstore 3 (daiCtorDomainNameMem I chainIdWord) (UInt256.ofNat 7)
      (by dai_ctor_decode) mem_cost rfl (by decide) (by evm_ov),
    dup3,
    raw mload 0 ⟨224⟩ (UInt256.ofNat 7)
      (by dai_ctor_decode) mem_cost (daiCtorDomainNameMem_mload64 I chainIdWord)
      (by decide) (by evm_ov),
    dup1, dup5, add, dup5,
    raw mstore 0 (daiCtorDomainPreFreeMem I chainIdWord) (UInt256.ofNat 7)
      (by dai_ctor_decode) mem_cost rfl (by decide) (by evm_ov),
    swap1, dup2,
    raw mstore 3 (daiCtorDomainVersionLenMem I chainIdWord) (UInt256.ofNat 8)
      (by dai_ctor_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨49⟩, push1 ⟨248⟩, shl, swap1, dup3, add,
    raw mstore 3 (daiCtorDomainPreMem I chainIdWord) (UInt256.ofNat 9)
      (by dai_ctor_decode) mem_cost rfl (by decide) (by evm_ov),
    dup2,
    raw mload 0 ⟨288⟩ (UInt256.ofNat 9)
      (by dai_ctor_decode) mem_cost (daiCtorDomainPreMem_mload64 I chainIdWord)
      (by decide) (by evm_ov)]
  have rdTypeHash := rdPreHash.pushConst daiCtorTypeHashWord
    (width := 32) (op := .PUSH32)
    (by native_decide) (by dai_ctor_decode) (by evm_ov)
  have rdTypeMem := dai_ctor_run rdTypeHash with [
    dup2, dup4, add,
    raw mstore 6 (daiCtorDomainTypeMem I chainIdWord) (UInt256.ofNat 11)
      (by dai_ctor_decode) mem_cost rfl (by decide) (by evm_ov)]
  have rdNameHash := rdTypeMem.pushConst daiCtorNameHashWord
    (width := 32) (op := .PUSH32)
    (by native_decide) (by dai_ctor_decode) (by evm_ov)
  have rdNameHashMem := dai_ctor_run rdNameHash with [
    dup2, dup5, add,
    raw mstore 3 (daiCtorDomainNameHashMem I chainIdWord) (UInt256.ofNat 12)
      (by dai_ctor_decode) mem_cost rfl (by decide) (by evm_ov)]
  have rdVersionHash := rdNameHashMem.pushConst daiCtorVersionHashWord
    (width := 32) (op := .PUSH32)
    (by native_decide) (by dai_ctor_decode) (by evm_ov)
  have rd := dai_ctor_run rdVersionHash with [
    push1 ⟨96⟩, dup3, add,
    raw mstore 3 (daiCtorDomainVersionHashMem I chainIdWord) (UInt256.ofNat 13)
      (by dai_ctor_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨128⟩, dup2, add, swap4, swap1, swap4,
    raw mstore 3 (daiCtorDomainChainMem I chainIdWord) (UInt256.ofNat 14)
      (by dai_ctor_decode) mem_cost rfl (by decide) (by evm_ov),
    address, push1 ⟨160⟩, dup1, dup6, add, swap2, swap1, swap2,
    raw mstore 3 (daiCtorDomainWordsMem I chainIdWord) (UInt256.ofNat 15)
      (by dai_ctor_decode) mem_cost rfl (by decide) (by evm_ov)]
  exact ⟨_, _, rd⟩

set_option maxHeartbeats 1500000 in
theorem daiCtorDomainHashTrace
    {I : ExecutionEnv}
    {g : Sat256}
    {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (chainIdWord : UInt256)
    (h : RD (daiCtorCode chainIdWord) I g s0 ⟨261⟩
      [⟨160⟩, ⟨32⟩, ⟨64⟩, ⟨288⟩]
      (daiCtorDomainWordsMem I chainIdWord) (UInt256.ofNat 15) rdata acc k C) :
    ∃ k' C', RD (daiCtorCode chainIdWord) I g s0 ⟨284⟩
      [daiCtorDomainWord chainIdWord (daiCtorThisWord I)]
      (daiCtorDomainHashMem I chainIdWord) (UInt256.ofNat 15) rdata acc k' C' := by
  have rd := dai_ctor_run h with [
    dup3,
    raw mload 0 ⟨288⟩ (UInt256.ofNat 15)
      (by dai_ctor_decode) mem_cost (daiCtorDomainWordsMem_mload64 I chainIdWord)
      (by decide) (by evm_ov),
    dup1, dup6, sub, swap1, swap2, add, dup2,
    raw mstore 0 (daiCtorDomainLenMem I chainIdWord) (UInt256.ofNat 15)
      (by dai_ctor_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨192⟩, swap1, swap4, add, swap1, swap2,
    raw mstore 0 (daiCtorDomainHashMem I chainIdWord) (UInt256.ofNat 15)
      (by dai_ctor_decode) mem_cost rfl (by decide) (by evm_ov),
    dup2,
    raw mload 0 ⟨160⟩ (UInt256.ofNat 15)
      (by dai_ctor_decode) mem_cost (daiCtorDomainHashMem_mload288 I chainIdWord)
      (by decide) (by evm_ov),
    swap2, add,
    raw keccak256 0 (daiCtorDomainWord chainIdWord (daiCtorThisWord I)) (UInt256.ofNat 15)
      (by dai_ctor_decode) mem_cost (daiCtorDomainKeccakWord I chainIdWord)
      (by decide) (by evm_ov)]
  exact ⟨_, _, rd⟩

set_option maxHeartbeats 800000 in
theorem daiCtorReturnTrace
    {I : ExecutionEnv}
    {g : Sat256}
    {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (chainIdWord : UInt256)
    (h : RD (daiCtorCode chainIdWord) I g s0 ⟨287⟩ []
      (daiCtorDomainHashMem I chainIdWord) (UInt256.ofNat 15) rdata acc k C) :
    RDret (daiCtorCode chainIdWord) g s0 acc daiBytecode := by
  have rdBeforeReturn := dai_ctor_run h with [
    push2 ⟨4011⟩, dup1, push2 ⟨301⟩, push1 ⟨0⟩,
    raw codecopy 364 (daiCtorReturnMem I chainIdWord) (UInt256.ofNat 126)
      (by dai_ctor_decode)
      mem_cost
      rfl
      (by decide) (by evm_ov),
    push1 ⟨0⟩]
  exact rdBeforeReturn.ret 0 daiBytecode
    (by dai_ctor_decode)
    mem_cost
    (daiCtorReturnMem_read I chainIdWord)
    (by evm_ov)

theorem daiInitcodeSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (chainIdWord : UInt256)
    (hcode : I.code = daiCtorCode chainIdWord)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) :
    RDret (daiCtorCode chainIdWord) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      (createdAccounts,
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ (daiCtorWardsSlot I) ⟨1⟩)
          daiCtorDomainSlot
          (daiCtorDomainWord chainIdWord (daiCtorThisWord I)))
      daiBytecode := by
  obtain ⟨_, _, rdAfterWardsStore⟩ :=
    daiInitcodeAfterWardsStore
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      chainIdWord hcode hperm hwv
  obtain ⟨_, _, rdDomainWords⟩ :=
    daiCtorDomainWordsTrace (I := I) chainIdWord rdAfterWardsStore
  obtain ⟨_, _, rdDomainHash⟩ :=
    daiCtorDomainHashTrace (I := I) chainIdWord rdDomainWords
  have rdBeforeDomainStore := dai_ctor_run rdDomainHash with [push1 ⟨5⟩]
  obtain ⟨_, _, rdAfterDomainStore⟩ :=
    rdBeforeDomainStore.sstore hperm (by dai_ctor_decode) (by evm_ov)
  exact daiCtorReturnTrace (I := I) chainIdWord rdAfterDomainStore

theorem daiSolmCtorExecSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (chainId : Int)
    (h0 : 0 ≤ chainId)
    (hlt : chainId < Int.ofNat (EVM.twoPow 256))
    (hwv : I.weiValue = ⟨0⟩) :
    solmCtorExec config contract [.int chainId] createdAccounts genesisBlockHeader blocks
      σ σ₀ g A I
      (.returned (daiCtorFrame chainId)
        (daiCtorPostState
          (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
          I (EVM.word chainId.toNat))
        none) := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I)
    (argsStore := daiCtorLocals chainId)
    ?_ rfl ?_ ?_
  · rfl
  · simp [daiCtorLocals, contract, constructorDecl]
  · refine ExecFuncBody.execBlockOK ?_
    let evm0 := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (daiCtorWardsSlot I) ⟨1⟩
    refine ExecBlock.consNormal (solm' := daiCtorFrame chainId) (evm' := evm0)
      (ExecStmt.requireTrue (evalCallvalueEq_true (cfg := config)
        (solm := daiCtorFrame chainId) (evm := evm0)
        (by simpa [evm0, initState] using hwv))) ?_
    refine ExecBlock.consNormal (solm' := daiCtorFrame chainId) (evm' := evm1) ?_ ?_
    · exact ExecStmt.assign (value := .int 1)
        (by simp [evalExpr?, pure])
        (by
          unfold evm0
          exact daiCtorAssignWards
            (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
            I chainId (by simp [initState]))
    · refine ExecBlock.consNormal ?_ ExecBlock.nil
      exact ExecStmt.assign
        (value := .fixedBytes bytes32Width
          (daiCtorDomainBytes (EVM.word chainId.toNat) (daiCtorThisWord I)))
        (by
          unfold evm1 evm0
          simpa [daiCtorThisWord, storageStore_executionEnv, initState] using
            evalExpr_daiCtor_domain
            (Solm.EVM.storageStore
              (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
              I.codeOwner (daiCtorWardsSlot I) ⟨1⟩)
            chainId h0 hlt)
        (by
          unfold evm1 evm0 daiCtorPostState
          simpa [storageStore_executionEnv, initState] using
            daiCtorAssignDomain
              (Solm.EVM.storageStore
                (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
                I.codeOwner (daiCtorWardsSlot I) ⟨1⟩)
              I chainId (EVM.word chainId.toNat))

theorem daiConstructorCorrect :
    constructorEquivalence config daiCreationBytecode contract daiBytecode := by
  refine constructorEquivalence.intro ?_
  intro createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I
      args deployedInitcode hdeploy hcode _hcalldata hperm hσ
  rcases daiDeployment_shape hdeploy with ⟨chainId, hargs, h0, hlt, hdeployed⟩
  subst args
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hcodeCtor : I.code = daiCtorCode (EVM.word chainId.toNat) := by
      rw [hcode, hdeployed]
      unfold daiCtorCode
      rfl
    have hrd := daiInitcodeSuccess
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) (EVM.word chainId.toNat) hcodeCtor hperm hwv
    rcases hrd with hOOG | ⟨s, hX, hacc⟩
    · exact constructorEquivalenceFor.outOfGas
        (Xi_error_of_X (g := g) (by
          rw [← hcodeCtor] at hOOG
          simpa [Sat256.ofUInt256] using hOOG))
    · have hsuccess := Xi_success_of_X (g := g) (by
        rw [← hcodeCtor] at hX
        simpa [Sat256.ofUInt256] using hX)
      have hcA : s.createdAccounts = createdAccounts := congrArg Prod.fst hacc
      have hσ' : s.accountMap =
          sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σ_evm (daiCtorWardsSlot I) ⟨1⟩)
            daiCtorDomainSlot
            (daiCtorDomainWord (EVM.word chainId.toNat) (daiCtorThisWord I)) :=
        congrArg Prod.snd hacc
      rw [hcA, hσ'] at hsuccess
      refine constructorEquivalenceFor.execution hsuccess
        (daiSolmCtorExecSuccess
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (g := g) (A := A) (I := I)
          chainId h0 hlt hwv) ?_
      refine ctorResultEquiv.success rfl rfl ?_ ?_ rfl
      · simp only [daiCtorPostState, storageStore_createdAccounts, initState]
      · simp only [daiCtorPostState, storageStore_accountMap, storageStore_executionEnv, initState]
        exact accountMapEquiv_sstoreAccountMap_two I.codeOwner I.codeOwner
          (daiCtorWardsSlot I) ⟨1⟩ daiCtorDomainSlot
          (daiCtorDomainWord (EVM.word chainId.toNat) (daiCtorThisWord I)) hσ
  · let tail := (EVM.Word.toBytesBE (EVM.word chainId.toNat)).toByteArray
    have hcodeTail : I.code = daiCreationBytecode ++ tail := by
      rw [hcode, hdeployed]
    have hrd := daiInitcodeNonpayableRevert
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) tail hcodeTail hwv
    rcases hrd.xiResult hcodeTail with hOOG | ⟨g', o, hrev⟩
    · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
    · refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hrev)
        (daiSolmCtorExecReverts_nonpayable
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (g := g) (A := A) (I := I)
          chainId hwv) ?_
      exact ctorResultEquiv.revert rfl rfl

end Benchmarks.Dss.Dai
