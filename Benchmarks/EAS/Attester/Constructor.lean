import Benchmarks.EAS.Attester.Common
import Reasoning.Initcode
import Solm.Equiv

/-!
# EAS Attester constructor correctness stub

Parameterized over the constructor-set immutable `_eas`. The constructor returns runtime bytecode
with `_eas` patched into the template at the offsets recorded in `Immutables.lean`; the proof is
left as the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

noncomputable def attesterCtorTail (eas : EVM.Address) : ByteArray :=
  (EVM.Word.toBytesBE (EVM.Word.ofNat eas.toNat)).toByteArray

noncomputable def attesterCtorCode (eas : EVM.Address) : ByteArray :=
  attesterCreationBytecode ++ attesterCtorTail eas

def attesterCtorArgLocals (v : AttesterImmutables) (eas : EVM.Address) : Store :=
  Std.HashMap.ofList
    (List.zip ((contract v).ctor.params.map Param.name) [.address eas])

def attesterCtorFinalLocals (v : AttesterImmutables) (eas : EVM.Address) : Store :=
  (attesterCtorArgLocals v eas).insert "imm_eas" (.address eas)

theorem attesterCtorDeployment_shape {args : List Value} {deployedInitcode : ByteArray}
    (v : AttesterImmutables) :
    (config v).selfDeployment attesterCreationBytecode args = some deployedInitcode →
    ∃ eas : EVM.Address,
      args = [.address eas] ∧
      deployedInitcode = attesterCreationBytecode ++ attesterCtorTail eas := by
  intro h
  cases args with
  | nil =>
      simp [config, genSolidityConstructorDeployment, constructorDecl,
        encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, addr,
        staticABIEncodedSize?, isDynamicABIType] at h
  | cons arg rest =>
      cases rest with
      | cons _ _ =>
          cases arg <;>
            simp [config, genSolidityConstructorDeployment, constructorDecl,
              encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, addr,
              staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
      | nil =>
          cases arg with
          | address eas =>
              simp [config, genSolidityConstructorDeployment, constructorDecl,
                encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, addr,
                staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
              refine ⟨eas, rfl, ?_⟩
              simpa [attesterCtorTail] using h.symm
          | _ =>
              simp [config, genSolidityConstructorDeployment, constructorDecl,
                encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, addr,
                staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h

theorem attesterCtorArgLocals_get_eas (v : AttesterImmutables) (eas : EVM.Address) :
    (attesterCtorArgLocals v eas).get? "eas" = some (.address eas) := by
  grind [attesterCtorArgLocals, contract, constructorDecl]

theorem attesterCtorFinalLocals_get_eas (v : AttesterImmutables) (eas : EVM.Address) :
    (attesterCtorFinalLocals v eas).get? "eas" = some (.address eas) := by
  grind [attesterCtorFinalLocals, attesterCtorArgLocals, contract, constructorDecl]

theorem attesterCtorFinalLocals_get_imm_eas (v : AttesterImmutables) (eas : EVM.Address) :
    (attesterCtorFinalLocals v eas).get? "imm_eas" = some (.address eas) := by
  grind [attesterCtorFinalLocals, attesterCtorArgLocals, contract, constructorDecl]

theorem attesterCtorRuntimeCodeOf (v : AttesterImmutables) (eas : EVM.Address) :
    runtimeCodeOf attesterBytecode (attesterCtorFinalLocals v eas) =
      some (patchedRuntime { eas := eas }) := by
  unfold runtimeCodeOf patchesFrom offsets wordBytes?
  simp [List.foldrM]
  rw [show (attesterCtorFinalLocals v eas)["imm_eas"]? = some (.address eas) by
    exact attesterCtorFinalLocals_get_imm_eas v eas]
  simp [valueToWord]
  simpa [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord,
    List.lookup_cons] using
    (patchRuntime_eq_patchedRuntime (v := { eas := eas }))

theorem evalExpr_ctor_eas_ne_zero_true (v : AttesterImmutables) (evm : EVM.State)
    (eas : EVM.Address) (hne : eas ≠ .ofNat 0) :
    evalExpr? (config v) { contract := contract v, locals := attesterCtorArgLocals v eas } evm
      (.binary .ne (.var "eas") zeroAddr) = .ok (.bool true) := by
  simp only [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.ofOption,
    EvalResult.bind, bind, pure]
  rw [attesterCtorArgLocals_get_eas]
  simp [evalBinaryOp?, hne]

theorem evalExpr_ctor_eas_ne_zero_false (v : AttesterImmutables) (evm : EVM.State)
    (eas : EVM.Address) (heq : eas = .ofNat 0) :
    evalExpr? (config v) { contract := contract v, locals := attesterCtorArgLocals v eas } evm
      (.binary .ne (.var "eas") zeroAddr) = .ok (.bool false) := by
  simp only [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.ofOption,
    EvalResult.bind, bind, pure]
  rw [attesterCtorArgLocals_get_eas]
  simp [evalBinaryOp?, heq]

theorem attesterCtorBodyReturns (v : AttesterImmutables) (evm : EVM.State)
    (eas : EVM.Address) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hne : eas ≠ .ofNat 0) :
    ExecTransitionBody (config v) (contract v) evm
      (attesterCtorArgLocals v eas) (contract v).ctor.body
      (.returned
        { contract := contract v
          locals := attesterCtorFinalLocals v eas }
        evm none) := by
  simp only [contract, constructorDecl, nonpayable]
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_ctor_eas_ne_zero_true v evm eas hne)) ?_
  simpa [attesterCtorFinalLocals] using
    (ExecBlock.consNormal (ExecStmt.letDecl (value := .address eas) (by
      show evalExpr? (config v)
        { contract := contract v, locals := attesterCtorArgLocals v eas } evm
        (.var "eas") = .ok (.address eas)
      have hget : (attesterCtorArgLocals v eas).get? "eas" = some (.address eas) :=
        attesterCtorArgLocals_get_eas v eas
      simp only [evalExpr?, EvalResult.ofOption]
      rw [hget])) ExecBlock.nil)

theorem attesterCtorBodyReverts_zero (v : AttesterImmutables) (evm : EVM.State)
    (eas : EVM.Address) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (heq : eas = .ofNat 0) :
    ExecTransitionBody (config v) (contract v) evm
      (attesterCtorArgLocals v eas) (contract v).ctor.body .reverted := by
  simp only [contract, constructorDecl, nonpayable]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (evalExpr_ctor_eas_ne_zero_false v evm eas heq))

theorem attesterSolmCtorExecSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (v : AttesterImmutables) (eas : EVM.Address)
    (hwv : I.weiValue = ⟨0⟩) (hne : eas ≠ .ofNat 0) :
    solmCtorExec (config v) (contract v) [.address eas]
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      (.returned
        { contract := contract v
          locals := attesterCtorFinalLocals v eas }
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
        none) := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
    (argsStore := attesterCtorArgLocals v eas)
    ?_ rfl ?_ ?_
  · rfl
  · simp [attesterCtorArgLocals, contract, constructorDecl]
  · exact attesterCtorBodyReturns v _ eas (by simp [initState, hwv]) hne

theorem attesterSolmCtorExecReverts_zero
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (v : AttesterImmutables) (eas : EVM.Address)
    (hwv : I.weiValue = ⟨0⟩) (heq : eas = .ofNat 0) :
    solmCtorExec (config v) (contract v) [.address eas]
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I .reverted := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
    (argsStore := attesterCtorArgLocals v eas)
    ?_ rfl ?_ ?_
  · rfl
  · simp [attesterCtorArgLocals, contract, constructorDecl]
  · exact attesterCtorBodyReverts_zero v _ eas (by simp [initState, hwv]) heq

theorem attesterSolmCtorExecReverts_nonpayable
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (v : AttesterImmutables) (eas : EVM.Address)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    solmCtorExec (config v) (contract v) [.address eas]
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I .reverted := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
    (argsStore := attesterCtorArgLocals v eas)
    ?_ rfl ?_ ?_
  · rfl
  · simp [attesterCtorArgLocals, contract, constructorDecl]
  · simpa [contract, constructorDecl, nonpayable] using
      (bodyReverts_nonPayable (cfg := config v) (contract := contract v)
        (evm := initState createdAccounts genesisBlockHeader blocks σ σ₀
          (Sat256.ofUInt256 g) A I)
        (locals := attesterCtorArgLocals v eas)
        (rest :=
          [ .require (.binary .ne (.var "eas") zeroAddr),
            .letDecl "imm_eas" (some addr) (.var "eas") ])
        (by simp [initState, hwv]))

theorem attesterCtorCreation_decode_append (tail : ByteArray) (pc : UInt256)
    (hpc : pc.toNat + 33 ≤ attesterCreationBytecode.size) :
    decode (attesterCreationBytecode ++ tail) pc =
      decode attesterCreationBytecode pc :=
  Reasoning.Theory.decode_append_left_window attesterCreationBytecode tail pc hpc
    (by rw [attesterCreationBytecode_size]; norm_num)

macro "attester_ctor_decode" : tactic =>
  `(tactic|
    (first
      | rw [attesterCtorCreation_decode_append _ _ (by
          rw [attesterCreationBytecode_size]
          native_decide)]
      | (unfold attesterCtorCode; rw [attesterCtorCreation_decode_append _ _ (by
          rw [attesterCreationBytecode_size]
          native_decide)]);
     native_decide))

macro "attester_ctor_jd" : tactic =>
  `(tactic|
    (first
      | (apply Reasoning.Theory.D_J_contains_append_left; native_decide)
      | (unfold attesterCtorCode; apply Reasoning.Theory.D_J_contains_append_left; native_decide)))

open Lean in
macro "attester_ctor_run " base:term " with " "[" steps:evmStep,* "]" : term => do
  let mut acc := base
  for s in steps.getElems do
    match s with
    | `(evmStep| raw $op:ident $args*) =>
        acc ← `($(acc).$op $args*)
    | `(evmStep| $op:ident $args*) =>
        match op.getId with
        | `jump    => acc ← `($(acc).jump (by attester_ctor_decode) $(args[0]!) (by evm_ov))
        | `jumpiT  => acc ← `($(acc).jumpiT (by attester_ctor_decode) $(args[0]!) $(args[1]!)
                            (by evm_ov))
        | `jumpiNT => acc ← `($(acc).jumpiNT (by attester_ctor_decode) $(args[0]!) (by evm_ov))
        | _        => acc ← `($(acc).$op $args* (by attester_ctor_decode) (by evm_ov))
    | _ => Macro.throwUnsupported
  return acc

noncomputable def attesterCtorFreePtrMem : ByteArray :=
  writeWord ByteArray.empty 64 (⟨160⟩ : UInt256)

theorem write_from_gap_eq (src base : ByteArray) (srcAddr destAddr len : Nat)
    (hlen : len ≠ 0) (hsrc : srcAddr + len ≤ src.size) (hge : base.size ≤ destAddr)
    (_hgap : destAddr - base.size < USize.size) :
    src.write srcAddr base destAddr len =
      base ++ ffi.ByteArray.zeroes (destAddr - base.size) ++
        src.extract srcAddr (srcAddr + len) := by
  apply ByteArray.ext
  unfold ByteArray.write
  rw [if_neg hlen, if_neg (show ¬ srcAddr ≥ src.size from by omega)]
  have hcopy : min len (src.size - srcAddr) = len := by omega
  have htail : min base.size (destAddr + len) - (destAddr + len) = 0 := by omega
  simp only [hcopy, htail, ByteArray.data_copySlice, ByteArray.data_append,
    ByteArray.data_extract]
  have hpz : (ffi.ByteArray.zeroes (destAddr - base.size)).data.size =
      destAddr - base.size := by
    rw [show (ffi.ByteArray.zeroes (destAddr - base.size)).data.size =
          (ffi.ByteArray.zeroes (destAddr - base.size)).size from rfl,
      ByteArray_zeroes_size]
  have hDsz :
      (base.data ++
        (ffi.ByteArray.zeroes (destAddr - base.size)).data).size =
        destAddr := by
    rw [Array.size_append, hpz, show base.data.size = base.size from rfl]
    omega
  rw [show (ffi.ByteArray.zeroes 0).data = (#[] : Array UInt8) from by
    rw [zeroes_zero (n := 0) (by rfl)]
    rfl]
  simp only [Array.append_empty, Nat.add_zero]
  rw [show min len (src.data.size - srcAddr) = len by
    have : src.data.size = src.size := rfl
    omega]
  rw [Array.extract_eq_self_of_le (by rw [hDsz])]
  rw [show (base.data ++
        (ffi.ByteArray.zeroes (destAddr - base.size)).data).extract
          (destAddr + len) = (#[] : Array UInt8) from by
    apply Array.extract_eq_empty_of_le
    rw [hDsz]
    omega]
  simp [Array.append_assoc]

theorem write0_eq_extract_from_of_base_le (src base : ByteArray) (srcAddr len : Nat)
    (hlen : len ≠ 0) (hsrc : srcAddr + len ≤ src.size) (hbase : base.size ≤ len) :
    src.write srcAddr base 0 len = src.extract srcAddr (srcAddr + len) := by
  apply ByteArray.ext
  rw [write0_data_from src base srcAddr len hlen hsrc]
  rw [show base.data.extract len base.data.size = (#[] : Array UInt8) from by
    apply Array.extract_eq_empty_of_le
    rw [show base.data.size = base.size from rfl]
    simpa using hbase]
  simp

theorem attesterCtorTail_size (eas : EVM.Address) :
    (attesterCtorTail eas).size = 32 := by
  unfold attesterCtorTail
  rw [word_toBytesBE_toByteArray_size]

theorem attesterCtorCode_size (eas : EVM.Address) :
    (attesterCtorCode eas).size = 3403 := by
  rw [attesterCtorCode, ByteArray.size_append, attesterCreationBytecode_size,
    attesterCtorTail_size]

theorem attesterCtorCode_tail_window (eas : EVM.Address) :
    (attesterCtorCode eas).extract 3371 (3371 + 32) = attesterCtorTail eas := by
  unfold attesterCtorCode
  exact extract_append_right' attesterCreationBytecode (attesterCtorTail eas) 3371
    (3371 + 32) attesterCreationBytecode_size.symm
    (by rw [attesterCreationBytecode_size, attesterCtorTail_size])

theorem attesterCtorCreation_runtime_window :
    attesterCreationBytecode.extract 185 (185 + 3186) = attesterBytecode := by
  native_decide +revert

theorem attesterCtorCode_runtime_window (eas : EVM.Address) :
    (attesterCtorCode eas).extract 185 (185 + 3186) = attesterBytecode := by
  unfold attesterCtorCode
  rw [extract_append_left attesterCreationBytecode (attesterCtorTail eas) 185 (185 + 3186)
    (by rw [attesterCreationBytecode_size])]
  exact attesterCtorCreation_runtime_window

noncomputable def attesterCtorArgMem (eas : EVM.Address) : ByteArray :=
  attesterCtorFreePtrMem ++ ffi.ByteArray.zeroes 64 ++ attesterCtorTail eas

noncomputable def attesterCtorArgFreeMem (eas : EVM.Address) : ByteArray :=
  writeWord (attesterCtorArgMem eas) 64 (⟨192⟩ : UInt256)

theorem attesterCtorFreePtrMem_size : attesterCtorFreePtrMem.size = 96 := by
  unfold attesterCtorFreePtrMem
  rw [writeWord_size]
  · rfl
  · exact lt_usize _ (by norm_num)

theorem attesterCtorArgMem_size (eas : EVM.Address) :
    (attesterCtorArgMem eas).size = 192 := by
  unfold attesterCtorArgMem
  rw [ByteArray.size_append, ByteArray.size_append, attesterCtorFreePtrMem_size,
    ByteArray_zeroes_size, attesterCtorTail_size]

theorem attesterCtorArgFreeMem_size (eas : EVM.Address) :
    (attesterCtorArgFreeMem eas).size = 192 := by
  unfold attesterCtorArgFreeMem
  rw [writeWord_size]
  · rw [attesterCtorArgMem_size]
    rfl
  · rw [attesterCtorArgMem_size]
    exact lt_usize _ (by norm_num)

theorem attesterCtorFreePtrMem_mload64 :
    (if (⟨64⟩ : UInt256).toNat ≥ attesterCtorFreePtrMem.size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (attesterCtorFreePtrMem.readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) = ⟨160⟩ := by
  apply mloadWordValue_of_readWithPadding
  · rw [attesterCtorFreePtrMem_size]
    decide
  · decide
  · change attesterCtorFreePtrMem.readWithPadding 64 32 =
      UInt256.toByteArray (⟨160⟩ : UInt256)
    unfold attesterCtorFreePtrMem
    exact writeWord_read_back ByteArray.empty 64 (⟨160⟩ : UInt256)
      (by exact lt_usize _ (by norm_num))

theorem attesterCtorArg_codecopy_mem (eas : EVM.Address) :
    (attesterCtorCode eas).write 3371 attesterCtorFreePtrMem 160 32 =
      attesterCtorArgMem eas := by
  unfold attesterCtorArgMem
  rw [write_from_gap_eq]
  · rw [attesterCtorFreePtrMem_size]
    rw [show 160 - 96 = 64 by norm_num]
    rw [attesterCtorCode_tail_window]
  · norm_num
  · rw [attesterCtorCode_size]
  · rw [attesterCtorFreePtrMem_size]
    norm_num
  · rw [attesterCtorFreePtrMem_size]
    exact lt_usize _ (by norm_num)

theorem attesterCtorArgMem_read160 (eas : EVM.Address) :
    (attesterCtorArgMem eas).readWithPadding 160 32 =
      UInt256.toByteArray (EVM.Word.ofNat eas.toNat) := by
  rw [readWithPadding_eq_extract' _ 160 32 (by norm_num) (by norm_num)
    (by rw [attesterCtorArgMem_size])]
  unfold attesterCtorArgMem attesterCtorTail
  set preBuf := attesterCtorFreePtrMem ++ ffi.ByteArray.zeroes 64
  have hpreBuf : preBuf.size = 160 := by
    unfold preBuf
    rw [ByteArray.size_append, attesterCtorFreePtrMem_size, ByteArray_zeroes_size]
  rw [extract_append_right_window preBuf
    (EVM.Word.toBytesBE (EVM.Word.ofNat eas.toNat)).toByteArray 160 (160 + 32)
    (by rw [hpreBuf]), hpreBuf]
  norm_num
  have hself :=
    byteArray_extract_self (EVM.Word.toBytesBE (EVM.Word.ofNat eas.toNat)).toByteArray
  simpa [word_toBytesBE_toByteArray_eq_toByteArray] using hself

theorem attesterCtorArgFreeMem_read160 (eas : EVM.Address) :
    (attesterCtorArgFreeMem eas).readWithPadding 160 32 =
      UInt256.toByteArray (EVM.Word.ofNat eas.toNat) := by
  unfold attesterCtorArgFreeMem
  rw [writeWord_read_preserved]
  · exact attesterCtorArgMem_read160 eas
  · rw [attesterCtorArgMem_size]
    exact lt_usize _ (by norm_num)
  · right
    constructor
    · norm_num
    · rw [attesterCtorArgMem_size]

theorem attesterCtorArgFreeMem_mload64 (eas : EVM.Address) :
    (if (⟨64⟩ : UInt256).toNat ≥ (attesterCtorArgFreeMem eas).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((attesterCtorArgFreeMem eas).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨192⟩ := by
  apply mloadWordValue_of_readWithPadding
  · rw [attesterCtorArgFreeMem_size]
    decide
  · decide
  · change (attesterCtorArgFreeMem eas).readWithPadding 64 32 =
      UInt256.toByteArray (⟨192⟩ : UInt256)
    unfold attesterCtorArgFreeMem
    rw [writeWord_read_back]
    rw [attesterCtorArgMem_size]
    exact lt_usize _ (by norm_num)

theorem attesterCtorArgFreeMem_mload160 (eas : EVM.Address) :
    (if (⟨160⟩ : UInt256).toNat ≥ (attesterCtorArgFreeMem eas).size
        ∨ (⟨160⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((attesterCtorArgFreeMem eas).readWithPadding (⟨160⟩ : UInt256).toNat 32)))
      = EVM.Word.ofNat eas.toNat := by
  apply mloadWordValue_of_readWithPadding
  · rw [attesterCtorArgFreeMem_size]
    decide
  · decide
  · simpa [show (⟨160⟩ : UInt256).toNat = 160 from by decide] using
      attesterCtorArgFreeMem_read160 eas

noncomputable def attesterCtorDecodedMem (eas : EVM.Address) : ByteArray :=
  writeWord (attesterCtorArgFreeMem eas) 128 (EVM.Word.ofNat eas.toNat)

noncomputable def attesterCtorPatchedRuntime (eas : EVM.Address) : ByteArray :=
  writeCascade attesterBytecode
    [ (722, EVM.Word.ofNat eas.toNat), (1465, EVM.Word.ofNat eas.toNat),
      (1598, EVM.Word.ofNat eas.toNat), (1939, EVM.Word.ofNat eas.toNat) ]

noncomputable def attesterCtorInvalidEASMem (eas : EVM.Address) : ByteArray :=
  writeWord (attesterCtorArgFreeMem eas) 192
    (UInt256.shiftLeft (⟨1102841855⟩ : UInt256) ⟨225⟩)

theorem attesterCtorDecodedMem_size (eas : EVM.Address) :
    (attesterCtorDecodedMem eas).size = 192 := by
  unfold attesterCtorDecodedMem
  rw [writeWord_size]
  · rw [attesterCtorArgFreeMem_size]
    rfl
  · rw [attesterCtorArgFreeMem_size]
    exact lt_usize _ (by norm_num)

theorem attesterCtorDecodedMem_read128 (eas : EVM.Address) :
    (attesterCtorDecodedMem eas).readWithPadding 128 32 =
      UInt256.toByteArray (EVM.Word.ofNat eas.toNat) := by
  unfold attesterCtorDecodedMem
  rw [writeWord_read_back]
  rw [attesterCtorArgFreeMem_size]
  exact lt_usize _ (by norm_num)

theorem attesterCtorDecodedMem_mload128 (eas : EVM.Address) :
    (if (⟨128⟩ : UInt256).toNat ≥ (attesterCtorDecodedMem eas).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((attesterCtorDecodedMem eas).readWithPadding (⟨128⟩ : UInt256).toNat 32)))
      = EVM.Word.ofNat eas.toNat := by
  apply mloadWordValue_of_readWithPadding
  · rw [attesterCtorDecodedMem_size]
    decide
  · decide
  · simpa [show (⟨128⟩ : UInt256).toNat = 128 from by decide] using
      attesterCtorDecodedMem_read128 eas

theorem attesterCtorInvalidEASMem_size (eas : EVM.Address) :
    (attesterCtorInvalidEASMem eas).size = 224 := by
  unfold attesterCtorInvalidEASMem
  rw [writeWord_size]
  · rw [attesterCtorArgFreeMem_size]
    rfl
  · rw [attesterCtorArgFreeMem_size]
    exact lt_usize _ (by norm_num)

theorem attesterCtorInvalidEASMem_read64 (eas : EVM.Address) :
    (attesterCtorInvalidEASMem eas).readWithPadding 64 32 =
      UInt256.toByteArray (⟨192⟩ : UInt256) := by
  unfold attesterCtorInvalidEASMem
  rw [writeWord_read_preserved]
  · unfold attesterCtorArgFreeMem
    rw [writeWord_read_back]
    rw [attesterCtorArgMem_size]
    exact lt_usize _ (by norm_num)
  · rw [attesterCtorArgFreeMem_size]
    exact lt_usize _ (by norm_num)
  · left
    constructor
    · norm_num
    · rw [attesterCtorArgFreeMem_size]
      norm_num

theorem attesterCtorInvalidEASMem_mload64 (eas : EVM.Address) :
    (if (⟨64⟩ : UInt256).toNat ≥ (attesterCtorInvalidEASMem eas).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((attesterCtorInvalidEASMem eas).readWithPadding
            (⟨64⟩ : UInt256).toNat 32)))
      = ⟨192⟩ := by
  apply mloadWordValue_of_readWithPadding
  · rw [attesterCtorInvalidEASMem_size]
    decide
  · decide
  · simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
      attesterCtorInvalidEASMem_read64 eas

theorem attesterCtorRuntime_codecopy_mem (eas : EVM.Address) :
    (attesterCtorCode eas).write 185 (attesterCtorDecodedMem eas) 0 3186 =
      attesterBytecode := by
  rw [write0_eq_extract_from_of_base_le]
  · exact attesterCtorCode_runtime_window eas
  · norm_num
  · rw [attesterCtorCode_size]
    norm_num
  · rw [attesterCtorDecodedMem_size]
    norm_num

theorem attesterCtorPatchedRuntime_eq_patchedRuntime (eas : EVM.Address) :
    attesterCtorPatchedRuntime eas = patchedRuntime { eas := eas } := by
  unfold attesterCtorPatchedRuntime patchedRuntime runtimeWrites
  rfl

theorem attesterCtorPatchedRuntime_size (eas : EVM.Address) :
    (attesterCtorPatchedRuntime eas).size = 3186 := by
  unfold attesterCtorPatchedRuntime
  exact writeCascade_size_of_base attesterBytecode
    [ (722, EVM.Word.ofNat eas.toNat), (1465, EVM.Word.ofNat eas.toNat),
      (1598, EVM.Word.ofNat eas.toNat), (1939, EVM.Word.ofNat eas.toNat) ]
    (base := 3186) (out := 3186)
    (by native_decide) (by simp [WriteGapsOk]) (by simp [writeCascadeSize])

theorem attesterCtorPatchedRuntime_read (eas : EVM.Address) :
    (attesterCtorPatchedRuntime eas).readWithPadding 0 3186 =
      patchedRuntime { eas := eas } := by
  rw [readWithPadding_eq_extract' _ 0 3186 (by norm_num) (by norm_num)
    (by rw [attesterCtorPatchedRuntime_size])]
  rw [show 3186 = (attesterCtorPatchedRuntime eas).size by
    rw [attesterCtorPatchedRuntime_size]]
  have hself := byteArray_extract_self (attesterCtorPatchedRuntime eas)
  simpa [attesterCtorPatchedRuntime_eq_patchedRuntime, Nat.zero_add] using hself

theorem attesterEasWord_canonical (eas : EVM.Address) :
    (EVM.Word.ofNat eas.toNat).toNat < EVM.addressModulus := by
  change (UInt256.ofNat eas.val).toNat < EVM.addressModulus
  rw [UInt256.toNat_ofNat_of_lt]
  · change eas.val < AccountAddress.size
    exact eas.isLt
  · exact lt_of_lt_of_le eas.isLt (by decide)

theorem attesterEasWord_toNat (eas : EVM.Address) :
    (EVM.Word.ofNat eas.toNat).toNat = eas.toNat := by
  change (UInt256.ofNat eas.val).toNat = eas.val
  rw [UInt256.toNat_ofNat_of_lt]
  exact lt_of_lt_of_le eas.isLt (by decide)

theorem attesterEasWord_clean (eas : EVM.Address) :
    UInt256.land (EVM.Word.ofNat eas.toNat) solcAddrMask =
      EVM.Word.ofNat eas.toNat :=
  solcAddrMask_clean (attesterEasWord_canonical eas)

theorem attesterEasWord_ne_zero (eas : EVM.Address) (hne : eas ≠ .ofNat 0) :
    EVM.Word.ofNat eas.toNat ≠ (⟨0⟩ : UInt256) := by
  intro hzero
  apply hne
  apply Fin.ext
  have hto := congrArg UInt256.toNat hzero
  rw [attesterEasWord_toNat eas] at hto
  simpa [AccountAddress.ofNat] using hto

theorem attesterEasWord_zero (eas : EVM.Address) (heq : eas = .ofNat 0) :
    EVM.Word.ofNat eas.toNat = (⟨0⟩ : UInt256) := by
  subst eas
  change UInt256.ofNat (Fin.ofNat AccountAddress.size 0).val = (⟨0⟩ : UInt256)
  native_decide

theorem attesterCtorInitcodeToBody
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (eas : EVM.Address)
    (hcode : I.code = attesterCtorCode eas)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD (attesterCtorCode eas) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨43⟩
      [EVM.Word.ofNat eas.toNat]
      (attesterCtorArgFreeMem eas) (UInt256.ofNat 6)
      ByteArray.empty (createdAccounts, σ) k C := by
  have rd0 :
      RD (attesterCtorCode eas) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨0⟩ []
        ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (createdAccounts, σ) 0 0 :=
    RD.initState hcode
  have rd97 := attester_ctor_run rd0 with [
    push1 ⟨160⟩, push1 ⟨64⟩,
    raw mstore 9 attesterCtorFreePtrMem (UInt256.ofNat 3) (by attester_ctor_decode)
      mem_cost
      (by
        unfold attesterCtorFreePtrMem Reasoning.Theory.writeWord
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide])
      (by decide) (by evm_ov),
    callvalue, dup1, iszero, push1 ⟨14⟩,
    jumpiT (by rw [hwv]; decide) (by attester_ctor_jd),
    jumpdest, pop, push1 ⟨64⟩,
    raw mload 0 ⟨160⟩ (UInt256.ofNat 3) (by attester_ctor_decode)
      mem_cost attesterCtorFreePtrMem_mload64 (by decide) (by evm_ov),
    push2 ⟨3371⟩, codesize, sub, dup1, push2 ⟨3371⟩, dup4,
    raw codecopy 9 (attesterCtorArgMem eas) (UInt256.ofNat 6)
      (by attester_ctor_decode)
      (fun s haws hstks => by
        set_option linter.unusedSimpArgs false in
          simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
            List.getElem!_cons_zero, List.getElem!_cons_succ]
        rw [attesterCtorCode_size]
        decide)
      (by
        rw [show ((UInt256.ofNat (attesterCtorCode eas).size).sub
            (⟨3371⟩ : UInt256)).toNat = 32 by
          rw [attesterCtorCode_size]
          decide]
        exact attesterCtorArg_codecopy_mem eas)
      (by
        rw [attesterCtorCode_size]
        decide)
      (by evm_ov),
    dup2, add, push1 ⟨64⟩, dup2, swap1,
    raw mstore 0 (attesterCtorArgFreeMem eas) (UInt256.ofNat 6)
      (by attester_ctor_decode) mem_cost
      (by
        rw [show (⟨160⟩ : UInt256) +
            (UInt256.ofNat (attesterCtorCode eas).size).sub ⟨3371⟩ =
            (⟨192⟩ : UInt256) by
          rw [attesterCtorCode_size]
          decide]
        unfold attesterCtorArgFreeMem Reasoning.Theory.writeWord
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide])
      (by decide) (by evm_ov),
    push1 ⟨43⟩, swap2, push1 ⟨97⟩, jump (by attester_ctor_jd)]
  have rd43 := attester_ctor_run rd97 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero,
    push1 ⟨112⟩,
    jumpiT (by
      rw [show (⟨160⟩ : UInt256) +
          (UInt256.ofNat (attesterCtorCode eas).size).sub ⟨3371⟩ =
          (⟨192⟩ : UInt256) by
        rw [attesterCtorCode_size]
        decide]
      decide) (by attester_ctor_jd),
    jumpdest, dup2,
    raw mload 0 (EVM.Word.ofNat eas.toNat) (UInt256.ofNat 6) (by attester_ctor_decode)
      mem_cost (attesterCtorArgFreeMem_mload160 eas) (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and, dup2, eq,
    push1 ⟨133⟩,
    jumpiT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask by decide]
      rw [attesterEasWord_clean eas]
      rw [uInt256_eq_self]
      decide) (by attester_ctor_jd),
    jumpdest, swap4, swap3, pop, pop, pop, jump (by attester_ctor_jd)]
  exact ⟨_, _, rd43⟩

theorem attesterCtorInitcodeSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (eas : EVM.Address)
    (hcode : I.code = attesterCtorCode eas)
    (hwv : I.weiValue = ⟨0⟩) (hne : eas ≠ .ofNat 0) :
    RDret (attesterCtorCode eas) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) (createdAccounts, σ)
      (patchedRuntime { eas := eas }) := by
  obtain ⟨_, _, rd43⟩ := attesterCtorInitcodeToBody
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    eas hcode hwv
  have rd140 := attester_ctor_run rd43 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and,
    push1 ⟨81⟩,
    jumpiT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask by decide]
      rw [attesterEasWord_clean eas]
      exact attesterEasWord_ne_zero eas hne) (by attester_ctor_jd),
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and,
    push1 ⟨128⟩,
    raw mstore 0 (attesterCtorDecodedMem eas) (UInt256.ofNat 6)
      (by attester_ctor_decode) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
            solcAddrMask by decide]
        rw [solcAddrMask_clean_left (attesterEasWord_canonical eas)]
        unfold attesterCtorDecodedMem Reasoning.Theory.writeWord
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide])
      (by decide) (by evm_ov),
    push1 ⟨140⟩, jump (by attester_ctor_jd)]
  exact attester_ctor_run rd140 with [
    jumpdest, push1 ⟨128⟩,
    raw mload 0 (EVM.Word.ofNat eas.toNat) (UInt256.ofNat 6)
      (by attester_ctor_decode) mem_cost (attesterCtorDecodedMem_mload128 eas)
      (by decide) (by evm_ov),
    push2 ⟨3186⟩, push2 ⟨185⟩, push0,
    raw codecopy 301 attesterBytecode (UInt256.ofNat 100)
      (by attester_ctor_decode) mem_cost (attesterCtorRuntime_codecopy_mem eas)
      (by decide) (by evm_ov),
    push0, dup2, dup2, push2 ⟨722⟩, add,
    raw mstore 0 (writeWord attesterBytecode 722 (EVM.Word.ofNat eas.toNat))
      (UInt256.ofNat 100)
      (by attester_ctor_decode) mem_cost
      (by
        unfold Reasoning.Theory.writeWord
        rw [show ((⟨722⟩ : UInt256) + ⟨0⟩).toNat = 722 from by decide])
      (by decide) (by evm_ov),
    dup2, dup2, push2 ⟨1465⟩, add,
    raw mstore 0
      (writeWord (writeWord attesterBytecode 722 (EVM.Word.ofNat eas.toNat)) 1465
        (EVM.Word.ofNat eas.toNat))
      (UInt256.ofNat 100)
      (by attester_ctor_decode) mem_cost
      (by
        unfold Reasoning.Theory.writeWord
        rw [show ((⟨1465⟩ : UInt256) + ⟨0⟩).toNat = 1465 from by decide])
      (by decide) (by evm_ov),
    dup2, dup2, push2 ⟨1598⟩, add,
    raw mstore 0
      (writeWord
        (writeWord (writeWord attesterBytecode 722 (EVM.Word.ofNat eas.toNat)) 1465
          (EVM.Word.ofNat eas.toNat)) 1598 (EVM.Word.ofNat eas.toNat))
      (UInt256.ofNat 100)
      (by attester_ctor_decode) mem_cost
      (by
        unfold Reasoning.Theory.writeWord
        rw [show ((⟨1598⟩ : UInt256) + ⟨0⟩).toNat = 1598 from by decide])
      (by decide) (by evm_ov),
    push2 ⟨1939⟩, add,
    raw mstore 0 (attesterCtorPatchedRuntime eas) (UInt256.ofNat 100)
      (by attester_ctor_decode) mem_cost
      (by
        simp [attesterCtorPatchedRuntime, Reasoning.Theory.writeCascade,
          Reasoning.Theory.writeWord,
          show ((⟨1939⟩ : UInt256) + ⟨0⟩).toNat = 1939 from by decide])
      (by decide) (by evm_ov),
    push2 ⟨3186⟩, push0,
    raw ret 0 (patchedRuntime { eas := eas })
      (by attester_ctor_decode) mem_cost (attesterCtorPatchedRuntime_read eas) (by evm_ov)]

theorem attesterCtorInitcodeZeroRevert
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (eas : EVM.Address)
    (hcode : I.code = attesterCtorCode eas)
    (hwv : I.weiValue = ⟨0⟩) (heq : eas = .ofNat 0) :
    RDrev (attesterCtorCode eas) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  obtain ⟨_, _, rd43⟩ := attesterCtorInitcodeToBody
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    eas hcode hwv
  have rd57 := attester_ctor_run rd43 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and,
    push1 ⟨81⟩,
    jumpiNT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask by decide]
      rw [attesterEasWord_clean eas]
      rw [attesterEasWord_zero eas heq])]
  exact attester_ctor_run rd57 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨192⟩ (UInt256.ofNat 6)
      (by attester_ctor_decode) mem_cost (attesterCtorArgFreeMem_mload64 eas)
      (by decide) (by evm_ov),
    push4 ⟨1102841855⟩, push1 ⟨225⟩, shl, dup2,
    raw mstore 3 (attesterCtorInvalidEASMem eas) (UInt256.ofNat 7)
      (by attester_ctor_decode) mem_cost
      (by
        unfold attesterCtorInvalidEASMem Reasoning.Theory.writeWord
        rw [show (⟨192⟩ : UInt256).toNat = 192 from by decide])
      (by decide) (by evm_ov),
    push1 ⟨4⟩, add, push1 ⟨64⟩,
    raw mload 0 ⟨192⟩ (UInt256.ofNat 7)
      (by attester_ctor_decode) mem_cost (attesterCtorInvalidEASMem_mload64 eas)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw rev 0 (by attester_ctor_decode) mem_cost (by evm_ov)]

theorem attesterCtorInitcodeNonpayableRevert
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (tail : ByteArray)
    (hcode : I.code = attesterCreationBytecode ++ tail)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev (attesterCreationBytecode ++ tail) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  have rd0 :
      RD (attesterCreationBytecode ++ tail) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨0⟩ []
        ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (createdAccounts, σ) 0 0 :=
    RD.initState hcode
  have rd11 := attester_ctor_run rd0 with [
    push1 ⟨160⟩, push1 ⟨64⟩,
    raw mstore 9 attesterCtorFreePtrMem (UInt256.ofNat 3)
      (by attester_ctor_decode)
      mem_cost
      (by
        unfold attesterCtorFreePtrMem Reasoning.Theory.writeWord
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide])
      (by decide) (by evm_ov),
    callvalue, dup1, iszero, push1 ⟨14⟩, jumpiNT (isZero_eq_zero_of_ne hwv)]
  exact rd11.push0 (by attester_ctor_decode) (by simp)
    |>.dup1 (by attester_ctor_decode) (by simp)
    |>.rev 0 (by attester_ctor_decode) (fun s _ hstks => memExpRevert0 s hstks) (by simp)

theorem attesterConstructorCorrect (v : AttesterImmutables) :
    constructorEquivalenceWith (config v) attesterCreationBytecode (contract v)
      (runtimeCodeOf attesterBytecode) := by
  refine constructorEquivalenceWith.intro ?_
  intro createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I
      args deployedInitcode hdeploy hcode _hcalldata _hperm hσ
  rcases attesterCtorDeployment_shape v hdeploy with ⟨eas, hargs, hdeployed⟩
  subst args
  rw [hdeployed] at hcode
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hzero : eas = .ofNat 0
    · have hcodeCtor : I.code = attesterCtorCode eas := by
        simpa [attesterCtorCode] using hcode
      have hrd := attesterCtorInitcodeZeroRevert
        (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) eas hcodeCtor hwv hzero
      rcases hrd.xiResult hcodeCtor with hOOG | ⟨g', o, hrev⟩
      · exact constructorEquivalenceForWith.outOfGas
          (by simpa [Sat256.ofUInt256] using hOOG)
      · refine constructorEquivalenceForWith.execution
          (by simpa [Sat256.ofUInt256] using hrev)
          (attesterSolmCtorExecReverts_zero
            (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
            (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (g := g) (A := A) (I := I)
            v eas hwv hzero) ?_
        exact ctorResultEquivWith.revert rfl rfl
    · have hcodeCtor : I.code = attesterCtorCode eas := by
        simpa [attesterCtorCode] using hcode
      have hrd := attesterCtorInitcodeSuccess
        (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) eas hcodeCtor hwv hzero
      rcases hrd.xiResult hcodeCtor with hOOG | ⟨g', A', hsuccess⟩
      · exact constructorEquivalenceForWith.outOfGas
          (by simpa [Sat256.ofUInt256] using hOOG)
      · refine constructorEquivalenceForWith.execution
          (by simpa [Sat256.ofUInt256] using hsuccess)
          (attesterSolmCtorExecSuccess
            (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
            (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (g := g) (A := A) (I := I)
            v eas hwv hzero) ?_
        refine ctorResultEquivWith.success rfl rfl ?_ ?_ ?_
        · rfl
        · simpa [initState] using hσ
        · exact attesterCtorRuntimeCodeOf v eas
  · have hrd := attesterCtorInitcodeNonpayableRevert
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g)
      (tail := attesterCtorTail eas) hcode hwv
    rcases hrd.xiResult hcode with hOOG | ⟨g', o, hrev⟩
    · exact constructorEquivalenceForWith.outOfGas
        (by simpa [Sat256.ofUInt256] using hOOG)
    · refine constructorEquivalenceForWith.execution
        (by simpa [Sat256.ofUInt256] using hrev)
        (attesterSolmCtorExecReverts_nonpayable
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (g := g) (A := A) (I := I)
          v eas hwv) ?_
      exact ctorResultEquivWith.revert rfl rfl

end Benchmarks.EAS.Attester
