import Examples.VyperERC20.Bytecode
import Examples.VyperERC20.Storage
import Examples.VyperERC20.TotalSupply
import Examples.VyperERC20.BalanceOf
import Examples.VyperERC20.Allowance
import Examples.VyperERC20.Approve
import Examples.VyperERC20.Transfer
import Examples.VyperERC20.TransferFromRuntime
import Solm.Equiv
import Reasoning.ABI
import Reasoning.Dispatch
import Reasoning.Stepping
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.Initcode
import Reasoning.Memory
import Reasoning.SolmBody
import Mathlib.Tactic.IntervalCases

/-!
# Vyper ERC20 — correctness entrypoints

This file wires the Vyper-compiled ERC20 artifact into the same equivalence statements used by the
Solidity ERC20 example.  The source-level behavior and ABI are the existing ERC20 Solm contract;
the storage layout and bytecode are Vyper-specific.

The constructor/initcode trace is proven below.  Runtime dispatch and function-body equivalence is
still the remaining Vyper bytecode proof obligation.
-/

open Solm
open ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option linter.unusedSimpArgs false

namespace VyperERC20

abbrev contract : ContractDecl :=
  erc20Contract

abbrev config : Config :=
  vyperERC20Config

/-! ## Constructor source side -/

def erc20CtorLocals (initialSupply : Int) : Store :=
  Std.HashMap.ofList
    (List.zip (erc20Contract.ctor.params.map Param.name) [.int initialSupply])

theorem erc20CtorLocals_get_initialSupply (initialSupply : Int) :
    (erc20CtorLocals initialSupply).get? "initialSupply" = some (.int initialSupply) := by
  unfold erc20CtorLocals
  simp [erc20Contract, ERC20.erc20Contract, ERC20.constructorDecl]

theorem erc20CtorLocals_get_balanceOf (initialSupply : Int) :
    (erc20CtorLocals initialSupply).get? "balanceOf" = none := by
  unfold erc20CtorLocals
  simp [erc20Contract, ERC20.erc20Contract, ERC20.constructorDecl]

theorem erc20CtorLocals_get_totalSupply (initialSupply : Int) :
    (erc20CtorLocals initialSupply).get? "totalSupply" = none := by
  unfold erc20CtorLocals
  simp [erc20Contract, ERC20.erc20Contract, ERC20.constructorDecl]

def erc20CtorBalancePostState (evm : EVM.State) (initialSupply : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (erc20BalanceOfSlot (.address evm.executionEnv.source)) initialSupply

def erc20CtorPostState (evm : EVM.State) (initialSupply : UInt256) : EVM.State :=
  Solm.EVM.storageStore (erc20CtorBalancePostState evm initialSupply)
    (erc20CtorBalancePostState evm initialSupply).executionEnv.codeOwner ⟨2⟩ initialSupply

theorem erc20Deployment_shape {args : List Value} {deployedInitcode : ByteArray} :
    config.selfDeployment vyperERC20Initcode args = some deployedInitcode →
    ∃ i : Int,
      args = [.int i]
        ∧ 0 ≤ i
        ∧ i < Int.ofNat (EVM.twoPow 256)
        ∧ deployedInitcode =
          vyperERC20Initcode ++ (EVM.Word.toBytesBE (EVM.word i.toNat)).toByteArray := by
  intro h
  cases args with
  | nil =>
      simp [config, vyperERC20Config, genSolidityConstructorDeployment, erc20Contract,
        ERC20.erc20Contract, ERC20.constructorDecl, encodeABIValues?, encodeABIValuesFrom?,
        abiTupleHeadSize?, uint256, uint256Int, ERC20.uint256, ERC20.uint256Int] at h
  | cons arg rest =>
      cases rest with
      | cons arg2 rest =>
          cases arg <;>
            simp [config, vyperERC20Config, genSolidityConstructorDeployment, erc20Contract,
              ERC20.erc20Contract, ERC20.constructorDecl, encodeABIValues?, encodeABIValuesFrom?,
              abiTupleHeadSize?, uint256, uint256Int, ERC20.uint256, ERC20.uint256Int,
              staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
      | nil =>
          cases arg with
          | int i =>
              by_cases hbounds : 0 ≤ i ∧ i < Int.ofNat (EVM.twoPow 256)
              · simp [config, vyperERC20Config, genSolidityConstructorDeployment, erc20Contract,
                  ERC20.erc20Contract, ERC20.constructorDecl, encodeABIValues?, encodeABIValuesFrom?,
                  abiTupleHeadSize?, uint256, uint256Int, ERC20.uint256, ERC20.uint256Int,
                  staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
                change (((if 0 ≤ i ∧ i < Int.ofNat (EVM.twoPow 256) then
                    some (EVM.word i.toNat) else none).bind
                    fun word => some word.toBytesBE).bind
                    fun args => some (vyperERC20Initcode ++ args.toByteArray)) =
                  some deployedInitcode at h
                split at h
                · simp at h
                  exact ⟨i, rfl, hbounds.1, hbounds.2, h.symm⟩
                · rename_i hnot
                  exact False.elim (hnot hbounds)
              · simp [config, vyperERC20Config, genSolidityConstructorDeployment, erc20Contract,
                  ERC20.erc20Contract, ERC20.constructorDecl, encodeABIValues?, encodeABIValuesFrom?,
                  abiTupleHeadSize?, uint256, uint256Int, ERC20.uint256, ERC20.uint256Int,
                  staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
                change (((if 0 ≤ i ∧ i < Int.ofNat (EVM.twoPow 256) then
                    some (EVM.word i.toNat) else none).bind
                    fun word => some word.toBytesBE).bind
                    fun args => some (vyperERC20Initcode ++ args.toByteArray)) =
                  some deployedInitcode at h
                split at h
                · rename_i hpos
                  exact False.elim (hbounds hpos)
                · simp at h
          | bool b =>
              simp [config, vyperERC20Config, genSolidityConstructorDeployment, erc20Contract,
                ERC20.erc20Contract, ERC20.constructorDecl, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                uint256, ERC20.uint256, ERC20.uint256Int, staticABIEncodedSize?,
                isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | address a =>
              simp [config, vyperERC20Config, genSolidityConstructorDeployment, erc20Contract,
                ERC20.erc20Contract, ERC20.constructorDecl, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                uint256, ERC20.uint256, ERC20.uint256Int, staticABIEncodedSize?,
                isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | array xs =>
              simp [config, vyperERC20Config, genSolidityConstructorDeployment, erc20Contract,
                ERC20.erc20Contract, ERC20.constructorDecl, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                uint256, ERC20.uint256, ERC20.uint256Int, staticABIEncodedSize?,
                isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | tuple xs =>
              simp [config, vyperERC20Config, genSolidityConstructorDeployment, erc20Contract,
                ERC20.erc20Contract, ERC20.constructorDecl, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                uint256, ERC20.uint256, ERC20.uint256Int, staticABIEncodedSize?,
                isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | fixedBytes n bs =>
              simp [config, vyperERC20Config, genSolidityConstructorDeployment, erc20Contract,
                ERC20.erc20Contract, ERC20.constructorDecl, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                uint256, ERC20.uint256, ERC20.uint256Int, staticABIEncodedSize?,
                isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | bytes =>
              simp [config, vyperERC20Config, genSolidityConstructorDeployment, erc20Contract,
                ERC20.erc20Contract, ERC20.constructorDecl, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                uint256, ERC20.uint256, ERC20.uint256Int, staticABIEncodedSize?,
                isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | struct name fields =>
              simp [config, vyperERC20Config, genSolidityConstructorDeployment, erc20Contract,
                ERC20.erc20Contract, ERC20.constructorDecl, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                uint256, ERC20.uint256, ERC20.uint256Int, staticABIEncodedSize?,
                isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | unit =>
              simp [config, vyperERC20Config, genSolidityConstructorDeployment, erc20Contract,
                ERC20.erc20Contract, ERC20.constructorDecl, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                uint256, ERC20.uint256, ERC20.uint256Int, staticABIEncodedSize?,
                isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | storageRef er ty =>
              simp [config, vyperERC20Config, genSolidityConstructorDeployment, erc20Contract,
                ERC20.erc20Contract, ERC20.constructorDecl, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                uint256, ERC20.uint256, ERC20.uint256Int, staticABIEncodedSize?,
                isDynamicABIType, encodeABIValue?, encodeABIWord?] at h

theorem erc20CtorAssignBalance (evm : EVM.State) (initialSupply : Int)
    (h0 : 0 ≤ initialSupply)
    (hlt : initialSupply < Int.ofNat (EVM.twoPow 256)) :
    assignStorageRef? config
      { contract := erc20Contract, locals := erc20CtorLocals initialSupply }
      evm .storage (balanceOfRef sender) (.int initialSupply) =
        .ok ({ contract := erc20Contract, locals := erc20CtorLocals initialSupply },
          erc20CtorBalancePostState evm (EVM.word initialSupply.toNat)) := by
  apply assignStorageRef_storage_scalar (ty := uint256Storage)
      (hbase := erc20CtorLocals_get_balanceOf initialSupply)
      (her := by
        simp [evalStorageRef, evalStorageRefStep, evalStorageRefSteps, balanceOfRef, sender,
          ERC20.balanceOfRef, ERC20.sender, envValue, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind,
          pure, evalExpr?])
      (hty := by simp [storageTypeAt?, erc20Contract, ERC20.erc20Contract,
        ERC20.erc20StorageDecls, uint256Storage, ERC20.uint256Storage, storageTypeStep?])
      (hloc := vyperERC20Config_storage_balanceOf (.address evm.executionEnv.source))
  have hword :
      (EVM.word initialSupply.toNat).toNat = initialSupply.toNat :=
    constructorUInt256Word_toNat initialSupply h0 hlt
  have hint : Int.ofNat (EVM.word initialSupply.toNat).toNat = initialSupply := by
    calc
      Int.ofNat (EVM.word initialSupply.toNat).toNat = Int.ofNat initialSupply.toNat := by
        rw [hword]
      _ = initialSupply := by
        exact Int.toNat_of_nonneg h0
  conv_lhs => rw [← hint]
  rw [vyperERC20StorageLocStore_uint256]
  rfl

theorem erc20CtorAssignTotalSupply (evm : EVM.State) (initialSupply : Int)
    (h0 : 0 ≤ initialSupply)
    (hlt : initialSupply < Int.ofNat (EVM.twoPow 256)) :
    assignStorageRef? config
      { contract := erc20Contract, locals := erc20CtorLocals initialSupply }
      evm .storage totalSupplyRef (.int initialSupply) =
        .ok ({ contract := erc20Contract, locals := erc20CtorLocals initialSupply },
          Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩
            (EVM.word initialSupply.toNat)) := by
  apply assignStorageRef_storage_scalar (ty := uint256Storage)
      (hbase := erc20CtorLocals_get_totalSupply initialSupply)
      (her := by
        simp [evalStorageRef, evalStorageRefSteps, totalSupplyRef, ERC20.totalSupplyRef,
          EvalResult.bind, pure, bind])
      (hty := by simp [storageTypeAt?, erc20Contract, ERC20.erc20Contract,
        ERC20.erc20StorageDecls, uint256Storage, ERC20.uint256Storage])
      (hloc := vyperERC20Config_storage_totalSupply)
  have hword :
      (EVM.word initialSupply.toNat).toNat = initialSupply.toNat :=
    constructorUInt256Word_toNat initialSupply h0 hlt
  have hint : Int.ofNat (EVM.word initialSupply.toNat).toNat = initialSupply := by
    calc
      Int.ofNat (EVM.word initialSupply.toNat).toNat = Int.ofNat initialSupply.toNat := by
        rw [hword]
      _ = initialSupply := by
        exact Int.toNat_of_nonneg h0
  conv_lhs => rw [← hint]
  rw [vyperERC20StorageLocStore_uint256]

theorem erc20SolmCtorExecReverts_nonpayable
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (initialSupply : Int)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    solmCtorExec config erc20Contract [.int initialSupply]
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I .reverted := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
    (argsStore := erc20CtorLocals initialSupply)
    ?_ rfl ?_ ?_
  · rfl
  · simp [erc20CtorLocals, erc20Contract, ERC20.erc20Contract, ERC20.constructorDecl]
  · exact bodyReverts_nonPayable (cfg := config) (contract := erc20Contract)
      (locals := erc20CtorLocals initialSupply) hwv

theorem erc20SolmCtorExecSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (initialSupply : Int)
    (h0 : 0 ≤ initialSupply)
    (hlt : initialSupply < Int.ofNat (EVM.twoPow 256))
    (hwv : I.weiValue = ⟨0⟩) :
    solmCtorExec config erc20Contract [.int initialSupply]
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      (.returned
        { contract := erc20Contract, locals := erc20CtorLocals initialSupply }
        (erc20CtorPostState
          (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
          (EVM.word initialSupply.toNat))
        none) := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
    (argsStore := erc20CtorLocals initialSupply)
    ?_ rfl ?_ ?_
  · rfl
  · simp [erc20CtorLocals, erc20Contract, ERC20.erc20Contract, ERC20.constructorDecl]
  · refine ExecFuncBody.execBlockOK ?_
    let frame : Frame := { contract := erc20Contract, locals := erc20CtorLocals initialSupply }
    let evm0 := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := erc20CtorBalancePostState evm0 (EVM.word initialSupply.toNat)
    refine ExecBlock.consNormal (solm' := frame) (evm' := evm0)
      (ExecStmt.requireTrue (evalCallvalueEq_true (cfg := config)
        (solm := frame) (evm := evm0) (by simpa [evm0, initState] using hwv))) ?_
    refine ExecBlock.consNormal (solm' := frame) (evm' := evm1) ?_ ?_
    · exact ExecStmt.assign (value := .int initialSupply)
        (by
          show evalExpr? config frame evm0 (.var "initialSupply") = .ok (.int initialSupply)
          unfold frame
          simp only [evalExpr?, erc20CtorLocals_get_initialSupply, EvalResult.ofOption])
        (by
          unfold evm1 evm0 frame
          exact erc20CtorAssignBalance
            (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
            initialSupply h0 hlt)
    · refine ExecBlock.consNormal ?_ ExecBlock.nil
      exact ExecStmt.assign (value := .int initialSupply)
        (by
          show evalExpr? config frame evm1 (.var "initialSupply") = .ok (.int initialSupply)
          unfold frame
          simp only [evalExpr?, erc20CtorLocals_get_initialSupply, EvalResult.ofOption])
        (by
          unfold evm1 frame
          simpa [erc20CtorPostState, storageStore_executionEnv] using
            erc20CtorAssignTotalSupply
              (erc20CtorBalancePostState
                (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
                (EVM.word initialSupply.toNat))
              initialSupply h0 hlt)

/-! ## Constructor bytecode side -/

theorem vyperERC20CtorPrefix_size : vyperERC20CtorPrefix.size = 107 := by
  decide +native

theorem vyperERC20Bytecode_size : vyperERC20Bytecode.size = 819 := by
  decide +native

theorem vyperERC20Initcode_size : vyperERC20Initcode.size = 926 := by
  rw [vyperERC20Initcode, ByteArray.size_append, vyperERC20CtorPrefix_size,
    vyperERC20Bytecode_size]

theorem vyperERC20Initcode_runtime_window :
    vyperERC20Initcode.extract 107 (107 + 819) = vyperERC20Bytecode := by
  unfold vyperERC20Initcode
  exact extract_append_right' vyperERC20CtorPrefix vyperERC20Bytecode 107 (107 + 819)
    vyperERC20CtorPrefix_size.symm
    (by rw [vyperERC20CtorPrefix_size, vyperERC20Bytecode_size])

noncomputable def erc20CtorCode (initialSupply : UInt256) : ByteArray :=
  vyperERC20Initcode ++ (EVM.Word.toBytesBE initialSupply).toByteArray

theorem vyperERC20Initcode_decode_append (tail : ByteArray) (pc : UInt256)
    (hwin : pc.toNat + 33 ≤ 926) :
    decode (vyperERC20Initcode ++ tail) pc = decode vyperERC20Initcode pc :=
  Reasoning.Theory.decode_append_left_window vyperERC20Initcode tail pc
    (by rw [vyperERC20Initcode_size]; exact hwin) (by rw [vyperERC20Initcode_size]; norm_num)

macro "vyper_erc20_ctor_decode" : tactic =>
  `(tactic|
    (first
      | rw [vyperERC20Initcode_decode_append _ _ (by decide)]
      | (unfold erc20CtorCode; rw [vyperERC20Initcode_decode_append _ _ (by decide)]);
     decide +native))

macro "vyper_erc20_ctor_jd" : tactic =>
  `(tactic|
    (first
      | (apply Reasoning.Theory.D_J_contains_append_left; decide +native)
      | (unfold erc20CtorCode; apply Reasoning.Theory.D_J_contains_append_left; decide +native)))

open Lean in
macro "vyper_erc20_ctor_run " base:term " with " "[" steps:evmStep,* "]" : term => do
  let mut acc := base
  for s in steps.getElems do
    match s with
    | `(evmStep| raw $op:ident $args*) =>
        acc ← `($(acc).$op $args*)
    | `(evmStep| $op:ident $args*) =>
        match op.getId with
        | `jump    => acc ← `($(acc).jump (by vyper_erc20_ctor_decode) $(args[0]!) (by evm_ov))
        | `jumpiT  => acc ← `($(acc).jumpiT (by vyper_erc20_ctor_decode) $(args[0]!) $(args[1]!)
                            (by evm_ov))
        | `jumpiNT => acc ← `($(acc).jumpiNT (by vyper_erc20_ctor_decode) $(args[0]!) (by evm_ov))
        | _        => acc ← `($(acc).$op $args* (by vyper_erc20_ctor_decode) (by evm_ov))
    | _ => Macro.throwUnsupported
  return acc

noncomputable def erc20CtorArgMem (initialSupply : UInt256) : ByteArray :=
  (erc20CtorCode initialSupply).write 926 ByteArray.empty 0 32

noncomputable def erc20CtorOwnerMem (caller : AccountAddress) (initialSupply : UInt256) :
    ByteArray :=
  wordAt32Mem (UInt256.ofNat caller.val) (erc20CtorArgMem initialSupply)

noncomputable def erc20CtorHashMem (caller : AccountAddress) (initialSupply : UInt256) :
    ByteArray :=
  wordAt0Mem ⟨0⟩ (erc20CtorOwnerMem caller initialSupply)

noncomputable def erc20CtorArgAgainMem (caller : AccountAddress) (initialSupply : UInt256) :
    ByteArray :=
  (erc20CtorCode initialSupply).write 926 (erc20CtorHashMem caller initialSupply) 0 32

noncomputable def erc20CtorLogMem (caller : AccountAddress) (initialSupply : UInt256) :
    ByteArray :=
  (erc20CtorCode initialSupply).write 926 (erc20CtorArgAgainMem caller initialSupply) 64 32

noncomputable def erc20CtorReturnMem (caller : AccountAddress) (initialSupply : UInt256) :
    ByteArray :=
  (erc20CtorCode initialSupply).write 107 (erc20CtorLogMem caller initialSupply) 0 819

theorem erc20CtorArg_extract (initialSupply : UInt256) :
    (erc20CtorCode initialSupply).extract 926 (926 + 32) =
      (EVM.Word.toBytesBE initialSupply).toByteArray := by
  unfold erc20CtorCode
  exact extract_append_right' vyperERC20Initcode (EVM.Word.toBytesBE initialSupply).toByteArray
    926 (926 + 32)
    vyperERC20Initcode_size.symm
    (by rw [vyperERC20Initcode_size, word_toBytesBE_toByteArray_size])

theorem erc20CtorArgMem_read0 (initialSupply : UInt256) :
    (erc20CtorArgMem initialSupply).readWithPadding 0 32 =
      UInt256.toByteArray initialSupply := by
  unfold erc20CtorArgMem
  rw [write0_read_back_from_gen (erc20CtorCode initialSupply) ByteArray.empty 926 32
    (by decide)
    (by rw [erc20CtorCode, ByteArray.size_append, vyperERC20Initcode_size,
      word_toBytesBE_toByteArray_size])
    (by decide)]
  rw [erc20CtorArg_extract, word_toBytesBE_toByteArray_eq_toByteArray]

theorem erc20CtorArgMem_size (initialSupply : UInt256) :
    (erc20CtorArgMem initialSupply).size = 32 := by
  unfold erc20CtorArgMem
  simpa using write_end_size_from (erc20CtorCode initialSupply) ByteArray.empty 926 32
    (by decide)
    (by rw [erc20CtorCode, ByteArray.size_append, vyperERC20Initcode_size,
      word_toBytesBE_toByteArray_size])

theorem erc20CtorArgMem_mload0 (initialSupply : UInt256) :
    (if (⟨0⟩ : UInt256).toNat ≥ (erc20CtorArgMem initialSupply).size
        ∨ (⟨0⟩ : UInt256) ≥ (UInt256.ofNat 1) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian
        ((erc20CtorArgMem initialSupply).readWithPadding 0 32)))
      = initialSupply := by
  exact mloadWordValue_of_readWithPadding
    (mem := erc20CtorArgMem initialSupply) (aw := UInt256.ofNat 1) (off := ⟨0⟩)
    (v := initialSupply)
    (by rw [erc20CtorArgMem_size]; decide)
    (by decide)
    (erc20CtorArgMem_read0 initialSupply)

theorem erc20CtorOwnerMem_size (caller : AccountAddress) (initialSupply : UInt256) :
    (erc20CtorOwnerMem caller initialSupply).size = 64 := by
  unfold erc20CtorOwnerMem wordAt32Mem
  have h := write_end_size_from (UInt256.toByteArray (UInt256.ofNat caller.val))
    (erc20CtorArgMem initialSupply) 0 32 (by decide)
    (by rw [toByteArray_size])
  simpa [erc20CtorArgMem_size initialSupply] using h

theorem erc20CtorOwnerMem_read32 (caller : AccountAddress) (initialSupply : UInt256) :
    (erc20CtorOwnerMem caller initialSupply).readWithPadding 32 32 =
      UInt256.toByteArray (UInt256.ofNat caller.val) := by
  unfold erc20CtorOwnerMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
    (by rw [erc20CtorArgMem_size initialSupply])]
  rw [show (UInt256.toByteArray (UInt256.ofNat caller.val)).extract 0 32 =
      UInt256.toByteArray (UInt256.ofNat caller.val) from by
    rw [show 32 = (UInt256.toByteArray (UInt256.ofNat caller.val)).size by rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem erc20CtorHashMem_size (caller : AccountAddress) (initialSupply : UInt256) :
    (erc20CtorHashMem caller initialSupply).size = 64 := by
  unfold erc20CtorHashMem wordAt0Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
    (by rw [erc20CtorOwnerMem_size caller initialSupply]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    erc20CtorOwnerMem_size caller initialSupply, toByteArray_size]
  omega

theorem erc20CtorHashMem_read0 (caller : AccountAddress) (initialSupply : UInt256) :
    (erc20CtorHashMem caller initialSupply).readWithPadding 0 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold erc20CtorHashMem
  exact wordAt0Mem_read0 ⟨0⟩ (erc20CtorOwnerMem caller initialSupply)

theorem erc20CtorHashMem_read32 (caller : AccountAddress) (initialSupply : UInt256) :
    (erc20CtorHashMem caller initialSupply).readWithPadding 32 32 =
      UInt256.toByteArray (UInt256.ofNat caller.val) := by
  unfold erc20CtorHashMem wordAt0Mem
  rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size])
    (by rw [erc20CtorOwnerMem_size caller initialSupply]; omega)
    (by omega)
    (by rw [erc20CtorOwnerMem_size caller initialSupply])]
  exact erc20CtorOwnerMem_read32 caller initialSupply

set_option maxHeartbeats 800000 in
theorem erc20CtorHashMem_read0_64 (caller : AccountAddress) (initialSupply : UInt256) :
    (erc20CtorHashMem caller initialSupply).readWithPadding 0 64 =
      UInt256.toByteArray (⟨0⟩ : UInt256) ++
        UInt256.toByteArray (UInt256.ofNat caller.val) := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [erc20CtorHashMem_size caller initialSupply])]
  have hleft :
      (erc20CtorHashMem caller initialSupply).extract 0 32 =
        UInt256.toByteArray (⟨0⟩ : UInt256) := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [erc20CtorHashMem_size caller initialSupply]; omega),
      erc20CtorHashMem_read0 caller initialSupply]
  have hright :
      (erc20CtorHashMem caller initialSupply).extract 32 64 =
        UInt256.toByteArray (UInt256.ofNat caller.val) := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [erc20CtorHashMem_size caller initialSupply]),
      erc20CtorHashMem_read32 caller initialSupply]
  rw [show (erc20CtorHashMem caller initialSupply).extract 0 64 =
      (erc20CtorHashMem caller initialSupply).extract 0 32 ++
        (erc20CtorHashMem caller initialSupply).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem erc20CtorKeccakSlot (caller : AccountAddress) (initialSupply : UInt256) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((erc20CtorHashMem caller initialSupply).readWithPadding 0 64)))
      = erc20BalanceOfSlot (.address caller) := by
  unfold erc20BalanceOfSlot vyperMappingSlot
  rw [erc20CtorHashMem_read0_64 caller initialSupply, keyValueToWord_address caller]
  exact keccakSlot_eq _

theorem erc20CtorArgAgainMem_read0 (caller : AccountAddress) (initialSupply : UInt256) :
    (erc20CtorArgAgainMem caller initialSupply).readWithPadding 0 32 =
      UInt256.toByteArray initialSupply := by
  unfold erc20CtorArgAgainMem
  rw [write0_read_back_from_gen (erc20CtorCode initialSupply)
    (erc20CtorHashMem caller initialSupply) 926 32
    (by decide)
    (by rw [erc20CtorCode, ByteArray.size_append, vyperERC20Initcode_size,
      word_toBytesBE_toByteArray_size])
    (by decide)]
  rw [erc20CtorArg_extract, word_toBytesBE_toByteArray_eq_toByteArray]

theorem erc20CtorArgAgainMem_size (caller : AccountAddress) (initialSupply : UInt256) :
    (erc20CtorArgAgainMem caller initialSupply).size = 64 := by
  unfold erc20CtorArgAgainMem
  rw [write_eq_gen_from _ _ 926 0 32
    (by decide)
    (by rw [erc20CtorCode, ByteArray.size_append, vyperERC20Initcode_size,
      word_toBytesBE_toByteArray_size])
    (by rw [erc20CtorHashMem_size caller initialSupply]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    erc20CtorHashMem_size caller initialSupply, erc20CtorCode, ByteArray.size_append,
    vyperERC20Initcode_size, word_toBytesBE_toByteArray_size]
  omega

theorem erc20CtorArgAgainMem_mload0 (caller : AccountAddress) (initialSupply : UInt256) :
    (if (⟨0⟩ : UInt256).toNat ≥ (erc20CtorArgAgainMem caller initialSupply).size
        ∨ (⟨0⟩ : UInt256) ≥ (UInt256.ofNat 2) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian
        ((erc20CtorArgAgainMem caller initialSupply).readWithPadding 0 32)))
      = initialSupply := by
  apply mloadWordValue_of_readWithPadding
    (mem := erc20CtorArgAgainMem caller initialSupply) (aw := UInt256.ofNat 2) (off := ⟨0⟩)
    (v := initialSupply)
  · rw [erc20CtorArgAgainMem_size]; decide
  · decide
  · exact erc20CtorArgAgainMem_read0 caller initialSupply

theorem erc20CtorReturnMem_read (caller : AccountAddress) (initialSupply : UInt256) :
    (erc20CtorReturnMem caller initialSupply).readWithPadding 0 819 = vyperERC20Bytecode := by
  unfold erc20CtorReturnMem
  rw [write0_read_back_from_gen (erc20CtorCode initialSupply)
    (erc20CtorLogMem caller initialSupply) 107 819
    (by decide)
    (by rw [erc20CtorCode, ByteArray.size_append, vyperERC20Initcode_size,
      word_toBytesBE_toByteArray_size]; omega)
    (by decide)]
  have hleft :
      (erc20CtorCode initialSupply).extract 107 (107 + 819) =
        vyperERC20Initcode.extract 107 (107 + 819) := by
    have h := extract_append_left vyperERC20Initcode
      (EVM.Word.toBytesBE initialSupply).toByteArray 107 (107 + 819)
      (by rw [vyperERC20Initcode_size])
    simpa [erc20CtorCode] using h
  rw [hleft, vyperERC20Initcode_runtime_window]

def transferTransferTopic : UInt256 :=
  ⟨0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef⟩

theorem erc20InitcodeNonpayableRevert
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (tail : ByteArray)
    (hcode : I.code = vyperERC20Initcode ++ tail)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev (vyperERC20Initcode ++ tail) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  have rd0 :
      RD (vyperERC20Initcode ++ tail) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨0⟩ []
        ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (createdAccounts, σ) 0 0 :=
    RD.initState hcode
  have rd103 := vyper_erc20_ctor_run rd0 with [
    callvalue, push2 ⟨103⟩,
    jumpiT hwv (by vyper_erc20_ctor_jd),
    jumpdest, push0, dup1]
  exact rd103.rev 0 (by vyper_erc20_ctor_decode)
    (fun s _ hstks => memExpRevert0 s hstks) (by simp)

theorem erc20InitcodeSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (initialSupply : UInt256)
    (hcode : I.code = erc20CtorCode initialSupply)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) :
    RDret (erc20CtorCode initialSupply) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      (createdAccounts,
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ (erc20BalanceOfSlot (.address I.source)) initialSupply)
          ⟨2⟩ initialSupply)
      vyperERC20Bytecode := by
  have rd0 :
      RD (erc20CtorCode initialSupply) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨0⟩ []
        ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (createdAccounts, σ) 0 0 :=
    RD.initState hcode
  have rdBeforeBalanceStore := vyper_erc20_ctor_run rd0 with [
    callvalue, push2 ⟨103⟩,
    jumpiNT (by simp [hwv]),
    push1 ⟨32⟩, push2 ⟨926⟩, push0,
    raw codecopy 3 (erc20CtorArgMem initialSupply) (UInt256.ofNat 1)
      (by vyper_erc20_ctor_decode)
      mem_cost
      rfl
      (by decide) (by evm_ov),
    push0,
    raw mload 0 initialSupply (UInt256.ofNat 1)
      (by vyper_erc20_ctor_decode)
      mem_cost
      (erc20CtorArgMem_mload0 initialSupply)
      (by decide) (by evm_ov),
    push0, caller, push1 ⟨32⟩,
    raw mstore 3 (erc20CtorOwnerMem I.source initialSupply) (UInt256.ofNat 2)
      (by vyper_erc20_ctor_decode)
      mem_cost
      rfl
      (by decide) (by evm_ov),
    push0,
    raw mstore 0 (erc20CtorHashMem I.source initialSupply) (UInt256.ofNat 2)
      (by vyper_erc20_ctor_decode)
      mem_cost
      rfl
      (by decide) (by evm_ov),
    push1 ⟨64⟩, push0,
    raw keccak256 0 (erc20BalanceOfSlot (.address I.source)) (UInt256.ofNat 2)
      (by vyper_erc20_ctor_decode)
      mem_cost
      (erc20CtorKeccakSlot I.source initialSupply)
      (by decide) (by evm_ov)]
  obtain ⟨k', C', rdAfterBalanceStore⟩ :=
    rdBeforeBalanceStore.sstore hperm (by vyper_erc20_ctor_decode) (by evm_ov)
  have rdBeforeTotalSupplyStore := vyper_erc20_ctor_run rdAfterBalanceStore with [
    push1 ⟨32⟩, push2 ⟨926⟩, push0,
    raw codecopy 0 (erc20CtorArgAgainMem I.source initialSupply) (UInt256.ofNat 2)
      (by vyper_erc20_ctor_decode)
      mem_cost
      rfl
      (by decide) (by evm_ov),
    push0,
    raw mload 0 initialSupply (UInt256.ofNat 2)
      (by vyper_erc20_ctor_decode)
      mem_cost
      (erc20CtorArgAgainMem_mload0 I.source initialSupply)
      (by decide) (by evm_ov),
    push1 ⟨2⟩]
  obtain ⟨k'', C'', rdAfterTotalSupplyStore⟩ :=
    rdBeforeTotalSupplyStore.sstore hperm (by vyper_erc20_ctor_decode) (by evm_ov)
  have rdBeforeTopic := vyper_erc20_ctor_run rdAfterTotalSupplyStore with [
    caller, push0]
  have rdAfterTopic := rdBeforeTopic.pushConst transferTransferTopic
    (width := 32) (op := .PUSH32)
    (by decide) (by vyper_erc20_ctor_decode) (by evm_ov)
  have rdBeforeReturn := vyper_erc20_ctor_run rdAfterTopic with [
    push1 ⟨32⟩, push2 ⟨926⟩, push1 ⟨64⟩,
    raw codecopy 3 (erc20CtorLogMem I.source initialSupply) (UInt256.ofNat 3)
      (by vyper_erc20_ctor_decode)
      mem_cost
      rfl
      (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨64⟩,
    raw log3 0 (UInt256.ofNat 3)
      (by vyper_erc20_ctor_decode)
      hperm
      mem_cost
      (by decide)
      (by evm_ov),
    push2 ⟨819⟩, push2 ⟨107⟩, push2 ⟨0⟩,
    raw codecopy 70 (erc20CtorReturnMem I.source initialSupply) (UInt256.ofNat 26)
      (by vyper_erc20_ctor_decode)
      mem_cost
      rfl
      (by decide) (by evm_ov),
    push2 ⟨819⟩, push2 ⟨0⟩]
  exact rdBeforeReturn.ret 0 vyperERC20Bytecode
    (by vyper_erc20_ctor_decode)
    mem_cost
    (erc20CtorReturnMem_read I.source initialSupply)
    (by evm_ov)

def erc20SelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩
  | 1 => ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩
  | 2 => ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩
  | 3 => ⟨#[0x70, 0xa0, 0x82, 0x31]⟩
  | 4 => ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩
  | _ => ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩

def selectorMissDispatchMem : ByteArray :=
  vyperERC20Bytecode.write 813 ByteArray.empty 30 2

theorem selectorMissDispatchMem_mload0 :
    (if (⟨0⟩ : UInt256).toNat ≥ selectorMissDispatchMem.size ∨
        (⟨0⟩ : UInt256) ≥ (UInt256.ofNat 1) * ⟨32⟩
      then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (selectorMissDispatchMem.readWithPadding (⟨0⟩ : UInt256).toNat 32)))
      = (⟨797⟩ : UInt256) := by
  decide +native

theorem erc20Dispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg erc20Contract cd = none := by
  refine dispatchMsg_none_of_all_ne (contract := erc20Contract) (hfallback := rfl) (hreceive := rfl) ?_
  intro t ht
  simp [erc20Contract, ERC20.erc20Contract] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · have hfalse : ((⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ : ByteArray) == cd.extract 0 4) = false := by
      by_cases hbeq : ((⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ : ByteArray) == cd.extract 0 4) = true
      · have hs := byteArray_size_eq_of_beq hbeq
        have hleft : (⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ : ByteArray).size = 4 := rfl
        rw [hleft, ByteArray.size_extract] at hs
        omega
      · simpa using hbeq
    simpa [selectorOf, vyperERC20ApproveSelectorBytes] using hfalse
  · have hfalse : ((⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ : ByteArray) == cd.extract 0 4) = false := by
      by_cases hbeq : ((⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ : ByteArray) == cd.extract 0 4) = true
      · have hs := byteArray_size_eq_of_beq hbeq
        have hleft : (⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ : ByteArray).size = 4 := rfl
        rw [hleft, ByteArray.size_extract] at hs
        omega
      · simpa using hbeq
    simpa [selectorOf, vyperERC20TotalSupplySelectorBytes] using hfalse
  · have hfalse : ((⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ : ByteArray) == cd.extract 0 4) = false := by
      by_cases hbeq : ((⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ : ByteArray) == cd.extract 0 4) = true
      · have hs := byteArray_size_eq_of_beq hbeq
        have hleft : (⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ : ByteArray).size = 4 := rfl
        rw [hleft, ByteArray.size_extract] at hs
        omega
      · simpa using hbeq
    simpa [selectorOf, vyperERC20TransferFromSelectorBytes] using hfalse
  · have hfalse : ((⟨#[0x70, 0xa0, 0x82, 0x31]⟩ : ByteArray) == cd.extract 0 4) = false := by
      by_cases hbeq : ((⟨#[0x70, 0xa0, 0x82, 0x31]⟩ : ByteArray) == cd.extract 0 4) = true
      · have hs := byteArray_size_eq_of_beq hbeq
        have hleft : (⟨#[0x70, 0xa0, 0x82, 0x31]⟩ : ByteArray).size = 4 := rfl
        rw [hleft, ByteArray.size_extract] at hs
        omega
      · simpa using hbeq
    simpa [selectorOf, vyperERC20BalanceOfSelectorBytes] using hfalse
  · have hfalse : ((⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ : ByteArray) == cd.extract 0 4) = false := by
      by_cases hbeq : ((⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ : ByteArray) == cd.extract 0 4) = true
      · have hs := byteArray_size_eq_of_beq hbeq
        have hleft : (⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ : ByteArray).size = 4 := rfl
        rw [hleft, ByteArray.size_extract] at hs
        omega
      · simpa using hbeq
    simpa [selectorOf, vyperERC20TransferSelectorBytes] using hfalse
  · have hfalse : ((⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ : ByteArray) == cd.extract 0 4) = false := by
      by_cases hbeq : ((⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ : ByteArray) == cd.extract 0 4) = true
      · have hs := byteArray_size_eq_of_beq hbeq
        have hleft : (⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ : ByteArray).size = 4 := rfl
        rw [hleft, ByteArray.size_extract] at hs
        omega
      · simpa using hbeq
    simpa [selectorOf, vyperERC20AllowanceSelectorBytes] using hfalse

theorem erc20Dispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 6 → (erc20SelBytes i == cd.extract 0 4) = false) :
    dispatchMsg erc20Contract cd = none := by
  refine dispatchMsg_none_of_all_ne (contract := erc20Contract) (hfallback := rfl) (hreceive := rfl) ?_
  intro t ht
  simp [erc20Contract, ERC20.erc20Contract] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [selectorOf, vyperERC20ApproveSelectorBytes] using hnm 0 (by decide)
  · simpa [selectorOf, vyperERC20TotalSupplySelectorBytes] using hnm 1 (by decide)
  · simpa [selectorOf, vyperERC20TransferFromSelectorBytes] using hnm 2 (by decide)
  · simpa [selectorOf, vyperERC20BalanceOfSelectorBytes] using hnm 3 (by decide)
  · simpa [selectorOf, vyperERC20TransferSelectorBytes] using hnm 4 (by decide)
  · simpa [selectorOf, vyperERC20AllowanceSelectorBytes] using hnm 5 (by decide)

theorem u256_xor_ne_zero_of_ne {a b : UInt256} (h : a ≠ b) :
    UInt256.xor a b ≠ ⟨0⟩ := by
  cases a with
  | mk av =>
      cases b with
      | mk bv =>
          simp [UInt256.xor] at h ⊢
          intro hx
          apply h
          apply Fin.ext
          have hxv := congrArg Fin.val hx
          have hxv' : (av.val ^^^ bv.val) % UInt256.size = 0 := by
            simpa [Fin.xor] using hxv
          have hlt : av.val ^^^ bv.val < UInt256.size := by
            simpa [UInt256.size] using Nat.xor_lt_two_pow (n := 256) av.isLt bv.isLt
          have hx0 : av.val ^^^ bv.val = 0 := by
            rwa [Nat.mod_eq_of_lt hlt] at hxv'
          exact Nat.xor_eq_zero_iff.mp hx0

theorem selector_toNat_readBytes4 (cd : ByteArray) :
    (UInt256.shiftRight (uInt256OfByteArray (ByteArray.readBytes cd 0 32)) ⟨224⟩).toNat
      = fromBytesBigEndian ((ByteArray.readBytes cd 0 32).data.toList.take 4) := by
  have hlen := readBytes32_len cd
  have hV : fromBytes' (ByteArray.readBytes cd 0 32).data.toList.reverse < 2 ^ 256 := by
    have := fromBytes'_le (bs := (ByteArray.readBytes cd 0 32).data.toList.reverse)
    rwa [List.length_reverse, hlen] at this
  unfold UInt256.shiftRight uInt256OfByteArray
  rw [if_neg (by decide : ¬ ((⟨224⟩ : UInt256).val ≥ 256))]
  show ((UInt256.ofNat _).val >>> (⟨224⟩ : UInt256).val).val = _
  rw [Fin.shiftRight_val]
  show (UInt256.ofNat _).val.val >>> (224 : ℕ) = _
  rw [Nat.shiftRight_eq_div_pow]
  show (fromBytes' _ % UInt256.size) / 2 ^ 224 = _
  rw [show UInt256.size = 2 ^ 256 from rfl, Nat.mod_eq_of_lt hV]
  show fromBytesBigEndian (ByteArray.readBytes cd 0 32).data.toList / 2 ^ 224 = _
  conv_lhs => rw [← List.take_append_drop 4 (ByteArray.readBytes cd 0 32).data.toList]
  rw [show (224 : ℕ) = 8 * ((ByteArray.readBytes cd 0 32).data.toList.drop 4).length from by
        rw [List.length_drop, hlen], fromBytesBigEndian_append_div]

theorem vyperRuntimeSelectorWord_short_mod_256_zero {cd : ByteArray}
    (hshort : cd.size < 4) :
    (UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩).toNat % 256 = 0 := by
  rw [selector_toNat_readBytes4]
  have htake32eq4 : cd.data.toList.take 32 = cd.data.toList.take 4 := by
    have htake32 : cd.data.toList.take 32 = cd.data.toList := by
      rw [List.take_of_length_le]
      simpa [Array.length_toList] using (show cd.size ≤ 32 by omega)
    have htake4 : cd.data.toList.take 4 = cd.data.toList := by
      rw [List.take_of_length_le]
      simpa [Array.length_toList] using (show cd.size ≤ 4 by omega)
    rw [htake32, htake4]
  have hpad :
      (ByteArray.readBytes cd 0 32).data.toList.take 4 =
        cd.data.toList.take 4 ++ List.replicate (4 - cd.size) 0 := by
    rw [readBytes32_toList]
    have hlenTake32 : (cd.data.toList.take 32).length = cd.size := by
      rw [List.length_take, Array.length_toList]
      simpa using min_eq_right (show cd.size ≤ 32 by omega)
    rw [List.take_append, List.take_take, show min 4 32 = 4 by decide, hlenTake32]
    congr 1
    rw [List.take_replicate]
    rw [min_eq_left]
    omega
  rw [hpad, fromBytesBigEndian_append_zeros]
  have hpos : 1 ≤ 4 - cd.size := by
    omega
  have hsplit : 2 ^ (8 * (4 - cd.size)) = 256 * 2 ^ (8 * (4 - cd.size) - 8) := by
    rw [show 256 = 2 ^ 8 by norm_num]
    calc
      2 ^ (8 * (4 - cd.size)) = 2 ^ (8 + (8 * (4 - cd.size) - 8)) := by
        congr
        omega
      _ = 2 ^ 8 * 2 ^ (8 * (4 - cd.size) - 8) := by rw [Nat.pow_add]
  rw [hsplit]
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    (Nat.mul_mod_right 256
      (fromBytesBigEndian (List.take 4 cd.data.toList) * 2 ^ (8 * (4 - cd.size) - 8)))

theorem vyperRuntimeSelectorWord_ne_of_short {cd : ByteArray} {sel : UInt256}
    (hshort : cd.size < 4) (hlow : sel.toNat % 256 ≠ 0) :
    UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩ ≠ sel := by
  intro heq
  have hmod := vyperRuntimeSelectorWord_short_mod_256_zero (cd := cd) hshort
  have : sel.toNat % 256 = 0 := by
    simpa [heq] using hmod
  exact hlow this

theorem vyperRuntimeSelectorWord_ne_of_selector_false
    {cd : ByteArray} {sel : UInt256} {c0 c1 c2 c3 : UInt8}
    (hsz : 4 ≤ cd.size)
    (hselNat : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat)
    (hfalse : ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == cd.extract 0 4) = false) :
    UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩ ≠ sel := by
  intro heq
  have h := evmSelectorDecode hsz c0 c1 c2 c3 sel hselNat
  rw [hfalse, heq, u256_eq_refl] at h
  cases h

theorem u256_lor_ne_zero_right {a b : UInt256} (hb : b ≠ ⟨0⟩) :
    UInt256.lor a b ≠ ⟨0⟩ := by
  intro hzero
  have hlt : Nat.lor a.toNat b.toNat < UInt256.size := by
    simpa [UInt256.size] using Nat.or_lt_two_pow (n := 256) a.val.isLt b.val.isLt
  have hle : b.toNat ≤ (UInt256.lor a b).toNat := by
    rw [u256_lor_toNat, Nat.mod_eq_of_lt hlt]
    exact Nat.right_le_or
  have hlor0 : (UInt256.lor a b).toNat = 0 := by
    rw [hzero]
    rfl
  have hb0 : b.toNat = 0 := by omega
  exact hb (u256_inj hb0)

theorem vyperDispatchIndexWord {sel : UInt256} {m : Nat}
    (hmod : sel.toNat % 7 = m) :
    UInt256.mod sel ⟨7⟩ = UInt256.ofNat m := by
  apply u256_inj
  unfold UInt256.mod
  rw [if_neg (by decide : ¬ ((⟨7⟩ : UInt256).val == 0))]
  show sel.toNat % 7 = (UInt256.ofNat m).toNat
  rw [hmod]
  have hm7 : m < 7 := by
    rw [← hmod]
    exact Nat.mod_lt _ (by decide)
  have hmlt : m < UInt256.size := lt_trans hm7 (by decide)
  exact (ulit_toNat' m hmlt).symm

theorem shiftLeft1_ofNat_eq {n : Nat} (h : 2 * n < UInt256.size) :
    UInt256.shiftLeft (UInt256.ofNat n) ⟨1⟩ = UInt256.ofNat (2 * n) := by
  apply u256_inj
  unfold UInt256.shiftLeft
  rw [if_neg (by decide : ¬ ((⟨1⟩ : UInt256).val ≥ 256))]
  change (((UInt256.ofNat n).val.val <<< 1) % UInt256.size) = (UInt256.ofNat (2 * n)).val.val
  have hn : n < UInt256.size := by
    omega
  rw [show (UInt256.ofNat n).val.val = n by exact ulit_toNat' n hn]
  rw [show (UInt256.ofNat (2 * n)).val.val = 2 * n by exact ulit_toNat' (2 * n) h]
  rw [Nat.shiftLeft_eq]
  simpa [Nat.mul_comm] using (Nat.mod_eq_of_lt h)

theorem vyperDispatchSourceOfMod {sel : UInt256} {m : Nat}
    (hmod : sel.toNat % 7 = m) :
    (⟨805⟩ : UInt256) + UInt256.shiftLeft (UInt256.mod sel ⟨7⟩) ⟨1⟩ =
      UInt256.ofNat (805 + 2 * m) := by
  have hm7 : m < 7 := by
    rw [← hmod]
    exact Nat.mod_lt _ (by decide)
  have h2m : 2 * m < UInt256.size := lt_trans (by omega : 2 * m < 14) (by decide)
  rw [vyperDispatchIndexWord hmod, shiftLeft1_ofNat_eq h2m]
  apply u256_inj
  have h805 : 805 < UInt256.size := by decide
  have hsum : 805 + 2 * m < UInt256.size := lt_trans (by omega : 805 + 2 * m < 819) (by decide)
  change (UInt256.add (UInt256.ofNat 805) (UInt256.ofNat (2 * m))).toNat =
    (UInt256.ofNat (805 + 2 * m)).toNat
  rw [uadd_ofNat_toNat h805 h2m hsum]
  have hfin : 805 + 2 * m < UInt256.size := lt_trans (by omega : 805 + 2 * m < 819) (by decide)
  rw [ulit_toNat' (805 + 2 * m) hfin]

abbrev vyperRuntimeSelectorWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

theorem erc20X_balanceOfReach_of_mod0 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vyperERC20Bytecode)
    (hmod : (vyperRuntimeSelectorWord I).toNat % 7 = 0) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨623⟩
      [vyperRuntimeSelectorWord I] balanceOfDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ) k C := by
  have rd0 := RD.initState (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode
  have rdBeforeCopy0 := evm_run rd0 with [
    push0, calldataload, push1 ⟨224⟩, shr, push1 ⟨2⟩, push1 ⟨7⟩, dup3, mod,
    push1 ⟨1⟩, shl, push2 ⟨805⟩, add, push1 ⟨30⟩]
  have rdAfterCopy0 := rdBeforeCopy0.codecopy 3
    (vyperERC20Bytecode.write
      (((⟨805⟩ : UInt256) +
        UInt256.shiftLeft (UInt256.mod (vyperRuntimeSelectorWord I) ⟨7⟩) ⟨1⟩).toNat)
      ByteArray.empty 30 2)
    (UInt256.ofNat 1)
    (by vyper_erc20_balance_decode) mem_cost rfl (by decide) (by evm_ov)
  have rdAfterCopy := by
    simpa [vyperRuntimeSelectorWord, balanceOfDispatchMem, vyperDispatchSourceOfMod hmod]
      using rdAfterCopy0
  have rdBeforeJump := evm_run rdAfterCopy with [
    push0,
    raw mload 0 ⟨623⟩ (UInt256.ofNat 1)
      (by vyper_erc20_balance_decode)
      mem_cost
      balanceOfDispatchMem_mload0
      (by decide) (by evm_ov)]
  exact ⟨_, _, rdBeforeJump.jump (by vyper_erc20_balance_decode) (by decide +native) (by evm_ov)⟩

theorem erc20X_approveReach_of_mod1 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vyperERC20Bytecode)
    (hmod : (vyperRuntimeSelectorWord I).toNat % 7 = 1) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨206⟩
      [vyperRuntimeSelectorWord I] approveDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ) k C := by
  have rd0 := RD.initState (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode
  have rdBeforeCopy0 := evm_run rd0 with [
    push0, calldataload, push1 ⟨224⟩, shr, push1 ⟨2⟩, push1 ⟨7⟩, dup3, mod,
    push1 ⟨1⟩, shl, push2 ⟨805⟩, add, push1 ⟨30⟩]
  have rdAfterCopy0 := rdBeforeCopy0.codecopy 3
    (vyperERC20Bytecode.write
      (((⟨805⟩ : UInt256) +
        UInt256.shiftLeft (UInt256.mod (vyperRuntimeSelectorWord I) ⟨7⟩) ⟨1⟩).toNat)
      ByteArray.empty 30 2)
    (UInt256.ofNat 1)
    (by vyper_erc20_approve_decode) mem_cost rfl (by decide) (by evm_ov)
  have rdAfterCopy := by
    simpa [vyperRuntimeSelectorWord, approveDispatchMem, vyperDispatchSourceOfMod hmod]
      using rdAfterCopy0
  have rdBeforeJump := evm_run rdAfterCopy with [
    push0,
    raw mload 0 ⟨206⟩ (UInt256.ofNat 1)
      (by vyper_erc20_approve_decode)
      mem_cost
      approveDispatchMem_mload0
      (by decide) (by evm_ov)]
  exact ⟨_, _, rdBeforeJump.jump (by vyper_erc20_approve_decode) (by decide +native) (by evm_ov)⟩

theorem erc20X_transferFromReach_of_mod2 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vyperERC20Bytecode)
    (hmod : (vyperRuntimeSelectorWord I).toNat % 7 = 2) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨331⟩
      [vyperRuntimeSelectorWord I] transferFromDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ) k C := by
  have rd0 := RD.initState (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode
  have rdBeforeCopy0 := evm_run rd0 with [
    push0, calldataload, push1 ⟨224⟩, shr, push1 ⟨2⟩, push1 ⟨7⟩, dup3, mod,
    push1 ⟨1⟩, shl, push2 ⟨805⟩, add, push1 ⟨30⟩]
  have rdAfterCopy0 := rdBeforeCopy0.codecopy 3
    (vyperERC20Bytecode.write
      (((⟨805⟩ : UInt256) +
        UInt256.shiftLeft (UInt256.mod (vyperRuntimeSelectorWord I) ⟨7⟩) ⟨1⟩).toNat)
      ByteArray.empty 30 2)
    (UInt256.ofNat 1)
    (by decide +native) mem_cost rfl (by decide) (by evm_ov)
  have rdAfterCopy := by
    simpa [vyperRuntimeSelectorWord, transferFromDispatchMem, vyperDispatchSourceOfMod hmod]
      using rdAfterCopy0
  have rdBeforeJump := evm_run rdAfterCopy with [
    push0,
    raw mload 0 ⟨331⟩ (UInt256.ofNat 1)
      (by decide +native)
      mem_cost
      transferFromDispatchMem_mload0
      (by decide) (by evm_ov)]
  exact ⟨_, _, rdBeforeJump.jump (by decide +native) (by decide +native) (by evm_ov)⟩

theorem erc20X_transferReach_of_mod3 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vyperERC20Bytecode)
    (hmod : (vyperRuntimeSelectorWord I).toNat % 7 = 3) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨24⟩
      [vyperRuntimeSelectorWord I] transferDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ) k C := by
  have rd0 := RD.initState (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode
  have rdBeforeCopy0 := evm_run rd0 with [
    push0, calldataload, push1 ⟨224⟩, shr, push1 ⟨2⟩, push1 ⟨7⟩, dup3, mod,
    push1 ⟨1⟩, shl, push2 ⟨805⟩, add, push1 ⟨30⟩]
  have rdAfterCopy0 := rdBeforeCopy0.codecopy 3
    (vyperERC20Bytecode.write
      (((⟨805⟩ : UInt256) +
        UInt256.shiftLeft (UInt256.mod (vyperRuntimeSelectorWord I) ⟨7⟩) ⟨1⟩).toNat)
      ByteArray.empty 30 2)
    (UInt256.ofNat 1)
    (by vyper_erc20_transfer_decode) mem_cost rfl (by decide) (by evm_ov)
  have rdAfterCopy := by
    simpa [vyperRuntimeSelectorWord, transferDispatchMem, vyperDispatchSourceOfMod hmod]
      using rdAfterCopy0
  have rdBeforeJump := evm_run rdAfterCopy with [
    push0,
    raw mload 0 ⟨24⟩ (UInt256.ofNat 1)
      (by vyper_erc20_transfer_decode)
      mem_cost
      transferDispatchMem_mload0
      (by decide) (by evm_ov)]
  exact ⟨_, _, rdBeforeJump.jump (by vyper_erc20_transfer_decode) (by decide +native) (by evm_ov)⟩

theorem erc20X_selectorMissReach_of_mod4 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vyperERC20Bytecode)
    (hmod : (vyperRuntimeSelectorWord I).toNat % 7 = 4) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨797⟩
      [vyperRuntimeSelectorWord I] selectorMissDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ) k C := by
  have rd0 := RD.initState (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode
  have rdBeforeCopy0 := evm_run rd0 with [
    push0, calldataload, push1 ⟨224⟩, shr, push1 ⟨2⟩, push1 ⟨7⟩, dup3, mod,
    push1 ⟨1⟩, shl, push2 ⟨805⟩, add, push1 ⟨30⟩]
  have rdAfterCopy0 := rdBeforeCopy0.codecopy 3
    (vyperERC20Bytecode.write
      (((⟨805⟩ : UInt256) +
        UInt256.shiftLeft (UInt256.mod (vyperRuntimeSelectorWord I) ⟨7⟩) ⟨1⟩).toNat)
      ByteArray.empty 30 2)
    (UInt256.ofNat 1)
    (by vyper_erc20_runtime_decode) mem_cost rfl (by decide) (by evm_ov)
  have rdAfterCopy := by
    simpa [vyperRuntimeSelectorWord, selectorMissDispatchMem, vyperDispatchSourceOfMod hmod]
      using rdAfterCopy0
  have rdBeforeJump := evm_run rdAfterCopy with [
    push0,
    raw mload 0 ⟨797⟩ (UInt256.ofNat 1)
      (by vyper_erc20_runtime_decode)
      mem_cost
      selectorMissDispatchMem_mload0
      (by decide) (by evm_ov)]
  exact ⟨_, _, rdBeforeJump.jump (by vyper_erc20_runtime_decode) (by decide +native) (by evm_ov)⟩

theorem erc20X_totalSupplyReach_of_mod5 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vyperERC20Bytecode)
    (hmod : (vyperRuntimeSelectorWord I).toNat % 7 = 5) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨769⟩
      [vyperRuntimeSelectorWord I] runtimeDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ) k C := by
  have rd0 := RD.initState (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode
  have rdBeforeCopy0 := evm_run rd0 with [
    push0, calldataload, push1 ⟨224⟩, shr, push1 ⟨2⟩, push1 ⟨7⟩, dup3, mod,
    push1 ⟨1⟩, shl, push2 ⟨805⟩, add, push1 ⟨30⟩]
  have rdAfterCopy0 := rdBeforeCopy0.codecopy 3
    (vyperERC20Bytecode.write
      (((⟨805⟩ : UInt256) +
        UInt256.shiftLeft (UInt256.mod (vyperRuntimeSelectorWord I) ⟨7⟩) ⟨1⟩).toNat)
      ByteArray.empty 30 2)
    (UInt256.ofNat 1)
    (by vyper_erc20_runtime_decode) mem_cost rfl (by decide) (by evm_ov)
  have rdAfterCopy := by
    simpa [vyperRuntimeSelectorWord, runtimeDispatchMem, vyperDispatchSourceOfMod hmod]
      using rdAfterCopy0
  have rdBeforeJump := evm_run rdAfterCopy with [
    push0,
    raw mload 0 ⟨769⟩ (UInt256.ofNat 1)
      (by vyper_erc20_runtime_decode)
      mem_cost
      runtimeDispatchMem_mload0
      (by decide) (by evm_ov)]
  exact ⟨_, _, rdBeforeJump.jump (by vyper_erc20_runtime_decode) (by decide +native) (by evm_ov)⟩

theorem erc20X_allowanceReach_of_mod6 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vyperERC20Bytecode)
    (hmod : (vyperRuntimeSelectorWord I).toNat % 7 = 6) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨681⟩
      [vyperRuntimeSelectorWord I] allowanceDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ) k C := by
  have rd0 := RD.initState (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode
  have rdBeforeCopy0 := evm_run rd0 with [
    push0, calldataload, push1 ⟨224⟩, shr, push1 ⟨2⟩, push1 ⟨7⟩, dup3, mod,
    push1 ⟨1⟩, shl, push2 ⟨805⟩, add, push1 ⟨30⟩]
  have rdAfterCopy0 := rdBeforeCopy0.codecopy 3
    (vyperERC20Bytecode.write
      (((⟨805⟩ : UInt256) +
        UInt256.shiftLeft (UInt256.mod (vyperRuntimeSelectorWord I) ⟨7⟩) ⟨1⟩).toNat)
      ByteArray.empty 30 2)
    (UInt256.ofNat 1)
    (by vyper_erc20_allowance_decode) mem_cost rfl (by decide) (by evm_ov)
  have rdAfterCopy := by
    simpa [vyperRuntimeSelectorWord, allowanceDispatchMem, vyperDispatchSourceOfMod hmod]
      using rdAfterCopy0
  have rdBeforeJump := evm_run rdAfterCopy with [
    push0,
    raw mload 0 ⟨681⟩ (UInt256.ofNat 1)
      (by vyper_erc20_allowance_decode)
      mem_cost
      allowanceDispatchMem_mload0
      (by decide) (by evm_ov)]
  exact ⟨_, _, rdBeforeJump.jump (by vyper_erc20_allowance_decode) (by decide +native) (by evm_ov)⟩

theorem erc20BalanceOfSelectorMiss {cA gh bl σ σ₀ A I} {g : Sat256}
    (hneq : vyperRuntimeSelectorWord I ≠ balanceOfSelectorWord)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨623⟩
      [vyperRuntimeSelectorWord I] balanceOfDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ) k C) :
    RDrev vyperERC20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd623⟩ := hreach
  have rd797 := evm_run rd623 with [
    jumpdest,
    raw push4 balanceOfSelectorWord (by vyper_erc20_balance_decode) (by evm_ov),
    dup2, xor, push2 ⟨797⟩,
    jumpiT (by simpa using u256_xor_ne_zero_of_ne hneq) (by vyper_erc20_balance_decode)]
  exact vyperRuntimeRevert797 (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) rd797 rfl (by norm_num)

theorem erc20ApproveSelectorMiss {cA gh bl σ σ₀ A I} {g : Sat256}
    (hneq : vyperRuntimeSelectorWord I ≠ approveSelectorWord)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨206⟩
      [vyperRuntimeSelectorWord I] approveDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ) k C) :
    RDrev vyperERC20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd206⟩ := hreach
  have rd797 := evm_run rd206 with [
    jumpdest,
    raw push4 approveSelectorWord (by vyper_erc20_approve_decode) (by evm_ov),
    dup2, xor, push2 ⟨797⟩,
    jumpiT (by simpa using u256_xor_ne_zero_of_ne hneq) (by vyper_erc20_approve_decode)]
  exact vyperRuntimeRevert797 (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) rd797 rfl (by norm_num)

theorem erc20TransferFromSelectorMiss {cA gh bl σ σ₀ A I} {g : Sat256}
    (hneq : vyperRuntimeSelectorWord I ≠ transferFromSelectorWord)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨331⟩
      [vyperRuntimeSelectorWord I] transferFromDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ) k C) :
    RDrev vyperERC20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd331⟩ := hreach
  have rd797 := evm_run rd331 with [
    jumpdest,
    raw push4 transferFromSelectorWord (by decide +native) (by evm_ov),
    dup2, xor, push2 ⟨797⟩,
    jumpiT (by simpa using u256_xor_ne_zero_of_ne hneq) (by decide +native)]
  exact vyperRuntimeRevert797 (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) rd797 rfl (by norm_num)

theorem erc20TransferSelectorMiss {cA gh bl σ σ₀ A I} {g : Sat256}
    (hneq : vyperRuntimeSelectorWord I ≠ transferSelectorWord)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨24⟩
      [vyperRuntimeSelectorWord I] transferDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ) k C) :
    RDrev vyperERC20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd24⟩ := hreach
  have rd797 := evm_run rd24 with [
    jumpdest,
    raw push4 transferSelectorWord (by vyper_erc20_transfer_decode) (by evm_ov),
    dup2, xor, push2 ⟨797⟩,
    jumpiT (by simpa using u256_xor_ne_zero_of_ne hneq) (by vyper_erc20_transfer_decode)]
  exact vyperRuntimeRevert797 (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) rd797 rfl (by norm_num)

theorem erc20TotalSupplySelectorMiss {cA gh bl σ σ₀ A I} {g : Sat256}
    (hneq : vyperRuntimeSelectorWord I ≠ totalSupplySelectorWord)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨769⟩
      [vyperRuntimeSelectorWord I] runtimeDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ) k C) :
    RDrev vyperERC20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd769⟩ := hreach
  have rd797 := evm_run rd769 with [
    jumpdest,
    raw push4 totalSupplySelectorWord (by vyper_erc20_runtime_decode) (by evm_ov),
    dup2, xor, push2 ⟨797⟩,
    jumpiT (by simpa using u256_xor_ne_zero_of_ne hneq) (by vyper_erc20_runtime_decode)]
  exact vyperRuntimeRevert797 (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) rd797 rfl (by norm_num)

theorem erc20AllowanceSelectorMiss {cA gh bl σ σ₀ A I} {g : Sat256}
    (hneq : vyperRuntimeSelectorWord I ≠ allowanceSelectorWord)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨681⟩
      [vyperRuntimeSelectorWord I] allowanceDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ) k C) :
    RDrev vyperERC20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd681⟩ := hreach
  have rd797 := evm_run rd681 with [
    jumpdest,
    raw push4 allowanceSelectorWord (by vyper_erc20_allowance_decode) (by evm_ov),
    dup2, xor, push2 ⟨797⟩,
    jumpiT (by simpa using u256_xor_ne_zero_of_ne hneq) (by vyper_erc20_allowance_decode)]
  exact vyperRuntimeRevert797 (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) rd797 rfl (by norm_num)

theorem erc20SelectorMissRuntime_mod4
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vyperERC20Bytecode)
    (hmod : (vyperRuntimeSelectorWord I).toNat % 7 = 4)
    (hdisp : dispatchMsg erc20Contract I.calldata = none) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, rd797⟩ := erc20X_selectorMissReach_of_mod4
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
    (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hmod
  exact (vyperRuntimeRevert797 (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
    (A := A) (I := I) (g := Sat256.ofUInt256 g) rd797 rfl (by norm_num))
    |>.reEquivNoDispatch hcode hdisp

theorem erc20TransferFromRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vyperERC20Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : ((⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact erc20TransferFromBodyCore hcode hwv hperm hsize
    (by
      have hcd : I.calldata.extract 0 4 = (⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ : ByteArray) :=
        (byteArray_eq_of_beq hsel).symm
      refine dispatchMsg_eq_some_of_split
        (pre := [ERC20.approveTransition, ERC20.totalSupplyTransition])
        (post := [ERC20.balanceOfTransition, ERC20.transferTransition, ERC20.allowanceTransition])
        rfl rfl ?_ (by rw [selectorOf, vyperERC20TransferFromSelectorBytes]; exact hsel)
      intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · rw [selectorOf, vyperERC20ApproveSelectorBytes, hcd]; decide
      · rw [selectorOf, vyperERC20TotalSupplySelectorBytes, hcd]; decide)
    hsel
    (erc20X_transferFromReach (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsel)
    hAccounts

theorem erc20NoDispatchRuntimeCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vyperERC20Bytecode)
    (hnm : ∀ i, i < 6 → (erc20SelBytes i == I.calldata.extract 0 4) = false) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hsz4 : 4 ≤ I.calldata.size
  · have hdisp : dispatchMsg erc20Contract I.calldata = none := erc20Dispatch_none_nomatch hnm
    set m : Nat := (vyperRuntimeSelectorWord I).toNat % 7 with hm
    have hm_lt : m < 7 := by
      rw [hm]
      exact Nat.mod_lt _ (by decide)
    interval_cases m
    · have hneq : vyperRuntimeSelectorWord I ≠ balanceOfSelectorWord := by
        exact vyperRuntimeSelectorWord_ne_of_selector_false hsz4 (by decide +native) (hnm 3 (by decide))
      exact (erc20BalanceOfSelectorMiss
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) hneq
        (erc20X_balanceOfReach_of_mod0
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
          (I := I) (g := Sat256.ofUInt256 g) hcode hm.symm)).reEquivNoDispatch hcode hdisp
    · have hneq : vyperRuntimeSelectorWord I ≠ approveSelectorWord := by
        exact vyperRuntimeSelectorWord_ne_of_selector_false hsz4 (by decide +native) (hnm 0 (by decide))
      exact (erc20ApproveSelectorMiss
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) hneq
        (erc20X_approveReach_of_mod1
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
          (I := I) (g := Sat256.ofUInt256 g) hcode hm.symm)).reEquivNoDispatch hcode hdisp
    · have hneq : vyperRuntimeSelectorWord I ≠ transferFromSelectorWord := by
        exact vyperRuntimeSelectorWord_ne_of_selector_false hsz4 (by decide +native) (hnm 2 (by decide))
      exact (erc20TransferFromSelectorMiss
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) hneq
        (erc20X_transferFromReach_of_mod2
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
          (I := I) (g := Sat256.ofUInt256 g) hcode hm.symm)).reEquivNoDispatch hcode hdisp
    · have hneq : vyperRuntimeSelectorWord I ≠ transferSelectorWord := by
        exact vyperRuntimeSelectorWord_ne_of_selector_false hsz4 (by decide +native) (hnm 4 (by decide))
      exact (erc20TransferSelectorMiss
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) hneq
        (erc20X_transferReach_of_mod3
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
          (I := I) (g := Sat256.ofUInt256 g) hcode hm.symm)).reEquivNoDispatch hcode hdisp
    · exact erc20SelectorMissRuntime_mod4 hcode hm.symm hdisp
    · have hneq : vyperRuntimeSelectorWord I ≠ totalSupplySelectorWord := by
        exact vyperRuntimeSelectorWord_ne_of_selector_false hsz4 (by decide +native) (hnm 1 (by decide))
      exact (erc20TotalSupplySelectorMiss
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) hneq
        (erc20X_totalSupplyReach_of_mod5
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
          (I := I) (g := Sat256.ofUInt256 g) hcode hm.symm)).reEquivNoDispatch hcode hdisp
    · have hneq : vyperRuntimeSelectorWord I ≠ allowanceSelectorWord := by
        exact vyperRuntimeSelectorWord_ne_of_selector_false hsz4 (by decide +native) (hnm 5 (by decide))
      exact (erc20AllowanceSelectorMiss
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) hneq
        (erc20X_allowanceReach_of_mod6
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
          (I := I) (g := Sat256.ofUInt256 g) hcode hm.symm)).reEquivNoDispatch hcode hdisp
  · have hshort : I.calldata.size < 4 := by omega
    have hdisp : dispatchMsg erc20Contract I.calldata = none := erc20Dispatch_none_short hshort
    set m : Nat := (vyperRuntimeSelectorWord I).toNat % 7 with hm
    have hm_lt : m < 7 := by
      rw [hm]
      exact Nat.mod_lt _ (by decide)
    interval_cases m
    · have hneq : vyperRuntimeSelectorWord I ≠ balanceOfSelectorWord := by
        exact vyperRuntimeSelectorWord_ne_of_short hshort (by decide +native)
      exact (erc20BalanceOfSelectorMiss
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) hneq
        (erc20X_balanceOfReach_of_mod0
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
          (I := I) (g := Sat256.ofUInt256 g) hcode hm.symm)).reEquivNoDispatch hcode hdisp
    · have hneq : vyperRuntimeSelectorWord I ≠ approveSelectorWord := by
        exact vyperRuntimeSelectorWord_ne_of_short hshort (by decide +native)
      exact (erc20ApproveSelectorMiss
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) hneq
        (erc20X_approveReach_of_mod1
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
          (I := I) (g := Sat256.ofUInt256 g) hcode hm.symm)).reEquivNoDispatch hcode hdisp
    · have hneq : vyperRuntimeSelectorWord I ≠ transferFromSelectorWord := by
        exact vyperRuntimeSelectorWord_ne_of_short hshort (by decide +native)
      exact (erc20TransferFromSelectorMiss
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) hneq
        (erc20X_transferFromReach_of_mod2
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
          (I := I) (g := Sat256.ofUInt256 g) hcode hm.symm)).reEquivNoDispatch hcode hdisp
    · have hneq : vyperRuntimeSelectorWord I ≠ transferSelectorWord := by
        exact vyperRuntimeSelectorWord_ne_of_short hshort (by decide +native)
      exact (erc20TransferSelectorMiss
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) hneq
        (erc20X_transferReach_of_mod3
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
          (I := I) (g := Sat256.ofUInt256 g) hcode hm.symm)).reEquivNoDispatch hcode hdisp
    · exact erc20SelectorMissRuntime_mod4 hcode hm.symm hdisp
    · have hneq : vyperRuntimeSelectorWord I ≠ totalSupplySelectorWord := by
        exact vyperRuntimeSelectorWord_ne_of_short hshort (by decide +native)
      exact (erc20TotalSupplySelectorMiss
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) hneq
        (erc20X_totalSupplyReach_of_mod5
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
          (I := I) (g := Sat256.ofUInt256 g) hcode hm.symm)).reEquivNoDispatch hcode hdisp
    · have hneq : vyperRuntimeSelectorWord I ≠ allowanceSelectorWord := by
        exact vyperRuntimeSelectorWord_ne_of_short hshort (by decide +native)
      exact (erc20AllowanceSelectorMiss
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) hneq
        (erc20X_allowanceReach_of_mod6
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
          (I := I) (g := Sat256.ofUInt256 g) hcode hm.symm)).reEquivNoDispatch hcode hdisp

theorem erc20NoDispatchRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vyperERC20Bytecode) (_hwv : I.weiValue = ⟨0⟩)
    (_hsize : I.calldata.size < UInt256.size) (_hperm : I.perm = true)
    (hnm : ∀ i, i < 6 → (erc20SelBytes i == I.calldata.extract 0 4) = false) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I :=
  erc20NoDispatchRuntimeCore hcode hnm

theorem erc20RuntimeNonPayableOfDispatch
    {t : TransitionDecl}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vyperERC20Bytecode)
    (hd : dispatchMsg erc20Contract I.calldata = some t)
    (hbody : ∀ callargs, ExecTransitionBody config erc20Contract
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) callargs t.body .reverted)
    (hrev : RDrev vyperERC20Bytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hdec : decodeCalldataWithMode config.abiDecodeMode (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata = none
  · exact hrev.reEquivDecodingFailed hcode hd hdec
  · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
    exact hrev.reEquivElim hcode fun _ _ hrevert =>
      reEquiv_execution hd hca (hbody callargs) (by rw [hrevert]; exact .revert rfl rfl)

theorem erc20ApproveNonPayableRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vyperERC20Bytecode) (hwv : I.weiValue ≠ ⟨0⟩)
    (hsel : ((⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, rd206⟩ := erc20X_approveReach
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
    (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsel
  have rd801 := evm_run rd206 with [
    jumpdest,
    raw push4 approveSelectorWord (by vyper_erc20_approve_decode) (by evm_ov),
    dup2, xor, push2 ⟨797⟩, jumpiNT (by decide +native),
    push1 ⟨68⟩, calldatasize, lt, callvalue, or, push2 ⟨801⟩,
    jumpiT (by
      simpa [u256_lor_comm] using
        (u256_lor_ne_zero_right
          (a := UInt256.lt (UInt256.ofNat I.calldata.size) ⟨68⟩)
          (b := I.weiValue) hwv))
      (by vyper_erc20_approve_decode)]
  exact erc20RuntimeNonPayableOfDispatch hcode (erc20Dispatch_approve hsel)
    (fun _ => bodyReverts_nonPayable (cfg := config) (contract := erc20Contract)
      (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) hwv)
    (vyperRuntimeRevert801 (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g) rd801 rfl (by norm_num))

theorem erc20TotalSupplyNonPayableRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vyperERC20Bytecode) (hwv : I.weiValue ≠ ⟨0⟩)
    (hsel : ((⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, rd769⟩ := erc20X_totalSupplyReach
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
    (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsel
  have rd801 := evm_run rd769 with [
    jumpdest,
    raw push4 totalSupplySelectorWord (by vyper_erc20_runtime_decode) (by evm_ov),
    dup2, xor, push2 ⟨797⟩, jumpiNT (by decide +native),
    callvalue, push2 ⟨801⟩,
    jumpiT hwv (by vyper_erc20_runtime_decode)]
  exact erc20RuntimeNonPayableOfDispatch hcode (erc20Dispatch_totalSupply hsel)
    (fun _ => bodyReverts_nonPayable (cfg := config) (contract := erc20Contract)
      (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) hwv)
    (vyperRuntimeRevert801 (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g) rd801 rfl (by norm_num))

theorem erc20Dispatch_transferFrom {cd : ByteArray}
    (hsel : ((⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg erc20Contract cd = some ERC20.transferFromTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [ERC20.approveTransition, ERC20.totalSupplyTransition])
    (post := [ERC20.balanceOfTransition, ERC20.transferTransition, ERC20.allowanceTransition])
    rfl rfl ?_ (by rw [selectorOf, vyperERC20TransferFromSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · rw [selectorOf, vyperERC20ApproveSelectorBytes, hcd]; decide
  · rw [selectorOf, vyperERC20TotalSupplySelectorBytes, hcd]; decide

theorem erc20TransferFromNonPayableRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vyperERC20Bytecode) (hwv : I.weiValue ≠ ⟨0⟩)
    (hsel : ((⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, rd331⟩ := erc20X_transferFromReach
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
    (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsel
  have rd801 := evm_run rd331 with [
    jumpdest,
    raw push4 transferFromSelectorWord (by decide +native) (by evm_ov),
    dup2, xor, push2 ⟨797⟩, jumpiNT (by decide +native),
    push1 ⟨100⟩, calldatasize, lt, callvalue, or, push2 ⟨801⟩,
    jumpiT (by
      simpa [u256_lor_comm] using
        (u256_lor_ne_zero_right
          (a := UInt256.lt (UInt256.ofNat I.calldata.size) ⟨100⟩)
          (b := I.weiValue) hwv))
      (by decide +native)]
  exact erc20RuntimeNonPayableOfDispatch hcode (erc20Dispatch_transferFrom hsel)
    (fun _ => bodyReverts_nonPayable (cfg := config) (contract := erc20Contract)
      (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) hwv)
    (vyperRuntimeRevert801 (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g) rd801 rfl (by norm_num))

theorem erc20BalanceOfNonPayableRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vyperERC20Bytecode) (hwv : I.weiValue ≠ ⟨0⟩)
    (hsel : ((⟨#[0x70, 0xa0, 0x82, 0x31]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, rd623⟩ := erc20X_balanceOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
    (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsel
  have rd801 := evm_run rd623 with [
    jumpdest,
    raw push4 balanceOfSelectorWord (by vyper_erc20_balance_decode) (by evm_ov),
    dup2, xor, push2 ⟨797⟩, jumpiNT (by decide +native),
    push1 ⟨36⟩, calldatasize, lt, callvalue, or, push2 ⟨801⟩,
    jumpiT (by
      simpa [u256_lor_comm] using
        (u256_lor_ne_zero_right
          (a := UInt256.lt (UInt256.ofNat I.calldata.size) ⟨36⟩)
          (b := I.weiValue) hwv))
      (by vyper_erc20_balance_decode)]
  exact erc20RuntimeNonPayableOfDispatch hcode (erc20Dispatch_balanceOf hsel)
    (fun _ => bodyReverts_nonPayable (cfg := config) (contract := erc20Contract)
      (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) hwv)
    (vyperRuntimeRevert801 (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g) rd801 rfl (by norm_num))

theorem erc20TransferNonPayableRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vyperERC20Bytecode) (hwv : I.weiValue ≠ ⟨0⟩)
    (hsel : ((⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, rd24⟩ := erc20X_transferReach
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
    (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsel
  have rd801 := evm_run rd24 with [
    jumpdest,
    raw push4 transferSelectorWord (by vyper_erc20_transfer_decode) (by evm_ov),
    dup2, xor, push2 ⟨797⟩, jumpiNT (by decide +native),
    push1 ⟨68⟩, calldatasize, lt, callvalue, or, push2 ⟨801⟩,
    jumpiT (by
      simpa [u256_lor_comm] using
        (u256_lor_ne_zero_right
          (a := UInt256.lt (UInt256.ofNat I.calldata.size) ⟨68⟩)
          (b := I.weiValue) hwv))
      (by vyper_erc20_transfer_decode)]
  exact erc20RuntimeNonPayableOfDispatch hcode (erc20Dispatch_transfer hsel)
    (fun _ => bodyReverts_nonPayable (cfg := config) (contract := erc20Contract)
      (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) hwv)
    (transferRevertStub (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (g := Sat256.ofUInt256 g) rd801 rfl (by norm_num))

theorem erc20AllowanceNonPayableRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vyperERC20Bytecode) (hwv : I.weiValue ≠ ⟨0⟩)
    (hsel : ((⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, rd681⟩ := erc20X_allowanceReach
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
    (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsel
  have rd801 := evm_run rd681 with [
    jumpdest,
    raw push4 allowanceSelectorWord (by vyper_erc20_allowance_decode) (by evm_ov),
    dup2, xor, push2 ⟨797⟩, jumpiNT (by decide +native),
    push1 ⟨68⟩, calldatasize, lt, callvalue, or, push2 ⟨801⟩,
    jumpiT (by
      simpa [u256_lor_comm] using
        (u256_lor_ne_zero_right
          (a := UInt256.lt (UInt256.ofNat I.calldata.size) ⟨68⟩)
          (b := I.weiValue) hwv))
      (by vyper_erc20_allowance_decode)]
  exact erc20RuntimeNonPayableOfDispatch hcode (erc20Dispatch_allowance hsel)
    (fun _ => bodyReverts_nonPayable (cfg := config) (contract := erc20Contract)
      (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) hwv)
    (vyperRuntimeRevert801 (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g) rd801 rfl (by norm_num))

theorem erc20NonPayableRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vyperERC20Bytecode) (hwv : I.weiValue ≠ ⟨0⟩)
    (_hsize : I.calldata.size < UInt256.size) (_hperm : I.perm = true)
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases h0 : ((⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ : ByteArray) == I.calldata.extract 0 4) = true
  · exact erc20ApproveNonPayableRuntime hcode hwv h0
  · by_cases h1 : ((⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ : ByteArray) == I.calldata.extract 0 4) = true
    · exact erc20TotalSupplyNonPayableRuntime hcode hwv h1
    · by_cases h2 : ((⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ : ByteArray) == I.calldata.extract 0 4) = true
      · exact erc20TransferFromNonPayableRuntime hcode hwv h2
      · by_cases h3 : ((⟨#[0x70, 0xa0, 0x82, 0x31]⟩ : ByteArray) == I.calldata.extract 0 4) = true
        · exact erc20BalanceOfNonPayableRuntime hcode hwv h3
        · by_cases h4 : ((⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ : ByteArray) == I.calldata.extract 0 4) = true
          · exact erc20TransferNonPayableRuntime hcode hwv h4
          · by_cases h5 : ((⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ : ByteArray) == I.calldata.extract 0 4) = true
            · exact erc20AllowanceNonPayableRuntime hcode hwv h5
            · exact erc20NoDispatchRuntimeCore hcode (fun i hi => by
                interval_cases i
                · simpa using h0
                · simpa using h1
                · simpa using h2
                · simpa using h3
                · simpa using h4
                · simpa using h5)

/-- Runtime equivalence for the Vyper 0.4.3 ERC20 runtime bytecode.

The dispatcher routing is explicit here.  The proven Vyper function-body obligations cover
`approve`, `totalSupply`, `balanceOf`, `transfer`, and `allowance`; only `transferFrom`
success remains isolated above as a bytecode obligation. -/
theorem runtimeCorrect :
    runtimeEquivalence config vyperERC20Bytecode contract := by
  refine ⟨fun cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm hAccounts => ?_⟩
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases h0 : ((⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ : ByteArray) == I.calldata.extract 0 4) = true
    · exact erc20ApproveRuntimeSuccess hcode hwv hperm hsize h0 hAccounts
    · by_cases h1 : ((⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ : ByteArray) == I.calldata.extract 0 4) = true
      · exact erc20TotalSupplyRuntime hcode hwv h1 hAccounts
      · by_cases h2 : ((⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ : ByteArray) == I.calldata.extract 0 4) = true
        · exact erc20TransferFromRuntime hcode hwv hperm hsize h2 hAccounts
        · by_cases h3 : ((⟨#[0x70, 0xa0, 0x82, 0x31]⟩ : ByteArray) == I.calldata.extract 0 4) = true
          · exact erc20BalanceOfRuntimeSuccess hcode hwv hsize h3 hAccounts
          · by_cases h4 : ((⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ : ByteArray) == I.calldata.extract 0 4) = true
            · exact erc20TransferRuntimeSuccess hcode hwv hperm hsize h4 hAccounts
            · by_cases h5 : ((⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ : ByteArray) == I.calldata.extract 0 4) = true
              · exact erc20AllowanceRuntimeSuccess hcode hwv hsize h5 hAccounts
              · refine erc20NoDispatchRuntime hcode hwv hsize hperm ?_
                intro i hi
                interval_cases i
                · simpa using h0
                · simpa using h1
                · simpa using h2
                · simpa using h3
                · simpa using h4
                · simpa using h5
  · exact erc20NonPayableRuntime hcode hwv hsize hperm hAccounts

/-- Constructor equivalence for the Vyper 0.4.3 ERC20 deployment bytecode. -/
theorem constructorCorrect :
    constructorEquivalence config vyperERC20Initcode contract vyperERC20Bytecode := by
  refine constructorEquivalence.intro ?_
  intro createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I
      args deployedInitcode hdeploy hcode hcalldata hperm hσ
  rcases erc20Deployment_shape hdeploy with ⟨initialSupply, hargs, h0, hlt, hdeployed⟩
  subst args
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hcodeCtor : I.code = erc20CtorCode (EVM.word initialSupply.toNat) := by
      rw [hcode, hdeployed]
      unfold erc20CtorCode
      rfl
    have hrd := erc20InitcodeSuccess
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) (EVM.word initialSupply.toNat) hcodeCtor hperm hwv
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
            (sstoreAccountMap I.codeOwner σ_evm (erc20BalanceOfSlot (.address I.source))
              (EVM.word initialSupply.toNat))
            ⟨2⟩ (EVM.word initialSupply.toNat) :=
        congrArg Prod.snd hacc
      rw [hcA, hσ'] at hsuccess
      refine constructorEquivalenceFor.execution hsuccess
        (erc20SolmCtorExecSuccess
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (g := g) (A := A) (I := I)
          initialSupply h0 hlt hwv) ?_
      refine ctorResultEquiv.success rfl rfl ?_ ?_ rfl
      · simp only [erc20CtorPostState, erc20CtorBalancePostState, storageStore_createdAccounts,
          initState]
      · simp only [erc20CtorPostState, erc20CtorBalancePostState, storageStore_accountMap,
          storageStore_executionEnv, initState]
        exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨2⟩ (EVM.word initialSupply.toNat)
          (accountMapEquiv_sstoreAccountMap I.codeOwner
            (erc20BalanceOfSlot (.address I.source)) (EVM.word initialSupply.toNat) hσ)
  · let tail := (EVM.Word.toBytesBE (EVM.word initialSupply.toNat)).toByteArray
    have hcodeTail : I.code = vyperERC20Initcode ++ tail := by
      rw [hcode, hdeployed]
    have hrd := erc20InitcodeNonpayableRevert
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) tail hcodeTail hwv
    rcases hrd.xiResult hcodeTail with hOOG | ⟨g', o, hrev⟩
    · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
    · refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hrev)
        (erc20SolmCtorExecReverts_nonpayable
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (g := g) (A := A) (I := I)
          initialSupply hwv) ?_
      exact ctorResultEquiv.revert rfl rfl

/-- Full Vyper ERC20 equivalence, combining constructor and runtime obligations. -/
theorem contractCorrect :
    contractEquivalence config vyperERC20Initcode vyperERC20Bytecode contract :=
  contractEquivalence.intro constructorCorrect runtimeCorrect

end VyperERC20
