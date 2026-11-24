import Benchmarks.CurveVault.AllowanceAdjustPrepare
import Benchmarks.CurveVault.ApproveArguments

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultAdjustCallPc (increase : Bool) : UInt256 := if increase then UInt256.ofNat 6145 else UInt256.ofNat 6286
def vaultAdjustReturnPc (increase : Bool) : UInt256 := if increase then UInt256.ofNat 6169 else UInt256.ofNat 6310
abbrev vaultAdjustFinishBody : List Stmt := (vaultAdjustFunction true).body.drop 3

theorem vaultAdjustReturn (increase : Bool) {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 4 ≤ 1024) (hperm : I.perm = true)
    (h : RD fork vaultBytecode I g s0 (vaultAdjustReturnPc increase) R mem aw rdata σ k C) :
    RDret fork vaultBytecode g s0 (tstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) (⟨1⟩ : UInt256).toByteArray := by
  have hret : RDret fork vaultBytecode g s0 (tstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
      (((⟨1⟩ : UInt256).toByteArray.write 0 mem 288 32).readWithPadding 288 32) := by
    cases increase
    · exact vaultBlocks.vault_block_6310 hstack hperm h
    · exact vaultBlocks.vault_block_6169 hstack hperm h
  rwa [toByteArray_write_read_back_of_gap _ _ _
    (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 288 (by omega)))] at hret

theorem vaultAdjustCall (increase : Bool) {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {spender value : UInt256} {R : List UInt256}
    (hsize : 288 ≤ mem.size) (hms : memLoad (UInt256.ofNat 192) mem = spender)
    (hmv : memLoad (UInt256.ofNat 256) mem = value) (hstack : R.length + 6 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (vaultAdjustCallPc increase) R mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork vaultBytecode I g s0 (UInt256.ofNat 7939) (vaultAdjustReturnPc increase :: R)
      (vaultApproveArguments mem (UInt256.ofNat I.source.val) spender value) aw' rdata σ k' C' := by
  let owner := UInt256.ofNat I.source.val
  let mem0 := owner.toByteArray.write 0 mem 64 32
  let mem1 := spender.toByteArray.write 0 mem0 96 32
  have hsp : memLoad (UInt256.ofNat 192) mem0 = spender := by
    rw [memLoad_above_write _ _ 64 192 (by rw [toByteArray_size]) (by omega) (by omega) (by omega) (by decide +kernel), hms]
  have hv : memLoad (UInt256.ofNat 256) mem1 = value := by
    have hs0 : mem0.size = mem.size := by
      change (writeWord mem 64 owner).size = _
      rw [writeWord_size _ _ _ (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 64 (by omega))), Nat.max_eq_left (by omega)]
    rw [memLoad_above_write _ _ 96 256 (by rw [toByteArray_size]) (by omega) (by omega) (by rw [hs0]; omega) (by decide +kernel),
      memLoad_above_write _ _ 64 256 (by rw [toByteArray_size]) (by omega) (by omega) hsize (by decide +kernel), hmv]
  have rd : ∃ aw' k' C', RD fork vaultBytecode I g s0 (UInt256.ofNat 7939) (vaultAdjustReturnPc increase :: R)
      ((memLoad (UInt256.ofNat 256) ((memLoad (UInt256.ofNat 192) mem0).toByteArray.write 0 mem0 96 32)).toByteArray.write 0
        ((memLoad (UInt256.ofNat 192) mem0).toByteArray.write 0 mem0 96 32) 128 32) aw' rdata σ k' C' := by
    cases increase
    · exact vaultBlocks.vault_block_6286_packed (by omega) (by native_decide) h
    · exact vaultBlocks.vault_block_6145_packed (by omega) (by native_decide) h
  rw [hsp, hv] at rd
  exact rd

theorem vaultAdjustFinish (increase : Bool) {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {locals : Store} {spender old value : UInt256} {R : List UInt256}
    (hs : SourceState s0 I σ evm) (hsize : 288 ≤ mem.size)
    (hsp : locals.get? "_spender" = some (.address (AccountAddress.ofNat spender.toNat)))
    (hc : locals.get? "cached_allowance" = some (.int (Int.ofNat old.toNat)))
    (hv : locals.get? "allowance_" = some (.int (Int.ofNat value.toNat)))
    (hms : memLoad (UInt256.ofNat 192) mem = spender)
    (hmc : memLoad (UInt256.ofNat 224) mem = old) (hmv : memLoad (UInt256.ofNat 256) mem = value)
    (hcanon : spender.toNat < EVM.addressModulus) (hperm : I.perm = true) (hstack : R.length + 6 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (vaultAdjustFinishPc increase) R mem aw rdata σ k C) :
    ∃ (evm' : State) (σ' : AccountMap) (locals' : Store),
      ExecBlock fork config {contract := contract, locals := locals} evm vaultAdjustFinishBody
        (.returned {contract := contract, locals := locals'} evm' (some [.bool true])) ∧
      SourceState s0 I σ' evm' ∧
      RDret fork vaultBytecode g s0 (tstoreAccountMap I.codeOwner σ' ⟨0⟩ ⟨0⟩) (⟨1⟩ : UInt256).toByteArray := by
  have hevalC := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm) hc
  have hevalV := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm) hv
  by_cases heq : value = old
  · have hcond : UInt256.eq (memLoad (UInt256.ofNat 256) mem) (memLoad (UInt256.ofNat 224) mem) ≠ ⟨0⟩ := by
      rw [hmv, hmc, heq, u256_eq_refl]; decide +kernel
    have rdReturn : ∃ aw' k' C', RD fork vaultBytecode I g s0 (vaultAdjustReturnPc increase) R mem aw' rdata σ k' C' := by
      cases increase
      · exact vaultBlocks.vault_block_6273_taken_packed (by omega) hcond (by native_decide) h
      · exact vaultBlocks.vault_block_6132_taken_packed (by omega) hcond (by native_decide) h
    obtain ⟨aw', k', C', rd⟩ := rdReturn
    refine ⟨evm, σ, locals, ?_, hs, vaultAdjustReturn increase (by omega) hperm rd⟩
    exact ExecBlock.consNormal (ExecStmt.iteFalse
      (evalExpr_ne_int_false hevalV hevalC (by rw [heq])) ExecBlock.nil) <|
      ExecBlock.consReturn (ExecStmt.return (by simp [evalExprs?, evalExpr?, EvalResult.bind, pure, bind]))
  · have hcond : UInt256.eq (memLoad (UInt256.ofNat 256) mem) (memLoad (UInt256.ofNat 224) mem) = ⟨0⟩ := by
      rw [hmv, hmc]; exact u256_eq_of_ne heq
    have rdCall : ∃ aw' k' C', RD fork vaultBytecode I g s0 (vaultAdjustCallPc increase) R mem aw' rdata σ k' C' := by
      cases increase
      · exact vaultBlocks.vault_block_6273_fallthrough_packed (by omega) hcond h
      · exact vaultBlocks.vault_block_6132_fallthrough_packed (by omega) hcond h
    obtain ⟨aw0, k0, C0, rdCall⟩ := rdCall
    obtain ⟨aw1, k1, C1, rdApprove⟩ := vaultAdjustCall increase hsize hms hmv hstack rdCall
    obtain ⟨hsizeArgs, hmo, hms', hmv'⟩ := vaultApproveArguments_reads mem (UInt256.ofNat I.source.val) spender value
    obtain ⟨evm', σ', aw2, k2, C2, hcallee, hs', rdReturn⟩ := vaultApproveRoutine hs hsizeArgs hmo hms' hmv'
      (addressWord_canonical I.source) hcanon hperm hstack (by cases increase <;> native_decide) rdApprove
    rw [addressWord_roundtrip] at hcallee
    have hargs : evalExprs? config {contract := contract, locals := locals} evm
        [.env .caller, .var "_spender", .var "allowance_"] =
        .ok [.address I.source, .address (AccountAddress.ofNat spender.toNat), .int (Int.ofNat value.toNat)] := by
      simp only [evalExprs?, evalExpr?, envValue, hs.env, hsp, hv, EvalResult.ofOption, EvalResult.bind, pure, bind]
    have hcall := internalCallFunctionReturn (caller := {contract := contract, locals := locals})
      (callee := vaultApproveFunction) (name := "_approve") (retVar := "__c0") hargs rfl rfl hcallee
    refine ⟨evm', σ', locals.insert "__c0" .unit, ?_, hs', vaultAdjustReturn increase (by omega) hperm rdReturn⟩
    exact ExecBlock.consNormal (ExecStmt.iteTrue
      (evalExpr_ne_int_true hevalV hevalC (fun hn => heq (u256_inj (Int.ofNat.inj hn))))
      (ExecBlock.consNormal hcall ExecBlock.nil)) <|
      ExecBlock.consReturn (ExecStmt.return (by simp [evalExprs?, evalExpr?, EvalResult.bind, pure, bind]))

end Benchmarks.CurveVault
