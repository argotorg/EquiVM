import Benchmarks.CurveVault.CreditAfterController
import Benchmarks.CurveVault.MutatingLock

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultCreditRoutine (isDeposit : Bool) {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {receiver : UInt256} {R : List UInt256}
    (hs : SourceState s0 I σ evm) (hsize : 608 ≤ mem.size)
    (hmr : memLoad (UInt256.ofNat 576) mem = receiver)
    (hcanon : receiver.toNat < EVM.addressModulus) (hperm : I.perm = true)
    (hstack : R.length + 14 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat (if isDeposit then 2169 else 3172)) R mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (locals' : Store) (value : UInt256),
      ExecFuncBody fork config {contract := contract, locals := vaultCreditLocals isDeposit (AccountAddress.ofNat receiver.toNat) (calldataWord I.calldata 4)}
        (vaultSetLock evm ⟨1⟩) (vaultCreditFunction isDeposit).body
        (.returned {contract := contract, locals := locals'} evm' (some [.int (Int.ofNat value.toNat)])) ∧
      SourceState s0 I σ' evm' ∧
      RDret fork vaultBytecode g s0 (tstoreAccountMap I.codeOwner σ' ⟨0⟩ ⟨0⟩) value.toByteArray) ∨
    (ExecFuncBody fork config {contract := contract, locals := vaultCreditLocals isDeposit (AccountAddress.ofNat receiver.toNat) (calldataWord I.calldata 4)}
      (vaultSetLock evm ⟨1⟩) (vaultCreditFunction isDeposit).body .reverted ∧ RDrev fork vaultBytecode g s0) := by
  let evm0 := vaultSetLock evm ⟨1⟩
  let σ0 := tstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨1⟩
  let controller := codeOwnerStorageWord I σ0 ⟨3⟩
  let locals := vaultCreditLocals isDeposit (AccountAddress.ofNat receiver.toNat) (calldataWord I.calldata 4)
  let mem0 := controller.toByteArray.write 0 mem 608 32
  have hs0 : SourceState s0 I σ0 evm0 := by
    unfold evm0 vaultSetLock
    rw [hs.env]
    exact sourceStateTransientWrite hs ⟨0⟩ ⟨1⟩
  have hprep :
      (ExecBlock fork config {contract := contract, locals := locals} evm0
        ((vaultCreditFunction isDeposit).body.take (if isDeposit then 0 else 1))
        (.ok {contract := contract, locals := locals} evm0) ∧
        ∃ aw0 k0 C0, RD fork vaultBytecode I g s0 (UInt256.ofNat 6772)
          (UInt256.ofNat 672 :: UInt256.ofNat (if isDeposit then 2190 else 3320) :: R)
          mem0 aw0 rdata σ0 k0 C0) ∨
      (ExecFuncBody fork config {contract := contract, locals := locals} evm0
        (vaultCreditFunction isDeposit).body .reverted ∧ RDrev fork vaultBytecode g s0) := by
    cases isDeposit
    · have hv : locals.get? "_shares" = some (.int (Int.ofNat (calldataWord I.calldata 4).toNat)) :=
        store_get_self _ _ _
      have heval := evalExpr_gt_zero (evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm0) hv)
      by_cases hz : calldataWord I.calldata 4 = ⟨0⟩
      · obtain ⟨_, _, _, rdFail⟩ := vaultBlocks.vault_block_3172_fallthrough_packed (by omega) hperm hz h
        refine Or.inr ⟨ExecFuncBody.execBlockRevert (ExecBlock.consRevert (ExecStmt.requireFalse ?_)),
          vaultBlocks.vault_block_3183 (by omega) rdFail⟩
        simpa only [hz, show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.lt_irrefl, decide_false] using heval
      have hpos : 0 < (calldataWord I.calldata 4).toNat := by
        have hne : (calldataWord I.calldata 4).toNat ≠ 0 := fun heq => hz (u256_inj heq)
        omega
      obtain ⟨aw0, k0, C0, rdCache⟩ := vaultBlocks.vault_block_3172_taken_packed (by omega) hperm hz (by native_decide) h
      obtain ⟨aw1, k1, C1, rdAssets⟩ := vaultBlocks.vault_block_3302_packed (by omega) (by native_decide) rdCache
      exact Or.inl ⟨ExecBlock.consNormal (ExecStmt.requireTrue
        (by simpa only [hpos, decide_true] using heval)) ExecBlock.nil, aw1, k1, C1, rdAssets⟩
    · obtain ⟨aw0, k0, C0, rdAssets⟩ := vaultBlocks.vault_block_2169_packed (by omega) hperm (by native_decide) h
      exact Or.inl ⟨ExecBlock.nil, aw0, k0, C0, rdAssets⟩
  rcases hprep with ⟨hprefix, aw0, k0, C0, rdAssets⟩ | hrev
  swap
  · exact Or.inr hrev
  have hgap : 608 - mem.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 608 (by omega))
  have hsize0 : 640 ≤ mem0.size := toByteArray_write_size_ge_off_add32 _ _ 608 hgap
  have hr0 : memLoad (UInt256.ofNat 576) mem0 = receiver := by
    rw [memLoad_below_write _ _ 608 576 hsize (by omega) hgap (by decide +kernel), hmr]
  have hc0 : memLoad (UInt256.ofNat 608) mem0 = controller :=
    memLoad_write_back _ _ 608 (by decide +kernel) hgap
  rcases vaultCreditAfterController isDeposit hs0 hsize0 hr0 hc0 hcanon hperm hstack rdAssets with
    ⟨evm1, σ1, locals1, value, hrest, hs1, hret⟩ | ⟨hrest, hrev⟩
  · refine Or.inl ⟨evm1, σ1, locals1, value, ExecFuncBody.execBlockRet ?_, hs1, hret⟩
    simpa only [List.take_append_drop] using execBlock_append hprefix hrest
  · refine Or.inr ⟨ExecFuncBody.execBlockRevert ?_, hrev⟩
    simpa only [List.take_append_drop] using execBlock_append hprefix hrest

end Benchmarks.CurveVault
