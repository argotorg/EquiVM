import Benchmarks.CurveVault.SetMaxGuard

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultSetMaxRoutine {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm) (hbase : locals.get? "_factory" = none)
    (hmax : locals.get? "maxSupply" = none)
    (hv : locals.get? "_max_supply" = some (.int (Int.ofNat (calldataWord I.calldata 4).toNat)))
    (hfactory : (codeOwnerStorageWord I σ ⟨4⟩).toNat < EVM.addressModulus)
    (hperm : I.perm = true) (hstack : R.length + 7 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 861) R mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (locals' : Store),
      ExecFuncBody fork config {contract := contract, locals := locals} (vaultSetLock evm ⟨1⟩) vaultSetMaxFunction.body
        (.returned {contract := contract, locals := locals'} evm' none) ∧
      SourceState s0 I σ' evm' ∧
      RDret fork vaultBytecode g s0 (tstoreAccountMap I.codeOwner σ' ⟨0⟩ ⟨0⟩) ByteArray.empty) ∨
    (ExecFuncBody fork config {contract := contract, locals := locals} (vaultSetLock evm ⟨1⟩)
      vaultSetMaxFunction.body .reverted ∧ RDrev fork vaultBytecode g s0) := by
  rcases vaultSetMaxAdminCall hs hbase hfactory hperm hstack h with
    ⟨evm1, σ1, out, aw1, k1, C1, hcanon, hfactory1, hcall, hs1, rd932⟩ | ⟨hcall, hrev⟩
  swap
  · exact Or.inr ⟨ExecFuncBody.execBlockRevert (ExecBlock.consRevert hcall), hrev⟩
  let locals1 := locals.insert "factory_admin" (.address (AccountAddress.ofNat (Reasoning.VyperCalls.retWord out).toNat))
  have hbase1 : locals1.get? "_factory" = none := by
    dsimp only [locals1]
    rw [store_get_ne locals _ (by decide +kernel)]
    exact hbase
  have hmax1 : locals1.get? "maxSupply" = none := by
    dsimp only [locals1]
    rw [store_get_ne locals _ (by decide +kernel)]
    exact hmax
  have hv1 : locals1.get? "_max_supply" = some (.int (Int.ofNat (calldataWord I.calldata 4).toNat)) := by
    dsimp only [locals1]
    rw [store_get_ne locals _ (by decide +kernel)]
    exact hv
  have ha1 : locals1.get? "factory_admin" =
      some (.address (AccountAddress.ofNat (Reasoning.VyperCalls.retWord out).toNat)) := by simp [locals1]
  rcases vaultSetMaxGuard hs1 hbase1 ha1 hcanon hfactory1 (by omega) rd932 with
    ⟨hguard, aw2, k2, C2, rd966⟩ | ⟨hguard, hrev⟩
  swap
  · exact Or.inr ⟨ExecFuncBody.execBlockRevert (ExecBlock.consNormal hcall
      (ExecBlock.consRevert (ExecStmt.requireFalse hguard))), hrev⟩
  let value := calldataWord I.calldata 4
  let evm2 := Stele.EVM.storageStore evm1 I.codeOwner ⟨5⟩ value
  let σ2 := sstoreAccountMap I.codeOwner σ1 ⟨5⟩ value
  have hs2 : SourceState s0 I σ2 evm2 := hs1.storageWrite _ _
  have hwrite : ExecStmt fork config {contract := contract, locals := locals1} evm1 vaultSetMaxFunction.body[2]!
      (.ok {contract := contract, locals := locals1} evm2) := by
    apply ExecStmt.assign (hperm := Or.inr ((congrArg ExecutionEnv.perm hs1.env).trans hperm)) (evalExpr_varUInt256 hv1)
    simpa only [hs1.env] using vaultAssignScalarUint256 evm1 locals1 "maxSupply" ⟨5⟩ value hmax1 rfl rfl (by decide +kernel)
  have hret := vaultBlocks.vault_block_966 (by omega) hperm rd966
  refine Or.inl ⟨evm2, σ2, locals1, ?_, hs2, hret⟩
  apply ExecFuncBody.execBlockOK
  apply ExecBlock.consNormal hcall
  apply ExecBlock.consNormal (ExecStmt.requireTrue hguard)
  apply ExecBlock.consNormal hwrite
  exact ExecBlock.consNormal (ExecStmt.emit (fork := fork) (hperm := (congrArg ExecutionEnv.perm hs2.env).trans hperm) (evalExprs?_singleton (evalExpr_varUInt256 hv1))) ExecBlock.nil

end Benchmarks.CurveVault
