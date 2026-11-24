import Benchmarks.CurveVault.AvailableBalanceInternal
import Benchmarks.CurveVault.ConvertSharesInternal
import Benchmarks.CurveVault.MaxRedeemArguments
import Benchmarks.CurveVault.BalanceStorage
import Benchmarks.CurveVault.RuntimeBlocks_017

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

abbrev vaultMaxRedeemFunction : FunctionDecl := contract.functions[17]!

theorem vaultMaxRedeemReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {owner shares : UInt256}
    (hsize : 64 ≤ mem.size) (howner : memLoad (UInt256.ofNat 576) mem = owner)
    (hshares : memLoad (UInt256.ofNat 640) mem = shares)
    (hcanon : owner.toNat < EVM.addressModulus) (hstack : R.length + 6 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 4888) R mem aw rdata σ k C) :
    RDret fork vaultBytecode g s0 σ
      (wordMin shares (codeOwnerStorageWord I σ
        (vyperMappingSlot ⟨13⟩ (.address (AccountAddress.ofNat owner.toNat))))).toByteArray := by
  have hhash := vyperHashMem_address ⟨13⟩ owner mem hsize hcanon
  have hret := vaultBlocks.vault_block_4888 hstack h
  let key := keccakWord ⟨0⟩ (UInt256.ofNat 64)
    (wordAt0Mem ⟨13⟩ (wordAt32Mem (memLoad (UInt256.ofNat 576) mem) mem))
  change RDret fork vaultBytecode g s0 σ
    (((UInt256.xor (UInt256.mul (UInt256.lt (memLoad (UInt256.ofNat 640) mem)
      (codeOwnerStorageWord I σ key)) (UInt256.xor (codeOwnerStorageWord I σ key)
        (memLoad (UInt256.ofNat 640) mem))) (codeOwnerStorageWord I σ key)).toByteArray.write
      0 (wordAt0Mem ⟨13⟩ (wordAt32Mem (memLoad (UInt256.ofNat 576) mem) mem)) 768 32).readWithPadding 768 32) at hret
  dsimp only [key] at hret
  rw [howner, hshares, hhash, branchlessMin, toByteArray_write_read_back_of_gap _ _ _
    (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 768 (by norm_num)))] at hret
  exact hret

theorem vaultMaxRedeemRoutine {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {locals : Store} {owner : UInt256}
    (hs : SourceState s0 I σ evm) (hsize : 608 ≤ mem.size)
    (howner : memLoad (UInt256.ofNat 576) mem = owner)
    (hcanon : owner.toNat < EVM.addressModulus)
    (hbase : locals.get? "balanceOf" = none)
    (harg : locals.get? "_owner" = some (.address (AccountAddress.ofNat owner.toNat)))
    (hstack : R.length + 14 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 4808) R mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (locals' : Store) (value : UInt256),
      ExecFuncBody fork config {contract := contract, locals := locals} evm vaultMaxRedeemFunction.body
        (.returned {contract := contract, locals := locals'} evm' (some [.int (Int.ofNat value.toNat)])) ∧
      SourceState s0 I σ' evm' ∧ RDret fork vaultBytecode g s0 σ' value.toByteArray) ∨
    (ExecFuncBody fork config {contract := contract, locals := locals} evm vaultMaxRedeemFunction.body .reverted ∧
      RDrev fork vaultBytecode g s0) := by
  have hgap (d : Nat) (hd : d < 1024) (m : ByteArray) : d - m.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize d (by omega))
  have rd7819 := vaultBlocks.vault_block_4808 (by omega) (by native_decide) h
  rcases vaultAvailableBalanceRoutine hs (by omega) (by native_decide) rd7819 with
    ⟨evm0, σ0, calleeLocals0, scratch0, available, aw0, out0, k0, C0, havailable, hs0, hframe0, rd4818⟩ | ⟨havailable, hrev⟩
  swap
  · refine Or.inr ⟨ExecFuncBody.execBlockRevert ?_, hrev⟩
    exact ExecBlock.consRevert (internalCallFunctionRevert (callee := vaultAvailableBalanceFunction)
      (argVals := []) (by simp [evalExprs?, pure]) rfl rfl havailable)
  let locals0 := locals.insert "__c0" (.int (Int.ofNat available.toNat))
  let mem0 := available.toByteArray.write 0 scratch0 608 32
  have hcall0 := internalCallFunctionReturn (caller := {contract := contract, locals := locals})
    (callee := vaultAvailableBalanceFunction) (name := "_available_balance") (args := []) (argVals := [])
    (retVar := "__c0") (by simp [evalExprs?, pure]) rfl rfl havailable
  have hsize0 : 640 ≤ mem0.size := toByteArray_write_size_ge_off_add32 _ _ 608 (hgap _ (by omega) _)
  have hword0 : memLoad (UInt256.ofNat 608) mem0 = available := memLoad_write_back _ _ 608 (by decide +kernel) (hgap _ (by omega) _)
  have howner0 : memLoad (UInt256.ofNat 576) mem0 = owner := by
    rw [memLoad_below_write _ _ 608 576 (le_trans hsize hframe0.size) (by omega) (hgap _ (by omega) _) (by decide +kernel),
      hframe0.load 576 (by omega) (by decide +kernel) hsize (by decide +kernel), howner]
  have rd7108 := vaultBlocks.vault_block_4818 (by omega) (by native_decide) rd4818
  change RD fork vaultBytecode I g s0 (UInt256.ofNat 7108) (UInt256.ofNat 640 :: UInt256.ofNat 4888 :: R)
    (vaultMaxRedeemArgsMemory mem0 (memLoad (UInt256.ofNat 608) mem0)) _ out0 σ0 _ _ at rd7108
  rw [hword0] at rd7108
  have hm := vaultMaxRedeemArgsMemory_reads mem0 available
  let argMem := vaultMaxRedeemArgsMemory mem0 available
  have hsizeArgs : 640 ≤ argMem.size := le_trans hsize0 hm.2.2.2.2.size
  have hownerArgs : memLoad (UInt256.ofNat 576) argMem = owner := by
    rw [hm.2.2.2.2.load 576 (by omega) (by omega) (by omega) (by decide +kernel), howner0]
  let args : List Expr := [.var "__c0", .boolLit false, .intLit (2 ^ 256 - 1)]
  have hargs : evalExprs? config {contract := contract, locals := locals0} evm0 args =
      .ok [.int (Int.ofNat available.toNat), .bool false, .int (Int.ofNat vaultMaxWord.toNat)] := by
    simp only [args, evalExprs?, evalExpr?, locals0, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert_self,
      EvalResult.ofOption, bind, pure, EvalResult.bind]
    rfl
  rcases vaultConvertSharesRoutine (isFloor := false) hs0 hm.1 hm.2.1 hm.2.2.1 hm.2.2.2.1
    hstack (by native_decide) rd7108 with
    ⟨evm1, σ1, calleeLocals1, scratch1, shares, aw1, out1, k1, C1, hconvert, hs1, hframe1, rd4888⟩ | ⟨hconvert, hrev⟩
  swap
  · refine Or.inr ⟨ExecFuncBody.execBlockRevert ?_, hrev⟩
    exact ExecBlock.consNormal hcall0 (ExecBlock.consRevert
      (internalCallFunctionRevert (callee := vaultConvertSharesFunction) (args := args) hargs rfl rfl hconvert))
  let locals1 := locals0.insert "__c1" (.int (Int.ofNat shares.toNat))
  let mem1 := shares.toByteArray.write 0 scratch1 640 32
  have hcall1 := internalCallFunctionReturn (caller := {contract := contract, locals := locals0})
    (callee := vaultConvertSharesFunction) (name := "_convert_to_shares") (args := args) (retVar := "__c1")
    hargs rfl rfl hconvert
  have hscratch : 640 ≤ scratch1.size := le_trans hsizeArgs hframe1.size
  have hsize1 : 672 ≤ mem1.size := toByteArray_write_size_ge_off_add32 _ _ 640 (hgap _ (by omega) _)
  have hword1 : memLoad (UInt256.ofNat 640) mem1 = shares := memLoad_write_back _ _ 640 (by decide +kernel) (hgap _ (by omega) _)
  have howner1 : memLoad (UInt256.ofNat 576) mem1 = owner := by
    rw [memLoad_below_write _ _ 640 576 (by omega) (by omega) (hgap _ (by omega) _) (by decide +kernel),
      hframe1.load 576 (by omega) (by decide +kernel) (by change 608 ≤ argMem.size; omega) (by decide +kernel), hownerArgs]
  let balance := codeOwnerStorageWord I σ1 (vyperMappingSlot ⟨13⟩ (.address (AccountAddress.ofNat owner.toNat)))
  have hret := vaultMaxRedeemReturn (by omega) howner1 hword1 hcanon (by omega) rd4888
  have hbalance : evalExpr? config {contract := contract, locals := locals1} evm1
      (.storage {base := "balanceOf", steps := [.mindex (.var "_owner")]}) =
      .ok (.int (Int.ofNat balance.toNat)) := by
    have hh := vaultBalanceEval evm1 locals1 "_owner" (AccountAddress.ofNat owner.toNat)
      (by rw [store_get_ne _ _ (by decide +kernel), store_get_ne _ _ (by decide +kernel)]; exact hbase)
      (by rw [store_get_ne _ _ (by decide +kernel), store_get_ne _ _ (by decide +kernel)]; exact harg)
    simpa only [hs1.storageRead] using hh
  let locals2 := locals1.insert "__v2" (.int (Int.ofNat balance.toNat))
  have hmin := evalExpr_min256 (cfg := config) (stele := {contract := contract, locals := locals2}) (evm := evm1)
    (lhs := .var "__c1") (rhs := .var "__v2")
    (evalExpr_varUInt256 (value := shares) (by rw [store_get_ne _ _ (by decide +kernel), store_get_self]))
    (evalExpr_varUInt256 (value := balance) (by simp [locals2]))
  refine Or.inl ⟨evm1, σ1, locals2, wordMin shares balance, ?_, hs1, hret⟩
  exact ExecFuncBody.execBlockRet (ExecBlock.consNormal hcall0 (ExecBlock.consNormal hcall1
    (ExecBlock.consNormal (ExecStmt.letDecl hbalance)
      (ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hmin))))))
end Benchmarks.CurveVault
