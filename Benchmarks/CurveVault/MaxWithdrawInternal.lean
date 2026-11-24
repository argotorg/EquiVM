import Benchmarks.CurveVault.AvailableBalanceInternal
import Benchmarks.CurveVault.ConvertAssetsInternal
import Benchmarks.CurveVault.ConversionArguments
import Benchmarks.CurveVault.BalanceStorage
import Benchmarks.CurveVault.RuntimeBlocks_014
import Benchmarks.CurveVault.RuntimeBlocks_015

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

abbrev vaultMaxWithdrawFunction : FunctionDecl := contract.functions[14]!

theorem vaultMaxWithdrawRoutine {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {locals : Store} {owner : UInt256}
    (hs : SourceState s0 I σ evm) (hsize : 64 ≤ mem.size)
    (howner : memLoad (UInt256.ofNat 576) mem = owner)
    (hcanon : owner.toNat < EVM.addressModulus)
    (hbase : locals.get? "balanceOf" = none)
    (harg : locals.get? "_owner" = some (.address (AccountAddress.ofNat owner.toNat)))
    (hstack : R.length + 14 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 3915) R mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (locals' : Store) (value : UInt256),
      ExecFuncBody fork config {contract := contract, locals := locals} evm vaultMaxWithdrawFunction.body
        (.returned {contract := contract, locals := locals'} evm' (some [.int (Int.ofNat value.toNat)])) ∧
      SourceState s0 I σ' evm' ∧ RDret fork vaultBytecode g s0 σ' value.toByteArray) ∨
    (ExecFuncBody fork config {contract := contract, locals := locals} evm vaultMaxWithdrawFunction.body .reverted ∧
      RDrev fork vaultBytecode g s0) := by
  let balance := codeOwnerStorageWord I σ (vyperMappingSlot ⟨13⟩ (.address (AccountAddress.ofNat owner.toNat)))
  let hashMem := wordAt0Mem ⟨13⟩ (wordAt32Mem owner mem)
  have hhash := vyperHashMem_address ⟨13⟩ owner mem hsize hcanon
  have hbalance : evalExpr? config {contract := contract, locals := locals} evm
      (.storage {base := "balanceOf", steps := [.mindex (.var "_owner")]}) =
      .ok (.int (Int.ofNat balance.toNat)) := by
    simpa only [hs.storageRead] using vaultBalanceEval evm locals "_owner" _ hbase harg
  let args : List Expr := [.storage {base := "balanceOf", steps := [.mindex (.var "_owner")]},
    .boolLit true, .intLit (2 ^ 256 - 1)]
  have hargs : evalExprs? config {contract := contract, locals := locals} evm args =
      .ok [.int (Int.ofNat balance.toNat), .bool true, .int (Int.ofNat vaultMaxWord.toNat)] := by
    simp only [args, evalExprs?, hbalance, evalExpr?, bind, pure, EvalResult.bind]
    rfl
  obtain ⟨_, _, rd7332⟩ := vaultBlocks.vault_block_3915 (by omega) (by native_decide) h
  change RD fork vaultBytecode I g s0 (UInt256.ofNat 7332) (UInt256.ofNat 608 :: UInt256.ofNat 3988 :: R)
    (vaultConversionArgsMemory (wordAt0Mem ⟨13⟩ (wordAt32Mem (memLoad (UInt256.ofNat 576) mem) mem))
      (codeOwnerStorageWord I σ (keccakWord ⟨0⟩ (UInt256.ofNat 64)
        (wordAt0Mem ⟨13⟩ (wordAt32Mem (memLoad (UInt256.ofNat 576) mem) mem)))) ⟨1⟩ vaultMaxWord)
    _ rdata σ _ _ at rd7332
  rw [howner, hhash] at rd7332
  have hm := vaultConversionArgsMemory_reads hashMem balance ⟨1⟩ vaultMaxWord
  rcases vaultConvertAssetsRoutine (isFloor := true) hs hm.1 hm.2.1 hm.2.2.1 hm.2.2.2
    hstack (by native_decide) rd7332 with
    ⟨evm0, σ0, calleeLocals0, scratch0, assets, aw0, out0, k0, C0, hconvert, hs0, _, rd3988⟩ | ⟨hconvert, hrev⟩
  swap
  · refine Or.inr ⟨ExecFuncBody.execBlockRevert ?_, hrev⟩
    exact ExecBlock.consRevert (internalCallFunctionRevert (callee := vaultConvertAssetsFunction)
      (args := args) hargs rfl rfl hconvert)
  let locals0 := locals.insert "__c0" (.int (Int.ofNat assets.toNat))
  let mem0 := assets.toByteArray.write 0 scratch0 608 32
  have hcall0 := internalCallFunctionReturn (caller := {contract := contract, locals := locals})
    (callee := vaultConvertAssetsFunction) (name := "_convert_to_assets") (args := args) (retVar := "__c0")
    hargs rfl rfl hconvert
  have hword0 : memLoad (UInt256.ofNat 608) mem0 = assets := memLoad_write_back _ _ 608 (by decide +kernel)
    (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 608 (by norm_num)))
  have rd7819 := vaultBlocks.vault_block_3988 (by omega) (by native_decide) rd3988
  change RD fork vaultBytecode I g s0 (UInt256.ofNat 7819)
    (UInt256.ofNat 640 :: UInt256.ofNat 4003 :: memLoad (UInt256.ofNat 608) mem0 :: R) mem0 _ out0 σ0 _ _ at rd7819
  rw [hword0] at rd7819
  rcases vaultAvailableBalanceRoutine hs0 (by simp only [List.length_cons]; omega) (by native_decide) rd7819 with
    ⟨evm1, σ1, calleeLocals1, scratch1, available, aw1, out1, k1, C1, havailable, hs1, _, rd4003⟩ | ⟨havailable, hrev⟩
  swap
  · refine Or.inr ⟨ExecFuncBody.execBlockRevert ?_, hrev⟩
    exact ExecBlock.consNormal hcall0 (ExecBlock.consRevert
      (internalCallFunctionRevert (callee := vaultAvailableBalanceFunction) (argVals := [])
        (by simp [evalExprs?, pure]) rfl rfl havailable))
  let locals1 := locals0.insert "__c1" (.int (Int.ofNat available.toNat))
  let mem1 := available.toByteArray.write 0 scratch1 640 32
  have hword1 : memLoad (UInt256.ofNat 640) mem1 = available := memLoad_write_back _ _ 640 (by decide +kernel)
    (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 640 (by norm_num)))
  have hret := vaultBlocks.vault_block_4003 (by omega) rd4003
  change RDret fork vaultBytecode g s0 σ1
    (((UInt256.xor (UInt256.mul (UInt256.lt assets (memLoad (UInt256.ofNat 640) mem1))
      (UInt256.xor (memLoad (UInt256.ofNat 640) mem1) assets)) (memLoad (UInt256.ofNat 640) mem1)).toByteArray.write
      0 mem1 672 32).readWithPadding 672 32) at hret
  rw [hword1, branchlessMin, toByteArray_write_read_back_of_gap _ _ _
    (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 672 (by norm_num)))] at hret
  have hcall1 := internalCallFunctionReturn (caller := {contract := contract, locals := locals0})
    (callee := vaultAvailableBalanceFunction) (name := "_available_balance") (args := []) (argVals := [])
    (retVar := "__c1") (by simp [evalExprs?, pure]) rfl rfl havailable
  have hmin := evalExpr_min256 (cfg := config) (stele := {contract := contract, locals := locals1}) (evm := evm1)
    (lhs := .var "__c0") (rhs := .var "__c1")
    (evalExpr_varUInt256 (value := assets) (by rw [store_get_ne _ _ (by decide +kernel), store_get_self]))
    (evalExpr_varUInt256 (value := available) (by simp [locals1]))
  refine Or.inl ⟨evm1, σ1, locals1, wordMin assets available, ?_, hs1, hret⟩
  exact ExecFuncBody.execBlockRet (ExecBlock.consNormal hcall0 (ExecBlock.consNormal hcall1
    (ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hmin)))))
end Benchmarks.CurveVault
