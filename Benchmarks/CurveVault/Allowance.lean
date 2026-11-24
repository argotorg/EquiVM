import Benchmarks.CurveVault.Dispatch
import Benchmarks.CurveVault.Entry
import Benchmarks.CurveVault.AllowanceStorage
import Benchmarks.CurveVault.Memory
import Benchmarks.CurveVault.RuntimeBlocks_024

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultAllowanceEval (evm : EVM.State) (locals : Store) (a b : AccountAddress)
    (hbase : locals.get? "allowance" = none)
    (harg : locals["arg0"]? = some (.address a))
    (harg1 : locals["arg1"]? = some (.address b)) :
    evalExpr? config {contract := contract, locals := locals} evm
      (.storage {base := "allowance", steps := [.mindex (.var "arg0"), .mindex (.var "arg1")]}) =
      .ok (.int (Int.ofNat (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
        (vyperMappingSlot (vyperMappingSlot ⟨12⟩ (.address a)) (.address b))).toNat)) := by
  exact vaultAllowanceEvalAt evm locals (.var "arg0") (.var "arg1") a b hbase
    (by simp [evalExpr?, harg, EvalResult.ofOption])
    (by simp [evalExpr?, harg1, EvalResult.ofOption])

theorem vaultAllowanceReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {owner spender : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcanon0 : owner.toNat < EVM.addressModulus) (hcanon1 : spender.toNat < EVM.addressModulus)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 6677) (spender :: R)
      (owner.toByteArray.write 0 mem 64 32) aw rdata σ k C) :
    RDret fork vaultBytecode g s0 σ
      (codeOwnerStorageWord I σ (vyperMappingSlot
        (vyperMappingSlot ⟨12⟩ (.address (AccountAddress.ofNat owner.toNat)))
        (.address (AccountAddress.ofNat spender.toNat)))).toByteArray := by
  let ownerMem := owner.toByteArray.write 0 mem 64 32
  let argsMem := spender.toByteArray.write 0 ownerMem 96 32
  have hgap64 : 64 - mem.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 64 (by norm_num))
  have hgap96 : 96 - ownerMem.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 96 (by norm_num))
  have hownerMem : 96 ≤ ownerMem.size := toByteArray_write_size_ge_off_add32 owner mem 64 hgap64
  have hargsMem : 128 ≤ argsMem.size := toByteArray_write_size_ge_off_add32 spender ownerMem 96 hgap96
  have hload0 : memLoad (UInt256.ofNat 64) argsMem = owner := by
    rw [memLoad_below_write spender ownerMem 96 64 hownerMem (by decide +kernel)
      hgap96 (by decide +kernel)]
    exact memLoad_write_back owner mem 64 (by decide +kernel) hgap64
  let hashMem0 := wordAt0Mem ⟨12⟩ (wordAt32Mem owner argsMem)
  have hload1 : memLoad (UInt256.ofNat 96) hashMem0 = spender := by
    rw [memLoad_vyperHashMem _ _ _ _ (by decide +kernel) hargsMem (by decide +kernel)]
    exact memLoad_write_back spender ownerMem 96 (by decide +kernel) hgap96
  have hhash0 := vyperHashMem_address ⟨12⟩ owner argsMem (by omega) hcanon0
  have hhashMem0 : 64 ≤ hashMem0.size := by
    dsimp only [hashMem0]
    rw [wordAt0Mem_size_of_ge64 _ (by rw [wordAt32Mem_size_of_ge_64 _ (by omega)]; omega),
      wordAt32Mem_size_of_ge_64 _ (by omega)]
    omega
  have hhash1 := vyperHashMem_address
    (vyperMappingSlot ⟨12⟩ (.address (AccountAddress.ofNat owner.toNat))) spender
    hashMem0 hhashMem0 hcanon1
  have hret := vaultBlocks.vault_block_6677 hstack h
  change RDret fork vaultBytecode g s0 σ
    (((codeOwnerStorageWord I σ (keccakWord ⟨0⟩ (UInt256.ofNat 64)
      (wordAt0Mem (keccakWord ⟨0⟩ (UInt256.ofNat 64)
        (wordAt0Mem ⟨12⟩ (wordAt32Mem (memLoad (UInt256.ofNat 64) argsMem) argsMem)))
        (wordAt32Mem (memLoad (UInt256.ofNat 96)
          (wordAt0Mem ⟨12⟩ (wordAt32Mem (memLoad (UInt256.ofNat 64) argsMem) argsMem)))
          (wordAt0Mem ⟨12⟩ (wordAt32Mem (memLoad (UInt256.ofNat 64) argsMem) argsMem)))))).toByteArray.write 0
      _ 128 32).readWithPadding 128 32) at hret
  rw [hload0, hload1, hhash0, hhash1,
    toByteArray_write_read_back_of_gap _ _ _
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 128 (by norm_num)))] at hret
  exact hret

theorem vaultAllowanceBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 41)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vaultSelBytes 41) rfl hsel
  have hd : dispatchMsg contract I.calldata = some allowanceTransition := by
    apply vaultDispatch_allowance
    all_goals first | exact hsel | exact selIs_exclusive (by decide +kernel) hsel
  apply vaultGuardedEntry (t := allowanceTransition) (pc := UInt256.ofNat 6651)
    hcode hsize hd rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel : 68 < UInt256.size) (by decide +kernel) (by native_decide)
    (decodeCalldataWithMode_vyper_address_address_none_short hsz)
    (vaultReachAllowanceBody hcode hsz hsize hsel)
  intro hvalue hargs k' C' rdBody
  by_cases hcanon0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus
  · have rd6663 := vaultBlocks.vault_block_6651_fallthrough (by simp)
      (u256_shiftRight160_zero_of_lt _ hcanon0) rdBody
    by_cases hcanon1 : (calldataWord I.calldata 36).toNat < EVM.addressModulus
    · have rd6677 := vaultBlocks.vault_block_6663_fallthrough (by simp)
        (u256_shiftRight160_zero_of_lt _ hcanon1) rd6663
      have hret := vaultAllowanceReturn (by simp) hcanon0 hcanon1 rd6677
      have hdec : config.externalABI.decodeCalldata? (allowanceTransition.params.map Param.name)
          (transitionSignature allowanceTransition).paramTypes I.calldata =
          some (((∅ : Store).insert "arg0" (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).insert
            "arg1" (.address (AccountAddress.ofNat (calldataWord I.calldata 36).toNat))) :=
        decodeCalldataWithMode_vyper_address_address_ok hargs hcanon0 hcanon1
      have heval := vaultAllowanceEval (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (((∅ : Store).insert "arg0" (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).insert
          "arg1" (.address (AccountAddress.ofNat (calldataWord I.calldata 36).toNat)))
        (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)
        (AccountAddress.ofNat (calldataWord I.calldata 36).toNat) (by simp)
        (by simp only [Std.HashMap.getElem?_insert]; rfl)
        (by simp)
      change evalExpr? config _ _ _ = .ok (.int (Int.ofNat
        (Stele.EVM.storageLoad (initState σ σ₀ (Sat256.ofUInt256 g) A I) I.codeOwner _).toNat)) at heval
      rw [codeOwnerStorageWord_initState] at heval
      have hsource := nonpayableReturnExprBodyReturns (fork := fork) (contract := contract) hvalue heval
      exact hret.reEquivExecution hcode hd hdec hsource
        (returnEquiv_of_encode (uint256ReturnEncoding _))
    · have rdRevert := vaultBlocks.vault_block_6663_taken (by simp)
        (fun h => hcanon1 (u256_lt_addressModulus_of_shiftRight160_zero _ h))
        (by native_decide) rd6663
      have hrev := vaultBlocks.vault_block_8284 (by simp [vaultBlocks.vault_block_6663_taken_stack]) rdRevert
      exact hrev.reEquivDecodingFailed hcode hd
        (decodeCalldataWithMode_vyper_address_address_none_noncanon1 hargs hcanon0 hcanon1) rfl rfl
  · have rdRevert := vaultBlocks.vault_block_6651_taken (by simp)
      (fun h => hcanon0 (u256_lt_addressModulus_of_shiftRight160_zero _ h))
      (by native_decide) rdBody
    have hrev := vaultBlocks.vault_block_8284 (by simp [vaultBlocks.vault_block_6651_taken_stack]) rdRevert
    exact hrev.reEquivDecodingFailed hcode hd
      (decodeCalldataWithMode_vyper_address_address_none_noncanon0 hargs hcanon0) rfl rfl

theorem vaultAllowanceBody {σ σ₀ A I} {g : UInt256}
    (_hwf : storageWF σ I)
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 41)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I :=
  vaultAllowanceBodyCore hcode hsize hsel

end Benchmarks.CurveVault
