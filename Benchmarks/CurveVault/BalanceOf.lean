import Benchmarks.CurveVault.Dispatch
import Benchmarks.CurveVault.Entry
import Benchmarks.CurveVault.BalanceStorage
import Benchmarks.CurveVault.Memory
import Benchmarks.CurveVault.RuntimeBlocks_024

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultBalanceOfEval (evm : EVM.State) (locals : Store) (a : AccountAddress)
    (hbase : locals.get? "balanceOf" = none)
    (harg : locals.get? "arg0" = some (.address a)) :
    evalExpr? config {contract := contract, locals := locals} evm
      (.storage {base := "balanceOf", steps := [.mindex (.var "arg0")]}) =
      .ok (.int (Int.ofNat (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
        (vyperMappingSlot ⟨13⟩ (.address a))).toNat)) :=
  vaultBalanceEval evm locals "arg0" a hbase harg

theorem vaultBalanceOfReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {key : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024) (hcanon : key.toNat < EVM.addressModulus)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 6730) (key :: R) mem aw rdata σ k C) :
    RDret fork vaultBytecode g s0 σ
      (codeOwnerStorageWord I σ (vyperMappingSlot ⟨13⟩ (.address (AccountAddress.ofNat key.toNat)))).toByteArray := by
  let argMem := key.toByteArray.write 0 mem 64 32
  have hgap : 64 - mem.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 64 (by norm_num))
  have hload : memLoad (UInt256.ofNat 64) argMem = key :=
    memLoad_write_back key mem 64 (by decide +kernel) hgap
  have hmem : 64 ≤ argMem.size :=
    le_trans (by decide +kernel : 64 ≤ 64 + 32) (toByteArray_write_size_ge_off_add32 key mem 64 hgap)
  have hhash := vyperHashMem_address ⟨13⟩ key argMem hmem hcanon
  have hret := vaultBlocks.vault_block_6730 hstack h
  change RDret fork vaultBytecode g s0 σ
    (((codeOwnerStorageWord I σ (keccakWord ⟨0⟩ (UInt256.ofNat 64)
      (wordAt0Mem ⟨13⟩ (wordAt32Mem (memLoad (UInt256.ofNat 64) argMem) argMem)))).toByteArray.write 0
      (wordAt0Mem ⟨13⟩ (wordAt32Mem (memLoad (UInt256.ofNat 64) argMem) argMem)) 96 32).readWithPadding 96 32) at hret
  rw [hload, hhash, toByteArray_write_read_back_of_gap _ _ _
    (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 96 (by norm_num)))] at hret
  exact hret

theorem vaultBalanceOfBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 21)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vaultSelBytes 21) rfl hsel
  have hd : dispatchMsg contract I.calldata = some balanceOfTransition := by
    apply vaultDispatch_balanceOf
    all_goals first | exact hsel | exact selIs_exclusive (by decide +kernel) hsel
  apply vaultGuardedEntry (t := balanceOfTransition) (pc := UInt256.ofNat 6718)
    hcode hsize hd rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel : 36 < UInt256.size) (by decide +kernel) (by native_decide)
    (decodeCalldataWithMode_vyper_address_none_short hsz)
    (vaultReachBalanceOfBody hcode hsz hsize hsel)
  intro hvalue hargs k' C' rdBody
  by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
  · have rd6730 := vaultBlocks.vault_block_6718_fallthrough (by simp)
      (u256_shiftRight160_zero_of_lt _ hcanon) rdBody
    have hret := vaultBalanceOfReturn (by simp) hcanon rd6730
    have hdec : config.externalABI.decodeCalldata? (balanceOfTransition.params.map Param.name)
        (transitionSignature balanceOfTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "arg0" (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))) :=
      decodeCalldataWithMode_vyper_address_ok hargs hcanon
    have heval := vaultBalanceOfEval (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      ((∅ : Store).insert "arg0" (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)))
      (AccountAddress.ofNat (calldataWord I.calldata 4).toNat) (by simp) (by simp)
    change evalExpr? config _ _ _ = .ok (.int (Int.ofNat
      (Stele.EVM.storageLoad (initState σ σ₀ (Sat256.ofUInt256 g) A I) I.codeOwner _).toNat)) at heval
    rw [codeOwnerStorageWord_initState] at heval
    have hsource := nonpayableReturnExprBodyReturns (fork := fork) (contract := contract) hvalue heval
    exact hret.reEquivExecution hcode hd hdec hsource
      (returnEquiv_of_encode (uint256ReturnEncoding _))
  · have rdRevert := vaultBlocks.vault_block_6718_taken (by simp)
      (fun h => hcanon (u256_lt_addressModulus_of_shiftRight160_zero _ h))
      (by native_decide) rdBody
    have hrev := vaultBlocks.vault_block_8284 (by simp [vaultBlocks.vault_block_6718_taken_stack]) rdRevert
    exact hrev.reEquivDecodingFailed hcode hd
      (decodeCalldataWithMode_vyper_address_none_noncanon hargs hcanon) rfl rfl

theorem vaultBalanceOfBody {σ σ₀ A I} {g : UInt256}
    (_hwf : storageWF σ I)
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 21)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I :=
  vaultBalanceOfBodyCore hcode hsize hsel

end Benchmarks.CurveVault
