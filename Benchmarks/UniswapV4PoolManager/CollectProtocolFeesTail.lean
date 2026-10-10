import Benchmarks.UniswapV4PoolManager.ProtocolFeesSource
import Benchmarks.UniswapV4PoolManager.CurrencyTransferTrace
import Benchmarks.UniswapV4PoolManager.Uint256ResultTrace
import Benchmarks.UniswapV4PoolManager.Arithmetic
import Benchmarks.UniswapV4PoolManager.StorageStaticTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_012

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem collectTransferTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {f : Frame}
    {mem rdata : ByteArray} {aw amount : UInt256} {currency recipient : AccountAddress}
    {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables) (hstack : R.length+18 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀) (hf : f.contract = contract)
    (hc : f.locals.get? "currency" = some (.address currency))
    (ht : f.locals.get? "recipient" = some (.address recipient))
    (ha : f.locals.get? "amountCollected" = some (.int (Int.ofNat amount.toNat)))
    (hmem : mem.size = 96) (hfree : memLoad ⟨64⟩ mem = ⟨160⟩)
    (h : RD (deployedRuntime v) I g s0 ⟨12792⟩
      (accountWord currency :: accountWord recipient :: amount :: ⟨1954⟩ :: amount :: ⟨32⟩ :: R)
      mem aw rdata evm.accountMap k C) :
    ∃ result, ExecFuncBody config f evm (collectProtocolFeesTransition.body.drop 9) result ∧
      uint256ResultTrace (deployedRuntime v) g s0 result := by
  let cf : Frame := {f with locals := (((∅ : Store).insert "amount" (.int (Int.ofNat amount.toNat))).insert
    "to" (.address recipient)).insert "currency" (.address currency)}
  have hgap : (⟨160⟩ : UInt256).toNat-mem.size < USize.size := by rw [hmem]; native_decide
  obtain ⟨result, hb, hr⟩ := currencyTransferMemoryTrace (f := cf) WordReturnMemory v (by simp; omega) hI hσ0
    (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("currency" == "to") = false)).trans (store_get_self _ _ _))
    ((store_get_ne _ _ (by decide : ("currency" == "amount") = false)).trans
      ((store_get_ne _ _ (by decide : ("to" == "amount") = false)).trans (store_get_self _ _ _)))
    ⟨by omega, by rw [hfree]; exact hgap⟩ (by decide) hgap hfree
    (fun out ho => currencyTransferOutput_wordReturn mem out ⟨160⟩ _ _ _ (by omega) hfree (by decide)
      (by decide) hgap ho) (by rw [deployedRuntime_jumps]; jump_dest) h
  have hargs : evalExprs? config f evm [.var "currency", .var "recipient", .var "amountCollected"] =
      .ok [.address currency, .address recipient, .int (Int.ofNat amount.toNat)] := by
    simp only [evalExprs?, evalLocalValue hc, evalLocalValue ht, evalLocalValue ha, bind, EvalResult.bind, pure]
  have hcall := internalCallFunctionExec (retVar := "__c2") hargs
    (by rw [hf]; exact currencyTransfer_lookup) rfl hb
  cases result with
  | returned cf evm' value =>
    cases value with
    | none =>
      obtain ⟨mem', aw', out, k', C', hm, rdReturn⟩ := hr
      refine ⟨.returned {f with locals := f.locals.insert "__c2" .unit} evm'
        (some [.int (Int.ofNat amount.toNat)]), ?_, amount, rfl, wordReturnTrace v (by omega) hm rdReturn⟩
      exact .execBlockRet (ExecBlock.consNormal hcall (ABlock.start.returns (evalLocalValue
        ((store_get_ne _ _ (by decide : ("__c2" == "amountCollected") = false)).trans ha))))
    | some _ => cases hr
  | reverted => exact ⟨.reverted, .execBlockRevert (ExecBlock.consRevert hcall), hr⟩
  | staticViolation => exact ⟨.staticViolation, .execBlockStatic (ExecBlock.consStatic hcall), hr⟩
  | _ => cases hr

theorem collectDebitTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {f : Frame}
    {mem rdata : ByteArray} {aw amount : UInt256} {currency recipient : AccountAddress}
    {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables) (hstack : R.length+18 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀) (hf : f.contract = contract)
    (hc : f.locals.get? "currency" = some (.address currency))
    (ht : f.locals.get? "recipient" = some (.address recipient))
    (ha : f.locals.get? "amountCollected" = some (.int (Int.ofNat amount.toNat)))
    (hb : f.locals.get? "protocolFeesAccrued" = none)
    (hmem : mem.size = 96) (hfree : memLoad ⟨64⟩ mem = ⟨160⟩)
    (h : RD (deployedRuntime v) I g s0 ⟨3283⟩
      (accountWord currency :: accountWord currency :: accountWord recipient :: amount :: ⟨1954⟩ :: amount :: ⟨32⟩ :: R)
      mem aw rdata evm.accountMap k C) :
    ∃ result, ExecFuncBody config f evm (collectProtocolFeesTransition.body.drop 8) result ∧
      uint256ResultTrace (deployedRuntime v) g s0 result := by
  obtain ⟨aw', k', C', rdSub⟩ := poolManagerBlocks.poolManager_block_3283_packed (by omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  let nextMem := twoWordHashMem (accountWord currency) ⟨1⟩ mem
  change RD _ _ _ _ ⟨12269⟩ (solcSlotWordAt (keccakWord ⟨0⟩ ⟨64⟩ nextMem) evm.accountMap I :: amount ::
    ⟨3304⟩ :: keccakWord ⟨0⟩ ⟨64⟩ nextMem :: accountWord currency :: accountWord recipient :: amount ::
      ⟨1954⟩ :: amount :: ⟨32⟩ :: R) nextMem aw' rdata evm.accountMap k' C' at rdSub
  have hslot : keccakWord ⟨0⟩ ⟨64⟩ nextMem = protocolFeesSlot currency := mappingMemory_slot _ _ hmem
  have hload : protocolFeesWord evm currency = solcSlotWordAt (protocolFeesSlot currency) evm.accountMap I :=
    storageLoad_codeOwner_eq_solcSlotWordAt evm I _ (by rw [hI])
  rw [hslot, ← hload] at rdSub
  have hread := protocolFeesRead (evm := evm) hf hb (evalLocalValue hc)
  by_cases hfit : amount.toNat ≤ (protocolFeesWord evm currency).toNat
  · have heval := evalExpr_uint256_sub hread (evalLocalValue ha) hfit
    have hwrite := protocolFeesWrite (evm := evm) (UInt256.sub (protocolFeesWord evm currency) amount) hf hb (evalLocalValue hc)
    obtain ⟨k2, C2, rdStore⟩ := checkedSubPass v (by simp; omega) hfit
      (by rw [deployedRuntime_jumps]; jump_dest) rdSub
    by_cases hp : I.perm = false
    · have hr := swappedStoreStatic (by simp; omega) hp
        (by immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨3304⟩ : UInt256),
          UInt8.ofNat 91, .JUMPDEST, none, poolManagerBlocks.immutableLayout_inBounds, poolManagerBlocks.immutableTemplate_size64))
        (by immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨3305⟩ : UInt256),
          UInt8.ofNat 144, .SWAP1, none, poolManagerBlocks.immutableLayout_inBounds, poolManagerBlocks.immutableTemplate_size64))
        (by immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨3306⟩ : UInt256),
          UInt8.ofNat 85, .SSTORE, none, poolManagerBlocks.immutableLayout_inBounds, poolManagerBlocks.immutableTemplate_size64)) rdStore
      exact ⟨.staticViolation, .execBlockStatic (ExecBlock.consStatic
        (ExecStmt.assignStatic heval hwrite (by rw [hI]; exact hp))), hr⟩
    · obtain ⟨k3, C3, rdTransfer⟩ := poolManagerBlocks.poolManager_block_3304 (by simp; omega)
        (Bool.eq_true_of_not_eq_false hp) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rdStore
      let evm' := protocolFeesPost evm currency (UInt256.sub (protocolFeesWord evm currency) amount)
      have hm : evm'.accountMap = sstoreAccountMap I.codeOwner evm.accountMap (protocolFeesSlot currency)
          (UInt256.sub (protocolFeesWord evm currency) amount) := by
        dsimp only [evm', protocolFeesPost]
        rw [storageStore_accountMap, hI]
      rw [← hm] at rdTransfer
      obtain ⟨result, hb', hr⟩ := collectTransferTrace (f := f) v hstack
        ((storageStore_executionEnv _ _ _ _).trans hI) ((storageStore_σ₀ _ _ _ _).trans hσ0) hf hc ht ha
        (twoWordHashMem_size_96 _ _ hmem) ((mappingMemory_load64 _ _ hmem).trans hfree) rdTransfer
      exact ⟨result, execFuncBody_prepend (execBlock_singleton (ExecStmt.assign heval hwrite)) hb', hr⟩
  · exact ⟨.reverted, .execBlockRevert (ExecBlock.consRevert (ExecStmt.assignExprRevert
      (checkedSubSourceUnderflow hread (evalLocalValue ha) (Nat.lt_of_not_ge hfit)))),
      checkedSubReverts v (by simp; omega) (Nat.lt_of_not_ge hfit) rdSub⟩

end Benchmarks.UniswapV4PoolManager
