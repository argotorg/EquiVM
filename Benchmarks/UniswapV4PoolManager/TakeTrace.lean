import Benchmarks.UniswapV4PoolManager.CurrencyTransferTrace
import Benchmarks.UniswapV4PoolManager.AccountDeltaTrace
import Benchmarks.UniswapV4PoolManager.SafeCast
import Benchmarks.UniswapV4PoolManager.MappingMemory
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_031
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_013
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_006

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem takeTransferTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {f : Frame}
    {mem rdata : ByteArray} {aw amount : UInt256} {currency recipient : AccountAddress}
    {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables) (hstack : R.length+16 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀) (hf : f.contract = contract)
    (hc : f.locals.get? "currency" = some (.address currency))
    (ht : f.locals.get? "to" = some (.address recipient))
    (ha : f.locals.get? "amount" = some (.int (Int.ofNat amount.toNat)))
    (hmem : mem.size = 96) (hfree : memLoad ⟨64⟩ mem = ⟨160⟩)
    (h : RD (deployedRuntime v) I g s0 ⟨11111⟩
      (accountWord currency :: accountWord recipient :: amount :: ⟨3631⟩ :: R) mem aw rdata evm.accountMap k C) :
    ∃ result, ExecFuncBody config f evm (takeTransition.body.drop 7) result ∧
      unitResultTrace (deployedRuntime v) g s0 result := by
  have rdCall := poolManagerBlocks.poolManager_block_11111 (by simp; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  let cf : Frame := {f with locals := (((∅ : Store).insert "amount" (.int (Int.ofNat amount.toNat))).insert
    "to" (.address recipient)).insert "currency" (.address currency)}
  obtain ⟨result, hb, hr⟩ := currencyTransferTrace (f := cf) v hstack hI hσ0 (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("currency" == "to") = false)).trans (store_get_self _ _ _))
    ((store_get_ne _ _ (by decide : ("currency" == "amount") = false)).trans
      ((store_get_ne _ _ (by decide : ("to" == "amount") = false)).trans (store_get_self _ _ _)))
    (by decide) (by rw [hmem]; change 64 < USize.size; exact (by native_decide)) hfree
    (by rw [deployedRuntime_jumps]; jump_dest) rdCall
  have hargs : evalExprs? config f evm [.var "currency", .var "to", .var "amount"] =
      .ok [.address currency, .address recipient, .int (Int.ofNat amount.toNat)] := by
    simp only [evalExprs?, evalLocalValue hc, evalLocalValue ht, evalLocalValue ha, bind, EvalResult.bind, pure]
  have hcall := internalCallFunctionExec (retVar := "__c3") hargs
    (by rw [hf]; exact currencyTransfer_lookup) rfl hb
  have hresult := unitContinuationTrace_finish
    (fun hr => poolManagerBlocks.poolManager_block_3631 (by omega) hr) hr
  exact ⟨_, execFuncBody_singleton hcall, unitResultTrace_finishCall f "__c3" hresult⟩

theorem takeAccountTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {f : Frame}
    {mem rdata : ByteArray} {aw amount : UInt256} {currency recipient : AccountAddress}
    {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables) (hstack : R.length+16 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀) (hf : f.contract = contract)
    (hc : f.locals.get? "currency" = some (.address currency))
    (ht : f.locals.get? "to" = some (.address recipient))
    (ha : f.locals.get? "amount" = some (.int (Int.ofNat amount.toNat)))
    (hd : f.locals.get? "__c1" = some (.int (Int.ofNat amount.toNat)))
    (hfit : amount.toNat < 2^127) (hmem : mem.size = 96) (hfree : memLoad ⟨64⟩ mem = ⟨160⟩)
    (h : RD (deployedRuntime v) I g s0 ⟨12528⟩
      (accountWord currency :: EVM.wordOfInt (-(Int.ofNat amount.toNat)) :: accountWord I.source :: ⟨11111⟩ ::
        accountWord currency :: accountWord recipient :: amount :: ⟨3631⟩ :: R) mem aw rdata evm.accountMap k C) :
    ∃ result, ExecFuncBody config f evm (takeTransition.body.drop 6) result ∧
      unitResultTrace (deployedRuntime v) g s0 result := by
  have hlo : -(2^127 : Int) ≤ -(Int.ofNat amount.toNat) := by simp only [Int.ofNat_eq_natCast]; omega
  have hhi : -(Int.ofNat amount.toNat) < (2^127 : Int) := by simp only [Int.ofNat_eq_natCast]; omega
  have htrace := accountDeltaTrace v (by simp; omega) hI hlo hhi
    (by rw [deployedRuntime_jumps]; jump_dest) h
  have hcall := accountDeltaCall (evm := evm) (et := .env .caller) hf (evalLocalValue hc)
    (evalNegateInt128Word (evalLocalValue hd) hfit) (by simp only [evalExpr?, envValue, pure]; rfl) "__c2"
  rw [accountDeltaCallResult, hI] at hcall
  rw [accountDeltaTraceResult] at htrace
  let f1 : Frame := {f with locals := f.locals.insert "__c2" .unit}
  have hc1 : f1.locals.get? "currency" = some (.address currency) :=
    (store_get_ne _ _ (by decide : ("__c2" == "currency") = false)).trans hc
  have ht1 : f1.locals.get? "to" = some (.address recipient) :=
    (store_get_ne _ _ (by decide : ("__c2" == "to") = false)).trans ht
  have ha1 : f1.locals.get? "amount" = some (.int (Int.ofNat amount.toNat)) :=
    (store_get_ne _ _ (by decide : ("__c2" == "amount") = false)).trans ha
  by_cases hz : -(Int.ofNat amount.toNat) = 0
  · rw [if_pos hz] at hcall htrace
    obtain ⟨aw', k', C', rdReturn⟩ := htrace
    obtain ⟨result, hb, hr⟩ := takeTransferTrace (f := f1) v hstack hI hσ0 hf hc1 ht1 ha1 hmem hfree rdReturn
    exact ⟨result, execFuncBody_prepend (execBlock_singleton hcall) hb, hr⟩
  · rw [if_neg hz] at hcall htrace
    generalize hsum : currencyDeltaValue evm I.source currency + -(Int.ofNat amount.toNat) = next at hcall htrace
    by_cases hs : int256Fits next
    · rw [if_pos hs] at hcall htrace
      by_cases hp : I.perm = false
      · rw [if_pos hp] at hcall htrace
        exact ⟨.staticViolation, .execBlockStatic (ExecBlock.consStatic hcall), htrace⟩
      · rw [if_neg hp] at hcall htrace
        obtain ⟨aw', k', C', rdReturn⟩ := htrace
        have hI' := (accountDeltaPost_env evm I.source currency (-(Int.ofNat amount.toNat))).trans hI
        have hσ0' := (accountDeltaPost_world evm I.source currency (-(Int.ofNat amount.toNat))).trans hσ0
        have hm' : (currencyDeltaMemory I.source currency mem).size = 96 := twoWordHashMem_size_96 _ _ hmem
        have hf' : memLoad ⟨64⟩ (currencyDeltaMemory I.source currency mem) = ⟨160⟩ :=
          (mappingMemory_load64 _ _ hmem).trans hfree
        obtain ⟨result, hb, hr⟩ := takeTransferTrace (f := f1) v hstack hI' hσ0' hf hc1 ht1 ha1 hm' hf' rdReturn
        exact ⟨result, execFuncBody_prepend (execBlock_singleton hcall) hb, hr⟩
    · rw [if_neg hs] at hcall htrace
      exact ⟨.reverted, .execBlockRevert (ExecBlock.consRevert hcall), htrace⟩

theorem takeBodyTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {f : Frame}
    {mem rdata : ByteArray} {aw : UInt256} {currency recipient : AccountAddress}
    {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables) (hstack : R.length+16 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀) (hf : f.contract = contract)
    (hc : f.locals.get? "currency" = some (.address currency))
    (ht : f.locals.get? "to" = some (.address recipient))
    (ha : f.locals.get? "amount" = some (.int (Int.ofNat (calldataWord I.calldata 68).toNat)))
    (hmem : mem.size = 96) (hfree : memLoad ⟨64⟩ mem = ⟨160⟩)
    (h : RD (deployedRuntime v) I g s0 ⟨11039⟩
      (accountWord recipient :: accountWord currency :: R) mem aw rdata evm.accountMap k C) :
    ∃ result, ExecFuncBody config f evm (takeTransition.body.drop 3) result ∧
      unitResultTrace (deployedRuntime v) g s0 result := by
  let amount := calldataWord I.calldata 68
  have hlock := lockCall (evm := evm) hf "__c0"
  have hlockword : codeOwnerTransientWord I evm.accountMap lockSlot = transientWord evm lockSlot :=
    (transientWord_accountMap hI lockSlot).symm
  by_cases hl : transientWord evm lockSlot = ⟨0⟩
  · rw [decide_eq_false (not_not.mpr hl)] at hlock
    have rdRev := poolManagerBlocks.poolManager_block_11039_taken (by simp; omega)
      (by change UInt256.isZero (codeOwnerTransientWord I evm.accountMap lockSlot) ≠ ⟨0⟩; rw [hlockword, hl]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    have hr := poolManagerBlocks.poolManager_block_1239
      (by simp [poolManagerBlocks.poolManager_block_11039_taken_stack]; omega) rdRev
    exact ⟨.reverted, .execBlockRevert (ExecBlock.consNormal hlock (ExecBlock.consRevert (ExecStmt.iteTrue
      (evalNotBool (va := false) (evalLocalValue (store_get_self _ _ _)))
      (ExecBlock.consRevert (ExecStmt.requireFalse (by simp only [evalExpr?, pure])))))), hr⟩
  · rw [decide_eq_true hl] at hlock
    let f1 : Frame := {f with locals := f.locals.insert "__c0" (.bool true)}
    have hguard : ExecStmt config f1 evm takeTransition.body[4]! (.ok f1 evm) :=
      ExecStmt.iteFalse (evalNotBool (va := true) (evalLocalValue (store_get_self _ _ _))) ExecBlock.nil
    have ha1 : f1.locals.get? "amount" = some (.int (Int.ofNat amount.toNat)) :=
      (store_get_ne _ _ (by decide : ("__c0" == "amount") = false)).trans ha
    have rdOpen := poolManagerBlocks.poolManager_block_11039_fallthrough (by simp; omega)
      (by change UInt256.isZero (codeOwnerTransientWord I evm.accountMap lockSlot) = ⟨0⟩; rw [hlockword]; exact isZero_eq_zero_of_ne hl) h
    change RD _ _ _ _ ⟨11083⟩ (accountWord recipient :: amount :: accountWord currency :: R) _ _ _ _ _ _ at rdOpen
    have rdCast := poolManagerBlocks.poolManager_block_11083 (by omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rdOpen
    by_cases hfit : amount.toNat < 2^127
    · have hcast := uintToInt128Call (f := f1) hf (evalLocalValue (cfg := config) (evm := evm) ha1) hfit "__c1"
      let f2 : Frame := {f1 with locals := f1.locals.insert "__c1" (.int (Int.ofNat amount.toNat))}
      have hc2 : f2.locals.get? "currency" = some (.address currency) :=
        (store_get_ne _ _ (by decide : ("__c1" == "currency") = false)).trans
          ((store_get_ne _ _ (by decide : ("__c0" == "currency") = false)).trans hc)
      have ht2 : f2.locals.get? "to" = some (.address recipient) :=
        (store_get_ne _ _ (by decide : ("__c1" == "to") = false)).trans
          ((store_get_ne _ _ (by decide : ("__c0" == "to") = false)).trans ht)
      have ha2 : f2.locals.get? "amount" = some (.int (Int.ofNat amount.toNat)) :=
        (store_get_ne _ _ (by decide : ("__c1" == "amount") = false)).trans ha1
      obtain ⟨k1, C1, rdPrep⟩ := uintToInt128Trace v (by simp; omega) hfit
        (by rw [deployedRuntime_jumps]; jump_dest) rdCast
      have rdAccount := poolManagerBlocks.poolManager_block_11098 (by simp; omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rdPrep
      change RD _ _ _ _ ⟨12528⟩
        (accountWord currency :: UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ amount) :: accountWord I.source :: ⟨11111⟩ ::
          accountWord currency :: accountWord recipient :: amount :: ⟨3631⟩ :: R) _ _ _ _ _ _ at rdAccount
      rw [← wordOfInt_neg_natCast_eq_sub_zero,
        signextend128_wordOfInt (by simp only [Int.ofNat_eq_natCast]; omega : -(2^127 : Int) ≤ -(Int.ofNat amount.toNat))
          (by simp only [Int.ofNat_eq_natCast]; omega : -(Int.ofNat amount.toNat) < (2^127 : Int))] at rdAccount
      obtain ⟨result, hb, hr⟩ := takeAccountTrace (f := f2) v hstack hI hσ0 hf hc2 ht2 ha2 (store_get_self _ _ _)
        hfit hmem hfree rdAccount
      exact ⟨result, execFuncBody_prepend
        (ExecBlock.consNormal hlock (ExecBlock.consNormal hguard (ExecBlock.consNormal hcast ExecBlock.nil))) hb, hr⟩
    · have hcast := uintToInt128CallReverts (f := f1) hf (evalLocalValue (cfg := config) (evm := evm) ha1) hfit "__c1"
      have hr := uintToInt128TraceReverts v (by simp; omega) hfit rdCast
      exact ⟨.reverted, .execBlockRevert (ExecBlock.consNormal hlock (ExecBlock.consNormal hguard
        (ExecBlock.consRevert hcast))), hr⟩

end Benchmarks.UniswapV4PoolManager
