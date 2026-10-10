import Benchmarks.UniswapV4PoolManager.CollectProtocolFeesTail
import Benchmarks.UniswapV4PoolManager.CollectProtocolFeesSource
import Benchmarks.UniswapV4PoolManager.ProtocolFeeSource
import Benchmarks.UniswapV4PoolManager.TransientTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_011

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem collectSelectTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {f : Frame}
    {mem rdata : ByteArray} {aw amount : UInt256} {currency recipient : AccountAddress} {initial : Value}
    {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables) (hstack : R.length+18 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀) (hf : f.contract = contract)
    (hc : f.locals.get? "currency" = some (.address currency))
    (ht : f.locals.get? "recipient" = some (.address recipient))
    (ha : f.locals.get? "amount" = some (.int (Int.ofNat amount.toNat)))
    (ha0 : f.locals.get? "amountCollected" = some initial) (hb : f.locals.get? "protocolFeesAccrued" = none)
    (hmem : mem.size = 96) (hfree : memLoad ⟨64⟩ mem = ⟨160⟩)
    (h : RD (deployedRuntime v) I g s0 ⟨3255⟩
      (accountWord currency :: amount :: accountWord currency :: accountWord recipient :: R)
      mem aw rdata evm.accountMap k C) :
    ∃ result, ExecFuncBody config f evm (collectProtocolFeesTransition.body.drop 7) result ∧
      uint256ResultTrace (deployedRuntime v) g s0 result := by
  let selected := if amount = ⟨0⟩ then protocolFeesWord evm currency else amount
  have hcond := evalNatEqLiteral (cfg := config) (evm := evm) (k := 0) (evalLocalValue ha)
  change evalExpr? config f evm (.binary .eq (.var "amount") (.intLit 0)) =
    .ok (.bool (decide (amount.toNat = 0))) at hcond
  have heval : evalExpr? config f evm (.ite (.binary .eq (.var "amount") (.intLit 0))
      (.storage {base := "protocolFeesAccrued", steps := [.mindex (.var "currency")]}) (.var "amount")) =
      .ok (.int (Int.ofNat selected.toNat)) := by
    by_cases hz : amount = ⟨0⟩
    · have hn : amount.toNat = 0 := by rw [hz]; rfl
      rw [evalExpr?, hcond, decide_eq_true hn]
      simpa only [selected, if_pos hz] using protocolFeesRead (evm := evm) hf hb (evalLocalValue hc)
    · have hn : amount.toNat ≠ 0 := fun he => hz (uint256_toNat_eq_zero he)
      rw [evalExpr?, hcond, decide_eq_false hn]
      change evalExpr? config f evm (.var "amount") = _
      simpa only [selected, if_neg hz] using evalLocalValue (cfg := config) (evm := evm) ha
  obtain ⟨mem', aw', k', C', hm', hf', rdDebit⟩ : ∃ mem' aw' k' C', mem'.size = 96 ∧
      memLoad ⟨64⟩ mem' = ⟨160⟩ ∧ RD (deployedRuntime v) I g s0 ⟨3283⟩
        (accountWord currency :: accountWord currency :: accountWord recipient :: selected :: ⟨1954⟩ :: selected :: ⟨32⟩ :: R)
        mem' aw' rdata evm.accountMap k' C' := by
    by_cases hz : amount = ⟨0⟩
    · have rd1 := poolManagerBlocks.poolManager_block_3255_fallthrough (by omega) hz h
      obtain ⟨aw2, k2, C2, rd2⟩ := poolManagerBlocks.poolManager_block_3267_packed (by omega) rd1
      let nextMem := twoWordHashMem (accountWord currency) ⟨1⟩ mem
      change RD _ _ _ _ ⟨3283⟩ (accountWord currency :: accountWord currency :: accountWord recipient ::
        solcSlotWordAt (keccakWord ⟨0⟩ ⟨64⟩ nextMem) evm.accountMap I :: ⟨1954⟩ ::
        solcSlotWordAt (keccakWord ⟨0⟩ ⟨64⟩ nextMem) evm.accountMap I :: ⟨32⟩ :: R)
        nextMem aw2 rdata evm.accountMap k2 C2 at rd2
      have hslot : keccakWord ⟨0⟩ ⟨64⟩ nextMem = protocolFeesSlot currency := mappingMemory_slot _ _ hmem
      have hload : protocolFeesWord evm currency = solcSlotWordAt (protocolFeesSlot currency) evm.accountMap I :=
        storageLoad_codeOwner_eq_solcSlotWordAt evm I _ (by rw [hI])
      rw [hslot, ← hload] at rd2
      exact ⟨nextMem, aw2, k2, C2, twoWordHashMem_size_96 _ _ hmem,
        (mappingMemory_load64 _ _ hmem).trans hfree, by simpa only [selected, if_pos hz] using rd2⟩
    · have rd1 := poolManagerBlocks.poolManager_block_3255_taken (by omega) hz
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
      have rd2 := poolManagerBlocks.poolManager_block_3311 (by simp; omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
      exact ⟨mem, _, _, _, hmem, hfree, by simpa only [selected, if_neg hz] using rd2⟩
  let f1 : Frame := {f with locals := f.locals.insert "amountCollected" (.int (Int.ofNat selected.toNat))}
  have hc1 : f1.locals.get? "currency" = some (.address currency) :=
    (store_get_ne _ _ (by decide : ("amountCollected" == "currency") = false)).trans hc
  have ht1 : f1.locals.get? "recipient" = some (.address recipient) :=
    (store_get_ne _ _ (by decide : ("amountCollected" == "recipient") = false)).trans ht
  have hb1 : f1.locals.get? "protocolFeesAccrued" = none :=
    (store_get_ne _ _ (by decide : ("amountCollected" == "protocolFeesAccrued") = false)).trans hb
  obtain ⟨result, hbody, hr⟩ := collectDebitTrace (f := f1) v hstack hI hσ0 hf hc1 ht1
    (store_get_self _ _ _) hb1 hm' hf' rdDebit
  exact ⟨result, execFuncBody_prepend (execBlock_singleton (ExecStmt.assign heval (assignLocalValue ha0))) hbody, hr⟩

theorem collectCurrencyCheckTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw amount : UInt256} {currency recipient : AccountAddress}
    {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables) (hstack : R.length+18 ≤ 1024)
    (hI : evm.executionEnv = I)
    (h : RD (deployedRuntime v) I g s0 ⟨3219⟩ (amount :: accountWord currency :: accountWord recipient :: R)
      mem aw rdata evm.accountMap k C) :
    (¬(currency = AccountAddress.ofNat 0 ∨ syncedCurrency evm ≠ currency) ∧ RDrev (deployedRuntime v) g s0) ∨
    ((currency = AccountAddress.ofNat 0 ∨ syncedCurrency evm ≠ currency) ∧ ∃ k' C',
      RD (deployedRuntime v) I g s0 ⟨3255⟩
        (accountWord currency :: amount :: accountWord currency :: accountWord recipient :: R)
        mem aw rdata evm.accountMap k' C') := by
  have hclean := solcAddrMask_clean (accountWord_canonical currency)
  by_cases hz : currency = AccountAddress.ofNat 0
  · have hw : accountWord currency = ⟨0⟩ := (accountWord_eq_iff currency ⟨0⟩ (by decide)).1 hz
    have rd1 := poolManagerBlocks.poolManager_block_3219_fallthrough (by simp; omega)
      (by change UInt256.isZero (UInt256.isZero (UInt256.land (accountWord currency) solcAddrMask)) = ⟨0⟩
          rw [hclean, hw]; decide) h
    simp only [poolManagerBlocks.poolManager_block_3219_fallthrough_stack] at rd1
    change RD _ _ _ _ ⟨3250⟩ (UInt256.isZero (UInt256.isZero (UInt256.land (accountWord currency) solcAddrMask)) ::
      UInt256.land (accountWord currency) solcAddrMask :: amount :: accountWord currency :: accountWord recipient :: R)
      _ _ _ _ _ _ at rd1
    rw [hclean] at rd1
    have rd2 := poolManagerBlocks.poolManager_block_3250_fallthrough (by simp; omega)
      (by rw [hw]; decide) rd1
    exact .inr ⟨.inl hz, _, _, rd2⟩
  · have hw : accountWord currency ≠ ⟨0⟩ := fun he => hz ((accountWord_eq_iff currency ⟨0⟩ (by decide)).2 he)
    have rd1 := poolManagerBlocks.poolManager_block_3219_taken (by simp; omega)
      (by change UInt256.isZero (UInt256.isZero (UInt256.land (accountWord currency) solcAddrMask)) ≠ ⟨0⟩
          rw [hclean, isZero_eq_zero_of_ne hw]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    change RD _ _ _ _ ⟨3359⟩ (UInt256.isZero (UInt256.isZero (UInt256.land (accountWord currency) solcAddrMask)) ::
      UInt256.land (accountWord currency) solcAddrMask :: amount :: accountWord currency :: accountWord recipient :: R)
      _ _ _ _ _ _ at rd1
    rw [hclean] at rd1
    have rd2 := poolManagerBlocks.poolManager_block_3359 (by simp; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    change RD _ _ _ _ ⟨3250⟩
      (UInt256.eq (UInt256.land (codeOwnerTransientWord I evm.accountMap currencySlot) solcAddrMask) (accountWord currency) ::
        accountWord currency :: amount :: accountWord currency :: accountWord recipient :: R) _ _ _ _ _ _ at rd2
    rw [← transientWord_accountMap hI currencySlot, ← syncedCurrency_word] at rd2
    by_cases hs : syncedCurrency evm = currency
    · rw [hs, uInt256_eq_self] at rd2
      have rd3 := poolManagerBlocks.poolManager_block_3250_taken (by simp; omega) (by decide)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
      exact .inl ⟨by tauto, poolManagerBlocks.poolManager_block_3319
        (by simp only [poolManagerBlocks.poolManager_block_3250_taken_stack, List.length_cons]; omega) rd3⟩
    · have hneq : accountWord (syncedCurrency evm) ≠ accountWord currency := by
        intro he
        have hc := (accountWord_eq_iff (syncedCurrency evm) _ (accountWord_canonical currency)).2 he
        have hc' := (accountWord_eq_iff currency _ (accountWord_canonical currency)).2 rfl
        exact hs (hc.trans hc'.symm)
      have rd3 := poolManagerBlocks.poolManager_block_3250_fallthrough (by simp; omega)
        (uInt256_eq_zero_of_ne (fun he => hneq (uInt256_eq_one_eq he))) rd2
      exact .inr ⟨.inr hs, _, _, rd3⟩

theorem collectCurrencyTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {f : Frame}
    {mem rdata : ByteArray} {aw amount : UInt256} {currency recipient : AccountAddress} {initial : Value}
    {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables) (hstack : R.length+18 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀) (hf : f.contract = contract)
    (hc : f.locals.get? "currency" = some (.address currency))
    (ht : f.locals.get? "recipient" = some (.address recipient))
    (ha : f.locals.get? "amount" = some (.int (Int.ofNat amount.toNat)))
    (ha0 : f.locals.get? "amountCollected" = some initial) (hb : f.locals.get? "protocolFeesAccrued" = none)
    (hmem : mem.size = 96) (hfree : memLoad ⟨64⟩ mem = ⟨160⟩)
    (h : RD (deployedRuntime v) I g s0 ⟨3219⟩ (amount :: accountWord currency :: accountWord recipient :: R)
      mem aw rdata evm.accountMap k C) :
    ∃ result, ExecFuncBody config f evm (collectProtocolFeesTransition.body.drop 5) result ∧
      uint256ResultTrace (deployedRuntime v) g s0 result := by
  have hg := collectCurrencyGuard (evm := evm) hf hc
  rcases collectCurrencyCheckTrace v hstack hI h with ⟨hbad, hr⟩ | ⟨hgood, k', C', rdSelect⟩
  · rw [if_neg hbad] at hg
    exact ⟨.reverted, .execBlockRevert (execBlock_reverted_append (s2 := collectProtocolFeesTransition.body.drop 7) hg), hr⟩
  · rw [if_pos hgood] at hg
    obtain ⟨result, hb', hr⟩ := collectSelectTrace (f := collectCurrencyFrame f evm currency) v hstack hI hσ0
      ((collectCurrencyFrame_contract _ _ _).trans hf)
      (collectCurrencyFrame_get (by decide) (by decide) hc)
      (collectCurrencyFrame_get (by decide) (by decide) ht)
      (collectCurrencyFrame_get (by decide) (by decide) ha)
      (collectCurrencyFrame_get (by decide) (by decide) ha0)
      (collectCurrencyFrame_get (by decide) (by decide) hb) hmem hfree rdSelect
    exact ⟨result, execFuncBody_prepend hg hb', hr⟩

theorem collectBodyTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {f : Frame}
    {mem rdata : ByteArray} {aw : UInt256} {currency recipient : AccountAddress}
    {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables) (hstack : R.length+18 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀) (hf : f.contract = contract)
    (hc : f.locals.get? "currency" = some (.address currency))
    (ht : f.locals.get? "recipient" = some (.address recipient))
    (ha : f.locals.get? "amount" = some (.int (Int.ofNat (calldataWord I.calldata 68).toNat)))
    (hb : f.locals.get? "protocolFeesAccrued" = none) (hctrl : f.locals.get? "protocolFeeController" = none)
    (hmem : mem.size = 96) (hfree : memLoad ⟨64⟩ mem = ⟨160⟩)
    (h : RD (deployedRuntime v) I g s0 ⟨3184⟩ (accountWord currency :: accountWord recipient :: R)
      mem aw rdata evm.accountMap k C) :
    ∃ result, ExecFuncBody config f evm (collectProtocolFeesTransition.body.drop 3) result ∧
      uint256ResultTrace (deployedRuntime v) g s0 result := by
  let f1 : Frame := {f with locals := f.locals.insert "amountCollected" (.int 0)}
  have hinit : ExecStmt config f evm collectProtocolFeesTransition.body[3]! (.ok f1 evm) :=
    ExecStmt.letDecl (value := .int 0) (by simp only [evalExpr?, pure])
  have hguard := protocolControllerGuard (f := f1) (evm := evm) hf
    ((store_get_ne _ _ (by decide : ("amountCollected" == "protocolFeeController") = false)).trans hctrl)
  have hw := protocolControllerWord_accountMap hI
  by_cases hp : protocolControllerAuthorized evm
  · rw [decide_eq_false (not_not.mpr hp)] at hguard
    have he : accountWord I.source = protocolControllerWord evm := by
      simpa only [protocolControllerAuthorized, hI] using hp
    obtain ⟨k', C', rdCurrency⟩ := poolManagerBlocks.poolManager_block_3184_fallthrough (by simp; omega)
      (by change UInt256.sub (accountWord I.source) (UInt256.land (solcSlotWordAt ⟨2⟩ evm.accountMap I) solcAddrMask) = ⟨0⟩
          rw [hw]; exact u256_sub_eq_zero_iff_eq.mpr he) h
    have hc1 : f1.locals.get? "currency" = some (.address currency) :=
      (store_get_ne _ _ (by decide : ("amountCollected" == "currency") = false)).trans hc
    have ht1 : f1.locals.get? "recipient" = some (.address recipient) :=
      (store_get_ne _ _ (by decide : ("amountCollected" == "recipient") = false)).trans ht
    have ha1 : f1.locals.get? "amount" = some (.int (Int.ofNat (calldataWord I.calldata 68).toNat)) :=
      (store_get_ne _ _ (by decide : ("amountCollected" == "amount") = false)).trans ha
    have hb1 : f1.locals.get? "protocolFeesAccrued" = none :=
      (store_get_ne _ _ (by decide : ("amountCollected" == "protocolFeesAccrued") = false)).trans hb
    obtain ⟨result, hb', hr⟩ := collectCurrencyTrace (I := I) (evm := evm) (f := f1) v hstack hI hσ0 hf hc1 ht1 ha1
      (store_get_self _ _ _) hb1 hmem hfree rdCurrency
    exact ⟨result, execFuncBody_prepend (ExecBlock.consNormal hinit
      (ExecBlock.consNormal (ExecStmt.iteFalse hguard ExecBlock.nil) ExecBlock.nil)) hb', hr⟩
  · rw [decide_eq_true hp] at hguard
    have he : accountWord I.source ≠ protocolControllerWord evm := by
      simpa only [protocolControllerAuthorized, hI] using hp
    obtain ⟨k', C', rdRevert⟩ := poolManagerBlocks.poolManager_block_3184_taken (by simp; omega)
      (by change UInt256.sub (accountWord I.source) (UInt256.land (solcSlotWordAt ⟨2⟩ evm.accountMap I) solcAddrMask) ≠ ⟨0⟩
          rw [hw]; exact u256_sub_ne_zero_of_ne he)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact ⟨.reverted, .execBlockRevert (ExecBlock.consNormal hinit (ExecBlock.consRevert
      (ExecStmt.iteTrue hguard (ExecBlock.consRevert (ExecStmt.requireFalse (by simp only [evalExpr?, pure])))))),
      poolManagerBlocks.poolManager_block_3423
        (by simp only [poolManagerBlocks.poolManager_block_3184_taken_stack, List.length_cons]; omega) rdRevert⟩

end Benchmarks.UniswapV4PoolManager
