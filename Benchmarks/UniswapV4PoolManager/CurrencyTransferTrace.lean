import Benchmarks.UniswapV4PoolManager.CurrencyTransferReturnTrace
import Benchmarks.UniswapV4PoolManager.RawCallBridge
import Benchmarks.UniswapV4PoolManager.UnitResultTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_036

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem currencyTransferMemoryTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {f : Frame}
    {mem rdata : ByteArray} {aw ptr ret amount : UInt256} {currency recipient : AccountAddress}
    {k C : Nat} {R : List UInt256}
    (P : ByteArray → Prop) (v : PoolManagerImmutables) (hstack : R.length+16 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀)
    (hc : f.locals.get? "currency" = some (.address currency))
    (ht : f.locals.get? "to" = some (.address recipient))
    (ha : f.locals.get? "amount" = some (.int (Int.ofNat amount.toNat)))
    (hmem : P mem)
    (hfit : ptr.toNat+67 < UInt256.size) (hgap : ptr.toNat-mem.size < USize.size)
    (hfree : memLoad ⟨64⟩ mem = ptr)
    (hcleanMem : ∀ out : ByteArray, out.size < UInt256.size →
      P (currencyTransferCleanMemory (callOutputMem
        (twoWordCallMemory mem ptr.toNat transferSelectorWord (accountWord recipient) amount) out ⟨0⟩ ⟨32⟩) ptr))
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨12792⟩
      (accountWord currency :: accountWord recipient :: amount :: ret :: R) mem aw rdata evm.accountMap k C) :
    ∃ result, ExecFuncBody config f evm currencyTransferFunction.body result ∧
      unitContinuationTraceWithMemory P (deployedRuntime v) I g s0 ret R result := by
  have hclean := solcAddrMask_clean (accountWord_canonical currency)
  by_cases hn : currency = AccountAddress.ofNat 0
  · subst currency
    have rd1 := poolManagerBlocks.poolManager_block_12792_fallthrough (by simp; omega) (by decide) h
    have rd2 := poolManagerBlocks.poolManager_block_12825 (by simp; omega) rd1
    simp only [poolManagerBlocks.poolManager_block_12825_stack] at rd2
    have hdecode : decode (deployedRuntime v) ⟨12834⟩ = some (.CALL, .none) := by
      immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨12834⟩ : UInt256),
        UInt8.ofNat 241, .CALL, none, poolManagerBlocks.immutableLayout_inBounds, poolManagerBlocks.immutableTemplate_size64)
    by_cases hp : I.perm = true ∨ amount = ⟨0⟩
    · obtain ⟨evm', z, out, k3, C3, hcall, _, _, rd3, ho⟩ := rawCallBridge hI hσ0 hp rd2 hdecode
        (byteArray_readWithPadding_zero mem 0) (by decide) (by simp; omega)
      have hcall' : callViaEVM evm recipient (Int.ofNat amount.toNat) .empty (z, evm', out) := by
        simpa only [accountWord, accountAddress_roundtrip] using hcall
      obtain ⟨f', hb⟩ := currencyTransferNativeBody hc ht ha hcall'
      cases z with
      | false =>
        have rd4 := poolManagerBlocks.poolManager_block_12835_taken (by simp; omega) (by decide)
          (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3
        have rd5 := poolManagerBlocks.poolManager_block_12842 (by simp; omega)
          (by rw [UInt256.toNat_ofNat_of_lt (lt_trans ho (by decide))]; change 0+out.size ≤ out.size; omega) rd4
        exact ⟨.reverted, hb, rd5⟩
      | true =>
        have rd4 := poolManagerBlocks.poolManager_block_12835_fallthrough (by simp; omega) (by decide) rd3
        have rd5 := poolManagerBlocks.poolManager_block_12840 (by simp; omega) hret rd4
        have hm : P (callOutputMem mem out ⟨0⟩ ⟨0⟩) := by rw [callOutputMem_zero]; exact hmem
        exact ⟨.returned f' evm' none, hb, _, _, _, _, _, hm, rd5⟩
    · have hperm : I.perm = false := by cases he : I.perm <;> simp_all
      have hamount : amount ≠ ⟨0⟩ := fun he => hp (.inr he)
      exact ⟨.staticViolation, currencyTransferNativeStatic hc ht ha hamount (by rw [hI]; exact hperm),
        RD.callValueStatic rd2 hperm hamount hdecode (by simp; omega)⟩
  · have hnword : accountWord currency ≠ ⟨0⟩ := fun he => hn ((accountWord_eq_iff currency ⟨0⟩ (by decide)).2 he)
    have rd1 := poolManagerBlocks.poolManager_block_12792_taken (by simp; omega)
      (by change UInt256.land (accountWord currency) solcAddrMask ≠ ⟨0⟩; rw [hclean]; exact hnword)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    change RD _ _ _ _ _ (accountWord currency :: UInt256.land (accountWord currency) solcAddrMask ::
      amount :: accountWord recipient :: ret :: R) _ _ _ _ _ _ at rd1
    rw [hclean] at rd1
    obtain ⟨aw2, k2, C2, rd2⟩ := poolManagerBlocks.poolManager_block_13034_packed (by simp; omega) rd1
    have h4 : (ptr+UInt256.ofNat 4).toNat = ptr.toNat+4 := uadd_word_ofNat_toNat ptr 4 (by omega)
    have h36 : (ptr+UInt256.ofNat 36).toNat = ptr.toNat+36 := uadd_word_ofNat_toNat ptr 36 (by omega)
    have hfree' : memLoad (UInt256.ofNat 64) mem = ptr := hfree
    have htoClean : UInt256.land (accountWord recipient) (UInt256.ofNat 1461501637330902918203684832716283019655932542975) =
        accountWord recipient := solcAddrMask_clean (accountWord_canonical recipient)
    simp only [poolManagerBlocks.poolManager_block_13034_stack, poolManagerBlocks.poolManager_block_13034_memory,
      hfree', h4, h36, htoClean] at rd2
    let requestMem := twoWordCallMemory mem ptr.toNat transferSelectorWord (accountWord recipient) amount
    change RD _ _ _ _ ⟨13121⟩ (_ :: accountWord currency :: ⟨0⟩ :: ptr :: ⟨68⟩ :: ⟨0⟩ :: ⟨32⟩ ::
      ⟨64⟩ :: ⟨0⟩ :: ptr :: accountWord currency :: ret :: R) requestMem aw2 rdata evm.accountMap k2 C2 at rd2
    obtain ⟨evm', z, out, k3, C3, hcall, _, _, rd3, ho⟩ := rawCallBridge hI hσ0 (Or.inr rfl) rd2
      (by immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨13121⟩ : UInt256),
        UInt8.ofNat 241, .CALL, none, poolManagerBlocks.immutableLayout_inBounds, poolManagerBlocks.immutableTemplate_size64))
      (transferCallMemory_read _ _ _ _ hgap) (by rw [transferPayload_size]; decide) (by simp; omega)
    have hcall' : callViaEVM evm currency 0 (transferPayload recipient amount) (z, evm', out) := by
      simpa only [accountWord, accountAddress_roundtrip] using hcall
    have ho256 := lt_trans ho (show 2^138 < UInt256.size from by decide)
    have hmsize : requestMem.size = max mem.size (ptr.toNat+68) := twoWordCallMemory_size _ _ _ _ _ hgap
    have houtmem : (callOutputMem requestMem out ⟨0⟩ ⟨32⟩).size = requestMem.size := by
      unfold callOutputMem
      rw [callOutputLen32 ho256]
      exact byteArray_write_size_of_inBounds out requestMem 0 (min 32 out.size) (Nat.min_le_right _ _)
        (by rw [hmsize]; omega)
    have hword : 32 ≤ out.size → memLoad ⟨0⟩ (callOutputMem requestMem out ⟨0⟩ ⟨32⟩) = returnedBalanceWord out := by
      intro hlo
      exact mloadWordValue_of_readWithPadding (by rw [houtmem, hmsize]; change 0 < _; omega)
        (copiedReturnWord_read hlo ho256 (Nat.zero_le _))
    have hr := currencyTransferTokenReturnTrace P v (by omega) ho256 hword (hcleanMem out ho256) hret rd3
    obtain ⟨f', hb⟩ := currencyTransferTokenBody hc ht ha hn hcall'
    rcases hr with ⟨hbad, hr⟩ | ⟨hz, hv, mem', aw', k', C', hm, hr⟩
    · rw [if_neg hbad] at hb
      exact ⟨.reverted, hb, hr⟩
    · rw [if_pos ⟨hz, hv⟩] at hb
      exact ⟨.returned f' evm' none, hb, mem', aw', out, k', C', hm, hr⟩

theorem currencyTransferTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {f : Frame}
    {mem rdata : ByteArray} {aw ptr ret amount : UInt256} {currency recipient : AccountAddress}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+16 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀)
    (hc : f.locals.get? "currency" = some (.address currency))
    (ht : f.locals.get? "to" = some (.address recipient))
    (ha : f.locals.get? "amount" = some (.int (Int.ofNat amount.toNat)))
    (hfit : ptr.toNat+67 < UInt256.size) (hgap : ptr.toNat-mem.size < USize.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨12792⟩
      (accountWord currency :: accountWord recipient :: amount :: ret :: R) mem aw rdata evm.accountMap k C) :
    ∃ result, ExecFuncBody config f evm currencyTransferFunction.body result ∧
      unitContinuationTrace (deployedRuntime v) I g s0 ret R result := by
  obtain ⟨result, hb, hr⟩ := currencyTransferMemoryTrace (fun _ => True) v hstack hI hσ0 hc ht ha
    trivial hfit hgap hfree (fun _ _ => trivial) hret h
  exact ⟨result, hb, unitContinuationTraceWithMemory_forget hr⟩

end Benchmarks.UniswapV4PoolManager
