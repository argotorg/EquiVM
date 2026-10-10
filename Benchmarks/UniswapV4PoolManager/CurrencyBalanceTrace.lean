import Benchmarks.UniswapV4PoolManager.CurrencyBalanceSource
import Benchmarks.UniswapV4PoolManager.CurrencyBalanceReturnTrace
import Benchmarks.UniswapV4PoolManager.StaticCallBridge

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem currencyBalanceWordTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw ptr ret currencyWord : UInt256} {currency : AccountAddress} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+10 ≤ 1024)
    (hcurrency : UInt256.land currencyWord solcAddrMask = accountWord currency)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀) (hn : currency ≠ AccountAddress.ofNat 0)
    (hptr : 96 ≤ ptr.toNat) (hfit : ptr.toNat+63 ≤ solcMaxU64)
    (hgap : ptr.toNat-mem.size < USize.size) (hfree : memLoad ⟨64⟩ mem = ptr)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨14994⟩ (currencyWord :: ret :: R) mem aw rdata evm.accountMap k C) :
    ∃ evm' z out,
      typedCallViaEVM config evm currency "balanceOf" 0 [.address evm.executionEnv.codeOwner] (z, evm', out) false ∧
      evm'.executionEnv = I ∧ evm'.σ₀ = s0.σ₀ ∧ out.size < 2^138 ∧
      ((¬(z = true ∧ 32 ≤ out.size) ∧ RDrev (deployedRuntime v) g s0) ∨
       (z = true ∧ 32 ≤ out.size ∧ ∃ mem' aw' k' C',
         96 ≤ mem'.size ∧ (memLoad ⟨64⟩ mem').toNat ≤ mem'.size ∧
         RD (deployedRuntime v) I g s0 ret (returnedBalanceWord out :: R) mem' aw' out evm'.accountMap k' C')) := by
  have hclean : UInt256.land solcAddrMask currencyWord = accountWord currency := by
    rw [u256_land_comm]; exact hcurrency
  have hnword : accountWord currency ≠ ⟨0⟩ := fun he => hn ((accountWord_eq_iff currency ⟨0⟩ (by decide)).2 he)
  have rd1 := poolManagerBlocks.poolManager_block_14994_taken (by simp; omega)
    (by change UInt256.land solcAddrMask currencyWord ≠ ⟨0⟩; rw [hclean]; exact hnword)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  change RD _ _ _ _ _ (UInt256.land solcAddrMask currencyWord :: ret :: R) _ _ _ _ _ _ at rd1
  rw [hclean] at rd1
  obtain ⟨aw2, k2, C2, rd2⟩ := poolManagerBlocks.poolManager_block_15026_packed (by simp; omega) rd1
  have h4 : (ptr+UInt256.ofNat 4).toNat = ptr.toNat+4 :=
    uadd_word_ofNat_toNat ptr 4 (by change _ < 2^256; change _ ≤ 2^64-1 at hfit; omega)
  have hfree' : memLoad (UInt256.ofNat 64) mem = ptr := hfree
  simp only [poolManagerBlocks.poolManager_block_15026_stack, poolManagerBlocks.poolManager_block_15026_memory, hfree', h4] at rd2
  change RD _ _ _ _ ⟨15081⟩ (_ :: accountWord currency :: ptr :: ⟨36⟩ :: ptr :: ⟨32⟩ :: ptr :: ret :: R)
    (singleWordCallMemory mem ptr.toNat balanceOfSelectorWord (accountWord I.codeOwner)) aw2 rdata evm.accountMap k2 C2 at rd2
  let requestMem := singleWordCallMemory mem ptr.toNat balanceOfSelectorWord (accountWord I.codeOwner)
  have hencode := balanceOfCallMemory_encode mem ptr.toNat I.codeOwner hgap
  have hsmall : (requestMem.readWithPadding ptr.toNat 36).size ≤ Ethereum.EVM.maxReturnDataSizeByGas := by
    rw [singleWordCallMemory_read _ _ _ _ hgap]
    rw [ByteArray.size_append, ByteArray.size_extract, toByteArray_size, toByteArray_size]
    decide
  obtain ⟨evm', z, out, k3, C3, hcall, hI', hσ0', rd3, ho⟩ := typedStaticCallBridge hI hσ0 rd2
    (by immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨15081⟩ : UInt256),
      UInt8.ofNat 250, .STATICCALL, none, poolManagerBlocks.immutableLayout_inBounds, poolManagerBlocks.immutableTemplate_size64))
    hencode hsmall (by simp; omega)
  have hc : typedCallViaEVM config evm currency "balanceOf" 0 [.address evm.executionEnv.codeOwner] (z, evm', out) false := by
    rw [hI, ← accountAddress_roundtrip currency]
    exact hcall
  have ho256 : out.size < UInt256.size := lt_trans ho (by decide)
  have hmsize : requestMem.size = max mem.size (ptr.toNat+36) := singleWordCallMemory_size _ _ _ _ hgap
  have houtmem : (callOutputMem requestMem out ptr ⟨32⟩).size = requestMem.size := by
    unfold callOutputMem
    rw [callOutputLen32 ho256]
    exact byteArray_write_size_of_inBounds out requestMem ptr.toNat (min 32 out.size) (Nat.min_le_right _ _)
      (by rw [hmsize]; omega)
  have hr := currencyBalanceReturnTrace (mem := callOutputMem requestMem out ptr ⟨32⟩) v hstack hptr hfit
    (by rw [houtmem, hmsize]; omega) ho256
    (fun hlo => copiedReturnWord_read hlo ho256 (by rw [hmsize]; omega)) hret rd3
  exact ⟨evm', z, out, hc, hI', hσ0', ho, hr⟩


-- Canonical address specialization used after ABI decoding.
theorem currencyBalanceTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw ptr ret : UInt256} {currency : AccountAddress} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+10 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀) (hn : currency ≠ AccountAddress.ofNat 0)
    (hptr : 96 ≤ ptr.toNat) (hfit : ptr.toNat+63 ≤ solcMaxU64)
    (hgap : ptr.toNat-mem.size < USize.size) (hfree : memLoad ⟨64⟩ mem = ptr)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨14994⟩ (accountWord currency :: ret :: R) mem aw rdata evm.accountMap k C) :
    ∃ evm' z out,
      typedCallViaEVM config evm currency "balanceOf" 0 [.address evm.executionEnv.codeOwner] (z, evm', out) false ∧
      evm'.executionEnv = I ∧ evm'.σ₀ = s0.σ₀ ∧ out.size < 2^138 ∧
      ((¬(z = true ∧ 32 ≤ out.size) ∧ RDrev (deployedRuntime v) g s0) ∨
       (z = true ∧ 32 ≤ out.size ∧ ∃ mem' aw' k' C',
         RD (deployedRuntime v) I g s0 ret (returnedBalanceWord out :: R) mem' aw' out evm'.accountMap k' C')) := by
  obtain ⟨evm', z, out, hc, hI', hσ0', ho, hr⟩ := currencyBalanceWordTrace v hstack
    (solcAddrMask_clean (accountWord_canonical currency)) hI hσ0 hn hptr hfit hgap hfree hret h
  refine ⟨evm', z, out, hc, hI', hσ0', ho, ?_⟩
  rcases hr with hb | ⟨hz, hlo, mem', aw', k', C', _, _, hr⟩
  · exact .inl hb
  · exact .inr ⟨hz, hlo, mem', aw', k', C', hr⟩

end Benchmarks.UniswapV4PoolManager
