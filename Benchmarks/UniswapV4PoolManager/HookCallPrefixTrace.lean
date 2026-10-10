import Benchmarks.UniswapV4PoolManager.HookFailureTrace
import Benchmarks.UniswapV4PoolManager.RawCallBridge
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_045
import Benchmarks.UniswapV4PoolManager.BytesObjectMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def hookCallActiveWords (aw ptr : UInt256) (data : ByteArray) : UInt256 :=
  callActiveWords (M aw ptr ⟨32⟩) (ptr+⟨32⟩) (UInt256.ofNat data.size) ⟨0⟩ ⟨0⟩

theorem hookCallPrefixTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem data rdata : ByteArray} {aw ptr ret : UInt256} {hook : AccountAddress}
    {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length+11 ≤ 1024) (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀)
    (hdata : BytesObjectView mem ptr data) (hsmall : data.size ≤ Ethereum.EVM.maxReturnDataSizeByGas)
    (hfit : ptr.toNat+32 < UInt256.size)
    (h : RD (deployedRuntime v) I g s0 ⟨16165⟩
      (accountWord hook :: ptr :: ret :: R) mem aw rdata evm.accountMap k C) :
    ∃ evm' z out k' C', callViaEVM evm hook 0 data (z, evm', out) ∧
      evm'.executionEnv = I ∧ evm'.σ₀ = s0.σ₀ ∧ out.size < 2^138 ∧
      (if z = true then RD (deployedRuntime v) I g s0 ⟨16189⟩
        (ptr :: accountWord hook :: ret :: (ptr+⟨32⟩) :: R)
        mem (hookCallActiveWords aw ptr data) out evm'.accountMap k' C'
      else RDrev (deployedRuntime v) g s0) := by
  have hsize : data.size < UInt256.size := lt_of_le_of_lt hsmall (by decide)
  have hptr : (ptr+⟨32⟩).toNat = ptr.toNat+32 := uadd_word_ofNat_toNat ptr 32 hfit
  have hinput : mem.readWithPadding (ptr+⟨32⟩).toNat (memLoad ptr mem).toNat = data := by
    rw [hptr, hdata.lengthWord, UInt256.toNat_ofNat_of_lt hsize]
    exact hdata.payload
  have rd1 := poolManagerBlocks.poolManager_block_16165 hstack h
  simp only [poolManagerBlocks.poolManager_block_16165_stack] at rd1
  obtain ⟨evm', z, out, k2, C2, hc, henv, hworld, rd2, ho⟩ := rawCallBridge hI hσ0 (Or.inr rfl) rd1
    (by immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨16183⟩ : UInt256),
      UInt8.ofNat 241, .CALL, none, poolManagerBlocks.immutableLayout_inBounds,
      poolManagerBlocks.immutableTemplate_size64)) hinput hsmall
    (by simp only [List.length_cons]; omega)
  have hc' : callViaEVM evm hook 0 data (z, evm', out) := by
    simpa only [accountWord, accountAddress_roundtrip] using hc
  simp only [callOutputMem_zero, hdata.lengthWord] at rd2
  cases z with
  | false =>
    refine ⟨evm', false, out, 0, 0, hc', henv, hworld, ho, ?_⟩
    simp only [Bool.false_eq_true, if_false]
    have rd3 := poolManagerBlocks.poolManager_block_16184_taken (by simp only [List.length_cons]; omega)
      (by decide) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
    exact hookFailureTrace v (by omega) rd3
  | true =>
    have rd3 := poolManagerBlocks.poolManager_block_16184_fallthrough
      (by simp only [List.length_cons]; omega) (by decide) rd2
    exact ⟨evm', true, out, _, _, hc', henv, hworld, ho, rd3⟩

end Benchmarks.UniswapV4PoolManager
