import Benchmarks.UniswapV4PoolManager.HookCallPrefixTrace
import Benchmarks.UniswapV4PoolManager.CallCostTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

-- GENERALIZES hookCallPrefixTrace by retaining the memory cost paid across the external call.
theorem hookCallPaidPrefixTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem data rdata : ByteArray} {aw ptr ret : UInt256} {hook : AccountAddress}
    {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length+11 ≤ 1024) (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀)
    (hdata : BytesObjectView mem ptr data) (hsmall : data.size ≤ Ethereum.EVM.maxReturnDataSizeByGas)
    (hfit : ptr.toNat+32 < UInt256.size) (hpaid : Cₘ aw ≤ C)
    (h : RD (deployedRuntime v) I g s0 ⟨16165⟩
      (accountWord hook :: ptr :: ret :: R) mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ post z out, callViaEVM evm hook 0 data (z, post, out) ∧
      post.executionEnv = I ∧ post.σ₀ = s0.σ₀ ∧ out.size < 2^138 ∧
      (if z = true then ∃ k' C', Cₘ (hookCallActiveWords aw ptr data) ≤ C' ∧
        RD (deployedRuntime v) I g s0 ⟨16189⟩
          (ptr :: accountWord hook :: ret :: (ptr+⟨32⟩) :: R)
          mem (hookCallActiveWords aw ptr data) out post.accountMap k' C'
      else RDrev (deployedRuntime v) g s0) := by
  have hsize : data.size < UInt256.size := lt_of_le_of_lt hsmall (by decide)
  have hptr : (ptr+UInt256.ofNat 32).toNat = ptr.toNat+32 := uadd_word_ofNat_toNat ptr 32 hfit
  have hinput : mem.readWithPadding (ptr+UInt256.ofNat 32).toNat (memLoad ptr mem).toNat = data := by
    rw [hptr, hdata.lengthWord, UInt256.toNat_ofNat_of_lt hsize]
    exact hdata.payload
  have rd1 := poolManagerBlocks.poolManager_block_16165 hstack h
  dsimp only [poolManagerBlocks.poolManager_block_16165_stack] at rd1
  have hdec : decode (deployedRuntime v) ⟨16183⟩ = some (.CALL, .none) := by
    immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨16183⟩ : UInt256),
      UInt8.ofNat 241, .CALL, none, poolManagerBlocks.immutableLayout_inBounds,
      poolManagerBlocks.immutableTemplate_size64)
  by_cases hd : I.depth = 1024
  · obtain ⟨k2, C2, rd2⟩ := RD.callDepthLimit rd1 hdec hd (by simp only [List.length_cons]; omega)
    have hc : callViaEVM evm hook 0 data
        (false, {evm with substate := (evm.addAccessedAccount hook).substate}, .empty) := by
      apply callViaEVM.callNotMade rfl rfl
      intro hh
      exact hh.2 (by rw [hI]; exact hd)
    have rd3 := poolManagerBlocks.poolManager_block_16184_taken (by simp only [List.length_cons]; omega)
      (by decide) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
    exact .inr ⟨_, false, .empty, hc, hI, hσ0, by decide, hookFailureTrace v (by omega) rd3⟩
  have hdepth : I.depth.val < 1024 := by
    have := I.depth.isLt
    have : I.depth.val ≠ 1024 := fun he => hd (Fin.ext he)
    omega
  rcases RD.callWithCost rd1 hdec hdepth (by simp only [List.length_cons]; omega) with hog | hcall
  · exact .inl hog
  obtain ⟨σ', z, out, Ain, callGas, gasLeft, A', k2, C2, hθ, rd2, hcost, _⟩ := hcall
  rw [hinput] at hθ
  let post : State := {evm with accountMap := σ', substate := A'}
  have hc : callViaEVM evm hook 0 data (z, post, out) := by
    apply callViaEVM.callMade (g' := gasLeft) (A' := A') wordOfInt_zero.symm
      ⟨callGas, Ain, ?_⟩ rfl (Fin.zero_le _) (by rw [hI]; exact hd)
    simpa only [post, hI, hσ0, accountWord, accountAddress_roundtrip, Bool.true_and] using hθ
  have ho : out.size < 2^138 :=
    Theta_returnData_size_lt_2pow138_of_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hθ hsmall
  change RD _ _ _ _ ⟨16184⟩
    ((if z then ⟨1⟩ else ⟨0⟩) :: ptr :: accountWord hook :: ret :: (ptr+⟨32⟩) :: R)
    (callOutputMem mem out ⟨0⟩ ⟨0⟩) _ _ _ _ _ at rd2
  simp only [callOutputMem_zero, hdata.lengthWord] at rd2 hcost
  refine .inr ⟨post, z, out, hc, hI, hσ0, ho, ?_⟩
  cases z with
  | false =>
    have rd3 := poolManagerBlocks.poolManager_block_16184_taken (by simp only [List.length_cons]; omega)
      (by decide) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
    exact hookFailureTrace v (by omega) rd3
  | true =>
    have rd3 := poolManagerBlocks.poolManager_block_16184_fallthrough
      (by simp only [List.length_cons]; omega) (by decide) rd2
    refine ⟨_, _, ?_, rd3⟩
    change Cₘ (callActiveWords (M aw ptr ⟨32⟩) (ptr+⟨32⟩) (UInt256.ofNat data.size) ⟨0⟩ ⟨0⟩) ≤ _
    change C+(47+(Cₘ (M aw ptr ⟨32⟩)-Cₘ aw))+
      (Cₘ (callActiveWords (M aw ptr ⟨32⟩) (ptr+⟨32⟩) (UInt256.ofNat data.size) ⟨0⟩ ⟨0⟩)-
        Cₘ (M aw ptr ⟨32⟩))+100+(callGas.toNat-gasLeft.toNat) ≤ C2 at hcost
    omega

end Benchmarks.UniswapV4PoolManager
