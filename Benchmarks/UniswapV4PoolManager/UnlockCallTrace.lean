import Benchmarks.UniswapV4PoolManager.UnlockABI
import Benchmarks.UniswapV4PoolManager.CallGasEvidence
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_025
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_026

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

theorem unlockCallFailureTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+6 ≤ 1024)
    (hout : out.size < UInt256.size)
    (h : RD (deployedRuntime v) I g s0 ⟨9036⟩ (⟨0⟩ :: ⟨160⟩ :: R) mem aw out σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd := poolManager_block_9036_taken (by omega) (by decide)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  exact poolManager_block_9410
    (by simp only [poolManager_block_9036_taken_stack, List.length_cons]; omega)
    (by change 0+(UInt256.ofNat out.size).toNat ≤ out.size
        rw [UInt256.toNat_ofNat_of_lt hout]; omega) rd

theorem unlockCallTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata data : ByteArray} {aw ending : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+8 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀)
    (hencode : config.externalABI.encode? "unlockCallback" [.bytes data] =
      some (mem.readWithPadding 160 (UInt256.sub ending ⟨160⟩).toNat))
    (hsmall : (mem.readWithPadding 160 (UInt256.sub ending ⟨160⟩).toNat).size ≤ maxReturnDataSizeByGas)
    (h : RD (deployedRuntime v) I g s0 ⟨9029⟩
      (ending :: ⟨160⟩ :: ⟨160⟩ :: ⟨0⟩ :: ⟨160⟩ :: R) mem aw rdata evm.accountMap k C) :
    (X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass) ∨
    ∃ evm' z out, typedCallViaEVM config evm I.source "unlockCallback" 0 [.bytes data] (z, evm', out) true ∧
      evm'.executionEnv = I ∧ evm'.σ₀ = s0.σ₀ ∧ out.size < 2^138 ∧
      (if z then ∃ (w : ZeroCallGasEvidence evm I.source
          (mem.readWithPadding 160 (UInt256.sub ending ⟨160⟩).toNat) evm' true out) (k' C' : Nat),
        C+154+w.spent+Cₘ (callActiveWords aw ⟨160⟩ (UInt256.sub ending ⟨160⟩) ⟨160⟩ ⟨0⟩) ≤ C'+Cₘ aw ∧
        RD (deployedRuntime v) I g s0 ⟨9242⟩ (⟨160⟩ :: ⟨0⟩ :: R) mem
          (callActiveWords aw ⟨160⟩ (UInt256.sub ending ⟨160⟩) ⟨160⟩ ⟨0⟩) out evm'.accountMap k' C'
       else RDrev (deployedRuntime v) g s0) := by
  have rd := poolManager_block_9029 (by simp only [List.length_cons]; omega) h
  dsimp only [poolManager_block_9029_stack] at rd
  have hdec : decode (deployedRuntime v) ⟨9035⟩ = some (.CALL, .none) := by
    immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨9035⟩ : UInt256), UInt8.ofNat 241, .CALL, none, immutableLayout_inBounds, immutableTemplate_size64)
  by_cases hd : I.depth = 1024
  · obtain ⟨k', C', hr⟩ := RD.callDepthLimit rd hdec hd (by simp only [List.length_cons]; omega)
    have hc := callNotMade_depthLimit (cfg := config) (evm := evm) (tgt := I.source)
      (name := "unlockCallback") (args := [.bytes data]) (callPerm := true)
      hencode (by rw [hI]; exact hd)
    refine .inr ⟨_, false, .empty, hc, hI, hσ0, by decide, ?_⟩
    apply unlockCallFailureTrace (R := R) (out := .empty) v (by omega) (by decide)
    simpa only [accountAddress_roundtrip] using hr
  · have hdepth : I.depth.val < 1024 := by
      have := I.depth.isLt
      have : I.depth.val ≠ 1024 := fun he => hd (Fin.ext he)
      omega
    rcases RD.callWithCost rd hdec hdepth (by simp only [List.length_cons]; omega) with hoog | hcall
    · exact .inl hoog
    obtain ⟨σ', z, out, Ain, callGas, gasLeft, A', k', C', hθ, hr, hcost, hout⟩ := hcall
    let evm' : EVM.State := {evm with accountMap := σ', substate := A'}
    have hθ' : (evm'.accountMap, gasLeft, evm'.substate, z, out) =
        Ethereum.EVM.Θ evm.accountMap evm.σ₀ Ain evm.executionEnv.codeOwner evm.executionEnv.sender
          I.source (toExecute evm.accountMap I.source) callGas (UInt256.ofNat evm.executionEnv.gasPrice)
          ⟨0⟩ ⟨0⟩ (mem.readWithPadding 160 (UInt256.sub ending ⟨160⟩).toNat)
          (evm.executionEnv.depth+1) evm.executionEnv.header evm.executionEnv.blobVersionedHashes
          evm.executionEnv.blocks evm.executionEnv.perm := by
      simpa only [evm', hI, hσ0, accountAddress_roundtrip] using hθ
    have hc : typedCallViaEVM config evm I.source "unlockCallback" 0 [.bytes data] (z, evm', out) true := by
      refine ⟨_, hencode, ?_⟩
      apply callViaEVM.callMade (g' := gasLeft) (A' := A') wordOfInt_zero.symm
        ⟨callGas, Ain, ?_⟩ rfl (Fin.zero_le _) (by rw [hI]; exact hd)
      simpa only [Bool.true_and] using hθ'
    have ho : out.size < 2^138 := Theta_returnData_size_lt_2pow138_of_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hθ' hsmall
    change RD _ _ _ _ ⟨9036⟩ ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨160⟩ :: R)
      (callOutputMem mem out ⟨160⟩ ⟨0⟩) _ _ _ _ _ at hr
    rw [callOutputMem_zero] at hr
    refine .inr ⟨evm', z, out, hc, hI, hσ0, ho, ?_⟩
    cases z with
    | false => exact unlockCallFailureTrace v (by omega) hout hr
    | true =>
      let w : ZeroCallGasEvidence evm I.source
          (mem.readWithPadding 160 (UInt256.sub ending ⟨160⟩).toNat) evm' true out :=
        ⟨callGas, gasLeft, Ain, hθ'⟩
      have rd1 := poolManager_block_9036_fallthrough (by omega) (by decide) hr
      have rd2 := poolManager_block_9043_taken (by omega) (by decide)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
      refine ⟨w, _, _, ?_, rd2⟩
      dsimp only [w, ZeroCallGasEvidence.spent]
      change C+14+(Cₘ (callActiveWords aw ⟨160⟩ (UInt256.sub ending ⟨160⟩) ⟨160⟩ ⟨0⟩)-Cₘ aw)+100+
        (callGas.toNat-gasLeft.toNat) ≤ C' at hcost
      omega

end Benchmarks.UniswapV4PoolManager
