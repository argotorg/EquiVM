import Benchmarks.Morpho.MetaMorphoV1_1.SkimSource
import Benchmarks.Morpho.MetaMorphoV1_1.SkimBalanceRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.SkimBalanceMemory
import Benchmarks.Morpho.MetaMorphoV1_1.SafeTransferRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.SkimEvent

/-! Composition of Skim's two opaque token calls and final event. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory
attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem skimBodySimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (imms : Store) (token : AccountAddress)
    (hstack : R.length + 16 ≤ 1024) (hs : SourceState s0 I σ evm)
    (hpre : ABlock config evm ⟨contract, skimLocals token, imms⟩ skimTransition.body
      (skimFrame evm imms token) (skimTransition.body.drop 5))
    (rd : RD (deployedRuntime v) I g s0 ⟨2755⟩
      (UInt256.ofNat token.toNat :: UInt256.ofNat (skimRecipientAddress evm).toNat :: R)
      solcFreePtrMem aw rdata σ k C) :
    (ExecTransitionBody config contract evm (skimLocals token) skimTransition.body .reverted imms ∧
      RDrev (deployedRuntime v) g s0) ∨
    (∃ (evm' : State) (frame' : Frame),
      ExecTransitionBody config contract evm (skimLocals token) skimTransition.body
        (.returned frame' evm' none) imms ∧
      RDret (deployedRuntime v) g s0 evm'.accountMap ByteArray.empty) ∨
    (ExecTransitionBody config contract evm (skimLocals token) skimTransition.body
      .staticViolation imms ∧ RDstatic (deployedRuntime v) g s0) := by
  obtain ⟨evmBalance, ok, out, aw1, k1, C1, hcall, hs1, hout, h1⟩ :=
    skimBalanceCall v token (by omega) hs (by decide : (⟨128⟩ : UInt256).toNat < 2 ^ 64)
      solcFreePtrMem_mload64 rd
  have hcallSource : typedCallViaEVM config evm token "balanceOf" 0
      [.address evm.executionEnv.codeOwner] (ok, evmBalance, out) false := by
    simpa only [hs.env] using hcall
  cases ok with
  | false =>
      refine .inl ⟨ExecFuncBody.execBlockRevert (hpre.run (ExecBlock.consRevert
        (skimBalanceReverts imms token false out hcallSource (.inl rfl)))), ?_⟩
      exact skimBalanceCallFailure v (by simp only [List.length_cons]; omega) hout h1
  | true =>
      rcases skimBalanceReturnAllocation v (by simp only [List.length_cons]; omega) hout
        (by decide : allocationFits ⟨128⟩ ⟨32⟩) h1 with
        ⟨hshort, hrev⟩ | ⟨hl, aw2, k2, C2, h2⟩
      · exact .inl ⟨ExecFuncBody.execBlockRevert (hpre.run (ExecBlock.consRevert
          (skimBalanceReverts imms token true out hcallSource (.inr hshort)))), hrev⟩
      · have hh : out.size < 2 ^ 255 := lt_trans (tokenBalanceReturnSize hcall) (by decide)
        have hbalance := skimBalanceSource imms token out hcallSource hl hh
        have hread := tokenBalanceReadMemory_load solcFreePtrMem ⟨128⟩ I.codeOwner out
          (by decide) (by decide) hl hout
        simp only [tokenBalanceReadMemory] at hread
        obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_2904_packed
          (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
          (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
        simp only [metaMorphoV1_1_block_2904_stack, hread] at h3
        obtain ⟨aw4, k4, C4, h4⟩ := metaMorphoV1_1_block_2809_packed
          (immWords := wordsOf (immStore v)) (by omega)
          (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
        simp only [metaMorphoV1_1_block_2809_stack] at h4
        have hsize : 128 ≤ (tokenBalanceReadMemory solcFreePtrMem ⟨128⟩ I.codeOwner out).size := by
          rw [tokenBalanceReadMemory_size _ _ _ _ hl hout, solcFreePtrMem_size]
          decide
        have hfree : memLoad ⟨64⟩
            (tokenBalanceReadMemory solcFreePtrMem ⟨128⟩ I.codeOwner out) = ⟨160⟩ := by
          rw [tokenBalanceReadMemory_free]
          decide
        rcases safeTransferSimulation v imms token (skimRecipientAddress evm) (calldataWord out 0)
          (by simp only [List.length_cons]; omega) hs1 (by decide) (by decide) hsize hfree
          (skimBalanceMemory_zero I.codeOwner out hl hout)
          (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h4 with
          ⟨htransfer, hrev⟩ |
          ⟨evm', cursor, mem', returned, aw5, k5, C5, hs2, htransfer, h5⟩
        · refine .inl ⟨ExecFuncBody.execBlockRevert (hpre.run
            (ExecBlock.consNormal hbalance (ExecBlock.consRevert ?_))), hrev⟩
          exact internalCallFunctionRevert (callee := allocatedSafeTransferFunction)
            (skimTransferArgs evm evmBalance imms token (calldataWord out 0)) rfl rfl htransfer
        · by_cases hperm : I.perm = true
          · refine .inr (.inl ⟨evm', skimFinalFrame evm evm' imms token (calldataWord out 0) cursor,
              ExecFuncBody.execBlockOK (hpre.run
              (ExecBlock.consNormal hbalance ?_)), ?_⟩)
            · apply skimAfterTransfer imms token (calldataWord out 0) cursor htransfer
              exact ExecBlock.consNormal
                (ExecStmt.emit (skimEmitArgs evm evm' imms token (calldataWord out 0) cursor))
                ExecBlock.nil
            · exact metaMorphoV1_1_block_2821 (immWords := wordsOf (immStore v))
                (by omega) hperm h5
          · have hp : I.perm = false := Bool.eq_false_of_not_eq_true hperm
            refine .inr (.inr ⟨ExecFuncBody.execBlockStatic (hpre.run
              (ExecBlock.consNormal hbalance ?_)), skimEventStatic v (by omega) hp h5⟩)
            apply skimAfterTransfer imms token (calldataWord out 0) cursor htransfer
            exact ExecBlock.consStatic (ExecStmt.emitStatic
              (skimEmitArgs evm evm' imms token (calldataWord out 0) cursor)
              (by rw [hs2.env]; exact hp))

end Benchmarks.Morpho.MetaMorphoV1_1
