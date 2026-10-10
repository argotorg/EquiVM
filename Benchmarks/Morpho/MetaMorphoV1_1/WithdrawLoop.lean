import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawLoopIteration

/-! Induction over the withdrawal queue, including stopping when all assets are available. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem withdrawLoopSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr i original assets total supply len : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (remaining : Nat) (hstack : R.length + 32 ≤ 1024)
    (hlocals : WithdrawLoopLocals v frame i assets ptr)
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat) (hmem : 96 ≤ mem.size)
    (hs : SourceState s0 I σ evm) (hlen : codeOwnerStorageWord I σ ⟨21⟩ = len)
    (hdiff : len.toNat = i.toNat + remaining)
    (rd : RD (deployedRuntime v) I g s0 ⟨15976⟩
      ([UInt256.ofNat v.MORPHO.toNat, i, original, assets, total, supply, len] ++ R)
      mem aw rdata σ k C) :
    (ExecForLoop config frame evm accruedAssetsCondition accruedAssetsPost withdrawLoopIteration
      .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (frame' : Frame) (i' assets' ptr' : UInt256) (mem' out : ByteArray),
      SourceState s0 I evm'.accountMap evm' ∧
      accountStorageStateEq evm.accountMap evm'.accountMap ∧
      WithdrawLoopLocals v frame' i' assets' ptr' ∧
      memLoad ⟨64⟩ mem' = ptr' ∧ 96 ≤ ptr'.toNat ∧ 96 ≤ mem'.size ∧
      ExecForLoop config frame evm accruedAssetsCondition accruedAssetsPost withdrawLoopIteration
        (.ok frame' evm') ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨12234⟩
        ([original, assets', ⟨12410⟩, total, supply] ++ R)
        mem' aw' out evm'.accountMap k' C' := by
  induction remaining generalizing evm frame mem aw rdata σ k C ptr i assets with
  | zero =>
      have hi : i = len := by apply u256_inj; omega
      subst i
      have hcond := accruedAssetsConditionSource hlocals.contract hlocals.queue hlocals.index
        ((hs.storageRead ⟨21⟩).trans hlen)
      simp only [Nat.lt_irrefl, decide_false] at hcond
      obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_15976_fallthrough_packed
        (immWords := wordsOf (immStore v)) (by simp only [List.append]; omega)
        (ult_zero (le_refl _)) rd
      obtain ⟨aw2, k2, C2, h2⟩ := withdrawLoopExitRoutine v (by omega) h1
      rw [hs.accounts] at h2
      exact .inr ⟨evm, frame, len, assets, ptr, mem, rdata, ⟨hs.world, hs.env, rfl⟩,
        accountStorageStateEq_refl _, hlocals, hfree, hlo, hmem,
        ExecForLoop.falseDone hcond, aw2, k2, C2, h2⟩
  | succ n ih =>
      have hlt : i.toNat < len.toNat := by omega
      have hfit : i.toNat + 1 < UInt256.size := by
        have hb : len.toNat < UInt256.size := len.val.isLt
        omega
      have hcond := accruedAssetsConditionSource hlocals.contract hlocals.queue hlocals.index
        ((hs.storageRead ⟨21⟩).trans hlen)
      simp only [hlt, decide_true] at hcond
      obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_15976_taken_packed
        (immWords := wordsOf (immStore v)) (by simp only [List.append]; omega)
        (by rw [ult_one hlt]; decide)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      rcases withdrawLoopIterationSimulation v hstack hlocals hcalldata hfree hlo (by omega) hs
          (by rw [hlen]; exact hlt) h1 with
        ⟨hbad, hrev⟩ | ⟨evm2, frame2, assets2, ptr2, mem2, out2, hs2, hstore2, hl2,
          hfree2, hlo2, hhi2, hmem2, hbody, aw2, k2, C2, h2⟩
      · exact .inl ⟨ExecForLoop.bodyRevert hcond hbad, hrev⟩
      by_cases hz : assets2 = ⟨0⟩
      · simp only [if_pos hz] at hbody h2
        obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_16091_packed
          (immWords := wordsOf (immStore v))
          (by change R.length + 8 ≤ 1024; omega)
          (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
        obtain ⟨aw4, k4, C4, h4⟩ := withdrawLoopExitRoutine v (by omega) h3
        exact .inr ⟨evm2, frame2, i, assets2, ptr2, mem2, out2, hs2, hstore2, hl2,
          hfree2, hlo2, by omega, ExecForLoop.bodyBreak hcond hbody, aw4, k4, C4, h4⟩
      · simp only [if_neg hz] at hbody h2
        have hlen2 : codeOwnerStorageWord I evm2.accountMap ⟨21⟩ = len := by
          rw [hs.accounts] at hlen
          exact (accountStorageStateEq_storage_getD hstore2 I.codeOwner ⟨21⟩ ⟨0⟩).symm.trans hlen
        have hpost := accruedAssetsPostSource (evm := evm2) hl2.index hfit
        obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_16083_packed
          (immWords := wordsOf (immStore v))
          (by simp only [List.append, List.length_cons]; omega)
          (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
        simp only [metaMorphoV1_1_block_16083_stack, u256_add_comm (UInt256.ofNat 1) i] at h3
        have hdiff2 : len.toNat = (i + ⟨1⟩).toNat + n := by
          have hadd : (i + ⟨1⟩).toNat = i.toNat + 1 := addWord_toNat i ⟨1⟩ hfit
          rw [hadd]
          omega
        rcases ih hl2.post hfree2 hlo2 (by omega) hs2 hlen2 hdiff2 h3 with
          ⟨hbad, hrev⟩ | ⟨evm3, frame3, i3, assets3, ptr3, mem3, out3, hs3, hstore3, hl3,
            hfree3, hlo3, hmem3, hloop, hdone⟩
        · exact .inl ⟨ExecForLoop.iterate hcond hbody hpost hbad, hrev⟩
        · exact .inr ⟨evm3, frame3, i3, assets3, ptr3, mem3, out3, hs3,
            accountStorageStateEq_trans hstore2 hstore3, hl3, hfree3, hlo3, hmem3,
            ExecForLoop.iterate hcond hbody hpost hloop, hdone⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
