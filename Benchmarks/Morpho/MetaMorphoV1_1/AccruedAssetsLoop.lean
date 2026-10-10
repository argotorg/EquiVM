import Benchmarks.Morpho.MetaMorphoV1_1.AccruedAssetsIteration

/-! Induction over the withdrawal queue while accumulating expected supply assets. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem accruedAssetsLoopSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr total len i : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (remaining : Nat) (hstack : R.length + 33 ≤ 1024)
    (hlocals : AccruedAssetsLocals v frame i total ptr)
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat) (hmem : 96 ≤ mem.size)
    (hs : SourceState s0 I σ evm) (hlen : codeOwnerStorageWord I σ ⟨21⟩ = len)
    (hdiff : len.toNat = i.toNat + remaining)
    (rd : RD (deployedRuntime v) I g s0 ⟨12288⟩
      ([UInt256.ofNat v.MORPHO.toNat, len, i, total] ++ R) mem aw rdata σ k C) :
    (ExecForLoop config frame evm accruedAssetsCondition accruedAssetsPost accruedAssetsIteration
      .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (frame' : Frame) (total' ptr' : UInt256) (mem' out : ByteArray),
      SourceState s0 I evm'.accountMap evm' ∧
      accountStorageStateEq evm.accountMap evm'.accountMap ∧
      AccruedAssetsLocals v frame' len total' ptr' ∧ AccruedAssetsPreserves frame frame' ∧
      memLoad ⟨64⟩ mem' = ptr' ∧ 96 ≤ ptr'.toNat ∧ 96 ≤ mem'.size ∧
      ExecForLoop config frame evm accruedAssetsCondition accruedAssetsPost accruedAssetsIteration
        (.ok frame' evm') ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨12296⟩
        ([UInt256.ofNat v.MORPHO.toNat, len, len, total'] ++ R)
        mem' aw' out evm'.accountMap k' C' := by
  induction remaining generalizing evm frame mem aw rdata σ k C ptr total i with
  | zero =>
      have hi : i = len := by apply u256_inj; omega
      subst i
      have hcond := accruedAssetsConditionSource hlocals.contract hlocals.queue hlocals.index
        ((hs.storageRead ⟨21⟩).trans hlen)
      simp only [Nat.lt_irrefl, decide_false] at hcond
      obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_12288_fallthrough_packed
        (immWords := wordsOf (immStore v))
        (by simp only [List.append, List.length_cons]; omega) (ult_zero (le_refl _)) rd
      rw [hs.accounts] at h1
      exact .inr ⟨evm, frame, total, ptr, mem, rdata, ⟨hs.world, hs.env, rfl⟩,
        accountStorageStateEq_refl _, hlocals, .refl _, hfree, hlo, hmem,
        ExecForLoop.falseDone hcond, aw1, k1, C1, h1⟩
  | succ n ih =>
      have hlt : i.toNat < len.toNat := by omega
      have hfit : i.toNat + 1 < UInt256.size := by
        have hl : len.toNat < UInt256.size := len.val.isLt
        omega
      have hcond := accruedAssetsConditionSource hlocals.contract hlocals.queue hlocals.index
        ((hs.storageRead ⟨21⟩).trans hlen)
      simp only [hlt, decide_true] at hcond
      obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_12288_taken_packed
        (immWords := wordsOf (immStore v))
        (by simp only [List.append, List.length_cons]; omega)
        (by rw [ult_one hlt]; decide)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      rcases accruedAssetsIterationSimulation v hstack hlocals hcalldata hfree hlo hmem hs
          (by rw [hlen]; exact hlt) h1 with
        ⟨hbad, hrev⟩ | ⟨evm2, frame2, total2, ptr2, mem2, out2, hs2, hstore2, hlocals2,
          hpreserve2, hfree2, hlo2, hmem2, hbody, aw2, k2, C2, h2⟩
      · exact .inl ⟨ExecForLoop.bodyRevert hcond hbad, hrev⟩
      have hlen2 : codeOwnerStorageWord I evm2.accountMap ⟨21⟩ = len := by
        rw [hs.accounts] at hlen
        exact (accountStorageStateEq_storage_getD hstore2 I.codeOwner ⟨21⟩ ⟨0⟩).symm.trans hlen
      have hpost := accruedAssetsPostSource (evm := evm2) hlocals2.index hfit
      obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_12521_packed
        (immWords := wordsOf (immStore v))
        (by simp only [List.append, List.length_cons]; omega)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
      have hdiff2 : len.toNat = (i + ⟨1⟩).toNat + n := by
        have hadd : (i + ⟨1⟩).toNat = i.toNat + 1 := addWord_toNat i ⟨1⟩ hfit
        rw [hadd]
        omega
      rcases ih hlocals2.post hfree2 hlo2 hmem2 hs2 hlen2 hdiff2 h3 with
        ⟨hbad, hrev⟩ | ⟨evm3, frame3, total3, ptr3, mem3, out3, hs3, hstore3, hlocals3,
          hpreserve3, hfree3, hlo3, hmem3, hloop, hdone⟩
      · exact .inl ⟨ExecForLoop.iterate hcond hbody hpost hbad, hrev⟩
      · exact .inr ⟨evm3, frame3, total3, ptr3, mem3, out3, hs3,
          accountStorageStateEq_trans hstore2 hstore3, hlocals3,
          hpreserve2.trans ((accruedAssetsPostPreserves frame2 i).trans hpreserve3),
          hfree3, hlo3, hmem3, ExecForLoop.iterate hcond hbody hpost hloop, hdone⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
