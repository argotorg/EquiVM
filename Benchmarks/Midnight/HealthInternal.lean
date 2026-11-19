import Benchmarks.Midnight.HealthLoop
import Benchmarks.Midnight.HealthPrepare
import Benchmarks.Midnight.HealthSource

/-! Refinement of the internal health predicate, including the zero-debt fast path. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightHealthInternal (imms : Store)
    {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw market arrayPtr heap root id user ret : UInt256} {m : MarketData}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 24 ≤ 1024) (hfork : I.fork ≥ .osaka)
    (hcanon : user.toNat < EVM.addressModulus) (hroot : root.toNat + 4096 < 2^64)
    (hheap : heap.toNat ≤ root.toNat) (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hm : MarketStored mem market arrayPtr heap m) (hs : SourceState s0 I σ evm)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨19775⟩ (market :: id :: user :: ret :: R)
      mem aw rdata σ k C) :
    (ExecFuncBody config (healthCallFrame imms m id user) evm healthFunction.body .reverted ∧
      RDrev midnightBytecode g s0) ∨
    ∃ (evm' : State) (σ' : AccountMap) (frame' : Frame) (mem' out : ByteArray)
      (root' aw' : UInt256) (k' C' : Nat) (value : Bool),
      ExecFuncBody config (healthCallFrame imms m id user) evm healthFunction.body
        (.returned frame' evm' (some [.bool value])) ∧
      SourceState s0 I σ' evm' ∧ MarketStored mem' market arrayPtr heap m ∧
      memLoad (UInt256.ofNat 64) mem' = root' ∧ heap.toNat ≤ root'.toNat ∧ root'.toNat < 2^64 ∧
      RD midnightBytecode I g s0 ret ((if value then ⟨1⟩ else ⟨0⟩) :: R)
        mem' aw' out σ' k' C' := by
  let w := solcSlotWordAt (positionSlot id user + ⟨2⟩) σ I
  have hword : healthPositionWord evm id user = w := hs.storageRead _
  have hmem : 96 ≤ mem.size := by
    have := hm.words.size
    have := hm.lower
    omega
  have hprefix := healthSourcePrefix evm imms m id user hcanon
  rw [hword] at hprefix
  have hp := positionReadMemory_prefix mem id user heap.toNat
  have hm1 := hm.preserve hp
  have hfree1 : memLoad (UInt256.ofNat 64) (positionReadMemory mem id user) = root := by
    rw [positionReadMemory, memLoad_twoWordHashMem _ _ (UInt256.ofNat 64) (by decide) (by
      rw [twoWordHashMem_size_of_ge_64 _ _ (by omega)]; exact hmem),
      memLoad_twoWordHashMem _ _ (UInt256.ofNat 64) (by decide) hmem, hfree]
  rcases midnightHealthPrepare (by omega) (by omega) hcanon rd with
    ⟨hzero, aw1, k1, C1, rd1⟩ | ⟨hnz, aw1, k1, C1, rd1⟩
  · have hzero' : low128 w = ⟨0⟩ := hzero
    have rd2 := midnightBlocks.midnight_block_19831 (R := R) (by omega) hret rd1
    simp only [midnightBlocks.midnight_block_19831_stack] at rd2
    refine Or.inr ⟨evm, σ, healthDebtFrame imms m id user w, _, rdata, root, aw1,
      _, _, true, ?_, hs, hm1, hfree1, hheap, by omega, rd2⟩
    apply ExecFuncBody.execBlockRet
    apply hprefix.run
    refine ExecBlock.consNormal (ExecStmt.iteFalse ?_ ExecBlock.nil) ?_
    · exact (evalHealthDebtGuard (healthDebtFrame_debt imms m id user w)).trans
        (by rw [hzero']; rfl)
    · simpa only [hzero'] using healthSourceReturn (cfg := config) (evm := evm)
        (healthDebtFrame_debt imms m id user w) (wordLocal_get ..)
  · have hnz' : low128 w ≠ ⟨0⟩ := hnz
    have hdebt : 0 < (low128 w).toNat := by
      by_contra h
      exact hnz' (u256_inj (by change (low128 w).toNat = 0; omega))
    have hguard := (evalHealthDebtGuard (cfg := config) (evm := evm)
      (healthDebtFrame_debt imms m id user w)).trans (by rw [decide_eq_true hdebt])
    have hbitmap := evalHealthBitmap (evm := evm) hcanon (healthDebtFrame_alias imms m id user w)
    rw [hword] at hbitmap
    rcases midnightHealthLoop (R := low128 w :: ret :: R)
        (by simp only [List.length_cons]; omega) hfork hcanon
        128 evm (healthLoopFrame imms m id user w) (positionReadMemory mem id user) rdata
        aw1 root (UInt256.shiftRight w (UInt256.ofNat 128)) ⟨0⟩ σ k1 C1
        (by decide) (shiftRight128_lt _) hroot hheap hfree1 hm1
        (healthLoopFrame_inv imms m id user w) hs rd1 with
      ⟨hloop, hrev⟩ | ⟨evm2, σ2, frame2, mem2, out2, root2, max2, aw2, k2, C2,
        hloop, hs2, hf2, hm2, hfree2, hheap2, hroot2, rd2⟩
    · refine Or.inl ⟨ExecFuncBody.execBlockRevert (hprefix.run ?_), hrev⟩
      exact ExecBlock.consRevert (ExecStmt.iteTrue hguard
        (ExecBlock.consNormal (ExecStmt.letDecl hbitmap) (ExecBlock.consRevert hloop)))
    · have rd3 := midnightBlocks.midnight_block_19831 (by omega) hret rd2
      simp only [midnightBlocks.midnight_block_19831_stack, healthBoolWord] at rd3
      refine Or.inr ⟨evm2, σ2, frame2, mem2, out2, root2, aw2, _, _, _,
        ?_, hs2, hm2, hfree2, hheap2, hroot2, rd3⟩
      apply ExecFuncBody.execBlockRet
      apply hprefix.run
      refine ExecBlock.consNormal (ExecStmt.iteTrue hguard
        (ExecBlock.consNormal (ExecStmt.letDecl hbitmap) (ExecBlock.consNormal hloop ExecBlock.nil))) ?_
      exact healthSourceReturn hf2.debt hf2.maxDebt

end Benchmarks.Midnight
