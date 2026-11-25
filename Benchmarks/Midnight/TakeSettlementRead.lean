import Benchmarks.Midnight.TakeGateDecision
import Benchmarks.Midnight.TakeBuyerDebtWrite
import Benchmarks.Midnight.ClaimSettlementSource

variable {fork : Ethereum.Fork}

/-! Reading the settlement-fee balance after all position and market writes. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def takeSettlementMemory (mem : ByteArray) (offer : OfferData) : ByteArray :=
  twoWordHashMem (UInt256.ofNat offer.market.loanToken.val) (UInt256.ofNat 6) mem

set_option maxHeartbeats 400000 in
theorem midnightTakeSettlementRead {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw value marketPtr arrayPtr callbackPtr root : UInt256}
    {offer : OfferData} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer)
    (hoffer : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨12598⟩ (value :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit (takeSettlementMemory mem offer) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨19536⟩
        (solcSlotWordAt (claimSettlementSlot offer.market.loanToken) σ I :: value ::
          ⟨12638⟩ :: claimSettlementSlot offer.market.loanToken :: R)
        (takeSettlementMemory mem offer) aw' rdata σ k' C' := by
  have hm : memLoad (⟨832⟩ : UInt256) mem = marketPtr :=
    ho.words.load_offset ⟨0, by change 0 < 15; decide⟩ rfl
  have htoken : memLoad (memLoad (memLoad (UInt256.ofNat 384) mem) mem + UInt256.ofNat 64) mem =
      UInt256.ofNat offer.market.loanToken.val := by
    rw [hoffer, hm]
    exact ho.market.words.load_offset ⟨2, by change 2 < 8; decide⟩ rfl
  have hclean : UInt256.land (UInt256.ofNat offer.market.loanToken.val) solcAddrMask =
      UInt256.ofNat offer.market.loanToken.val := addressWord_val_clean offer.market.loanToken
  have hmem : 64 ≤ mem.size := by
    have h := ho.words.size
    change 832 + 32 * 15 ≤ mem.size at h
    omega
  have hhash : keccakWord ⟨0⟩ (UInt256.ofNat 64) (takeSettlementMemory mem offer) =
      claimSettlementSlot offer.market.loanToken := twoWordHashMem_mapSlot_of_ge64 _ _ hmem
  let r0 := rd
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r9 := RD.genMload r8 (by native_decide) (by evm_ov)
  have r10 := RD.genMload r9 (by native_decide) (by evm_ov)
  have r11 := r10.add (by native_decide) (by evm_ov)
  have r12 := RD.genMload r11 (by native_decide) (by evm_ov)
  have r13 := r12.and (by native_decide) (by evm_ov)
  have r14 := r13.push0 (by native_decide) (by evm_ov)
  have r15 := RD.genMstore r14 (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 6) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r18 := RD.genMstore r17 (by native_decide) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 12638) (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r21 := r20.push0 (by native_decide) (by evm_ov)
  have r22 := RD.genKeccak256 r21 (by native_decide) (by evm_ov)
  have ha22 := memoryFundingAt (credit := credit) r22 (by memory_fund ha)
  simp only [htoken, addressMask_computed, hclean,
    show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold] at r22 ha22
  dsimp only [takeSettlementMemory] at hhash
  rw [hhash] at r22
  have r23 := r22.swap2 (by native_decide) (by evm_ov)
  have r24 := r23.dup3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc25, r25⟩ := RD.sloadMono r24 (by native_decide) (by evm_ov)
  have ha25 := ha22.mono
    ((Nat.le_add_right _ 3).trans ((Nat.le_add_right _ 3).trans hc25))
  have r26 := r25.push2 (UInt256.ofNat 19536) (by native_decide) (by evm_ov)
  have r27 := r26.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19536)) r27 (by native_decide)
  exact ⟨_, _, _, ha25.mono
    ((Nat.le_add_right _ 3).trans (Nat.le_add_right _ 8)), rFinal⟩

end Benchmarks.Midnight
