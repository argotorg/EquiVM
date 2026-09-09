import Benchmarks.Auction.Common

open Solm Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def auctionLoadWord (mem : ByteArray) (aw off : UInt256) : UInt256 :=
  if off.toNat ≥ mem.size ∨ off ≥ aw * ⟨32⟩ then ⟨0⟩
  else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding off.toNat 32))

def auctionGrowWords (aw off : UInt256) (len : Nat) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat off.toNat len)

def auctionStoreWord (mem : ByteArray) (off val : UInt256) : ByteArray :=
  val.toByteArray.write 0 mem off.toNat 32

-- LIBRARY CANDIDATE: memory steps whose result and gas cost remain symbolic.
theorem auctionMloadDynamic {code : ByteArray} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc off aw : UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat} {R : List UInt256}
    (h : RD code I g s0 pc (off :: R) mem aw rdata acc k C)
    (hdec : decode code pc = some (.MLOAD, .none)) (hR : R.length + 1 ≤ 1024) :
    ∃ k C, RD code I g s0 (pc + ⟨1⟩) (auctionLoadWord mem aw off :: R)
      mem (auctionGrowWords aw off 32) rdata acc k C := by
  exact ⟨_, _, h.mload (Cₘ (auctionGrowWords aw off 32) - Cₘ aw) _ _ hdec
    (fun _ haw hstk ↦ auctionMloadCost_of_stack haw hstk rfl) rfl rfl hR⟩

theorem auctionMstoreDynamic {code : ByteArray} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc off val aw : UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat} {R : List UInt256}
    (h : RD code I g s0 pc (off :: val :: R) mem aw rdata acc k C)
    (hdec : decode code pc = some (.MSTORE, .none)) (hR : R.length ≤ 1024) :
    ∃ k C, RD code I g s0 (pc + ⟨1⟩) R (auctionStoreWord mem off val)
      (auctionGrowWords aw off 32) rdata acc k C := by
  exact ⟨_, _, h.mstore (Cₘ (auctionGrowWords aw off 32) - Cₘ aw) _ _ hdec
    (fun _ haw hstk ↦ mstoreCost_of_stack haw hstk rfl) rfl rfl hR⟩

theorem auctionLog2Dynamic {code : ByteArray} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc off len topic1 topic2 aw : UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat} {R : List UInt256}
    (h : RD code I g s0 pc (off :: len :: topic1 :: topic2 :: R) mem aw rdata acc k C)
    (hdec : decode code pc = some (.LOG2, .none)) (hperm : I.perm = true)
    (hR : R.length ≤ 1024) :
    ∃ k C, RD code I g s0 (pc + ⟨1⟩) R mem (auctionGrowWords aw off len.toNat)
      rdata acc k C := by
  exact ⟨_, _, RD.log2 (Cₘ (auctionGrowWords aw off len.toNat) - Cₘ aw) _ h hdec hperm
    (fun _ haw hstk ↦ auctionLog2Cost_of_stack haw hstk rfl) rfl hR⟩

theorem auctionRevertDynamic {code : ByteArray} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc off len aw : UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat} {R : List UInt256}
    (h : RD code I g s0 pc (off :: len :: R) mem aw rdata acc k C)
    (hdec : decode code pc = some (.REVERT, .none)) (hR : R.length ≤ 1024) :
    RDrev code g s0 := by
  exact h.rev (Cₘ (auctionGrowWords aw off len.toNat) - Cₘ aw) hdec
    (fun _ haw hstk ↦ by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, auctionGrowWords]) hR

theorem auctionReturndataCopyDynamic {code : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc dest src len aw : UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat} {R : List UInt256}
    (h : RD code I g s0 pc (dest :: src :: len :: R) mem aw rdata acc k C)
    (hdec : decode code pc = some (.RETURNDATACOPY, .none))
    (hcopy : src.toNat + len.toNat ≤ rdata.size) (hR : R.length ≤ 1024) :
    ∃ mem aw k C, RD code I g s0 (pc + ⟨1⟩) R mem aw rdata acc k C := by
  exact ⟨_, _, _, _,
    RD.returndatacopy (Cₘ (auctionGrowWords aw dest len.toNat) - Cₘ aw) _ _ h hdec hcopy
      (fun _ haw hstk ↦ by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, auctionGrowWords])
      rfl rfl hR⟩

theorem auctionCallNotMade {code : ByteArray} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc gasArg target value inOff inSize outOff outSize aw : UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (h : RD code I g s0 pc
      (gasArg :: target :: value :: inOff :: inSize :: outOff :: outSize :: R)
      mem aw rdata (cA, σ) k C)
    (hdec : decode code pc = some (.CALL, .none)) (hperm : I.perm = true)
    (hnot : ¬ (value ≤ (σ.find? I.codeOwner |>.elim ⟨0⟩ (·.balance)) ∧ I.depth ≠ 1024))
    (hR : R.length + 1 ≤ 1024) :
    ∃ mem aw k C, RD code I g s0 (pc + ⟨1⟩) (⟨0⟩ :: R)
      mem aw ByteArray.empty (cA, σ) k C := by
  by_cases hdepth : I.depth.val < 1024
  · have hne : I.depth ≠ 1024 := by
      intro heq
      rw [heq] at hdepth
      contradiction
    obtain ⟨_, _, hout⟩ := h.callValueInsufficientBalance hperm hdec
      (fun hb ↦ hnot ⟨hb, hne⟩) hdepth hR
    exact ⟨_, _, _, _, hout⟩
  · have heq : I.depth = 1024 := by
      apply Fin.ext
      have hb := I.depth.isLt
      change I.depth.val = 1024
      omega
    obtain ⟨_, _, hout⟩ := h.callValueDepthLimit hperm hdec heq hR
    exact ⟨_, _, _, _, hout⟩

end Auction
