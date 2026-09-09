import Benchmarks.Auction.CreateBidRefundSuccess
import Benchmarks.Auction.DynamicMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

namespace Auction

set_option maxHeartbeats 1000000 in
theorem auctionCreateBidStoreBidderDynamic
    {cA cA' gh bl σ σCall σ₀ A I} {g : Sat256} {marker : UInt256}
    {aw : UInt256} {mem rdata : ByteArray}
    (hperm : I.perm = true)
    (rd1715 : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1715⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      mem
      aw rdata (cA', σCall) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1738⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      mem
      aw rdata
      (cA', auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) k C := by
  let σAmount := auctionCreateBidAmountMap σCall I
  let packedAfterAmount := auctionSlotWord ⟨211⟩ σAmount I
  obtain ⟨_, _, rd1715'⟩ := rd1715
  have rd1719 := evm_run rd1715' with [jumpdest, callvalue, push1 ⟨208⟩]
  obtain ⟨_, _, rd1720₀⟩ := rd1719.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1720⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1720⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      mem
      aw rdata (cA', σAmount) k C := by
    exact ⟨_, _, by simpa [σAmount, auctionCreateBidAmountMap] using rd1720₀⟩
  have rd1723₀ := evm_run rd1720 with [push1 ⟨211⟩, dup1]
  obtain ⟨_, _, rd1723₁⟩ := rd1723₀.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1724⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1724⟩
      [packedAfterAmount, ⟨211⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩,
        auctionSelWord I]
      mem
      aw rdata (cA', σAmount) k C := by
    exact ⟨_, _, by simpa [packedAfterAmount, auctionSlotWord] using rd1723₁⟩
  have hsourceClean : UInt256.land (auctionSourceWord I) solcAddrMask = auctionSourceWord I :=
    solcAddrMask_clean (auctionSourceWord_canonical I)
  have hpostWord :
      UInt256.lor (UInt256.ofNat I.source.val)
          (UInt256.land
            (UInt256.lnot
              (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩))
            packedAfterAmount) =
        setAddressOffset0Word packedAfterAmount (auctionSourceWord I) := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask by native_decide]
    rw [u256_land_comm (UInt256.lnot solcAddrMask) packedAfterAmount]
    change UInt256.lor (auctionSourceWord I)
        (UInt256.land packedAfterAmount (UInt256.lnot solcAddrMask)) =
      setAddressOffset0Word packedAfterAmount (auctionSourceWord I)
    unfold setAddressOffset0Word
    rw [hsourceClean, u256_lor_comm]
  have rd1737₀ := evm_run rd1724 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, and, caller, lor, swap1]
  have rd1737 := rd1737₀
  rw [hpostWord] at rd1737
  obtain ⟨_, _, rd1738₀⟩ := rd1737.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [auctionCreateBidBidderMap, packedAfterAmount, σAmount] using rd1738₀⟩

set_option maxHeartbeats 1000000 in
theorem auctionCreateBidLogDynamic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {flag marker arg sel aw : UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hperm : I.perm = true)
    (h : RD auctionBytecode I g s0 ⟨1792⟩ [flag, marker, ⟨128⟩, arg, ⟨413⟩, sel]
      mem aw rdata acc k C) :
    ∃ mem aw k C, RD auctionBytecode I g s0 ⟨1859⟩
      [flag, marker, ⟨128⟩, arg, ⟨413⟩, sel] mem aw rdata acc k C := by
  have h1794 := evm_run h with [jumpdest, dup3]
  obtain ⟨_, _, h1795⟩ := auctionMloadDynamic h1794 (by native_decide) (by evm_ov)
  have h1798 := evm_run h1795 with [push1 ⟨64⟩, dup1]
  obtain ⟨_, _, h1799⟩ := auctionMloadDynamic h1798 (by native_decide) (by evm_ov)
  have h1801 := evm_run h1799 with [caller, dup2]
  obtain ⟨_, _, h1802⟩ := auctionMstoreDynamic h1801 (by native_decide) (by evm_ov)
  have h1807 := evm_run h1802 with [callvalue, push1 ⟨32⟩, dup3, add]
  obtain ⟨_, _, h1808⟩ := auctionMstoreDynamic h1807 (by native_decide) (by evm_ov)
  have h1814 := evm_run h1808 with [dup4, iszero, iszero, dup2, dup4, add]
  obtain ⟨_, _, h1815⟩ := auctionMstoreDynamic h1814 (by native_decide) (by evm_ov)
  have h1816 := evm_run h1815 with [swap1]
  obtain ⟨_, _, h1817⟩ := auctionMloadDynamic h1816 (by native_decide) (by evm_ov)
  have h1850 := h1817.pushConst auctionCreateBidAuctionBidTopic
    (width := 32) (op := .PUSH32) (by native_decide) (by native_decide) (by evm_ov)
  have h1858 := evm_run h1850 with [swap2, dup2, swap1, sub, push1 ⟨96⟩, add, swap1]
  obtain ⟨_, _, h1859⟩ := auctionLog2Dynamic h1858 (by native_decide) hperm (by evm_ov)
  exact ⟨_, _, _, _, h1859⟩

set_option maxHeartbeats 1000000 in
theorem auctionCreateBidExtendedLogDynamic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {flag marker arg sel aw : UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hperm : I.perm = true)
    (h : RD auctionBytecode I g s0 ⟨1865⟩ [flag, marker, ⟨128⟩, arg, ⟨413⟩, sel]
      mem aw rdata acc k C) :
    ∃ mem aw k C, RD auctionBytecode I g s0 ⟨1923⟩
      [flag, marker, ⟨128⟩, arg, ⟨413⟩, sel] mem aw rdata acc k C := by
  have h1866 := evm_run h with [dup3]
  obtain ⟨_, _, h1867⟩ := auctionMloadDynamic h1866 (by native_decide) (by evm_ov)
  have h1871 := evm_run h1867 with [push1 ⟨96⟩, dup5, add]
  obtain ⟨_, _, h1872⟩ := auctionMloadDynamic h1871 (by native_decide) (by evm_ov)
  have h1874 := evm_run h1872 with [push1 ⟨64⟩]
  obtain ⟨_, _, h1875⟩ := auctionMloadDynamic h1874 (by native_decide) (by evm_ov)
  have h1877 := evm_run h1875 with [swap1, dup2]
  obtain ⟨_, _, h1878⟩ := auctionMstoreDynamic h1877 (by native_decide) (by evm_ov)
  have h1911 := h1878.pushConst auctionCreateBidAuctionExtendedTopic
    (width := 32) (op := .PUSH32) (by native_decide) (by native_decide) (by evm_ov)
  have h1917 := evm_run h1911 with [swap1, push1 ⟨32⟩, add, push1 ⟨64⟩]
  obtain ⟨_, _, h1918⟩ := auctionMloadDynamic h1917 (by native_decide) (by evm_ov)
  have h1922 := evm_run h1918 with [dup1, swap2, sub, swap1]
  obtain ⟨_, _, h1923⟩ := auctionLog2Dynamic h1922 (by native_decide) hperm (by evm_ov)
  exact ⟨_, _, _, _, h1923⟩

set_option maxHeartbeats 1000000 in
theorem auctionCreateBidFinishDynamic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {flag marker arg sel aw : UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : Nat}
    (hperm : I.perm = true)
    (h : RD auctionBytecode I g s0 ⟨1792⟩ [flag, marker, ⟨128⟩, arg, ⟨413⟩, sel]
      mem aw rdata (cA, σ) k C) :
    RDret auctionBytecode g s0 (cA, auctionCreateBidUnlockedMap σ I) ByteArray.empty := by
  obtain ⟨mem', aw', _, _, h1859⟩ := auctionCreateBidLogDynamic hperm h
  have h1864 := evm_run h1859 with [dup1, iszero, push2 ⟨1923⟩]
  obtain ⟨mem'', aw'', _, _, h1923⟩ : ∃ mem aw k C,
      RD auctionBytecode I g s0 ⟨1923⟩ [flag, marker, ⟨128⟩, arg, ⟨413⟩, sel]
        mem aw rdata (cA, σ) k C := by
    by_cases hflag : flag = ⟨0⟩
    · have h1923 := evm_run h1864 with [
        jumpiT (by rw [hflag]; native_decide) (by jump_dest)]
      exact ⟨_, _, _, _, h1923⟩
    · have h1865 := evm_run h1864 with [jumpiNT (isZero_eq_zero_of_ne hflag)]
      exact auctionCreateBidExtendedLogDynamic hperm h1865
  have h1930 := evm_run h1923 with [jumpdest, pop, pop, push1 ⟨1⟩, push1 ⟨101⟩]
  obtain ⟨_, _, h1931⟩ := h1930.sstore hperm (by native_decide) (by evm_ov)
  have h414 := evm_run h1931 with [pop, pop, jump (by jump_dest), jumpdest]
  exact h414.stop (by native_decide) (by evm_ov)

set_option maxHeartbeats 1000000 in
theorem auctionCreateBidDecisionDynamic
    {cA cA' gh bl σ σCall σ₀ A I} {g : Sat256} {marker : UInt256}
    {finish aw : UInt256} {mem rdata : ByteArray}
    (hfinish : auctionLoadWord mem aw ⟨224⟩ = finish)
    (hperm : I.perm = true)
    (htime : (UInt256.ofNat I.header.timestamp).toNat < finish.toNat)
    (rd1715 : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1715⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      mem
      aw rdata (cA', σCall) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1759⟩
      [UInt256.sub finish (UInt256.ofNat I.header.timestamp),
        auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I,
        ⟨0⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      mem
      (auctionGrowWords aw ⟨224⟩ 32) rdata
      (cA', auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) k C := by
  let σAmount := auctionCreateBidAmountMap σCall I
  let σBidder := auctionCreateBidBidderMap σAmount I
  let timeBuffer := auctionSlotWord ⟨203⟩ σBidder I
  obtain ⟨_, _, rd1738⟩ := auctionCreateBidStoreBidderDynamic
    (cA := cA) (cA' := cA') (gh := gh) (bl := bl) (σ := σ) (σCall := σCall)
    (σ₀ := σ₀) (A := A) (g := g) (marker := marker)
    hperm rd1715
  obtain ⟨_, _, rd1738'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1738⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      mem
      aw rdata (cA', σBidder) k C := by
    exact ⟨_, _, by simpa [σAmount, σBidder] using rd1738⟩
  obtain ⟨_, _, rd1740₀⟩ := (evm_run rd1738' with [push1 ⟨203⟩]).sload
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1741⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1741⟩
      [timeBuffer, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      mem
      aw rdata (cA', σBidder) k C := by
    exact ⟨_, _, by simpa [timeBuffer, auctionSlotWord] using rd1740₀⟩
  have rd1745₀ := evm_run rd1741 with [push1 ⟨96⟩, dup4, add]
  have rd1745 := rd1745₀
  rw [show (⟨128⟩ : UInt256) + ⟨96⟩ = ⟨224⟩ by decide] at rd1745
  obtain ⟨_, _, rd1746⟩ := auctionMloadDynamic rd1745 (by native_decide) (by evm_ov)
  rw [hfinish] at rd1746
  have rd5723 := evm_run rd1746 with [
    push0, swap2, swap1, push2 ⟨1759⟩, swap1, timestamp, swap1, push2 ⟨5723⟩,
    jump (by jump_dest)]
  obtain ⟨_, _, rd1759⟩ := auctionCreateBidCheckedSubOk
    (a := finish) (b := UInt256.ofNat I.header.timestamp) (ret := ⟨1759⟩)
    (R := [timeBuffer, ⟨0⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩,
      auctionSelWord I])
    rd5723 (Nat.le_of_lt htime) (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [σAmount, σBidder, timeBuffer] using rd1759⟩

set_option maxHeartbeats 1000000 in
theorem auctionCreateBidNoExtensionDynamic
    {cA cA' gh bl σ σCall σ₀ A I} {g : Sat256} {marker finish aw : UInt256}
    {mem rdata : ByteArray}
    (hfinish : auctionLoadWord mem aw ⟨224⟩ = finish)
    (hperm : I.perm = true)
    (htime : (UInt256.ofNat I.header.timestamp).toNat < finish.toNat)
    (hnotExtended :
      (auctionSlotWord ⟨203⟩
        (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I).toNat ≤
        (UInt256.sub finish (UInt256.ofNat I.header.timestamp)).toNat)
    (rd1715 : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1715⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      mem aw rdata (cA', σCall) k C) :
    RDret auctionBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA', auctionCreateBidUnlockedMap
        (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I) ByteArray.empty := by
  obtain ⟨_, _, h1759⟩ := auctionCreateBidDecisionDynamic hfinish hperm htime rd1715
  have h1764 := evm_run h1759 with [jumpdest, lt, swap1, pop, dup1, iszero]
  rw [ult_zero hnotExtended] at h1764
  have h1792 := evm_run h1764 with [
    push2 ⟨1792⟩, jumpiT (by native_decide) (by jump_dest)]
  exact auctionCreateBidFinishDynamic hperm h1792

set_option maxHeartbeats 1000000 in
theorem auctionCreateBidExtensionToAddDynamic
    {cA cA' gh bl σ σCall σ₀ A I} {g : Sat256} {marker finish aw : UInt256}
    {mem rdata : ByteArray}
    (hfinish : auctionLoadWord mem aw ⟨224⟩ = finish)
    (hperm : I.perm = true)
    (htime : (UInt256.ofNat I.header.timestamp).toNat < finish.toNat)
    (hextended :
      (UInt256.sub finish (UInt256.ofNat I.header.timestamp)).toNat <
        (auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I).toNat)
    (rd1715 : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1715⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      mem aw rdata (cA', σCall) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5704⟩
      [UInt256.ofNat I.header.timestamp,
        auctionSlotWord ⟨203⟩ (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I,
        ⟨1781⟩, ⟨1⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      mem (auctionGrowWords aw ⟨224⟩ 32) rdata
      (cA', auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) k C := by
  obtain ⟨_, _, h1759⟩ := auctionCreateBidDecisionDynamic hfinish hperm htime rd1715
  have h1764 := evm_run h1759 with [jumpdest, lt, swap1, pop, dup1, iszero]
  rw [ult_one hextended] at h1764
  have h1771 := evm_run h1764 with [push2 ⟨1792⟩, jumpiNT (by native_decide), push1 ⟨203⟩]
  obtain ⟨_, _, h1772⟩ := h1771.sload (by native_decide) (by evm_ov)
  have h5704 := evm_run h1772 with [
    push2 ⟨1781⟩, swap1, timestamp, push2 ⟨5704⟩, jump (by jump_dest)]
  exact ⟨_, _, h5704⟩

set_option maxHeartbeats 1000000 in
theorem auctionCreateBidExtensionDynamic
    {cA cA' gh bl σ σCall σ₀ A I} {g : Sat256} {marker finish aw : UInt256}
    {mem rdata : ByteArray}
    (hfinish : auctionLoadWord mem aw ⟨224⟩ = finish)
    (hperm : I.perm = true)
    (htime : (UInt256.ofNat I.header.timestamp).toNat < finish.toNat)
    (hextended :
      (UInt256.sub finish (UInt256.ofNat I.header.timestamp)).toNat <
        (auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I).toNat)
    (hadd : (UInt256.ofNat I.header.timestamp).toNat +
      (auctionSlotWord ⟨203⟩
        (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I).toNat < UInt256.size)
    (rd1715 : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1715⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      mem aw rdata (cA', σCall) k C) :
    RDret auctionBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA', auctionCreateBidUnlockedMap
        (auctionCreateBidExtendedMap
          (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I) I)
      ByteArray.empty := by
  obtain ⟨_, _, h5704⟩ :=
    auctionCreateBidExtensionToAddDynamic hfinish hperm htime hextended rd1715
  obtain ⟨_, _, h1781⟩ := auctionCreateAuctionCheckedAddOk h5704 hadd (by jump_dest) (by evm_ov)
  have h1787 := evm_run h1781 with [jumpdest, push1 ⟨96⟩, dup5, add, dup2, swap1]
  obtain ⟨_, _, h1788⟩ := auctionMstoreDynamic h1787 (by native_decide) (by evm_ov)
  have h1791 := evm_run h1788 with [push1 ⟨210⟩]
  obtain ⟨_, _, h1792⟩ := h1791.sstore hperm (by native_decide) (by evm_ov)
  have hret := auctionCreateBidFinishDynamic hperm h1792
  rw [u256_add_comm] at hret
  exact hret


theorem auctionCreateBidOverflowDynamic
    {cA cA' gh bl σ σCall σ₀ A I} {g : Sat256} {marker finish aw : UInt256}
    {mem rdata : ByteArray}
    (hfinish : auctionLoadWord mem aw ⟨224⟩ = finish)
    (hperm : I.perm = true)
    (htime : (UInt256.ofNat I.header.timestamp).toNat < finish.toNat)
    (hextended :
      (UInt256.sub finish (UInt256.ofNat I.header.timestamp)).toNat <
        (auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I).toNat)
    (hover : UInt256.size ≤ (UInt256.ofNat I.header.timestamp).toNat +
      (auctionSlotWord ⟨203⟩
        (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I).toNat)
    (rd1715 : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1715⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      mem aw rdata (cA', σCall) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, h5704⟩ :=
    auctionCreateBidExtensionToAddDynamic hfinish hperm htime hextended rd1715
  exact auctionCheckedAddOverflowDynamic h5704 hover (by evm_ov)

end Auction
