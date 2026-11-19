import Benchmarks.Midnight.MulticallPrepare
import Benchmarks.Midnight.MulticallReturn
import Benchmarks.Midnight.DelegateCallBridgeGas
import Benchmarks.Midnight.TransferHeap

/-! One delegate call, retaining the heap invariant for the next multicall iteration. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightMulticallCall {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {mem rdata : ByteArray} {aw root dp dl : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 10 ≤ 1024)
    (hmem : 832 ≤ mem.size) (hlower : 832 ≤ root.toNat)
    (hz : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hdl : dl.toNat < 2^64)
    (hd : dl.toNat = 0 ∨ dp.toNat + dl.toNat ≤ I.calldata.size)
    (hh : TransferHeap mem aw root C) (hgas : midnightGasBound g) (hfork : I.fork ≥ .osaka)
    (hs : SourceState s0 I σ evm)
    (rd : RD midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨3662⟩
      (dl :: dp :: R) mem aw rdata σ k C) :
    let data := I.calldata.readWithPadding dp.toNat dl.toNat
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (∃ evm' success out, delegateCallViaEVM evm I.codeOwner data (success, evm', out) ∧
      (success = false ∨ 2^64 ≤ out.size) ∧ RDrev midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ (evm' : State) (σ' : AccountMap) (out mem' : ByteArray) (root' retptr aw' : UInt256)
      (k' C' : Nat),
      delegateCallViaEVM evm I.codeOwner data (true, evm', out) ∧ out.size < 2^64 ∧
      SourceState s0 I σ' evm' ∧ MemoryPrefix mem mem' root.toNat ∧
      root.toNat ≤ root'.toNat ∧ TransferHeap mem' aw' root' C' ∧
      RD midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨3707⟩
        (retptr :: R) mem' aw' out σ' k' C' := by
  dsimp only
  rcases midnightMemoryPaid_headroom rd hh.funding.accounting.paid hgas hh.covered with
    hoog | hroom
  · exact Or.inl hoog
  let mem1 := copyZeroMemory I.calldata mem dp.toNat root.toNat dl.toNat
  have hm1 : mem1.size = max mem.size (root.toNat + dl.toNat + 32) :=
    copyZeroMemory_size_or_empty _ _ _ _ _ hd
  have hp1 : MemoryPrefix mem mem1 root.toNat :=
    copyZeroMemory_prefix_or_empty _ _ _ _ _ _ hd le_rfl
  have hf1 : memLoad (UInt256.ofNat 64) mem1 = root := by
    rw [copyZeroMemory_load_before_or_empty I.calldata mem dp.toNat root.toNat dl.toNat
      (UInt256.ofNat 64) hd (by change 64 + 32 ≤ mem.size; omega)
        (by change 64 + 32 ≤ root.toNat; omega), hh.free]
  obtain ⟨gasArg, aw1, k1, C1, ha1, rd1⟩ := midnightMulticallPrepare (by omega)
    hmem hlower (by omega) hdl hd hh.free hz hh.funding rd
  rcases memoryAccounting_headroom rd1 ha1.accounting hgas with hoog | hroom1
  · exact Or.inl hoog
  change mem1.size + 2^62 < 2^64 at hroom1
  have hparent : (root.toNat + 31) / 32 ≤ aw1.toNat := by
    have hc := ha1.covered
    change mem1.size ≤ 32 * aw1.toNat at hc
    rw [hm1] at hc
    omega
  have hbudget : memoryCost ((root.toNat + 31) / 32) +
      4 * ((root.toNat + 31) / 32) ≤ C1 + 1000000 := by
    have hw := memoryCost_mono hparent
    have he : memoryCost aw1.toNat = Cₘ aw1 := by
      rw [memoryCost_eq_Cₘ (words := aw1.toNat) aw1.val.isLt, u256_ofNat_toNat]
    rw [he] at hw
    have hp := ha1.paid
    unfold transferHeapCredit at hp
    omega
  have hcd : mem1.readWithPadding root.toNat dl.toNat =
      I.calldata.readWithPadding dp.toNat dl.toNat :=
    copyZeroMemory_read_or_empty _ _ _ _ _ hd hdl
  have hsmall := Ethereum.EVM.ByteArray.readWithPadding_size_le I.calldata dp.toNat dl.toNat
  rcases delegateCallCostBridge rd1 hs (by native_decide) hcd
      (hsmall.trans ((Nat.le_of_lt hdl).trans (by decide : 2^64 ≤ maxReturnDataSizeByGas)))
      hfork (by omega) with
    hoog | ⟨evm', σ', success, out, aw2, k2, C2, hcall, hs', rd2, hout, hcost, hcharge⟩
  · exact Or.inl hoog
  have hcall' : delegateCallViaEVM evm I.codeOwner
      (I.calldata.readWithPadding dp.toNat dl.toNat) (success, evm', out) := by
    simpa only [accountAddress_roundtrip] using hcall
  have hfit : root.toNat + returnDataAllocation out.size < 2^64 := by
    rcases hcost with hsmallOut | hcost
    · unfold returnDataAllocation
      rw [hm1] at hroom1
      omega
    · change C1 + 100 + forwardingMinimum (memoryCost ((out.size + 31) / 32)) ≤ g.toNat at hcost
      exact aggregateReturnDataFits (parent := (root.toNat + 31) / 32)
        (by omega) hbudget (midnightGasBound_lt_capacityCutoff hgas) (by omega)
  rcases midnightMulticallReturn success hstack (by change _ < 2^256; omega)
      (by rw [hm1]; omega) hlower hf1 (fun _ _ ↦ hfit) rd2 with
    ⟨hbad, hrev⟩ | ⟨htrue, hb, hp2, hf2, aw3, k3, C3, hpost, hcover3, rd3⟩
  · exact Or.inr (Or.inl ⟨evm', success, out, hcall', hbad, hrev⟩)
  · subst success
    rcases hcharge with hfalse | ⟨hC12, haw12, hpaid12, hpaidOut⟩
    · cases hfalse
    have hcovered3 := hcover3 (ha1.covered.mono haw12)
    have hfund3 : MemoryFunding (transferHeapCredit root + multicallOutputWork dl.toNat out)
        (safeTransferOutputMem mem1 out root) aw3 C3 := by
      refine ⟨?_, hcovered3⟩
      have hp1 := ha1.paid
      have hp3 := hpost.paid
      unfold multicallOutputWork
      by_cases hsmallOut : out.size ≤ max 1024 dl.toNat
      · rw [if_pos hsmallOut]
        omega
      · rw [if_neg hsmallOut]
        rcases hpaidOut with hsmallOut' | hpaidOut
        · have : out.size ≤ max 1024 dl.toNat := by omega
          contradiction
        · omega
    have hfit' : root.toNat + returnDataAllocation out.size < UInt256.size := by
      change _ < 2^256
      omega
    have hnewnat := safeTransferOutputPtr_toNat hfit'
    have hnewalign := safeTransferOutputPtr_aligned hfit' hh.aligned
    have hnewlower : root.toNat ≤ (safeTransferOutputPtr root out).toNat := by
      rw [hnewnat]
      omega
    have hprefix := hp1.trans hp2
    have hnewcover : root.toNat ≤ 32 * aw3.toNat := by
      have hw := hpost.active_le
      omega
    have hh3 : TransferHeap (safeTransferOutputMem mem1 out root) aw3
        (safeTransferOutputPtr root out) C3 := by
      refine ⟨hh.size.trans hprefix.size, hh.lower.trans hnewlower, hf2, ?_, ?_, hnewalign, ?_⟩
      · rw [hprefix.load (UInt256.ofNat 96) (by decide) hh.lower hh.size, hh.zero]
      · exact safeTransferOutputPtr_covered (by rw [hm1]; omega) (by omega)
          hfit' hh.aligned hnewcover hcovered3
      · apply hfund3.weaken
        apply transferHeapCredit_grows hnewlower hh.aligned hnewalign
        rw [hnewnat]
        simpa only [Nat.add_sub_cancel_left] using multicallOutputWork_growth dl.toNat out
    exact Or.inr (Or.inr ⟨evm', σ', out, _, _, _, aw3, k3, C3,
      hcall', hb, hs', hprefix, hnewlower, hh3, rd3⟩)

end Benchmarks.Midnight
