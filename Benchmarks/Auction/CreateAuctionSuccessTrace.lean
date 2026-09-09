import Benchmarks.Auction.CreateAuctionArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem auctionCreateAuctionToCheckedAdd {s0 : State} {I : ExecutionEnv}
    {σ : AccountMap} {cACur : Batteries.RBSet AccountAddress compare} {g : Sat256}
    {mem out : ByteArray} {aw ret nounId : UInt256} {R : List UInt256} {k C : ℕ}
    (hR : R.length ≤ 980)
    (h : RD auctionBytecode I g s0 ⟨3108⟩ (nounId :: ret :: R) mem aw out (cACur, σ) k C) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨5704⟩
      (UInt256.ofNat I.header.timestamp :: auctionSlotWord ⟨206⟩ σ I :: ⟨3189⟩ ::
        ⟨0⟩ :: UInt256.ofNat I.header.timestamp :: nounId :: ret :: R)
      mem aw out (cACur, σ) k' C' := by
  have rd3172 := evm_run h with [
    jumpdest, push1 ⟨1⟩, jumpdest, push2 ⟨3172⟩,
    jumpiT (by decide) (by jump_dest), jumpdest, push1 ⟨206⟩]
  obtain ⟨_, _, rd3176₀⟩ := rd3172.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3176⟩ : ∃ k C, RD auctionBytecode I g s0 ⟨3176⟩
      (auctionSlotWord ⟨206⟩ σ I :: nounId :: ret :: R) mem aw out (cACur, σ) k C := by
    exact ⟨_, _, by simpa only [auctionSlotWord] using rd3176₀⟩
  exact ⟨_, _, evm_run rd3176 with [
    timestamp, swap1, push0, swap1, push2 ⟨3189⟩, swap1, dup4, push2 ⟨5704⟩,
    jump (by jump_dest)]⟩

theorem auctionCreateAuctionOverflowFromDecoded {s0 : State} {I : ExecutionEnv}
    {σ : AccountMap} {cACur : Batteries.RBSet AccountAddress compare} {g : Sat256}
    {mem out : ByteArray} {aw ret nounId : UInt256} {R : List UInt256} {k C : ℕ}
    (hR : R.length ≤ 980)
    (hover : UInt256.size ≤ (UInt256.ofNat I.header.timestamp).toNat +
      (auctionSlotWord ⟨206⟩ σ I).toNat)
    (h : RD auctionBytecode I g s0 ⟨3108⟩ (nounId :: ret :: R) mem aw out (cACur, σ) k C) :
    RDrev auctionBytecode g s0 := by
  obtain ⟨_, _, rd5704⟩ := auctionCreateAuctionToCheckedAdd hR h
  exact auctionCheckedAddOverflowDynamic rd5704 hover (by evm_ov)

-- The successful mint continuation is independent of the allocator address and caller.
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
theorem auctionCreateAuctionSuccessToRet {s0 : State} {I : ExecutionEnv}
    {σ : AccountMap} {cACur : Batteries.RBSet AccountAddress compare} {g : Sat256}
    {mem o : ByteArray} {aw ret nounId : UInt256} {R : List UInt256} {k C : ℕ}
    (hperm : I.perm = true) (hR : R.length ≤ 980)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (hadd : (UInt256.ofNat I.header.timestamp).toNat + (auctionSlotWord ⟨206⟩ σ I).toNat <
      UInt256.size)
    (h : RD auctionBytecode I g s0 ⟨3108⟩ (nounId :: ret :: R) mem aw o (cACur, σ) k C) :
    ∃ k' C' mem' aw', RD auctionBytecode I g s0 ret R mem' aw' o
      (cACur, auctionCreateAuctionSuccessPostMap σ I nounId
        (UInt256.ofNat I.header.timestamp)
        (UInt256.ofNat I.header.timestamp + auctionSlotWord ⟨206⟩ σ I)) k' C' := by
  let start := UInt256.ofNat I.header.timestamp
  let duration := auctionSlotWord ⟨206⟩ σ I
  let endTime := start + duration
  obtain ⟨_, _, rd5704⟩ := auctionCreateAuctionToCheckedAdd hR h
  obtain ⟨_, _, rd3189₀⟩ := auctionCreateAuctionCheckedAddOk rd5704
    (by simpa [start, duration, Nat.add_comm] using hadd)
    (by jump_dest) (by evm_ov)
  have rd3189 := rd3189₀
  rw [show duration + start = endTime by simp [endTime, u256_add_comm]] at rd3189
  let fmp : UInt256 :=
    if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
    else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 64 32))
  let awLoad := UInt256.ofNat (MachineState.M aw.toNat 64 32)
  let mem3200 : ByteArray := (fmp + ⟨192⟩).toByteArray.write 0
    mem (⟨64⟩ : UInt256).toNat 32
  let aw3200 : UInt256 :=
    UInt256.ofNat (MachineState.M awLoad.toNat (⟨64⟩ : UInt256).toNat 32)
  let mem3203 : ByteArray := nounId.toByteArray.write 0 mem3200 fmp.toNat 32
  let aw3203 : UInt256 :=
    UInt256.ofNat (MachineState.M aw3200.toNat fmp.toNat 32)
  let mem3212 : ByteArray := (⟨0⟩ : UInt256).toByteArray.write 0 mem3203
    (fmp + ⟨32⟩).toNat 32
  let aw3212 : UInt256 :=
    UInt256.ofNat (MachineState.M aw3203.toNat (fmp + ⟨32⟩).toNat 32)
  let mem3218 : ByteArray := start.toByteArray.write 0 mem3212
    ((⟨64⟩ : UInt256) + fmp).toNat 32
  let aw3218 : UInt256 :=
    UInt256.ofNat (MachineState.M aw3212.toNat ((⟨64⟩ : UInt256) + fmp).toNat 32)
  let mem3225 : ByteArray := endTime.toByteArray.write 0 mem3218
    (fmp + ⟨96⟩).toNat 32
  let aw3225 : UInt256 :=
    UInt256.ofNat (MachineState.M aw3218.toNat (fmp + ⟨96⟩).toNat 32)
  let mem3232 : ByteArray := (⟨0⟩ : UInt256).toByteArray.write 0 mem3225
    (fmp + ⟨128⟩).toNat 32
  let aw3232 : UInt256 :=
    UInt256.ofNat (MachineState.M aw3225.toNat (fmp + ⟨128⟩).toNat 32)
  let mem3240w : ByteArray := (⟨0⟩ : UInt256).toByteArray.write 0 mem3232
    (fmp + ⟨160⟩).toNat 32
  let aw3240w : UInt256 :=
    UInt256.ofNat (MachineState.M aw3232.toNat (fmp + ⟨160⟩).toNat 32)
  obtain ⟨_, _, mem3240, aw3240, rd3240⟩ :
      ∃ k C mem' aw', RD auctionBytecode I g
        s0 ⟨3240⟩
        (⟨0⟩ :: ⟨32⟩ :: ⟨64⟩ :: endTime :: ⟨0⟩ :: start :: nounId :: ret :: R)
        mem' aw' o (cACur, σ) k C := by
    exact ⟨_, _, _, _, by
      simpa [start, endTime] using evm_run rd3189 with [
      jumpdest, push1 ⟨64⟩, dup1,
      raw mload (Cₘ awLoad - Cₘ aw) fmp awLoad (by native_decide)
        (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
        (by rfl) (by rfl) (by evm_ov),
      push1 ⟨192⟩, dup2, add, dup3,
      raw mstore (Cₘ aw3200 - Cₘ awLoad) mem3200 aw3200 (by native_decide)
        (fun _ haws hstks => mstoreCost_of_stack haws hstks (by rfl))
        (by rfl) (by rfl) (by evm_ov),
      dup6, dup2,
      raw mstore (Cₘ aw3203 - Cₘ aw3200) mem3203 aw3203 (by native_decide)
        (fun _ haws hstks => mstoreCost_of_stack haws hstks (by rfl))
        (by rfl) (by rfl) (by evm_ov),
      push0, push1 ⟨32⟩, dup1, dup4, add, dup3, swap1,
      raw mstore (Cₘ aw3212 - Cₘ aw3203) mem3212 aw3212 (by native_decide)
        (fun _ haws hstks => mstoreCost_of_stack haws hstks (by rfl))
        (by rfl) (by rfl) (by evm_ov),
      dup3, dup5, add, dup8, swap1,
      raw mstore (Cₘ aw3218 - Cₘ aw3212) mem3218 aw3218 (by native_decide)
        (fun _ haws hstks => mstoreCost_of_stack haws hstks (by rfl))
        (by rfl) (by rfl) (by evm_ov),
      push1 ⟨96⟩, dup4, add, dup6, swap1,
      raw mstore (Cₘ aw3225 - Cₘ aw3218) mem3225 aw3225 (by native_decide)
        (fun _ haws hstks => mstoreCost_of_stack haws hstks (by rfl))
        (by rfl) (by rfl) (by evm_ov),
      push1 ⟨128⟩, dup4, add, dup3, swap1,
      raw mstore (Cₘ aw3232 - Cₘ aw3225) mem3232 aw3232 (by native_decide)
        (fun _ haws hstks => mstoreCost_of_stack haws hstks (by rfl))
        (by rfl) (by rfl) (by evm_ov),
      push1 ⟨160⟩, swap1, swap3, add, dup2, swap1,
      raw mstore (Cₘ aw3240w - Cₘ aw3232) mem3240w aw3240w (by native_decide)
        (fun _ haws hstks => mstoreCost_of_stack haws hstks (by rfl))
        (by rfl) (by rfl) (by evm_ov)]⟩
  let σ1 := sstoreAccountMap I.codeOwner σ ⟨207⟩ nounId
  let σ2 := sstoreAccountMap I.codeOwner σ1 ⟨208⟩ ⟨0⟩
  let σ3 := sstoreAccountMap I.codeOwner σ2 ⟨209⟩ start
  let σ4 := sstoreAccountMap I.codeOwner σ3 ⟨210⟩ endTime
  let σ5 := sstoreAccountMap I.codeOwner σ4 ⟨211⟩
    (auctionCreateAuctionClearBidderSettledWord (auctionSlotWord ⟨211⟩ σ4 I))
  obtain ⟨_, _, rd3245₀⟩ := (evm_run rd3240 with [push1 ⟨207⟩, dup8, swap1]).sstore
    hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3245⟩ : ∃ k C, RD auctionBytecode I g
      s0 ⟨3245⟩
      (⟨0⟩ :: ⟨32⟩ :: ⟨64⟩ :: endTime :: ⟨0⟩ :: start :: nounId :: ret :: R)
      mem3240 aw3240 o (cACur, σ1) k C := by
    exact ⟨_, _, by simpa [σ1] using rd3245₀⟩
  obtain ⟨_, _, rd3248₀⟩ := (evm_run rd3245 with [push1 ⟨208⟩]).sstore
    hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3248⟩ : ∃ k C, RD auctionBytecode I g
      s0 ⟨3248⟩
      (⟨32⟩ :: ⟨64⟩ :: endTime :: ⟨0⟩ :: start :: nounId :: ret :: R)
      mem3240 aw3240 o (cACur, σ2) k C := by
    exact ⟨_, _, by simpa [σ2] using rd3248₀⟩
  obtain ⟨_, _, rd3253₀⟩ := (evm_run rd3248 with [push1 ⟨209⟩, dup6, swap1]).sstore
    hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3253⟩ : ∃ k C, RD auctionBytecode I g
      s0 ⟨3253⟩
      (⟨32⟩ :: ⟨64⟩ :: endTime :: ⟨0⟩ :: start :: nounId :: ret :: R)
      mem3240 aw3240 o (cACur, σ3) k C := by
    exact ⟨_, _, by simpa [σ3] using rd3253₀⟩
  obtain ⟨_, _, rd3258₀⟩ := (evm_run rd3253 with [push1 ⟨210⟩, dup4, swap1]).sstore
    hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3258⟩ : ∃ k C, RD auctionBytecode I g
      s0 ⟨3258⟩
      (⟨32⟩ :: ⟨64⟩ :: endTime :: ⟨0⟩ :: start :: nounId :: ret :: R)
      mem3240 aw3240 o (cACur, σ4) k C := by
    exact ⟨_, _, by simpa [σ4] using rd3258₀⟩
  have rd3261₀ := evm_run rd3258 with [push1 ⟨211⟩, dup1]
  obtain ⟨_, _, rd3262₀⟩ := rd3261₀.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3262⟩ : ∃ k C, RD auctionBytecode I g
      s0 ⟨3262⟩
      (auctionSlotWord ⟨211⟩ σ4 I :: ⟨211⟩ :: ⟨32⟩ :: ⟨64⟩ :: endTime :: ⟨0⟩ :: start :: nounId :: ret :: R)
      mem3240 aw3240 o (cACur, σ4) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd3262₀⟩
  have rd3272₀ := evm_run rd3262 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨168⟩, shl, sub, not, and]
  have hclear : UInt256.land (UInt256.lnot
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨168⟩) ⟨1⟩))
        (auctionSlotWord ⟨211⟩ σ4 I) =
      auctionCreateAuctionClearBidderSettledWord (auctionSlotWord ⟨211⟩ σ4 I) := by
    unfold auctionCreateAuctionClearBidderSettledWord
    exact u256_land_comm _ _
  have rd3272 := rd3272₀
  rw [hclear] at rd3272
  obtain ⟨_, _, rd3274₀⟩ := (evm_run rd3272 with [swap1]).sstore
    hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3274⟩ : ∃ k C, RD auctionBytecode I g
      s0 ⟨3274⟩
      (⟨32⟩ :: ⟨64⟩ :: endTime :: ⟨0⟩ :: start :: nounId :: ret :: R)
      mem3240 aw3240 o (cACur, σ5) k C := by
    exact ⟨_, _, by simpa [σ5] using rd3274₀⟩
  let eventDataPtr : UInt256 :=
    if (⟨64⟩ : UInt256).toNat ≥ mem3240.size ∨ (⟨64⟩ : UInt256) ≥ aw3240 * ⟨32⟩
    then ⟨0⟩
    else UInt256.ofNat
      (fromByteArrayBigEndian (mem3240.readWithPadding (⟨64⟩ : UInt256).toNat 32))
  let aw3276 : UInt256 :=
    UInt256.ofNat (MachineState.M aw3240.toNat (⟨64⟩ : UInt256).toNat 32)
  let eventMem3279 : ByteArray := start.toByteArray.write 0 mem3240 eventDataPtr.toNat 32
  let eventAw3279 : UInt256 :=
    UInt256.ofNat (MachineState.M aw3276.toNat eventDataPtr.toNat 32)
  let eventMem3285 : ByteArray := endTime.toByteArray.write 0 eventMem3279
    (eventDataPtr + ⟨32⟩).toNat 32
  let eventAw3285 : UInt256 :=
    UInt256.ofNat (MachineState.M eventAw3279.toNat (eventDataPtr + ⟨32⟩).toNat 32)
  have rd3276 := evm_run rd3274 with [
    dup2,
    raw mload (Cₘ aw3276 - Cₘ aw3240) eventDataPtr aw3276 (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov)]
  have rd3279 := evm_run rd3276 with [
    dup6, dup2,
      raw mstore (Cₘ eventAw3279 - Cₘ aw3276) eventMem3279 eventAw3279 (by native_decide)
      (fun _ haws hstks => mstoreCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov)]
  obtain ⟨_, _, rd3285⟩ : ∃ k C, RD auctionBytecode I g
      s0 ⟨3285⟩
      (eventDataPtr :: ⟨64⟩ :: endTime :: ⟨0⟩ :: start :: nounId :: ret :: R)
      eventMem3285 eventAw3285 o (cACur, σ5) k C := by
    exact ⟨_, _, evm_run rd3279 with [
      swap1, dup2, add, dup4, swap1,
      raw mstore (Cₘ eventAw3285 - Cₘ eventAw3279) eventMem3285 eventAw3285 (by native_decide)
        (fun _ haws hstks => mstoreCost_of_stack haws hstks (by rfl))
        (by rfl) (by rfl) (by evm_ov)]⟩
  have rd3336 := evm_run rd3285 with [swap2, swap3, pop]
  have rd3332 := evm_run rd3336 with [dup5, swap2]
  have rdTopic := rd3332.pushConst
    (⟨0xd6eddd1118d71820909c1197aa966dbc15ed6f508554252169cc3d5ccac756ca⟩ : UInt256)
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  let logDataPtr : UInt256 :=
    if (⟨64⟩ : UInt256).toNat ≥ eventMem3285.size ∨
        (⟨64⟩ : UInt256) ≥ eventAw3285 * ⟨32⟩ then ⟨0⟩
    else UInt256.ofNat
      (fromByteArrayBigEndian (eventMem3285.readWithPadding (⟨64⟩ : UInt256).toNat 32))
  let aw3328 : UInt256 :=
    UInt256.ofNat (MachineState.M eventAw3285.toNat (⟨64⟩ : UInt256).toNat 32)
  have rd3328 := evm_run rdTopic with [
    swap2, add, push1 ⟨64⟩,
    raw mload (Cₘ aw3328 - Cₘ eventAw3285) logDataPtr aw3328 (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov)]
  let logSize : UInt256 := ((⟨64⟩ : UInt256) + eventDataPtr).sub logDataPtr
  let aw3333 : UInt256 :=
    UInt256.ofNat (MachineState.M aw3328.toNat logDataPtr.toNat logSize.toNat)
  have rd3332PreLog := evm_run rd3328 with [dup1, swap2, sub, swap1]
  have rd3332' := Auction.RD.log2 (Cₘ aw3333 - Cₘ aw3328) aw3333 rd3332PreLog
    (by native_decide) hperm
    (fun _ haws hstks => auctionLog2Cost_of_stack haws hstks (by rfl))
    (by rfl) (by evm_ov)
  have rdret := evm_run rd3332' with [pop, pop, pop, jump hret]
  have hpost : σ5 = auctionCreateAuctionSuccessPostMap σ I nounId start endTime := by
    simp [σ5, σ4, σ3, σ2, σ1, auctionCreateAuctionSuccessPostMap, endTime]
  rw [hpost] at rdret
  exact ⟨_, _, _, _, by simpa only [start, duration, endTime] using rdret⟩

end Auction
