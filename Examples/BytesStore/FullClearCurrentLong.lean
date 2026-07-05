import Examples.BytesStore.FullSetLongOldLongRuntime
import Examples.StringStoreLite.SetLong

/-!
# BytesStore — full `clearCurrent()` long-current bytecode path
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000

namespace BytesStore

def clearCurrentFullLoopStack (s : StringStoreLite.CurrentLengthLoopState)
    (endp len : UInt256) (I : ExecutionEnv) : List UInt256 :=
  [s.ptr, s.slot, endp, len, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩, bytesStoreSelWord I]

theorem bytesStoreX_clearCurrentLongReachCopyLoop {cA gh bl σ σ₀ A I} {g : Sat256}
    {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1457⟩
      [len, ⟨0⟩, ⟨160⟩, len, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩,
        ⟨263⟩, bytesStoreSelWord I]
      (currentLengthMem len) (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C)
    (hnonzero : len ≠ ⟨0⟩)
    (hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1503⟩
      [⟨160⟩, bytesLikeDataBase ⟨0⟩, (⟨160⟩ : UInt256) + len, len, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩, bytesStoreSelWord I]
      (StringStoreLite.currentLengthLongScratchMem len) (UInt256.ofNat 5)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1457⟩ := hreach
  have rd1464 := evm_run rd1457 with [jumpdest, dup1, iszero, push2 ⟨1532⟩]
  have rd1465 := rd1464.jumpiNT (by native_decide) (isZero_eq_zero_of_ne hnonzero)
    (by evm_ov)
  have rd1491 := evm_run rd1465 with [dup1, push1 ⟨31⟩, lt, push2 ⟨1491⟩]
  have rd1491' := rd1491.jumpiT (by native_decide) hgt31 (by native_decide)
    (by evm_ov)
  have rd1501 := evm_run rd1491' with [
    jumpdest, dup3, add, swap2, swap1, push0,
    raw mstore 0 (StringStoreLite.currentLengthLongScratchMem len) (UInt256.ofNat 5)
      (by native_decide)
      mem_cost
      (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl]; rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, push0]
  have rd1502 := rd1501.keccak256 0 (bytesLikeDataBase ⟨0⟩) (UInt256.ofNat 5)
    (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hstk, haw,
        List.getElem!_cons_zero, List.getElem!_cons_succ,
        show (⟨0⟩ : UInt256).toNat = 0 from rfl,
        show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      native_decide)
    (StringStoreLite.currentLengthLongScratchMem_keccak0 len)
    (by native_decide)
    (by evm_ov)
  exact ⟨_, _, evm_run rd1502 with [swap1]⟩

theorem bytesStoreX_clearCurrentLongFinalCopyToDelete {cA gh bl σ σ₀ A I}
    {g : Sat256} {ptr slot endp len aw awStore awLoad : UInt256} {m memout : ByteArray}
    {mstoreCost mloadCost : Nat}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1503⟩
      [ptr, slot, endp, len, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩,
        bytesStoreSelWord I]
      m aw ByteArray.empty (cA, σ) k C)
    (hdone : UInt256.gt endp ((⟨32⟩ : UInt256) + ptr) = ⟨0⟩)
    (hmemout :
      (StringStoreLite.currentLengthStorageWord σ I slot).toByteArray.write 0 m ptr.toNat 32 =
        memout)
    (hmstoreCost : ∀ s : State, s.machineState.activeWords = aw →
      s.machineState.stack =
        [ptr, StringStoreLite.currentLengthStorageWord σ I slot, ptr, slot, endp, len, ⟨0⟩,
          ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩, bytesStoreSelWord I] →
      memoryExpansionCost s .MSTORE = mstoreCost)
    (hawStore : UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32) = awStore)
    (hmloadCost : ∀ s : State, s.machineState.activeWords = awStore →
      s.machineState.stack = [⟨128⟩, ⟨128⟩, ⟨0⟩, ⟨263⟩, bytesStoreSelWord I] →
      memoryExpansionCost s .MLOAD = mloadCost)
    (hloadVal : (if (⟨128⟩ : UInt256).toNat ≥ memout.size
        ∨ (⟨128⟩ : UInt256) ≥ awStore * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (memout.readWithPadding (⟨128⟩ : UInt256).toNat 32))) = len)
    (hawLoad : UInt256.ofNat (MachineState.M awStore.toNat (⟨128⟩ : UInt256).toNat 32) =
      awLoad) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1732⟩
      [⟨0⟩, ⟨0⟩, ⟨1555⟩, ⟨128⟩, len, ⟨263⟩, bytesStoreSelWord I]
      memout awLoad ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1503⟩ := hreach
  have rd1505 := evm_run rd1503 with [jumpdest, dup2]
  obtain ⟨_, _, rd1506₀⟩ := rd1505.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1506⟩ : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1506⟩
      [StringStoreLite.currentLengthStorageWord σ I slot, ptr, slot, endp, len, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩, bytesStoreSelWord I]
      m aw ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [StringStoreLite.currentLengthStorageWord, initState] using rd1506₀⟩
  have rd1507 := evm_run rd1506 with [dup2]
  have rd1508 := rd1507.mstore mstoreCost memout awStore
    (by native_decide) hmstoreCost hmemout hawStore (by evm_ov)
  have rd1523 := evm_run rd1508 with [
    swap1, push1 ⟨1⟩, add, swap1, push1 ⟨32⟩, add, dup1, dup4, gt, push2 ⟨1503⟩]
  have rd1523' := rd1523.jumpiNT (by native_decide) hdone (by evm_ov)
  have rd1532 := evm_run rd1523' with [
    dup3, swap1, sub, push1 ⟨31⟩, and, dup3, add, swap2,
    jumpdest, pop, pop, pop, pop, pop, swap1, pop, dup1]
  have rd1533 := rd1532.mload mloadCost len awLoad
    (by native_decide) hmloadCost hloadVal hawLoad (by evm_ov)
  exact ⟨_, _, evm_run rd1533 with [
    swap2, pop, push0, push0, push2 ⟨1555⟩, swap2, swap1, push2 ⟨1732⟩,
    jump (by native_decide)]⟩

theorem bytesStoreX_clearCurrentLongCopyContinue {cA gh bl σ σ₀ A I}
    {g : Sat256} {ptr slot endp len aw awStore : UInt256} {m memout : ByteArray}
    {mstoreCost : Nat}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1503⟩
      [ptr, slot, endp, len, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩,
        bytesStoreSelWord I]
      m aw ByteArray.empty (cA, σ) k C)
    (hcontinue : UInt256.gt endp ((⟨32⟩ : UInt256) + ptr) ≠ ⟨0⟩)
    (hmemout :
      (StringStoreLite.currentLengthStorageWord σ I slot).toByteArray.write 0 m ptr.toNat 32 =
        memout)
    (hmstoreCost : ∀ s : State, s.machineState.activeWords = aw →
      s.machineState.stack =
        [ptr, StringStoreLite.currentLengthStorageWord σ I slot, ptr, slot, endp, len, ⟨0⟩,
          ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩, bytesStoreSelWord I] →
      memoryExpansionCost s .MSTORE = mstoreCost)
    (hawStore : UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32) = awStore) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1503⟩
      [(⟨32⟩ : UInt256) + ptr, (⟨1⟩ : UInt256) + slot, endp, len, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩, bytesStoreSelWord I]
      memout awStore ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1503⟩ := hreach
  have rd1505 := evm_run rd1503 with [jumpdest, dup2]
  obtain ⟨_, _, rd1506₀⟩ := rd1505.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1506⟩ : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1506⟩
      [StringStoreLite.currentLengthStorageWord σ I slot, ptr, slot, endp, len, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩, bytesStoreSelWord I]
      m aw ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [StringStoreLite.currentLengthStorageWord, initState] using rd1506₀⟩
  have rd1507 := evm_run rd1506 with [dup2]
  have rd1508 := rd1507.mstore mstoreCost memout awStore
    (by native_decide) hmstoreCost hmemout hawStore (by evm_ov)
  have rd1523 := evm_run rd1508 with [
    swap1, push1 ⟨1⟩, add, swap1, push1 ⟨32⟩, add, dup1, dup4, gt, push2 ⟨1503⟩]
  have rd1503' := rd1523.jumpiT (by native_decide) hcontinue (by native_decide)
    (by evm_ov)
  exact ⟨_, _, rd1503'⟩

theorem bytesStoreX_clearCurrentLongCopyLoopSchedule {cA gh bl σ σ₀ A I}
    {g : Sat256} {endp len : UInt256} (fuel : Nat)
    (st : Nat → StringStoreLite.CurrentLengthLoopState)
    (hsteps : ∀ i, i < fuel →
      StringStoreLite.CurrentLengthLoopStep σ I endp len (st i) (st (i + 1)))
    (hfinal : StringStoreLite.CurrentLengthLoopFinal σ I endp len (st fuel))
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1503⟩
      (clearCurrentFullLoopStack (st 0) endp len I) (st 0).mem (st 0).aw
      ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1732⟩
      [⟨0⟩, ⟨0⟩, ⟨1555⟩, ⟨128⟩, len, ⟨263⟩, bytesStoreSelWord I]
      hfinal.memout hfinal.awLoad ByteArray.empty (cA, σ) k C := by
  induction fuel generalizing st with
  | zero =>
      simpa [clearCurrentFullLoopStack] using
        bytesStoreX_clearCurrentLongFinalCopyToDelete
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
          (g := g) (ptr := (st 0).ptr) (slot := (st 0).slot) (endp := endp)
          (len := len) (aw := (st 0).aw) (m := (st 0).mem)
          (memout := hfinal.memout) (awStore := hfinal.awStore)
          (awLoad := hfinal.awLoad)
          (mstoreCost :=
            Cₘ (UInt256.ofNat (MachineState.M (st 0).aw.toNat (st 0).ptr.toNat 32)) -
              Cₘ (st 0).aw)
          (mloadCost :=
            Cₘ (UInt256.ofNat (MachineState.M hfinal.awStore.toNat (⟨128⟩ : UInt256).toNat 32)) -
              Cₘ hfinal.awStore)
          hreach hfinal.hdone hfinal.hmemout
          (by
            intro s haw hstk
            simpa using
              (StringStoreLite.mstoreCostSpec
                (aw := (st 0).aw) (off := (st 0).ptr)
                (stk := [StringStoreLite.currentLengthStorageWord σ I (st 0).slot,
                  (st 0).ptr, (st 0).slot, endp, len, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩,
                  ⟨263⟩, bytesStoreSelWord I]) s haw hstk))
          hfinal.hawStore
          (by
            intro s haw hstk
            simpa using
              (StringStoreLite.mloadCostSpec
                (aw := hfinal.awStore) (off := (⟨128⟩ : UInt256))
                (stk := [⟨128⟩, ⟨0⟩, ⟨263⟩, bytesStoreSelWord I]) s haw hstk))
          hfinal.hloadVal hfinal.hawLoad
  | succ fuel ih =>
      have hs : StringStoreLite.CurrentLengthLoopStep σ I endp len (st 0) (st 1) := by
        simpa using hsteps 0 (Nat.zero_lt_succ fuel)
      have hnext₀ := bytesStoreX_clearCurrentLongCopyContinue
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := g) (ptr := (st 0).ptr) (slot := (st 0).slot) (endp := endp)
        (len := len) (aw := (st 0).aw) (m := (st 0).mem)
        (memout := (st 1).mem) (awStore := (st 1).aw)
        (mstoreCost :=
          Cₘ (UInt256.ofNat (MachineState.M (st 0).aw.toNat (st 0).ptr.toNat 32)) -
            Cₘ (st 0).aw)
        hreach hs.hcontinue hs.hmemout
        (by
          intro s haw hstk
          simpa using
            (StringStoreLite.mstoreCostSpec
              (aw := (st 0).aw) (off := (st 0).ptr)
              (stk := [StringStoreLite.currentLengthStorageWord σ I (st 0).slot,
                (st 0).ptr, (st 0).slot, endp, len, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩,
                ⟨263⟩, bytesStoreSelWord I]) s haw hstk))
        hs.hawStore
      have hnext : ∃ k C, RD bytesStoreBytecode I g
          (initState cA gh bl σ σ₀ g A I) ⟨1503⟩
          (clearCurrentFullLoopStack ((fun i => st i.succ) 0) endp len I)
          ((fun i => st i.succ) 0).mem ((fun i => st i.succ) 0).aw
          ByteArray.empty (cA, σ) k C := by
        obtain ⟨k, C, rd⟩ := hnext₀
        exact ⟨k, C, by
          simpa [clearCurrentFullLoopStack, hs.hptrNext, hs.hslotNext] using rd⟩
      have hsteps' : ∀ i, i < fuel →
          StringStoreLite.CurrentLengthLoopStep σ I endp len ((fun j => st j.succ) i)
            ((fun j => st j.succ) (i + 1)) := by
        intro i hi
        simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
          hsteps i.succ (Nat.succ_lt_succ hi)
      exact ih (fun i => st i.succ) hsteps' hfinal hnext

theorem bytesStoreX_clearCurrentLongReachDeleteWithSchedule
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (fuel : Nat) (st : Nat → StringStoreLite.CurrentLengthLoopState)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨449⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hlen : len = UInt256.div (bytesStoreCurrentLengthHeaderWord σ I) ⟨2⟩)
    (hnonzero : len ≠ ⟨0⟩)
    (hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩)
    (hinit : st 0 =
      { ptr := ⟨160⟩
        slot := bytesLikeDataBase ⟨0⟩
        mem := StringStoreLite.currentLengthLongScratchMem len
        aw := UInt256.ofNat 5 })
    (hsteps : ∀ i, i < fuel →
      StringStoreLite.CurrentLengthLoopStep σ I ((⟨160⟩ : UInt256) + len) len
        (st i) (st (i + 1)))
    (hfinal :
      StringStoreLite.CurrentLengthLoopFinal σ I ((⟨160⟩ : UInt256) + len) len
        (st fuel)) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1732⟩
      [⟨0⟩, ⟨0⟩, ⟨1555⟩, ⟨128⟩, len, ⟨263⟩, bytesStoreSelWord I]
      hfinal.memout hfinal.awLoad ByteArray.empty (cA, σ) k C := by
  have hdecoded₀ := bytesStoreX_bytesLengthDecoderLongValid
    (hreach := bytesStoreX_clearCurrentReachDecoder hreach)
    (header := bytesStoreCurrentLengthHeaderWord σ I) (ret := ⟨1413⟩)
    (rest := [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩, bytesStoreSelWord I])
    hflag hvalid
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1413₀⟩ := hdecoded₀
  obtain ⟨_, _, rd1413⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1413⟩
        [len, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩, bytesStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [← hlen] using rd1413₀⟩
  have rd1436 := evm_run rd1413 with [
    jumpdest, dup1, push1 ⟨31⟩, add, push1 ⟨32⟩, dup1, swap2, div, mul,
    push1 ⟨32⟩, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      solcFreePtrMem_mload64
      (by native_decide) (by evm_ov),
    swap1, dup2, add, push1 ⟨64⟩,
    raw mstore 0 (currentLengthAllocMem len) (UInt256.ofNat 3)
      (by native_decide)
      mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by native_decide) (by evm_ov)]
  have rd1446 := evm_run rd1436 with [
    dup1, swap3, swap2, swap1, dup2, dup2,
    raw mstore 6 (currentLengthMem len) (UInt256.ofNat 5)
      (by native_decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, add, dup3]
  have rd1448 := evm_run rd1446 with [dup1]
  obtain ⟨_, _, rd1449₀⟩ := rd1448.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1449⟩ : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1449⟩
      [bytesStoreCurrentLengthHeaderWord σ I, ⟨0⟩, ⟨160⟩, len, ⟨0⟩, ⟨128⟩,
        ⟨0⟩, ⟨0⟩, ⟨263⟩, bytesStoreSelWord I]
      (currentLengthMem len) (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C := by
    exact ⟨_, _, by simpa [bytesStoreCurrentLengthHeaderWord, initState] using rd1449₀⟩
  have hdecodedCopy := bytesStoreX_bytesLengthDecoderLongValidMem
    (hreach := ⟨_, _, evm_run rd1449 with [
      push2 ⟨1457⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩)
    (header := bytesStoreCurrentLengthHeaderWord σ I) (ret := ⟨1457⟩)
    (rest := [⟨0⟩, ⟨160⟩, len, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨263⟩,
      bytesStoreSelWord I])
    (mem := currentLengthMem len) (aw := UInt256.ofNat 5)
    (rdata := ByteArray.empty)
    hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1457₀⟩ := hdecodedCopy
  obtain ⟨_, _, rd1457⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1457⟩
        [len, ⟨0⟩, ⟨160⟩, len, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩,
          ⟨263⟩, bytesStoreSelWord I]
        (currentLengthMem len) (UInt256.ofNat 5) ByteArray.empty
        (cA, σ) k C := by
    exact ⟨_, _, by simpa [← hlen] using rd1457₀⟩
  have hloop := bytesStoreX_clearCurrentLongReachCopyLoop
    (g := g) ⟨_, _, rd1457⟩ hnonzero hgt31
  exact bytesStoreX_clearCurrentLongCopyLoopSchedule
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (endp := (⟨160⟩ : UInt256) + len) (len := len) fuel st
    hsteps hfinal (by
      simpa [clearCurrentFullLoopStack, hinit] using hloop)

theorem bytesStoreX_clearDataWordsLoopDone {cA gh bl σinit σ₀ A I} {g : Sat256}
    {τ : AccountMap} {idx count base ret : UInt256} {rest : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1788⟩
      (idx :: count :: base :: ret :: rest) mem aw rdata (cA, τ) k C)
    (hdone : UInt256.gt count idx = ⟨0⟩)
    (hret : (D_J bytesStoreBytecode 0).contains ret = true)
    (hov : rest.length + 6 ≤ 1024) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ret rest mem aw rdata (cA, τ) k C := by
  obtain ⟨_, _, rd1788⟩ := hreach
  have hcond : UInt256.isZero (UInt256.gt count idx) ≠ ⟨0⟩ := by
    rw [hdone]
    decide
  have hovStack : (idx :: count :: base :: ret :: rest).length ≤ 1024 := by
    simp only [List.length_cons]
    omega
  have hlenBase : (base :: ret :: rest).length = rest.length + 2 := by
    simp only [List.length_cons]
  have hlenRet : (ret :: rest).length = rest.length + 1 := by
    simp only [List.length_cons]
  have hlenCount : (count :: base :: ret :: rest).length = rest.length + 3 := by
    simp only [List.length_cons]
  have hlenIdx : (idx :: count :: base :: ret :: rest).length = rest.length + 4 := by
    simp only [List.length_cons]
  have hlenCond :
      (UInt256.isZero (UInt256.gt count idx) :: idx :: count :: base :: ret :: rest).length =
        rest.length + 5 := by
    simp only [List.length_cons]
  have rd1789₀ := rd1788.jumpdest (by native_decide) hovStack
  have rd1789 := rd1789₀.dup1 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1790 := rd1789.dup3 (by native_decide)
    (by rw [hlenBase]; omega)
  have rd1791 := rd1790.gt (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1792 := rd1791.iszero (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1796 := rd1792.push2 ⟨1809⟩ (by native_decide)
    (by rw [hlenCond]; omega)
  have rd1809 := rd1796.jumpiT (by native_decide) hcond (by native_decide)
    (by rw [hlenIdx]; omega)
  have rd1810 := rd1809.jumpdest (by native_decide) hovStack
  have rd1811 := rd1810.pop (by native_decide)
    (by rw [hlenCount]; omega)
  have rd1812 := rd1811.pop (by native_decide)
    (by rw [hlenBase]; omega)
  have rd1813 := rd1812.pop (by native_decide)
    (by rw [hlenRet]; omega)
  exact ⟨_, _, rd1813.jump (by native_decide) hret (by omega)⟩

theorem bytesStoreX_clearDataWordsLoopStep {cA gh bl σinit σ₀ A I} {g : Sat256}
    {τ : AccountMap} {idx count base ret : UInt256} {rest : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1788⟩
      (idx :: count :: base :: ret :: rest) mem aw rdata (cA, τ) k C)
    (hcontinue : UInt256.isZero (UInt256.gt count idx) = ⟨0⟩)
    (hov : rest.length + 7 ≤ 1024) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1788⟩
      (((⟨1⟩ : UInt256) + idx) :: count :: base :: ret :: rest) mem aw rdata
      (cA, sstoreAccountMap I.codeOwner τ (idx + base) ⟨0⟩) k C := by
  obtain ⟨_, _, rd1788⟩ := hreach
  have hlenBase : (base :: ret :: rest).length = rest.length + 2 := by
    simp only [List.length_cons]
  have hlenRet : (ret :: rest).length = rest.length + 1 := by
    simp only [List.length_cons]
  have hlenIdx : (idx :: count :: base :: ret :: rest).length = rest.length + 4 := by
    simp only [List.length_cons]
  have hlenCond :
      (UInt256.isZero (UInt256.gt count idx) :: idx :: count :: base :: ret :: rest).length =
        rest.length + 5 := by
    simp only [List.length_cons]
  have hovStack : (idx :: count :: base :: ret :: rest).length ≤ 1024 := by
    simp only [List.length_cons]
    omega
  have rd1789₀ := rd1788.jumpdest (by native_decide) hovStack
  have rd1789 := rd1789₀.dup1 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1790 := rd1789.dup3 (by native_decide)
    (by rw [hlenBase]; omega)
  have rd1791 := rd1790.gt (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1792 := rd1791.iszero (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1796 := rd1792.push2 ⟨1809⟩ (by native_decide)
    (by rw [hlenCond]; omega)
  have rd1797 := rd1796.jumpiNT (by native_decide) hcontinue
    (by rw [hlenIdx]; omega)
  have rd1798 := rd1797.push0 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1799 := rd1798.dup2 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1800 := rd1799.dup5 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1801 := rd1800.add (by native_decide)
    (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd1802⟩ := rd1801.sstore hperm (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1805 := evm_run rd1802 with [push1 ⟨1⟩, add, push2 ⟨1788⟩]
  exact ⟨_, _, by
    simpa [u256_add_comm idx base] using
      rd1805.jump (by native_decide) (by native_decide)
        (by simp only [List.length_cons]; omega)⟩

theorem bytesStoreX_clearDataWordsLoopGenerated {cA gh bl σinit σ₀ A I} {g : Sat256}
    {τ : AccountMap} {idx count base ret : UInt256} {rest : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256} {fuel : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1788⟩
      (idx :: count :: base :: ret :: rest) mem aw rdata (cA, τ) k C)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero (UInt256.gt count (StringStoreLite.clearDataWordsLoopIndex idx i)) =
        ⟨0⟩)
    (hdone : UInt256.gt count (StringStoreLite.clearDataWordsLoopIndex idx fuel) = ⟨0⟩)
    (hret : (D_J bytesStoreBytecode 0).contains ret = true)
    (hov : rest.length + 7 ≤ 1024) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ret rest mem aw rdata
      (cA, clearDataWordsForwardFrom I.codeOwner τ base idx fuel) k C := by
  induction fuel generalizing idx τ with
  | zero =>
      simpa [StringStoreLite.clearDataWordsLoopIndex, clearDataWordsForwardFrom] using
        bytesStoreX_clearDataWordsLoopDone
          (σinit := σinit) (τ := τ) (idx := idx) (count := count) (base := base)
          (ret := ret) (rest := rest) (mem := mem) (aw := aw) (rdata := rdata)
          hreach hdone hret (by omega)
  | succ n ih =>
      have hstep := bytesStoreX_clearDataWordsLoopStep
        (σinit := σinit) (τ := τ) (idx := idx) (count := count) (base := base)
        (ret := ret) (rest := rest) (mem := mem) (aw := aw) (rdata := rdata)
        hperm hreach
        (by
          simpa [StringStoreLite.clearDataWordsLoopIndex] using
            hcontinue 0 (Nat.zero_lt_succ n))
        hov
      have hstep' :
          ∃ k C, RD bytesStoreBytecode I g
            (initState cA gh bl σinit σ₀ g A I) ⟨1788⟩
            (((⟨1⟩ : UInt256) + idx) :: count :: base :: ret :: rest) mem aw rdata
            (cA, sstoreAccountMap I.codeOwner τ (base + idx) ⟨0⟩) k C := by
        simpa [u256_add_comm idx base] using hstep
      have hcontinueTail : ∀ i, i < n →
          UInt256.isZero
            (UInt256.gt count
              (StringStoreLite.clearDataWordsLoopIndex ((⟨1⟩ : UInt256) + idx) i)) =
              ⟨0⟩ := by
        intro i hi
        simpa [StringStoreLite.clearDataWordsLoopIndex,
          StringStoreLite.clearDataWordsLoopIndex_succ_base] using
          hcontinue (i + 1) (Nat.succ_lt_succ hi)
      have hdoneTail :
          UInt256.gt count
            (StringStoreLite.clearDataWordsLoopIndex ((⟨1⟩ : UInt256) + idx) n) =
            ⟨0⟩ := by
        simpa [StringStoreLite.clearDataWordsLoopIndex,
          StringStoreLite.clearDataWordsLoopIndex_succ_base] using hdone
      simpa [clearDataWordsForwardFrom] using
        ih
          (idx := (⟨1⟩ : UInt256) + idx)
          (τ := sstoreAccountMap I.codeOwner τ (base + idx) ⟨0⟩)
          hstep' hcontinueTail hdoneTail

theorem bytesStoreX_clearCurrentDeleteLongValidToLoop {cA gh bl σ σ₀ A I}
    {g : Sat256} {len : UInt256} {mem rdata : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1732⟩
      [⟨0⟩, ⟨0⟩, ⟨1555⟩, ⟨128⟩, len, ⟨263⟩, bytesStoreSelWord I]
      mem aw rdata (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hlen : len = UInt256.div (bytesStoreCurrentLengthHeaderWord σ I) ⟨2⟩)
    (hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1788⟩
      [⟨0⟩, UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩,
        StringStoreLite.clearCurrentBaseWord, ⟨1784⟩, ⟨1555⟩, ⟨128⟩, len,
        ⟨263⟩, bytesStoreSelWord I]
      (StringStoreLite.clearCurrentBaseMemFrom mem)
      (StringStoreLite.clearCurrentHashAw aw) rdata
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) k C := by
  obtain ⟨_, _, rd1732⟩ := hreach
  have rd1736pre := evm_run rd1732 with [jumpdest, pop, dup1]
  obtain ⟨_, _, rd1736₀⟩ := rd1736pre.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1736⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1736⟩
        [bytesStoreCurrentLengthHeaderWord σ I, ⟨0⟩, ⟨1555⟩, ⟨128⟩, len, ⟨263⟩,
          bytesStoreSelWord I]
        mem aw rdata (cA, σ) k C := by
    exact ⟨_, _, by simpa [bytesStoreCurrentLengthHeaderWord, initState] using rd1736₀⟩
  have hdecode := bytesStoreX_bytesLengthDecoderLongValidMem
    (hreach := ⟨_, _, evm_run rd1736 with [
      push2 ⟨1744⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩)
    (header := bytesStoreCurrentLengthHeaderWord σ I) (ret := ⟨1744⟩)
    (rest := [⟨0⟩, ⟨1555⟩, ⟨128⟩, len, ⟨263⟩, bytesStoreSelWord I])
    (mem := mem) (aw := aw) (rdata := rdata)
    hflag hvalid
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1744₀⟩ := hdecode
  obtain ⟨_, _, rd1744⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1744⟩
        [len, ⟨0⟩, ⟨1555⟩, ⟨128⟩, len, ⟨263⟩, bytesStoreSelWord I]
        mem aw rdata (cA, σ) k C := by
    exact ⟨_, _, by simpa [← hlen] using rd1744₀⟩
  have rd1747pre := evm_run rd1744 with [jumpdest, push0, dup3]
  obtain ⟨_, _, rd1748₀⟩ := rd1747pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1748⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1748⟩
        [len, ⟨0⟩, ⟨1555⟩, ⟨128⟩, len, ⟨263⟩, bytesStoreSelWord I]
        mem aw rdata
        (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) k C := by
    exact ⟨_, _, by simpa [initState] using rd1748₀⟩
  have rd1755 := evm_run rd1748 with [dup1, push1 ⟨31⟩, lt, push2 ⟨1759⟩]
  have rd1759 := rd1755.jumpiT (by native_decide) hgt31 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1773 := evm_run rd1759 with [
    jumpdest, push1 ⟨31⟩, add, push1 ⟨32⟩, swap1, div, swap1, push0,
    raw mstore
      (Cₘ (StringStoreLite.clearCurrentBaseAw aw) - Cₘ aw)
      (StringStoreLite.clearCurrentBaseMemFrom mem)
      (StringStoreLite.clearCurrentBaseAw aw) (by native_decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
          StringStoreLite.clearCurrentBaseAw])
      (by rfl) (by rfl) (by evm_ov),
    push1 ⟨32⟩, push0]
  have rd1774 := evm_run rd1773 with [
    raw keccak256
      (Cₘ (StringStoreLite.clearCurrentHashAw aw) -
        Cₘ (StringStoreLite.clearCurrentBaseAw aw))
      StringStoreLite.clearCurrentBaseWord (StringStoreLite.clearCurrentHashAw aw)
      (by native_decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
          StringStoreLite.clearCurrentHashAw, StringStoreLite.clearCurrentBaseAw])
      (StringStoreLite.clearCurrentBaseMemFrom_keccak mem) (by rfl) (by evm_ov)]
  exact ⟨_, _, evm_run rd1774 with [
    swap1, push2 ⟨1784⟩, swap2, swap1, push2 ⟨1786⟩, jump (by native_decide),
    jumpdest, push0]⟩

theorem bytesStoreX_clearCurrentLoopReturnToWrapper {cA gh bl σinit σ₀ A I}
    {g : Sat256} {τ : AccountMap} {mem rdata : ByteArray} {aw len : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1784⟩
      [⟨1555⟩, ⟨128⟩, len, ⟨263⟩, bytesStoreSelWord I]
      mem aw rdata (cA, τ) k C) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨263⟩
      [len, bytesStoreSelWord I] mem aw rdata (cA, τ) k C := by
  obtain ⟨_, _, rd1784⟩ := hreach
  have rd1555 := evm_run rd1784 with [jumpdest, jump (by native_decide)]
  exact ⟨_, _, evm_run rd1555 with [
    jumpdest, pop, swap1, jump (by native_decide)]⟩

theorem bytesStoreX_clearCurrentDeleteLongValidWithLoopSchedule
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {len : UInt256} {mem rdata : ByteArray} {aw : UInt256} {fuel : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1732⟩
      [⟨0⟩, ⟨0⟩, ⟨1555⟩, ⟨128⟩, len, ⟨263⟩, bytesStoreSelWord I]
      mem aw rdata (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hlen : len = UInt256.div (bytesStoreCurrentLengthHeaderWord σ I) ⟨2⟩)
    (hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.gt (UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩)
          (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ i)) = ⟨0⟩)
    (hdone :
      UInt256.gt (UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩)
        (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ fuel) = ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨263⟩
      [len, bytesStoreSelWord I]
      (StringStoreLite.clearCurrentBaseMemFrom mem)
      (StringStoreLite.clearCurrentHashAw aw) rdata
      (cA, clearDataWordsForwardFrom I.codeOwner
        (sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
        StringStoreLite.clearCurrentBaseWord ⟨0⟩ fuel) k C := by
  have hloopStart := bytesStoreX_clearCurrentDeleteLongValidToLoop
    (g := g) hperm hreach hflag hvalid hlen hgt31
  have hloop := bytesStoreX_clearDataWordsLoopGenerated
    (σinit := σ) (τ := sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
    (idx := (⟨0⟩ : UInt256))
    (count := UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩)
    (base := StringStoreLite.clearCurrentBaseWord)
    (ret := (⟨1784⟩ : UInt256))
    (rest := [⟨1555⟩, ⟨128⟩, len, ⟨263⟩, bytesStoreSelWord I])
    (mem := StringStoreLite.clearCurrentBaseMemFrom mem)
    (aw := StringStoreLite.clearCurrentHashAw aw)
    (rdata := rdata)
    (fuel := fuel)
    hperm hloopStart hcontinue hdone (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact bytesStoreX_clearCurrentLoopReturnToWrapper hloop

theorem bytesStoreX_clearCurrentDeleteLongValid {cA gh bl σ σ₀ A I}
    {g : Sat256} {len : UInt256} {mem rdata : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1732⟩
      [⟨0⟩, ⟨0⟩, ⟨1555⟩, ⟨128⟩, len, ⟨263⟩, bytesStoreSelWord I]
      mem aw rdata (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hlen : len = UInt256.div (bytesStoreCurrentLengthHeaderWord σ I) ⟨2⟩)
    (hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨263⟩
      [len, bytesStoreSelWord I]
      (StringStoreLite.clearCurrentBaseMemFrom mem)
      (StringStoreLite.clearCurrentHashAw aw) rdata
      (cA, clearDataWordsForwardFrom I.codeOwner
        (sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
        StringStoreLite.clearCurrentBaseWord ⟨0⟩
        (UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩).toNat) k C := by
  let count := UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩
  have hcontinue : ∀ i, i < count.toNat →
      UInt256.isZero
        (UInt256.gt count (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ i)) = ⟨0⟩ := by
    intro i hi
    have hidx : (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ i).toNat = i := by
      rw [StringStoreLite.clearDataWordsLoopIndex_zero_ofNat]
      exact ulit_toNat' i (lt_trans hi count.val.isLt)
    have hgt : UInt256.gt count (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ i) = ⟨1⟩ :=
      ugt_one (by simpa [hidx] using hi)
    rw [hgt]
    decide
  have hdone :
      UInt256.gt count (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ count.toNat) = ⟨0⟩ := by
    rw [StringStoreLite.clearDataWordsLoopIndex_zero_ofNat, u256_ofNat_toNat count]
    exact ugt_zero (a := count) (b := count) (Nat.le_refl _)
  simpa [count] using
    bytesStoreX_clearCurrentDeleteLongValidWithLoopSchedule
      (g := g) (len := len) (fuel := count.toNat)
      hperm hreach hflag hvalid hlen hgt31 hcontinue hdone

theorem bytesStoreX_clearCurrentReturnFromFullWrapperGeneric
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {len freePtr aw awLoad awStore awFinal : UInt256}
    {mem memret rdata : ByteArray}
    {mloadCost mstoreCost finalMloadCost retCost : Nat}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨263⟩
      [len, bytesStoreSelWord I] mem aw rdata (cA, τ) k C)
    (hmloadCost : ∀ s : State, s.machineState.activeWords = aw →
      s.machineState.stack = [⟨64⟩, len, bytesStoreSelWord I] →
      memoryExpansionCost s .MLOAD = mloadCost)
    (hfreePtr : (if (⟨64⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = freePtr)
    (hawLoad : UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32) =
      awLoad)
    (hmemret : len.toByteArray.write 0 mem freePtr.toNat 32 = memret)
    (hmstoreCost : ∀ s : State, s.machineState.activeWords = awLoad →
      s.machineState.stack = [freePtr, len, freePtr, bytesStoreSelWord I] →
      memoryExpansionCost s .MSTORE = mstoreCost)
    (hawStore : UInt256.ofNat (MachineState.M awLoad.toNat freePtr.toNat 32) =
      awStore)
    (hfinalMloadCost : ∀ s : State, s.machineState.activeWords = awStore →
      s.machineState.stack = [⟨64⟩, (⟨32⟩ : UInt256) + freePtr, bytesStoreSelWord I] →
      memoryExpansionCost s .MLOAD = finalMloadCost)
    (hfinalFreePtr : (if (⟨64⟩ : UInt256).toNat ≥ memret.size
        ∨ (⟨64⟩ : UInt256) ≥ awStore * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (memret.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        freePtr)
    (hawFinal :
      UInt256.ofNat (MachineState.M awStore.toNat (⟨64⟩ : UInt256).toNat 32) =
        awFinal)
    (hretBytes :
      memret.readWithPadding freePtr.toNat
        (UInt256.sub ((⟨32⟩ : UInt256) + freePtr) freePtr).toNat = UInt256.toByteArray len)
    (hretCost : ∀ s : State, s.machineState.activeWords = awFinal →
      s.machineState.stack =
        [freePtr, UInt256.sub ((⟨32⟩ : UInt256) + freePtr) freePtr, bytesStoreSelWord I] →
      memoryExpansionCost s .RETURN = retCost) :
    RDret bytesStoreBytecode g (initState cA gh bl σinit σ₀ g A I) (cA, τ)
      (UInt256.toByteArray len) := by
  obtain ⟨_, _, rd263⟩ := hreach
  have rd266 := evm_run rd263 with [jumpdest, push1 ⟨64⟩]
  have rd267 := rd266.mload mloadCost freePtr awLoad
    (by native_decide) hmloadCost hfreePtr hawLoad (by evm_ov)
  have rd273₀ := evm_run rd267 with [swap1, dup2]
  have rd274 := rd273₀.mstore mstoreCost memret awStore
    (by native_decide) hmstoreCost hmemret hawStore (by evm_ov)
  have rd277 := evm_run rd274 with [push1 ⟨32⟩, add]
  have rd280 := evm_run rd277 with [jumpdest, push1 ⟨64⟩]
  have rd281 := rd280.mload finalMloadCost freePtr awFinal
    (by native_decide) hfinalMloadCost hfinalFreePtr hawFinal (by evm_ov)
  have rd284 := evm_run rd281 with [dup1, swap2, sub, swap1]
  exact rd284.ret retCost (UInt256.toByteArray len)
    (by native_decide) hretCost hretBytes (by evm_ov)

theorem bytesStoreX_clearCurrentLongValidGenerated {cA gh bl σ σ₀ A I}
    {g : Sat256} {len : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨449⟩ [bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hlen : len = UInt256.div (bytesStoreCurrentLengthHeaderWord σ I) ⟨2⟩)
    (hnonzero : len ≠ ⟨0⟩)
    (hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, clearDataWordsForwardFrom I.codeOwner
        (sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
        StringStoreLite.clearCurrentBaseWord ⟨0⟩
        (UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩).toNat)
      (UInt256.toByteArray len) := by
  let fuel := (len.toNat - 1) / 32
  let copyAwStore := UInt256.ofNat
    (MachineState.M (StringStoreLite.currentLengthGeneratedLoopState σ I len fuel).aw.toNat
      (StringStoreLite.currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32)
  let copyMloadCost :=
    Cₘ (UInt256.ofNat (MachineState.M copyAwStore.toNat (⟨128⟩ : UInt256).toNat 32)) -
      Cₘ copyAwStore
  let copyAwLoad := UInt256.ofNat
    (MachineState.M copyAwStore.toNat (⟨128⟩ : UInt256).toNat 32)
  have hlenLt : len.toNat < 2 ^ 255 :=
    StringStoreLite.clearCurrent_len_toNat_lt_sign_of_div2
      (header := bytesStoreCurrentLengthHeaderWord σ I) hlen
  have hcontinue : ∀ i, i < fuel →
      UInt256.gt ((⟨160⟩ : UInt256) + len)
        ((⟨32⟩ : UInt256) +
          (StringStoreLite.currentLengthGeneratedLoopState σ I len i).ptr) ≠ ⟨0⟩ := by
    simpa [fuel] using
      StringStoreLite.currentLengthConcreteFuel_continue
        (σ := σ) (I := I) (len := len) hlenLt hgt31
  have hdone : UInt256.gt ((⟨160⟩ : UInt256) + len)
      ((⟨32⟩ : UInt256) +
        (StringStoreLite.currentLengthGeneratedLoopState σ I len fuel).ptr) = ⟨0⟩ := by
    simpa [fuel] using
      StringStoreLite.currentLengthConcreteFuel_done
        (σ := σ) (I := I) (len := len) hlenLt hgt31
  have hcopyMloadCost : ∀ st : State, st.machineState.activeWords = copyAwStore →
      st.machineState.stack = [⟨128⟩, ⟨128⟩, ⟨0⟩, ⟨153⟩,
        StringStoreLite.stringStoreLiteSelWord I] →
      memoryExpansionCost st .MLOAD = copyMloadCost := by
    intro st haw hstk
    simpa [copyMloadCost, copyAwStore] using
      (StringStoreLite.mloadCostSpec
        (aw := copyAwStore) (off := (⟨128⟩ : UInt256))
        (stk := [⟨128⟩, ⟨0⟩, ⟨153⟩,
          StringStoreLite.stringStoreLiteSelWord I]) st haw hstk)
  have hcopyLoadVal :
      (if (⟨128⟩ : UInt256).toNat ≥
          (StringStoreLite.currentLengthCopyMem
            (StringStoreLite.currentLengthGeneratedLoopState σ I len fuel).mem
            (StringStoreLite.currentLengthGeneratedLoopState σ I len fuel).ptr
            (StringStoreLite.currentLengthStorageWord σ I
              (StringStoreLite.currentLengthGeneratedLoopState σ I len fuel).slot)).size
          ∨ (⟨128⟩ : UInt256) ≥ copyAwStore * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((StringStoreLite.currentLengthCopyMem
              (StringStoreLite.currentLengthGeneratedLoopState σ I len fuel).mem
              (StringStoreLite.currentLengthGeneratedLoopState σ I len fuel).ptr
              (StringStoreLite.currentLengthStorageWord σ I
                (StringStoreLite.currentLengthGeneratedLoopState σ I len fuel).slot)).readWithPadding
                (⟨128⟩ : UInt256).toNat 32))) = len := by
    simpa [fuel, copyAwStore] using
      StringStoreLite.currentLengthConcreteFuel_finalMload128
        (σ := σ) (I := I) (len := len) hlenLt
  have hcopyAwLoad :
      UInt256.ofNat (MachineState.M copyAwStore.toNat (⟨128⟩ : UInt256).toNat 32) =
        copyAwLoad := by
    rfl
  let copyFinal := StringStoreLite.currentLengthGeneratedLoopFinal
    (σ := σ) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
    (fuel := fuel) (finalMloadCost := copyMloadCost) (awLoad := copyAwLoad)
    hdone hcopyMloadCost hcopyLoadVal hcopyAwLoad
  have hreadStart : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1732⟩
      [⟨0⟩, ⟨0⟩, ⟨1555⟩, ⟨128⟩, len, ⟨263⟩, bytesStoreSelWord I]
      copyFinal.memout copyFinal.awLoad ByteArray.empty (cA, σ) k C := by
    simpa [copyFinal, fuel, copyAwStore, copyMloadCost, copyAwLoad] using
      bytesStoreX_clearCurrentLongReachDeleteWithSchedule
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := g) (len := len) fuel (StringStoreLite.currentLengthGeneratedLoopState σ I len)
        hreach hflag hvalid hlen hnonzero hgt31
        StringStoreLite.currentLengthGeneratedLoopState_zero
        (StringStoreLite.currentLengthGeneratedLoopSteps
          (σ := σ) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
          (fuel := fuel) hcontinue)
        (StringStoreLite.currentLengthGeneratedLoopFinal
          (σ := σ) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
          (fuel := fuel) (finalMloadCost := copyMloadCost) (awLoad := copyAwLoad)
          hdone hcopyMloadCost hcopyLoadVal hcopyAwLoad)
  have hdelReach := bytesStoreX_clearCurrentDeleteLongValid
    (g := g) (len := len) (mem := copyFinal.memout) (aw := copyFinal.awLoad)
    hperm hreadStart hflag hvalid hlen hgt31
  have hadd32 : ∀ i, i ≤ fuel →
      (((⟨32⟩ : UInt256) +
          (StringStoreLite.currentLengthGeneratedLoopState σ I len i).ptr).toNat =
        (StringStoreLite.currentLengthGeneratedLoopState σ I len i).ptr.toNat + 32) := by
    simpa [fuel] using
      StringStoreLite.currentLengthConcreteFuel_add32
        (σ := σ) (I := I) (len := len) hlenLt
  have hptrBound :
      (StringStoreLite.currentLengthGeneratedLoopState σ I len fuel).ptr.toNat + 32 <
        UInt256.size := by
    simpa [fuel] using
      StringStoreLite.currentLengthGeneratedFinalCopy_ptrBound_of_fuelBound
        (σ := σ) (I := I) (len := len) (fuel := fuel)
        hadd32 (by simpa [fuel] using StringStoreLite.currentLengthFuel_bound hlenLt)
  have hMNoWrap :
      MachineState.M (StringStoreLite.currentLengthGeneratedLoopState σ I len fuel).aw.toNat
          (StringStoreLite.currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32 * 32 <
        UInt256.size :=
    StringStoreLite.currentLengthGeneratedFinalCopy_mNoWrap_of_ptr_add32
      (σ := σ) (I := I) (len := len) (fuel := fuel) hadd32 hptrBound
  have hcopyAwLoadEq : copyFinal.awLoad = copyAwStore := by
    simpa [copyFinal, copyAwStore, copyAwLoad] using
      StringStoreLite.currentLengthGeneratedFinalCopy_mload128_aw_eq_awStore_of_mNoWrap
        (σ := σ) (I := I) (len := len) (fuel := fuel) hMNoWrap
  have hcopyAwGe5 : 5 ≤ copyFinal.awLoad.toNat := by
    rw [hcopyAwLoadEq]
    simpa [copyAwStore] using
      StringStoreLite.currentLengthGeneratedFinalCopy_awStore_ge5_of_mNoWrap
        (σ := σ) (I := I) (len := len) (fuel := fuel) hMNoWrap
  have hdeleteAwEq :
      StringStoreLite.clearCurrentHashAw copyFinal.awLoad = copyFinal.awLoad :=
    StringStoreLite.clearCurrentHashAw_eq_self_of_ge1
      (by omega : 1 ≤ copyFinal.awLoad.toNat)
  let deleteMem := StringStoreLite.clearCurrentBaseMemFrom copyFinal.memout
  let deleteAw := StringStoreLite.clearCurrentHashAw copyFinal.awLoad
  let freePtr := StringStoreLite.currentLengthFreePtr len
  have hcopyRead64 :
      copyFinal.memout.readWithPadding 64 32 = UInt256.toByteArray freePtr := by
    simpa [copyFinal, freePtr] using
      StringStoreLite.currentLengthGeneratedLoopFinal_read64_of_add32
        (σ := σ) (I := I) (len := len) (fuel := fuel)
        (finalMloadCost := copyMloadCost) (awLoad := copyAwLoad)
        hcontinue hdone hcopyMloadCost hcopyLoadVal hcopyAwLoad hadd32
  have hcopySize : copyFinal.memout.size = freePtr.toNat := by
    simpa [copyFinal, fuel, freePtr] using
      StringStoreLite.currentLengthConcreteFuel_finalCopy_size_eq_freePtr
        (σ := σ) (I := I) (len := len) hlenLt hgt31
  have hfreeGe96 : 96 ≤ freePtr.toNat :=
    StringStoreLite.currentLengthFreePtr_ge96_of_long (len := len) hlenLt hgt31
  have hdeleteRead64 : deleteMem.readWithPadding 64 32 = UInt256.toByteArray freePtr := by
    simpa [deleteMem, hcopyRead64] using
      StringStoreLite.clearCurrentBaseMemFrom_read64 (mem := copyFinal.memout) (by omega)
  have hdeleteSize : deleteMem.size = copyFinal.memout.size := by
    simpa [deleteMem] using
      StringStoreLite.clearCurrentBaseMemFrom_size_eq
        (mem := copyFinal.memout) (by omega : 32 ≤ copyFinal.memout.size)
  have hcopyAwStoreNoWrap : copyAwStore.toNat * 32 < UInt256.size := by
    let m := MachineState.M
      (StringStoreLite.currentLengthGeneratedLoopState σ I len fuel).aw.toNat
      (StringStoreLite.currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32
    have hmSize : m < UInt256.size := by
      have hle : m ≤ m * 32 := by
        simpa using Nat.mul_le_mul_left m (by decide : 1 ≤ 32)
      exact lt_of_le_of_lt hle (by simpa [m] using hMNoWrap)
    simpa [copyAwStore, m, ulit_toNat' m hmSize] using hMNoWrap
  have hdeleteAwNoWrap : deleteAw.toNat * 32 < UInt256.size := by
    simpa [deleteAw, hdeleteAwEq, hcopyAwLoadEq] using hcopyAwStoreNoWrap
  have hdeleteAw64 : ¬ (⟨64⟩ : UInt256) ≥ deleteAw * ⟨32⟩ :=
    StringStoreLite.wordMul32_not_le64_of_ge3
      (by simpa [deleteAw, hdeleteAwEq] using
        (show 3 ≤ copyFinal.awLoad.toNat from by omega))
      hdeleteAwNoWrap
  have hfreePtrVal :
      (if (⟨64⟩ : UInt256).toNat ≥ deleteMem.size
          ∨ (⟨64⟩ : UInt256) ≥ deleteAw * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (deleteMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        freePtr := by
    exact mloadWordValue_of_readWithPadding
      (mem := deleteMem) (aw := deleteAw) (off := (⟨64⟩ : UInt256)) (v := freePtr)
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, hdeleteSize, hcopySize]; omega)
      hdeleteAw64
      (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hdeleteRead64)
  have hwrapperAwLoad :
      UInt256.ofNat (MachineState.M deleteAw.toNat (⟨64⟩ : UInt256).toNat 32) =
        deleteAw :=
    StringStoreLite.activeWordsMload64_eq_self
      (aw := deleteAw)
      (by simpa [deleteAw, hdeleteAwEq] using
        (show 3 ≤ copyFinal.awLoad.toNat from by omega))
  let wrapperMloadCost :=
    Cₘ (UInt256.ofNat (MachineState.M deleteAw.toNat (⟨64⟩ : UInt256).toNat 32)) -
      Cₘ deleteAw
  let wrapperAwStore := UInt256.ofNat (MachineState.M deleteAw.toNat freePtr.toNat 32)
  let wrapperMstoreCost := Cₘ wrapperAwStore - Cₘ deleteAw
  let returnMem := len.toByteArray.write 0 deleteMem freePtr.toNat 32
  have hreturnMem : len.toByteArray.write 0 deleteMem freePtr.toNat 32 = returnMem := rfl
  have hmstoreCost : ∀ s : State, s.machineState.activeWords = deleteAw →
      s.machineState.stack = [freePtr, len, freePtr, bytesStoreSelWord I] →
      memoryExpansionCost s .MSTORE = wrapperMstoreCost := by
    intro s haw hstk
    simpa [wrapperMstoreCost, wrapperAwStore] using
      (StringStoreLite.mstoreCostSpec (aw := deleteAw) (off := freePtr)
        (stk := [len, freePtr, bytesStoreSelWord I]) s haw hstk)
  have hwrapperAwStore :
      UInt256.ofNat (MachineState.M deleteAw.toNat freePtr.toNat 32) =
        wrapperAwStore := by
    rfl
  have hfreePtrLeMem : freePtr.toNat ≤ deleteMem.size := by
    rw [hdeleteSize, hcopySize]
  have hreturnRead64 : returnMem.readWithPadding 64 32 = UInt256.toByteArray freePtr := by
    simpa [returnMem] using
      StringStoreLite.currentLengthReturnWrite_preserves_read64
        (mem := deleteMem) (len := len) (freePtr := freePtr)
        hfreeGe96 hfreePtrLeMem hdeleteRead64
  have hreturnSizeGe64 : 64 < returnMem.size := by
    have hge := StringStoreLite.writeWord_size_gt64_of_mem
      (mem := deleteMem) (off := freePtr.toNat) (word := len)
      (by rw [hdeleteSize, hcopySize]; omega)
      hfreePtrLeMem
    simpa [returnMem] using hge
  have hwrapperAwStoreNoWrap :
      wrapperAwStore.toNat * 32 < UInt256.size := by
    simpa [wrapperAwStore, deleteAw, hdeleteAwEq, hcopyAwLoadEq, freePtr] using
      StringStoreLite.currentLengthConcreteWrapperStore_aw_mul32_lt
        (σ := σ) (I := I) (len := len) hlenLt hgt31
  have hwrapperAw64 : ¬ (⟨64⟩ : UInt256) ≥ wrapperAwStore * ⟨32⟩ :=
    StringStoreLite.wordMul32_not_le64_of_ge3
      (by
        simpa [wrapperAwStore, deleteAw, hdeleteAwEq, hcopyAwLoadEq, freePtr] using
          StringStoreLite.currentLengthConcreteWrapperStore_aw_ge3
            (σ := σ) (I := I) (len := len) hlenLt hgt31)
      hwrapperAwStoreNoWrap
  have hfinalFreePtrVal :
      (if (⟨64⟩ : UInt256).toNat ≥ returnMem.size
          ∨ (⟨64⟩ : UInt256) ≥ wrapperAwStore * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (returnMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        freePtr := by
    exact mloadWordValue_of_readWithPadding
      (mem := returnMem) (aw := wrapperAwStore) (off := (⟨64⟩ : UInt256)) (v := freePtr)
      (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hreturnSizeGe64)
      hwrapperAw64
      (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hreturnRead64)
  let wrapperAwFinal := UInt256.ofNat (MachineState.M wrapperAwStore.toNat
    (⟨64⟩ : UInt256).toNat 32)
  let wrapperFinalMloadCost := Cₘ wrapperAwFinal - Cₘ wrapperAwStore
  have hwrapperAwFinal :
      UInt256.ofNat (MachineState.M wrapperAwStore.toNat (⟨64⟩ : UInt256).toNat 32) =
        wrapperAwFinal := rfl
  have hretLen : (UInt256.sub ((⟨32⟩ : UInt256) + freePtr) freePtr).toNat = 32 :=
    by
      have hretLenCore : (UInt256.sub (freePtr + ⟨32⟩) freePtr).toNat = 32 := by
        simpa [freePtr] using
          (StringStoreLite.currentLengthFreePtr_retLen_of_len_lt_sign_pos
            (len := len) hlenLt (by
              have hgtNat : 31 < len.toNat := by
                simpa [show (⟨31⟩ : UInt256).toNat = 31 from by decide] using
                  ult_ne_zero_toNat_lt hgt31
              omega))
      simpa [u256_add_comm freePtr (⟨32⟩ : UInt256)] using hretLenCore
  have hretBytes :
      returnMem.readWithPadding freePtr.toNat
        (UInt256.sub ((⟨32⟩ : UInt256) + freePtr) freePtr).toNat =
          UInt256.toByteArray len := by
    rw [hretLen]
    simpa [returnMem] using
      StringStoreLite.currentLengthReturnWrite_readBack
        (mem := deleteMem) (len := len) (freePtr := freePtr) hfreePtrLeMem
  let wrapperRetCost :=
    Cₘ (UInt256.ofNat (MachineState.M wrapperAwFinal.toNat freePtr.toNat
      (UInt256.sub ((⟨32⟩ : UInt256) + freePtr) freePtr).toNat)) - Cₘ wrapperAwFinal
  have hretCost : ∀ s : State, s.machineState.activeWords = wrapperAwFinal →
      s.machineState.stack =
        [freePtr, UInt256.sub ((⟨32⟩ : UInt256) + freePtr) freePtr, bytesStoreSelWord I] →
      memoryExpansionCost s .RETURN = wrapperRetCost := by
    intro s haw hstk
    simpa [wrapperRetCost] using
      (StringStoreLite.returnCostSpec
        (aw := wrapperAwFinal) (off := freePtr)
        (len := UInt256.sub ((⟨32⟩ : UInt256) + freePtr) freePtr)
        (stk := [bytesStoreSelWord I]) s haw hstk)
  exact bytesStoreX_clearCurrentReturnFromFullWrapperGeneric
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g)
    (τ := clearDataWordsForwardFrom I.codeOwner
      (sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
      StringStoreLite.clearCurrentBaseWord ⟨0⟩
      (UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩).toNat)
    (len := len) (freePtr := freePtr) (aw := deleteAw) (awLoad := deleteAw)
    (awStore := wrapperAwStore) (awFinal := wrapperAwFinal)
    (mem := deleteMem) (memret := returnMem) (rdata := ByteArray.empty)
    (mloadCost := wrapperMloadCost)
    (mstoreCost := wrapperMstoreCost)
    (finalMloadCost := wrapperFinalMloadCost)
    (retCost := wrapperRetCost)
    (by simpa [deleteMem, deleteAw] using hdelReach)
    (by
      intro s haw hstk
      simpa [wrapperMloadCost] using
        (StringStoreLite.mloadCostSpec (aw := deleteAw) (off := (⟨64⟩ : UInt256))
          (stk := [len, bytesStoreSelWord I]) s haw hstk))
    hfreePtrVal
    hwrapperAwLoad
    hreturnMem
    hmstoreCost
    hwrapperAwStore
    (by
      intro s haw hstk
      simpa [wrapperFinalMloadCost, wrapperAwFinal] using
        (StringStoreLite.mloadCostSpec (aw := wrapperAwStore) (off := (⟨64⟩ : UInt256))
          (stk := [(⟨32⟩ : UInt256) + freePtr, bytesStoreSelWord I]) s haw hstk))
    hfinalFreePtrVal
    hwrapperAwFinal
    hretBytes
    hretCost

theorem bytesStoreReadCurrentLongExists {evm : EVM.State} {header len : UInt256}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    ∃ copy : ByteArray,
      evalExpr? bytesStoreConfig { contract := bytesStoreContract, locals := ∅ }
        evm (.storage currentRef) = .ok (.bytes copy) ∧ copy.size = len.toNat := by
  exact evalSolidityBytesLongExists
    (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
    (solm := { contract := bytesStoreContract, locals := ∅ })
    (evm := evm) (ref := currentRef) (er := { base := "current", steps := [] })
    (baseSlot := ⟨0⟩) (header := header) (len := len)
    rfl (bytesStoreCurrentLengthResolve evm) bytesStoreCurrentLengthBaseSlot
    hload hflag hlen hvalid

theorem bytesStoreDeleteCurrentLongPrepared {evm : EVM.State} {header len : UInt256}
    {copy : ByteArray}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    deleteStorage? bytesStoreConfig
      { contract := bytesStoreContract,
        locals := (∅ : Store).insert "copy" (.bytes copy) }
      evm currentRef =
        .ok (clearSolidityBytesDataWordsFrom
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ ⟨0⟩)
          ⟨0⟩ 0 ((len.toNat + 31) / 32)) := by
  let solm : Frame :=
    { contract := bytesStoreContract, locals := (∅ : Store).insert "copy" (.bytes copy) }
  have hresolve :
      resolveStorageRef? bytesStoreConfig solm evm currentRef =
        .ok ({ base := "current", steps := [] }, .bytes) := by
    exact bytesStoreCurrentResolveOfGetNone (evm := evm) (locals := solm.locals) (by
      simp [solm, currentRef])
  exact deleteSolidityBytesLongPrepared
    (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
    (solm := solm)
    (evm := evm) (ref := currentRef) (er := { base := "current", steps := [] })
    (baseSlot := ⟨0⟩) (header := header) (len := len)
    rfl hresolve bytesStoreCurrentLengthBaseSlot hload hflag hlen hvalid

theorem bytesStoreClearCurrentLongValidRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠
          ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len := UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩
  have hlen : len = UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩ := rfl
  have hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩ :=
    StringStoreLite.clearCurrentLongValid_gt31
      (header := bytesStoreCurrentLengthHeaderWord σ_evm I) (len := len)
      hflag (by simpa [len] using hvalid)
  have hnonzero : len ≠ ⟨0⟩ :=
    StringStoreLite.currentLengthLongValid_nonzero
      (header := bytesStoreCurrentLengthHeaderWord σ_evm I) (len := len)
      hflag (by simpa [len] using hvalid)
  have hlenLt : len.toNat < 2 ^ 255 :=
    StringStoreLite.clearCurrent_len_toNat_lt_sign_of_div2
      (header := bytesStoreCurrentLengthHeaderWord σ_evm I) hlen
  have hcountNat :
      (UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩).toNat =
        (len.toNat + 31) / 32 := by
    have hadd : (((⟨31⟩ : UInt256) + len).toNat = 31 + len.toNat) := by
      rw [uadd_toNat, show (⟨31⟩ : UInt256).toNat = 31 from by decide]
      exact Nat.mod_eq_of_lt (by
        have hsize : (2 : Nat) ^ 255 + 31 < UInt256.size := by
          norm_num [UInt256.size]
        nlinarith)
    rw [udiv_toNat, hadd, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
    rw [Nat.add_comm 31 len.toNat]
  have hsz := bytesStoreClearCurrentSelector_size hsel
  have hd := bytesStoreDispatch_clearCurrent (cd := I.calldata)
    (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_clearCurrent (I := I) hsz
  have hreach := bytesStoreReachClearCurrent (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hret := bytesStoreX_clearCurrentLongValidGenerated
    (g := Sat256.ofUInt256 g) (len := len)
    hperm hreach hflag (by simpa [len] using hvalid) hlen hnonzero hgt31
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolmLen := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ ⟨0⟩
  let evmSolm1 := clearSolidityBytesDataWordsFrom evmSolmLen ⟨0⟩ 0 ((len.toNat + 31) / 32)
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        bytesStoreCurrentLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadCurrentLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  obtain ⟨copy, hread, hcopySize⟩ :=
    bytesStoreReadCurrentLongExists (evm := evmSolm0)
      (header := bytesStoreCurrentLengthHeaderWord σ_evm I) (len := len)
      hload hflag hlen (by simpa [len] using hvalid)
  have hdel :
      deleteStorage? bytesStoreConfig
        { contract := bytesStoreContract,
          locals := (∅ : Store).insert "copy" (.bytes copy) }
        evmSolm0 currentRef = .ok evmSolm1 := by
    simpa [evmSolm0, evmSolmLen, evmSolm1, initState, hlen] using
      bytesStoreDeleteCurrentLongPrepared
        (evm := evmSolm0) (copy := copy)
        (header := bytesStoreCurrentLengthHeaderWord σ_evm I) (len := len)
        hload hflag hlen (by simpa [len] using hvalid)
  have hbodyBytes := bytesStoreClearCurrentBodyReturnsBytes
    (evm := evmSolm0) (evm' := evmSolm1) (copy := copy)
    (by simp [evmSolm0, initState]; exact hwv) hread hdel
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0 ∅
        clearCurrentTransition.body
        (.returned
          { contract := bytesStoreContract,
            locals := (∅ : Store).insert "copy" (.bytes copy) }
          evmSolm1 (some (.int len.toNat))) := by
    simpa [hcopySize] using hbodyBytes
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by
      simp [evmSolm1, evmSolmLen, evmSolm0, clearSolidityBytesDataWordsFrom_createdAccounts,
        storageStore_createdAccounts, initState])
    (by
      have hlenStore :
          accountMapEquiv (sstoreAccountMap I.codeOwner σ_evm ⟨0⟩ ⟨0⟩)
            evmSolmLen.accountMap := by
        simpa [evmSolmLen, evmSolm0, initState] using
          accountMapEquiv_storageStore_initState_codeOwner
            (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
            (I := I) (g := Sat256.ofUInt256 g) hAccounts ⟨0⟩ ⟨0⟩
      simpa [evmSolm1, evmSolmLen, evmSolm0, clearSolidityBytesDataWordsFrom_accountMap,
        storageStore_executionEnv, initState, hcountNat,
        StringStoreLite.clearCurrentBaseWord_eq_solidityBytesDataBaseSlot] using
        accountMapEquiv_clearDataWordsForwardFrom I.codeOwner
        (solidityBytesDataBaseSlot ⟨0⟩) ⟨0⟩ ((len.toNat + 31) / 32)
        hlenStore)
    (returnEquiv_of_encode (uint256ReturnEncoding len))

theorem bytesStoreClearCurrentShortDecodedZeroRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hzero : UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
        ⟨127⟩ = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 I.codeOwner ⟨0⟩ ⟨0⟩
  have hsz := bytesStoreClearCurrentSelector_size hsel
  have hd := bytesStoreDispatch_clearCurrent (cd := I.calldata)
    (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_clearCurrent (I := I) hsz
  have hreach := bytesStoreReachClearCurrent (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hret := bytesStoreX_clearCurrentShortZeroValid
    (g := Sat256.ofUInt256 g) hperm hreach hflag hvalid hzero
  have hload :
      Solm.EVM.storageLoad evmSolm0 I.codeOwner ⟨0⟩ =
        bytesStoreCurrentLengthHeaderWord σ_evm I := by
    simpa [evmSolm0, initState] using
      bytesStoreStorageLoadCurrentLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadBytes :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        bytesStoreCurrentLengthHeaderWord σ_evm I := by
    simpa [evmSolm0, initState] using hload
  have hvalidLen :
      UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (⟨0⟩ : UInt256) ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hzero] using hvalid
  obtain ⟨copy, hread, hcopySize⟩ :=
    bytesStoreReadCurrentShortPackedExists (evm := evmSolm0)
      (header := bytesStoreCurrentLengthHeaderWord σ_evm I) (len := ⟨0⟩)
      hloadBytes hflag hzero.symm hvalidLen
  have hpacked : checkBytesPacked ⟨0⟩ evmSolm0 = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hloadBytes hflag
  have hdel :
      deleteStorage? bytesStoreConfig
        { contract := bytesStoreContract,
          locals := (∅ : Store).insert "copy" (.bytes copy) }
        evmSolm0 currentRef = .ok evmSolm1 := by
    simpa [evmSolm0, evmSolm1, initState] using
      bytesStoreDeleteCurrentShortPacked (evm := evmSolm0)
        (header := bytesStoreCurrentLengthHeaderWord σ_evm I) (len := ⟨0⟩) (copy := copy)
        hloadBytes hpacked hflag hzero.symm hvalidLen
  have hbodyBytes := bytesStoreClearCurrentBodyReturnsBytes
    (evm := evmSolm0) (evm' := evmSolm1) (copy := copy)
    (by simp [evmSolm0, initState]; exact hwv) hread hdel
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0 ∅
        clearCurrentTransition.body
        (.returned
          { contract := bytesStoreContract,
            locals := (∅ : Store).insert "copy" (.bytes copy) }
          evmSolm1 (some (.int 0))) := by
    simpa [hcopySize] using hbodyBytes
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts])
    (by
      simpa [evmSolm1, evmSolm0] using
        accountMapEquiv_storageStore_initState_codeOwner
          (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
          (I := I) (g := Sat256.ofUInt256 g) hAccounts (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))
    (returnEquiv_of_encode (uint256ReturnEncoding (⟨0⟩ : UInt256)))

theorem bytesStoreClearCurrentRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩
  · by_cases hvalid : UInt256.sub
        (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩
    · let len :=
        UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩
      by_cases hzero : len = ⟨0⟩
      · exact bytesStoreClearCurrentShortDecodedZeroRuntime hcode hsize hperm hwv hsel
          hAccounts hflag (by simpa [len] using hvalid) (by simpa [len] using hzero)
      · exact bytesStoreClearCurrentShortNonzeroRuntime (len := len)
          hcode hsize hperm hwv hsel hAccounts hflag (by rfl)
          (by simpa [len] using hvalid) hzero
    · have hbad : UInt256.sub
          (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
            ⟨32⟩) = ⟨0⟩ :=
        not_ne_iff.mp hvalid
      exact bytesStoreClearCurrentShortMalformedRuntime hcode hsize hperm hwv hsel
        hAccounts hflag hbad
  · by_cases hvalid : UInt256.sub
        (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠
          ⟨0⟩
    · exact bytesStoreClearCurrentLongValidRuntime hcode hsize hperm hwv hsel
        hAccounts hflag hvalid
    · have hbad : UInt256.sub
          (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) =
            ⟨0⟩ :=
        not_ne_iff.mp hvalid
      exact bytesStoreClearCurrentLongMalformedRuntime hcode hsize hperm hwv hsel
        hAccounts hflag hbad

end BytesStore
