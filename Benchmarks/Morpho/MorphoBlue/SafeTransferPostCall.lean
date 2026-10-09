import Benchmarks.Morpho.MorphoBlue.SafeTransferPost

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def safeTransferAfterCallPC (isFrom : Bool) : UInt256 :=
  UInt256.ofNat (if isFrom then 15164 else 14859)

theorem safeTransferReturnAlloc_nonzero {n : Nat} (hn : n ≠ 0) :
    safeTransferReturnAlloc n = (n + 63) / 32 * 32 := by
  rw [safeTransferReturnAlloc, if_neg hn]
  omega

theorem morphoTransferPostCall {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {frame : Frame} {evm : EVM.State} {success : Bool}
    (isFrom : Bool) (hstack : R.length + 16 ≤ 1024)
    (hmem : frame.locals.get? "__memory" = some (.int (Int.ofNat ptr.toNat)))
    (hout : frame.locals.get? "returndata" = some (.bytes out))
    (hz : frame.locals.get? "success" = some (.bool success))
    (hb : out.size < 2 ^ 138) (hm : MorphoHeap mem ptr 0)
    (hsize : 128 ≤ mem.size) (hlower : 128 ≤ ptr.toNat)
    (hzero : memLoad (UInt256.ofNat 96) mem = UInt256.ofNat 0)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 (safeTransferAfterCallPC isFrom)
      ((if success then ⟨1⟩ else ⟨0⟩) :: UInt256.ofNat 15005 :: ret :: R)
      mem aw out σ k C) :
    (ExecBlock config frame evm safeTransferTail .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ frame' mem' ptr' aw' k' C',
      ExecBlock config frame evm safeTransferTail (.returned frame' evm
        (some [.int (Int.ofNat (ptr.toNat + safeTransferReturnAlloc out.size + 128))])) ∧
      RD (deployedRuntime v) ee g s0 ret R mem' aw' out σ k' C' ∧
      MorphoHeap mem' ptr' 0 ∧ MemoryPrefix mem mem' ptr.toNat ∧
      ptr'.toNat = ptr.toNat + safeTransferReturnAlloc out.size + 128 := by
  have hstart : ∃ a k C, RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14548)
      (safeTransferStatusPC isFrom :: safeTransferBoolPC isFrom ::
        (if success then ⟨1⟩ else ⟨0⟩) :: UInt256.ofNat 15005 :: ret :: R)
      mem a out σ k C := by
    cases isFrom
    · exact morphoBlocks.morpho_block_14859_packed (immWords := wordsOf (immStore v))
        (by change R.length + 3 + 3 ≤ 1024; omega)
        (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
    · exact morphoBlocks.morpho_block_15164_packed (immWords := wordsOf (immStore v))
        (by change R.length + 3 + 3 ≤ 1024; omega)
        (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨a0, k0, C0, rd0⟩ := hstart
  by_cases hn : out.size = 0
  · obtain ⟨a1, k1, C1, rd1⟩ := morphoReturnDataEmpty hn
      (by change R.length + 4 + 3 ≤ 1024; omega)
      (by cases isFrom <;> rw [morphoPatchedValidJumps v] <;> jump_dest) rd0
    have hv := returnBoolView_empty hn hsize hlower hzero
    have hcursor : ptr.toNat = ptr.toNat + safeTransferReturnAlloc out.size := by
      rw [safeTransferReturnAlloc, if_pos hn, Nat.add_zero]
    rcases morphoTransferPostGuards isFrom hstack hmem hout hz (by omega) hm
        hcursor hv hvalid rd1 with hbad | ⟨frame', a2, k2, C2, hs, rd2, hm2, hp, hc⟩
    · exact Or.inl hbad
    · exact Or.inr ⟨frame', _, _, a2, k2, C2, hs, rd2, hm2, hp, hc⟩
  · by_cases hs : out.size < 2 ^ 64
    · have halloc := safeTransferReturnAlloc_nonzero hn
      by_cases hfit : ptr.toNat + (out.size + 63) / 32 * 32 < 2 ^ 64
      · obtain ⟨a1, k1, C1, rd1⟩ := morphoReturnDataCopy hs hn hm.free
          (by change R.length + 4 + 8 ≤ 1024; omega)
          (by cases isFrom <;> rw [morphoPatchedValidJumps v] <;> jump_dest) hfit rd0
        have hm1 := hm.returnData (spare := 0) hn (by omega) (by exact lt_usize _ (by decide))
        have hv := returnBoolView_allocated hm hn hfit
        have hp := bytesAllocPtr_toNat (ptr := ptr) (size := out.size) (by omega)
        have hcursor : (bytesAllocPtr ptr out.size).toNat = ptr.toNat + safeTransferReturnAlloc out.size := by
          rw [hp, halloc]
        have hpref := bytesAllocMem_prefix_of_gap hm.size (by have hg := hm.gap; omega) hn
        rcases morphoTransferPostGuards isFrom hstack hmem hout hz hs hm1 hcursor hv hvalid rd1
            with hbad | ⟨frame', a2, k2, C2, hsource, rd2, hm2, hp2, hc⟩
        · exact Or.inl hbad
        · exact Or.inr ⟨frame', _, _, a2, k2, C2, hsource, rd2, hm2,
            hpref.trans (hp2.mono (by rw [hp]; omega)), hc⟩
      · refine Or.inl ⟨safeTransferTail_allocationRevert hmem hout hs (by rw [halloc]; omega), ?_⟩
        exact morphoReturnDataOverflow hs hn (by have hh := hm.space; omega) hm.free
          (by change R.length + 4 + 8 ≤ 1024; omega) (by omega) rd0
    · refine Or.inl ⟨safeTransferTail_oversize hout (by omega), ?_⟩
      exact morphoReturnDataOversize (by change _ < 2 ^ 256; omega) (by omega)
        (by change R.length + 4 + 4 ≤ 1024; omega) rd0

end Benchmarks.Morpho.MorphoBlue
