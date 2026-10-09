import Benchmarks.Morpho.MorphoBlue.SafeTransferGuards
import Benchmarks.Morpho.MorphoBlue.SafeTransferBoolRoute
import Benchmarks.Morpho.MorphoBlue.SafeTransferSourceTail
import Benchmarks.Morpho.MorphoBlue.ReturnBoolView

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def safeTransferPostMem (isFrom : Bool) (mem : ByteArray) : ByteArray :=
  safeTransferMessageMem isFrom true (safeTransferMessageMem isFrom false mem)

theorem safeTransferBoolStatus_accept {out : ByteArray} (hb : out.size < 2 ^ 64)
    (hv : out.size = 0 ∨ BoolReturnValid out) (hz : safeTransferBoolStatus out ≠ UInt256.ofNat 0) :
    out.size = 0 ∨ ABI.decodeReturnValueWithMode? config.abiDecodeMode abiBool out = some (.bool true) := by
  by_cases hn : out.size = 0
  · exact Or.inl hn
  · right
    change ABI.decodeReturnValue? abiBool out = some (.bool true)
    have hz : calldataWord out 0 ≠ ⟨0⟩ := by
      simpa only [safeTransferBoolStatus, if_neg hn] using hz
    rw [decodeReturnBool_valid (hv.resolve_left hn) (by omega), decide_eq_true hz]

theorem safeTransferBoolStatus_reject {out : ByteArray} (hb : out.size < 2 ^ 64)
    (hv : out.size = 0 ∨ BoolReturnValid out) (hz : safeTransferBoolStatus out = UInt256.ofNat 0) :
    out.size ≠ 0 ∧ ABI.decodeReturnValueWithMode? config.abiDecodeMode abiBool out = some (.bool false) := by
  have hn : out.size ≠ 0 := by
    intro hn
    rw [safeTransferBoolStatus, if_pos hn] at hz
    contradiction
  refine ⟨hn, ?_⟩
  change ABI.decodeReturnValue? abiBool out = some (.bool false)
  have hz : calldataWord out 0 = UInt256.ofNat 0 := by
    simpa only [safeTransferBoolStatus, if_neg hn] using hz
  rw [decodeReturnBool_long (hv.resolve_left hn).1 (by omega), hz]
  decide

theorem morphoTransferPostGuards {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr data ret : UInt256} {σ : AccountMap}
    {k C n : Nat} {R : List UInt256} {frame : Frame} {evm : EVM.State} {success : Bool}
    (isFrom : Bool) (hstack : R.length + 16 ≤ 1024)
    (hmem : frame.locals.get? "__memory" = some (.int (Int.ofNat n)))
    (hout : frame.locals.get? "returndata" = some (.bytes out))
    (hz : frame.locals.get? "success" = some (.bool success))
    (hb : out.size < 2 ^ 64) (hm : MorphoHeap mem ptr 0)
    (hcursor : ptr.toNat = n + safeTransferReturnAlloc out.size)
    (hv : ReturnBoolView mem data out ptr.toNat)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 (safeTransferStatusPC isFrom)
      (data :: safeTransferBoolPC isFrom :: (if success then ⟨1⟩ else ⟨0⟩) ::
        UInt256.ofNat 15005 :: ret :: R) mem aw out σ k C) :
    (ExecBlock config frame evm safeTransferTail .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ frame' aw' k' C',
      ExecBlock config frame evm safeTransferTail (.returned frame' evm
        (some [.int (Int.ofNat (n + safeTransferReturnAlloc out.size + 128))])) ∧
      RD (deployedRuntime v) ee g s0 ret R (safeTransferPostMem isFrom mem) aw' out σ k' C' ∧
      MorphoHeap (safeTransferPostMem isFrom mem) (ptr + UInt256.ofNat 64 + UInt256.ofNat 64) 0 ∧
      MemoryPrefix mem (safeTransferPostMem isFrom mem) ptr.toNat ∧
      (ptr + UInt256.ofNat 64 + UInt256.ofNat 64).toNat =
        n + safeTransferReturnAlloc out.size + 128 := by
  obtain ⟨a0, k0, C0, rd0⟩ := morphoTransferStatusPrepare isFrom
    (by change R.length + 2 + 7 ≤ 1024; omega) h
  rw [hm.free] at rd0
  by_cases hfit : ptr.toNat + 64 < 2 ^ 64
  · cases success
    · refine Or.inl ⟨safeTransferTail_callFailure hmem hout hz, ?_⟩
      exact morphoTransferGuardRevert isFrom false
        (by change R.length + 3 + 11 ≤ 1024; omega) hm (Or.inr rfl) rd0
    · obtain ⟨a1, k1, C1, rd1⟩ := morphoTransferGuardOk isFrom false
        (by change R.length + 3 + 11 ≤ 1024; omega) hm.free hfit (by decide)
        (by cases isFrom <;> rw [morphoPatchedValidJumps v] <;> jump_dest) rd0
      let mem1 := safeTransferMessageMem isFrom false mem
      let ptr1 := ptr + UInt256.ofNat 64
      have hptr1 : ptr1.toNat = ptr.toNat + 64 :=
        uadd_word_ofNat_toNat ptr 64 (by change _ < 2 ^ 256; omega)
      have hm1 : MorphoHeap mem1 ptr1 0 := hm.errorMessage _ _ hfit
      have hp1 : MemoryPrefix mem mem1 ptr.toNat := morphoErrorMem_prefix _ _ hm.size hm.free
        (by have hg := hm.gap; omega) (by change _ < 2 ^ 256; omega)
      have hv1 := hv.preserve hp1
      by_cases hgood : out.size = 0 ∨ BoolReturnValid out
      · obtain ⟨b0, b1, a2, k2, C2, rd2⟩ := morphoTransferBoolRouteOk isFrom hb hgood
          hv1.header hv1.word (by change R.length + 2 + 6 ≤ 1024; omega) rd1
        obtain ⟨a3, k3, C3, rd3⟩ := morphoTransferResultPrepare isFrom
          (by change R.length + 2 + 5 ≤ 1024; omega) rd2
        change RD _ _ _ _ _
          (memLoad (UInt256.ofNat 64) mem1 :: safeTransferMessagePC isFrom true ::
            safeTransferBoolStatus out :: memLoad (UInt256.ofNat 64) mem1 ::
            UInt256.ofNat 15005 :: ret :: R) mem1 _ _ _ _ _ at rd3
        rw [hm1.free] at rd3
        by_cases hfit1 : ptr1.toNat + 64 < 2 ^ 64
        · by_cases hzero : safeTransferBoolStatus out = UInt256.ofNat 0
          · have hbad := safeTransferBoolStatus_reject hb hgood hzero
            refine Or.inl ⟨safeTransferTail_decodeFailure hmem hout hz hbad.1 (Or.inr hbad.2), ?_⟩
            exact morphoTransferGuardRevert isFrom true
              (by change R.length + 1 + 11 ≤ 1024; omega) hm1 (Or.inr hzero) rd3
          · obtain ⟨a4, k4, C4, rd4⟩ := morphoTransferGuardOk isFrom true
              (by change R.length + 1 + 11 ≤ 1024; omega) hm1.free hfit1 hzero
              (by rw [morphoPatchedValidJumps v]; jump_dest) rd3
            obtain ⟨a5, k5, C5, rd5⟩ := morphoBlocks.morpho_block_15005_packed
              (immWords := wordsOf (immStore v)) (by omega) hvalid rd4
            obtain ⟨frame', hsource⟩ := safeTransferTail_success hmem hout hz hb
              (by omega) (safeTransferBoolStatus_accept hb hgood hzero)
            have hm2 := hm1.errorMessage (safeTransferErrorLength isFrom true)
              (safeTransferErrorPayload isFrom true) hfit1
            have hp2 := morphoErrorMem_prefix (safeTransferErrorLength isFrom true)
              (safeTransferErrorPayload isFrom true) hm1.size hm1.free
              (by have hg := hm1.gap; omega) (by change _ < 2 ^ 256; omega)
            have hptr2 := uadd_word_ofNat_toNat ptr1 64 (by change _ < 2 ^ 256; omega)
            exact Or.inr ⟨frame', a5, k5, C5, hsource, rd5, hm2,
              hp1.trans (hp2.mono (by omega)), by rw [hptr2, hptr1, hcursor]⟩
        · refine Or.inl ⟨safeTransferTail_allocationRevert hmem hout hb (by omega), ?_⟩
          exact morphoTransferGuardRevert isFrom true
            (by change R.length + 1 + 11 ≤ 1024; omega) hm1 (Or.inl (by omega)) rd3
      · have hn : out.size ≠ 0 := fun hn => hgood (Or.inl hn)
        have hbad : ¬ BoolReturnValid out := fun hv => hgood (Or.inr hv)
        obtain ⟨hd, hrev⟩ := morphoTransferBoolRouteRevert isFrom hb hn hbad
          hv1.header hv1.word (by change R.length + 2 + 6 ≤ 1024; omega) rd1
        exact Or.inl ⟨safeTransferTail_decodeFailure hmem hout hz hn (Or.inl hd), hrev⟩
  · refine Or.inl ⟨safeTransferTail_allocationRevert hmem hout hb (by omega), ?_⟩
    exact morphoTransferGuardRevert isFrom false
      (by change R.length + 3 + 11 ≤ 1024; omega) hm (Or.inl (by omega)) rd0

end Benchmarks.Morpho.MorphoBlue
