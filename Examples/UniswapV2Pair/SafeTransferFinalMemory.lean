import Examples.UniswapV2Pair.SafeTransferDynamicCallCases
import Examples.UniswapV2Pair.SafeTransferReturnCases
import Examples.UniswapV2Pair.SafeTransferFinalMemoryCore
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem safeTransferDynamicFinalMemory_invariants {base : ByteArray} (aw ptr toWord value : UInt256) (out : ByteArray)
    (hin : 128 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size)
    (hptrLo : 128 ≤ ptr.toNat) (hbase : base.size ≤ ptr.toNat + 132)
    (haw : aw.toNat * 32 < UInt256.size) (hfit : ptr.toNat + out.size + 355 < UInt256.size)
    (hzero : base.readWithPadding 96 32 = (⟨0⟩ : UInt256).toByteArray) :
    ∃ next : UInt256,
      128 ≤ (safeTransferDynamicFinalMem base ptr toWord value out).size ∧
      next.toNat - (safeTransferDynamicFinalMem base ptr toWord value out).size < USize.size ∧
      128 ≤ next.toNat ∧ (safeTransferDynamicFinalMem base ptr toWord value out).size ≤ next.toNat + 132 ∧
      next.toNat ≤ ptr.toNat + out.size + 227 ∧
      (safeTransferDynamicFinalWords aw ptr out).toNat * 32 < UInt256.size ∧
      128 ≤ (safeTransferDynamicFinalWords aw ptr out).toNat * 32 ∧
      (safeTransferDynamicFinalMem base ptr toWord value out).readWithPadding 64 32 = next.toByteArray ∧
      (safeTransferDynamicFinalMem base ptr toWord value out).readWithPadding 96 32 = (⟨0⟩ : UInt256).toByteArray := by
  exact safeTransferDynamicFinalMemory_invariants_of_zeroSlot aw ptr toWord value out
    (by omega) hgap hptrLo hbase haw hfit
    ((safeTransferDynamicCallMem2_read96 ptr toWord value hin hgap hptrLo (by omega)).trans hzero)

set_option maxHeartbeats 1000000 in
theorem safeTransferRuntimeFinalMemory_invariants {base : ByteArray} (toWord value : UInt256) (out : ByteArray)
    (hbase : base.size = 164) (hzero : base.readWithPadding 96 32 = (⟨0⟩ : UInt256).toByteArray)
    (hout : out.size < 2 ^ 255) :
    ∃ ptr : UInt256,
      128 ≤ (safeTransferRuntimeFinalMem base toWord value out).size ∧
      ptr.toNat - (safeTransferRuntimeFinalMem base toWord value out).size < USize.size ∧
      128 ≤ ptr.toNat ∧ (safeTransferRuntimeFinalMem base toWord value out).size ≤ ptr.toNat + 132 ∧
      ptr.toNat ≤ 2 ^ 255 + 1024 ∧
      (safeTransferRuntimeFinalActiveWords out).toNat * 32 < UInt256.size ∧
      128 ≤ (safeTransferRuntimeFinalActiveWords out).toNat * 32 ∧
      (safeTransferRuntimeFinalMem base toWord value out).readWithPadding 64 32 = ptr.toByteArray ∧
      (safeTransferRuntimeFinalMem base toWord value out).readWithPadding 96 32 = (⟨0⟩ : UInt256).toByteArray := by
  have hnum : 2 ^ 255 + 1024 < UInt256.size := by native_decide
  obtain ⟨ptr, hm, hgap, hlo, hs, hcap, haw, hawLo, h64, h96⟩ :=
    safeTransferDynamicFinalMemory_invariants (base := base) (UInt256.ofNat 6) ⟨128⟩ toWord value out
      (by omega) (by change 128 - base.size < _; rw [hbase]; exact lt_usize 0 (by omega))
      (by decide) (by change base.size ≤ 128 + 132; omega) (by native_decide)
      (by change 128 + out.size + 355 < _; omega) hzero
  have hmem : safeTransferDynamicFinalMem base ⟨128⟩ toWord value out = safeTransferRuntimeFinalMem base toWord value out := by
    unfold safeTransferDynamicFinalMem safeTransferRuntimeFinalMem
    rw [safeTransferDynamicCallMem2_default]
    rfl
  have hwords : safeTransferDynamicFinalWords (UInt256.ofNat 6) ⟨128⟩ out = safeTransferRuntimeFinalActiveWords out := by
    unfold safeTransferDynamicFinalWords safeTransferRuntimeFinalActiveWords
    have hd : safeTransferDynamicCallWords2 (UInt256.ofNat 6) ⟨128⟩ = UInt256.ofNat 13 := safeTransferDynamicCallWords2_default
    rw [hd]
    rfl
  rw [hmem] at hm hgap hs h64 h96
  rw [hwords] at haw hawLo
  refine ⟨ptr, hm, hgap, hlo, hs, ?_, haw, hawLo, h64, h96⟩
  change ptr.toNat ≤ 128 + out.size + 227 at hcap
  omega

end UniswapV2Pair
