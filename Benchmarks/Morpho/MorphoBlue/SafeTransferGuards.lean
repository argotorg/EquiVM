import Benchmarks.Morpho.MorphoBlue.SafeTransferMessages

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoTransferGuardOk {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr status ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (isFrom decoded : Bool) (hstack : R.length + 11 ≤ 1024)
    (hfree : memLoad (UInt256.ofNat 64) mem = ptr) (hfit : ptr.toNat + 64 < 2 ^ 64)
    (hstatus : status ≠ UInt256.ofNat 0)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 11507)
      (ptr :: safeTransferMessagePC isFrom decoded :: status :: ptr :: ret :: R)
      mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret R
      (safeTransferMessageMem isFrom decoded mem) aw' out σ k' C' := by
  obtain ⟨a, k, C, rd⟩ := morphoTransferMessage isFrom decoded
    (by change R.length + 1 + 7 ≤ 1024; omega) hfree hfit h
  obtain ⟨k1, C1, rd1⟩ := morphoRequireTrue (by omega) hvalid (isZero_eq_zero_of_ne hstatus) rd
  exact ⟨a, k1, C1, rd1⟩

theorem morphoTransferGuardRevert {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr status ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (isFrom decoded : Bool) (hstack : R.length + 11 ≤ 1024)
    (hm : MorphoHeap mem ptr 0) (hbad : 2 ^ 64 ≤ ptr.toNat + 64 ∨ status = UInt256.ofNat 0)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 11507)
      (ptr :: safeTransferMessagePC isFrom decoded :: status :: ptr :: ret :: R)
      mem aw out σ k C) : RDrev (deployedRuntime v) g s0 := by
  by_cases hf : ptr.toNat + 64 < 2 ^ 64
  · have hz := hbad.resolve_left (by omega)
    obtain ⟨a, k, C, rd⟩ := morphoTransferMessage isFrom decoded
      (by change R.length + 1 + 7 ≤ 1024; omega) hm.free hf h
    rw [hz] at rd
    exact morphoTransferRequireFalse isFrom decoded hstack hm rd
  · exact morphoAlloc64Overflow (by change R.length + 4 + 4 ≤ 1024; omega)
      (by have hh := hm.space; omega) (by omega) h

end Benchmarks.Morpho.MorphoBlue
