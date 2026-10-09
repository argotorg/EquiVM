import Benchmarks.Morpho.MorphoBlue.SafeTransferFunctionLower

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

inductive SafeTransferFunctionRefines (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (isFrom : Bool) (token sender recipient : AccountAddress) (value : UInt256) (imms : Store)
    (evm : EVM.State) (mem : ByteArray) (ptr ret : UInt256) (R : List UInt256) : Prop where
  | reverted : ExecFuncBody config (safeTransferStart isFrom token sender recipient value ptr.toNat imms)
      evm (safeTransferFunctionFor isFrom).body .reverted → RDrev (deployedRuntime v) g s0 →
      SafeTransferFunctionRefines v ee g s0 isFrom token sender recipient value imms evm mem ptr ret R
  | ok {frame' evm' σ' mem' ptr' aw' rdata' k' C'} :
      ExecFuncBody config (safeTransferStart isFrom token sender recipient value ptr.toNat imms)
        evm (safeTransferFunctionFor isFrom).body (.returned frame' evm' (some [.int (Int.ofNat ptr'.toNat)])) →
      SourceState s0 ee σ' evm' → MorphoHeap mem' ptr' 0 → MemoryPrefix mem mem' ptr.toNat →
      128 ≤ mem'.size → 128 ≤ ptr'.toNat → memLoad (UInt256.ofNat 96) mem' = UInt256.ofNat 0 →
      RD (deployedRuntime v) ee g s0 ret R mem' aw' rdata' σ' k' C' →
      SafeTransferFunctionRefines v ee g s0 isFrom token sender recipient value imms evm mem ptr ret R

theorem morphoSafeTransferFunctionRefine {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem out : ByteArray} {aw ptr value ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (isFrom : Bool) (token sender recipient : AccountAddress) (imms : Store)
    (hstack : R.length + 21 ≤ 1024) (hs : SourceState s0 ee σ evm) (hm : MorphoHeap mem ptr 0)
    (hsize : 128 ≤ mem.size) (hlower : 128 ≤ ptr.toNat)
    (hzero : memLoad (UInt256.ofNat 96) mem = UInt256.ofNat 0)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 (safeTransferEntryPC isFrom)
      (safeTransferEVMArgs isFrom token sender recipient value ++ ret :: R) mem aw out σ k C) :
    SafeTransferFunctionRefines v ee g s0 isFrom token sender recipient value imms evm mem ptr ret R := by
  cases morphoSafeTransferFunctionRefineAt (v := v) isFrom token sender recipient imms
    hstack hs hm hsize hlower 128 hlower hzero hvalid h with
  | reverted hb hr => exact .reverted hb hr
  | ok hb hs' hm' hp hsiz hl hz rd => exact .ok hb hs' hm' hp hsiz hl hz rd

end Benchmarks.Morpho.MorphoBlue
