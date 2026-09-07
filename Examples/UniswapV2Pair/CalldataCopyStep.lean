import Examples.UniswapV2Pair.MemorySteps
import Reasoning.Solc
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

-- GENERALIZES Reasoning.Reach.RD.calldatacopy: derive memory, active words, and gas cost.
theorem RD.calldatacopyAny
    {code : ByteArray} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc offset source len aw : UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {R : List UInt256} {k C : Nat}
    (rd : RD code I g s0 pc (offset :: source :: len :: R) mem aw rdata acc k C)
    (hdec : decode code pc = some (.CALLDATACOPY, .none)) (hov : R.length ≤ 1024) :
    RD code I g s0 (pc + ⟨1⟩) R (I.calldata.write source.toNat mem offset.toNat len.toNat)
      (UInt256.ofNat (MachineState.M aw.toNat offset.toNat len.toNat)) rdata acc (k + 1)
      (C + (Cₘ (UInt256.ofNat (MachineState.M aw.toNat offset.toNat len.toNat)) - Cₘ aw +
        (GasConstants.Gverylow + GasConstants.Gcopy * ((len.toNat + 31) / 32)))) := by
  exact RD.calldatacopy _ _ _ rd hdec (fun s haw hstk ↦ by
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
      List.getElem!_cons_zero, List.getElem!_cons_succ]) rfl rfl hov


end UniswapV2Pair
