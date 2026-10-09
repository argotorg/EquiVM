import Benchmarks.CompoundIII.Comet.AbiRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

-- GENERALIZES cometValidateAddress_ok by exposing the exact charge used by a gas-bounded loop.
theorem cometValidateAddress_cost {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {w ret : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024) (hcanon : w.toNat < EVM.addressModulus)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨1393⟩ (w :: ret :: R) mem aw rdata σ k C) :
    RD (deployedRuntime v) ee g s0 ret R mem aw rdata σ (k + 12) (C + 46) := by
  have hcond : UInt256.sub (UInt256.land w
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1))) w = UInt256.ofNat 0 := by
    change UInt256.sub (UInt256.land w solcAddrMask) w = ⟨0⟩
    rw [solcAddrMask_clean hcanon, u256_sub_self]
  have r1 := cometWithExtendedAssetList_block_1393_fallthrough
    (immWords := wordsOf (immStore v)) (by simpa using hstack) hcond h
  have r2 := cometWithExtendedAssetList_block_1409
    (immWords := wordsOf (immStore v)) (by omega) hvalid r1
  simpa only [Nat.add_assoc] using r2

end Benchmarks.CompoundIII.Comet
