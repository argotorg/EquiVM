import Benchmarks.CompoundIII.Comet.WithdrawBaseTotalsModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

theorem sourceState_totalsPrincipalRead {s0 ee σ evm} (hs : SourceState s0 ee σ evm)
    (borrow : Bool) :
    totalsPrincipalWord (solcSlotWordAt (UInt256.ofNat 1) σ ee) borrow =
      withdrawBaseTotal evm borrow := by
  have hr : solcSlotWordAt (UInt256.ofNat 1) σ ee =
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ := by
    simpa only [hs.env] using (hs.storageRead ⟨1⟩).symm
  rw [hr]
  rfl

theorem sourceState_supplyPrincipalRead {s0 ee σ evm} (hs : SourceState s0 ee σ evm) :
    UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 104)) (UInt256.ofNat 1))
      (solcSlotWordAt (UInt256.ofNat 1) σ ee) = withdrawBaseTotal evm false := by
  rw [u256_land_comm]
  exact (totalsPrincipalWord_eq _ false).symm.trans (sourceState_totalsPrincipalRead hs false)

theorem sourceState_borrowPrincipalRead {s0 ee σ evm} (hs : SourceState s0 ee σ evm) :
    UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 104)) (UInt256.ofNat 1))
      (UInt256.shiftRight (solcSlotWordAt (UInt256.ofNat 1) σ ee) (UInt256.ofNat 104)) =
        withdrawBaseTotal evm true := by
  rw [u256_land_comm]
  exact (totalsPrincipalWord_eq _ true).symm.trans (sourceState_totalsPrincipalRead hs true)

end Benchmarks.CompoundIII.Comet
