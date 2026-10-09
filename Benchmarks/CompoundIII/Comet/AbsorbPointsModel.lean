import Benchmarks.CompoundIII.Comet.LiquidatorPointsData
import Benchmarks.CompoundIII.Comet.InternalOutcome

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def absorbPointsCounts (p : LiquidatorPointsData) (n : UInt256) : LiquidatorPointsData :=
  { p with absorbs := p.absorbs + ⟨1⟩, absorbed := p.absorbed + n }

def absorbPointsCost (gasUsed fee : UInt256) : UInt256 := UInt256.mul gasUsed fee

def absorbPointsSpend (p : LiquidatorPointsData) (gasUsed fee : UInt256) : LiquidatorPointsData :=
  { p with spend := p.spend + absorbPointsCost gasUsed fee }

def AbsorbPointsSpendValid (p : LiquidatorPointsData) (gasUsed fee : UInt256) : Prop :=
  gasUsed.toNat * fee.toNat < UInt256.size ∧
    (absorbPointsCost gasUsed fee).toNat < 2^128 ∧
    p.spend.toNat + (absorbPointsCost gasUsed fee).toNat < 2^128

def AbsorbPointsValid (p : LiquidatorPointsData) (n gasUsed fee : UInt256) : Prop :=
  (p.absorbs.toNat + 1 < 2^32 ∧ p.absorbed.toNat + n.toNat < 2^64) ∧
    AbsorbPointsSpendValid p gasUsed fee

instance (p : LiquidatorPointsData) (gasUsed fee : UInt256) :
    Decidable (AbsorbPointsSpendValid p gasUsed fee) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance (p : LiquidatorPointsData) (n gasUsed fee : UInt256) :
    Decidable (AbsorbPointsValid p n gasUsed fee) := inferInstanceAs (Decidable ((_ ∧ _) ∧ _))

def absorbPointsLoaded (evm : State) (addr : AccountAddress) : LiquidatorPointsData :=
  liquidatorPointsData (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (liquidatorSlot addr))

def absorbPointsOutcome (evm : State) (addr : AccountAddress) (n gasUsed : UInt256) :
    InternalOutcome :=
  let p := absorbPointsLoaded evm addr
  let fee := UInt256.ofNat evm.executionEnv.header.baseFeePerGas
  if AbsorbPointsValid p n gasUsed fee then
    if evm.executionEnv.perm then
      .ok (storeLiquidatorPoints evm addr (absorbPointsSpend (absorbPointsCounts p n) gasUsed fee))
    else .staticViolation
  else .reverted

def absorbAfterAccountsOutcome (evm : State) (addr : AccountAddress)
    (n startGas endGas : UInt256) : InternalOutcome :=
  if endGas.toNat ≤ startGas.toNat then
    absorbPointsOutcome evm addr n (UInt256.sub startGas endGas)
  else .reverted

end Benchmarks.CompoundIII.Comet
