import Benchmarks.CompoundIII.Comet.AbsorbCalldata
import Benchmarks.CompoundIII.Comet.AbsorbInternalModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def absorbArrayBase (cd : ByteArray) : UInt256 := calldataWord cd 36 + UInt256.ofNat 36

def absorbArrayAccountWord (cd : ByteArray) (i : Nat) : UInt256 :=
  calldataWord cd (absorbArrayOffset cd + 36 + 32 * i)

def absorbArrayAccount (cd : ByteArray) (i : Nat) : AccountAddress :=
  AccountAddress.ofNat (absorbArrayAccountWord cd i).toNat

inductive AbsorbAccountsTrace (v : CometWithExtendedAssetListImmutables) (cd : ByteArray) :
    Nat → State → InternalOutcome → Prop where
  | exhausted {i evm} (hi : absorbArrayLength cd ≤ i) :
      AbsorbAccountsTrace v cd i evm (.ok evm)
  | dirty {i evm} (hi : i < absorbArrayLength cd)
      (hc : ¬ (absorbArrayAccountWord cd i).toNat < EVM.addressModulus) :
      AbsorbAccountsTrace v cd i evm .reverted
  | reverted {i evm} (hi : i < absorbArrayLength cd)
      (hc : (absorbArrayAccountWord cd i).toNat < EVM.addressModulus)
      (ht : AbsorbInternalTrace v (absorbArrayAccount cd i) evm .reverted) :
      AbsorbAccountsTrace v cd i evm .reverted
  | staticViolation {i evm} (hi : i < absorbArrayLength cd)
      (hc : (absorbArrayAccountWord cd i).toNat < EVM.addressModulus)
      (ht : AbsorbInternalTrace v (absorbArrayAccount cd i) evm .staticViolation) :
      AbsorbAccountsTrace v cd i evm .staticViolation
  | next {i evm evm' result} (hi : i < absorbArrayLength cd)
      (hc : (absorbArrayAccountWord cd i).toNat < EVM.addressModulus)
      (ht : AbsorbInternalTrace v (absorbArrayAccount cd i) evm (.ok evm'))
      (htail : AbsorbAccountsTrace v cd (i + 1) evm' result) :
      AbsorbAccountsTrace v cd i evm result

end Benchmarks.CompoundIII.Comet
