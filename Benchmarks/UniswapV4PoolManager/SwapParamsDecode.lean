import Benchmarks.UniswapV4PoolManager.SwapParams
import Benchmarks.UniswapV4PoolManager.SignedBytesDecode
import Benchmarks.UniswapV4PoolManager.BoolWordDecode
import Benchmarks.UniswapV4PoolManager.ScalarTupleDecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000
attribute [local irreducible] EVM.signed

def swapParamsOfCalldata (cd : ByteArray) : SwapParamsWords :=
  ⟨decide (calldataWord cd 164 ≠ ⟨0⟩), calldataWord cd 196, calldataWord cd 228⟩
def SwapParamsBounds (cd : ByteArray) : Prop :=
  (calldataWord cd 164 = ⟨0⟩ ∨ calldataWord cd 164 = ⟨1⟩) ∧ (calldataWord cd 228).toNat < 2^160
instance (cd : ByteArray) : Decidable (SwapParamsBounds cd) := inferInstanceAs (Decidable (_ ∧ _))

theorem decodeSwapParamsWords {bytes : List UInt8} {direction amount price : UInt256}
    (h0 : readWord? bytes 160 = some direction)
    (h1 : readWord? bytes 192 = some amount)
    (h2 : readWord? bytes 224 = some price) :
    decodeABIValue? abiSwapParams bytes 160 =
      if (direction = ⟨0⟩ ∨ direction = ⟨1⟩) ∧ price.toNat < 2^160 then
        some (.tuple (swapParamsValues ⟨decide (direction ≠ ⟨0⟩), amount, price⟩), 256) else none := by
  rw [abiSwapParams, decodeABIValue?, show abiTupleHeadSize? swapParamsTypes = some 96 by native_decide]
  simp only [bind, Option.bind]
  rw [decodeScalarTupleAt (by rfl : swapParamsTypes.all isABIScalarWordType = true) (by rfl)]
  simp only [swapParamsTypes, decodeScalarWords?, decodeScalarWord?, h0, h1, h2,
    bind, Option.bind, decodeBoolWord, decodeABIWord_signed256, decodeUnsignedWord, EVM.twoPow]
  by_cases hz : direction = ⟨0⟩ ∨ direction = ⟨1⟩ <;> by_cases hp : price.toNat < 2^160 <;>
    simp only [hz, hp, if_true, if_false, bind, Option.bind, true_and, false_and, and_false, swapParamsValues]

theorem decodeSwapParams {cd : ByteArray} (hlen : 260 ≤ cd.size) :
    decodeABIValue? abiSwapParams (cd.toList.drop 4) 160 =
      if SwapParamsBounds cd then some (.tuple (swapParamsValues (swapParamsOfCalldata cd)), 256) else none := by
  have ht := decodeSwapParamsWords (direction := calldataWord cd 164)
    (amount := calldataWord cd 196) (price := calldataWord cd 228)
    (readWord_drop4 (off := 160) (by omega : 4+160+32 ≤ cd.size))
    (readWord_drop4 (off := 192) (by omega : 4+192+32 ≤ cd.size))
    (readWord_drop4 (off := 224) (by omega : 4+224+32 ≤ cd.size))
  simpa only [SwapParamsBounds, swapParamsOfCalldata] using ht

end Benchmarks.UniswapV4PoolManager
