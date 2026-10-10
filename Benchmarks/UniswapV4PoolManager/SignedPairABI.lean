import Benchmarks.UniswapV4PoolManager.IntWordABI
import Benchmarks.UniswapV4PoolManager.SignedWordBounds
import Benchmarks.UniswapV4PoolManager.WordArrayMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: encoding a pair of signed 256-bit return words.
theorem signedPairReturnEncoding (a b : UInt256) :
    encodeReturnValues? [.elem (.int (.sint ⟨256, by decide⟩)), .elem (.int (.sint ⟨256, by decide⟩))]
      [.int (EVM.signed a), .int (EVM.signed b)] = some (wordBytes [a, b]) := by
  have ha := encodeSignedWord ⟨256, by decide⟩ a (signedWord_fits a)
  have hb := encodeSignedWord ⟨256, by decide⟩ b (signedWord_fits b)
  rw [encodeReturnValues?, encodeABIValues?, show abiTupleHeadSize?
    [.elem (.int (.sint ⟨256, by decide⟩)), .elem (.int (.sint ⟨256, by decide⟩))] = some 64 by native_decide]
  simp only [bind, Option.bind, encodeABIValuesFrom?, ha, hb, isDynamicABIType,
    Bool.false_eq_true, if_false, List.nil_append, List.append_nil, wordBytes,
    toByteArray_eq_toBytesBE]
  apply congrArg some
  apply ByteArray.ext
  simp only [ByteArray.data_append, ByteArray.data_empty, Array.append_empty, List.append_toArray]

end Benchmarks.UniswapV4PoolManager
