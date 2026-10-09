import Benchmarks.Morpho.MorphoBlue.ScalarSliceABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000


-- LIBRARY CANDIDATE: decode a bytes32 field of a bounded byte-array slice as an EVM word.
theorem decodeBytes32_extract {cd : ByteArray} {start stop off : Nat}
    (hs : start + off + 32 ≤ stop) (he : stop ≤ cd.size) :
    decodeABIValue? abiBytes32 (cd.extract start stop).toList off =
      some (wordBytes32Value (calldataWord cd (start + off)), off + 32) := by
  have hslice : (((cd.extract start stop).toList.drop off).take 32) =
      (cd.toList.drop (start + off)).take 32 := by
    rw [extract_toList, List.drop_take, List.drop_drop, List.take_take]
    rw [Nat.min_eq_left (by omega)]
  have hl : (((cd.extract start stop).toList.drop off).take 32).length = 32 := by
    rw [hslice, List.length_take, List.length_drop, byteArray_toList_eq, Array.length_toList]
    change min 32 (cd.size - (start + off)) = 32
    omega
  rw [decodeABIValue_bytes32_ok hl, ← toBytesBE_bytesToWord_of_length hl,
    hslice, decode_word_at_eq_any cd (start + off) (by omega)]

end Benchmarks.Morpho.MorphoBlue
