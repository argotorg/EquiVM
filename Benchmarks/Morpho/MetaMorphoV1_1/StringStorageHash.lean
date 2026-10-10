import Benchmarks.Morpho.MetaMorphoV1_1.StringStorageSource

/-! The two constant hashes shared by metadata reads and writes. -/

open Solm Ethereum

namespace Benchmarks.Morpho.MetaMorphoV1_1

def stringStorageHash (symbol : Bool) : UInt256 :=
  if symbol then
    UInt256.ofNat 67072331549493647622825787457569556318728415786901242217649037894484240406165
  else
    UInt256.ofNat 80167465652159884487584418398737133515478493586045375474096367959472086682926

theorem stringStorageHash_eq (symbol : Bool) :
    stringStorageHash symbol = solidityBytesDataBaseSlot (stringViewSlot symbol) := by
  cases symbol <;> native_decide

end Benchmarks.Morpho.MetaMorphoV1_1
