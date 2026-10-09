import Benchmarks.Safe.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def moduleArgs (target : EVM.Address) (value : UInt256) (payload : ByteArray)
    (operation : UInt256) : Store :=
  ((((∅ : Store).insert "to" (.address target)).insert
    "value" (.int (Int.ofNat value.toNat))).insert "data" (.bytes payload)).insert
      "operation" (.int (Int.ofNat operation.toNat))

def moduleFrame (target : EVM.Address) (value : UInt256) (payload : ByteArray)
    (operation : UInt256) : Frame :=
  { contract := contract, locals := moduleArgs target value payload operation }

end Benchmarks.Safe
