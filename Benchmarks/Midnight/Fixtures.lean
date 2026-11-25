import Stele.DiffTest.Harness

open Stele Stele.DiffTest

namespace Benchmarks.Midnight

def callbackSuccess : Nat :=
  0x7f87788ea698181ea4d28d1576d0ba4fc92c0dbe5bf75b43692af2ce91dbaea2

def midnightCallees : List (EVM.Address × ByteArray) :=
  standardCallees ++
    [(EVM.address 0x6000, callee (wordBytes callbackSuccess)),
     (EVM.address 0x6001, callee (wordBytes (10 ^ 36)))]

end Benchmarks.Midnight
