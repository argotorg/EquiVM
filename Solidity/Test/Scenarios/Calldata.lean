import Solidity.Test.Harness
import Solidity.Test.Specs.Calldata
import Solidity.Test.Fixtures.CalldataSolc

/-! # Differential cases: calldata words that are not canonical, `using` on an interface type.

`Copies`: a calldata array or struct parameter keeps its words; solc validates a word when an
element or field is read, when the object is ABI-encoded (`abi.encode`, an external call, an
event, an error), when it is copied to storage and when a struct or an array of dynamic arrays or
structs is copied to memory; an array of value-type words (or of static arrays of them) is copied
to memory with cleanup; the inner headers of `uint8[][]` are checked when the inner array is used
(fixture `Lazy` covers that in depth).  `Attach`: `using Lib for IT` with a call through a value of
the interface type; `retCd`: a calldata-typed return with a word that is not canonical reverts with
empty data.  `Enums`: an enum array copied from calldata to memory keeps an out-of-range word; every
use of the element (read, comparison, conversion, an internal parameter, `abi.encode`,
`abi.encodePacked`, an event, a return, an external argument, a copy to storage) is `Panic(0x21)`,
while the length, a write to the element, `delete` and sharing the copy are not; the same for
`E[2]` and `E[2][]`. -/

namespace Solidity.Test.Calldata

open Solidity.Test Ethereum

def tokRuntime : ByteArray := bytesOfHex Fixtures.tokRuntimeHex
def attachRuntime : ByteArray := bytesOfHex Fixtures.attachRuntimeHex
def copiesRuntime : ByteArray := bytesOfHex Fixtures.copiesRuntimeHex
def enumsRuntime : ByteArray := bytesOfHex Fixtures.enumsRuntimeHex

def M : Nat := 2 ^ 256 - 1
def TOK : Nat := 0x70C
def A (n : Nat) : ABI.ABIValue := .address (addr n)
def arr (xs : List Int) : ABI.ABIValue := .array (xs.map (.int ·))
def words (ws : List Nat) : ByteArray := ws.foldl (fun b w => b ++ wordBytes w) ByteArray.empty

def mk (code : ByteArray) (sig : String) (args : List ABI.ABIValue) (tag : String := "") : Case :=
  { name := s!"{sig} {tag}", code := code, call := some (sig, args) }

/-- A call with the argument words as given (not necessarily canonical). -/
def rawCall (code : ByteArray) (sig : String) (ws : List Nat) (tag : String := "") : Case :=
  { name := s!"{sig} raw {tag}", code := code, calldata := selectorOfSig sig ++ words ws }

/-! ## Attach -/

def mkA (sig : String) (args : List ABI.ABIValue) (tag : String := "") : Case :=
  { mk attachRuntime sig args tag with accounts := [(addr TOK, account (code := tokRuntime))] }

def attachCases : List Case :=
  [ { mkA "viaMember(address)" [A TOK] with expect := .success },
    { mkA "viaLib(address)" [A TOK] with expect := .success },
    { mkA "own(address)" [A TOK] with expect := .success },
    { mkA "viaMember(address)" [A 0xE0A] "no code" with expect := .revert },
    { mkA "num(uint256)" [.int 21] with expect := .success },
    { mkA "num(uint256)" [.int M] "overflow" with expect := .revert } ]

/-! ## Copies -/

def mkC (sig : String) (args : List ABI.ABIValue) (tag : String := "") : Case := mk copiesRuntime sig args tag
def rc (sig : String) (ws : List Nat) (tag : String := "") : Case := rawCall copiesRuntime sig ws tag

/-- A dynamic array of two words, the second one dirty for `uint16`. -/
def dirty16 : List Nat := [0x20, 2, 1, 2 ^ 16]

def copyCases : List Case :=
  [ { rc "pass(uint128[])" [0x20, 2, 1, 2 ^ 128] "dirty" with expect := .success },
    { mkC "pass(uint128[])" [arr [1, 2]] "clean" with expect := .success },
    { rc "enc(uint16[])" dirty16 "dirty" with expect := .revert },
    { mkC "enc(uint16[])" [arr [1, 2]] "clean" with expect := .success },
    { rc "packed(uint16[])" dirty16 "dirty" with expect := .revert },
    { mkC "packed(uint16[])" [arr [1, 2]] "clean" with expect := .success },
    { rc "hashIt(uint16[])" dirty16 "dirty" with expect := .revert },
    { rc "copyLen(uint16[])" dirty16 "dirty" with expect := .success },
    { rc "copyAdd(uint16[])" dirty16 "dirty" with expect := .success },
    { rc "copyAdd(uint16[])" [0x20, 2, 1, 2 ^ 16 + 3] "dirty+3" with expect := .success },
    { mkC "copyAdd(uint16[])" [arr [1, 2 ^ 16 - 1]] "overflow" with expect := .revert },
    { rc "copyEnc(uint16[])" [0x20, 2, 1, 2 ^ 16 + 3] "dirty" with expect := .success },
    { rc "copyEq(uint16[])" dirty16 "dirty" with expect := .success },
    { rc "copyBool(bool[])" [0x20, 2, 1, 2] "two" with expect := .success },
    { rc "copyBool(bool[])" [0x20, 2, 1, 0] "zero" with expect := .success },
    { rc "toStore(uint16[])" dirty16 "dirty" with expect := .revert },
    { mkC "toStore(uint16[])" [arr [1, 2, 3]] "clean" with expect := .success },
    { rc "fwd(uint16[])" dirty16 "dirty" with expect := .revert },
    { mkC "fwd(uint16[])" [arr [1, 2]] "clean" with expect := .success },
    { rc "len(uint16[])" dirty16 "dirty" with expect := .success },
    { rc "first(uint16[])" dirty16 "dirty second" with expect := .success },
    { rc "first(uint16[])" [0x20, 1, 2 ^ 16] "dirty first" with expect := .revert },
    { rc "memLen(uint16[])" dirty16 "dirty" with expect := .revert },
    { mkC "memLen(uint16[])" [arr [1, 2]] "clean" with expect := .success },
    { rc "emitArr(uint16[])" dirty16 "dirty" with expect := .revert },
    { mkC "emitArr(uint16[])" [arr [1, 2]] "clean" with expect := .success },
    { rc "revertArr(uint16[])" dirty16 "dirty" with expect := .revert },
    { mkC "revertArr(uint16[])" [arr [1, 2]] "clean" with expect := .revert },
    { rc "fieldY((uint8,uint256))" [300, 1] "dirty x" with expect := .success },
    { rc "fieldX((uint8,uint256))" [300, 1] "dirty x" with expect := .revert },
    { rc "fieldX((uint8,uint256))" [3, 1] "clean" with expect := .success },
    { rc "structCopy((uint8,uint256))" [300, 1] "dirty" with expect := .revert },
    { rc "structCopy((uint8,uint256))" [3, 1] "clean" with expect := .success },
    { rc "structEnc((uint8,uint256))" [300, 1] "dirty" with expect := .revert },
    { rc "structEnc((uint8,uint256))" [3, 1] "clean" with expect := .success },
    { rc "ssY((uint8,uint256)[],uint256)" [0x40, 0, 1, 300, 1] "dirty x" with expect := .success },
    { rc "ssX((uint8,uint256)[],uint256)" [0x40, 0, 1, 300, 1] "dirty x" with expect := .revert },
    { rc "ssCopy((uint8,uint256)[])" [0x20, 1, 300, 1] "dirty" with expect := .revert },
    { rc "ssCopy((uint8,uint256)[])" [0x20, 1, 3, 1] "clean" with expect := .success },
    { rc "nested(uint8[][],uint256,uint256)" [0x60, 0, 0, 1, 0x20, 1, 300] "dirty read" with expect := .revert },
    { rc "nested(uint8[][],uint256,uint256)" [0x60, 0, 0, 1, 0x20, 2, 3, 300] "dirty not read" with expect := .success },
    { rc "nested(uint8[][],uint256,uint256)" [0x60, 0, 0, 1, 2 ^ 255, 1, 300] "inner offset 2^255" with expect := .revert },
    { rc "nestedCopy(uint8[][])" [0x20, 1, 0x20, 1, 300] "dirty" with expect := .revert },
    { rc "nestedCopy(uint8[][])" [0x20, 1, 0x20, 1, 3] "clean" with expect := .success },
    { rc "nestedCopy(uint8[][])" [0x20, 1, 0x20, 2 ^ 160 + 0xf7e5, 300] "absurd inner length" with expect := .revert },
    { rc "fixedOuter(uint8[2][],uint256)" [0x40, 0, 1, 300, 1] "dirty" with expect := .success },
    { rc "fixedOuterCopy(uint8[2][])" [0x20, 1, 300, 1] "dirty" with expect := .success },
    { rc "fixedOuterCopy(uint8[2][])" [0x20, 1, 3, 1] "clean" with expect := .success },
    { rc "fixedCopy(uint16[2])" [1, 2 ^ 16 + 5] "dirty" with expect := .success },
    { rc "addrAt(address[],uint256)" [0x40, 0, 1, 2 ^ 160] "dirty read" with expect := .revert },
    { rc "addrAt(address[],uint256)" [0x40, 0, 2, 1, 2 ^ 160] "dirty not read" with expect := .success },
    { rc "addrCopy(address[])" [0x20, 1, 2 ^ 160 + 7] "dirty" with expect := .success },
    { rc "bytesAt(bytes4[],uint256)" [0x40, 0, 1, 1] "dirty read" with expect := .revert },
    { rc "bytesAt(bytes4[],uint256)" [0x40, 0, 1, 0xdeadbeef <<< 224] "clean" with expect := .success },
    { rc "bytesCopy(bytes4[])" [0x20, 1, (0xdeadbeef <<< 224) + 1] "dirty" with expect := .success },
    { rc "intAt(int64[],uint256)" [0x40, 0, 1, 2 ^ 63] "dirty read" with expect := .revert },
    { rc "intAt(int64[],uint256)" [0x40, 0, 1, M] "minus one" with expect := .success },
    { rc "intAt(int64[],uint256)" [0x40, 1, 2, 2 ^ 63, 5] "dirty not read" with expect := .success },
    { rc "intCopy(int64[])" [0x20, 1, 2 ^ 63] "dirty" with expect := .success },
    { rc "intCopy(int64[])" [0x20, 1, M] "minus one" with expect := .success },
    { rc "enumAt(uint8[],uint256)" [0x40, 0, 1, 3] "out of range read" with expect := .revert },
    { rc "enumAt(uint8[],uint256)" [0x40, 0, 1, 2] "clean" with expect := .success },
    { rc "enumAt(uint8[],uint256)" [0x40, 0, 2, 2, 7] "out of range not read" with expect := .success },
    { rc "enumCopy(uint8[])" [0x20, 1, 7] "out of range" with expect := .revert },
    { rc "enumCopy(uint8[])" [0x20, 1, 1] "clean" with expect := .success },
    { rc "priceAt(uint128[],uint256)" [0x40, 0, 1, 2 ^ 128] "dirty read" with expect := .revert },
    { rc "priceAt(uint128[],uint256)" [0x40, 0, 2, 1, 2 ^ 128] "dirty not read" with expect := .success },
    { rc "priceCopy(uint128[])" [0x20, 1, 2 ^ 128 + 9] "dirty" with expect := .success },
    { rc "retCd(uint16[])" dirty16 "dirty" with expect := .revert },
    { mk copiesRuntime "retCd(uint16[])" [arr [1, 2]] "clean" with expect := .success } ]

/-! ## Enums -/

/-- A call of `Enums` with the argument words as given (`7` and `0x100` are out of range). -/
def rn (sig : String) (ws : List Nat) (tag : String) (e : Expect) : Case :=
  { rawCall enumsRuntime sig ws tag with expect := e }

def enumCases : List Case :=
  [ rn "copyRead(uint8[],uint256)" [0x40, 0, 1, 7] "bad read" .revert,
    rn "copyRead(uint8[],uint256)" [0x40, 0, 1, 0x100] "bad read 0x100" .revert,
    rn "copyRead(uint8[],uint256)" [0x40, 0, 1, 2] "clean" .success,
    rn "copyRead(uint8[],uint256)" [0x40, 1, 2, 7, 1] "bad not read" .success,
    rn "copyLen(uint8[])" [0x20, 1, 7] "bad" .success,
    rn "copyLen(uint8[])" [0x20, 1, 0x100] "bad 0x100" .success,
    rn "copyEnc(uint8[])" [0x20, 1, 7] "bad" .revert,
    rn "copyEnc(uint8[])" [0x20, 2, 1, 2] "clean" .success,
    rn "copyPacked(uint8[])" [0x20, 1, 7] "bad" .revert,
    rn "copyPacked(uint8[])" [0x20, 1, 1] "clean" .success,
    rn "copyEmit(uint8[])" [0x20, 1, 7] "bad" .revert,
    rn "copyEmit(uint8[])" [0x20, 1, 1] "clean" .success,
    rn "copyRet(uint8[])" [0x20, 1, 7] "bad" .revert,
    rn "copyRet(uint8[])" [0x20, 1, 1] "clean" .success,
    rn "copyExt(uint8[])" [0x20, 1, 7] "bad" .revert,
    rn "copyExt(uint8[])" [0x20, 1, 1] "clean" .success,
    rn "copyStore(uint8[])" [0x20, 1, 7] "bad" .revert,
    rn "copyStore(uint8[])" [0x20, 1, 1] "clean" .success,
    rn "copyStoreRead(uint8[],uint256)" [0x40, 0, 1, 7] "bad" .revert,
    rn "copyStoreRead(uint8[],uint256)" [0x40, 1, 2, 1, 2] "clean" .success,
    rn "copyWriteRead(uint8[])" [0x20, 1, 7] "bad overwritten" .success,
    rn "copyWriteRead(uint8[])" [0x20, 1, 0x100] "bad 0x100 overwritten" .success,
    rn "copyDelete(uint8[])" [0x20, 1, 7] "bad deleted" .success,
    rn "copyInner(uint8[],uint256)" [0x40, 0, 1, 7] "bad" .revert,
    rn "copyInner(uint8[],uint256)" [0x40, 0, 1, 1] "clean" .success,
    rn "copyCmp(uint8[])" [0x20, 1, 7] "bad" .revert,
    rn "copyCmp(uint8[])" [0x20, 1, 0] "clean" .success,
    rn "copyConv(uint8[])" [0x20, 1, 7] "bad" .revert,
    rn "copyConv(uint8[])" [0x20, 1, 2] "clean" .success,
    rn "copyShare(uint8[])" [0x20, 1, 7] "bad shared" .success,
    rn "copyShare(uint8[])" [0x20, 1, 2] "clean" .success,
    rn "copyStatic(uint8[2],uint256)" [1, 7, 1] "bad read" .revert,
    rn "copyStatic(uint8[2],uint256)" [1, 0x100, 1] "bad read 0x100" .revert,
    rn "copyStatic(uint8[2],uint256)" [1, 7, 0] "bad not read" .success,
    rn "copyStaticNoRead(uint8[2])" [1, 7] "bad" .success,
    rn "copyNested(uint8[2][],uint256,uint256)" [0x60, 0, 1, 1, 1, 7] "bad read" .revert,
    rn "copyNested(uint8[2][],uint256,uint256)" [0x60, 0, 0, 1, 1, 7] "bad not read" .success,
    rn "copyNestedLen(uint8[2][])" [0x20, 1, 1, 7] "bad" .success,
    rn "cdEnc(uint8[])" [0x20, 1, 7] "bad" .revert,
    rn "cdStore(uint8[])" [0x20, 1, 7] "bad" .revert,
    rn "cdStore(uint8[])" [0x20, 1, 1] "clean" .success,
    rn "cdRead(uint8[],uint256)" [0x40, 0, 1, 7] "bad" .revert ]

def P := _root_.Calldata.SoliditySpec.program

def scenarios : List Scenario :=
  [ { name := "Attach", program := P, target := "Attach", cases := attachCases },
    { name := "Copies", program := P, target := "Copies", cases := copyCases },
    { name := "Enums", program := P, target := "Enums", cases := enumCases } ]

end Solidity.Test.Calldata
