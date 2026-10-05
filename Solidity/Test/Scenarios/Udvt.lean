import Solidity.Test.Harness
import Solidity.Test.Specs.Udvt
import Solidity.Test.Fixtures.UdvtSolc

/-! # Differential cases: user-defined value types.

`Udvt`: wrap / unwrap, storage (packing, mapping keys, arrays, structs), getters, an event and an
error.  `UdvtAbi`: `abi.encode*`, `abi.decode`, arrays through the ABI.  `UdvtCall`: an external call
with value-type arguments.  `UDer`: types declared in a base contract and in a library.  `UdvtImm`:
immutables and a constant.  `UdvtUsing`: functions attached with `using`.  The `/boundaries`
scenarios run boundary values and calldata that is not canonical; they are not fuzzed.

`UdvtArr/arrays`: array elements that are not canonical: a calldata array is validated when an
element is read, a memory array when the call is decoded; plain `bool` arrays behave as the value
types over `bool`.  `UdvtOps`: the solc source binds operators (`using {psum as +} …`); the spec
writes the bound calls, which is what solc compiles the operators to, left operand first. -/

namespace Solidity.Test.Udvt

open Solidity.Test Ethereum

def udvtRuntime : ByteArray := bytesOfHex Fixtures.udvtRuntimeHex
def udvtCreation : ByteArray := bytesOfHex Fixtures.udvtCreationHex
def abiRuntime : ByteArray := bytesOfHex Fixtures.udvtAbiRuntimeHex
def oracleRuntime : ByteArray := bytesOfHex Fixtures.oracleRuntimeHex
def callRuntime : ByteArray := bytesOfHex Fixtures.udvtCallRuntimeHex
def derRuntime : ByteArray := bytesOfHex Fixtures.uDerRuntimeHex
def immRuntime : ByteArray := bytesOfHex Fixtures.udvtImmRuntimeHex
def immCreation : ByteArray := bytesOfHex Fixtures.udvtImmCreationHex
def usingRuntime : ByteArray := bytesOfHex Fixtures.udvtUsingRuntimeHex

def MAX : Nat := 2 ^ 256 - 1
def M128 : Int := 2 ^ 128 - 1
def A (n : Nat) : ABI.ABIValue := .address (addr n)

/-- `bytesN` with `N = k + 1`: the low `N` bytes of `n`. -/
def fb (k : Fin 32) (n : Nat) : ABI.ABIValue := .fixedBytes k ((wordBytes n).toList.drop (31 - k.val))
def tag (n : Nat) : ABI.ABIValue := fb ⟨3, by decide⟩ n
def arr (xs : List Int) : ABI.ABIValue := .array (xs.map (.int ·))

def tU (n : Nat) (h : 0 < n ∧ n ≤ 256 ∧ n % 8 = 0 := by decide) : ABI.ABIType := .elem (.int (.uint ⟨n, h⟩))
def tI (n : Nat) (h : 0 < n ∧ n ≤ 256 ∧ n % 8 = 0 := by decide) : ABI.ABIType := .elem (.int (.sint ⟨n, h⟩))
def encOf (tys : List ABI.ABIType) (vs : List ABI.ABIValue) : ByteArray :=
  ((ABI.encodeABIValues? tys vs).map fun bs => (⟨bs.toArray⟩ : ByteArray)).getD .empty
def words (ws : List Nat) : ByteArray := ws.foldl (fun b w => b ++ wordBytes w) ByteArray.empty

def mk (code : ByteArray) (sig : String) (args : List ABI.ABIValue) (tag : String := "") : Case :=
  { name := s!"{sig} {tag}", code := code, call := some (sig, args) }

/-- A call with the argument words as given (not necessarily canonical). -/
def rawCall (code : ByteArray) (sig : String) (ws : List Nat) (tag : String := "") : Case :=
  { name := s!"{sig} raw {tag}", code := code, calldata := selectorOfSig sig ++ words ws }

/-! ## Udvt -/

def r (base : String) (v : Nat) : Solm.EvaledStorageRef × Nat := (⟨base, []⟩, v)
def tagKey (n : Nat) : Solm.KeyValue := .fixedBytes ⟨3, by decide⟩ ((wordBytes n).toList.drop 28)

/-- `price = 9`, `delta = -4`, `flag = true`, `who = 0xB0B`, `tag = 0x11223344`, `wide = 2^200`. -/
def scalars : List (Solm.EvaledStorageRef × Nat) :=
  [r "price" 9, r "delta" (2 ^ 64 - 4), r "flag" 1, r "who" 0xB0B, r "tag" 0x11223344, r "wide" (2 ^ 200)]

/-- `prices = [11, 22, 33]`. -/
def priceList : List (Solm.EvaledStorageRef × Nat) :=
  [(⟨"prices", [.length]⟩, 3), (⟨"prices", [.aindex (.int 0)]⟩, 11), (⟨"prices", [.aindex (.int 1)]⟩, 22),
   (⟨"prices", [.aindex (.int 2)]⟩, 33)]

def quoteOf (bid ask : Nat) : List (Solm.EvaledStorageRef × Nat) :=
  [(⟨"quote", [.field "bid"]⟩, bid), (⟨"quote", [.field "ask"]⟩, ask), (⟨"quote", [.field "maker"]⟩, 0xB0B),
   (⟨"quote", [.field "live"]⟩, 1)]

def mkU (sig : String) (args : List ABI.ABIValue) (tag : String := "") : Case := mk udvtRuntime sig args tag

def cases : List Case :=
  [ { mkU "setSome(uint128,int64,bool)" [.int 5, .int (-3), .bool true] with expect := .success },
    { mkU "setSome(uint128,int64,bool)" [.int 0, .int 0, .bool false] "over" with refs := scalars, expect := .success },
    { mkU "setRest(address,bytes4,uint256)" [A 0xB0B, tag 0xdeadbeef, .int 77] with refs := scalars, expect := .success },
    { mkU "wrap3(uint128,int64,bool)" [.int 9, .int (-9), .bool true] with expect := .success },
    { mkU "wrap2(address,bytes4)" [A 0xB0B, tag 0x01020304] with expect := .success },
    { mkU "unwrap3(uint128,int64,bool)" [.int 9, .int (-9), .bool true] with expect := .success },
    { mkU "unwrap2(address,bytes4)" [A 0xB0B, tag 0x01020304] with expect := .success },
    { mkU "widen(uint8,int8)" [.int 200, .int (-100)] with expect := .success },
    { mkU "lits()" [] with expect := .success },
    { mkU "sum(uint128,uint128)" [.int 3, .int 4] with expect := .success },
    { mkU "sum(uint128,uint128)" [.int M128, .int 1] "overflow" with expect := .revert },
    { mkU "capped(uint128)" [.int 10] with expect := .success },
    { mkU "capped(uint128)" [.int 11] "too high" with expect := .revert },
    { mkU "put(uint128,uint256)" [.int 5, .int 99] with expect := .success },
    { mkU "byPrice(uint128)" [.int 5] with refs := [(⟨"byPrice", [.mindex (.int 5)]⟩, 42)], expect := .success },
    { mkU "mark(address,bytes4,bool)" [A 0xB0B, tag 0xaabbccdd, .bool true] with expect := .success },
    { mkU "marks(address,bytes4)" [A 0xB0B, tag 0xaabbccdd] with
        refs := [(⟨"marks", [.mindex (.address (addr 0xB0B)), .mindex (tagKey 0xaabbccdd)]⟩, 1)], expect := .success },
    { mkU "push(uint128)" [.int 7] with expect := .success },
    { mkU "pop()" [] "empty" with expect := .revert },
    { mkU "prices(uint256)" [.int 0] "empty" with expect := .revert },
    { mkU "setQuote(uint128,uint128,address)" [.int 3, .int 10, A 0xF00D] with expect := .success },
    { mkU "spread()" [] with refs := quoteOf 3 10, expect := .success },
    { mkU "spread()" [] "underflow" with refs := quoteOf 10 3, expect := .revert },
    { mkU "quote()" [] with refs := quoteOf 3 10, expect := .success },
    { mkU "clear()" [] with refs := quoteOf 3 10, expect := .success },
    { mkU "pick(bool,uint128,uint128)" [.bool true, .int 1, .int 2] with expect := .success },
    { mkU "pick(bool,uint128,uint128)" [.bool false, .int 1, .int 2] "second" with expect := .success },
    { mkU "same(uint128)" [.int 6] with expect := .success },
    { mkU "zeros()" [] with expect := .success },
    { mkU "locals(uint128)" [.int 8] with expect := .success },
    { mkU "shadow(uint128)" [.int 4] with expect := .success },
    { mkU "fileK()" [] with expect := .success } ] ++
  (["price()", "delta()", "flag()", "who()", "tag()", "wide()"].map fun g =>
    { mkU g [] with refs := scalars, expect := .success }) ++
  [ { name := "constructor", code := udvtCreation, ctorArgs := some ([], udvtRuntime), expect := .success } ]

/-- Cases on a seeded `prices` array.  Not fuzzed: the interpreter clears an array element by
    element, and the fuzz run was killed for lack of memory when the stored length was mutated. -/
def arrayStore : List Case :=
  [ { mkU "push(uint128)" [.int 44] "fourth" with refs := priceList, expect := .success },
    { mkU "pop()" [] with refs := priceList, expect := .success },
    { mkU "prices(uint256)" [.int 1] with refs := priceList, expect := .success },
    { mkU "prices(uint256)" [.int 3] "out of range" with refs := priceList, expect := .revert },
    { mkU "clear()" [] "with prices" with refs := quoteOf 3 10 ++ priceList, expect := .success } ]

def boundaries : List Case :=
  arrayStore ++
  -- words that are not canonical for the underlying type
  [ { rawCall udvtRuntime "setSome(uint128,int64,bool)" [2 ^ 128, 0, 0] "dirty uint128" with expect := .revert },
    { rawCall udvtRuntime "setSome(uint128,int64,bool)" [1, 2 ^ 63, 0] "int64 not sign-extended" with expect := .revert },
    { rawCall udvtRuntime "setSome(uint128,int64,bool)" [1, MAX, 1] "int64 -1" with expect := .success },
    { rawCall udvtRuntime "setSome(uint128,int64,bool)" [1, MAX - 2 ^ 63 + 1, 1] "int64 min" with expect := .success },
    { rawCall udvtRuntime "setSome(uint128,int64,bool)" [1, 0, 2] "bool 2" with expect := .revert },
    { rawCall udvtRuntime "unwrap2(address,bytes4)" [2 ^ 160, 0xdeadbeef <<< 224] "dirty address" with expect := .revert },
    { rawCall udvtRuntime "unwrap2(address,bytes4)" [0xB0B, (0xdeadbeef <<< 224) + 1] "dirty bytes4" with expect := .revert },
    { rawCall udvtRuntime "unwrap2(address,bytes4)" [0xB0B, 0xdeadbeef <<< 224] "clean" with expect := .success },
    { rawCall udvtRuntime "byPrice(uint128)" [2 ^ 128 + 5] "dirty key" with expect := .revert },
    { rawCall udvtRuntime "wrap3(uint128,int64,bool)" [MAX, 0, 0] "dirty uint128" with expect := .revert },
    { rawCall udvtRuntime "same(uint128)" [] "short" with expect := .revert } ] ++
  ([(0 : Int), 1, 2 ^ 127, M128].flatMap fun a => [(0 : Int), 1, 2 ^ 127, M128].map fun b =>
    mkU "sum(uint128,uint128)" [.int a, .int b] s!"{a} {b}") ++
  ([(0 : Int), 9, 10, 11, M128].map fun a => mkU "capped(uint128)" [.int a] s!"{a}") ++
  ([(0 : Int), 1, 255].flatMap fun a => [(-128 : Int), -1, 0, 127].map fun b =>
    mkU "widen(uint8,int8)" [.int a, .int b] s!"{a} {b}") ++
  ([(0 : Int), 1, M128].flatMap fun a => [(-(2 ^ 63) : Int), -1, 0, 2 ^ 63 - 1].flatMap fun d =>
    [mkU "wrap3(uint128,int64,bool)" [.int a, .int d, .bool true] s!"{a} {d}",
     mkU "unwrap3(uint128,int64,bool)" [.int a, .int d, .bool false] s!"{a} {d}",
     { mkU "setSome(uint128,int64,bool)" [.int a, .int d, .bool true] s!"{a} {d}" with refs := scalars }]) ++
  ([(0 : Int), 1, 2, 3, 4].map fun i => { mkU "prices(uint256)" [.int i] s!"{i}" with refs := priceList }) ++
  ([(0, 0), (0, 1), (5, 5), (2 ^ 128 - 1, 0), (0, 2 ^ 128 - 1)].map fun (b, a) =>
    { mkU "spread()" [] s!"{b} {a}" with refs := quoteOf b a }) ++
  [ { mkU "pop()" [] "one" with refs := [(⟨"prices", [.length]⟩, 1), (⟨"prices", [.aindex (.int 0)]⟩, 2 ^ 128 - 1)] },
    mkU "clear()" [] "empty", mkU "quote()" [] "empty",
    mkU "setRest(address,bytes4,uint256)" [A 0, tag 0, .int 0] "zeros",
    { mkU "setRest(address,bytes4,uint256)" [A (2 ^ 160 - 1), tag 0xffffffff, .int (2 ^ 256 - 1)] "max" with refs := scalars },
    mkU "put(uint128,uint256)" [.int M128, .int (2 ^ 256 - 1)] "max",
    mkU "mark(address,bytes4,bool)" [A 0, tag 0, .bool false] "zeros" ]

/-! ## UdvtAbi -/

def mkA (sig : String) (args : List ABI.ABIValue) (tag : String := "") : Case := mk abiRuntime sig args tag

def triple (p d : Int) (f : Nat) : ByteArray := words [(p % 2 ^ 256).toNat, (d % 2 ^ 256).toNat, f]

def abiCases : List Case :=
  [ { mkA "enc(uint128,bytes4,bool)" [.int 5, tag 0xdeadbeef, .bool true] with expect := .success },
    { mkA "dec(bytes)" [.bytes (triple 5 (-2) 1)] with expect := .success },
    { mkA "sumArr(uint128[])" [arr [3, 4, 5]] with expect := .success },
    { mkA "flagAt(bool[],uint256)" [.array [.bool true, .bool false, .bool true], .int 2] with expect := .success },
    { mkA "fixedArr(uint128[2])" [arr [7, 8]] with expect := .success },
    { mkA "mem(uint128,uint128)" [.int 1, .int 2] with expect := .success },
    { mkA "hash(uint128,address)" [.int 5, A 0xB0B] with expect := .success },
    { mkA "sel()" [] with expect := .success } ]

def abiBoundaries : List Case :=
  [ { mkA "dec(bytes)" [.bytes (triple 5 (-2) 2)] "bool 2" with expect := .revert },
    { mkA "dec(bytes)" [.bytes (triple (2 ^ 128) 0 0)] "dirty uint128" with expect := .revert },
    { mkA "dec(bytes)" [.bytes (triple 0 (2 ^ 63) 0)] "int64 not sign-extended" with expect := .revert },
    { mkA "dec(bytes)" [.bytes (words [1, 2])] "short" with expect := .revert },
    { mkA "dec(bytes)" [.bytes (triple M128 (-(2 ^ 63)) 1)] "extremes" with expect := .success },
    { mkA "dec(bytes)" [.bytes (triple 1 1 1 ++ words [9])] "long" with expect := .success },
    -- a `bool` word that is not canonical: checked when the element is read (calldata), when the
    -- array is copied (memory)
    { rawCall abiRuntime "flagAt(bool[],uint256)" [0x40, 0, 3, 1, 2, 0] "dirty, not read" with expect := .success },
    { rawCall abiRuntime "flagAt(bool[],uint256)" [0x40, 1, 3, 1, 2, 0] "dirty, read" with expect := .revert },
    { rawCall abiRuntime "flagAt(bool[],uint256)" [0x40, 3, 3, 1, 0, 1] "out of range" with expect := .revert },
    { rawCall abiRuntime "sumArr(uint128[])" [0x20, 2, 1, 2 ^ 128] "dirty element" with expect := .revert },
    { rawCall abiRuntime "fixedArr(uint128[2])" [1, 2 ^ 128] "dirty element" with expect := .revert },
    { mkA "sumArr(uint128[])" [arr []] "empty" with expect := .success },
    { mkA "sumArr(uint128[])" [arr [M128, M128, M128]] "large" with expect := .success },
    { mkA "enc(uint128,bytes4,bool)" [.int M128, tag 0xffffffff, .bool false] "max" with expect := .success },
    { mkA "enc(uint128,bytes4,bool)" [.int 0, tag 0, .bool false] "zeros" with expect := .success },
    { mkA "mem(uint128,uint128)" [.int M128, .int 0] "max" with expect := .success },
    { mkA "hash(uint128,address)" [.int M128, A (2 ^ 160 - 1)] "max" with expect := .success },
    { mkA "flagAt(bool[],uint256)" [.array [], .int 0] "empty" with expect := .revert } ]

def arrRuntime : ByteArray := bytesOfHex Fixtures.udvtArrRuntimeHex
def mkR (sig : String) (args : List ABI.ABIValue) (tag : String := "") : Case := mk arrRuntime sig args tag

/-- Arrays whose elements are read one at a time. -/
def arrayCases : List Case :=
  [ { mkR "flagMem(bool[],uint256)" [.array [.bool true, .bool false, .bool true], .int 1] with expect := .success },
    { mkR "flagFixed(bool[2],uint256)" [.array [.bool true, .bool false], .int 1] with expect := .success },
    { mkR "priceAt(uint128[],uint256)" [arr [3, 4, 5], .int 1] with expect := .success },
    { mkR "boolMem(bool[],uint256)" [.array [.bool true, .bool false], .int 0] with expect := .success },
    { mkR "boolFixed(bool[2],uint256)" [.array [.bool true, .bool false], .int 0] with expect := .success },
    { rawCall arrRuntime "flagMem(bool[],uint256)" [0x40, 2, 3, 1, 0, 1] "clean" with expect := .success },
    { rawCall arrRuntime "flagMem(bool[],uint256)" [0x40, 1, 3, 1, 2, 0] "dirty, read" with expect := .revert },
    { rawCall arrRuntime "flagMem(bool[],uint256)" [0x40, 0, 3, 1, 2, 0] "dirty, not read" with expect := .revert },
    { rawCall arrRuntime "boolMem(bool[],uint256)" [0x40, 1, 3, 1, 2, 0] "dirty, read" with expect := .revert },
    { rawCall arrRuntime "boolMem(bool[],uint256)" [0x40, 0, 3, 1, 2, 0] "dirty, not read" with expect := .revert },
    { rawCall arrRuntime "priceAt(uint128[],uint256)" [0x40, 1, 2, 7, 2 ^ 128] "dirty, read" with expect := .revert },
    { rawCall arrRuntime "priceAt(uint128[],uint256)" [0x40, 2, 2, 7, 8] "out of range" with expect := .revert },
    { rawCall arrRuntime "priceAt(uint128[],uint256)" [0x40, 0, 2, 7, 2 ^ 128] "dirty, not read" with expect := .success },
    { rawCall arrRuntime "boolFixed(bool[2],uint256)" [1, 2, 1] "dirty, read" with expect := .revert },
    { rawCall arrRuntime "boolFixed(bool[2],uint256)" [1, 0, 2] "out of range" with expect := .revert },
    { rawCall arrRuntime "boolFixed(bool[2],uint256)" [1, 2, 0] "dirty, not read" with expect := .success },
    { rawCall arrRuntime "flagFixed(bool[2],uint256)" [1, 2, 1] "dirty, read" with expect := .revert },
    { rawCall arrRuntime "flagFixed(bool[2],uint256)" [1, 2, 0] "dirty, not read" with expect := .success } ]

/-! ## UdvtCall -/

def ORACLE : Nat := 0x0AC1E
def feed (n : Nat) : ABI.ABIValue := fb ⟨7, by decide⟩ n
def mkC (sig : String) (args : List ABI.ABIValue) (tag : String := "") : Case :=
  { mk callRuntime sig args tag with accounts := [(addr ORACLE, account (code := oracleRuntime))] }

def callCases : List Case :=
  [ { mkC "ask(address,bytes8,uint128)" [A ORACLE, feed 0x0102030405060708, .int 5] with expect := .success },
    { mkC "feed(bytes8)" [feed 0xa1a2a3a4a5a6a7a8] with expect := .success },
    { mkC "unfeed(bytes8)" [feed 0xa1a2a3a4a5a6a7a8] with expect := .success } ]

def callBoundaries : List Case :=
  [ { mkC "ask(address,bytes8,uint128)" [A ORACLE, feed (2 ^ 64 - 1), .int M128] "overflow in the callee" with expect := .revert },
    { mkC "ask(address,bytes8,uint128)" [A ORACLE, feed 0, .int 0] "zeros" with expect := .success },
    { mkC "ask(address,bytes8,uint128)" [A 0xE0A, feed 1, .int 1] "no code" with expect := .revert },
    { rawCall callRuntime "unfeed(bytes8)" [1] "dirty bytes8" with expect := .revert },
    { rawCall callRuntime "ask(address,bytes8,uint128)" [ORACLE, 1 <<< 192, 2 ^ 128] "dirty uint128" with
        accounts := [(addr ORACLE, account (code := oracleRuntime))], expect := .revert } ]

/-! ## UDer -/

def mkD (sig : String) (args : List ABI.ABIValue) (tag : String := "") : Case := mk derRuntime sig args tag
def b32 (n : Nat) : ABI.ABIValue := fb ⟨31, by decide⟩ n

def derCases : List Case :=
  [ { mkD "ids(uint32)" [.int 7] with expect := .success },
    { mkD "keep(bytes32)" [b32 (2 ^ 255 + 9)] with expect := .success },
    { mkD "delay(uint32,uint32)" [.int 3, .int 4] with expect := .success },
    { mkD "plain(uint32,bytes32,uint112)" [.int 1, b32 2, .int 3] with expect := .success },
    { mkD "again(uint32,uint112)" [.int 7, .int 9] with expect := .success },
    { mkD "slot()" [] with refs := [r "slot" (2 ^ 200 + 1), r "last" 5], expect := .success } ]

def derBoundaries : List Case :=
  [ { mkD "ids(uint32)" [.int (2 ^ 32 - 1)] "overflow" with expect := .revert },
    { mkD "ids(uint32)" [.int 0] "zero" with refs := [r "last" 9], expect := .success },
    { mkD "delay(uint32,uint32)" [.int (2 ^ 32 - 1), .int (2 ^ 32 - 1)] "max" with expect := .success },
    { mkD "delay(uint32,uint32)" [.int 0, .int 0] "zeros" with expect := .success },
    { mkD "plain(uint32,bytes32,uint112)" [.int (2 ^ 32 - 1), b32 MAX, .int (2 ^ 112 - 1)] "max" with expect := .success },
    { rawCall derRuntime "plain(uint32,bytes32,uint112)" [2 ^ 32, 0, 0] "dirty uint32" with expect := .revert },
    { rawCall derRuntime "plain(uint32,bytes32,uint112)" [0, 0, 2 ^ 112] "dirty uint112" with expect := .revert } ]

/-! ## UdvtImm -/

/-- solc's `immutableReferences` of the runtime: `base`, `owner`. -/
def baseOffsets : List Nat := [141, 221]
def ownerOffsets : List Nat := [174]

def patch (rt : ByteArray) (offs : List Nat) (v : Nat) : ByteArray :=
  offs.foldl (fun b off => (wordBytes v).copySlice 0 b off 32) rt

def immWith (base owner : Nat) : ByteArray := patch (patch immRuntime baseOffsets base) ownerOffsets owner

def price (n : Nat) : Value := .wrapped (some "") "Price" (.uint ⟨128, by decide⟩ n)
def whoV (n : Nat) : Value := .wrapped (some "") "Who" (.address (addr n))

def immCases : List Case :=
  [ { mk (immWith 5 0xA11CE) "get()" [] with expect := .success },
    { mk (immWith 5 0xA11CE) "above(uint128)" [.int 6] with expect := .success },
    { mk (immWith 5 0xA11CE) "above(uint128)" [.int 5] "equal" with expect := .success },
    { name := "constructor", code := immCreation, ctorArgs := some ([.int 5], immWith 5 0xA11CE), expect := .success },
    { name := "constructor max", code := immCreation, sender := addr 0xB0B,
      ctorArgs := some ([.int M128], immWith (2 ^ 128 - 1) 0xB0B), expect := .success } ]

/-! ## UdvtUsing -/

def mkG (sig : String) (args : List ABI.ABIValue) (tag : String := "") : Case := mk usingRuntime sig args tag

def usingCases : List Case :=
  [ { mkG "bump(uint128)" [.int 5] with expect := .success },
    { mkG "addTo(uint128,uint128)" [.int 5, .int 6] with expect := .success },
    { mkG "named(uint128)" [.int 5] with expect := .success },
    { mkG "dbl(uint128)" [.int 5] with expect := .success },
    { mkG "sq(uint128)" [.int 12] with expect := .success },
    { mkG "halves(uint128,uint128)" [.int 100, .int 7] with expect := .success },
    { mkG "viaOwn(uint128)" [.int 9] with expect := .success },
    { mkG "flipIt(bool)" [.bool true] with expect := .success },
    { mkG "delay(uint32,uint32)" [.int 3, .int 4] with expect := .success },
    { mkG "tw(uint256)" [.int 21] with expect := .success },
    { mkG "free2(uint128)" [.int 5] with expect := .success },
    { mkG "store(uint128)" [.int 5] with expect := .success },
    { mkG "p()" [] with refs := [r "p" 77], expect := .success } ]

def usingBoundaries : List Case :=
  [ { mkG "bump(uint128)" [.int M128] "overflow" with expect := .revert },
    { mkG "addTo(uint128,uint128)" [.int M128, .int 0] "overflow in pinc" with expect := .revert },
    { mkG "addTo(uint128,uint128)" [.int 1, .int M128] "overflow in padd" with expect := .revert },
    { mkG "named(uint128)" [.int (M128 - 2)] "overflow" with expect := .revert },
    { mkG "named(uint128)" [.int (M128 - 3)] "max" with expect := .success },
    { mkG "dbl(uint128)" [.int (2 ^ 127)] "overflow" with expect := .revert },
    { mkG "dbl(uint128)" [.int (2 ^ 127 - 1)] "overflow in pinc" with expect := .success },
    { mkG "sq(uint128)" [.int (2 ^ 64)] "overflow" with expect := .revert },
    { mkG "sq(uint128)" [.int (2 ^ 64 - 1)] "max" with expect := .success },
    { mkG "halves(uint128,uint128)" [.int 100, .int 0] "division by zero" with expect := .revert },
    { mkG "halves(uint128,uint128)" [.int M128, .int M128] "max" with expect := .success },
    { mkG "viaOwn(uint128)" [.int 0] "zero" with expect := .success },
    { mkG "flipIt(bool)" [.bool false] "false" with expect := .success },
    { mkG "delay(uint32,uint32)" [.int 4, .int 3] "shorter" with expect := .success },
    { mkG "delay(uint32,uint32)" [.int (2 ^ 32 - 1), .int 0] "max" with expect := .success },
    { mkG "tw(uint256)" [.int (2 ^ 255)] "overflow" with expect := .revert },
    { mkG "free2(uint128)" [.int (M128 - 1)] "overflow" with expect := .revert },
    { mkG "store(uint128)" [.int (M128 - 1)] "overflow in the second" with expect := .revert },
    { mkG "store(uint128)" [.int 0] "zero" with refs := [r "p" 77], expect := .success },
    { rawCall usingRuntime "flipIt(bool)" [2] "bool 2" with expect := .revert } ]

/-! ## UdvtOps -/

def opsRuntime : ByteArray := bytesOfHex Fixtures.udvtOpsRuntimeHex

/-- solc calls the bound function with the left operand first; the spec's calls do the same
    (`ord` records 12, `bothFail` reverts with the left operand's message). -/
def opsCases : List Case :=
  [ { mk opsRuntime "ord()" [] with expect := .success },
    { mk opsRuntime "ordEq()" [] with expect := .success },
    { mk opsRuntime "bothFail()" [] with expect := .revert },
    { mk opsRuntime "inv(uint128)" [.int 5] with expect := .success },
    { mk opsRuntime "inv(uint128)" [.int 0] "zero" with expect := .success },
    { mk opsRuntime "both(uint128,uint128)" [.int 3, .int 4] with expect := .success },
    { mk opsRuntime "both(uint128,uint128)" [.int M128, .int 1] "overflow" with expect := .revert },
    { mk opsRuntime "trace()" [] with expect := .success } ]

def P := _root_.Udvt.SoliditySpec.program

def scenarios : List Scenario :=
  [ { name := "Udvt", program := P, target := "Udvt", cases := cases },
    { name := "Udvt/boundaries", program := P, target := "Udvt", cases := boundaries },
    { name := "UdvtAbi", program := P, target := "UdvtAbi", cases := abiCases },
    { name := "UdvtAbi/boundaries", program := P, target := "UdvtAbi", cases := abiBoundaries },
    { name := "UdvtArr/arrays", program := P, target := "UdvtArr", cases := arrayCases },
    { name := "UdvtCall", program := P, target := "UdvtCall", cases := callCases },
    { name := "UdvtCall/boundaries", program := P, target := "UdvtCall", cases := callBoundaries },
    { name := "UDer", program := P, target := "UDer", cases := derCases },
    { name := "UDer/boundaries", program := P, target := "UDer", cases := derBoundaries },
    { name := "UdvtImm", program := P, target := "UdvtImm", cases := immCases,
      immutables := [("base", price 5), ("owner", whoV 0xA11CE)] },
    { name := "UdvtUsing", program := P, target := "UdvtUsing", cases := usingCases },
    { name := "UdvtUsing/boundaries", program := P, target := "UdvtUsing", cases := usingBoundaries },
    { name := "UdvtOps", program := P, target := "UdvtOps", cases := opsCases } ]

end Solidity.Test.Udvt
