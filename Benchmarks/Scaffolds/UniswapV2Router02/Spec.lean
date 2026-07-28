import Solm.Semantics
import Solm.SolidityLayout
import Benchmarks.Scaffolds.UniswapV2Router02.Immutables

/-!
# Uniswap V2 Router02 benchmark spec

Source-shaped Solm benchmark scaffold for upstream `UniswapV2Router02` at Solidity `=0.6.6`.
The contract has no storage; its persistent constructor data are the immutable `factory` and `WETH`
addresses, modeled in `Immutables.lean` and returned by the public getters here.

Events and revert strings are omitted, as in the other benchmark specs.  The external ABI table
contains the exact selectors used for typed external calls and for TransferHelper's raw calls.
-/

open Solm ABI
open Benchmarks.UniswapV2Router02.Immutables

namespace Benchmarks.UniswapV2Router02

/-! ## Types -/

def uint8Int : IntType := .uint ⟨8, by decide⟩
def uint32Int : IntType := .uint ⟨32, by decide⟩
def uint112Int : IntType := .uint ⟨112, by decide⟩
def uint256Int : IntType := .uint ⟨256, by decide⟩

def bytes1Width : Fin 32 := ⟨0, by decide⟩
def bytes32Width : Fin 32 := ⟨31, by decide⟩

def uint8 : ABIType := .elem (.int uint8Int)
def uint32 : ABIType := .elem (.int uint32Int)
def uint112 : ABIType := .elem (.int uint112Int)
def uint256 : ABIType := .elem (.int uint256Int)
def addr : ABIType := .elem .address
def boolTy : ABIType := .elem .bool
def bytesTy : ABIType := .bytes
def bytes1 : ABIType := .elem (.bytes bytes1Width)
def bytes32 : ABIType := .elem (.bytes bytes32Width)
def addrArray : ABIType := .dynamicArray addr
def uintArray : ABIType := .dynamicArray uint256

def uint256St : StorageType := .elem (.int uint256Int)
def addrSt : StorageType := .elem .address

def zeroAddr : Expr := .cast (.intLit 0) addrSt
def sender : Expr := .env .caller
def thisAddr : Expr := .env .this
def maxUint256 : Int := (2 : Int) ^ 256 - 1

def u256 (e : Expr) : Expr := .inRange uint256Int e
def add256 (x y : Expr) : Expr := u256 (.binary .add x y)
def sub256 (x y : Expr) : Expr := u256 (.binary .sub x y)
def mul256 (x y : Expr) : Expr := u256 (.binary .mul x y)

def localRef (name : Ident) : StorageRef := { base := name }
def localIndex (name : Ident) (idx : Expr) : StorageRef :=
  { base := name, steps := [.aindex idx] }

def lenLocal (name : Ident) : Expr :=
  .arrayLength .localVar (localRef name)

def arrGet (name : Ident) (idx : Expr) : Expr :=
  .index (.var name) idx

def arrSet (name : Ident) (idx value : Expr) : Stmt :=
  .assign .localVar (localIndex name idx) value

def tuple0 (e : Expr) : Expr := .tupleGet e 0
def tuple1 (e : Expr) : Expr := .tupleGet e 1
def tuple2 (e : Expr) : Expr := .tupleGet e 2

def emptyBytes : Expr := .newBytes (.intLit 0)

def initCodeHashLit : Expr :=
  .fixedBytesLit bytes32Width
    [0x96, 0xe8, 0xac, 0x42, 0x77, 0x19, 0x8f, 0xf8,
     0xb6, 0xf7, 0x85, 0x47, 0x8a, 0xa9, 0xa3, 0x9f,
     0x40, 0x3c, 0xb7, 0x68, 0xdd, 0x02, 0xcb, 0xee,
     0x32, 0x6c, 0x3e, 0x7d, 0xa3, 0x48, 0x84, 0x5f]

/-! ## External ABI -/

def selectorBytes (a b c d : UInt8) : ByteArray := ⟨#[a, b, c, d]⟩

def getPairSelector : ByteArray := selectorBytes 0xe6 0xa4 0x39 0x05
def createPairSelector : ByteArray := selectorBytes 0xc9 0xc6 0x53 0x96
def getReservesSelector : ByteArray := selectorBytes 0x09 0x02 0xf1 0xac
def mintSelector : ByteArray := selectorBytes 0x6a 0x62 0x78 0x42
def burnSelector : ByteArray := selectorBytes 0x89 0xaf 0xcb 0x44
def swapSelector : ByteArray := selectorBytes 0x02 0x2c 0x0d 0x9f
def transferSelector : ByteArray := selectorBytes 0xa9 0x05 0x9c 0xbb
def transferFromSelector : ByteArray := selectorBytes 0x23 0xb8 0x72 0xdd
def permitSelector : ByteArray := selectorBytes 0xd5 0x05 0xac 0xcf
def balanceOfSelector : ByteArray := selectorBytes 0x70 0xa0 0x82 0x31
def depositSelector : ByteArray := selectorBytes 0xd0 0xe3 0x0d 0xb0
def withdrawSelector : ByteArray := selectorBytes 0x2e 0x1a 0x7d 0x4d

def decodeReturn? (ty : ABIType) (out : EVM.Bytes) : Option (List Value) :=
  (ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 ty out).map (fun v => [v])

def decodeReturns? (tys : List ABIType) (out : EVM.Bytes) : Option (List Value) :=
  ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 tys out

def decodeVoid? (_out : EVM.Bytes) : Option (List Value) :=
  some []

def routerExternalABI : ExternalCallABI where
  encode? := fun name args =>
    if name = "getPair" then
      ABI.encodeCallWithSelector? getPairSelector [addr, addr] args
    else if name = "createPair" then
      ABI.encodeCallWithSelector? createPairSelector [addr, addr] args
    else if name = "getReserves" then
      match args with
      | [] => some getReservesSelector
      | _ => none
    else if name = "mint" then
      ABI.encodeCallWithSelector? mintSelector [addr] args
    else if name = "burn" then
      ABI.encodeCallWithSelector? burnSelector [addr] args
    else if name = "swap" then
      ABI.encodeCallWithSelector? swapSelector [uint256, uint256, addr, bytesTy] args
    else if name = "transfer" then
      ABI.encodeCallWithSelector? transferSelector [addr, uint256] args
    else if name = "transferFrom" then
      ABI.encodeCallWithSelector? transferFromSelector [addr, addr, uint256] args
    else if name = "permit" then
      ABI.encodeCallWithSelector? permitSelector
        [addr, addr, uint256, uint256, uint8, bytes32, bytes32] args
    else if name = "balanceOf" then
      ABI.encodeCallWithSelector? balanceOfSelector [addr] args
    else if name = "deposit" then
      match args with
      | [] => some depositSelector
      | _ => none
    else if name = "withdraw" then
      ABI.encodeCallWithSelector? withdrawSelector [uint256] args
    else
      none
  decode? := fun name out =>
    if name = "getPair" then
      decodeReturn? addr out
    else if name = "createPair" then
      decodeReturn? addr out
    else if name = "getReserves" then
      decodeReturns? [uint112, uint112, uint32] out
    else if name = "mint" then
      decodeReturn? uint256 out
    else if name = "burn" then
      decodeReturns? [uint256, uint256] out
    else if name = "swap" then
      decodeVoid? out
    else if name = "transfer" then
      decodeReturn? boolTy out
    else if name = "transferFrom" then
      decodeReturn? boolTy out
    else if name = "permit" then
      decodeVoid? out
    else if name = "balanceOf" then
      decodeReturn? uint256 out
    else if name = "deposit" then
      decodeVoid? out
    else if name = "withdraw" then
      decodeVoid? out
    else
      none

/-! ## Storage declarations and layout -/

def storageDecls : List StorageDecl := []

def storageLayoutRaw : EvaledStorageRef -> EVM.State -> Option StorageLoc
  | _, _ => none

def storageLayout : StorageLayout :=
  solidityStorageLayout storageLayoutRaw

/-! ## Shared source patterns -/

def nonpayable : List Stmt :=
  [ .require (.binary .eq (.env .callvalue) (.intLit 0)) ]

def ensure (deadline : Expr) : List Stmt :=
  [ .require (.binary .ge deadline (.env .timestamp)) ]

def checkedAddInto (name : Ident) (x y : Expr) : List Stmt :=
  [ .letDecl name (some uint256) (add256 x y),
    .require (.binary .ge (.var name) x) ]

def checkedSubInto (name : Ident) (x y : Expr) : List Stmt :=
  [ .letDecl name (some uint256) (sub256 x y),
    .require (.binary .le (.var name) x) ]

def checkedMulInto (name : Ident) (x y : Expr) : List Stmt :=
  [ .ite
      (.binary .eq y (.intLit 0))
      [ .letDecl name (some uint256) (.intLit 0) ]
      [ .letDecl name (some uint256) (mul256 x y),
        .require (.binary .eq (.binary .div (.var name) y) x) ] ]

def requireDecodedBoolIfPresent (data : Ident) : List Stmt :=
  [ .ite
      (.binary .ne (lenLocal data) (.intLit 0))
      [ .letDecl (data ++ "_ok") (some boolTy) (.abiDecode boolTy (.var data)),
        .require (.var (data ++ "_ok")) ]
      [] ]

/-! ## Internal library/helper functions -/

def addFunction : FunctionDecl :=
  { name := "safeAdd"
    params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }]
    returnType := [uint256]
    body := checkedAddInto "z" (.var "x") (.var "y") ++ [ .return [.var "z"] ] }

def subFunction : FunctionDecl :=
  { name := "safeSub"
    params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }]
    returnType := [uint256]
    body := checkedSubInto "z" (.var "x") (.var "y") ++ [ .return [.var "z"] ] }

def mulFunction : FunctionDecl :=
  { name := "safeMul"
    params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }]
    returnType := [uint256]
    body := checkedMulInto "z" (.var "x") (.var "y") ++ [ .return [.var "z"] ] }

def sortTokensFunction : FunctionDecl :=
  { name := "sortTokens"
    params := [{ name := "tokenA", ty := addr }, { name := "tokenB", ty := addr }]
    returnType := [addr, addr]
    body :=
      [ .require (.binary .ne (.var "tokenA") (.var "tokenB")),
        .letDecl "token0" (some addr)
          (.ite (.binary .lt (.var "tokenA") (.var "tokenB")) (.var "tokenA") (.var "tokenB")),
        .letDecl "token1" (some addr)
          (.ite (.binary .lt (.var "tokenA") (.var "tokenB")) (.var "tokenB") (.var "tokenA")),
        .require (.binary .ne (.var "token0") zeroAddr),
        .return [.var "token0", .var "token1"] ] }

def pairForFunction : FunctionDecl :=
  { name := "pairFor"
    params :=
      [ { name := "factory_", ty := addr }, { name := "tokenA", ty := addr },
        { name := "tokenB", ty := addr } ]
    returnType := [addr]
    body :=
      [ .internalCall "sortTokens" [.var "tokenA", .var "tokenB"] "tokens",
        .letDecl "salt" (some bytes32)
          (.keccak256
            (.abiEncodePacked
              [(addr, tuple0 (.var "tokens")), (addr, tuple1 (.var "tokens"))])),
        .letDecl "raw" (some bytes32)
          (.keccak256
            (.abiEncodePacked
              [ (bytes1, .fixedBytesLit bytes1Width [0xff]),
                (addr, .var "factory_"),
                (bytes32, .var "salt"),
                (bytes32, initCodeHashLit) ])),
        .return [.cast (.cast (.var "raw") uint256St) addrSt] ] }

def quoteFunction : FunctionDecl :=
  { name := "quoteBody"
    params :=
      [ { name := "amountA", ty := uint256 }, { name := "reserveA", ty := uint256 },
        { name := "reserveB", ty := uint256 } ]
    returnType := [uint256]
    body :=
      [ .require (.binary .gt (.var "amountA") (.intLit 0)),
        .require
          (.binary .and
            (.binary .gt (.var "reserveA") (.intLit 0))
            (.binary .gt (.var "reserveB") (.intLit 0))),
        .internalCall "safeMul" [.var "amountA", .var "reserveB"] "num",
        .return [.binary .div (.var "num") (.var "reserveA")] ] }

def getAmountOutFunction : FunctionDecl :=
  { name := "getAmountOutBody"
    params :=
      [ { name := "amountIn", ty := uint256 }, { name := "reserveIn", ty := uint256 },
        { name := "reserveOut", ty := uint256 } ]
    returnType := [uint256]
    body :=
      [ .require (.binary .gt (.var "amountIn") (.intLit 0)),
        .require
          (.binary .and
            (.binary .gt (.var "reserveIn") (.intLit 0))
            (.binary .gt (.var "reserveOut") (.intLit 0))),
        .internalCall "safeMul" [.var "amountIn", (.intLit 997)] "amountInWithFee",
        .internalCall "safeMul" [.var "amountInWithFee", .var "reserveOut"] "numerator",
        .internalCall "safeMul" [.var "reserveIn", (.intLit 1000)] "reserveTimes",
        .internalCall "safeAdd" [.var "reserveTimes", .var "amountInWithFee"] "denominator",
        .return [.binary .div (.var "numerator") (.var "denominator")] ] }

def getAmountInFunction : FunctionDecl :=
  { name := "getAmountInBody"
    params :=
      [ { name := "amountOut", ty := uint256 }, { name := "reserveIn", ty := uint256 },
        { name := "reserveOut", ty := uint256 } ]
    returnType := [uint256]
    body :=
      [ .require (.binary .gt (.var "amountOut") (.intLit 0)),
        .require
          (.binary .and
            (.binary .gt (.var "reserveIn") (.intLit 0))
            (.binary .gt (.var "reserveOut") (.intLit 0))),
        .internalCall "safeMul" [.var "reserveIn", .var "amountOut"] "a",
        .internalCall "safeMul" [.var "a", (.intLit 1000)] "numerator",
        .internalCall "safeSub" [.var "reserveOut", .var "amountOut"] "reserveMinus",
        .internalCall "safeMul" [.var "reserveMinus", (.intLit 997)] "denominator",
        .internalCall "safeAdd" [.binary .div (.var "numerator") (.var "denominator"), (.intLit 1)]
          "amountIn",
        .return [.var "amountIn"] ] }

def getReservesFunction : FunctionDecl :=
  { name := "getReservesBody"
    params :=
      [ { name := "factory_", ty := addr }, { name := "tokenA", ty := addr },
        { name := "tokenB", ty := addr } ]
    returnType := [uint256, uint256]
    body :=
      [ .internalCall "sortTokens" [.var "tokenA", .var "tokenB"] "tokens",
        .internalCall "pairFor" [.var "factory_", .var "tokenA", .var "tokenB"] "pair",
        .externalCall (.var "pair") "getReserves" (.intLit 0) [] "reserves" false,
        .letDecl "reserve0" (some uint256) (tuple0 (.var "reserves")),
        .letDecl "reserve1" (some uint256) (tuple1 (.var "reserves")),
        .ite
          (.binary .eq (.var "tokenA") (tuple0 (.var "tokens")))
          [ .return [.var "reserve0", .var "reserve1"] ]
          [ .return [.var "reserve1", .var "reserve0"] ] ] }

def getAmountsOutFunction : FunctionDecl :=
  { name := "getAmountsOutBody"
    params :=
      [ { name := "factory_", ty := addr }, { name := "amountIn", ty := uint256 },
        { name := "path", ty := addrArray } ]
    returnType := [uintArray]
    body :=
      [ .require (.binary .ge (lenLocal "path") (.intLit 2)),
        .letDecl "amounts" (some uintArray) (.newArray uint256St (lenLocal "path")),
        arrSet "amounts" (.intLit 0) (.var "amountIn"),
        .for
          [ .letDecl "i" (some uint256) (.intLit 0) ]
          (.binary .lt (.var "i") (.binary .sub (lenLocal "path") (.intLit 1)))
          [ .assign .localVar (localRef "i") (.binary .add (.var "i") (.intLit 1)) ]
          [ .internalCall "getReservesBody"
              [.var "factory_", arrGet "path" (.var "i"),
                arrGet "path" (.binary .add (.var "i") (.intLit 1))] "reserves",
            .internalCall "getAmountOutBody"
              [arrGet "amounts" (.var "i"), tuple0 (.var "reserves"), tuple1 (.var "reserves")]
              "amountOut",
            arrSet "amounts" (.binary .add (.var "i") (.intLit 1)) (.var "amountOut") ],
        .return [.var "amounts"] ] }

def getAmountsInFunction : FunctionDecl :=
  { name := "getAmountsInBody"
    params :=
      [ { name := "factory_", ty := addr }, { name := "amountOut", ty := uint256 },
        { name := "path", ty := addrArray } ]
    returnType := [uintArray]
    body :=
      [ .require (.binary .ge (lenLocal "path") (.intLit 2)),
        .letDecl "amounts" (some uintArray) (.newArray uint256St (lenLocal "path")),
        arrSet "amounts" (.binary .sub (lenLocal "path") (.intLit 1)) (.var "amountOut"),
        .for
          [ .letDecl "i" (some uint256) (.binary .sub (lenLocal "path") (.intLit 1)) ]
          (.binary .gt (.var "i") (.intLit 0))
          [ .assign .localVar (localRef "i") (.binary .sub (.var "i") (.intLit 1)) ]
          [ .internalCall "getReservesBody"
              [.var "factory_", arrGet "path" (.binary .sub (.var "i") (.intLit 1)),
                arrGet "path" (.var "i")] "reserves",
            .internalCall "getAmountInBody"
              [arrGet "amounts" (.var "i"), tuple0 (.var "reserves"), tuple1 (.var "reserves")]
              "amountIn",
            arrSet "amounts" (.binary .sub (.var "i") (.intLit 1)) (.var "amountIn") ],
        .return [.var "amounts"] ] }

def safeTransferFunction : FunctionDecl :=
  { name := "safeTransfer"
    params :=
      [ { name := "token", ty := addr }, { name := "to", ty := addr },
        { name := "value", ty := uint256 } ]
    returnType := []
    body :=
      [ .letDecl "data" (some bytesTy) (.abiEncodeCall "transfer" [.var "to", .var "value"]),
        .lowLevelCall (.var "token") (.intLit 0) (.var "data") "success" "returndata",
        .require (.var "success") ] ++
      requireDecodedBoolIfPresent "returndata" ++
      [ .return [] ] }

def safeTransferFromFunction : FunctionDecl :=
  { name := "safeTransferFrom"
    params :=
      [ { name := "token", ty := addr }, { name := "from", ty := addr },
        { name := "to", ty := addr }, { name := "value", ty := uint256 } ]
    returnType := []
    body :=
      [ .letDecl "data" (some bytesTy)
          (.abiEncodeCall "transferFrom" [.var "from", .var "to", .var "value"]),
        .lowLevelCall (.var "token") (.intLit 0) (.var "data") "success" "returndata",
        .require (.var "success") ] ++
      requireDecodedBoolIfPresent "returndata" ++
      [ .return [] ] }

def safeTransferETHFunction : FunctionDecl :=
  { name := "safeTransferETH"
    params := [{ name := "to", ty := addr }, { name := "value", ty := uint256 }]
    returnType := []
    body :=
      [ .lowLevelCall (.var "to") (.var "value") emptyBytes "success" "_data",
        .require (.var "success"),
        .return [] ] }

def addLiquidityBodyFunction : FunctionDecl :=
  { name := "addLiquidityBody"
    params :=
      [ { name := "factory_", ty := addr }, { name := "tokenA", ty := addr },
        { name := "tokenB", ty := addr }, { name := "amountADesired", ty := uint256 },
        { name := "amountBDesired", ty := uint256 }, { name := "amountAMin", ty := uint256 },
        { name := "amountBMin", ty := uint256 } ]
    returnType := [uint256, uint256]
    body :=
      [ .externalCall (.var "factory_") "getPair" (.intLit 0) [.var "tokenA", .var "tokenB"]
          "pair0" false,
        .ite
          (.binary .eq (.var "pair0") zeroAddr)
          [ .externalCall (.var "factory_") "createPair" (.intLit 0)
              [.var "tokenA", .var "tokenB"] "_created" ]
          [],
        .internalCall "getReservesBody" [.var "factory_", .var "tokenA", .var "tokenB"] "reserves",
        .ite
          (.binary .and
            (.binary .eq (tuple0 (.var "reserves")) (.intLit 0))
            (.binary .eq (tuple1 (.var "reserves")) (.intLit 0)))
          [ .return [.var "amountADesired", .var "amountBDesired"] ]
          [ .internalCall "quoteBody"
              [.var "amountADesired", tuple0 (.var "reserves"), tuple1 (.var "reserves")]
              "amountBOptimal",
            .ite
              (.binary .le (.var "amountBOptimal") (.var "amountBDesired"))
              [ .require (.binary .ge (.var "amountBOptimal") (.var "amountBMin")),
                .return [.var "amountADesired", .var "amountBOptimal"] ]
              [ .internalCall "quoteBody"
                  [.var "amountBDesired", tuple1 (.var "reserves"), tuple0 (.var "reserves")]
                  "amountAOptimal",
                .require (.binary .le (.var "amountAOptimal") (.var "amountADesired")),
                .require (.binary .ge (.var "amountAOptimal") (.var "amountAMin")),
                .return [.var "amountAOptimal", .var "amountBDesired"] ] ] ] }

def removeLiquidityBodyFunction : FunctionDecl :=
  { name := "removeLiquidityBody"
    params :=
      [ { name := "factory_", ty := addr }, { name := "tokenA", ty := addr },
        { name := "tokenB", ty := addr }, { name := "liquidity", ty := uint256 },
        { name := "amountAMin", ty := uint256 }, { name := "amountBMin", ty := uint256 },
        { name := "to", ty := addr }, { name := "deadline", ty := uint256 } ]
    returnType := [uint256, uint256]
    body :=
      ensure (.var "deadline") ++
      [ .internalCall "pairFor" [.var "factory_", .var "tokenA", .var "tokenB"] "pair",
        .externalCall (.var "pair") "transferFrom" (.intLit 0)
          [sender, .var "pair", .var "liquidity"] "_transferOk",
        .externalCall (.var "pair") "burn" (.intLit 0) [.var "to"] "burned",
        .internalCall "sortTokens" [.var "tokenA", .var "tokenB"] "tokens",
        .letDecl "amountA" (some uint256)
          (.ite (.binary .eq (.var "tokenA") (tuple0 (.var "tokens")))
            (tuple0 (.var "burned")) (tuple1 (.var "burned"))),
        .letDecl "amountB" (some uint256)
          (.ite (.binary .eq (.var "tokenA") (tuple0 (.var "tokens")))
            (tuple1 (.var "burned")) (tuple0 (.var "burned"))),
        .require (.binary .ge (.var "amountA") (.var "amountAMin")),
        .require (.binary .ge (.var "amountB") (.var "amountBMin")),
        .return [.var "amountA", .var "amountB"] ] }

def removeLiquidityETHBodyFunction : FunctionDecl :=
  { name := "removeLiquidityETHBody"
    params :=
      [ { name := "factory_", ty := addr }, { name := "weth_", ty := addr },
        { name := "token", ty := addr }, { name := "liquidity", ty := uint256 },
        { name := "amountTokenMin", ty := uint256 }, { name := "amountETHMin", ty := uint256 },
        { name := "to", ty := addr }, { name := "deadline", ty := uint256 } ]
    returnType := [uint256, uint256]
    body :=
      ensure (.var "deadline") ++
      [ .internalCall "removeLiquidityBody"
          [.var "factory_", .var "token", .var "weth_", .var "liquidity",
            .var "amountTokenMin", .var "amountETHMin", thisAddr, .var "deadline"]
          "amounts",
        .internalCall "safeTransfer" [.var "token", .var "to", tuple0 (.var "amounts")] "_t",
        .externalCall (.var "weth_") "withdraw" (.intLit 0) [tuple1 (.var "amounts")] "_w",
        .internalCall "safeTransferETH" [.var "to", tuple1 (.var "amounts")] "_eth",
        .return [tuple0 (.var "amounts"), tuple1 (.var "amounts")] ] }

def removeLiquidityETHSupportingFeeBodyFunction : FunctionDecl :=
  { name := "removeLiquidityETHSupportingFeeBody"
    params :=
      [ { name := "factory_", ty := addr }, { name := "weth_", ty := addr },
        { name := "token", ty := addr }, { name := "liquidity", ty := uint256 },
        { name := "amountTokenMin", ty := uint256 }, { name := "amountETHMin", ty := uint256 },
        { name := "to", ty := addr }, { name := "deadline", ty := uint256 } ]
    returnType := [uint256]
    body :=
      ensure (.var "deadline") ++
      [ .internalCall "removeLiquidityBody"
          [.var "factory_", .var "token", .var "weth_", .var "liquidity",
            .var "amountTokenMin", .var "amountETHMin", thisAddr, .var "deadline"]
          "amounts",
        .externalCall (.var "token") "balanceOf" (.intLit 0) [thisAddr] "tokenBalance" false,
        .internalCall "safeTransfer" [.var "token", .var "to", .var "tokenBalance"] "_t",
        .externalCall (.var "weth_") "withdraw" (.intLit 0) [tuple1 (.var "amounts")] "_w",
        .internalCall "safeTransferETH" [.var "to", tuple1 (.var "amounts")] "_eth",
        .return [tuple1 (.var "amounts")] ] }

def swapLoopToBody : List Stmt :=
  [ .letDecl "nextTo" (some addr) (.var "_to"),
    .ite
      (.binary .lt (.var "i") (.binary .sub (lenLocal "path") (.intLit 2)))
      [ .internalCall "pairFor"
          [.var "factory_", .var "output", arrGet "path" (.binary .add (.var "i") (.intLit 2))]
          "nextPair",
        .assign .localVar (localRef "nextTo") (.var "nextPair") ]
      [] ]

def swapFunction : FunctionDecl :=
  { name := "swapBody"
    params :=
      [ { name := "factory_", ty := addr }, { name := "amounts", ty := uintArray },
        { name := "path", ty := addrArray }, { name := "_to", ty := addr } ]
    returnType := []
    body :=
      [ .for
          [ .letDecl "i" (some uint256) (.intLit 0) ]
          (.binary .lt (.var "i") (.binary .sub (lenLocal "path") (.intLit 1)))
          [ .assign .localVar (localRef "i") (.binary .add (.var "i") (.intLit 1)) ]
          ([ .letDecl "input" (some addr) (arrGet "path" (.var "i")),
             .letDecl "output" (some addr) (arrGet "path" (.binary .add (.var "i") (.intLit 1))),
             .internalCall "sortTokens" [.var "input", .var "output"] "tokens",
             .letDecl "amountOut" (some uint256)
               (arrGet "amounts" (.binary .add (.var "i") (.intLit 1))),
             .letDecl "amount0Out" (some uint256)
               (.ite (.binary .eq (.var "input") (tuple0 (.var "tokens")))
                 (.intLit 0) (.var "amountOut")),
             .letDecl "amount1Out" (some uint256)
               (.ite (.binary .eq (.var "input") (tuple0 (.var "tokens")))
                 (.var "amountOut") (.intLit 0)) ] ++
           swapLoopToBody ++
           [ .internalCall "pairFor" [.var "factory_", .var "input", .var "output"] "pair",
             .externalCall (.var "pair") "swap" (.intLit 0)
               [.var "amount0Out", .var "amount1Out", .var "nextTo", emptyBytes] "_swap" ]),
        .return [] ] }

def swapSupportingFeeFunction : FunctionDecl :=
  { name := "swapSupportingFeeBody"
    params :=
      [ { name := "factory_", ty := addr }, { name := "path", ty := addrArray },
        { name := "_to", ty := addr } ]
    returnType := []
    body :=
      [ .for
          [ .letDecl "i" (some uint256) (.intLit 0) ]
          (.binary .lt (.var "i") (.binary .sub (lenLocal "path") (.intLit 1)))
          [ .assign .localVar (localRef "i") (.binary .add (.var "i") (.intLit 1)) ]
          ([ .letDecl "input" (some addr) (arrGet "path" (.var "i")),
             .letDecl "output" (some addr) (arrGet "path" (.binary .add (.var "i") (.intLit 1))),
             .internalCall "sortTokens" [.var "input", .var "output"] "tokens",
             .internalCall "pairFor" [.var "factory_", .var "input", .var "output"] "pair",
             .externalCall (.var "pair") "getReserves" (.intLit 0) [] "reserves" false,
             .letDecl "reserveInput" (some uint256)
               (.ite (.binary .eq (.var "input") (tuple0 (.var "tokens")))
                 (tuple0 (.var "reserves")) (tuple1 (.var "reserves"))),
             .letDecl "reserveOutput" (some uint256)
               (.ite (.binary .eq (.var "input") (tuple0 (.var "tokens")))
                 (tuple1 (.var "reserves")) (tuple0 (.var "reserves"))),
             .externalCall (.var "input") "balanceOf" (.intLit 0) [.var "pair"] "balanceIn" false,
             .internalCall "safeSub" [.var "balanceIn", .var "reserveInput"] "amountInput",
             .internalCall "getAmountOutBody"
               [.var "amountInput", .var "reserveInput", .var "reserveOutput"] "amountOutput",
             .letDecl "amount0Out" (some uint256)
               (.ite (.binary .eq (.var "input") (tuple0 (.var "tokens")))
                 (.intLit 0) (.var "amountOutput")),
             .letDecl "amount1Out" (some uint256)
               (.ite (.binary .eq (.var "input") (tuple0 (.var "tokens")))
                 (.var "amountOutput") (.intLit 0)) ] ++
           swapLoopToBody ++
           [ .externalCall (.var "pair") "swap" (.intLit 0)
               [.var "amount0Out", .var "amount1Out", .var "nextTo", emptyBytes] "_swap" ]),
        .return [] ] }

def functions : List FunctionDecl :=
  [ addFunction,
    subFunction,
    mulFunction,
    sortTokensFunction,
    pairForFunction,
    quoteFunction,
    getAmountOutFunction,
    getAmountInFunction,
    getReservesFunction,
    getAmountsOutFunction,
    getAmountsInFunction,
    safeTransferFunction,
    safeTransferFromFunction,
    safeTransferETHFunction,
    addLiquidityBodyFunction,
    removeLiquidityBodyFunction,
    removeLiquidityETHBodyFunction,
    removeLiquidityETHSupportingFeeBodyFunction,
    swapFunction,
    swapSupportingFeeFunction ]

/-! ## Constructor and immutable getters -/

def constructorDecl : ConstructorDecl :=
  { params := [{ name := "_factory", ty := addr }, { name := "_WETH", ty := addr }]
    body :=
      nonpayable ++
      [ .letDecl "imm_factory" (some addr) (.var "_factory"),
        .letDecl "imm_WETH" (some addr) (.var "_WETH") ] }

def receiveTransition (v : RouterImmutables) : TransitionDecl :=
  { name := "receive"
    params := []
    returnType := []
    body := [ .require (.binary .eq sender (WETH v)), .return [] ] }

def factoryTransition (v : RouterImmutables) : TransitionDecl :=
  { name := "factory"
    params := []
    returnType := [addr]
    body := nonpayable ++ [ .return [factory v] ] }

def WETHTransition (v : RouterImmutables) : TransitionDecl :=
  { name := "WETH"
    params := []
    returnType := [addr]
    body := nonpayable ++ [ .return [WETH v] ] }

/-! ## Public transitions -/

def addLiquidityTransition (v : RouterImmutables) : TransitionDecl :=
  { name := "addLiquidity"
    params :=
      [ { name := "tokenA", ty := addr }, { name := "tokenB", ty := addr },
        { name := "amountADesired", ty := uint256 }, { name := "amountBDesired", ty := uint256 },
        { name := "amountAMin", ty := uint256 }, { name := "amountBMin", ty := uint256 },
        { name := "to", ty := addr }, { name := "deadline", ty := uint256 } ]
    returnType := [uint256, uint256, uint256]
    body :=
      nonpayable ++ ensure (.var "deadline") ++
      [ .internalCall "addLiquidityBody"
          [factory v, .var "tokenA", .var "tokenB", .var "amountADesired",
            .var "amountBDesired", .var "amountAMin", .var "amountBMin"] "amounts",
        .internalCall "pairFor" [factory v, .var "tokenA", .var "tokenB"] "pair",
        .internalCall "safeTransferFrom"
          [.var "tokenA", sender, .var "pair", tuple0 (.var "amounts")] "_a",
        .internalCall "safeTransferFrom"
          [.var "tokenB", sender, .var "pair", tuple1 (.var "amounts")] "_b",
        .externalCall (.var "pair") "mint" (.intLit 0) [.var "to"] "liquidity",
        .return [tuple0 (.var "amounts"), tuple1 (.var "amounts"), .var "liquidity"] ] }

def addLiquidityETHTransition (v : RouterImmutables) : TransitionDecl :=
  { name := "addLiquidityETH"
    params :=
      [ { name := "token", ty := addr }, { name := "amountTokenDesired", ty := uint256 },
        { name := "amountTokenMin", ty := uint256 }, { name := "amountETHMin", ty := uint256 },
        { name := "to", ty := addr }, { name := "deadline", ty := uint256 } ]
    returnType := [uint256, uint256, uint256]
    body :=
      ensure (.var "deadline") ++
      [ .internalCall "addLiquidityBody"
          [factory v, .var "token", WETH v, .var "amountTokenDesired", (.env .callvalue),
            .var "amountTokenMin", .var "amountETHMin"] "amounts",
        .internalCall "pairFor" [factory v, .var "token", WETH v] "pair",
        .internalCall "safeTransferFrom"
          [.var "token", sender, .var "pair", tuple0 (.var "amounts")] "_t",
        .externalCall (WETH v) "deposit" (tuple1 (.var "amounts")) [] "_d",
        .externalCall (WETH v) "transfer" (.intLit 0) [.var "pair", tuple1 (.var "amounts")]
          "wethTransferOk",
        .require (.var "wethTransferOk"),
        .externalCall (.var "pair") "mint" (.intLit 0) [.var "to"] "liquidity",
        .ite
          (.binary .gt (.env .callvalue) (tuple1 (.var "amounts")))
          [ .internalCall "safeTransferETH"
              [sender, sub256 (.env .callvalue) (tuple1 (.var "amounts"))] "_refund" ]
          [],
        .return [tuple0 (.var "amounts"), tuple1 (.var "amounts"), .var "liquidity"] ] }

def removeLiquidityTransition (v : RouterImmutables) : TransitionDecl :=
  { name := "removeLiquidity"
    params :=
      [ { name := "tokenA", ty := addr }, { name := "tokenB", ty := addr },
        { name := "liquidity", ty := uint256 }, { name := "amountAMin", ty := uint256 },
        { name := "amountBMin", ty := uint256 }, { name := "to", ty := addr },
        { name := "deadline", ty := uint256 } ]
    returnType := [uint256, uint256]
    body :=
      nonpayable ++
      [ .internalCall "removeLiquidityBody"
          [factory v, .var "tokenA", .var "tokenB", .var "liquidity",
            .var "amountAMin", .var "amountBMin", .var "to", .var "deadline"] "amounts",
        .return [tuple0 (.var "amounts"), tuple1 (.var "amounts")] ] }

def removeLiquidityETHTransition (v : RouterImmutables) : TransitionDecl :=
  { name := "removeLiquidityETH"
    params :=
      [ { name := "token", ty := addr }, { name := "liquidity", ty := uint256 },
        { name := "amountTokenMin", ty := uint256 }, { name := "amountETHMin", ty := uint256 },
        { name := "to", ty := addr }, { name := "deadline", ty := uint256 } ]
    returnType := [uint256, uint256]
    body :=
      nonpayable ++
      [ .internalCall "removeLiquidityETHBody"
          [factory v, WETH v, .var "token", .var "liquidity", .var "amountTokenMin",
            .var "amountETHMin", .var "to", .var "deadline"] "amounts",
        .return [tuple0 (.var "amounts"), tuple1 (.var "amounts")] ] }

def permitValue : Expr :=
  .ite (.var "approveMax") (.intLit maxUint256) (.var "liquidity")

def removeLiquidityWithPermitTransition (v : RouterImmutables) : TransitionDecl :=
  { name := "removeLiquidityWithPermit"
    params :=
      [ { name := "tokenA", ty := addr }, { name := "tokenB", ty := addr },
        { name := "liquidity", ty := uint256 }, { name := "amountAMin", ty := uint256 },
        { name := "amountBMin", ty := uint256 }, { name := "to", ty := addr },
        { name := "deadline", ty := uint256 }, { name := "approveMax", ty := boolTy },
        { name := "v", ty := uint8 }, { name := "r", ty := bytes32 },
        { name := "s", ty := bytes32 } ]
    returnType := [uint256, uint256]
    body :=
      nonpayable ++
      [ .internalCall "pairFor" [factory v, .var "tokenA", .var "tokenB"] "pair",
        .externalCall (.var "pair") "permit" (.intLit 0)
          [sender, thisAddr, permitValue, .var "deadline", .var "v", .var "r", .var "s"] "_permit",
        .internalCall "removeLiquidityBody"
          [factory v, .var "tokenA", .var "tokenB", .var "liquidity",
            .var "amountAMin", .var "amountBMin", .var "to", .var "deadline"] "amounts",
        .return [tuple0 (.var "amounts"), tuple1 (.var "amounts")] ] }

def removeLiquidityETHWithPermitTransition (v : RouterImmutables) : TransitionDecl :=
  { name := "removeLiquidityETHWithPermit"
    params :=
      [ { name := "token", ty := addr }, { name := "liquidity", ty := uint256 },
        { name := "amountTokenMin", ty := uint256 }, { name := "amountETHMin", ty := uint256 },
        { name := "to", ty := addr }, { name := "deadline", ty := uint256 },
        { name := "approveMax", ty := boolTy }, { name := "v", ty := uint8 },
        { name := "r", ty := bytes32 }, { name := "s", ty := bytes32 } ]
    returnType := [uint256, uint256]
    body :=
      nonpayable ++
      [ .internalCall "pairFor" [factory v, .var "token", WETH v] "pair",
        .externalCall (.var "pair") "permit" (.intLit 0)
          [sender, thisAddr, permitValue, .var "deadline", .var "v", .var "r", .var "s"] "_permit",
        .internalCall "removeLiquidityETHBody"
          [factory v, WETH v, .var "token", .var "liquidity", .var "amountTokenMin",
            .var "amountETHMin", .var "to", .var "deadline"] "amounts",
        .return [tuple0 (.var "amounts"), tuple1 (.var "amounts")] ] }

def removeLiquidityETHSupportingFeeTransition (v : RouterImmutables) : TransitionDecl :=
  { name := "removeLiquidityETHSupportingFeeOnTransferTokens"
    params :=
      [ { name := "token", ty := addr }, { name := "liquidity", ty := uint256 },
        { name := "amountTokenMin", ty := uint256 }, { name := "amountETHMin", ty := uint256 },
        { name := "to", ty := addr }, { name := "deadline", ty := uint256 } ]
    returnType := [uint256]
    body :=
      nonpayable ++
      [ .internalCall "removeLiquidityETHSupportingFeeBody"
          [factory v, WETH v, .var "token", .var "liquidity", .var "amountTokenMin",
            .var "amountETHMin", .var "to", .var "deadline"] "amountETH",
        .return [.var "amountETH"] ] }

def removeLiquidityETHWithPermitSupportingFeeTransition (v : RouterImmutables) : TransitionDecl :=
  { name := "removeLiquidityETHWithPermitSupportingFeeOnTransferTokens"
    params :=
      [ { name := "token", ty := addr }, { name := "liquidity", ty := uint256 },
        { name := "amountTokenMin", ty := uint256 }, { name := "amountETHMin", ty := uint256 },
        { name := "to", ty := addr }, { name := "deadline", ty := uint256 },
        { name := "approveMax", ty := boolTy }, { name := "v", ty := uint8 },
        { name := "r", ty := bytes32 }, { name := "s", ty := bytes32 } ]
    returnType := [uint256]
    body :=
      nonpayable ++
      [ .internalCall "pairFor" [factory v, .var "token", WETH v] "pair",
        .externalCall (.var "pair") "permit" (.intLit 0)
          [sender, thisAddr, permitValue, .var "deadline", .var "v", .var "r", .var "s"] "_permit",
        .internalCall "removeLiquidityETHSupportingFeeBody"
          [factory v, WETH v, .var "token", .var "liquidity", .var "amountTokenMin",
            .var "amountETHMin", .var "to", .var "deadline"] "amountETH",
        .return [.var "amountETH"] ] }

def lastIndex (arrayName : Ident) : Expr :=
  .binary .sub (lenLocal arrayName) (.intLit 1)

def firstPairForPath (v : RouterImmutables) : List Stmt :=
  [ .internalCall "pairFor" [factory v, arrGet "path" (.intLit 0), arrGet "path" (.intLit 1)]
      "firstPair" ]

def swapExactTokensForTokensTransition (v : RouterImmutables) : TransitionDecl :=
  { name := "swapExactTokensForTokens"
    params :=
      [ { name := "amountIn", ty := uint256 }, { name := "amountOutMin", ty := uint256 },
        { name := "path", ty := addrArray }, { name := "to", ty := addr },
        { name := "deadline", ty := uint256 } ]
    returnType := [uintArray]
    body :=
      nonpayable ++ ensure (.var "deadline") ++
      [ .internalCall "getAmountsOutBody" [factory v, .var "amountIn", .var "path"] "amounts",
        .require (.binary .ge (arrGet "amounts" (lastIndex "amounts")) (.var "amountOutMin")) ] ++
      firstPairForPath v ++
      [ .internalCall "safeTransferFrom"
          [arrGet "path" (.intLit 0), sender, .var "firstPair", arrGet "amounts" (.intLit 0)] "_t",
        .internalCall "swapBody" [factory v, .var "amounts", .var "path", .var "to"] "_swap",
        .return [.var "amounts"] ] }

def swapTokensForExactTokensTransition (v : RouterImmutables) : TransitionDecl :=
  { name := "swapTokensForExactTokens"
    params :=
      [ { name := "amountOut", ty := uint256 }, { name := "amountInMax", ty := uint256 },
        { name := "path", ty := addrArray }, { name := "to", ty := addr },
        { name := "deadline", ty := uint256 } ]
    returnType := [uintArray]
    body :=
      nonpayable ++ ensure (.var "deadline") ++
      [ .internalCall "getAmountsInBody" [factory v, .var "amountOut", .var "path"] "amounts",
        .require (.binary .le (arrGet "amounts" (.intLit 0)) (.var "amountInMax")) ] ++
      firstPairForPath v ++
      [ .internalCall "safeTransferFrom"
          [arrGet "path" (.intLit 0), sender, .var "firstPair", arrGet "amounts" (.intLit 0)] "_t",
        .internalCall "swapBody" [factory v, .var "amounts", .var "path", .var "to"] "_swap",
        .return [.var "amounts"] ] }

def swapExactETHForTokensTransition (v : RouterImmutables) : TransitionDecl :=
  { name := "swapExactETHForTokens"
    params :=
      [ { name := "amountOutMin", ty := uint256 }, { name := "path", ty := addrArray },
        { name := "to", ty := addr }, { name := "deadline", ty := uint256 } ]
    returnType := [uintArray]
    body :=
      ensure (.var "deadline") ++
      [ .require (.binary .eq (arrGet "path" (.intLit 0)) (WETH v)),
        .internalCall "getAmountsOutBody" [factory v, (.env .callvalue), .var "path"] "amounts",
        .require (.binary .ge (arrGet "amounts" (lastIndex "amounts")) (.var "amountOutMin")),
        .externalCall (WETH v) "deposit" (arrGet "amounts" (.intLit 0)) [] "_d" ] ++
      firstPairForPath v ++
      [ .externalCall (WETH v) "transfer" (.intLit 0)
          [.var "firstPair", arrGet "amounts" (.intLit 0)] "wethTransferOk",
        .require (.var "wethTransferOk"),
        .internalCall "swapBody" [factory v, .var "amounts", .var "path", .var "to"] "_swap",
        .return [.var "amounts"] ] }

def swapTokensForExactETHTransition (v : RouterImmutables) : TransitionDecl :=
  { name := "swapTokensForExactETH"
    params :=
      [ { name := "amountOut", ty := uint256 }, { name := "amountInMax", ty := uint256 },
        { name := "path", ty := addrArray }, { name := "to", ty := addr },
        { name := "deadline", ty := uint256 } ]
    returnType := [uintArray]
    body :=
      nonpayable ++ ensure (.var "deadline") ++
      [ .require (.binary .eq (arrGet "path" (lastIndex "path")) (WETH v)),
        .internalCall "getAmountsInBody" [factory v, .var "amountOut", .var "path"] "amounts",
        .require (.binary .le (arrGet "amounts" (.intLit 0)) (.var "amountInMax")) ] ++
      firstPairForPath v ++
      [ .internalCall "safeTransferFrom"
          [arrGet "path" (.intLit 0), sender, .var "firstPair", arrGet "amounts" (.intLit 0)] "_t",
        .internalCall "swapBody" [factory v, .var "amounts", .var "path", thisAddr] "_swap",
        .externalCall (WETH v) "withdraw" (.intLit 0) [arrGet "amounts" (lastIndex "amounts")]
          "_w",
        .internalCall "safeTransferETH" [.var "to", arrGet "amounts" (lastIndex "amounts")]
          "_eth",
        .return [.var "amounts"] ] }

def swapExactTokensForETHTransition (v : RouterImmutables) : TransitionDecl :=
  { name := "swapExactTokensForETH"
    params :=
      [ { name := "amountIn", ty := uint256 }, { name := "amountOutMin", ty := uint256 },
        { name := "path", ty := addrArray }, { name := "to", ty := addr },
        { name := "deadline", ty := uint256 } ]
    returnType := [uintArray]
    body :=
      nonpayable ++ ensure (.var "deadline") ++
      [ .require (.binary .eq (arrGet "path" (lastIndex "path")) (WETH v)),
        .internalCall "getAmountsOutBody" [factory v, .var "amountIn", .var "path"] "amounts",
        .require (.binary .ge (arrGet "amounts" (lastIndex "amounts")) (.var "amountOutMin")) ] ++
      firstPairForPath v ++
      [ .internalCall "safeTransferFrom"
          [arrGet "path" (.intLit 0), sender, .var "firstPair", arrGet "amounts" (.intLit 0)] "_t",
        .internalCall "swapBody" [factory v, .var "amounts", .var "path", thisAddr] "_swap",
        .externalCall (WETH v) "withdraw" (.intLit 0) [arrGet "amounts" (lastIndex "amounts")]
          "_w",
        .internalCall "safeTransferETH" [.var "to", arrGet "amounts" (lastIndex "amounts")]
          "_eth",
        .return [.var "amounts"] ] }

def swapETHForExactTokensTransition (v : RouterImmutables) : TransitionDecl :=
  { name := "swapETHForExactTokens"
    params :=
      [ { name := "amountOut", ty := uint256 }, { name := "path", ty := addrArray },
        { name := "to", ty := addr }, { name := "deadline", ty := uint256 } ]
    returnType := [uintArray]
    body :=
      ensure (.var "deadline") ++
      [ .require (.binary .eq (arrGet "path" (.intLit 0)) (WETH v)),
        .internalCall "getAmountsInBody" [factory v, .var "amountOut", .var "path"] "amounts",
        .require (.binary .le (arrGet "amounts" (.intLit 0)) (.env .callvalue)),
        .externalCall (WETH v) "deposit" (arrGet "amounts" (.intLit 0)) [] "_d" ] ++
      firstPairForPath v ++
      [ .externalCall (WETH v) "transfer" (.intLit 0)
          [.var "firstPair", arrGet "amounts" (.intLit 0)] "wethTransferOk",
        .require (.var "wethTransferOk"),
        .internalCall "swapBody" [factory v, .var "amounts", .var "path", .var "to"] "_swap",
        .ite
          (.binary .gt (.env .callvalue) (arrGet "amounts" (.intLit 0)))
          [ .internalCall "safeTransferETH"
              [sender, sub256 (.env .callvalue) (arrGet "amounts" (.intLit 0))] "_refund" ]
          [],
        .return [.var "amounts"] ] }

def swapExactTokensForTokensSupportingFeeTransition (v : RouterImmutables) : TransitionDecl :=
  { name := "swapExactTokensForTokensSupportingFeeOnTransferTokens"
    params :=
      [ { name := "amountIn", ty := uint256 }, { name := "amountOutMin", ty := uint256 },
        { name := "path", ty := addrArray }, { name := "to", ty := addr },
        { name := "deadline", ty := uint256 } ]
    returnType := []
    body :=
      nonpayable ++ ensure (.var "deadline") ++ firstPairForPath v ++
      [ .internalCall "safeTransferFrom"
          [arrGet "path" (.intLit 0), sender, .var "firstPair", .var "amountIn"] "_t",
        .externalCall (arrGet "path" (lastIndex "path")) "balanceOf" (.intLit 0) [.var "to"]
          "balanceBefore" false,
        .internalCall "swapSupportingFeeBody" [factory v, .var "path", .var "to"] "_swap",
        .externalCall (arrGet "path" (lastIndex "path")) "balanceOf" (.intLit 0) [.var "to"]
          "balanceAfter" false,
        .internalCall "safeSub" [.var "balanceAfter", .var "balanceBefore"] "delta",
        .require (.binary .ge (.var "delta") (.var "amountOutMin")),
        .return [] ] }

def swapExactETHForTokensSupportingFeeTransition (v : RouterImmutables) : TransitionDecl :=
  { name := "swapExactETHForTokensSupportingFeeOnTransferTokens"
    params :=
      [ { name := "amountOutMin", ty := uint256 }, { name := "path", ty := addrArray },
        { name := "to", ty := addr }, { name := "deadline", ty := uint256 } ]
    returnType := []
    body :=
      ensure (.var "deadline") ++
      [ .require (.binary .eq (arrGet "path" (.intLit 0)) (WETH v)),
        .letDecl "amountIn" (some uint256) (.env .callvalue),
        .externalCall (WETH v) "deposit" (.var "amountIn") [] "_d" ] ++
      firstPairForPath v ++
      [ .externalCall (WETH v) "transfer" (.intLit 0) [.var "firstPair", .var "amountIn"]
          "wethTransferOk",
        .require (.var "wethTransferOk"),
        .externalCall (arrGet "path" (lastIndex "path")) "balanceOf" (.intLit 0) [.var "to"]
          "balanceBefore" false,
        .internalCall "swapSupportingFeeBody" [factory v, .var "path", .var "to"] "_swap",
        .externalCall (arrGet "path" (lastIndex "path")) "balanceOf" (.intLit 0) [.var "to"]
          "balanceAfter" false,
        .internalCall "safeSub" [.var "balanceAfter", .var "balanceBefore"] "delta",
        .require (.binary .ge (.var "delta") (.var "amountOutMin")),
        .return [] ] }

def swapExactTokensForETHSupportingFeeTransition (v : RouterImmutables) : TransitionDecl :=
  { name := "swapExactTokensForETHSupportingFeeOnTransferTokens"
    params :=
      [ { name := "amountIn", ty := uint256 }, { name := "amountOutMin", ty := uint256 },
        { name := "path", ty := addrArray }, { name := "to", ty := addr },
        { name := "deadline", ty := uint256 } ]
    returnType := []
    body :=
      nonpayable ++ ensure (.var "deadline") ++
      [ .require (.binary .eq (arrGet "path" (lastIndex "path")) (WETH v)) ] ++
      firstPairForPath v ++
      [ .internalCall "safeTransferFrom"
          [arrGet "path" (.intLit 0), sender, .var "firstPair", .var "amountIn"] "_t",
        .internalCall "swapSupportingFeeBody" [factory v, .var "path", thisAddr] "_swap",
        .externalCall (WETH v) "balanceOf" (.intLit 0) [thisAddr] "amountOut" false,
        .require (.binary .ge (.var "amountOut") (.var "amountOutMin")),
        .externalCall (WETH v) "withdraw" (.intLit 0) [.var "amountOut"] "_w",
        .internalCall "safeTransferETH" [.var "to", .var "amountOut"] "_eth",
        .return [] ] }

def quoteTransition : TransitionDecl :=
  { name := "quote"
    params :=
      [ { name := "amountA", ty := uint256 }, { name := "reserveA", ty := uint256 },
        { name := "reserveB", ty := uint256 } ]
    returnType := [uint256]
    body :=
      nonpayable ++
      [ .internalCall "quoteBody" [.var "amountA", .var "reserveA", .var "reserveB"] "amountB",
        .return [.var "amountB"] ] }

def getAmountOutTransition : TransitionDecl :=
  { name := "getAmountOut"
    params :=
      [ { name := "amountIn", ty := uint256 }, { name := "reserveIn", ty := uint256 },
        { name := "reserveOut", ty := uint256 } ]
    returnType := [uint256]
    body :=
      nonpayable ++
      [ .internalCall "getAmountOutBody"
          [.var "amountIn", .var "reserveIn", .var "reserveOut"] "amountOut",
        .return [.var "amountOut"] ] }

def getAmountInTransition : TransitionDecl :=
  { name := "getAmountIn"
    params :=
      [ { name := "amountOut", ty := uint256 }, { name := "reserveIn", ty := uint256 },
        { name := "reserveOut", ty := uint256 } ]
    returnType := [uint256]
    body :=
      nonpayable ++
      [ .internalCall "getAmountInBody"
          [.var "amountOut", .var "reserveIn", .var "reserveOut"] "amountIn",
        .return [.var "amountIn"] ] }

def getAmountsOutTransition (v : RouterImmutables) : TransitionDecl :=
  { name := "getAmountsOut"
    params := [{ name := "amountIn", ty := uint256 }, { name := "path", ty := addrArray }]
    returnType := [uintArray]
    body :=
      nonpayable ++
      [ .internalCall "getAmountsOutBody" [factory v, .var "amountIn", .var "path"] "amounts",
        .return [.var "amounts"] ] }

def getAmountsInTransition (v : RouterImmutables) : TransitionDecl :=
  { name := "getAmountsIn"
    params := [{ name := "amountOut", ty := uint256 }, { name := "path", ty := addrArray }]
    returnType := [uintArray]
    body :=
      nonpayable ++
      [ .internalCall "getAmountsInBody" [factory v, .var "amountOut", .var "path"] "amounts",
        .return [.var "amounts"] ] }

def transitions (v : RouterImmutables) : List TransitionDecl :=
  [ factoryTransition v,
    WETHTransition v,
    addLiquidityTransition v,
    addLiquidityETHTransition v,
    removeLiquidityTransition v,
    removeLiquidityETHTransition v,
    removeLiquidityWithPermitTransition v,
    removeLiquidityETHWithPermitTransition v,
    removeLiquidityETHSupportingFeeTransition v,
    removeLiquidityETHWithPermitSupportingFeeTransition v,
    swapExactTokensForTokensTransition v,
    swapTokensForExactTokensTransition v,
    swapExactETHForTokensTransition v,
    swapTokensForExactETHTransition v,
    swapExactTokensForETHTransition v,
    swapETHForExactTokensTransition v,
    swapExactTokensForTokensSupportingFeeTransition v,
    swapExactETHForTokensSupportingFeeTransition v,
    swapExactTokensForETHSupportingFeeTransition v,
    quoteTransition,
    getAmountOutTransition,
    getAmountInTransition,
    getAmountsOutTransition v,
    getAmountsInTransition v ]

def contract (v : RouterImmutables) : ContractDecl :=
  { name := "UniswapV2Router02"
    storage := storageDecls
    ctor := constructorDecl
    functions := functions
    transitions := transitions v
    receive := some (receiveTransition v) }

def config (v : RouterImmutables) : Config :=
  { storage := storageLayout
    externalABI := routerExternalABI
    abiDecodeMode := DecodeMode.legacySolc05
    selfDeployment := genSolidityConstructorDeployment (contract v).ctor.params }

end Benchmarks.UniswapV2Router02
