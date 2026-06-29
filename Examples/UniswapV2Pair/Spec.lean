import Solm.Semantics
import Solm.SolidityLayout

/-!
# Uniswap V2 Pair benchmark spec

Solm benchmark spec for the unmodified upstream `UniswapV2Pair` contract from
`Uniswap/v2-core` tag `v1.0.1`.

The benchmark intentionally targets the full production Pair runtime, including the inherited
`UniswapV2ERC20` LP-token surface.  The storage layout and ABI surface are explicit and complete;
events are omitted, as in the other examples.
-/

open Solm ABI

namespace UniswapV2Pair

/-! ## Types -/

def uint8Int : IntType := .uint ⟨8, by decide⟩
def uint32Int : IntType := .uint ⟨32, by decide⟩
def uint112Int : IntType := .uint ⟨112, by decide⟩
def uint256Int : IntType := .uint ⟨256, by decide⟩

def bytes32Width : Fin 32 := ⟨31, by decide⟩
def bytes2Width : Fin 32 := ⟨1, by decide⟩

def uint8 : ABIType := .elem (.int uint8Int)
def uint32 : ABIType := .elem (.int uint32Int)
def uint112 : ABIType := .elem (.int uint112Int)
def uint256 : ABIType := .elem (.int uint256Int)
def addr : ABIType := .elem .address
def legacyAddr : ABIType := .elem .legacyAddress
def boolTy : ABIType := .elem .bool
def bytes32 : ABIType := .elem (.bytes bytes32Width)
def bytes2 : ABIType := .elem (.bytes bytes2Width)

def uint8St : StorageType := .elem (.int uint8Int)
def uint32St : StorageType := .elem (.int uint32Int)
def uint112St : StorageType := .elem (.int uint112Int)
def uint256St : StorageType := .elem (.int uint256Int)
def addrSt : StorageType := .elem .address
def bytes32St : StorageType := .elem (.bytes bytes32Width)

def sender : Expr := .env .caller
def this : Expr := .env .this
def now : Expr := .env .timestamp
def zeroAddr : Expr := .cast (.intLit 0) addrSt

def u256 (e : Expr) : Expr := .inRange uint256Int e
def u112 (e : Expr) : Expr := .inRange uint112Int e
def u32 (e : Expr) : Expr := .inRange uint32Int e

def maxUint256 : Int := (2 : Int) ^ 256 - 1
def maxUint112 : Int := (2 : Int) ^ 112 - 1
def twoPow256 : Int := (2 : Int) ^ 256
def twoPow32 : Int := (2 : Int) ^ 32
def q112 : Int := (2 : Int) ^ 112
def minimumLiquidity : Int := 1000

def selectorBytes (a b c d : UInt8) : ByteArray := ⟨#[a, b, c, d]⟩

def balanceOfSelector : ByteArray := selectorBytes 0x70 0xa0 0x82 0x31
def transferSelector : ByteArray := selectorBytes 0xa9 0x05 0x9c 0xbb
def feeToSelector : ByteArray := selectorBytes 0x01 0x7e 0x7e 0x58
def uniswapV2CallSelector : ByteArray := selectorBytes 0x10 0xd1 0xe8 0x5c

def nameBytes : ByteArray := String.toByteArray "Uniswap V2"
def symbolBytes : ByteArray := String.toByteArray "UNI-V2"
def versionBytes : ByteArray := String.toByteArray "1"

def eip712DomainTypehashBytes : ByteArray :=
  String.toByteArray "EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"

def permitTypehashBytes : List UInt8 :=
  [ 0x6e, 0x71, 0xed, 0xae, 0x12, 0xb1, 0xb9, 0x7f,
    0x4d, 0x1f, 0x60, 0x37, 0x0f, 0xef, 0x10, 0x10,
    0x5f, 0xa2, 0xfa, 0xae, 0x01, 0x26, 0x11, 0x4a,
    0x16, 0x9c, 0x64, 0x84, 0x5d, 0x61, 0x26, 0xc9 ]

def permitTypehashExpr : Expr := .fixedBytesLit bytes32Width permitTypehashBytes

def wrapU256 (e : Expr) : Expr := .binary .mod e (.intLit twoPow256)

def addressAsUint256 (e : Expr) : Expr := .cast e uint256St

def uq112Price (numerator denominator : Expr) : Expr :=
  .binary .div (.binary .mul numerator (.intLit q112)) denominator

def eip712DomainTypehashExpr : Expr := .keccak256 (.bytesLit eip712DomainTypehashBytes)

def nameHashExpr : Expr := .keccak256 (.bytesLit nameBytes)

def versionHashExpr : Expr := .keccak256 (.bytesLit versionBytes)

/-! ## Storage references -/

def totalSupplyRef : StorageRef := { base := "totalSupply" }
def balanceOfRef (owner : Expr) : StorageRef :=
  { base := "balanceOf", steps := [.mindex owner] }
def allowanceRef (owner spender : Expr) : StorageRef :=
  { base := "allowance", steps := [.mindex owner, .mindex spender] }
def domainSeparatorRef : StorageRef := { base := "DOMAIN_SEPARATOR" }
def noncesRef (owner : Expr) : StorageRef := { base := "nonces", steps := [.mindex owner] }

def factoryRef : StorageRef := { base := "factory" }
def token0Ref : StorageRef := { base := "token0" }
def token1Ref : StorageRef := { base := "token1" }
def reserve0Ref : StorageRef := { base := "reserve0" }
def reserve1Ref : StorageRef := { base := "reserve1" }
def blockTimestampLastRef : StorageRef := { base := "blockTimestampLast" }
def price0CumulativeLastRef : StorageRef := { base := "price0CumulativeLast" }
def price1CumulativeLastRef : StorageRef := { base := "price1CumulativeLast" }
def kLastRef : StorageRef := { base := "kLast" }
def unlockedRef : StorageRef := { base := "unlocked" }

/-! ## Storage declarations and layout -/

def storageDecls : List StorageDecl :=
  [ { name := "totalSupply", ty := uint256St },
    { name := "balanceOf", ty := .mapping .address uint256St },
    { name := "allowance", ty := .mapping .address (.mapping .address uint256St) },
    { name := "DOMAIN_SEPARATOR", ty := bytes32St },
    { name := "nonces", ty := .mapping .address uint256St },
    { name := "factory", ty := addrSt },
    { name := "token0", ty := addrSt },
    { name := "token1", ty := addrSt },
    { name := "reserve0", ty := uint112St },
    { name := "reserve1", ty := uint112St },
    { name := "blockTimestampLast", ty := uint32St },
    { name := "price0CumulativeLast", ty := uint256St },
    { name := "price1CumulativeLast", ty := uint256St },
    { name := "kLast", ty := uint256St },
    { name := "unlocked", ty := uint256St } ]

def mapSlot (key baseSlot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC (key.toByteArray ++ baseSlot.toByteArray))

def balanceOfSlot (owner : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord owner) ⟨1⟩

def allowanceOwnerSlot (owner : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord owner) ⟨2⟩

def allowanceSlot (owner spender : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord spender) (allowanceOwnerSlot owner)

def nonceSlot (owner : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord owner) ⟨4⟩

def wordLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, type := .int uint256Int }

def bytes32Loc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, type := .bytes bytes32Width }

def addrLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 20, hbound := by decide, type := .address }

def uint112Loc0 (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 14, hbound := by decide, type := .int uint112Int }

def uint112Loc14 (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 14, size := 14, hbound := by decide, type := .int uint112Int }

def uint32Loc28 (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 28, size := 4, hbound := by decide, type := .int uint32Int }

def storageLayout : StorageLayout where
  layout ref _ :=
    match ref.base, ref.steps with
    | "totalSupply", [] => some (wordLoc ⟨0⟩)
    | "balanceOf", [.mindex owner] => some (wordLoc (balanceOfSlot owner))
    | "allowance", [.mindex owner, .mindex spender] =>
        some (wordLoc (allowanceSlot owner spender))
    | "DOMAIN_SEPARATOR", [] => some (bytes32Loc ⟨3⟩)
    | "nonces", [.mindex owner] => some (wordLoc (nonceSlot owner))
    | "factory", [] => some (addrLoc ⟨5⟩)
    | "token0", [] => some (addrLoc ⟨6⟩)
    | "token1", [] => some (addrLoc ⟨7⟩)
    | "reserve0", [] => some (uint112Loc0 ⟨8⟩)
    | "reserve1", [] => some (uint112Loc14 ⟨8⟩)
    | "blockTimestampLast", [] => some (uint32Loc28 ⟨8⟩)
    | "price0CumulativeLast", [] => some (wordLoc ⟨9⟩)
    | "price1CumulativeLast", [] => some (wordLoc ⟨10⟩)
    | "kLast", [] => some (wordLoc ⟨11⟩)
    | "unlocked", [] => some (wordLoc ⟨12⟩)
    | _, _ => none

/-! ## Shared source-body helpers -/

def nonpayable : List Stmt :=
  [ .require (.binary .eq (.env .callvalue) (.intLit 0)) ]

def lockEnter : List Stmt :=
  nonpayable ++
    [ .require (.binary .eq (.storage unlockedRef) (.intLit 1)),
      .assign .storage unlockedRef (.intLit 0) ]

def lockExit : List Stmt :=
  [ .assign .storage unlockedRef (.intLit 1) ]

def updateReservesStmts (balance0 balance1 : Expr) : List Stmt :=
  [ .internalCall "_update" [balance0, balance1, .storage reserve0Ref, .storage reserve1Ref]
      "_updateResult" ]

def safeTransferStmts (token recipient value : Expr) (okVar _dataVar : Ident) : List Stmt :=
  [ .internalCall "_safeTransfer" [token, recipient, value] okVar ]

def transferCalldataExpr (recipient value : Expr) : Expr :=
  .abiEncodeCall "transfer" [recipient, value]

def safeTransferReturnOkExpr : Expr :=
  .ite (.var "_success")
    (.ite (.binary .eq (.arrayLength .localVar { base := "_data" }) (.intLit 0))
      (.boolLit true)
      (.abiDecode boolTy (.var "_data")))
    (.boolLit false)

def checkedExternalCallStmts (receiver : Expr) (name : Ident) (eth : Expr)
    (args : List Expr) (retVar : Ident) : List Stmt :=
  [ .require (.binary .gt (.extCodeSize receiver) (.intLit 0)),
    .externalCall receiver name eth args retVar ]

def balanceOfThisStmts (token : Expr) (retVar : Ident) : List Stmt :=
  checkedExternalCallStmts token "balanceOf" (.intLit 0) [this] retVar

def token0BalanceOfThisStmts (retVar : Ident) : List Stmt :=
  balanceOfThisStmts (.storage token0Ref) retVar

def token1BalanceOfThisStmts (retVar : Ident) : List Stmt :=
  balanceOfThisStmts (.storage token1Ref) retVar

def pairBalanceOfThisStmts (ret0 ret1 : Ident) : List Stmt :=
  token0BalanceOfThisStmts ret0 ++ token1BalanceOfThisStmts ret1

def domainSeparatorExpr : Expr :=
  .keccak256 (.abiEncodePacked
    [ (bytes32, eip712DomainTypehashExpr),
      (bytes32, nameHashExpr),
      (bytes32, versionHashExpr),
      (uint256, .env .chainid),
      (uint256, addressAsUint256 this) ])

def permitStructHashExpr : Expr :=
  .keccak256 (.abiEncodePacked
    [ (bytes32, permitTypehashExpr),
      (uint256, addressAsUint256 (.var "owner")),
      (uint256, addressAsUint256 (.var "spender")),
      (uint256, .var "value"),
      (uint256, .var "nonce"),
      (uint256, .var "deadline") ])

def permitDigestExpr : Expr :=
  .keccak256 (.abiEncodePacked
    [ (bytes2, .fixedBytesLit bytes2Width [0x19, 0x01]),
      (bytes32, .storage domainSeparatorRef),
      (bytes32, .var "structHash") ])

/-! ## Internal functions -/

def approveFunction : FunctionDecl :=
  { name := "_approve"
    params :=
      [ { name := "owner", ty := addr }, { name := "spender", ty := addr },
        { name := "value", ty := uint256 } ]
    returnType := none
    body := [ .assign .storage (allowanceRef (.var "owner") (.var "spender")) (.var "value") ] }

def transferFunction : FunctionDecl :=
  { name := "_transfer"
    params :=
      [ { name := "from", ty := addr }, { name := "to", ty := addr },
        { name := "value", ty := uint256 } ]
    returnType := none
    body :=
      [ .letDecl "fromBalance" (some uint256) (.storage (balanceOfRef (.var "from"))),
        .require (.binary .ge (.var "fromBalance") (.var "value")),
        .assign .storage (balanceOfRef (.var "from"))
          (.binary .sub (.var "fromBalance") (.var "value")),
        .letDecl "toBalance" (some uint256) (.storage (balanceOfRef (.var "to"))),
        .assign .storage (balanceOfRef (.var "to"))
          (u256 (.binary .add (.var "toBalance") (.var "value"))) ] }

def mintFunction : FunctionDecl :=
  { name := "_mint"
    params := [{ name := "to", ty := addr }, { name := "value", ty := uint256 }]
    returnType := none
    body :=
      [ .assign .storage totalSupplyRef
          (u256 (.binary .add (.storage totalSupplyRef) (.var "value"))),
        .assign .storage (balanceOfRef (.var "to"))
          (u256 (.binary .add (.storage (balanceOfRef (.var "to"))) (.var "value"))) ] }

def burnFunction : FunctionDecl :=
  { name := "_burn"
    params := [{ name := "from", ty := addr }, { name := "value", ty := uint256 }]
    returnType := none
    body :=
      [ .letDecl "fromBalance" (some uint256) (.storage (balanceOfRef (.var "from"))),
        .require (.binary .ge (.var "fromBalance") (.var "value")),
        .assign .storage (balanceOfRef (.var "from"))
          (.binary .sub (.var "fromBalance") (.var "value")),
        .letDecl "_totalSupply" (some uint256) (.storage totalSupplyRef),
        .require (.binary .ge (.var "_totalSupply") (.var "value")),
        .assign .storage totalSupplyRef (.binary .sub (.var "_totalSupply") (.var "value")) ] }

def safeTransferFunction : FunctionDecl :=
  { name := "_safeTransfer"
    params :=
      [ { name := "token", ty := addr }, { name := "to", ty := addr },
        { name := "value", ty := uint256 } ]
    returnType := none
    body :=
      [ .lowLevelCall (.var "token") (.intLit 0)
          (transferCalldataExpr (.var "to") (.var "value")) "_success" "_data",
        .require safeTransferReturnOkExpr ] }

def updateFunction : FunctionDecl :=
  { name := "_update"
    params :=
      [ { name := "balance0", ty := uint256 }, { name := "balance1", ty := uint256 },
        { name := "_reserve0", ty := uint112 }, { name := "_reserve1", ty := uint112 } ]
    returnType := none
    body :=
      [ .require (.binary .and
          (.binary .le (.var "balance0") (.intLit maxUint112))
          (.binary .le (.var "balance1") (.intLit maxUint112))),
        .letDecl "blockTimestamp" (some uint32) (u32 (.binary .mod now (.intLit twoPow32))),
        .letDecl "timeElapsed" (some uint32)
          (u32 (.binary .mod
            (.binary .add
              (.binary .sub (.var "blockTimestamp") (.storage blockTimestampLastRef))
              (.intLit twoPow32))
            (.intLit twoPow32))),
        .ite (.binary .and
            (.binary .gt (.var "timeElapsed") (.intLit 0))
            (.binary .and
              (.binary .ne (.var "_reserve0") (.intLit 0))
              (.binary .ne (.var "_reserve1") (.intLit 0))))
          [ .assign .storage price0CumulativeLastRef
              (wrapU256 (.binary .add (.storage price0CumulativeLastRef)
                (.binary .mul (uq112Price (.var "_reserve1") (.var "_reserve0"))
                  (.var "timeElapsed")))),
            .assign .storage price1CumulativeLastRef
              (wrapU256 (.binary .add (.storage price1CumulativeLastRef)
                (.binary .mul (uq112Price (.var "_reserve0") (.var "_reserve1"))
                  (.var "timeElapsed")))) ]
          [],
        .assign .storage reserve0Ref (u112 (.var "balance0")),
        .assign .storage reserve1Ref (u112 (.var "balance1")),
        .assign .storage blockTimestampLastRef (.var "blockTimestamp") ] }

def sqrtFunction : FunctionDecl :=
  { name := "sqrt"
    params := [{ name := "y", ty := uint256 }]
    returnType := some uint256
    body :=
      [ .ite (.binary .gt (.var "y") (.intLit 3))
          [ .letDecl "z" (some uint256) (.var "y"),
            .letDecl "x" (some uint256)
              (.binary .add (.binary .div (.var "y") (.intLit 2)) (.intLit 1)),
            .while (.binary .lt (.var "x") (.var "z"))
              [ .assign .localVar { base := "z" } (.var "x"),
                .assign .localVar { base := "x" }
                  (.binary .div
                    (.binary .add (.binary .div (.var "y") (.var "x")) (.var "x"))
                    (.intLit 2)) ],
            .return (.var "z") ]
          [ .ite (.binary .ne (.var "y") (.intLit 0))
              [ .return (.intLit 1) ]
              [ .return (.intLit 0) ] ] ] }

def minFunction : FunctionDecl :=
  { name := "min"
    params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }]
    returnType := some uint256
    body := [ .return (.ite (.binary .lt (.var "x") (.var "y")) (.var "x") (.var "y")) ] }

def mintFeeFunction : FunctionDecl :=
  { name := "_mintFee"
    params := [{ name := "_reserve0", ty := uint112 }, { name := "_reserve1", ty := uint112 }]
    returnType := some boolTy
    body :=
      checkedExternalCallStmts (.storage factoryRef) "feeTo" (.intLit 0) [] "feeTo" ++
      [ .letDecl "feeOn" (some boolTy) (.binary .ne (.var "feeTo") zeroAddr),
        .letDecl "_kLast" (some uint256) (.storage kLastRef),
        .ite (.var "feeOn")
          [ .ite (.binary .ne (.var "_kLast") (.intLit 0))
              [ .internalCall "sqrt"
                  [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))] "rootK",
                .internalCall "sqrt" [.var "_kLast"] "rootKLast",
                .ite (.binary .gt (.var "rootK") (.var "rootKLast"))
                  [ .letDecl "numerator" (some uint256)
                      (u256 (.binary .mul (.storage totalSupplyRef)
                        (u256 (.binary .sub (.var "rootK") (.var "rootKLast"))))),
                    .letDecl "denominator" (some uint256)
                      (u256 (.binary .add
                        (u256 (.binary .mul (.var "rootK") (.intLit 5)))
                        (.var "rootKLast"))),
                    .letDecl "liquidity" (some uint256)
                      (.binary .div (.var "numerator") (.var "denominator")),
                    .ite (.binary .gt (.var "liquidity") (.intLit 0))
                      [ .internalCall "_mint" [.var "feeTo", .var "liquidity"] "_feeMint" ]
                      [] ]
                  [] ]
              [] ]
          [ .ite (.binary .ne (.var "_kLast") (.intLit 0))
              [ .assign .storage kLastRef (.intLit 0) ]
              [] ],
        .return (.var "feeOn") ] }

/-! ## Constructor -/

def constructorDecl : ConstructorDecl :=
  { params := []
    body :=
      [ .assign .storage domainSeparatorRef domainSeparatorExpr,
        .assign .storage unlockedRef (.intLit 1),
        .assign .storage factoryRef sender ] }

/-! ## LP-token inherited public surface -/

def nameTransition : TransitionDecl :=
  { name := "name", params := [], returnType := some .string
    body := nonpayable ++ [ .return (.bytesLit nameBytes) ] }

def symbolTransition : TransitionDecl :=
  { name := "symbol", params := [], returnType := some .string
    body := nonpayable ++ [ .return (.bytesLit symbolBytes) ] }

def decimalsTransition : TransitionDecl :=
  { name := "decimals", params := [], returnType := some uint8
    body := nonpayable ++ [ .return (.intLit 18) ] }

def totalSupplyTransition : TransitionDecl :=
  { name := "totalSupply", params := [], returnType := some uint256
    body := nonpayable ++ [ .return (.storage totalSupplyRef) ] }

def balanceOfTransition : TransitionDecl :=
  { name := "balanceOf"
    params := [{ name := "owner", ty := legacyAddr }]
    returnType := some uint256
    body := nonpayable ++ [ .return (.storage (balanceOfRef (.var "owner"))) ] }

def allowanceTransition : TransitionDecl :=
  { name := "allowance"
    params := [{ name := "owner", ty := legacyAddr }, { name := "spender", ty := legacyAddr }]
    returnType := some uint256
    body := nonpayable ++ [ .return (.storage (allowanceRef (.var "owner") (.var "spender"))) ] }

def approveTransition : TransitionDecl :=
  { name := "approve"
    params := [{ name := "spender", ty := legacyAddr }, { name := "value", ty := uint256 }]
    returnType := some boolTy
    body :=
      nonpayable ++
        [ .assign .storage (allowanceRef sender (.var "spender")) (.var "value"),
          .return (.boolLit true) ] }

def transferTransition : TransitionDecl :=
  { name := "transfer"
    params := [{ name := "to", ty := legacyAddr }, { name := "value", ty := uint256 }]
    returnType := some boolTy
    body :=
      nonpayable ++
        [ .letDecl "fromBalance" (some uint256) (.storage (balanceOfRef sender)),
          .require (.binary .ge (.var "fromBalance") (.var "value")),
          .assign .storage (balanceOfRef sender)
            (.binary .sub (.var "fromBalance") (.var "value")),
          .letDecl "toBalance" (some uint256) (.storage (balanceOfRef (.var "to"))),
          .assign .storage (balanceOfRef (.var "to"))
            (u256 (.binary .add (.var "toBalance") (.var "value"))),
          .return (.boolLit true) ] }

def transferFromTransition : TransitionDecl :=
  { name := "transferFrom"
    params := [{ name := "from", ty := legacyAddr }, { name := "to", ty := legacyAddr },
      { name := "value", ty := uint256 }]
    returnType := some boolTy
    body :=
      nonpayable ++
        [ .letDecl "currentAllowance" (some uint256) (.storage (allowanceRef (.var "from") sender)),
          .ite (.binary .ne (.var "currentAllowance") (.intLit maxUint256))
            [ .require (.binary .ge (.var "currentAllowance") (.var "value")),
              .assign .storage (allowanceRef (.var "from") sender)
                (.binary .sub (.var "currentAllowance") (.var "value")) ]
            [],
          .letDecl "fromBalance" (some uint256) (.storage (balanceOfRef (.var "from"))),
          .require (.binary .ge (.var "fromBalance") (.var "value")),
          .assign .storage (balanceOfRef (.var "from"))
            (.binary .sub (.var "fromBalance") (.var "value")),
          .letDecl "toBalance" (some uint256) (.storage (balanceOfRef (.var "to"))),
          .assign .storage (balanceOfRef (.var "to"))
            (u256 (.binary .add (.var "toBalance") (.var "value"))),
          .return (.boolLit true) ] }

def domainSeparatorTransition : TransitionDecl :=
  { name := "DOMAIN_SEPARATOR", params := [], returnType := some bytes32
    body := nonpayable ++ [ .return (.storage domainSeparatorRef) ] }

def permitTypehashTransition : TransitionDecl :=
  { name := "PERMIT_TYPEHASH", params := [], returnType := some bytes32
    body := nonpayable ++ [ .return permitTypehashExpr ] }

def noncesTransition : TransitionDecl :=
  { name := "nonces"
    params := [{ name := "owner", ty := legacyAddr }]
    returnType := some uint256
    body := nonpayable ++ [ .return (.storage (noncesRef (.var "owner"))) ] }

def permitTransition : TransitionDecl :=
  { name := "permit"
    params :=
      [ { name := "owner", ty := legacyAddr }, { name := "spender", ty := legacyAddr },
        { name := "value", ty := uint256 }, { name := "deadline", ty := uint256 },
        { name := "v", ty := uint8 }, { name := "r", ty := bytes32 }, { name := "s", ty := bytes32 } ]
    returnType := none
    body :=
      nonpayable ++
        [ .require (.binary .ge (.var "deadline") now),
          .letDecl "nonce" (some uint256) (.storage (noncesRef (.var "owner"))),
          .assign .storage (noncesRef (.var "owner"))
            (u256 (.binary .add (.var "nonce") (.intLit 1))),
          .letDecl "structHash" (some bytes32) permitStructHashExpr,
          .letDecl "digest" (some bytes32) permitDigestExpr,
          .externalCall (.cast (.intLit 1) addrSt) "ecrecover" (.intLit 0)
            [.var "digest", .var "v", .var "r", .var "s"] "recoveredAddress",
          .require (.binary .and
            (.binary .ne (.var "recoveredAddress") zeroAddr)
            (.binary .eq (.var "recoveredAddress") (.var "owner"))),
          .internalCall "_approve" [.var "owner", .var "spender", .var "value"]
            "_approveResult" ] }

/-! ## Pair getters and mutating AMM surface -/

def minimumLiquidityTransition : TransitionDecl :=
  { name := "MINIMUM_LIQUIDITY", params := [], returnType := some uint256
    body := nonpayable ++ [ .return (.intLit minimumLiquidity) ] }

def factoryTransition : TransitionDecl :=
  { name := "factory", params := [], returnType := some addr
    body := nonpayable ++ [ .return (.storage factoryRef) ] }

def token0Transition : TransitionDecl :=
  { name := "token0", params := [], returnType := some addr
    body := nonpayable ++ [ .return (.storage token0Ref) ] }

def token1Transition : TransitionDecl :=
  { name := "token1", params := [], returnType := some addr
    body := nonpayable ++ [ .return (.storage token1Ref) ] }

def getReservesTransition : TransitionDecl :=
  { name := "getReserves"
    params := []
    returnType := some (.tuple [uint112, uint112, uint32])
    body :=
      nonpayable ++
        [ .return (.tupleLit
            [ .storage reserve0Ref, .storage reserve1Ref, .storage blockTimestampLastRef ]) ] }

def price0CumulativeLastTransition : TransitionDecl :=
  { name := "price0CumulativeLast", params := [], returnType := some uint256
    body := nonpayable ++ [ .return (.storage price0CumulativeLastRef) ] }

def price1CumulativeLastTransition : TransitionDecl :=
  { name := "price1CumulativeLast", params := [], returnType := some uint256
    body := nonpayable ++ [ .return (.storage price1CumulativeLastRef) ] }

def kLastTransition : TransitionDecl :=
  { name := "kLast", params := [], returnType := some uint256
    body := nonpayable ++ [ .return (.storage kLastRef) ] }

def initializeTransition : TransitionDecl :=
  { name := "initialize"
    params := [{ name := "_token0", ty := legacyAddr }, { name := "_token1", ty := legacyAddr }]
    returnType := none
    body :=
      nonpayable ++
        [ .require (.binary .eq sender (.storage factoryRef)),
          .assign .storage token0Ref (.var "_token0"),
          .assign .storage token1Ref (.var "_token1") ] }

def mintTransition : TransitionDecl :=
  { name := "mint"
    params := [{ name := "to", ty := legacyAddr }]
    returnType := some uint256
    body :=
      lockEnter ++
        [ .letDecl "_reserve0" (some uint112) (.storage reserve0Ref),
          .letDecl "_reserve1" (some uint112) (.storage reserve1Ref) ] ++
      pairBalanceOfThisStmts "balance0" "balance1" ++
        [ .letDecl "amount0" (some uint256)
            (u256 (.binary .sub (.var "balance0") (.var "_reserve0"))),
          .letDecl "amount1" (some uint256)
            (u256 (.binary .sub (.var "balance1") (.var "_reserve1"))),
          .internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn",
          .letDecl "_totalSupply" (some uint256) (.storage totalSupplyRef),
          .ite (.binary .eq (.var "_totalSupply") (.intLit 0))
            [ .internalCall "sqrt" [u256 (.binary .mul (.var "amount0") (.var "amount1"))]
                "rootLiquidity",
              .letDecl "liquidity" (some uint256)
                (u256 (.binary .sub (.var "rootLiquidity") (.intLit minimumLiquidity))),
              .internalCall "_mint" [zeroAddr, (.intLit minimumLiquidity)] "_minimumMint" ]
            [ .letDecl "liquidity0" (some uint256)
                (.binary .div (u256 (.binary .mul (.var "amount0") (.var "_totalSupply")))
                  (.var "_reserve0")),
              .letDecl "liquidity1" (some uint256)
                (.binary .div (u256 (.binary .mul (.var "amount1") (.var "_totalSupply")))
                  (.var "_reserve1")),
              .internalCall "min" [.var "liquidity0", .var "liquidity1"] "liquidity" ],
          .require (.binary .gt (.var "liquidity") (.intLit 0)),
          .internalCall "_mint" [.var "to", .var "liquidity"] "_mintResult" ] ++
      updateReservesStmts (.var "balance0") (.var "balance1") ++
      [ .ite (.var "feeOn")
          [ .assign .storage kLastRef
              (u256 (.binary .mul (.storage reserve0Ref) (.storage reserve1Ref))) ]
          [] ] ++
      lockExit ++
        [ .return (.var "liquidity") ] }

def burnTransition : TransitionDecl :=
  { name := "burn"
    params := [{ name := "to", ty := legacyAddr }]
    returnType := some (.tuple [uint256, uint256])
    body :=
      lockEnter ++
        [ .letDecl "_reserve0" (some uint112) (.storage reserve0Ref),
          .letDecl "_reserve1" (some uint112) (.storage reserve1Ref),
          .letDecl "_token0" (some addr) (.storage token0Ref),
          .letDecl "_token1" (some addr) (.storage token1Ref) ] ++
      balanceOfThisStmts (.var "_token0") "balance0" ++
      balanceOfThisStmts (.var "_token1") "balance1" ++
        [ .letDecl "liquidity" (some uint256) (.storage (balanceOfRef this)),
          .internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn",
          .letDecl "_totalSupply" (some uint256) (.storage totalSupplyRef),
          .letDecl "amount0" (some uint256)
            (.binary .div (u256 (.binary .mul (.var "liquidity") (.var "balance0")))
              (.var "_totalSupply")),
          .letDecl "amount1" (some uint256)
            (.binary .div (u256 (.binary .mul (.var "liquidity") (.var "balance1")))
              (.var "_totalSupply")),
          .require (.binary .and
            (.binary .gt (.var "amount0") (.intLit 0))
            (.binary .gt (.var "amount1") (.intLit 0))),
          .internalCall "_burn" [this, .var "liquidity"] "_burnResult" ] ++
      safeTransferStmts (.var "_token0") (.var "to") (.var "amount0") "ok0" "_ret0" ++
      safeTransferStmts (.var "_token1") (.var "to") (.var "amount1") "ok1" "_ret1" ++
      balanceOfThisStmts (.var "_token0") "newBalance0" ++
      balanceOfThisStmts (.var "_token1") "newBalance1" ++
      updateReservesStmts (.var "newBalance0") (.var "newBalance1") ++
      [ .ite (.var "feeOn")
          [ .assign .storage kLastRef
              (u256 (.binary .mul (.storage reserve0Ref) (.storage reserve1Ref))) ]
          [] ] ++
      lockExit ++
        [ .return (.tupleLit [.var "amount0", .var "amount1"]) ] }

def swapTransition : TransitionDecl :=
  { name := "swap"
    params :=
      [ { name := "amount0Out", ty := uint256 }, { name := "amount1Out", ty := uint256 },
        { name := "to", ty := legacyAddr }, { name := "data", ty := .bytes } ]
    returnType := none
    body :=
      lockEnter ++
        [ .require (.binary .or
            (.binary .gt (.var "amount0Out") (.intLit 0))
            (.binary .gt (.var "amount1Out") (.intLit 0))),
          .letDecl "_reserve0" (some uint112) (.storage reserve0Ref),
          .letDecl "_reserve1" (some uint112) (.storage reserve1Ref),
          .require (.binary .and
            (.binary .lt (.var "amount0Out") (.var "_reserve0"))
            (.binary .lt (.var "amount1Out") (.var "_reserve1"))),
          .letDecl "_token0" (some addr) (.storage token0Ref),
          .letDecl "_token1" (some addr) (.storage token1Ref),
          .require (.binary .and
            (.binary .ne (.var "to") (.var "_token0"))
            (.binary .ne (.var "to") (.var "_token1"))),
          .ite (.binary .gt (.var "amount0Out") (.intLit 0))
            (safeTransferStmts (.var "_token0") (.var "to") (.var "amount0Out") "ok0" "_ret0")
            [],
          .ite (.binary .gt (.var "amount1Out") (.intLit 0))
            (safeTransferStmts (.var "_token1") (.var "to") (.var "amount1Out") "ok1" "_ret1")
            [],
          .ite (.binary .gt (.arrayLength .localVar { base := "data" }) (.intLit 0))
            (checkedExternalCallStmts (.var "to") "uniswapV2Call" (.intLit 0)
              [sender, .var "amount0Out", .var "amount1Out", .var "data"] "_callback")
            [] ] ++
      balanceOfThisStmts (.var "_token0") "balance0" ++
      balanceOfThisStmts (.var "_token1") "balance1" ++
        [ .letDecl "amount0In" (some uint256)
            (.ite
              (.binary .gt (.var "balance0")
                (.binary .sub (.var "_reserve0") (.var "amount0Out")))
              (u256 (.binary .sub (.var "balance0")
                (.binary .sub (.var "_reserve0") (.var "amount0Out"))))
              (.intLit 0)),
          .letDecl "amount1In" (some uint256)
            (.ite
              (.binary .gt (.var "balance1")
                (.binary .sub (.var "_reserve1") (.var "amount1Out")))
              (u256 (.binary .sub (.var "balance1")
                (.binary .sub (.var "_reserve1") (.var "amount1Out"))))
              (.intLit 0)),
          .require (.binary .or
            (.binary .gt (.var "amount0In") (.intLit 0))
            (.binary .gt (.var "amount1In") (.intLit 0))),
          .letDecl "balance0Adjusted" (some uint256)
            (u256 (.binary .sub (u256 (.binary .mul (.var "balance0") (.intLit 1000)))
              (u256 (.binary .mul (.var "amount0In") (.intLit 3))))),
          .letDecl "balance1Adjusted" (some uint256)
            (u256 (.binary .sub (u256 (.binary .mul (.var "balance1") (.intLit 1000)))
              (u256 (.binary .mul (.var "amount1In") (.intLit 3))))),
          .require (.binary .ge
            (u256 (.binary .mul (.var "balance0Adjusted") (.var "balance1Adjusted")))
            (u256 (.binary .mul
              (u256 (.binary .mul (.var "_reserve0") (.var "_reserve1")))
              (.intLit 1000000)))) ] ++
      updateReservesStmts (.var "balance0") (.var "balance1") ++
      lockExit }

def skimTransition : TransitionDecl :=
  { name := "skim"
    params := [{ name := "to", ty := legacyAddr }]
    returnType := none
    body :=
      lockEnter ++
        [ .letDecl "_token0" (some addr) (.storage token0Ref),
          .letDecl "_token1" (some addr) (.storage token1Ref) ] ++
      balanceOfThisStmts (.var "_token0") "balance0" ++
        [ .letDecl "excess0" (some uint256)
            (u256 (.binary .sub (.var "balance0") (.storage reserve0Ref))) ] ++
      safeTransferStmts (.var "_token0") (.var "to") (.var "excess0") "ok0" "_ret0" ++
      balanceOfThisStmts (.var "_token1") "balance1" ++
        [ .letDecl "excess1" (some uint256)
            (u256 (.binary .sub (.var "balance1") (.storage reserve1Ref))) ] ++
      safeTransferStmts (.var "_token1") (.var "to") (.var "excess1") "ok1" "_ret1" ++
      lockExit }

def syncTransition : TransitionDecl :=
  { name := "sync"
    params := []
    returnType := none
    body :=
      lockEnter ++ pairBalanceOfThisStmts "balance0" "balance1" ++
      updateReservesStmts (.var "balance0") (.var "balance1") ++
      lockExit }

/-! ## Contract and config -/

def decodeOptionalBoolOrEmpty? (out : EVM.Bytes) : Option Value :=
  if out.size = 0 then
    some .unit
  else
    match ABI.decodeReturnValue? boolTy out with
    | some (.bool true) => some .unit
    | _ => none

def encodeEcrecoverInput? (args : List Value) : Option EVM.Bytes := do
  let payload <- ABI.encodeABIValues? [bytes32, uint8, bytes32, bytes32] args
  some payload.toByteArray

def uniswapExternalABI : ExternalCallABI where
  encode? := fun name args =>
    if name = "balanceOf" then
      ABI.encodeCallWithSelector? balanceOfSelector [addr] args
    else if name = "transfer" then
      ABI.encodeCallWithSelector? transferSelector [addr, uint256] args
    else if name = "feeTo" then
      match args with
      | [] => some feeToSelector
      | _ => none
    else if name = "uniswapV2Call" then
      ABI.encodeCallWithSelector? uniswapV2CallSelector [addr, uint256, uint256, .bytes] args
    else if name = "ecrecover" then
      encodeEcrecoverInput? args
    else
      none
  decode? := fun name out =>
    if name = "balanceOf" then
      ABI.decodeReturnValue? uint256 out
    else if name = "transfer" then
      decodeOptionalBoolOrEmpty? out
    else if name = "feeTo" then
      ABI.decodeReturnValue? addr out
    else if name = "uniswapV2Call" then
      some .unit
    else if name = "ecrecover" then
      ABI.decodeReturnValue? addr out
    else
      none

def contract : ContractDecl :=
  { name := "UniswapV2Pair"
    storage := storageDecls
    ctor := constructorDecl
    functions :=
      [ approveFunction, transferFunction, mintFunction, burnFunction, safeTransferFunction,
        updateFunction, sqrtFunction, minFunction, mintFeeFunction ]
    transitions :=
      [ swapTransition,                  -- 022c0d9f
        nameTransition,                  -- 06fdde03
        getReservesTransition,           -- 0902f1ac
        approveTransition,               -- 095ea7b3
        token0Transition,                -- 0dfe1681
        totalSupplyTransition,           -- 18160ddd
        transferFromTransition,          -- 23b872dd
        permitTypehashTransition,        -- 30adf81f
        decimalsTransition,              -- 313ce567
        domainSeparatorTransition,       -- 3644e515
        initializeTransition,            -- 485cc955
        price0CumulativeLastTransition,  -- 5909c0d5
        price1CumulativeLastTransition,  -- 5a3d5493
        mintTransition,                  -- 6a627842
        balanceOfTransition,             -- 70a08231
        kLastTransition,                 -- 7464fc3d
        noncesTransition,                -- 7ecebe00
        burnTransition,                  -- 89afcb44
        symbolTransition,                -- 95d89b41
        transferTransition,              -- a9059cbb
        minimumLiquidityTransition,      -- ba9a7a56
        skimTransition,                  -- bc25cf77
        factoryTransition,               -- c45a0155
        token1Transition,                -- d21220a7
        permitTransition,                -- d505accf
        allowanceTransition,             -- dd62ed3e
        syncTransition ] }               -- fff6cae9

def config : Config :=
  { storage := storageLayout
    externalABI := uniswapExternalABI
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

end UniswapV2Pair
