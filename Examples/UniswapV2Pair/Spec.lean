import Solm.Semantics
import Solm.SolidityLayout

/-!
# Uniswap V2 Pair benchmark spec stub

Solm benchmark stub for the unmodified upstream `UniswapV2Pair` contract from
`Uniswap/v2-core` tag `v1.0.1`.

The benchmark intentionally targets the full production Pair runtime, including the inherited
`UniswapV2ERC20` LP-token surface.  The storage layout and ABI surface are explicit and complete;
events are omitted, as in the other examples.

The source bodies for the largest AMM routines are scaffolded rather than proof-ready.  They expose
the benchmark features we want EquiVM to cover: packed reserves, mapping accounting, non-payable
guards, the reentrancy lock, external token balance calls, low-level token transfers, dynamic `bytes`
calldata, and reserve updates.  Legacy-Solidity details not yet represented directly in Solm
(`ecrecover`, `Math.sqrt`, exact `abi.encodeWithSelector` call data, and string return encoding) are
left as TODOs for the later proof pass.
-/

open Solm ABI

namespace UniswapV2Pair

/-! ## Types -/

def uint8Int : IntType := .uint ⟨8, by decide⟩
def uint32Int : IntType := .uint ⟨32, by decide⟩
def uint112Int : IntType := .uint ⟨112, by decide⟩
def uint256Int : IntType := .uint ⟨256, by decide⟩

def bytes32Width : Fin 32 := ⟨31, by decide⟩

def uint8 : ABIType := .elem (.int uint8Int)
def uint32 : ABIType := .elem (.int uint32Int)
def uint112 : ABIType := .elem (.int uint112Int)
def uint256 : ABIType := .elem (.int uint256Int)
def addr : ABIType := .elem .address
def boolTy : ABIType := .elem .bool
def bytes32 : ABIType := .elem (.bytes bytes32Width)

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
def u32 (e : Expr) : Expr := .inRange uint32Int e

def maxUint256 : Int := (2 : Int) ^ 256 - 1
def maxUint112 : Int := (2 : Int) ^ 112 - 1
def twoPow32 : Int := (2 : Int) ^ 32
def minimumLiquidity : Int := 1000

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

/-! ## Shared source-body scaffolding -/

def nonpayable : List Stmt :=
  [ .require (.binary .eq (.env .callvalue) (.intLit 0)) ]

def lockEnter : List Stmt :=
  nonpayable ++
    [ .require (.binary .eq (.storage unlockedRef) (.intLit 1)),
      .assign .storage unlockedRef (.intLit 0) ]

def lockExit : List Stmt :=
  [ .assign .storage unlockedRef (.intLit 1) ]

def updateReservesStmts (balance0 balance1 : Expr) : List Stmt :=
  [ .require (.binary .le balance0 (.intLit maxUint112)),
    .require (.binary .le balance1 (.intLit maxUint112)),
    .letDecl "blockTimestamp" (some uint32) (u32 (.binary .mod now (.intLit twoPow32))),
    .assign .storage reserve0Ref balance0,
    .assign .storage reserve1Ref balance1,
    .assign .storage blockTimestampLastRef (.var "blockTimestamp") ]

def safeTransferStmts (token _recipient _value : Expr) (okVar dataVar : Ident) : List Stmt :=
  -- TODO: replace empty calldata with exact `abi.encodeWithSelector(transfer(address,uint256), ...)`.
  [ .lowLevelCall token (.intLit 0) (.bytesLit ByteArray.empty) okVar dataVar,
    .require (.var okVar) ]

/-! ## Constructor -/

def constructorDecl : ConstructorDecl :=
  { params := []
    body :=
      [ .assign .storage factoryRef sender,
        .assign .storage unlockedRef (.intLit 1) ] }

/-! ## LP-token inherited public surface -/

def nameTransition : TransitionDecl :=
  { name := "name", params := [], returnType := some .string, body := nonpayable }

def symbolTransition : TransitionDecl :=
  { name := "symbol", params := [], returnType := some .string, body := nonpayable }

def decimalsTransition : TransitionDecl :=
  { name := "decimals", params := [], returnType := some uint8
    body := nonpayable ++ [ .return (.intLit 18) ] }

def totalSupplyTransition : TransitionDecl :=
  { name := "totalSupply", params := [], returnType := some uint256
    body := nonpayable ++ [ .return (.storage totalSupplyRef) ] }

def balanceOfTransition : TransitionDecl :=
  { name := "balanceOf"
    params := [{ name := "owner", ty := addr }]
    returnType := some uint256
    body := nonpayable ++ [ .return (.storage (balanceOfRef (.var "owner"))) ] }

def allowanceTransition : TransitionDecl :=
  { name := "allowance"
    params := [{ name := "owner", ty := addr }, { name := "spender", ty := addr }]
    returnType := some uint256
    body := nonpayable ++ [ .return (.storage (allowanceRef (.var "owner") (.var "spender"))) ] }

def approveTransition : TransitionDecl :=
  { name := "approve"
    params := [{ name := "spender", ty := addr }, { name := "value", ty := uint256 }]
    returnType := some boolTy
    body :=
      nonpayable ++
        [ .assign .storage (allowanceRef sender (.var "spender")) (.var "value"),
          .return (.boolLit true) ] }

def transferTransition : TransitionDecl :=
  { name := "transfer"
    params := [{ name := "to", ty := addr }, { name := "value", ty := uint256 }]
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
    params := [{ name := "from", ty := addr }, { name := "to", ty := addr },
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
    body :=
      nonpayable ++
        [ .return (.fixedBytesLit bytes32Width
            [ 0x6e, 0x71, 0xed, 0xae, 0x12, 0xb1, 0xb9, 0x7f,
              0x4d, 0x1f, 0x60, 0x37, 0x0f, 0xef, 0x10, 0x10,
              0x5f, 0xa2, 0x77, 0x6a, 0xe0, 0x12, 0x61, 0x14,
              0xa1, 0x69, 0xc6, 0x48, 0x45, 0xd6, 0x12, 0x6c ]) ] }

def noncesTransition : TransitionDecl :=
  { name := "nonces"
    params := [{ name := "owner", ty := addr }]
    returnType := some uint256
    body := nonpayable ++ [ .return (.storage (noncesRef (.var "owner"))) ] }

def permitTransition : TransitionDecl :=
  { name := "permit"
    params :=
      [ { name := "owner", ty := addr }, { name := "spender", ty := addr },
        { name := "value", ty := uint256 }, { name := "deadline", ty := uint256 },
        { name := "v", ty := uint8 }, { name := "r", ty := bytes32 }, { name := "s", ty := bytes32 } ]
    returnType := none
    body :=
      -- TODO: model `ecrecover` and the exact EIP-712 digest check.
      nonpayable ++
        [ .require (.binary .ge (.var "deadline") now),
          .assign .storage (noncesRef (.var "owner"))
            (u256 (.binary .add (.storage (noncesRef (.var "owner"))) (.intLit 1))),
          .assign .storage (allowanceRef (.var "owner") (.var "spender")) (.var "value") ] }

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
    params := [{ name := "_token0", ty := addr }, { name := "_token1", ty := addr }]
    returnType := none
    body :=
      nonpayable ++
        [ .require (.binary .eq sender (.storage factoryRef)),
          .assign .storage token0Ref (.var "_token0"),
          .assign .storage token1Ref (.var "_token1") ] }

def mintTransition : TransitionDecl :=
  { name := "mint"
    params := [{ name := "to", ty := addr }]
    returnType := some uint256
    body :=
      lockEnter ++
        [ .externalCall (.storage token0Ref) "balanceOf" (.intLit 0) [this] "balance0",
          .externalCall (.storage token1Ref) "balanceOf" (.intLit 0) [this] "balance1",
          .letDecl "amount0" (some uint256)
            (.binary .sub (.var "balance0") (.storage reserve0Ref)),
          .letDecl "amount1" (some uint256)
            (.binary .sub (.var "balance1") (.storage reserve1Ref)),
          -- TODO: replace this liquidity placeholder with `sqrt`/`min` logic plus fee minting.
          .letDecl "liquidity" (some uint256)
            (.ite (.binary .eq (.storage totalSupplyRef) (.intLit 0))
              (.binary .sub (u256 (.binary .mul (.var "amount0") (.var "amount1")))
                (.intLit minimumLiquidity))
              (.var "amount0")),
          .require (.binary .gt (.var "liquidity") (.intLit 0)),
          .assign .storage totalSupplyRef
            (u256 (.binary .add (.storage totalSupplyRef) (.var "liquidity"))),
          .assign .storage (balanceOfRef (.var "to"))
            (u256 (.binary .add (.storage (balanceOfRef (.var "to"))) (.var "liquidity"))) ] ++
      updateReservesStmts (.var "balance0") (.var "balance1") ++
      lockExit ++
        [ .return (.var "liquidity") ] }

def burnTransition : TransitionDecl :=
  { name := "burn"
    params := [{ name := "to", ty := addr }]
    returnType := some (.tuple [uint256, uint256])
    body :=
      lockEnter ++
        [ .externalCall (.storage token0Ref) "balanceOf" (.intLit 0) [this] "balance0",
          .externalCall (.storage token1Ref) "balanceOf" (.intLit 0) [this] "balance1",
          .letDecl "liquidity" (some uint256) (.storage (balanceOfRef this)),
          .letDecl "_totalSupply" (some uint256) (.storage totalSupplyRef),
          .require (.binary .gt (.var "_totalSupply") (.intLit 0)),
          .letDecl "amount0" (some uint256)
            (.binary .div (.binary .mul (.var "liquidity") (.var "balance0"))
              (.var "_totalSupply")),
          .letDecl "amount1" (some uint256)
            (.binary .div (.binary .mul (.var "liquidity") (.var "balance1"))
              (.var "_totalSupply")),
          .require (.binary .and
            (.binary .gt (.var "amount0") (.intLit 0))
            (.binary .gt (.var "amount1") (.intLit 0))),
          .assign .storage (balanceOfRef this)
            (.binary .sub (.storage (balanceOfRef this)) (.var "liquidity")),
          .assign .storage totalSupplyRef
            (.binary .sub (.storage totalSupplyRef) (.var "liquidity")) ] ++
      safeTransferStmts (.storage token0Ref) (.var "to") (.var "amount0") "ok0" "_ret0" ++
      safeTransferStmts (.storage token1Ref) (.var "to") (.var "amount1") "ok1" "_ret1" ++
        [ .externalCall (.storage token0Ref) "balanceOf" (.intLit 0) [this] "newBalance0",
          .externalCall (.storage token1Ref) "balanceOf" (.intLit 0) [this] "newBalance1" ] ++
      updateReservesStmts (.var "newBalance0") (.var "newBalance1") ++
      lockExit ++
        [ .return (.tupleLit [.var "amount0", .var "amount1"]) ] }

def swapTransition : TransitionDecl :=
  { name := "swap"
    params :=
      [ { name := "amount0Out", ty := uint256 }, { name := "amount1Out", ty := uint256 },
        { name := "to", ty := addr }, { name := "data", ty := .bytes } ]
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
          .require (.binary .and
            (.binary .ne (.var "to") (.storage token0Ref))
            (.binary .ne (.var "to") (.storage token1Ref))),
          .ite (.binary .gt (.var "amount0Out") (.intLit 0))
            (safeTransferStmts (.storage token0Ref) (.var "to") (.var "amount0Out") "ok0" "_ret0")
            [],
          .ite (.binary .gt (.var "amount1Out") (.intLit 0))
            (safeTransferStmts (.storage token1Ref) (.var "to") (.var "amount1Out") "ok1" "_ret1")
            [],
          -- TODO: replace raw `data` with encoded `uniswapV2Call(sender, amount0Out, amount1Out, data)`.
          .ite (.binary .gt (.arrayLength .localVar { base := "data" }) (.intLit 0))
            [ .lowLevelCall (.var "to") (.intLit 0) (.var "data") "callbackOk" "_callbackRet",
              .require (.var "callbackOk") ]
            [],
          .externalCall (.storage token0Ref) "balanceOf" (.intLit 0) [this] "balance0",
          .externalCall (.storage token1Ref) "balanceOf" (.intLit 0) [this] "balance1",
          .letDecl "amount0In" (some uint256)
            (.ite
              (.binary .gt (.var "balance0")
                (.binary .sub (.var "_reserve0") (.var "amount0Out")))
              (.binary .sub (.var "balance0")
                (.binary .sub (.var "_reserve0") (.var "amount0Out")))
              (.intLit 0)),
          .letDecl "amount1In" (some uint256)
            (.ite
              (.binary .gt (.var "balance1")
                (.binary .sub (.var "_reserve1") (.var "amount1Out")))
              (.binary .sub (.var "balance1")
                (.binary .sub (.var "_reserve1") (.var "amount1Out")))
              (.intLit 0)),
          .require (.binary .or
            (.binary .gt (.var "amount0In") (.intLit 0))
            (.binary .gt (.var "amount1In") (.intLit 0))),
          .letDecl "balance0Adjusted" (some uint256)
            (.binary .sub (.binary .mul (.var "balance0") (.intLit 1000))
              (.binary .mul (.var "amount0In") (.intLit 3))),
          .letDecl "balance1Adjusted" (some uint256)
            (.binary .sub (.binary .mul (.var "balance1") (.intLit 1000))
              (.binary .mul (.var "amount1In") (.intLit 3))),
          .require (.binary .ge
            (.binary .mul (.var "balance0Adjusted") (.var "balance1Adjusted"))
            (.binary .mul (.binary .mul (.var "_reserve0") (.var "_reserve1"))
              (.intLit 1000000))) ] ++
      updateReservesStmts (.var "balance0") (.var "balance1") ++
      lockExit }

def skimTransition : TransitionDecl :=
  { name := "skim"
    params := [{ name := "to", ty := addr }]
    returnType := none
    body :=
      lockEnter ++
        [ .externalCall (.storage token0Ref) "balanceOf" (.intLit 0) [this] "balance0",
          .externalCall (.storage token1Ref) "balanceOf" (.intLit 0) [this] "balance1",
          .letDecl "excess0" (some uint256)
            (.binary .sub (.var "balance0") (.storage reserve0Ref)),
          .letDecl "excess1" (some uint256)
            (.binary .sub (.var "balance1") (.storage reserve1Ref)) ] ++
      safeTransferStmts (.storage token0Ref) (.var "to") (.var "excess0") "ok0" "_ret0" ++
      safeTransferStmts (.storage token1Ref) (.var "to") (.var "excess1") "ok1" "_ret1" ++
      lockExit }

def syncTransition : TransitionDecl :=
  { name := "sync"
    params := []
    returnType := none
    body :=
      lockEnter ++
        [ .externalCall (.storage token0Ref) "balanceOf" (.intLit 0) [this] "balance0",
          .externalCall (.storage token1Ref) "balanceOf" (.intLit 0) [this] "balance1" ] ++
      updateReservesStmts (.var "balance0") (.var "balance1") ++
      lockExit }

/-! ## Contract and config -/

def contract : ContractDecl :=
  { name := "UniswapV2Pair"
    storage := storageDecls
    ctor := constructorDecl
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
    externalABI := defaultExternalCallABI
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

end UniswapV2Pair
