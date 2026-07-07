import Solm.Semantics
import Solm.SolidityLayout
import Benchmarks.Klima.StringLayout

/-!
# KlimaDAO KlimaToken benchmark spec

Solm benchmark scaffold for KlimaDAO `src/protocol/tokens/regular/KlimaToken.sol` (solc 0.7.5), the
full inherited contract: OpenZeppelin-style ERC20 with `SafeMath` checked arithmetic, EIP-2612
`permit` (EIP-712 digest + `ecrecover` precompile), `Ownable`/`VaultOwned` access control, and a
`TWAPOracleUpdater` layer whose `_beforeTokenTransfer` hook fires an external `twapOracle.updateTWAP`
call whenever the sender or recipient is a registered TWAP source (an `EnumerableSet.AddressSet`).

Events are omitted (the equivalence observes neither logs nor revert data).  Modeling choices:

- `SafeMath.add`/`sub` are the explicit `require`-guarded uint256 range-cast forms.
- `_name`/`_symbol` are mutable compact `string` storage read/written through the pre-0.8 total
  decode in `StringLayout.lean`; `_decimals` is a `uint8` storage read.
- `_nonces` (`mapping(address => Counters.Counter)`) is modeled as `mapping(address => uint256)`:
  the single-word `Counter._value` at offset 0 has the identical slot `keccak(addr ‖ 6)`.
- `_dexPoolsTWAPSources` (`EnumerableSet.AddressSet`) is flattened to its two solc slots: `_values`
  (`bytes32[]` slot 10) and `_indexes` (`mapping(bytes32 => uint256)` slot 11), with the set keys
  `bytes32(uint256(addr))` exactly as the library stores them.
- The `permit` nonce post-increment is unchecked (0.7 `Counter.increment`), so it wraps at 2^256.
- `twapOracle.updateTWAP` is an `EXTCODESIZE`-guarded external `CALL` whose ignored `bool` return is
  decoded through the legacy coder (size-check only, matching the discarded runtime decode).
-/

open Solm ABI

namespace Benchmarks.Klima

/-! ## Types -/

def uint8Int : IntType := .uint ⟨8, by decide⟩
def uint256Int : IntType := .uint ⟨256, by decide⟩
def bytes32Width : Fin 32 := ⟨31, by decide⟩

def uint8 : ABIType := .elem (.int uint8Int)
def uint256 : ABIType := .elem (.int uint256Int)
def addr : ABIType := .elem .address
def boolTy : ABIType := .elem .bool
def bytes32 : ABIType := .elem (.bytes bytes32Width)
def stringTy : ABIType := .string

def uint8St : StorageType := .elem (.int uint8Int)
def uint256St : StorageType := .elem (.int uint256Int)
def addrSt : StorageType := .elem .address
def bytes32St : StorageType := .elem (.bytes bytes32Width)

def sender : Expr := .env .caller
def zeroAddr : Expr := .cast (.intLit 0) addrSt
def ecrecoverPrecompile : Expr := .cast (.intLit 1) addrSt
def maxUint256 : Int := (2 : Int) ^ 256 - 1

def u256 (e : Expr) : Expr := .inRange uint256Int e
def add256 (x y : Expr) : Expr := u256 (.binary .add x y)
def sub256 (x y : Expr) : Expr := u256 (.binary .sub x y)

def addrAsU256 (e : Expr) : Expr := .cast e uint256St
/-- The `bytes32(uint256(addr))` set key form the EnumerableSet library stores. -/
def key (e : Expr) : Expr := .cast (addrAsU256 e) bytes32St

/-- `SafeMath.add(a, b)` overflow guard: `c = a + b; require(c >= a)`. -/
def safeAddChk (a b : Expr) : Stmt := .require (.binary .ge (add256 a b) a)
/-- `SafeMath.sub(a, b)` underflow guard: `require(b <= a)`. -/
def safeSubChk (a b : Expr) : Stmt := .require (.binary .le b a)

/-! ## Storage references -/

def balancesRef (usr : Expr) : StorageRef := { base := "balances", steps := [.mindex usr] }
def allowanceRef (owner spender : Expr) : StorageRef :=
  { base := "allowances", steps := [.mindex owner, .mindex spender] }
def totalSupplyRef : StorageRef := { base := "totalSupply" }
def nameRef : StorageRef := { base := "name" }
def symbolRef : StorageRef := { base := "symbol" }
def decimalsRef : StorageRef := { base := "decimals" }
def noncesRef (usr : Expr) : StorageRef := { base := "nonces", steps := [.mindex usr] }
def domainSeparatorRef : StorageRef := { base := "DOMAIN_SEPARATOR" }
def ownerRef : StorageRef := { base := "owner" }
def vaultRef : StorageRef := { base := "vault" }
def dexValuesRef : StorageRef := { base := "dexValues" }
def dexElemRef (i : Expr) : StorageRef := { base := "dexValues", steps := [.aindex i] }
def dexIndexRef (k : Expr) : StorageRef := { base := "dexIndexes", steps := [.mindex k] }
def twapOracleRef : StorageRef := { base := "twapOracle" }
def twapEpochPeriodRef : StorageRef := { base := "twapEpochPeriod" }

/-! ## Storage declarations and layout -/

def storageDecls : List StorageDecl :=
  [ { name := "balances", ty := .mapping .address uint256St },
    { name := "allowances", ty := .mapping .address (.mapping .address uint256St) },
    { name := "totalSupply", ty := uint256St },
    { name := "name", ty := .string },
    { name := "symbol", ty := .string },
    { name := "decimals", ty := uint8St },
    { name := "nonces", ty := .mapping .address uint256St },
    { name := "DOMAIN_SEPARATOR", ty := bytes32St },
    { name := "owner", ty := addrSt },
    { name := "vault", ty := addrSt },
    { name := "dexValues", ty := .dynamicArray bytes32St },
    { name := "dexIndexes", ty := .mapping (.bytes bytes32Width) uint256St },
    { name := "twapOracle", ty := addrSt },
    { name := "twapEpochPeriod", ty := uint256St } ]

def mapSlot (key baseSlot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC (key.toByteArray ++ baseSlot.toByteArray))

def balancesSlot (usr : KeyValue) : Ethereum.UInt256 := mapSlot (keyValueToWord usr) ⟨0⟩
def allowanceOwnerSlot (owner : KeyValue) : Ethereum.UInt256 := mapSlot (keyValueToWord owner) ⟨1⟩
def allowanceSlot (owner spender : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord spender) (allowanceOwnerSlot owner)
def noncesSlot (usr : KeyValue) : Ethereum.UInt256 := mapSlot (keyValueToWord usr) ⟨6⟩
def dexIndexSlot (k : KeyValue) : Ethereum.UInt256 := mapSlot (keyValueToWord k) ⟨11⟩
/-- Dynamic-array data region: elements of `_values` (slot 10) live at `keccak(10) + i`. -/
def dexValuesDataSlot : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC (Ethereum.UInt256.toByteArray ⟨10⟩))
def dexElemSlot (i : KeyValue) : Ethereum.UInt256 := dexValuesDataSlot + keyValueToWord i

def wordLoc (slot : Ethereum.UInt256) (ty : ElemType) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, type := ty }
def addrLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 20, hbound := by decide, type := .address }
def uint8Loc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 1, hbound := by decide, type := .int uint8Int }
def bytes32Loc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, type := .bytes bytes32Width }

def storageLayoutRaw : EvaledStorageRef -> EVM.State -> Option StorageLoc
  | { base := "balances", steps := [.mindex usr] }, _ =>
      some (wordLoc (balancesSlot usr) (.int uint256Int))
  | { base := "allowances", steps := [.mindex owner, .mindex spender] }, _ =>
      some (wordLoc (allowanceSlot owner spender) (.int uint256Int))
  | { base := "totalSupply", steps := [] }, _ => some (wordLoc ⟨2⟩ (.int uint256Int))
  | { base := "name", steps := [.length] }, evm => some (bytesLikeLengthLoc ⟨3⟩ evm)
  | { base := "symbol", steps := [.length] }, evm => some (bytesLikeLengthLoc ⟨4⟩ evm)
  | { base := "decimals", steps := [] }, _ => some (uint8Loc ⟨5⟩)
  | { base := "nonces", steps := [.mindex usr] }, _ =>
      some (wordLoc (noncesSlot usr) (.int uint256Int))
  | { base := "DOMAIN_SEPARATOR", steps := [] }, _ => some (bytes32Loc ⟨7⟩)
  | { base := "owner", steps := [] }, _ => some (addrLoc ⟨8⟩)
  | { base := "vault", steps := [] }, _ => some (addrLoc ⟨9⟩)
  | { base := "dexValues", steps := [.length] }, _ => some (wordLoc ⟨10⟩ (.int uint256Int))
  | { base := "dexValues", steps := [.aindex i] }, _ => some (bytes32Loc (dexElemSlot i))
  | { base := "dexIndexes", steps := [.mindex k] }, _ =>
      some (wordLoc (dexIndexSlot k) (.int uint256Int))
  | { base := "twapOracle", steps := [] }, _ => some (addrLoc ⟨12⟩)
  | { base := "twapEpochPeriod", steps := [] }, _ => some (wordLoc ⟨13⟩ (.int uint256Int))
  | _, _ => none

def storageLayout : StorageLayout :=
  klimaStorageLayout storageLayoutRaw

/-! ## External ABI for `ITWAPOracle` -/

def selectorBytes (a b c d : UInt8) : ByteArray := ⟨#[a, b, c, d]⟩
def updateTWAPSelector : ByteArray := selectorBytes 0xef 0x51 0xa9 0x82

/-- The discarded `updateTWAP` `bool` return is decoded through the legacy coder: a size check only
    (no `0/1` validation), matching the runtime's `returndatasize >= 32` guard. -/
def decodeReturn? (ty : ABIType) (out : EVM.Bytes) : Option (List Value) :=
  (ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 ty out).map (fun v => [v])

def klimaExternalABI : ExternalCallABI where
  encode? := fun name args =>
    if name = "updateTWAP" then
      ABI.encodeCallWithSelector? updateTWAPSelector [addr, uint256] args
    else none
  decode? := fun name out =>
    if name = "updateTWAP" then decodeReturn? boolTy out
    else none

/-! ## Shared source patterns -/

def nonpayable : List Stmt :=
  [ .require (.binary .eq (.env .callvalue) (.intLit 0)) ]

def onlyOwner : List Stmt :=
  [ .require (.binary .eq (.storage ownerRef) sender) ]

def onlyVault : List Stmt :=
  [ .require (.binary .eq (.storage vaultRef) sender) ]

/-- `_balances[usr] = _balances[usr].sub(amount)` (SafeMath). -/
def debitBalance (usr amount : Expr) : List Stmt :=
  [ safeSubChk (.storage (balancesRef usr)) amount,
    .assign .storage (balancesRef usr) (sub256 (.storage (balancesRef usr)) amount) ]

/-- `_balances[usr] = _balances[usr].add(amount)` (SafeMath). -/
def creditBalance (usr amount : Expr) : List Stmt :=
  [ safeAddChk (.storage (balancesRef usr)) amount,
    .assign .storage (balancesRef usr) (add256 (.storage (balancesRef usr)) amount) ]

/-- `_approve(owner, spender, amount)`. -/
def approveBody (owner spender amount : Expr) : List Stmt :=
  [ .require (.binary .ne owner zeroAddr),
    .require (.binary .ne spender zeroAddr),
    .assign .storage (allowanceRef owner spender) amount ]

/-- `twapOracle.updateTWAP(pool, twapEpochPeriod)` with solc's high-level-call `EXTCODESIZE` guard. -/
def guardedUpdateTWAP (pool : Expr) : List Stmt :=
  [ .require (.binary .gt (.extCodeSize (.storage twapOracleRef)) (.intLit 0)),
    .externalCall (.storage twapOracleRef) "updateTWAP" (.intLit 0)
      [pool, .storage twapEpochPeriodRef] "_twapRet" (perm := true) ]

/-- `_uodateTWAPOracle(pool, ·)`: calls only if `pool` is (still) in the set. -/
def uodateTWAPOracle (pool : Expr) : List Stmt :=
  [ .ite (.binary .ne (.storage (dexIndexRef (key pool))) (.intLit 0))
      (guardedUpdateTWAP pool) [] ]

/-- `_beforeTokenTransfer(from, to, ·)`: update TWAP for `from` if it is a source, else for `to`. -/
def beforeTokenTransfer (from_ to_ : Expr) : List Stmt :=
  [ .ite (.binary .ne (.storage (dexIndexRef (key from_))) (.intLit 0))
      (uodateTWAPOracle from_)
      [ .ite (.binary .ne (.storage (dexIndexRef (key to_))) (.intLit 0))
          (uodateTWAPOracle to_) [] ] ]

/-- `_transfer(from, to, amount)`. -/
def transferBody (from_ to_ amount : Expr) : List Stmt :=
  [ .require (.binary .ne from_ zeroAddr),
    .require (.binary .ne to_ zeroAddr) ] ++
  beforeTokenTransfer from_ to_ ++
  debitBalance from_ amount ++
  creditBalance to_ amount

/-- `_mint(account, amount)`; `_beforeTokenTransfer(address(this), account, ·)`. -/
def mintBody (account amount : Expr) : List Stmt :=
  [ .require (.binary .ne account zeroAddr) ] ++
  beforeTokenTransfer (.env .this) account ++
  [ safeAddChk (.storage totalSupplyRef) amount,
    .assign .storage totalSupplyRef (add256 (.storage totalSupplyRef) amount) ] ++
  creditBalance account amount

/-- `_burn(account, amount)`; `_beforeTokenTransfer(account, address(0), ·)`. -/
def burnBody (account amount : Expr) : List Stmt :=
  [ .require (.binary .ne account zeroAddr) ] ++
  beforeTokenTransfer account zeroAddr ++
  debitBalance account amount ++
  [ safeSubChk (.storage totalSupplyRef) amount,
    .assign .storage totalSupplyRef (sub256 (.storage totalSupplyRef) amount) ]

/-- `_burnFrom(account, amount)`: spend caller's allowance, then `_burn`. -/
def burnFromBody (account amount : Expr) : List Stmt :=
  [ safeSubChk (.storage (allowanceRef account sender)) amount ] ++
  approveBody account sender (sub256 (.storage (allowanceRef account sender)) amount) ++
  burnBody account amount

/-! ## EIP-712 / permit expressions -/

def permitTypehashBytes : List UInt8 :=
  [ 110, 113, 237, 174, 18, 177, 185, 127, 77, 31, 96, 55, 15, 239, 16, 16,
    95, 162, 250, 174, 1, 38, 17, 74, 22, 156, 100, 132, 93, 97, 38, 201 ]

def permitTypehashExpr : Expr := .fixedBytesLit bytes32Width permitTypehashBytes

def eip191Prefix : Expr := .bytesLit ⟨#[25, 1]⟩

/-- `keccak256(abi.encode(keccak(EIP712Domain type), keccak(name), keccak("1"), chainid, this))`. -/
def domainSeparatorExpr : Expr :=
  .keccak256
    (.abiEncodePacked
      [ (bytes32, .keccak256
          (.bytesLit
            (String.toByteArray
              "EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"))),
        (bytes32, .keccak256 (.bytesLit (String.toByteArray "Klima DAO"))),
        (bytes32, .keccak256 (.bytesLit (String.toByteArray "1"))),
        (uint256, .env .chainid),
        (uint256, addrAsU256 (.env .this)) ])

/-- `keccak256(abi.encode(PERMIT_TYPEHASH, owner, spender, amount, nonces[owner], deadline))`. -/
def permitStructHashExpr : Expr :=
  .keccak256
    (.abiEncodePacked
      [ (bytes32, permitTypehashExpr),
        (uint256, addrAsU256 (.var "owner")),
        (uint256, addrAsU256 (.var "spender")),
        (uint256, .var "amount"),
        (uint256, .storage (noncesRef (.var "owner"))),
        (uint256, .var "deadline") ])

/-- `keccak256(abi.encodePacked(uint16(0x1901), DOMAIN_SEPARATOR, hashStruct))`. -/
def permitDigestExpr : Expr :=
  .keccak256
    (.abiEncodePacked
      [ (ABIType.bytes, eip191Prefix),
        (bytes32, .storage domainSeparatorRef),
        (bytes32, .var "hashStruct") ])

def ecrecoverCalldataExpr : Expr :=
  .abiEncodePacked
    [ (bytes32, .var "digest"),
      (uint256, .var "v"),
      (bytes32, .var "r"),
      (bytes32, .var "s") ]

/-! ## Constructor -/

-- `constructor() Divine("Klima DAO", "KLIMA", 9) {}`: sets name/symbol/decimals (ERC20), the EIP-712
-- `DOMAIN_SEPARATOR` (ERC20Permit, reading the just-set name), and `_owner = msg.sender` (Ownable).
def constructorDecl : ConstructorDecl :=
  { params := []
    body :=
      nonpayable ++
      [ .assign .storage nameRef (.bytesLit (String.toByteArray "Klima DAO")),
        .assign .storage symbolRef (.bytesLit (String.toByteArray "KLIMA")),
        .assign .storage decimalsRef (.intLit 9),
        .assign .storage domainSeparatorRef domainSeparatorExpr,
        .assign .storage ownerRef sender ] }

/-! ## Public ABI surface: constants and getters -/

def nameTransition : TransitionDecl :=
  { name := "name", params := [], returnType := [stringTy],
    body := nonpayable ++ [ .return [.storage nameRef] ] }

def symbolTransition : TransitionDecl :=
  { name := "symbol", params := [], returnType := [stringTy],
    body := nonpayable ++ [ .return [.storage symbolRef] ] }

def decimalsTransition : TransitionDecl :=
  { name := "decimals", params := [], returnType := [uint8],
    body := nonpayable ++ [ .return [.storage decimalsRef] ] }

def totalSupplyTransition : TransitionDecl :=
  { name := "totalSupply", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage totalSupplyRef] ] }

def balanceOfTransition : TransitionDecl :=
  { name := "balanceOf", params := [{ name := "account", ty := addr }], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage (balancesRef (.var "account"))] ] }

def allowanceTransition : TransitionDecl :=
  { name := "allowance"
    params := [{ name := "owner", ty := addr }, { name := "spender", ty := addr }]
    returnType := [uint256]
    body := nonpayable ++ [ .return [.storage (allowanceRef (.var "owner") (.var "spender"))] ] }

def noncesTransition : TransitionDecl :=
  { name := "nonces", params := [{ name := "owner", ty := addr }], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage (noncesRef (.var "owner"))] ] }

def domainSeparatorTransition : TransitionDecl :=
  { name := "DOMAIN_SEPARATOR", params := [], returnType := [bytes32],
    body := nonpayable ++ [ .return [.storage domainSeparatorRef] ] }

def permitTypehashTransition : TransitionDecl :=
  { name := "PERMIT_TYPEHASH", params := [], returnType := [bytes32],
    body := nonpayable ++ [ .return [permitTypehashExpr] ] }

def ownerTransition : TransitionDecl :=
  { name := "owner", params := [], returnType := [addr],
    body := nonpayable ++ [ .return [.storage ownerRef] ] }

def vaultTransition : TransitionDecl :=
  { name := "vault", params := [], returnType := [addr],
    body := nonpayable ++ [ .return [.storage vaultRef] ] }

def twapOracleTransition : TransitionDecl :=
  { name := "twapOracle", params := [], returnType := [addr],
    body := nonpayable ++ [ .return [.storage twapOracleRef] ] }

def twapEpochPeriodTransition : TransitionDecl :=
  { name := "twapEpochPeriod", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage twapEpochPeriodRef] ] }

/-! ## Public ABI surface: ERC20 actions -/

def approveTransition : TransitionDecl :=
  { name := "approve"
    params := [{ name := "spender", ty := addr }, { name := "amount", ty := uint256 }]
    returnType := [boolTy]
    body := nonpayable ++ approveBody sender (.var "spender") (.var "amount") ++
      [ .return [.boolLit true] ] }

def transferTransition : TransitionDecl :=
  { name := "transfer"
    params := [{ name := "recipient", ty := addr }, { name := "amount", ty := uint256 }]
    returnType := [boolTy]
    body := nonpayable ++ transferBody sender (.var "recipient") (.var "amount") ++
      [ .return [.boolLit true] ] }

def transferFromTransition : TransitionDecl :=
  { name := "transferFrom"
    params :=
      [ { name := "sender_", ty := addr }, { name := "recipient", ty := addr },
        { name := "amount", ty := uint256 } ]
    returnType := [boolTy]
    body :=
      nonpayable ++
      transferBody (.var "sender_") (.var "recipient") (.var "amount") ++
      [ safeSubChk (.storage (allowanceRef (.var "sender_") sender)) (.var "amount") ] ++
      approveBody (.var "sender_") sender
        (sub256 (.storage (allowanceRef (.var "sender_") sender)) (.var "amount")) ++
      [ .return [.boolLit true] ] }

def increaseAllowanceTransition : TransitionDecl :=
  { name := "increaseAllowance"
    params := [{ name := "spender", ty := addr }, { name := "addedValue", ty := uint256 }]
    returnType := [boolTy]
    body :=
      nonpayable ++
      [ safeAddChk (.storage (allowanceRef sender (.var "spender"))) (.var "addedValue") ] ++
      approveBody sender (.var "spender")
        (add256 (.storage (allowanceRef sender (.var "spender"))) (.var "addedValue")) ++
      [ .return [.boolLit true] ] }

def decreaseAllowanceTransition : TransitionDecl :=
  { name := "decreaseAllowance"
    params := [{ name := "spender", ty := addr }, { name := "subtractedValue", ty := uint256 }]
    returnType := [boolTy]
    body :=
      nonpayable ++
      [ safeSubChk (.storage (allowanceRef sender (.var "spender"))) (.var "subtractedValue") ] ++
      approveBody sender (.var "spender")
        (sub256 (.storage (allowanceRef sender (.var "spender"))) (.var "subtractedValue")) ++
      [ .return [.boolLit true] ] }

def mintTransition : TransitionDecl :=
  { name := "mint"
    params := [{ name := "account", ty := addr }, { name := "amount", ty := uint256 }]
    returnType := []
    body := nonpayable ++ onlyVault ++ mintBody (.var "account") (.var "amount") }

def burnTransition : TransitionDecl :=
  { name := "burn"
    params := [{ name := "amount", ty := uint256 }]
    returnType := []
    body := nonpayable ++ burnBody sender (.var "amount") }

def burnFromTransition : TransitionDecl :=
  { name := "burnFrom"
    params := [{ name := "account", ty := addr }, { name := "amount", ty := uint256 }]
    returnType := []
    body := nonpayable ++ burnFromBody (.var "account") (.var "amount") }

-- `_burnFrom` is (accidentally) `public` in the source, so it is part of the ABI surface with the
-- same body `burnFrom` delegates to.
def burnFromInternalTransition : TransitionDecl :=
  { name := "_burnFrom"
    params := [{ name := "account", ty := addr }, { name := "amount", ty := uint256 }]
    returnType := []
    body := nonpayable ++ burnFromBody (.var "account") (.var "amount") }

def permitTransition : TransitionDecl :=
  { name := "permit"
    params :=
      [ { name := "owner", ty := addr }, { name := "spender", ty := addr },
        { name := "amount", ty := uint256 }, { name := "deadline", ty := uint256 },
        { name := "v", ty := uint8 }, { name := "r", ty := bytes32 },
        { name := "s", ty := bytes32 } ]
    returnType := []
    body :=
      nonpayable ++
      [ .require (.binary .le (.env .timestamp) (.var "deadline")),
        .letDecl "hashStruct" (some bytes32) permitStructHashExpr,
        .letDecl "digest" (some bytes32) permitDigestExpr,
        .lowLevelCall ecrecoverPrecompile (.intLit 0) ecrecoverCalldataExpr
          "ecrecoverSuccess" "ecrecoverData" false,
        .require (.var "ecrecoverSuccess"),
        .letDecl "signer" (some addr) (.abiDecode addr (.var "ecrecoverData")),
        .require
          (.binary .and
            (.binary .ne (.var "signer") zeroAddr)
            (.binary .eq (.var "signer") (.var "owner"))),
        .assign .storage (noncesRef (.var "owner"))
          (add256 (.storage (noncesRef (.var "owner"))) (.intLit 1)) ] ++
      approveBody (.var "owner") (.var "spender") (.var "amount") }

/-! ## Public ABI surface: access control and TWAP config -/

def transferOwnershipTransition : TransitionDecl :=
  { name := "transferOwnership"
    params := [{ name := "newOwner", ty := addr }]
    returnType := []
    body :=
      nonpayable ++ onlyOwner ++
      [ .require (.binary .ne (.var "newOwner") zeroAddr),
        .assign .storage ownerRef (.var "newOwner") ] }

def renounceOwnershipTransition : TransitionDecl :=
  { name := "renounceOwnership"
    params := []
    returnType := []
    body := nonpayable ++ onlyOwner ++ [ .assign .storage ownerRef zeroAddr ] }

def setVaultTransition : TransitionDecl :=
  { name := "setVault"
    params := [{ name := "vault_", ty := addr }]
    returnType := [boolTy]
    body :=
      nonpayable ++ onlyOwner ++
      [ .assign .storage vaultRef (.var "vault_"),
        .return [.boolLit true] ] }

def changeTWAPOracleTransition : TransitionDecl :=
  { name := "changeTWAPOracle"
    params := [{ name := "newTWAPOracle", ty := addr }]
    returnType := []
    body := nonpayable ++ onlyOwner ++ [ .assign .storage twapOracleRef (.var "newTWAPOracle") ] }

def changeTWAPEpochPeriodTransition : TransitionDecl :=
  { name := "changeTWAPEpochPeriod"
    params := [{ name := "newTWAPEpochPeriod", ty := uint256 }]
    returnType := []
    body :=
      nonpayable ++ onlyOwner ++
      [ .require (.binary .gt (.var "newTWAPEpochPeriod") (.intLit 0)),
        .assign .storage twapEpochPeriodRef (.var "newTWAPEpochPeriod") ] }

-- `require(_dexPoolsTWAPSources.add(newSource))`: EnumerableSet `_add`, reverting when already present.
def addTWAPSourceTransition : TransitionDecl :=
  { name := "addTWAPSource"
    params := [{ name := "newSource", ty := addr }]
    returnType := []
    body :=
      nonpayable ++ onlyOwner ++
      [ .require (.binary .eq (.storage (dexIndexRef (key (.var "newSource")))) (.intLit 0)),
        .push dexValuesRef (some (key (.var "newSource"))),
        .assign .storage (dexIndexRef (key (.var "newSource")))
          (.arrayLength .storage dexValuesRef) ] }

-- `require(_dexPoolsTWAPSources.remove(rm))`: EnumerableSet `_remove` swap-and-pop, reverting when absent.
def removeTWAPSourceTransition : TransitionDecl :=
  { name := "removeTWAPSource"
    params := [{ name := "rm", ty := addr }]
    returnType := []
    body :=
      nonpayable ++ onlyOwner ++
      [ .letDecl "valueIndex" (some uint256) (.storage (dexIndexRef (key (.var "rm")))),
        .require (.binary .ne (.var "valueIndex") (.intLit 0)),
        .letDecl "toDeleteIndex" (some uint256) (sub256 (.var "valueIndex") (.intLit 1)),
        .letDecl "lastIndex" (some uint256) (sub256 (.arrayLength .storage dexValuesRef) (.intLit 1)),
        .letDecl "lastvalue" (some bytes32) (.storage (dexElemRef (.var "lastIndex"))),
        .assign .storage (dexElemRef (.var "toDeleteIndex")) (.var "lastvalue"),
        .assign .storage (dexIndexRef (.var "lastvalue")) (add256 (.var "toDeleteIndex") (.intLit 1)),
        .pop dexValuesRef,
        .delete (dexIndexRef (key (.var "rm"))) ] }

def transitions : List TransitionDecl :=
  [ addTWAPSourceTransition,
    allowanceTransition,
    approveTransition,
    balanceOfTransition,
    burnTransition,
    burnFromTransition,
    burnFromInternalTransition,
    changeTWAPEpochPeriodTransition,
    changeTWAPOracleTransition,
    decimalsTransition,
    decreaseAllowanceTransition,
    domainSeparatorTransition,
    increaseAllowanceTransition,
    mintTransition,
    nameTransition,
    noncesTransition,
    ownerTransition,
    permitTransition,
    permitTypehashTransition,
    removeTWAPSourceTransition,
    renounceOwnershipTransition,
    setVaultTransition,
    symbolTransition,
    totalSupplyTransition,
    transferTransition,
    transferFromTransition,
    transferOwnershipTransition,
    twapEpochPeriodTransition,
    twapOracleTransition,
    vaultTransition ]

def contract : ContractDecl :=
  { name := "KlimaToken"
    storage := storageDecls
    ctor := constructorDecl
    functions := []
    transitions := transitions }

def config : Config :=
  { storage := storageLayout
    externalABI := klimaExternalABI
    abiDecodeMode := DecodeMode.legacySolc05
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

end Benchmarks.Klima
