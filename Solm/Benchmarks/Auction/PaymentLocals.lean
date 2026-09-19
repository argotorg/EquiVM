import Solm.Benchmarks.Auction.PaymentArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def paymentAddress (recipient : UInt256) : AccountAddress :=
  AccountAddress.ofUInt256 (UInt256.land recipient solcAddrMask)

theorem addressOfWord_eq (word : UInt256) :
    AccountAddress.ofUInt256 word = AccountAddress.ofNat word.toNat := by
  exact accountAddress_ofUInt256_eq_ofNat_toNat word

theorem addressOfAddress (target : AccountAddress) : EVM.address target.val = target := by
  apply Fin.ext
  change target.val % AccountAddress.size = target.val
  exact Nat.mod_eq_of_lt target.isLt

structure PaymentValues (locals : Store) (recipient amount ptr : UInt256) : Prop where
  recipient : locals.get? "to" = some (.address (paymentAddress recipient))
  amount : locals.get? "amount" = some (.int (Int.ofNat amount.toNat))
  ptr : locals.get? "_freePtr" = some (.int (Int.ofNat ptr.toNat))
  weth : locals.get? "weth" = none

theorem PaymentValues.setFree {locals recipient amount ptr} (h : PaymentValues locals recipient
  amount ptr)
    (next : UInt256) :
    PaymentValues (locals.insert "_freePtr" (.int (Int.ofNat next.toNat))) recipient amount next
      := by
  exact ⟨(store_get_ne _ _ (by decide)).trans h.recipient,
    (store_get_ne _ _ (by decide)).trans h.amount, store_get_self _ _ _,
    (store_get_ne _ _ (by decide)).trans h.weth⟩

theorem PaymentValues.insertOther {locals recipient amount ptr name}
    (h : PaymentValues locals recipient amount ptr) (value : Value)
    (ht : (name == "to") = false) (ha : (name == "amount") = false)
    (hp : (name == "_freePtr") = false) (hw : (name == "weth") = false) :
    PaymentValues (locals.insert name value) recipient amount ptr := by
  exact ⟨(store_get_ne _ _ ht).trans h.recipient, (store_get_ne _ _ ha).trans h.amount,
    (store_get_ne _ _ hp).trans h.ptr, (store_get_ne _ _ hw).trans h.weth⟩

def paymentRawStmts : List Stmt :=
  [ advanceFreePtr (.intLit 32),
    .lowLevelCall (.var "to") (.var "amount") (.newBytes (.intLit 0)) "success" "_data",
    .ite (.binary .ne (localBytesLength "_data") (.intLit 0))
      [advanceFreePtr (wordRoundedSize (.binary .add (localBytesLength "_data") (.intLit 32)))]
      [] ]

def paymentTransferStmts : List Stmt :=
  [ .lowLevelCall (.storage wethRef) (.intLit 0)
      (.abiEncodeCall "transfer" [.var "to", .var "amount"])
      "_transferSuccess" "_transferData",
    .require (.var "_transferSuccess"),
    advanceFreePtr (wordRoundedSize (localBytesLength "_transferData")),
    .letDecl "_xfer" (some boolTy) (.abiDecode boolTy (.var "_transferData")) ]

def paymentFallbackStmts : List Stmt :=
  checkedExternalCallStmts (.storage wethRef) "deposit" (.var "amount") [] "_dep" ++
    paymentTransferStmts

theorem paymentBody_eq : safeTransferETHWithFallback.body = paymentRawStmts ++
    [.ite (.unary .not (.var "success")) paymentFallbackStmts [], .return [.var "_freePtr"]] := rfl

end Auction
