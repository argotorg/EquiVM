import Benchmarks.Auction.ErrorSourceDecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

-- LIBRARY CANDIDATE: arithmetic and comparison of natural-valued source expressions.
theorem naturalAddSource {cfg frame evm lhs rhs} {a b : Nat}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int (Int.ofNat a)))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int (Int.ofNat b))) :
    evalExpr? cfg frame evm (.binary .add lhs rhs) = .ok (.int (Int.ofNat (a + b))) := by
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?]
  rfl

theorem naturalLeSource {cfg frame evm lhs rhs} {a b : Nat}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int (Int.ofNat a)))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int (Int.ofNat b))) :
    evalExpr? cfg frame evm (.binary .le lhs rhs) = .ok (.bool (decide (a ≤ b))) := by
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_eq_natCast,
    Nat.cast_le]

theorem naturalGeSource {cfg frame evm lhs rhs} {a b : Nat}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int (Int.ofNat a)))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int (Int.ofNat b))) :
    evalExpr? cfg frame evm (.binary .ge lhs rhs) = .ok (.bool (decide (b ≤ a))) := by
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_eq_natCast,
    Nat.cast_le]

theorem localNatSource {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {locals : Store} {name : Ident} {n : Nat}
    (hn : locals.get? name = some (.int (Int.ofNat n))) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.var name) =
      .ok (.int (Int.ofNat n)) := by
  simp only [evalExpr?, hn, EvalResult.ofOption]

theorem errorLongSource {evm : EVM.State} {locals : Store} {name : Ident} {out : ByteArray}
    (hd : locals.get? name = some (.bytes out)) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (errorStringReturndataLongEnough name) = .ok (.bool (decide (68 ≤ out.size))) :=
  naturalGeSource (localBytesLengthSource hd) (by simp only [evalExpr?, pure]; rfl)

theorem errorU64Source {evm : EVM.State} {locals : Store} {name : Ident} {word : UInt256}
    (hn : locals.get? name = some (.int (Int.ofNat word.toNat))) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.binary .le (.var name) solcMaxU64Expr) =
      .ok (.bool (decide (word.toNat ≤ 2 ^ 64 - 1))) :=
  naturalLeSource (localNatSource hn) (by simp only [solcMaxU64Expr, evalExpr?, pure]; rfl)

theorem errorOffsetBoundSource {evm : EVM.State} {locals : Store} {name offName : Ident}
    {out : ByteArray} (hd : locals.get? name = some (.bytes out))
    (ho : locals.get? offName = some (.int (Int.ofNat (errorOffset out).toNat))) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (errorStringOffsetInBounds name offName) =
      .ok (.bool (decide ((errorOffset out).toNat + 36 ≤ out.size))) :=
  naturalLeSource (naturalAddSource (localNatSource ho)
    (by simp only [evalExpr?, pure]; rfl)) (localBytesLengthSource hd)

theorem errorPayloadBoundSource {evm : EVM.State} {locals : Store}
    {name offName lenName : Ident} {out : ByteArray}
    (hd : locals.get? name = some (.bytes out))
    (ho : locals.get? offName = some (.int (Int.ofNat (errorOffset out).toNat)))
    (hn : locals.get? lenName = some (.int (Int.ofNat (errorLength out).toNat))) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (errorStringPayloadInBounds name offName lenName) =
      .ok (.bool (decide ((errorOffset out).toNat + (errorLength out).toNat + 36 ≤ out.size))) :=
  naturalLeSource (naturalAddSource (naturalAddSource (localNatSource ho) (localNatSource hn))
    (by simp only [evalExpr?, pure]; rfl)) (localBytesLengthSource hd)

theorem errorNewFreePtrSource {evm : EVM.State} {locals : Store} {offName lenName : Ident}
    {out : ByteArray} {ptr : UInt256}
    (ho : locals.get? offName = some (.int (Int.ofNat (errorOffset out).toNat)))
    (hn : locals.get? lenName = some (.int (Int.ofNat (errorLength out).toNat)))
    (hp : locals.get? "_freePtr" = some (.int (Int.ofNat ptr.toNat)))
    (hv : ErrorDataValid out) (hb : ptr.toNat + out.size + 64 ≤ 2 ^ 200) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (errorStringNewFreePtr offName lenName) =
      .ok (.int (Int.ofNat (errorAllocPtr ptr (errorAllocSize out)).toNat)) := by
  have hs : (errorOffset out).toNat + (errorLength out).toNat + 32 + 31 < UInt256.size := by
    have hpay := hv.2.2.2
    change _ < 2 ^ 256
    omega
  have hr := wordRoundedSizeSource (evm := evm)
    (naturalAddSource (naturalAddSource (localNatSource ho) (localNatSource hn))
      (rhs := .intLit 32) (b := 32) (by simp only [evalExpr?, pure]; rfl)) hs
  have hh := naturalAddSource (localNatSource hp) hr
  rw [returnReserveSize_toNat hs] at hh
  rw [errorAllocPtr_toNat hv hb]
  simpa only [Nat.add_assoc] using hh

theorem errorAllocationBoundSource {evm : EVM.State} {locals : Store}
    {offName lenName : Ident} {out : ByteArray} {ptr : UInt256}
    (ho : locals.get? offName = some (.int (Int.ofNat (errorOffset out).toNat)))
    (hn : locals.get? lenName = some (.int (Int.ofNat (errorLength out).toNat)))
    (hp : locals.get? "_freePtr" = some (.int (Int.ofNat ptr.toNat)))
    (hv : ErrorDataValid out) (hb : ptr.toNat + out.size + 64 ≤ 2 ^ 200) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (errorStringAllocationWithinU64 offName lenName) =
      .ok (.bool (decide ((errorAllocPtr ptr (errorAllocSize out)).toNat ≤ 2 ^ 64 - 1))) :=
  naturalLeSource (errorNewFreePtrSource ho hn hp hv hb)
    (by simp only [solcMaxU64Expr, evalExpr?, pure]; rfl)

theorem errorAllocationNoWrapSource {evm : EVM.State} {locals : Store}
    {offName lenName : Ident} {out : ByteArray} {ptr : UInt256}
    (ho : locals.get? offName = some (.int (Int.ofNat (errorOffset out).toNat)))
    (hn : locals.get? lenName = some (.int (Int.ofNat (errorLength out).toNat)))
    (hp : locals.get? "_freePtr" = some (.int (Int.ofNat ptr.toNat)))
    (hv : ErrorDataValid out) (hb : ptr.toNat + out.size + 64 ≤ 2 ^ 200) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (errorStringAllocationNoWrap offName lenName) =
      .ok (.bool (decide (ptr.toNat ≤ (errorAllocPtr ptr (errorAllocSize out)).toNat))) :=
  naturalGeSource (errorNewFreePtrSource ho hn hp hv hb) (localNatSource hp)

end Auction
