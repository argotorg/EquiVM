import Benchmarks.Auction.PaymentLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem rawReturnSource {locals : Store} {evm : EVM.State} {recipient amount ptr : UInt256}
    {out : ByteArray} {z : Bool} (hv : PaymentValues locals recipient amount ptr)
    (hd : locals.get? "_data" = some (.bytes out))
    (hz : locals.get? "success" = some (.bool z))
    (hb : ptr.toNat + out.size + 63 ≤ 2 ^ 200) :
    ∃ locals', ExecStmt auctionConfig { contract := auctionContract, locals := locals } evm
      (.ite (.binary .ne (localBytesLength "_data") (.intLit 0))
        [advanceFreePtr (wordRoundedSize (.binary .add (localBytesLength "_data") (.intLit 32)))]
        []) (.ok { contract := auctionContract, locals := locals' } evm) ∧
      PaymentValues locals' recipient amount (rawReturnPtr ptr out) ∧
      locals'.get? "success" = some (.bool z) := by
  have hl := localBytesLengthSource (evm := evm) hd
  by_cases he : out.size = 0
  · refine ⟨locals, ExecStmt.iteFalse ?_ ExecBlock.nil, ?_, hz⟩
    · simp only [evalExpr?, hl, he, pure, bind, EvalResult.bind, evalBinaryOp?]
      rfl
    · simpa only [rawReturnPtr, he, if_pos rfl] using hv
  · have hn : out.size + 63 < UInt256.size := by change out.size + 63 < 2 ^ 256; omega
    have hr : evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
        (wordRoundedSize (.binary .add (localBytesLength "_data") (.intLit 32))) =
        .ok (.int (Int.ofNat (bytesAllocSize out.size).toNat)) := by
      rw [bytesAllocSize_eq_returnReserveSize hn]
      apply wordRoundedSizeSource
      · simp only [evalExpr?, hl, pure, bind, EvalResult.bind, evalBinaryOp?]
        rfl
      · omega
    have ha : ptr.toNat + (bytesAllocSize out.size).toNat < UInt256.size := by
      rw [bytesAllocSize_toNat hn]
      have hround : (out.size + 63) / 32 * 32 ≤ out.size + 63 := Nat.div_mul_le_self _ _
      change ptr.toNat + (out.size + 63) / 32 * 32 < 2 ^ 256
      omega
    refine ⟨locals.insert "_freePtr" (.int (Int.ofNat (bytesAllocPtr ptr out.size).toNat)),
      ExecStmt.iteTrue ?_ (ExecBlock.consNormal (advanceFreePtrSource hv.ptr hr ha) ExecBlock.nil),
      ?_, ?_⟩
    · simp only [evalExpr?, hl, pure, bind, EvalResult.bind, evalBinaryOp?]
      have hi : (Value.int (Int.ofNat out.size) == Value.int 0) = false := by
        rw [beq_eq_false_iff_ne]
        exact fun h ↦ he (Int.ofNat.inj (Value.int.inj h))
      rw [hi]
      rfl
    · simpa only [rawReturnPtr, he, if_false] using hv.setFree (bytesAllocPtr ptr out.size)
    · exact (store_get_ne _ _ (by decide)).trans hz

theorem rawEthSource {locals : Store} {evm evm' : EVM.State} {recipient amount ptr : UInt256}
    {out : ByteArray} {z : Bool} (hv : PaymentValues locals recipient amount ptr)
    (hb : ptr.toNat + 2 ^ 139 ≤ 2 ^ 200) (ho : out.size < 2 ^ 138)
    (hc : callViaEVM evm (paymentAddress recipient) (Int.ofNat amount.toNat)
      ByteArray.empty (z, evm', out)) :
    ∃ locals', ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
      paymentRawStmts (.ok { contract := auctionContract, locals := locals' } evm') ∧
      PaymentValues locals' recipient amount (rawEthPtr ptr out) ∧
      locals'.get? "success" = some (.bool z) := by
  let l1 := locals.insert "_freePtr" (.int (Int.ofNat (nextEmptyPtr ptr).toNat))
  have h1 : PaymentValues l1 recipient amount (nextEmptyPtr ptr) := hv.setFree _
  have st1 : ExecStmt auctionConfig { contract := auctionContract, locals := locals } evm
      (advanceFreePtr (.intLit 32)) (.ok { contract := auctionContract, locals := l1 } evm) :=
    advanceFreePtrSource (delta := ⟨32⟩) hv.ptr (by simp [evalExpr?, pure]; decide)
      (by change ptr.toNat + 32 < 2 ^ 256; omega)
  let l2 := (l1.insert "success" (.bool z)).insert "_data" (.bytes out)
  have h2 : PaymentValues l2 recipient amount (nextEmptyPtr ptr) :=
    (h1.insertOther (.bool z) (by decide) (by decide) (by decide) (by decide)).insertOther
      (.bytes out) (by decide) (by decide) (by decide) (by decide)
  have st2 : ExecStmt auctionConfig { contract := auctionContract, locals := l1 } evm
      (.lowLevelCall (.var "to") (.var "amount") (.newBytes (.intLit 0)) "success" "_data")
      (.ok { contract := auctionContract, locals := l2 } evm') := by
    apply lowLevelCallSource (target := paymentAddress recipient)
      (value := Int.ofNat amount.toNat) (calldata := ByteArray.empty)
    · simp only [evalExpr?, h1.recipient, EvalResult.ofOption]
    · simp only [evalExpr?, h1.amount, EvalResult.ofOption]
    · simp [evalExpr?, pure]
      rfl
    · exact hc
  have hp := nextEmptyPtr_toNat (ptr := ptr) (by omega)
  obtain ⟨l3, st3, h3, hz⟩ := rawReturnSource h2 (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide)).trans (store_get_self _ _ _)) (by omega)
  exact ⟨l3, ExecBlock.consNormal st1 (ExecBlock.consNormal st2
    (ExecBlock.consNormal st3 ExecBlock.nil)), h3, hz⟩

end Auction
