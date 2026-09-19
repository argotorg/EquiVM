import Solm.Benchmarks.Auction.ErrorSourceGuards

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def errorDecodeStmts : List Stmt :=
  [.require (errorStringReturndataLongEnough "err"),
    .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
    .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
    .require (errorStringOffsetInBounds "err" "_errOffset"),
    .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
    .require (.binary .le (.var "_errLength") solcMaxU64Expr),
    .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
    .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
    .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
    .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err"))]

theorem errorDecodeSource {evm : EVM.State} {locals : Store} {out : ByteArray} {ptr : UInt256}
    (hd : locals.get? "err" = some (.bytes out))
    (hp : locals.get? "_freePtr" = some (.int (Int.ofNat ptr.toNat)))
    (hpause : locals.get? "_paused" = none)
    (hb : ptr.toNat + out.size + 64 ≤ 2 ^ 200) :
    (ErrorDataValid out ∧ ErrorAllocAllowed ptr (errorAllocSize out) ∧
      ∃ locals', ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
        errorDecodeStmts (.ok { contract := auctionContract, locals := locals' } evm) ∧
        locals'.get? "_paused" = none) ∨
    ((¬ ErrorDataValid out ∨ ¬ ErrorAllocAllowed ptr (errorAllocSize out)) ∧
      ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
        errorDecodeStmts .reverted) := by
  have hb255 : out.size < 2 ^ 255 := by omega
  have b0 : ABlock auctionConfig evm { contract := auctionContract, locals := locals }
      errorDecodeStmts { contract := auctionContract, locals := locals } errorDecodeStmts :=
    ABlock.start
  by_cases hl : 68 ≤ out.size
  · have b1 := b0.requireStep (by rw [errorLongSource hd, decide_eq_true hl])
    have b2 := b1.letStep (errorOffsetSource hd (by omega) hb255)
    let l1 := locals.insert "_errOffset" (.int (Int.ofNat (errorOffset out).toNat))
    have hd1 : l1.get? "err" = some (.bytes out) := (store_get_ne _ _ (by decide)).trans hd
    have ho1 : l1.get? "_errOffset" = some (.int (Int.ofNat (errorOffset out).toNat)) :=
      store_get_self _ _ _
    by_cases ho64 : (errorOffset out).toNat ≤ 2 ^ 64 - 1
    · have b3 := b2.requireStep (by rw [errorU64Source ho1, decide_eq_true ho64])
      by_cases hob : (errorOffset out).toNat + 36 ≤ out.size
      · have b4 := b3.requireStep (by rw [errorOffsetBoundSource hd1 ho1, decide_eq_true hob])
        have b5 := b4.letStep (errorLengthSource hd1 ho1 hob)
        let l2 := l1.insert "_errLength" (.int (Int.ofNat (errorLength out).toNat))
        have hd2 : l2.get? "err" = some (.bytes out) :=
          (store_get_ne _ _ (by decide)).trans hd1
        have ho2 : l2.get? "_errOffset" = some (.int (Int.ofNat (errorOffset out).toNat)) :=
          (store_get_ne _ _ (by decide)).trans ho1
        have hn2 : l2.get? "_errLength" = some (.int (Int.ofNat (errorLength out).toNat)) :=
          store_get_self _ _ _
        have hp2 : l2.get? "_freePtr" = some (.int (Int.ofNat ptr.toNat)) :=
          (store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans hp)
        by_cases hn64 : (errorLength out).toNat ≤ 2 ^ 64 - 1
        · have b6 := b5.requireStep (by rw [errorU64Source hn2, decide_eq_true hn64])
          by_cases hpay : (errorOffset out).toNat + (errorLength out).toNat + 36 ≤ out.size
          · have hv : ErrorDataValid out := ⟨hl, ⟨ho64, hob⟩, hn64, hpay⟩
            have b7 := b6.requireStep (by
              rw [errorPayloadBoundSource hd2 ho2 hn2, decide_eq_true hpay])
            by_cases ha : ErrorAllocAllowed ptr (errorAllocSize out)
            · have b8 := b7.requireStep (by
                rw [errorAllocationBoundSource ho2 hn2 hp2 hv hb, decide_eq_true ha.1])
              have b9 := b8.requireStep (by
                rw [errorAllocationNoWrapSource ho2 hn2 hp2 hv hb, decide_eq_true ha.2])
              obtain ⟨value, he⟩ := errorStringSource (evm := evm) hd2 hv hb255
              have b10 := b9.letStep he
              exact Or.inl ⟨hv, ha, _, b10.run ExecBlock.nil,
                (store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans
                  ((store_get_ne _ _ (by decide)).trans hpause))⟩
            · have hwrap : ptr.toNat ≤ (errorAllocPtr ptr (errorAllocSize out)).toNat := by
                rw [errorAllocPtr_toNat hv hb]
                omega
              have hbig : ¬ (errorAllocPtr ptr (errorAllocSize out)).toNat ≤ 2 ^ 64 - 1 :=
                fun hx ↦ ha ⟨hx, hwrap⟩
              exact Or.inr ⟨Or.inr ha, b7.requireRevert (by
                rw [errorAllocationBoundSource ho2 hn2 hp2 hv hb, decide_eq_false hbig])⟩
          · exact Or.inr ⟨Or.inl (fun hv ↦ hpay hv.2.2.2), b6.requireRevert (by
              rw [errorPayloadBoundSource hd2 ho2 hn2, decide_eq_false hpay])⟩
        · exact Or.inr ⟨Or.inl (fun hv ↦ hn64 hv.2.2.1), b5.requireRevert (by
            rw [errorU64Source hn2, decide_eq_false hn64])⟩
      · exact Or.inr ⟨Or.inl (fun hv ↦ hob hv.2.1.2), b3.requireRevert (by
          rw [errorOffsetBoundSource hd1 ho1, decide_eq_false hob])⟩
    · exact Or.inr ⟨Or.inl (fun hv ↦ ho64 hv.2.1.1), b2.requireRevert (by
        rw [errorU64Source ho1, decide_eq_false ho64])⟩
  · exact Or.inr ⟨Or.inl (fun hv ↦ hl hv.1), b0.requireRevert (by
      rw [errorLongSource hd, decide_eq_false hl])⟩

end Auction
