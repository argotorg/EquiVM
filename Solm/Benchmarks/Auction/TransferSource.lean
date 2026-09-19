import Solm.Benchmarks.Auction.DepositSource
import Solm.Benchmarks.Auction.TransferCall
import Solm.Benchmarks.Auction.ReturnABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def transferSourceLocals (locals : Store) (z : Bool) (out : ByteArray) : Store :=
  (locals.insert "_transferSuccess" (.bool z)).insert "_transferData" (.bytes out)

theorem transferSourceLocals_values {locals recipient amount ptr}
    (hv : PaymentValues locals recipient amount ptr) (z : Bool) (out : ByteArray) :
    PaymentValues (transferSourceLocals locals z out) recipient amount ptr :=
  (hv.insertOther (.bool z) (by decide) (by decide) (by decide) (by decide)).insertOther
    (.bytes out) (by decide) (by decide) (by decide) (by decide)

theorem transferSourceLocals_status (locals : Store) (z : Bool) (out : ByteArray) :
    (transferSourceLocals locals z out).get? "_transferSuccess" = some (.bool z) :=
  (store_get_ne _ _ (by decide)).trans (store_get_self _ _ _)

theorem transferSourceLocals_data (locals : Store) (z : Bool) (out : ByteArray) :
    (transferSourceLocals locals z out).get? "_transferData" = some (.bytes out) :=
      store_get_self _ _ _

theorem transferCallSource {s0 I cA σ evm evm' locals recipient amount ptr out z}
    (hs : SourceState s0 I cA σ evm) (hv : PaymentValues locals recipient amount ptr)
    (hc : callViaEVM evm (AccountAddress.ofUInt256 (wethWord σ I)) 0
      (transferData recipient amount) (z, evm', out)) :
    ExecStmt auctionConfig { contract := auctionContract, locals := locals } evm
      (.lowLevelCall (.storage wethRef) (.intLit 0)
        (.abiEncodeCall "transfer" [.var "to", .var "amount"]) "_transferSuccess" "_transferData")
      (.ok { contract := auctionContract, locals := transferSourceLocals locals z out } evm') := by
  apply lowLevelCallSource (wethSourceRead hs hv.weth) (by simp [evalExpr?, pure]) ?_ hc
  have ht : auctionConfig.externalABI.encode? "transfer"
      [.address (paymentAddress recipient), .int (Int.ofNat amount.toNat)] =
      some (transferData recipient amount) := by
    simpa only [paymentAddress, addressOfWord_eq] using transferData_encode recipient amount
  simp only [evalExpr?, evalExprList?, hv.recipient, hv.amount, EvalResult.ofOption,
    EvalResult.bind, bind, pure, ht]

theorem reserveTransferSource {evm locals ptr out}
    (hp : locals.get? "_freePtr" = some (.int (Int.ofNat ptr.toNat)))
    (hd : locals.get? "_transferData" = some (.bytes out))
    (hb : ptr.toNat + out.size + 31 ≤ 2 ^ 200) :
    ExecStmt auctionConfig { contract := auctionContract, locals := locals } evm
      (advanceFreePtr (wordRoundedSize (localBytesLength "_transferData")))
      (.ok
        { contract := auctionContract
          locals := locals.insert "_freePtr" (.int (Int.ofNat (returnReservePtr ptr
            out.size).toNat)) }
        evm) := by
  have hn : out.size + 31 < UInt256.size := by change out.size + 31 < 2 ^ 256; omega
  apply advanceFreePtrSource hp (wordRoundedSizeSource (localBytesLengthSource hd) hn)
  rw [returnReserveSize_toNat hn]
  have hr : (out.size + 31) / 32 * 32 ≤ out.size + 31 := Nat.div_mul_le_self _ _
  change ptr.toNat + (out.size + 31) / 32 * 32 < 2 ^ 256
  omega

theorem boolDecodeSourceValid {evm locals out}
    (hd : locals.get? "_transferData" = some (.bytes out)) (hv : BoolReturnValid out)
    (hb : out.size < 2 ^ 255) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.abiDecode boolTy (.var "_transferData")) =
      .ok (.bool (decide (calldataWord out 0 ≠ ⟨0⟩))) := by
  have hh := decodeReturnBool_valid hv hb
  simp only [evalExpr?, hd, EvalResult.ofOption, bind, EvalResult.bind, pure]
  change (match ABI.decodeReturnValue? boolTy out with
    | some value => EvalResult.ok value
    | none => EvalResult.revert) = _
  rw [hh]

theorem boolDecodeSourceInvalid {evm locals out}
    (hd : locals.get? "_transferData" = some (.bytes out)) (hv : ¬ BoolReturnValid out)
    (hb : out.size < 2 ^ 255) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.abiDecode boolTy (.var "_transferData")) = .revert := by
  have hh := decodeReturnBool_invalid hv hb
  simp only [evalExpr?, hd, EvalResult.ofOption, bind, EvalResult.bind, pure]
  change (match ABI.decodeReturnValue? boolTy out with
    | some value => EvalResult.ok value
    | none => EvalResult.revert) = _
  rw [hh]

theorem transferSourceSuccess {s0 I cA σ evm evm' locals recipient amount ptr out}
    (hs : SourceState s0 I cA σ evm) (hv : PaymentValues locals recipient amount ptr)
    (hc : callViaEVM evm (AccountAddress.ofUInt256 (wethWord σ I)) 0
      (transferData recipient amount) (true, evm', out))
    (hb : ptr.toNat + out.size + 31 ≤ 2 ^ 200) (ho : out.size < 2 ^ 255)
    (hvalid : BoolReturnValid out) :
    ∃ locals', ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
      paymentTransferStmts (.ok { contract := auctionContract, locals := locals' } evm') ∧
      PaymentValues locals' recipient amount (returnReservePtr ptr out.size) := by
  have h1 := transferSourceLocals_values hv true out
  have hp := h1.setFree (returnReservePtr ptr out.size)
  have hd :
      ((transferSourceLocals locals true out).insert "_freePtr"
        (.int (Int.ofNat (returnReservePtr ptr out.size).toNat))).get? "_transferData" =
      some (.bytes out) :=
    (store_get_ne _ _ (by decide)).trans (transferSourceLocals_data _ _ _)
  refine ⟨_, ExecBlock.consNormal (transferCallSource hs hv hc)
    (ExecBlock.consNormal (ExecStmt.requireTrue ?_)
      (ExecBlock.consNormal (reserveTransferSource h1.ptr (transferSourceLocals_data _ _ _) hb)
        (ExecBlock.consNormal (ExecStmt.letDecl (boolDecodeSourceValid hd hvalid ho))
          ExecBlock.nil))),
    hp.insertOther _ (by decide) (by decide) (by decide) (by decide)⟩
  simp only [evalExpr?, transferSourceLocals_status, EvalResult.ofOption]

theorem transferSourceFailure {s0 I cA σ evm evm' locals recipient amount ptr out z}
    (hs : SourceState s0 I cA σ evm) (hv : PaymentValues locals recipient amount ptr)
    (hc : callViaEVM evm (AccountAddress.ofUInt256 (wethWord σ I)) 0
      (transferData recipient amount) (z, evm', out))
    (hb : ptr.toNat + out.size + 31 ≤ 2 ^ 200) (ho : out.size < 2 ^ 255)
    (hfail : z = false ∨ ¬ BoolReturnValid out) :
    ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
      paymentTransferStmts .reverted := by
  refine ExecBlock.consNormal (transferCallSource hs hv hc) ?_
  cases z with
  | false =>
    exact ExecBlock.consRevert (ExecStmt.requireFalse (by
      simp only [evalExpr?, transferSourceLocals_status, EvalResult.ofOption]))
  | true =>
    have hbad : ¬ BoolReturnValid out := hfail.resolve_left (by decide)
    have h1 := transferSourceLocals_values hv true out
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_)
      (ExecBlock.consNormal (reserveTransferSource h1.ptr (transferSourceLocals_data _ _ _) hb)
        (ExecBlock.consRevert (ExecStmt.letDeclRevert (boolDecodeSourceInvalid ?_ hbad ho))))
    · simp only [evalExpr?, transferSourceLocals_status, EvalResult.ofOption]
    · exact (store_get_ne _ _ (by decide)).trans (transferSourceLocals_data _ _ _)

end Auction
