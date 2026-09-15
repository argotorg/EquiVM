import Benchmarks.Auction.ErrorReturnABI
import Benchmarks.Auction.PaymentArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

-- LIBRARY CANDIDATE: successful natural-number byte slicing in the source semantics.
theorem sliceBytes_nat {out : ByteArray} {start finish : Nat}
    (hs : start ≤ finish) (he : finish ≤ out.size) :
    sliceBytes? out (Int.ofNat start) (Int.ofNat finish) =
      .ok (.bytes (out.extract start finish)) := by
  simp [sliceBytes?, Int.ofNat_eq_natCast, Nat.not_lt.mpr hs, Nat.not_lt.mpr he]

theorem errorPayloadSource {evm : EVM.State} {locals : Store} {name : Ident} {out : ByteArray}
    (hd : locals.get? name = some (.bytes out)) (hl : 4 ≤ out.size) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (errorStringPayload name) = .ok (.bytes (out.extract 4 out.size)) := by
  have hb := localBytesLengthSource (evm := evm) hd
  simp only [errorStringPayload, evalExpr?, hd, hb, EvalResult.ofOption, pure, bind,
    EvalResult.bind]
  exact sliceBytes_nat hl (Nat.le_refl _)

theorem errorOffsetSource {evm : EVM.State} {locals : Store} {name : Ident} {out : ByteArray}
    (hd : locals.get? name = some (.bytes out)) (hl : 36 ≤ out.size)
    (hb : out.size < 2 ^ 255) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (errorStringOffsetDecode name) = .ok (.int (Int.ofNat (errorOffset out).toNat)) := by
  have hp := errorPayloadSource (evm := evm) hd (by omega)
  have hh := decodeReturnUint_extract (out := out) (start := 4) (finish := out.size)
    hl (Nat.le_refl _) (by omega)
  simp only [errorStringOffsetDecode, evalExpr?, hp, bind, EvalResult.bind, pure]
  change (match ABI.decodeReturnValue? uint256 (out.extract 4 out.size) with
    | some value => EvalResult.ok value
    | none => EvalResult.revert) = _
  simp only [uint256, uint256Int, hh, errorOffset]

theorem errorLengthWordSource {evm : EVM.State} {locals : Store} {name offName : Ident}
    {out : ByteArray} (hd : locals.get? name = some (.bytes out))
    (ho : locals.get? offName = some (.int (Int.ofNat (errorOffset out).toNat)))
    (hb : (errorOffset out).toNat + 36 ≤ out.size) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (errorStringLengthWord name offName) =
      .ok (.bytes (out.extract (4 + (errorOffset out).toNat)
        (4 + (errorOffset out).toNat + 32))) := by
  have hp := errorPayloadSource (evm := evm) hd (by omega)
  simp only [errorStringLengthWord, evalExpr?, hp, ho, EvalResult.ofOption, pure, bind,
    EvalResult.bind, evalBinaryOp?]
  have hs := sliceBytes_nat (out := out.extract 4 out.size)
    (start := (errorOffset out).toNat) (finish := (errorOffset out).toNat + 32)
    (by omega) (by rw [ByteArray.size_extract]; omega)
  simp only [Int.ofNat_eq_natCast, Int.natCast_add, Nat.cast_ofNat] at hs ⊢
  rw [hs, extract_extract_BA]
  rw [show min (4 + ((errorOffset out).toNat + 32)) out.size =
    4 + (errorOffset out).toNat + 32 by omega]

theorem errorLengthSource {evm : EVM.State} {locals : Store} {name offName : Ident}
    {out : ByteArray} (hd : locals.get? name = some (.bytes out))
    (ho : locals.get? offName = some (.int (Int.ofNat (errorOffset out).toNat)))
    (hb : (errorOffset out).toNat + 36 ≤ out.size) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (errorStringLengthDecode name offName) = .ok (.int (Int.ofNat (errorLength out).toNat)) := by
  have hp := errorLengthWordSource (evm := evm) hd ho hb
  have hh := decodeReturnUint_extract (out := out) (start := 4 + (errorOffset out).toNat)
    (finish := 4 + (errorOffset out).toNat + 32) (by omega) (by omega) (by omega)
  simp only [errorStringLengthDecode, evalExpr?, hp, bind, EvalResult.bind, pure]
  change (match ABI.decodeReturnValue? uint256
      (out.extract (4 + (errorOffset out).toNat) (4 + (errorOffset out).toNat + 32)) with
    | some value => EvalResult.ok value
    | none => EvalResult.revert) = _
  simp only [uint256, uint256Int, hh, errorLength]

theorem errorStringSource {evm : EVM.State} {locals : Store} {name : Ident} {out : ByteArray}
    (hd : locals.get? name = some (.bytes out)) (hv : ErrorDataValid out)
    (hb : out.size < 2 ^ 255) :
    ∃ value, evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.abiDecode .string (errorStringPayload name)) = .ok value := by
  have hp := errorPayloadSource (evm := evm) hd (by have h := hv.1; omega)
  obtain ⟨value, hh⟩ := errorReturnString_ok hv hb
  refine ⟨value, ?_⟩
  simp only [evalExpr?, hp, bind, EvalResult.bind, pure]
  change (match ABI.decodeReturnValue? .string (out.extract 4 out.size) with
    | some value => EvalResult.ok value
    | none => EvalResult.revert) = _
  rw [hh]

end Auction
