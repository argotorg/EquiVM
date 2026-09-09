import Benchmarks.Auction.Spec
import Reasoning.SolmBody

open Solm Ethereum Ethereum.EVM

namespace Auction

-- LIBRARY CANDIDATE: evaluate nonnegative integer addition without unfolding its operands.
theorem evalExpr_add_nat {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : Nat}
    (hl : evalExpr? cfg frame evm lhs = .ok (.int (Int.ofNat a)))
    (hr : evalExpr? cfg frame evm rhs = .ok (.int (Int.ofNat b))) :
    evalExpr? cfg frame evm (.binary .add lhs rhs) =
      .ok (.int (Int.ofNat (a + b))) := by
  rw [Solm.evalExpr?.eq_def]
  simp only [EvalResult.bind, bind]
  rw [hl, hr]
  simp [evalBinaryOp?]

-- LIBRARY CANDIDATE: bytes length depends only on the local bytes binding.
theorem evalExpr_localBytesLength {cfg : Config} {frame : Frame} {evm : EVM.State}
    {name : Ident} {out : ByteArray} (hlocal : frame.locals.get? name = some (.bytes out)) :
    evalExpr? cfg frame evm (localBytesLength name) = .ok (.int (Int.ofNat out.size)) := by
  change frame.locals[name]? = some (.bytes out) at hlocal
  simp [localBytesLength, evalExpr?, hlocal, readLocalPath?, pure, EvalResult.bind, bind]

def auctionRoundedMemoryNat (size : Nat) : Nat :=
  Nat.land (UInt256.size - 32) (size + 31)

theorem evalExpr_roundedMemoryAllocation {cfg : Config} {frame : Frame} {evm : EVM.State}
    {size : Expr} {n : Nat}
    (he : evalExpr? cfg frame evm size = .ok (.int (Int.ofNat n)))
    (hn : n + 31 < UInt256.size) :
    evalExpr? cfg frame evm (roundedMemoryAllocation size) =
      .ok (.int (Int.ofNat (auctionRoundedMemoryNat n))) := by
  have hm : UInt256.size - 32 < EVM.wordModulus := by decide
  have hcast : Int.ofNat n + 31 = Int.ofNat (n + 31) := by norm_num
  have hni : (0 : Int) ≤ Int.ofNat n + 31 ∧
      Int.ofNat n + 31 < (EVM.wordModulus : Int) := by
    change (0 : Int) ≤ Int.ofNat n + 31 ∧ Int.ofNat n + 31 < (UInt256.size : Int)
    constructor
    · exact Int.add_nonneg (Int.natCast_nonneg _) (by decide)
    · rw [hcast]
      exact Int.ofNat_lt.mpr hn
  have hs : evalExpr? cfg frame evm (.binary .add size (.intLit 31)) =
      .ok (.int (Int.ofNat (n + 31))) := by
    rw [Solm.evalExpr?.eq_def]
    simp only [EvalResult.bind, bind]
    rw [he]
    simp [evalExpr?, pure, evalBinaryOp?]
  change evalExpr? cfg frame evm
    (.binary .bitAnd solcWordAlignMaskExpr (.binary .add size (.intLit 31))) = _
  rw [Solm.evalExpr?.eq_def]
  simp only [EvalResult.bind, bind]
  rw [hs]
  simp [solcWordAlignMaskExpr, evalExpr?, pure, evalBinaryOp?,
    hm, auctionRoundedMemoryNat]
  rw [if_pos (by simpa using hni)]
  have hnat : (↑n + 31 : Int).toNat = n + 31 := by
    change (Int.ofNat n + 31).toNat = n + 31
    rw [hcast]
    exact Int.toNat_natCast _
  rw [hnat]

def auctionPayoutFreeNat (size : Nat) : Nat :=
  if size = 0 then 352 else 352 + auctionRoundedMemoryNat (size + 32)

theorem evalExpr_payoutFreePtrAfterETH {cfg : Config} {frame : Frame} {evm : EVM.State}
    {out : ByteArray} (hlocal : frame.locals.get? "_data" = some (.bytes out))
    (hsize : out.size + 63 < UInt256.size) :
    evalExpr? cfg frame evm payoutFreePtrAfterETH =
      .ok (.int (Int.ofNat (auctionPayoutFreeNat out.size))) := by
  have hlen := evalExpr_localBytesLength (evm := evm) (cfg := cfg) hlocal
  have hsum := evalExpr_add_nat hlen
    (show evalExpr? cfg frame evm (.intLit 32) = .ok (.int (Int.ofNat 32)) by
      simp only [evalExpr?, pure]; rfl)
  have hround := evalExpr_roundedMemoryAllocation hsum (by omega)
  have hadd := evalExpr_add_nat
    (show evalExpr? cfg frame evm (.intLit 352) = .ok (.int (Int.ofNat 352)) by
      simp only [evalExpr?, pure]; rfl) hround
  unfold payoutFreePtrAfterETH
  rw [Solm.evalExpr?.eq_def]
  simp only [EvalResult.bind, bind]
  have heq : evalExpr? cfg frame evm
      (.binary .eq (localBytesLength "_data") (.intLit 0)) =
        .ok (.bool (out.size == 0)) := by
    rw [Solm.evalExpr?.eq_def]
    simp only [EvalResult.bind, bind]
    rw [hlen]
    simp [evalExpr?, evalBinaryOp?, pure]
  rw [heq]
  by_cases hz : out.size = 0
  · simp [hz, auctionPayoutFreeNat, evalExpr?, pure]
  · simpa [BEq.beq, hz, auctionPayoutFreeNat] using hadd

end Auction
