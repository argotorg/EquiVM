import Benchmarks.Auction.RawEthRoutine
import Benchmarks.Auction.ReturnReserve

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem advanceFreePtrSource {evm : EVM.State} {locals : Store} {ptr delta : UInt256} {e : Expr}
    (hp : locals.get? "_freePtr" = some (.int (Int.ofNat ptr.toNat)))
    (he : evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm e =
      .ok (.int (Int.ofNat delta.toNat))) (hb : ptr.toNat + delta.toNat < UInt256.size) :
    ExecStmt auctionConfig { contract := auctionContract, locals := locals } evm (advanceFreePtr e)
      (.ok
        { contract := auctionContract
          locals := locals.insert "_freePtr" (.int (Int.ofNat (ptr + delta).toNat)) } evm) := by
  have hn : (ptr + delta).toNat = ptr.toNat + delta.toNat := addWord_toNat ptr delta hb
  apply ExecStmt.assign
  · simp only [evalExpr?, hp, EvalResult.ofOption, EvalResult.bind, bind, he, evalBinaryOp?]
    congr 2
  · simp only [assignStorageRef?, hp, updateLocalPath?, pure, bind, EvalResult.bind]
    rw [hn]
    rfl

theorem localBytesLengthSource {evm : EVM.State} {locals : Store} {name : Ident} {out : ByteArray}
    (hb : locals.get? name = some (.bytes out)) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (localBytesLength name) = .ok (.int (Int.ofNat out.size)) := by
  simp only [localBytesLength, evalExpr?, hb, readLocalPath?, pure, bind, EvalResult.bind]

theorem wordRoundedSizeSource {evm : EVM.State} {locals : Store} {e : Expr} {size : Nat}
    (he : evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm e =
      .ok (.int (Int.ofNat size))) (hb : size + 31 < UInt256.size) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (wordRoundedSize e) = .ok (.int (Int.ofNat (returnReserveSize size).toNat)) := by
  have hn : (UInt256.ofNat size).toNat = size := ulit_toNat' size (by omega)
  have hadd : (UInt256.ofNat size + ⟨31⟩).toNat = size + 31 := by
    have ha : (UInt256.ofNat size + ⟨31⟩).toNat = (UInt256.ofNat size).toNat + 31 :=
      addWord_toNat (UInt256.ofNat size) ⟨31⟩ (by rw [hn]; exact hb)
    simpa only [hn] using ha
  have hr : (returnReserveSize size).toNat = Nat.land (UInt256.size - 32) (size + 31) := by
    rw [returnReserveSize, uland_toNat, hadd]
    rfl
  simp only [wordRoundedSize, solcWordAlignMaskExpr, evalExpr?, he, pure, bind,
    EvalResult.bind, evalBinaryOp?]
  rw [hr]
  have hguard : 0 ≤ Int.ofNat (UInt256.size - 32) ∧
      Int.ofNat (UInt256.size - 32) < (EVM.wordModulus : Int) ∧
      0 ≤ Int.ofNat size + 31 ∧ Int.ofNat size + 31 < (EVM.wordModulus : Int) := by
    change 0 ≤ Int.ofNat (2 ^ 256 - 32) ∧
      Int.ofNat (2 ^ 256 - 32) < (2 ^ 256 : Int) ∧
      0 ≤ Int.ofNat size + 31 ∧ Int.ofNat size + 31 < (2 ^ 256 : Int)
    change size + 31 < 2 ^ 256 at hb
    simp only [Int.ofNat_eq_natCast]
    refine ⟨by decide, by decide, by omega, ?_⟩
    exact_mod_cast hb
  rw [if_pos hguard]
  congr 3

theorem bytesAllocSize_eq_returnReserveSize {size : Nat} (hb : size + 63 < UInt256.size) :
    bytesAllocSize size = returnReserveSize (size + 32) := by
  apply u256_inj
  rw [bytesAllocSize_toNat hb, returnReserveSize_toNat (by omega)]

-- LIBRARY CANDIDATE: both low-level-call outcomes update the same two locals.
theorem lowLevelCallSource {cfg : Config} {frame : Frame} {evm evm' : EVM.State}
    {receiver eth cdata : Expr} {target : AccountAddress} {value : Int} {calldata out : ByteArray}
    {success data : Ident} {z : Bool}
    (hr : evalExpr? cfg frame evm receiver = .ok (.address target))
    (hv : evalExpr? cfg frame evm eth = .ok (.int value))
    (hd : evalExpr? cfg frame evm cdata = .ok (.bytes calldata))
    (hc : callViaEVM evm target value calldata (z, evm', out)) :
    ExecStmt cfg frame evm (.lowLevelCall receiver eth cdata success data)
      (.ok { frame with locals := (frame.locals.insert success (.bool z)).insert data (.bytes out) }
        evm') := by
  have ht : EVM.address target.val = target := by
    apply Fin.ext
    change target.val % AccountAddress.size = target.val
    exact Nat.mod_eq_of_lt target.isLt
  rw [← ht] at hc
  cases z with
  | false => exact ExecStmt.lowLevelCallFailure hr hv hd hc
  | true => exact ExecStmt.lowLevelCallSuccess hr hv hd hc

end Auction
