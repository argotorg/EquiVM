import Benchmarks.Auction.ShortError
import Benchmarks.Auction.SettleGuards

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

set_option synthInstance.maxSize 4096 in
theorem bidWrongNounErrorWf : literalErrorWf auctionBytecode ⟨1289⟩ ⟨994⟩ ⟨23⟩
    ⟨0x4e6f756e206e6f7420757020666f722061756374696f6e000000000000000000⟩ := by
  unfold literalErrorWf errorHeaderWf errorWordTailWf
  native_decide

set_option synthInstance.maxSize 4096 in
theorem bidExpiredErrorWf : shortErrorWf auctionBytecode ⟨1372⟩ ⟨994⟩ ⟨15⟩
    ⟨0x105d58dd1a5bdb88195e1c1a5c9959⟩ ⟨138⟩ .PUSH15 15 := by
  unfold shortErrorWf errorHeaderWf errorWordTailWf
  native_decide

set_option synthInstance.maxSize 4096 in
theorem bidReserveErrorWf : literalErrorWf auctionBytecode ⟨1440⟩ ⟨994⟩ ⟨31⟩
    ⟨0x4d7573742073656e64206174206c656173742072657365727665507269636500⟩ := by
  unfold literalErrorWf errorHeaderWf errorWordTailWf
  native_decide

theorem bidWrongNounError {I g s0 R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨1289⟩ R mem aw rdata acc k C)
    (hov : R.length + 6 ≤ 1024) : RDrev auctionBytecode g s0 := by
  obtain ⟨_, _, _, _, _, hr⟩ := literalError h bidWrongNounErrorWf hov
  exact auctionErrorRevert hr (by omega)

theorem bidExpiredError {I g s0 R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨1372⟩ R mem aw rdata acc k C)
    (hov : R.length + 6 ≤ 1024) : RDrev auctionBytecode g s0 := by
  obtain ⟨_, _, _, _, _, hr⟩ := shortError h bidExpiredErrorWf (by decide) hov
  exact auctionErrorRevert hr (by omega)

theorem bidReserveError {I g s0 R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨1440⟩ R mem aw rdata acc k C)
    (hov : R.length + 6 ≤ 1024) : RDrev auctionBytecode g s0 := by
  obtain ⟨_, _, _, _, _, hr⟩ := literalError h bidReserveErrorWf hov
  exact auctionErrorRevert hr (by omega)

theorem bidIncrementError {I g s0 R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨1570⟩ R mem aw rdata acc k C)
    (hov : R.length + 7 ≤ 1024) : RDrev auctionBytecode g s0 := by
  have rd1574 := evm_run h with [push1 ⟨64⟩, dup1,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  have rd1578 := rd1574.pushConst ⟨0x461bcd⟩ (width := 3) (op := .PUSH3)
    (by decide) (by native_decide) (by evm_ov)
  have rd1598 := evm_run rd1578 with [push1 ⟨229⟩, shl, dup2,
    raw mstoreSymbolic (by native_decide) (by evm_ov), push1 ⟨32⟩, push1 ⟨4⟩, dup3, add,
    raw mstoreSymbolic (by native_decide) (by evm_ov), push1 ⟨36⟩, dup2, add, swap2,
    swap1, swap2, raw mstoreSymbolic (by native_decide) (by evm_ov)]
  have rd1631 := rd1598.pushConst
    ⟨0x4d7573742073656e64206d6f7265207468616e206c6173742062696420627920⟩
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd1636 := evm_run rd1631 with [push1 ⟨68⟩, dup3, add,
    raw mstoreSymbolic (by native_decide) (by evm_ov)]
  have rd1669 := rd1636.pushConst
    ⟨0x6d696e426964496e6372656d656e7450657263656e7461676520616d6f756e74⟩
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd994 := evm_run rd1669 with [push1 ⟨100⟩, dup3, add,
    raw mstoreSymbolic (by native_decide) (by evm_ov), push1 ⟨132⟩, add,
    push2 ⟨994⟩, jump (by jump_dest)]
  exact auctionErrorRevert rd994 (by evm_ov)

end Auction
