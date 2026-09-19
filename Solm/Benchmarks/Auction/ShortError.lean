import Solm.Benchmarks.Auction.ErrorStringParts

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

-- GENERALIZES Reasoning.Reach.RD.solcErrorStringRevertTail to a shared revert continuation
-- and symbolic memory; this compiler omits the leading DUP1 and jumps to its common epilogue.
def shortErrorWf (code : ByteArray) (pc ret len word shift : UInt256)
    (op : Operation.POp) (width : Nat) : Prop :=
  let pWord := errorHeaderEnd pc + UInt256.ofNat width.succ
  errorHeaderWf code pc len ∧
  decode code (errorHeaderEnd pc) = some (.Push op, some (word, width)) ∧
  decode code pWord = some (.Push .PUSH1, some (shift, 1)) ∧
  decode code (pWord + UInt256.ofNat 2) = some (.SHL, .none) ∧
  errorWordTailWf code ((pWord + UInt256.ofNat 2) + ⟨1⟩) ret

theorem shortError {code I g s0 pc ret len word shift op width R mem aw rdata acc k C}
    (h : RD code I g s0 pc R mem aw rdata acc k C)
    (hwf : shortErrorWf code pc ret len word shift op width) (hpush : op ≠ .PUSH0)
    (hov : R.length + 6 ≤ 1024) :
    ∃ finish mem' aw' k' C', RD code I g s0 ret (finish :: R) mem' aw' rdata acc k' C' := by
  obtain ⟨hhead, dWord, dShift, dShl, htail⟩ := hwf
  obtain ⟨_, _, _, _, _, rdWord⟩ := errorHeader h hhead hov
  have rdShift := rdWord.pushConst word (width := width) (op := op) hpush dWord (by evm_ov)
  have rdTail := evm_run rdShift with [raw push1 shift dShift (by evm_ov),
    raw shl dShl (by evm_ov)]
  exact errorWordTail rdTail htail (by omega)

-- The same encoder also occurs with a full PUSH32 literal and no shift.
def literalErrorWf (code : ByteArray) (pc ret len word : UInt256) : Prop :=
  errorHeaderWf code pc len ∧
  decode code (errorHeaderEnd pc) = some (.Push .PUSH32, some (word, 32)) ∧
  errorWordTailWf code (errorHeaderEnd pc + UInt256.ofNat 33) ret

theorem literalError {code I g s0 pc ret len word R mem aw rdata acc k C}
    (h : RD code I g s0 pc R mem aw rdata acc k C)
    (hwf : literalErrorWf code pc ret len word) (hov : R.length + 6 ≤ 1024) :
    ∃ finish mem' aw' k' C', RD code I g s0 ret (finish :: R) mem' aw' rdata acc k' C' := by
  obtain ⟨hhead, dWord, htail⟩ := hwf
  obtain ⟨_, _, _, _, _, rdWord⟩ := errorHeader h hhead hov
  have rdTail := rdWord.pushConst word (width := 32) (op := .PUSH32)
    (by decide) dWord (by evm_ov)
  exact errorWordTail rdTail htail (by omega)

end Auction
