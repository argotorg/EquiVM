import Solm.Benchmarks.Auction.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem evalZeroAddr (cfg : Config) (solm : Frame) (evm : EVM.State) :
    evalExpr? cfg solm evm zeroAddr = .ok (.address (AccountAddress.ofNat 0)) := by
  simp [zeroAddr, addrSt, evalExpr?, EvalResult.bind, EvalResult.ofOption, castValue?, bind, pure]

-- LIBRARY CANDIDATE: testing a canonical address word against zero.
theorem canonicalAddress_eq_zero_iff (value : UInt256)
    (hc : value.toNat < EVM.addressModulus) :
    AccountAddress.ofNat value.toNat = AccountAddress.ofNat 0 ↔ value = ⟨0⟩ := by
  constructor
  · intro h
    have hv := congrArg (fun a => valueToWord (.address a)) h
    dsimp only at hv
    rw [valueToWord_address_ofNat_canonical value hc] at hv
    exact Option.some.inj hv
  · intro h
    rw [h]
    rfl

theorem evalAddressNeZero_true {cfg : Config} {solm : Frame} {evm : EVM.State}
    {expr : Expr} {value : AccountAddress}
    (heval : evalExpr? cfg solm evm expr = .ok (.address value))
    (hz : value ≠ AccountAddress.ofNat 0) :
    evalExpr? cfg solm evm (.binary .ne expr zeroAddr) = .ok (.bool true) := by
  have hv : (Value.address value == Value.address (AccountAddress.ofNat 0)) = false := by
    rw [beq_eq_false_iff_ne]
    exact fun h => hz (Value.address.inj h)
  simp only [evalExpr?, heval, evalZeroAddr, EvalResult.bind, bind, evalBinaryOp?, hv,
    Bool.not_false]

theorem evalAddressNeZero_false {cfg : Config} {solm : Frame} {evm : EVM.State}
    {expr : Expr} {value : AccountAddress}
    (heval : evalExpr? cfg solm evm expr = .ok (.address value))
    (hz : value = AccountAddress.ofNat 0) :
    evalExpr? cfg solm evm (.binary .ne expr zeroAddr) = .ok (.bool false) := by
  have hv : (Value.address value == Value.address (AccountAddress.ofNat 0)) = true := by
    rw [hz]
    exact beq_self_eq_true _
  simp only [evalExpr?, heval, evalZeroAddr, EvalResult.bind, bind, evalBinaryOp?, hv,
    Bool.not_true]

end Auction
