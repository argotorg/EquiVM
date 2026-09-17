import Benchmarks.Auction.DynamicMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

-- LIBRARY CANDIDATE: split a shared Error(string) encoder into header and final word.
def errorHeaderEnd (pc : UInt256) : UInt256 :=
  ((((((((((((((((pc + ⟨2⟩) + ⟨1⟩) + ⟨4⟩) + ⟨2⟩) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩) + ⟨2⟩) +
    ⟨2⟩) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩) + ⟨2⟩) + ⟨2⟩) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩

def errorHeaderWf (code : ByteArray) (pc len : UInt256) : Prop :=
  let p2 := pc + UInt256.ofNat 2
  let p3 := p2 + ⟨1⟩
  let p7 := p3 + UInt256.ofNat 4
  let p9 := p7 + UInt256.ofNat 2
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p14 := p12 + UInt256.ofNat 2
  let p16 := p14 + UInt256.ofNat 2
  let p17 := p16 + ⟨1⟩
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p21 := p19 + UInt256.ofNat 2
  let p23 := p21 + UInt256.ofNat 2
  let p24 := p23 + ⟨1⟩
  let p25 := p24 + ⟨1⟩
  decode code pc = some (.Push .PUSH1, some (⟨64⟩, 1)) ∧
  decode code p2 = some (.MLOAD, .none) ∧
  decode code p3 = some (.Push .PUSH3, some (⟨4594637⟩, 3)) ∧
  decode code p7 = some (.Push .PUSH1, some (⟨229⟩, 1)) ∧
  decode code p9 = some (.SHL, .none) ∧
  decode code p10 = some (.DUP2, .none) ∧
  decode code p11 = some (.MSTORE, .none) ∧
  decode code p12 = some (.Push .PUSH1, some (⟨32⟩, 1)) ∧
  decode code p14 = some (.Push .PUSH1, some (⟨4⟩, 1)) ∧
  decode code p16 = some (.DUP3, .none) ∧
  decode code p17 = some (.ADD, .none) ∧
  decode code p18 = some (.MSTORE, .none) ∧
  decode code p19 = some (.Push .PUSH1, some (len, 1)) ∧
  decode code p21 = some (.Push .PUSH1, some (⟨36⟩, 1)) ∧
  decode code p23 = some (.DUP3, .none) ∧
  decode code p24 = some (.ADD, .none) ∧
  decode code p25 = some (.MSTORE, .none)

theorem errorHeader {code I g s0 pc len R mem aw rdata acc k C}
    (h : RD code I g s0 pc R mem aw rdata acc k C)
    (hwf : errorHeaderWf code pc len) (hov : R.length + 6 ≤ 1024) :
    ∃ ptr mem' aw' k' C', RD code I g s0 (errorHeaderEnd pc) (ptr :: R)
      mem' aw' rdata acc k' C' := by
  obtain ⟨d0, d2, d3, d7, d9, d10, d11, d12, d14, d16, d17, d18, d19, d21, d23,
    d24, d25⟩ := hwf
  have rd3 := evm_run h with [raw push1 ⟨64⟩ d0 (by evm_ov),
    raw mloadSymbolic d2 (by evm_ov)]
  have rd7 := rd3.pushConst ⟨4594637⟩ (width := 3) (op := .PUSH3)
    (by decide) d3 (by evm_ov)
  exact ⟨_, _, _, _, _, evm_run rd7 with [raw push1 ⟨229⟩ d7 (by evm_ov),
    raw shl d9 (by evm_ov), raw dup2 d10 (by evm_ov), raw mstoreSymbolic d11 (by evm_ov),
    raw push1 ⟨32⟩ d12 (by evm_ov), raw push1 ⟨4⟩ d14 (by evm_ov), raw dup3 d16 (by evm_ov),
    raw add d17 (by evm_ov), raw mstoreSymbolic d18 (by evm_ov), raw push1 len d19 (by evm_ov),
    raw push1 ⟨36⟩ d21 (by evm_ov), raw dup3 d23 (by evm_ov), raw add d24 (by evm_ov),
    raw mstoreSymbolic d25 (by evm_ov)]⟩

def errorWordTailWf (code : ByteArray) (pc ret : UInt256) : Prop :=
  let pDup := pc + UInt256.ofNat 2
  let pAdd := pDup + ⟨1⟩
  let pStore := pAdd + ⟨1⟩
  let p100 := pStore + ⟨1⟩
  let pEnd := p100 + UInt256.ofNat 2
  let pRet := pEnd + ⟨1⟩
  let pJump := pRet + UInt256.ofNat 3
  decode code pc = some (.Push .PUSH1, some (⟨68⟩, 1)) ∧
  decode code pDup = some (.DUP3, .none) ∧
  decode code pAdd = some (.ADD, .none) ∧
  decode code pStore = some (.MSTORE, .none) ∧
  decode code p100 = some (.Push .PUSH1, some (⟨100⟩, 1)) ∧
  decode code pEnd = some (.ADD, .none) ∧
  decode code pRet = some (.Push .PUSH2, some (ret, 2)) ∧
  decode code pJump = some (.JUMP, .none) ∧
  (D_J code 0).contains ret = true

theorem errorWordTail {code I g s0 pc ret word ptr R mem aw rdata acc k C}
    (h : RD code I g s0 pc (word :: ptr :: R) mem aw rdata acc k C)
    (hwf : errorWordTailWf code pc ret) (hov : R.length + 4 ≤ 1024) :
    ∃ finish mem' aw' k' C', RD code I g s0 ret (finish :: R) mem' aw' rdata acc k' C' := by
  obtain ⟨d68, dDup, dAdd, dStore, d100, dEnd, dRet, dJump, hret⟩ := hwf
  exact ⟨_, _, _, _, _, evm_run h with [raw push1 ⟨68⟩ d68 (by evm_ov),
    raw dup3 dDup (by evm_ov), raw add dAdd (by evm_ov),
    raw mstoreSymbolic dStore (by evm_ov), raw push1 ⟨100⟩ d100 (by evm_ov),
    raw add dEnd (by evm_ov), raw push2 ret dRet (by evm_ov),
    raw jump dJump hret (by evm_ov)]⟩

end Auction
