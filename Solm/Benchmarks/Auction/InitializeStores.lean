import Solm.Benchmarks.Auction.InitializeArgs
import Solm.Benchmarks.Auction.InitializerStorage
import Solm.Benchmarks.Auction.PackedByte

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000

namespace Auction

def InitializeArgs.storeMap (args : InitializeArgs) (σ : AccountMap) (I : ExecutionEnv) :
    AccountMap :=
  let σ1 := sstoreAccountMap I.codeOwner σ ⟨201⟩
    (setAddressOffset0Word (storedWord σ I ⟨201⟩) args.nouns)
  let σ2 := sstoreAccountMap I.codeOwner σ1 ⟨202⟩
    (setAddressOffset0Word (storedWord σ1 I ⟨202⟩) args.weth)
  let σ3 := sstoreAccountMap I.codeOwner σ2 ⟨203⟩ args.timeBuffer
  let σ4 := sstoreAccountMap I.codeOwner σ3 ⟨204⟩ args.reservePrice
  let σ5 := sstoreAccountMap I.codeOwner σ4 ⟨205⟩
    (UInt256.lor (UInt256.land (storedWord σ4 I ⟨205⟩) (UInt256.lnot ⟨255⟩))
      args.minBidIncrement)
  sstoreAccountMap I.codeOwner σ5 ⟨206⟩ args.duration

def initializerExited (σ : AccountMap) (I : ExecutionEnv) (top : UInt256) : AccountMap :=
  if top = ⟨0⟩ then σ else
    sstoreAccountMap I.codeOwner σ ⟨0⟩ (initializerEndWord (storedWord σ I ⟨0⟩))

theorem initializeStoreArgs {I g s0 top ret R mem aw rdata cA σ k C} (args : InitializeArgs)
    (h : RD auctionBytecode I g s0 ⟨2245⟩ (top :: args.words.reverse ++ ret :: R)
      mem aw rdata (cA, σ) k C)
    (hc : args.canonical) (hperm : I.perm = true) (hov : R.length + 15 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨2326⟩ (top :: args.words.reverse ++ ret :: R)
      mem aw rdata (cA, args.storeMap σ I) k' C' := by
  change RD _ _ _ _ _
    (top :: args.duration :: args.minBidIncrement :: args.reservePrice :: args.timeBuffer ::
      args.weth :: args.nouns :: ret :: R) _ _ _ _ _ _ at h
  have rd2249 := evm_run h with [jumpdest, push1 ⟨201⟩, dup1]
  obtain ⟨_, _, rd2250⟩ := rd2249.sload (by native_decide) (by evm_ov)
  have rd2276 := evm_run rd2250 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup1, dup11, and,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, swap3, dup4, and,
    or, swap1, swap3 ]
  obtain ⟨_, _, rd2277⟩ := rd2276.sstore hperm (by native_decide) (by evm_ov)
  have rd2280 := evm_run rd2277 with [push1 ⟨202⟩, dup1]
  obtain ⟨_, _, rd2281⟩ := rd2280.sload (by native_decide) (by evm_ov)
  have rd2293 := evm_run rd2281 with [
    swap3, dup10, and, swap3, swap1, swap2, and, swap2, swap1, swap2, or, swap1 ]
  obtain ⟨_, _, rd2294⟩ := rd2293.sstore hperm (by native_decide) (by evm_ov)
  have rd2298 := evm_run rd2294 with [push1 ⟨203⟩, dup6, swap1]
  obtain ⟨_, _, rd2299⟩ := rd2298.sstore hperm (by native_decide) (by evm_ov)
  have rd2303 := evm_run rd2299 with [push1 ⟨204⟩, dup5, swap1]
  obtain ⟨_, _, rd2304⟩ := rd2303.sstore hperm (by native_decide) (by evm_ov)
  have rd2307 := evm_run rd2304 with [push1 ⟨205⟩, dup1]
  obtain ⟨_, _, rd2308⟩ := rd2307.sload (by native_decide) (by evm_ov)
  have rd2320 := evm_run rd2308 with [
    push1 ⟨255⟩, dup6, and, push1 ⟨255⟩, not, swap1, swap2, and, or, swap1 ]
  obtain ⟨_, _, rd2321⟩ := rd2320.sstore hperm (by native_decide) (by evm_ov)
  have rd2325 := evm_run rd2321 with [push1 ⟨206⟩, dup3, swap1]
  obtain ⟨_, _, rd2326⟩ := rd2325.sstore hperm (by native_decide) (by evm_ov)
  have hm : UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  simp only [hm, u256_land_comm (UInt256.lnot solcAddrMask), lowByteClean hc.2.2]
    at rd2326
  exact ⟨_, _, rd2326⟩

theorem initializeExit {I g s0 top ret R mem aw rdata cA σ k C} (args : InitializeArgs)
    (h : RD auctionBytecode I g s0 ⟨2326⟩ (top :: args.words.reverse ++ ret :: R)
      mem aw rdata (cA, σ) k C)
    (hperm : I.perm = true) (hret : (D_J auctionBytecode 0).contains ret = true)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret R mem aw rdata
      (cA, initializerExited σ I top) k' C' := by
  change RD _ _ _ _ _
    (top :: args.duration :: args.minBidIncrement :: args.reservePrice :: args.timeBuffer ::
      args.weth :: args.nouns :: ret :: R) _ _ _ _ _ _ at h
  by_cases ht : top = ⟨0⟩
  · rw [initializerExited, if_pos ht]
    have rd2342 := evm_run h with [dup1, iszero, push2 ⟨2342⟩, jumpiT (by rw [ht]; decide)
      (by jump_dest)]
    exact ⟨_, _, evm_run rd2342 with [jumpdest, pop, pop, pop, pop, pop, pop, pop, jump hret]⟩
  · rw [initializerExited, if_neg ht]
    have rd2334 := evm_run h with [
      dup1, iszero, push2 ⟨2342⟩, jumpiNT (isZero_eq_zero_of_ne ht), push0, dup1 ]
    obtain ⟨_, _, rd2335⟩ := rd2334.sload (by native_decide) (by evm_ov)
    have rd2341 := evm_run rd2335 with [push2 ⟨65280⟩, not, and, swap1]
    obtain ⟨_, _, rd2342⟩ := rd2341.sstore hperm (by native_decide) (by evm_ov)
    change RD _ _ _ _ _ _ _ _ _ (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩
      (UInt256.land (UInt256.lnot ⟨65280⟩) (storedWord σ I ⟨0⟩))) _ _ at rd2342
    rw [u256_land_comm (UInt256.lnot ⟨65280⟩)] at rd2342
    exact ⟨_, _, evm_run rd2342 with [jumpdest, pop, pop, pop, pop, pop, pop, pop, jump hret]⟩

end Auction
