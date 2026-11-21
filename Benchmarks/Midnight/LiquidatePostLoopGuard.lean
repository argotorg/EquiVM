import Benchmarks.Midnight.LiquidateEligibilityTrace
import Benchmarks.Midnight.LiquidateEligibilitySource

/-! The matching source and runtime guard after the collateral loop. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightLiquidatePostLoopGuard {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem rdata data : ByteArray} {m : MarketData}
    {id target seized repaid borrower mode maxDebt price badDebt debtWord reverseRep rep dp dl
      receiverWord root budgetRoot aw : UInt256} {receiver callback : AccountAddress}
    {credit : Nat} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 22 ≤ 1024) (hcanon : borrower.toNat < EVM.addressModulus)
    (hd : decodeCalldataMarket I.calldata 4 = some m)
    (hroot : root.toNat + 128 < 2^64) (hlower : 96 ≤ root.toNat)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hid : memLoad (UInt256.ofNat 768) mem = id)
    (hf : LiquidateSourceFrame frame m id target seized repaid borrower mode receiver callback data)
    (ha : LiquidateAccumulators frame ⟨0⟩ maxDebt price (low128 debtWord) badDebt)
    (hs : SourceState s0 I σ evm) (hb : TransferBudget budgetRoot credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨5358⟩
      ([debtWord, reverseRep, rep, maxDebt, price, positionSlot id borrower, dp, dl,
        borrower, badDebt, receiverWord, mode] ++ R) mem aw rdata σ k C) (rest : List Stmt) :
    (ExecBlock config frame evm ((liquidateTransition.body.drop 15).take 2 ++ rest) .reverted ∧
      RDrev midnightBytecode g s0) ∨
    ∃ aw' k' C',
      ABlock config evm frame ((liquidateTransition.body.drop 15).take 2 ++ rest)
        (liquidateLockFrame frame evm id borrower) rest ∧
      LiquidateEligible I m (codeOwnerTransientWord I σ (lockSlot liquidationLockBase id borrower))
        mode (low128 debtWord) maxDebt ∧
      MemoryPrefix mem (dynamicLockMemory mem root id borrower) root.toNat ∧
      memLoad (UInt256.ofNat 64) (dynamicLockMemory mem root id borrower) =
        root + UInt256.ofNat 128 ∧
      TransferBudget budgetRoot credit (dynamicLockMemory mem root id borrower) aw' C' ∧
      RD midnightBytecode I g s0 ⟨5463⟩
        ([debtWord, reverseRep, rep, maxDebt, price, positionSlot id borrower, dp, dl,
          borrower, badDebt, receiverWord, mode] ++ R)
        (dynamicLockMemory mem root id borrower) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, hb1, rd1⟩ := midnightLiquidateLockAllocation
    (R := [badDebt, receiverWord, mode] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    hcanon hroot hfree hid hb rd
  have ht : Stele.EVM.transientLoad evm evm.executionEnv.codeOwner
      (lockSlot liquidationLockBase id borrower) =
      codeOwnerTransientWord I σ (lockSlot liquidationLockBase id borrower) := by
    change codeOwnerTransientWord evm.executionEnv evm.accountMap _ = _
    rw [hs.env, ← hs.accounts]
  have hsource := liquidateEligibilitySource (evm := evm) hf ha hcanon rest
  dsimp only at hsource
  rw [ht, hs.env] at hsource
  rcases midnightLiquidateEligibility (R := R) (by omega) hd
      (dynamicLockMemory_length mem id borrower hlower)
      (dynamicLockMemory_hash mem id borrower hlower (by change _ < 2^256; omega)) hb1 rd1 with
    ⟨hbad, hrev⟩ | ⟨hgood, aw2, k2, C2, hb2, rd2⟩
  · rcases hsource with ⟨_, hrevSource⟩ | ⟨hgood, _⟩
    · exact Or.inl ⟨hrevSource, hrev⟩
    · exact False.elim (hbad hgood)
  · rcases hsource with ⟨hbad, _⟩ | ⟨_, hsource⟩
    · exact False.elim (hbad hgood)
    · exact Or.inr ⟨aw2, k2, C2, hsource, hgood, dynamicLockMemory_prefix mem root id borrower,
        dynamicLockMemory_free mem root id borrower, hb2, rd2⟩

end Benchmarks.Midnight
