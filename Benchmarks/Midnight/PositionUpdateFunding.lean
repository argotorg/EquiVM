import Benchmarks.Midnight.PositionUpdateInternalBudget

variable {fork : Ethereum.Fork}

/-! The position update preserves unconditional memory funding. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- GENERALIZES the retained-resource guarantee to unconditional MemoryFunding.
-- This budget parameter makes TransferBudget's small-heap alternative false.
theorem midnightPositionUpdateInternal_funded {evm : EVM.State} {g : Sat256} {s0 : State}
    {imms : Store} {m : MarketData} {mem rdata : ByteArray} {aw root ptr id user ret : UInt256}
    {gasCredit : Nat}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 27 ≤ 1024)
    (hcanon : user.toNat < EVM.addressModulus)
    (hlo : 64 ≤ (ptr + UInt256.ofNat 128).toNat)
    (hhi : (ptr + UInt256.ofNat 128).toNat + 32 ≤ mem.size)
    (hmaturity : memLoad (ptr + UInt256.ofNat 128) mem = m.maturity)
    (hrootlo : 96 ≤ root.toNat) (hroot : root.toNat < 2^64)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (ha : MemoryFunding gasCredit mem aw C)
    (rd : RD fork midnightBytecode evm.executionEnv g s0 ⟨23599⟩ (ptr :: id :: user :: ret :: R)
      mem aw rdata evm.accountMap k C) :
    let credit := positionNewCredit evm m id user
    let pending := positionNewPending evm m id user
    let fee := positionViewFee evm m id user
    (RDrev fork midnightBytecode g s0 ∧
      ExecFuncBody fork config (positionViewCallFrame imms m id user) evm positionUpdateFunction.body
        .reverted) ∨
    (RDstatic fork midnightBytecode g s0 ∧
      ExecFuncBody fork config (positionViewCallFrame imms m id user) evm positionUpdateFunction.body
        .staticViolation) ∨
    (evm.executionEnv.perm = true ∧
      credit.toNat < 2^128 ∧ pending.toNat < 2^128 ∧ fee.toNat < 2^128 ∧
      ExecFuncBody fork config (positionViewCallFrame imms m id user) evm positionUpdateFunction.body
        (.returned (positionUpdateFinalFrame evm imms m id user)
          (positionUpdateFinalState evm m id user)
          (some [.int credit.toNat, .int pending.toNat, .int fee.toNat])) ∧
      ∃ aw' k' C',
        MemoryFunding gasCredit
          (positionUpdateLogMemory mem root evm m id user) aw' C' ∧
        RD fork midnightBytecode evm.executionEnv g s0 ret (fee :: pending :: credit :: R)
        (positionUpdateLogMemory mem root evm m id user) aw' rdata
        (positionUpdateFinalState evm m id user).accountMap k' C') := by
  have hb : TransferBudget (UInt256.ofNat (2^62)) gasCredit mem aw C :=
    Or.inr ⟨by decide, ha⟩
  rcases midnightPositionUpdateInternal_budget hstack hcanon hlo hhi hmaturity
      hrootlo hroot hfree hret hb rd with
    ⟨hr, hx⟩ | ⟨hr, hx⟩ | ⟨hperm, hc, hp, hf, hx, aw1, k1, C1, hb1, rd1⟩
  · exact Or.inl ⟨hr, hx⟩
  · exact Or.inr (Or.inl ⟨hr, hx⟩)
  · have ha1 : MemoryFunding gasCredit
        (positionUpdateLogMemory mem root evm m id user) aw1 C1 := by
      rcases hb1 with hsmall | ⟨_, hfund⟩
      · exact False.elim ((by decide : ¬ (UInt256.ofNat (2^62)).toNat + 160 ≤ 2^62) hsmall)
      · exact hfund
    exact Or.inr (Or.inr ⟨hperm, hc, hp, hf, hx, aw1, k1, C1, ha1, rd1⟩)

end Benchmarks.Midnight
