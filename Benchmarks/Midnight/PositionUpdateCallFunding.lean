import Benchmarks.Midnight.PositionUpdateFunding
import Benchmarks.Midnight.PositionUpdateCall
import Benchmarks.Midnight.MarketHeapAccess
import Reasoning.ExternalCall

variable {fork : Ethereum.Fork}

/-! A position-update call preserves source state, allocated memory, and memory funding. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def positionUpdateCallerFrame (frame : Frame) (evm : State) (m : MarketData)
    (id user : UInt256) (name : Ident) : Frame :=
  resumeAfterInternalCall frame name (some [.int (positionNewCredit evm m id user).toNat,
    .int (positionNewPending evm m id user).toNat, .int (positionViewFee evm m id user).toNat])

theorem positionUpdateSourceState {s0 evm : State} {I : ExecutionEnv}
    (hs : SourceState s0 I evm.accountMap evm) (m : MarketData) (id user : UInt256) :
    SourceState s0 I (positionUpdateFinalState evm m id user).accountMap
      (positionUpdateFinalState evm m id user) := by
  refine ⟨?_, (positionUpdateFinalState_env ..).trans hs.env, rfl⟩
  simpa only [positionUpdateFinalState, positionUpdateFeeState, positionUpdatedBalances,
    positionUpdateState, storeLow128, storeHigh128, storageStore_σ₀] using hs.world

theorem midnightPositionUpdateCall {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {frame : Frame} {m : MarketData} {mem rdata : ByteArray}
    {aw ptr array heap root id user ret : UInt256} {args : List Expr} {name : Ident}
    {k C : Nat} {R : List UInt256}
    (hstack : R.length + 27 ≤ 1024) (hcanon : user.toNat < EVM.addressModulus)
    (hc : frame.contract = contract)
    (he : evalExprs? config frame evm args =
      .ok [Model.marketValue m.value, wordBytes32Value id,
        .address (AccountAddress.ofNat user.toNat)])
    (hs : SourceState s0 I evm.accountMap evm) (hm : MarketStored mem ptr array heap m)
    (hrootlo : 96 ≤ root.toNat) (hroot : root.toNat < 2^64)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨23599⟩ (ptr :: id :: user :: ret :: R)
      mem aw rdata evm.accountMap k C) :
    (ExecStmt fork config frame evm (.internalCall "_updatePosition" args name) .reverted ∧
      RDrev fork midnightBytecode g s0) ∨
    (ExecStmt fork config frame evm (.internalCall "_updatePosition" args name) .staticViolation ∧
      RDstatic fork midnightBytecode g s0) ∨
    (let evm' := positionUpdateFinalState evm m id user
     let mem' := positionUpdateLogMemory mem root evm m id user
     ExecStmt fork config frame evm (.internalCall "_updatePosition" args name)
       (.ok (positionUpdateCallerFrame frame evm m id user name) evm') ∧
     SourceState s0 I evm'.accountMap evm' ∧ MemoryPrefix mem mem' root.toNat ∧
     memLoad (UInt256.ofNat 64) mem' = root ∧
     ∃ aw' k' C', MemoryFunding credit mem' aw' C' ∧
       RD fork midnightBytecode I g s0 ret
         (positionViewFee evm m id user :: positionNewPending evm m id user ::
           positionNewCredit evm m id user :: R) mem' aw' rdata evm'.accountMap k' C') := by
  have hoff : (ptr + UInt256.ofNat 128).toNat = ptr.toNat + 128 :=
    uadd_word_ofNat_toNat _ _ (by
      have := hm.array
      have := hm.extent
      have := hm.bound
      change _ < 2^256
      omega)
  have hlo : 64 ≤ (ptr + UInt256.ofNat 128).toNat := by rw [hoff]; omega
  have hhi : (ptr + UInt256.ofNat 128).toNat + 32 ≤ mem.size := by
    rw [hoff]
    have hw := hm.words.size
    change ptr.toNat + 32 * 8 ≤ mem.size at hw
    omega
  rcases midnightPositionUpdateInternal_funded (evm := evm) (g := g) (s0 := s0)
      (m := m) (id := id) (rdata := rdata) (k := k) (imms := frame.immutables) hstack hcanon
      hlo hhi hm.maturity hrootlo hroot hfree hret ha (by simpa only [hs.env] using rd) with
    ⟨hr, hx⟩ | ⟨hr, hx⟩ | ⟨_, _, _, _, hx, aw1, k1, C1, ha1, rd1⟩
  · exact Or.inl ⟨callPositionUpdateRevert hc he hx, hr⟩
  · exact Or.inr (Or.inl ⟨callPositionUpdateStatic hc he hx, hr⟩)
  · exact Or.inr (Or.inr ⟨callPositionUpdate hc he hx, positionUpdateSourceState hs m id user,
      positionUpdateLogMemory_prefix mem root evm m id user,
      positionUpdateLogMemory_free mem root evm m id user (by omega) hrootlo hfree,
      aw1, k1, C1, ha1, by simpa only [hs.env] using rd1⟩)

end Benchmarks.Midnight
