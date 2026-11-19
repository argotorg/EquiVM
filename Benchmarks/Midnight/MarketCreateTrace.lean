import Benchmarks.Midnight.Create2Bridge
import Benchmarks.Midnight.MarketStoreSource
import Benchmarks.Midnight.AddressDecode
import Benchmarks.Midnight.RuntimeBlocks_081

/-! The market deployment instruction and its checked address result. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000 in
theorem midnightMarketCreate {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem rdata : ByteArray} {aw offset size : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (m : MarketData)
    (hstack : R.length + 4 ≤ 1024) (hs : SourceState s0 I σ evm)
    (hperm : I.perm = true)
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hinit : mem.readWithPadding offset.toNat size.toNat = m.initcode)
    (rd : RD midnightBytecode I g s0 ⟨21667⟩ (⟨0⟩ :: offset :: size :: ⟨0⟩ :: R)
      mem aw rdata σ k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (RDrev midnightBytecode g s0 ∧
      ExecFuncBody config frame evm marketStoreCodeFunction.body .reverted) ∨
    ∃ (evm' : State) (σ' : AccountMap) (addr : AccountAddress)
      (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      addr ≠ 0 ∧ SourceState s0 I σ' evm' ∧
      ExecFuncBody config frame evm marketStoreCodeFunction.body
        (.returned (marketStoreCodeResultFrame frame addr) evm' (some [.address addr])) ∧
      RD midnightBytecode I g s0 ⟨21682⟩ R mem aw' out σ' k' C' := by
  have hp : evm.executionEnv.perm = true := hs.env ▸ hperm
  rcases zeroValueCreate2Bridge (cfg := config) (name := "SSTORE2")
    (args := [Model.marketValue m.value]) rd hs (by native_decide) hperm
    m.creationCode hinit (by omega) with
    hoog | ⟨evm', σ', addr, z, out, aw', k', C', hnew, hs', rd'⟩
  · exact Or.inl hoog
  change RD midnightBytecode I g s0 ⟨21668⟩
    ((if z then UInt256.ofNat addr.val else ⟨0⟩) :: R) mem aw' out σ' k' C' at rd'
  cases z with
  | false =>
    simp only [Bool.false_eq_true, if_false] at rd'
    have rd1 := midnightBlocks.midnight_block_21668_taken hstack
      (by decide +kernel) (by jump_dest) rd'
    have rev := midnightBlocks.midnight_block_21745
      (by simp only [midnightBlocks.midnight_block_21668_taken_stack]; omega) rd1
    exact Or.inr (Or.inl ⟨rev, marketStoreCodeFailureSource hm hp hnew⟩)
  | true =>
    simp only [if_true] at rd'
    by_cases ha : addr = 0
    · subst addr
      have rd1 := midnightBlocks.midnight_block_21668_taken hstack
        (by decide +kernel) (by jump_dest) rd'
      have rev := midnightBlocks.midnight_block_21745
        (by simp only [midnightBlocks.midnight_block_21668_taken_stack]; omega) rd1
      exact Or.inr (Or.inl ⟨rev, marketStoreCodeZeroSource hm hp hnew⟩)
    · have hab : addr.val < UInt256.size := lt_trans addr.isLt (by decide)
      have hc : (UInt256.ofNat addr.val).toNat < EVM.addressModulus := by
        rw [UInt256.toNat_ofNat_of_lt hab]
        exact addr.isLt
      have hn : UInt256.ofNat addr.val ≠ ⟨0⟩ := by
        intro hz
        apply ha
        apply Fin.ext
        have hv := congrArg UInt256.toNat hz
        rw [UInt256.toNat_ofNat_of_lt hab] at hv
        exact hv
      have rd1 := midnightBlocks.midnight_block_21668_fallthrough hstack
        (by rw [addressMask_computed, solcAddrMask_clean_left hc]
            exact isZero_eq_zero_of_ne hn) rd'
      exact Or.inr (Or.inr ⟨evm', σ', addr, out, aw', _, _, ha, hs',
        marketStoreCodeSuccessSource hm hp ha hnew, rd1⟩)

end Benchmarks.Midnight
