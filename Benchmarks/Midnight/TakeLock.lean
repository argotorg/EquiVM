import Benchmarks.Midnight.LockExchangeSource
import Benchmarks.Midnight.TakeEventTrace
import Benchmarks.Midnight.RuntimeBlocks_049

/-! Setting the seller's liquidation lock before the buyer callback. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def takeLockFrame (frame : Frame) (evm : State) (id seller : UInt256) : Frame :=
  resumeAfterInternalCall frame "wasLocked" (some [lockValue evm liquidationLockBase id seller])

theorem takeLockSource {frame : Frame} {evm : State} {id seller : UInt256}
    (hc : frame.contract = contract) (hcanon : seller.toNat < EVM.addressModulus)
    (hi : frame.locals.get? "id" = some (wordBytes32Value id))
    (hs : frame.locals.get? "seller" = some (.address (AccountAddress.ofNat seller.toNat)))
    (hp : evm.executionEnv.perm = true) :
    ExecStmt config frame evm takeTransition.body[66]!
      (.ok (takeLockFrame frame evm id seller)
        (lockExchangeState evm liquidationLockBase id seller true)) := by
  apply callLockExchange hc hcanon
  · change evalExprs? config frame evm
      [.cast (.keccak256 (.bytesLit "morpho.midnight.liquidationLocked".toByteArray))
        (.elem (.int (.uint ⟨256, by decide⟩))), .var "id", .var "seller", .boolLit true] = _
    rw [evalExprs?, evalLiquidationLockBase]
    simp only [evalExprs?, evalExpr?, hi, hs, EvalResult.ofOption, EvalResult.bind, bind, pure]
    rfl
  · exact hp

theorem midnightTakeLockTrace {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw root id seller buyerCallback sellerCallback payer : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 7 ≤ 1024)
    (hroot : 96 ≤ root.toNat) (hb : root.toNat + 128 < UInt256.size)
    (hcb : buyerCallback.toNat < EVM.addressModulus) (hp : I.perm = true)
    (ha : MemoryFunding credit (dynamicLockMemory mem root id seller) aw C)
    (rd : RD midnightBytecode I g s0 ⟨13223⟩
      ([root, sellerCallback, payer, buyerCallback] ++ R)
      (dynamicLockMemory mem root id seller) aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit (dynamicLockMemory mem root id seller) aw' C' ∧
      RD midnightBytecode I g s0 (if buyerCallback = ⟨0⟩ then ⟨13252⟩ else ⟨13774⟩)
        ([buyerCallback, sellerCallback, payer,
          codeOwnerTransientWord I σ (lockSlot liquidationLockBase id seller)] ++ R)
        (dynamicLockMemory mem root id seller) aw' rdata
        (tstoreAccountMap I.codeOwner σ (lockSlot liquidationLockBase id seller) ⟨1⟩) k' C' := by
  have hl := dynamicLockMemory_length mem id seller hroot
  have hh := dynamicLockMemory_hash mem id seller hroot hb
  simp only [List.cons_append, List.nil_append] at rd
  by_cases hz : buyerCallback = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_13223_fallthrough hstack hp
      (by rw [addressMask_computed, solcAddrMask_clean hcb, hz]; rfl) rd
    have ha1 := memoryFundingAt (credit := credit) rd1 (by memory_fund ha)
    simp only [midnightBlocks.midnight_block_13223_fallthrough_stack, hl, hh] at rd1 ha1
    rw [if_pos hz]
    exact ⟨_, _, _, ha1, rd1⟩
  · have rd1 := midnightBlocks.midnight_block_13223_taken hstack hp
      (by rw [addressMask_computed, solcAddrMask_clean hcb]; exact hz) (by jump_dest) rd
    have ha1 := memoryFundingAt (credit := credit) rd1 (by memory_fund ha)
    simp only [midnightBlocks.midnight_block_13223_taken_stack, hl, hh] at rd1 ha1
    rw [if_neg hz]
    exact ⟨_, _, _, ha1, rd1⟩

theorem midnightTakeLock {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem rdata : ByteArray}
    {aw root id seller buyerCallback sellerCallback payer : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 7 ≤ 1024)
    (hc : frame.contract = contract) (hcanon : seller.toNat < EVM.addressModulus)
    (hi : frame.locals.get? "id" = some (wordBytes32Value id))
    (hsel : frame.locals.get? "seller" = some (.address (AccountAddress.ofNat seller.toNat)))
    (hroot : 96 ≤ root.toNat) (hb : root.toNat + 128 < UInt256.size)
    (hcb : buyerCallback.toNat < EVM.addressModulus) (hp : I.perm = true)
    (hs : SourceState s0 I σ evm)
    (ha : MemoryFunding credit (dynamicLockMemory mem root id seller) aw C)
    (rd : RD midnightBytecode I g s0 ⟨13223⟩
      ([root, sellerCallback, payer, buyerCallback] ++ R)
      (dynamicLockMemory mem root id seller) aw rdata σ k C) :
    ∃ σ' aw' k' C',
      (∀ result, ExecBlock config (takeLockFrame frame evm id seller)
          (lockExchangeState evm liquidationLockBase id seller true)
          (takeTransition.body.drop 67) result →
        ExecBlock config frame evm (takeTransition.body.drop 66) result) ∧
      SourceState s0 I σ' (lockExchangeState evm liquidationLockBase id seller true) ∧
      MemoryFunding credit (dynamicLockMemory mem root id seller) aw' C' ∧
      RD midnightBytecode I g s0 (if buyerCallback = ⟨0⟩ then ⟨13252⟩ else ⟨13774⟩)
        ([buyerCallback, sellerCallback, payer,
          Stele.EVM.transientLoad evm evm.executionEnv.codeOwner
            (lockSlot liquidationLockBase id seller)] ++ R)
        (dynamicLockMemory mem root id seller) aw' rdata σ' k' C' := by
  obtain ⟨aw', k', C', ha', rd'⟩ := midnightTakeLockTrace hstack hroot hb hcb hp ha rd
  rw [← sourceState_transientRead hs] at rd'
  refine ⟨_, aw', k', C', ?_, sourceState_transientWrite hs _ ⟨1⟩, ha', rd'⟩
  intro result hx
  change ExecBlock config frame evm
    (takeTransition.body[66]! :: takeTransition.body.drop 67) result
  exact ExecBlock.consNormal (takeLockSource hc hcanon hi hsel (by rw [hs.env]; exact hp)) hx

end Benchmarks.Midnight
