import Solm.Benchmarks.Auction.ShortError
import Solm.Benchmarks.Auction.SettleGuards

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def pausableErrorPc (i : Fin 4) : UInt256 :=
  match i.val with
  | 0 => ⟨2624⟩
  | 1 => ⟨3667⟩
  | 2 => ⟨2362⟩
  | _ => ⟨2864⟩

def pausableErrorLen (i : Fin 4) : UInt256 := if i.val < 2 then ⟨16⟩ else ⟨20⟩
def pausableErrorWord (i : Fin 4) : UInt256 :=
  if i.val < 2 then ⟨0x14185d5cd8589b194e881c185d5cd959⟩
  else ⟨0x14185d5cd8589b194e881b9bdd081c185d5cd959⟩
def pausableErrorShift (i : Fin 4) : UInt256 := if i.val < 2 then ⟨130⟩ else ⟨98⟩
def pausableErrorOp (i : Fin 4) : Operation.POp := if i.val < 2 then .PUSH16 else .PUSH20
def pausableErrorWidth (i : Fin 4) : Nat := if i.val < 2 then 16 else 20

set_option synthInstance.maxSize 4096 in
theorem pausableErrorWfs : ∀ i : Fin 4,
    shortErrorWf auctionBytecode (pausableErrorPc i) ⟨994⟩ (pausableErrorLen i)
      (pausableErrorWord i) (pausableErrorShift i) (pausableErrorOp i) (pausableErrorWidth i) := by
  unfold shortErrorWf errorHeaderWf errorWordTailWf
  native_decide

theorem pausableError {I g s0 R mem aw rdata acc k C} (i : Fin 4)
    (h : RD auctionBytecode I g s0 (pausableErrorPc i) R mem aw rdata acc k C)
    (hov : R.length + 6 ≤ 1024) : RDrev auctionBytecode g s0 := by
  obtain ⟨_, _, _, _, _, hr⟩ := shortError h (pausableErrorWfs i)
    (by unfold pausableErrorOp; split <;> decide) hov
  exact auctionErrorRevert hr (by omega)

end Auction
