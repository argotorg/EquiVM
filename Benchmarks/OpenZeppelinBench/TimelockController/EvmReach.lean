import Benchmarks.OpenZeppelinBench.TimelockController.Dispatch
import Benchmarks.OpenZeppelinBench.TimelockController.Routines

/-!
# OpenZeppelin TimelockController `hashOperation` EVM reach lemmas (shared)

Reach the `hashOperation` body (pc 988, G194 arm 0) and set up the external 5-arg decoder call
(pc 4600).  Shared by the execute-path (`EvmExec`) and revert-path (`EvmReverts`) proofs.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace OpenZeppelinBench.TimelockController

/-- Reach the `hashOperation` body pc 988 (G194 arm 0, selector `0x8065657f`). -/
theorem tlcReachHashOperation {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 13)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨988⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : tlcSelWord I = ⟨0x8065657f⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x80 0x65 0x65 0x7f ⟨0x8065657f⟩ (by native_decide)
      (by simpa [tlcSelBytes] using hsel)
  exact tlcReachG194Body 0 (by omega) ⟨988⟩ hcode hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
    (by intro j hj; omega)
    (by rw [hsw]; native_decide) (by jump_dest) (by native_decide)

/-- Peel the non-payable guard and set up the decoder call: reach pc 4600 with the decoder's
    argument stack `[4, size, 1014, 581, sel]` (offset, calldatasize, decoder-return, final-return). -/
theorem tlcHashOpReachDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tlcSelBytes 13)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4600⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨1014⟩, ⟨581⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h988⟩ := tlcReachHashOperation (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize hsel
  obtain ⟨_, _, h1001⟩ := tlcGuardPeelOk (gt := ⟨999⟩) h988 hwv (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by jump_dest)
    (by native_decide) (by native_decide)
  exact ⟨_, _, evm_run h1001 with [
    push2 ⟨581⟩, push2 ⟨1014⟩, calldatasize, push1 ⟨4⟩, push2 ⟨4600⟩, jump (by jump_dest)]⟩

end OpenZeppelinBench.TimelockController
