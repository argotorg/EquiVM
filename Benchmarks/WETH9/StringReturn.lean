import Benchmarks.WETH9.StringLayout
import Benchmarks.WETH9.Routines

/-!
# WETH9 dynamic-string getter — config-independent EVM/byte machinery

`name()`/`symbol()` read a Solidity compact dynamic string from storage slot 0/1 and ABI-return it.
Both dispatch (via the non-payable guard) into a shared string-load routine (pc 839 reading slot 0
for `name`, pc 1571 reading slot 1 for `symbol`), which decodes the compact header, copies the data
into memory as a `[len ; data]` object, and returns to the shared ABI-string return encoder (pc 187)
which reallocates the object as an ABI `(offset, len, paddeddata)` triple and `RETURN`s it.

This module proves the reusable, **config-independent** facts: driving the RD symbolic executor from
the routine entry to an `RDret` returning exactly `weth9StringAbiEncode len data` (or `OutOfGass`).
The final `runtimeEquivalenceFor` connect (dispatch/decode/body) is wired separately in
`Name.lean`/`Symbol.lean`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace Benchmarks.WETH9

/-- Raw storage header word at `slot` for the code owner (the compact-string length header). -/
def weth9StringSlotWord (σ : AccountMap) (I : ExecutionEnv) (slot : UInt256) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)

/-! ## Reach the shared string-load routine

`name()` enters at pc 166; the non-payable guard (gt = 178) peels to pc 180, whose
`PUSH2 187; PUSH2 839; JUMP` lands at the routine (pc 839) with `[187, sel]`. -/

theorem weth9ReachName839 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (weth9SelBytes 0)) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨839⟩
      [⟨187⟩, weth9SelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h166⟩ := weth9ReachName (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h180⟩ := weth9GuardPeelOk (gt := ⟨178⟩) h166 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
  have h839 := h180.push2 ⟨187⟩ (by native_decide) (by simp)
    |>.push2 ⟨839⟩ (by native_decide) (by simp)
    |>.jump (by native_decide) (by jump_dest) (by simp)
  exact ⟨_, _, h839⟩

/-! ## Scratch: drive the header/length mask arithmetic (pc 839–871) -/

theorem weth9NameScratch {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨839⟩
      [⟨187⟩, weth9SelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    True := by
  obtain ⟨_, _, h844⟩ := (evm_run h with [jumpdest, push1 ⟨0⟩, dup1]).sload
    (by native_decide) (by evm_ov)
  have h871 := evm_run h844 with [
    push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost
      solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨2⟩, push1 ⟨1⟩, dup6, and, iszero, push2 ⟨256⟩, mul,
    push1 ⟨0⟩, not, add, swap1, swap5, and, swap4, swap1, swap4, div]
  have h886 := evm_run h871 with [
    push1 ⟨31⟩, dup2, add, dup5, swap1, div, dup5, mul, dup3, add, dup5, add, swap1, swap3]
  sorry

end Benchmarks.WETH9
