import Benchmarks.OpenZeppelinBench.TimelockController.Return
import Benchmarks.OpenZeppelinBench.TimelockController.SolmDispatch
import Benchmarks.OpenZeppelinBench.TimelockController.Dispatch
import Benchmarks.OpenZeppelinBench.TimelockController.Routines

/-!
# OpenZeppelin TimelockController — shared ERC-receiver routines

The three ERC receivers (`onERC721Received`, `onERC1155Received`, `onERC1155BatchReceived`) each decode
their dynamic-typed calldata, ignore the decoded arguments, and `RETURN` a constant left-aligned
`bytes4` selector.  The runtime shares one `bytes4` return encoder at pc 687 → pc 521:

```
687  MLOAD(0x40)                      -- P := free pointer (bumped past the decoded buffer)
     PUSH1 1; PUSH1 1; PUSH1 0xe0; SHL; SUB; NOT   -- top-4-byte mask ~((1<<224)-1)
     AND; MSTORE(P)                   -- store (selVal & mask) at P
     PUSH1 0x20; ADD; PUSH2 521; JUMP
521  MLOAD(0x40); DUP1; SWAP2; SUB; SWAP1; RETURN   -- RETURN(P, 0x20) = mem[P .. P+0x20]
```

Because the decoder bumps the free pointer to `P = 0x80 + 0x20 + paddedLen` and leaves the active-word
count at exactly `(P + 0x20)/0x20`, the encoder's `MSTORE(P)` and `RETURN(P, 0x20)` touch only
already-active memory, so both have zero memory-expansion cost.  `tlcRecvReturnBytes4` captures this
over an abstract `(mem, P, aw)`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace OpenZeppelinBench.TimelockController

/-! ## Left-aligned `bytes4` selector words (as `RETURN`ed by the shared encoder) -/

/-- `0x150b7a02 << 224` — the `onERC721Received` selector, left-aligned in a word. -/
def tlcRecvErc721Word : UInt256 :=
  ⟨0x150b7a0200000000000000000000000000000000000000000000000000000000⟩

/-- `0xf23a6e61 << 224` — the `onERC1155Received` selector, left-aligned in a word. -/
def tlcRecvErc1155Word : UInt256 :=
  ⟨0xf23a6e6100000000000000000000000000000000000000000000000000000000⟩

/-- `0xbc197c81 << 224` — the `onERC1155BatchReceived` selector, left-aligned in a word. -/
def tlcRecvErc1155BatchWord : UInt256 :=
  ⟨0xbc197c8100000000000000000000000000000000000000000000000000000000⟩

/-- The top-4-byte keep mask the runtime materialises at pc 691..699 (`~((1<<224)-1)`). -/
def tlcRecvBytes4Mask : UInt256 :=
  UInt256.lnot (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩) ⟨1⟩)

/-! ## `bytes4` ABI return encoding

The Solm body returns `.fixedBytes bytes4Width <4 bytes>`; solc encodes that as the 4 bytes followed
by 28 zero bytes, i.e. exactly the 32 big-endian bytes of the left-aligned word. -/

theorem tlcRecvErc721ReturnEncoding :
    encodeReturnValue? bytes4 (.fixedBytes bytes4Width [0x15, 0x0b, 0x7a, 0x02]) =
      some (UInt256.toByteArray tlcRecvErc721Word) := by
  refine scalarReturnEncoding (t := .bytes bytes4Width) (w := tlcRecvErc721Word) (by decide) ?_ ?_
  · native_decide
  · native_decide

theorem tlcRecvErc1155ReturnEncoding :
    encodeReturnValue? bytes4 (.fixedBytes bytes4Width [0xf2, 0x3a, 0x6e, 0x61]) =
      some (UInt256.toByteArray tlcRecvErc1155Word) := by
  refine scalarReturnEncoding (t := .bytes bytes4Width) (w := tlcRecvErc1155Word) (by decide) ?_ ?_
  · native_decide
  · native_decide

theorem tlcRecvErc1155BatchReturnEncoding :
    encodeReturnValue? bytes4 (.fixedBytes bytes4Width [0xbc, 0x19, 0x7c, 0x81]) =
      some (UInt256.toByteArray tlcRecvErc1155BatchWord) := by
  refine scalarReturnEncoding (t := .bytes bytes4Width) (w := tlcRecvErc1155BatchWord) (by decide) ?_ ?_
  · native_decide
  · native_decide

/-! ## Zero memory-expansion cost for an already-active 32-byte window -/

/-- `MachineState.M` fixed point: a 32-byte window ending at or before `aw*32` does not grow memory. -/
theorem tlcRecvM_fixed {aw off : ℕ} (hle : off + 32 ≤ aw * 32) :
    MachineState.M aw off 32 = aw := by
  show max aw ((off + 32 + 31) / 32) = aw
  rw [Nat.max_eq_left]
  omega

/-- `MSTORE` of a word into an already-active window costs nothing. -/
theorem tlcRecvMstoreCost0 {s : State} {aw off val : UInt256} {t : List UInt256}
    (haw : s.machineState.activeWords = aw) (hstk : s.machineState.stack = off :: val :: t)
    (hle : off.toNat + 32 ≤ aw.toNat * 32) :
    memoryExpansionCost s .MSTORE = 0 := by
  refine mstoreCost_of_stack haw hstk ?_
  rw [tlcRecvM_fixed hle, u256_ofNat_toNat]
  omega

/-- `MLOAD` of an already-active window costs nothing. -/
theorem tlcRecvMloadCost0 {s : State} {aw off : UInt256} {t : List UInt256}
    (haw : s.machineState.activeWords = aw) (hstk : s.machineState.stack = off :: t)
    (hle : off.toNat + 32 ≤ aw.toNat * 32) :
    memoryExpansionCost s .MLOAD = 0 := by
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ']
  have htop : s.machineState.stack[0]! = off := by rw [hstk]; rfl
  rw [htop, haw, tlcRecvM_fixed hle, u256_ofNat_toNat]
  omega

/-- `RETURN`ing an already-active 32-byte window costs nothing. -/
theorem tlcRecvReturnCost0 {s : State} {aw off : UInt256} {t : List UInt256}
    (haw : s.machineState.activeWords = aw)
    (hstk : s.machineState.stack = off :: (⟨32⟩ : UInt256) :: t)
    (hle : off.toNat + 32 ≤ aw.toNat * 32) :
    memoryExpansionCost s .RETURN = 0 := by
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ']
  have htop : s.machineState.stack[0]! = off := by rw [hstk]; rfl
  have hnext : s.machineState.stack[1]! = (⟨32⟩ : UInt256) := by rw [hstk]; rfl
  rw [htop, hnext, haw, show ((⟨32⟩ : UInt256).toNat) = 32 from by decide,
    tlcRecvM_fixed hle, u256_ofNat_toNat]
  omega

/-- The active-word slot `aw*32` exceeds an in-range offset, so `MLOAD off` reads real memory. -/
theorem tlcRecvNotGe {off aw : UInt256} (hawsz : aw.toNat * 32 < UInt256.size)
    (hlt : off.toNat < aw.toNat * 32) : ¬ off ≥ aw * ⟨32⟩ := by
  have hmul : (aw * ⟨32⟩).toNat = aw.toNat * 32 := by
    rw [umul_toNat aw ⟨32⟩ (by rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]; exact hawsz),
      show (⟨32⟩ : UInt256).toNat = 32 from by decide]
  intro hge
  have h2 : (aw * ⟨32⟩).toNat ≤ off.toNat := hge
  rw [hmul] at h2
  omega

/-- `MachineState.M` fixed point, lifted to the word `activeWords`. -/
theorem tlcRecvAwFixed {aw : UInt256} {off : ℕ} (hle : off + 32 ≤ aw.toNat * 32) :
    UInt256.ofNat (MachineState.M aw.toNat off 32) = aw := by
  rw [tlcRecvM_fixed hle, u256_ofNat_toNat]

/-! ## Shared `bytes4` return encoder (pc 687 → pc 521)

    Runs over the memory the decoder left: free pointer `P` at `0x40`, buffer occupying `[0x80, P)`,
    and active words at exactly `(P + 0x20)/0x20`.  Stores the masked selector at `P` and
    `RETURN(P, 0x20)`s it.  All three memory touches (`MLOAD 0x40`, `MSTORE P`, `MLOAD 0x40`,
    `RETURN P`) land in already-active memory, so they cost nothing. -/
theorem tlcRecvReturnBytes4 {cA gh bl σ σ₀ A I} {g : Sat256}
    {selVal P cont : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨687⟩
      (selVal :: cont :: R) mem aw ByteArray.empty (cA, σ) k C)
    (hfree : mem.readWithPadding 64 32 = UInt256.toByteArray P)
    (hmemsz : P.toNat ≤ mem.size)
    (hPlo : 96 ≤ P.toNat)
    (hawP : aw.toNat * 32 = P.toNat + 32)
    (hPhi : P.toNat + 32 < UInt256.size)
    (hov : R.length + 6 ≤ 1024) :
    RDret timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.land selVal tlcRecvBytes4Mask)) := by
  have hawsz : aw.toNat * 32 < UInt256.size := by rw [hawP]; exact hPhi
  have h64lt : (64 : ℕ) < aw.toNat * 32 := by omega
  -- masked value stored at P
  set val := UInt256.land selVal tlcRecvBytes4Mask with hval
  set memout := (UInt256.toByteArray val).write 0 mem P.toNat 32 with hmemout
  -- pc 687 .. 711: MLOAD 0x40, build mask, AND, MSTORE at P, jump to 521
  have h521 := h.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨64⟩ (by native_decide) (by evm_ov)
    |>.mload 0 P aw (by native_decide)
        (fun s hs1 hs2 => tlcRecvMloadCost0 hs1 hs2
          (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; omega))
        (mloadWordValue_of_readWithPadding
          (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; omega)
          (tlcRecvNotGe hawsz (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; omega))
          (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; exact hfree))
        (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; exact tlcRecvAwFixed (by omega))
        (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨224⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.not (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.mstore 0 memout aw (by native_decide)
        (fun s hs1 hs2 => tlcRecvMstoreCost0 hs1 hs2 (by omega))
        hmemout.symm
        (by rw [tlcRecvAwFixed (by omega)])
        (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
    |>.add (by native_decide) (by evm_ov)
    |>.push2 ⟨521⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)
  -- pc 521 .. 529: MLOAD 0x40 (still P), compute length 0x20, RETURN(P, 0x20)
  have hmemoutsz : P.toNat + 32 ≤ memout.size :=
    toByteArray_write_size_ge_off_add32 val mem P.toNat (lt_usize _ (by omega))
  have hread64 : memout.readWithPadding 64 32 = UInt256.toByteArray P := by
    rw [hmemout, write32_read_below (UInt256.toByteArray val) mem P.toNat 64
      (by rw [toByteArray_size]) hmemsz (by omega)]
    exact hfree
  have hreadP : memout.readWithPadding P.toNat 32 = UInt256.toByteArray val := by
    rw [hmemout]; exact toByteArray_write32_read_back mem val P.toNat hmemsz
  have hret := h521.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨64⟩ (by native_decide) (by evm_ov)
    |>.mload 0 P aw (by native_decide)
        (fun s hs1 hs2 => tlcRecvMloadCost0 hs1 hs2
          (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; omega))
        (mloadWordValue_of_readWithPadding
          (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; omega)
          (tlcRecvNotGe hawsz (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; omega))
          (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; exact hread64))
        (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; exact tlcRecvAwFixed (by omega))
        (by evm_ov)
    |>.dup1 (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
  have hlen32 : UInt256.sub (⟨32⟩ + P) P = ⟨32⟩ := by
    apply u256_inj
    have hadd : (⟨32⟩ + P).toNat = 32 + P.toNat := by
      rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide, Nat.mod_eq_of_lt (by omega)]
    show (UInt256.sub (⟨32⟩ + P) P).toNat = (⟨32⟩ : UInt256).toNat
    rw [usub_toNat (by rw [hadd]; omega), hadd, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
    omega
  rw [hlen32] at hret
  exact hret.ret 0 (UInt256.toByteArray val) (by native_decide)
    (fun s hs1 hs2 => tlcRecvReturnCost0 hs1 hs2 (by omega))
    (by rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]; exact hreadP)
    (by evm_ov)

end OpenZeppelinBench.TimelockController
