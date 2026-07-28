import Benchmarks.Dss.Cat.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Cat

/-!
# Cat `bite` — external `vat.grab(...)` CALL helper

`bite` performs `vat.grab(ilk, urn, address(this), vow, -int256(dink), -int256(dart))` — a
6-argument `(bytes32,address,address,address,int256,int256)` **void** CALL (perm := true, eth 0).

The solc build lays 196 (`0xc4`) calldata bytes at the free pointer `0x80`:

```
  0x80 : selector 0x7bab3f40  (top 4 bytes of the word)
  0x84 : ilk                  (bytes32)
  0xa4 : urn                  (address, masked)
  0xc4 : address(this)        (ADDRESS)
  0xe4 : vow                  (address, masked)
 0x104 : -int256(dink)        (two's-complement word 0 - dink)
 0x124 : -int256(dart)        (two's-complement word 0 - dart)
```

PCs (runtime): EXTCODESIZE guard @2177, `okPc` (JUMPDEST) @2189, CALL @2192, ISZERO
(call-success guard) @2193, success `okPc` (JUMPDEST) @2209, `POP` @2210, second `POP` @2211.

This file provides:

* the **RD call helpers** (`RD.catBiteGrab*`) that step the EXTCODESIZE guard and the CALL,
  stated GENERICALLY over the pre-call memory `mem`, the CALL operands
  (`inOff`/`inSize`/`outOff`) and the incoming stack tail `R`, so the trace agent can apply them;
* the **memory-encoding coupling** definitions and the `catGrabEncode_eq` coupling lemma
  matching the bytecode-built calldata slice to `config.externalABI.encode? "grab" args`.
-/

/-! ## RD helpers: EXTCODESIZE guard + CALL for `vat.grab(...)` (void)

All lemmas are stated over the concrete `catBytecode` at the `bite`-routine PCs but are otherwise
generic in the target word, the CALL operands, the pre-call memory and the incoming stack tail. -/

/-- EXTCODESIZE guard, missing-code branch: the `grab` target has no deployed code, so the guard
reverts. -/
theorem RD.catBiteGrabNoCode
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {target inOff inSize outOff : UInt256} {R : List UInt256}
    (rd2177 : RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2177⟩
      (target :: target :: ⟨0⟩ :: inOff :: inSize :: outOff :: ⟨0⟩ :: R)
      mem aw rdata (cA, σ) k C)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ target = ⟨0⟩)
    (hov : R.length + 9 ≤ 1024) :
    RDrev catBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨2177⟩) (okPc := ⟨2189⟩) rd2177
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
    (by simp only [List.length_cons]; omega)

/-- EXTCODESIZE guard, has-code branch + CALL: steps the guard, pushes `GAS`, executes the void
`CALL`, and lands just after the CALL (`pc 2193`, the ISZERO of the call-success guard) with the
status word on top of the incoming tail `R`. Produces the `Θ` witness whose input bytes are the
`mem`-slice `mem.readWithPadding inOff.toNat inSize.toNat` (coupled to `encode? "grab"` by
`catGrabEncode_eq`), and post-call memory equal to `mem` (void call: `outSize = 0`). -/
theorem RD.catBiteGrabCall
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {target inOff inSize outOff : UInt256} {R : List UInt256}
    (rd2177 : RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2177⟩
      (target :: target :: ⟨0⟩ :: inOff :: inSize :: outOff :: ⟨0⟩ :: R)
      mem aw rdata (cA, σ) k C)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ target ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hov : R.length + 9 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (Ain : Substate) (callGas : UInt256)
      (mem' : ByteArray) (aw' : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl σ σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 target) (toExecute σ (AccountAddress.ofUInt256 target))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          (mem.readWithPadding inOff.toNat inSize.toNat)
          (I.depth + 1) I.header I.perm)
      ∧ RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2193⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: R) mem' aw' o (cA', σ') k' C'
      ∧ o.size < UInt256.size := by
  obtain ⟨gasWord, k1, C1, rd2192⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨2177⟩) (okPc := ⟨2189⟩) rd2177
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide)
      (by simp only [List.length_cons]; omega)
  obtain ⟨cA', σ', z, o, Ain, callGas, k', C', hΘ, rd2193raw, hout⟩ :=
    RD.call rd2192 (by native_decide) hdepth
      (by omega)
  have hpc : ((⟨2189⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = (⟨2193⟩ : UInt256) := by
    native_decide
  rw [hpc] at rd2193raw
  exact ⟨cA', σ', z, o, Ain, callGas, _, _, k', C',
    (by simpa [initState] using hΘ), rd2193raw, hout⟩

/-- Depth-limit branch: `depth = 1024`, so the `CALL` fails immediately (status `0`) without
recursing; lands at `pc 2193` with status `⟨0⟩` and memory unchanged. -/
theorem RD.catBiteGrabCallDepthLimit
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {target inOff inSize outOff : UInt256} {R : List UInt256}
    (rd2177 : RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2177⟩
      (target :: target :: ⟨0⟩ :: inOff :: inSize :: outOff :: ⟨0⟩ :: R)
      mem aw rdata (cA, σ) k C)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ target ≠ ⟨0⟩)
    (hdepth : I.depth = 1024)
    (hov : R.length + 9 ≤ 1024) :
    ∃ mem' aw' k' C', RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2193⟩
      (⟨0⟩ :: R) mem' aw' ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨gasWord, k1, C1, rd2192⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨2177⟩) (okPc := ⟨2189⟩) rd2177
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide)
      (by simp only [List.length_cons]; omega)
  obtain ⟨k', C', rd2193raw⟩ :=
    RD.callDepthLimit rd2192 (by native_decide) hdepth
      (by omega)
  have hpc : ((⟨2189⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = (⟨2193⟩ : UInt256) := by
    native_decide
  rw [hpc] at rd2193raw
  exact ⟨_, _, k', C', rd2193raw⟩

/-- Call-success guard, failure branch: the `CALL` returned status `0`, so the guard bubbles the
callee revert data and reverts. -/
theorem RD.catBiteGrabCallFailed
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256}
    (rd2193 : RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2193⟩
      (⟨0⟩ :: R) mem aw rdata acc k C)
    (hrdataSize : rdata.size < UInt256.size)
    (hov : R.length + 5 ≤ 1024) :
    RDrev catBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨2193⟩) (okPc := ⟨2209⟩) rd2193
    rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hrdataSize
    hov

/-- Call-success guard, success branch: the `CALL` returned nonzero status; the guard `POP`s the
status and the void return value, leaving the incoming tail `R` at `pc 2212` (the routine
continues to the `fess` call). -/
theorem RD.catBiteGrabCallSucceeded
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {status : UInt256} {x : UInt256} {R : List UInt256}
    (rd2193 : RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2193⟩
      (status :: x :: R) mem aw rdata acc k C)
    (hstatus : status ≠ ⟨0⟩)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2212⟩
      R mem aw rdata acc k' C' := by
  obtain ⟨k1, C1, rd2211⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨2193⟩) (okPc := ⟨2209⟩) rd2193
      hstatus
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
      (by simp only [List.length_cons]; omega)
  have rd2212 := RD.pop rd2211 (by native_decide) (by omega)
  exact ⟨_, _, by simpa using rd2212⟩

/-! ## Memory-encoding coupling for `vat.grab(...)`

The solc build writes 7 words into the running memory `mem` at the free pointer `0x80` (all offsets
in-bounds when `324 ≤ mem.size`): the selector word at `128`, then the six argument words at
`132, 164, 196, 228, 260, 292`.  We model this as seven nested `write32`s and prove the free-pointer
read (`[64,96)`) is preserved and the calldata slice `[128,324)` equals
`vatGrabSelector ++ ilkW ++ urnW ++ thisW ++ vowW ++ dinkW ++ dartW`. -/

/-- Grab selector `0x7bab3f40` shifted into the top 4 bytes of a word, exactly as the bytecode
builds it: `PUSH4 0x01eeacfd; PUSH1 0xe6; SHL`. -/
abbrev catGrabSelectorShifted : UInt256 :=
  UInt256.shiftLeft ⟨32419069⟩ ⟨230⟩

noncomputable def catGrabSelMem (mem : ByteArray) : ByteArray :=
  catGrabSelectorShifted.toByteArray.write 0 mem 128 32

noncomputable def catGrabIlkMem (ilkW : UInt256) (mem : ByteArray) : ByteArray :=
  ilkW.toByteArray.write 0 (catGrabSelMem mem) 132 32

noncomputable def catGrabUrnMem (ilkW urnW : UInt256) (mem : ByteArray) : ByteArray :=
  urnW.toByteArray.write 0 (catGrabIlkMem ilkW mem) 164 32

noncomputable def catGrabThisMem (ilkW urnW thisW : UInt256) (mem : ByteArray) : ByteArray :=
  thisW.toByteArray.write 0 (catGrabUrnMem ilkW urnW mem) 196 32

noncomputable def catGrabVowMem (ilkW urnW thisW vowW : UInt256) (mem : ByteArray) : ByteArray :=
  vowW.toByteArray.write 0 (catGrabThisMem ilkW urnW thisW mem) 228 32

noncomputable def catGrabDinkMem (ilkW urnW thisW vowW dinkW : UInt256)
    (mem : ByteArray) : ByteArray :=
  dinkW.toByteArray.write 0 (catGrabVowMem ilkW urnW thisW vowW mem) 260 32

/-- The full 196-byte `grab` calldata laid at `0x80` over base memory `mem`. -/
noncomputable def catGrabCalldataMem (ilkW urnW thisW vowW dinkW dartW : UInt256)
    (mem : ByteArray) : ByteArray :=
  dartW.toByteArray.write 0 (catGrabDinkMem ilkW urnW thisW vowW dinkW mem) 292 32

/-! ### Size invariants (each nested write is in-bounds when `324 ≤ mem.size`). -/

theorem catGrabSelMem_size {mem : ByteArray} (hmem : 324 ≤ mem.size) :
    (catGrabSelMem mem).size = mem.size := by
  unfold catGrabSelMem
  exact toByteArray_write32_size_of_le mem catGrabSelectorShifted 128 mem.size mem.size rfl
    (by omega) (by omega)

theorem catGrabIlkMem_size (ilkW : UInt256) {mem : ByteArray} (hmem : 324 ≤ mem.size) :
    (catGrabIlkMem ilkW mem).size = mem.size := by
  unfold catGrabIlkMem
  exact toByteArray_write32_size_of_le (catGrabSelMem mem) ilkW 132 mem.size mem.size
    (catGrabSelMem_size hmem) (by rw [catGrabSelMem_size hmem]; omega) (by omega)

theorem catGrabUrnMem_size (ilkW urnW : UInt256) {mem : ByteArray} (hmem : 324 ≤ mem.size) :
    (catGrabUrnMem ilkW urnW mem).size = mem.size := by
  unfold catGrabUrnMem
  exact toByteArray_write32_size_of_le (catGrabIlkMem ilkW mem) urnW 164 mem.size mem.size
    (catGrabIlkMem_size ilkW hmem) (by rw [catGrabIlkMem_size ilkW hmem]; omega) (by omega)

theorem catGrabThisMem_size (ilkW urnW thisW : UInt256) {mem : ByteArray}
    (hmem : 324 ≤ mem.size) : (catGrabThisMem ilkW urnW thisW mem).size = mem.size := by
  unfold catGrabThisMem
  exact toByteArray_write32_size_of_le (catGrabUrnMem ilkW urnW mem) thisW 196 mem.size mem.size
    (catGrabUrnMem_size ilkW urnW hmem) (by rw [catGrabUrnMem_size ilkW urnW hmem]; omega)
    (by omega)

theorem catGrabVowMem_size (ilkW urnW thisW vowW : UInt256) {mem : ByteArray}
    (hmem : 324 ≤ mem.size) : (catGrabVowMem ilkW urnW thisW vowW mem).size = mem.size := by
  unfold catGrabVowMem
  exact toByteArray_write32_size_of_le (catGrabThisMem ilkW urnW thisW mem) vowW 228 mem.size
    mem.size (catGrabThisMem_size ilkW urnW thisW hmem)
    (by rw [catGrabThisMem_size ilkW urnW thisW hmem]; omega) (by omega)

theorem catGrabDinkMem_size (ilkW urnW thisW vowW dinkW : UInt256) {mem : ByteArray}
    (hmem : 324 ≤ mem.size) :
    (catGrabDinkMem ilkW urnW thisW vowW dinkW mem).size = mem.size := by
  unfold catGrabDinkMem
  exact toByteArray_write32_size_of_le (catGrabVowMem ilkW urnW thisW vowW mem) dinkW 260 mem.size
    mem.size (catGrabVowMem_size ilkW urnW thisW vowW hmem)
    (by rw [catGrabVowMem_size ilkW urnW thisW vowW hmem]; omega) (by omega)

theorem catGrabCalldataMem_size (ilkW urnW thisW vowW dinkW dartW : UInt256) {mem : ByteArray}
    (hmem : 324 ≤ mem.size) :
    (catGrabCalldataMem ilkW urnW thisW vowW dinkW dartW mem).size = mem.size := by
  unfold catGrabCalldataMem
  exact toByteArray_write32_size_of_le (catGrabDinkMem ilkW urnW thisW vowW dinkW mem) dartW 292
    mem.size mem.size (catGrabDinkMem_size ilkW urnW thisW vowW dinkW hmem)
    (by rw [catGrabDinkMem_size ilkW urnW thisW vowW dinkW hmem]; omega) (by omega)

/-! ### Free-pointer preservation: the read at `[64,96)` is untouched by the 7 writes. -/

theorem catGrabCalldataMem_read64 (ilkW urnW thisW vowW dinkW dartW : UInt256) {mem : ByteArray}
    (hmem : 324 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (catGrabCalldataMem ilkW urnW thisW vowW dinkW dartW mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold catGrabCalldataMem
  rw [write32_read_below_len _ _ 292 64 32 (by rw [toByteArray_size])
      (by rw [catGrabDinkMem_size ilkW urnW thisW vowW dinkW hmem]; omega) (by omega)
      (by rw [catGrabDinkMem_size ilkW urnW thisW vowW dinkW hmem]; omega) (by norm_num)
      (by norm_num)]
  unfold catGrabDinkMem
  rw [write32_read_below_len _ _ 260 64 32 (by rw [toByteArray_size])
      (by rw [catGrabVowMem_size ilkW urnW thisW vowW hmem]; omega) (by omega)
      (by rw [catGrabVowMem_size ilkW urnW thisW vowW hmem]; omega) (by norm_num) (by norm_num)]
  unfold catGrabVowMem
  rw [write32_read_below_len _ _ 228 64 32 (by rw [toByteArray_size])
      (by rw [catGrabThisMem_size ilkW urnW thisW hmem]; omega) (by omega)
      (by rw [catGrabThisMem_size ilkW urnW thisW hmem]; omega) (by norm_num) (by norm_num)]
  unfold catGrabThisMem
  rw [write32_read_below_len _ _ 196 64 32 (by rw [toByteArray_size])
      (by rw [catGrabUrnMem_size ilkW urnW hmem]; omega) (by omega)
      (by rw [catGrabUrnMem_size ilkW urnW hmem]; omega) (by norm_num) (by norm_num)]
  unfold catGrabUrnMem
  rw [write32_read_below_len _ _ 164 64 32 (by rw [toByteArray_size])
      (by rw [catGrabIlkMem_size ilkW hmem]; omega) (by omega)
      (by rw [catGrabIlkMem_size ilkW hmem]; omega) (by norm_num) (by norm_num)]
  unfold catGrabIlkMem
  rw [write32_read_below_len _ _ 132 64 32 (by rw [toByteArray_size])
      (by rw [catGrabSelMem_size hmem]; omega) (by omega)
      (by rw [catGrabSelMem_size hmem]; omega) (by norm_num) (by norm_num)]
  unfold catGrabSelMem
  rw [write32_read_below_len _ _ 128 64 32 (by rw [toByteArray_size])
      (by omega) (by omega) (by omega) (by norm_num) (by norm_num)]
  exact hread64

end Benchmarks.Dss.Cat
