import Benchmarks.Dss.Cat.BiteConnect

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.Dss.Cat

/-! # Cat `bite(bytes32,address)` — reach-to-guard cursor lemmas

The `bite` success trace is proved as a chain of frozen "happy-path" segment lemmas
(`catBiteReach*` in `BiteConnect`, `catBiteTraceSeg*` in `BiteTrace`) that only expose their END
states.  But `bite` has ~17 business-logic revert guards (six `checkedMul` overflows @ pc `3720`, a
`checkedSub` underflow @ pc `3762`, a `milkChop != 0` div-by-zero `INVALID` @ pc `1865`, and the
`require` string reverts) MID-segment.  Each revert leaf in `BiteRevertLeaves` takes a "reach cursor
at the guard pc" as a hypothesis.

This file produces those cursors: for each guard, a composable `catBiteReachGuard*` lemma that,
from the enclosing segment's ENTRY reach point (the same cursor the `catBiteTraceSeg*`/`catBiteReach*`
wrapper consumes) plus the "prior guards passed" hypotheses, reaches the guard pc with exactly the
stack/memory the leaf's cursor hypothesis expects.  Each is modeled on the internal segment cursor
(e.g. `rd3720a` in `catBiteTraceSeg5`) but exposed standalone so the top-level integrator can, at each
guard, `by_cases` the condition: holds → continue the happy path; fails → feed this cursor to the
revert leaf.

Memory/active-words (`mem`/`aw`) are kept abstract exactly as the segments do (the `checkedMul`/
`checkedSub`/require guards thread them through unchanged), so the cursors compose along whatever
concrete-memory spine the integrator walks. -/

/-! ## Parametric `@3720` `checkedMul`-entry tail

The shared entry to the DSMath checked-multiply routine `@3720`: from a cursor at the `PUSH2 3720`
instruction with the checked-mul operand frame `a :: b :: ret :: R` on top, step `PUSH2 3720; JUMP`
to land at pc `3720` with the frame intact — exactly the `RD.catBiteCheckedMul{,Revert}` entry shape.
Parametric in the operands `a, b, ret` and the reach point `pc` (the `PUSH2 3720` pc); the six
per-site wrappers below discharge the two decode facts by `native_decide` at their concrete `pc`. -/
theorem RD.catBiteReachMul3720Tail {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a b ret pc : UInt256} {R : List UInt256} {k C : ℕ}
    (rd : RD catBytecode I g (initState cA gh bl σ σ₀ g A I) pc
      (a :: b :: ret :: R) mem aw rdata acc k C)
    (hpush : decode catBytecode pc = some (.Push .PUSH2, some (⟨3720⟩, 2)))
    (hjump : decode catBytecode (pc + UInt256.ofNat 3) = some (.JUMP, .none))
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3720⟩
      (a :: b :: ret :: R) mem aw rdata acc k' C' := by
  have rd1 := rd.push2 ⟨3720⟩ hpush (by simp only [List.length_cons]; omega)
  exact ⟨_, _, rd1.jump hjump (by jump_dest) (by simp only [List.length_cons]; omega)⟩

/-! ## Seg 5 (`1521`) `checkedMul` guards: `artRate = art*rate`, `inkSpot = ink*spot` @ pc `3720`

`Seg5` computes `require(spot > 0 && ink*spot < art*rate)` via two shared `@3720` `checkedMul`s.  The
FIRST (`artRate`, `rd3720a`) is reached once `spot > 0` cleared the short-circuit; the SECOND
(`inkSpot`, `rd3720b`) once `artRate` also multiplied without overflow. -/

/-- **`artRate` mul-overflow guard** (`Seg5`, `@3720`): from the `1521` entry, past the `spot > 0`
short-circuit, reach the `art*rate` `checkedMul` frame `iRate :: art :: 1542 :: …`.  Feeds
`catBiteArtRateOverflowLeaf` / `catBiteMulOverflowRevertLeaf` (`a = iRate`, `b = art`). -/
theorem catBiteReachGuardArtRate {cA gh bl σ σ₀ A I} {g : UInt256}
    {art ink iDust iSpot iRate urn ilk : UInt256} {R : List UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1521⟩
      (art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R) mem aw o acc k C)
    (hspotPos : 0 < iSpot.toNat)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3720⟩
      (iRate :: art :: ⟨1542⟩ :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o acc k' C' := by
  have rd1522 := rd.jumpdest (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1524 := rd1522.push1 ⟨0⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1525 := rd1524.dup5 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1526 := rd1525.gt (by native_decide) (by simp only [List.length_cons]; omega)
  rw [ugt_one (show (⟨0⟩ : UInt256).toNat < iSpot.toNat by simpa using hspotPos)] at rd1526
  have rd1527 := rd1526.dup1 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1528 := rd1527.iszero (by native_decide) (by simp only [List.length_cons]; omega)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by native_decide] at rd1528
  have rd1531 := rd1528.push2 ⟨1554⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1532 := rd1531.jumpiNT (by native_decide) rfl (by simp only [List.length_cons]; omega)
  have rd1533 := rd1532.pop (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1536 := rd1533.push2 ⟨1542⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1537 := rd1536.dup2 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1538 := rd1537.dup7 (by native_decide) (by simp only [List.length_cons]; omega)
  exact RD.catBiteReachMul3720Tail rd1538 (by native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)

/-- **`inkSpot` mul-overflow guard** (`Seg5`, `@3720`): from the `1521` entry, past `spot > 0` and
the (non-overflowing) `artRate` mul, reach the `ink*spot` `checkedMul` frame `iSpot :: ink :: 1552 ::
…`.  Feeds `catBiteMulOverflowRevertLeaf` (`a = iSpot`, `b = ink`). -/
theorem catBiteReachGuardInkSpot {cA gh bl σ σ₀ A I} {g : UInt256}
    {art ink iDust iSpot iRate urn ilk : UInt256} {R : List UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1521⟩
      (art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R) mem aw o acc k C)
    (hspotPos : 0 < iSpot.toNat)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3720⟩
      (iSpot :: ink :: ⟨1552⟩ :: UInt256.mul art iRate :: art :: ink :: iDust :: iSpot :: iRate ::
        ⟨0⟩ :: urn :: ilk :: R)
      mem aw o acc k' C' := by
  have rd1522 := rd.jumpdest (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1524 := rd1522.push1 ⟨0⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1525 := rd1524.dup5 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1526 := rd1525.gt (by native_decide) (by simp only [List.length_cons]; omega)
  rw [ugt_one (show (⟨0⟩ : UInt256).toNat < iSpot.toNat by simpa using hspotPos)] at rd1526
  have rd1527 := rd1526.dup1 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1528 := rd1527.iszero (by native_decide) (by simp only [List.length_cons]; omega)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by native_decide] at rd1528
  have rd1531 := rd1528.push2 ⟨1554⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1532 := rd1531.jumpiNT (by native_decide) rfl (by simp only [List.length_cons]; omega)
  have rd1533 := rd1532.pop (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1536 := rd1533.push2 ⟨1542⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1537 := rd1536.dup2 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1538 := rd1537.dup7 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1541 := rd1538.push2 ⟨3720⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd3720a := rd1541.jump (by native_decide) (by jump_dest) (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd1542⟩ := RD.catBiteCheckedMul rd3720a
    (by rw [Nat.mul_comm]; exact hfitArtRate) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1543 := rd1542.jumpdest (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1546 := rd1543.push2 ⟨1552⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1547 := rd1546.dup4 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1548 := rd1547.dup7 (by native_decide) (by simp only [List.length_cons]; omega)
  exact RD.catBiteReachMul3720Tail rd1548 (by native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)

/-! ## Seg 7b (`1810`) `checkedMul` guard: `dunkRoomWad = dunkRoom*WAD` @ pc `3720`

`Seg7b` computes `dunkRoom = min(milkDunk, room)` (`@3778`) then `dunkRoomWad = dunkRoom*WAD` via the
shared `@3720` `checkedMul`.  The reach threads the two struct reads (`milkChop@q+32`, `milkDunk@q+64`)
and pins the `min` output with `hDunkRoom`. -/

/-- **`dunkRoomWad` mul-overflow guard** (`Seg7b`, `@3720`): reach the `dunkRoom*WAD` `checkedMul`
frame `WAD :: dunkRoom :: 1851 :: …`.  Feeds `catBiteMulOverflowRevertLeaf` (`a = WAD`,
`b = dunkRoom`). -/
theorem catBiteReachGuardDunkRoomWad {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {room q art ink iDust iSpot iRate urn ilk milkChop milkDunk dunkRoom : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1810⟩
      (room :: ⟨0⟩ :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o acc k C)
    (hChop : (if (⟨32⟩ + q).toNat ≥ mem.size ∨ (⟨32⟩ + q) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨32⟩ + q).toNat 32)))
        = milkChop)
    (hDunk : (if (⟨64⟩ + q).toNat ≥ mem.size ∨ (⟨64⟩ + q) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ + q).toNat 32)))
        = milkDunk)
    (haw : q.toNat + 96 ≤ aw.toNat * 32) (hqsz : q.toNat + 96 < UInt256.size)
    (hDunkRoom : (if UInt256.gt milkDunk room = ⟨0⟩ then milkDunk else room) = dunkRoom)
    (hov : R.length + 24 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3720⟩
      (⟨1000000000000000000⟩ :: dunkRoom :: ⟨1851⟩ :: iRate :: milkChop :: art :: ⟨1872⟩ :: room ::
        ⟨0⟩ :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o acc k' C' := by
  have e32q : (⟨32⟩ + q).toNat = q.toNat + 32 := uadd_lit32_toNat q (by omega)
  have e64q : (⟨64⟩ + q).toNat = q.toNat + 64 := by
    rw [uadd_toNat, show (⟨64⟩ : UInt256).toNat = 64 from by decide, Nat.add_comm,
      Nat.mod_eq_of_lt (by omega)]
  have hChopAw : UInt256.ofNat (MachineState.M aw.toNat (⟨32⟩ + q).toNat 32) = aw :=
    catBiteAwMInv32 aw (by rw [e32q]; omega)
  have hDunkAw : UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ + q).toNat 32) = aw :=
    catBiteAwMInv32 aw (by rw [e64q]; omega)
  have rd1811 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd1814 := rd1811.push2 ⟨1872⟩ (by native_decide) (by evm_ov)
  have rd1815 := rd1814.dup5 (by native_decide) (by evm_ov)
  have rd1816 := rd1815.dup5 (by native_decide) (by evm_ov)
  have rd1818 := rd1816.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd1819 := rd1818.add (by native_decide) (by evm_ov)
  have rd1820 := RD.mload 0 milkChop aw rd1819 (by native_decide) (catBiteMloadCost0 hChopAw)
    hChop hChopAw (by evm_ov)
  have rd1821 := rd1820.dup11 (by native_decide) (by evm_ov)
  have rd1824 := rd1821.push2 ⟨1851⟩ (by native_decide) (by evm_ov)
  have rd1827 := rd1824.push2 ⟨1837⟩ (by native_decide) (by evm_ov)
  have rd1828 := rd1827.dup9 (by native_decide) (by evm_ov)
  have rd1830 := rd1828.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd1831 := rd1830.add (by native_decide) (by evm_ov)
  have rd1832 := RD.mload 0 milkDunk aw rd1831 (by native_decide) (catBiteMloadCost0 hDunkAw)
    hDunk hDunkAw (by evm_ov)
  have rd1833 := rd1832.dup8 (by native_decide) (by evm_ov)
  have rd1836 := rd1833.push2 ⟨3778⟩ (by native_decide) (by evm_ov)
  have rd3778a := rd1836.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd1837⟩ := RD.catBiteMin rd3778a (by native_decide) (by evm_ov)
  rw [hDunkRoom] at rd1837
  have rd1837j := rd1837.jumpdest (by native_decide) (by evm_ov)
  have rd1838 := RD.push8 rd1837j ⟨1000000000000000000⟩ (by native_decide) (by evm_ov)
  exact RD.catBiteReachMul3720Tail rd1838 (by native_decide) (by native_decide) (by evm_ov)

/-! ## Seg 7c (`1872`) `checkedMul` guard: `inkDart = ink*dart` @ pc `3720`

`Seg7c` computes `inkDart = ink*dart` via the shared `@3720` `checkedMul` (before the inline
`/art` div + `min` + `require(dart>0 && dink>0)`).  Reached with no extra hypotheses (the prefix is
pure stack shuffling). -/

/-- **`inkDart` mul-overflow guard** (`Seg7c`, `@3720`): reach the `ink*dart` `checkedMul` frame
`dart :: ink :: 1892 :: …`.  Feeds `catBiteMulOverflowRevertLeaf` (`a = dart`, `b = ink`). -/
theorem catBiteReachGuardInkDart {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {room q art ink iDust iSpot iRate urn ilk dart : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1872⟩
      (dart :: room :: ⟨0⟩ :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o acc k C)
    (hov : R.length + 24 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3720⟩
      (dart :: ink :: ⟨1892⟩ :: art :: ink :: ⟨1899⟩ :: ⟨0⟩ :: dart :: q :: art :: ink :: iDust ::
        iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o acc k' C' := by
  have rd1873 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd1874 := rd1873.swap2 (by native_decide) (by evm_ov)
  have rd1875 := rd1874.pop (by native_decide) (by evm_ov)
  have rd1876 := rd1875.pop (by native_decide) (by evm_ov)
  have rd1878 := rd1876.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd1881 := rd1878.push2 ⟨1899⟩ (by native_decide) (by evm_ov)
  have rd1882 := rd1881.dup6 (by native_decide) (by evm_ov)
  have rd1883 := rd1882.dup6 (by native_decide) (by evm_ov)
  have rd1886 := rd1883.push2 ⟨1892⟩ (by native_decide) (by evm_ov)
  have rd1887 := rd1886.dup9 (by native_decide) (by evm_ov)
  have rd1888 := rd1887.dup7 (by native_decide) (by evm_ov)
  exact RD.catBiteReachMul3720Tail rd1888 (by native_decide) (by native_decide) (by evm_ov)

/-! ## Seg 7f (`2193`) `checkedMul` guard: `dartRate = dart*rate` @ pc `3720`

`Seg7f` first clears the `grab` call-success guard (`hstatus`), then computes `dartRate = dart*rate`
via the shared `@3720` `checkedMul` (while assembling the `fess` frame). -/

/-- **`dartRate` mul-overflow guard** (`Seg7f`, `@3720`): from the `2193` (post-`grab`) entry, past
the call-success guard, reach the `dart*rate` `checkedMul` frame `iRate :: dart :: 2242 :: …`.  Feeds
`catBiteMulOverflowRevertLeaf` (`a = iRate`, `b = dart`). -/
theorem catBiteReachGuardDartRate {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {status d0 d1 d2 dink dart q art ink iDust iSpot iRate urn ilk : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2193⟩
      (status :: d0 :: d1 :: d2 :: dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate ::
        ⟨0⟩ :: urn :: ilk :: R) mem aw o (cA', σ') k C)
    (hstatus : status ≠ ⟨0⟩)
    (hov : R.length + 22 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3720⟩
      (iRate :: dart :: ⟨2242⟩ :: ⟨1769929592⟩ ::
        UInt256.land biteAddrMaskWord (solcSlotWord σ' I ⟨4⟩) ::
        dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o (cA', σ') k' C' := by
  have rd2194 := rd.iszero (by native_decide) (by evm_ov)
  rw [isZero_eq_zero_of_ne hstatus] at rd2194
  have rd2195 := rd2194.dup1 (by native_decide) (by evm_ov)
  have rd2196 := rd2195.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd2196
  have rd2199 := rd2196.push2 ⟨2209⟩ (by native_decide) (by evm_ov)
  have rd2209 := rd2199.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)
  have rd2210 := rd2209.jumpdest (by native_decide) (by evm_ov)
  have rd2211 := rd2210.pop (by native_decide) (by evm_ov)
  have rd2212 := rd2211.pop (by native_decide) (by evm_ov)
  have rd2214 := rd2212.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2215raw⟩ := rd2214.sload (by native_decide) (by evm_ov)
  have rd2215 : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2215⟩
      (solcSlotWord σ' I ⟨4⟩ :: d1 :: d2 :: dink :: dart :: q :: art :: ink :: iDust :: iSpot ::
        iRate :: ⟨0⟩ :: urn :: ilk :: R) mem aw o (cA', σ') _ _ := rd2215raw
  have rd2217 := rd2215.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2219 := rd2217.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2221 := rd2219.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd2222 := rd2221.shl (by native_decide) (by evm_ov)
  have rd2223 := rd2222.sub (by native_decide) (by evm_ov)
  have rd2224 := rd2223.and (by native_decide) (by evm_ov)
  have rd2225 := rd2224.swap2 (by native_decide) (by evm_ov)
  have rd2226 := rd2225.pop (by native_decide) (by evm_ov)
  have rd2231 := rd2226.push4 ⟨1769929592⟩ (by native_decide) (by evm_ov)
  have rd2232 := rd2231.swap1 (by native_decide) (by evm_ov)
  have rd2233 := rd2232.pop (by native_decide) (by evm_ov)
  have rd2236 := rd2233.push2 ⟨2242⟩ (by native_decide) (by evm_ov)
  have rd2237 := rd2236.dup5 (by native_decide) (by evm_ov)
  have rd2238 := RD.dup12 rd2237 (by native_decide) (by evm_ov)
  exact RD.catBiteReachMul3720Tail rd2238 (by native_decide) (by native_decide) (by evm_ov)

/-! ## Seg 7i (`2321`) `checkedMul` guard: `tabBase = dartRate*milkChop` @ pc `3720`

`Seg7i` (post-`fess` tail) re-derives `dartRate = dart*rate` (`@3720`, cannot re-overflow if `Seg7f`
succeeded, so `hRateFit`) then computes `tabBase = dartRate*milkChop` via a SECOND `@3720`
`checkedMul` (`milkChop` re-read from `mem[q+32]`).  The `tabBase` mul is the sixth overflow site. -/

/-- **`tabBase` mul-overflow guard** (`Seg7i`, `@3720`): reach the `dartRate*milkChop` `checkedMul`
frame `milkChop :: dartRate :: 2354 :: …`.  Feeds `catBiteMulOverflowRevertLeaf` (`a = milkChop`,
`b = dartRate`). -/
theorem catBiteReachGuardTabBase {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {q art ink iDust iSpot iRate urn ilk dink dart milkChop dartRate : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2321⟩
      (dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o (cA', σ') k C)
    (hChop : (if (⟨32⟩ + q).toNat ≥ mem.size ∨ (⟨32⟩ + q) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨32⟩ + q).toNat 32)))
        = milkChop)
    (haw : q.toNat + 64 ≤ aw.toNat * 32) (hqsz : q.toNat + 64 < UInt256.size)
    (hRateFit : iRate.toNat * dart.toNat < UInt256.size)
    (hDartRate : UInt256.mul dart iRate = dartRate)
    (hov : R.length + 24 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3720⟩
      (milkChop :: dartRate :: ⟨2354⟩ :: ⟨1000000000000000000⟩ :: ⟨0⟩ :: dink :: dart :: q :: art ::
        ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o (cA', σ') k' C' := by
  have e32q : (⟨32⟩ + q).toNat = q.toNat + 32 := uadd_lit32_toNat q (by omega)
  have hChopAw : UInt256.ofNat (MachineState.M aw.toNat (⟨32⟩ + q).toNat 32) = aw :=
    catBiteAwMInv32 aw (by rw [e32q]; omega)
  have rd2321 := rd.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd2323 := RD.push8 rd2321 ⟨1000000000000000000⟩ (by native_decide) (by evm_ov)
  have rd2332 := rd2323.push2 ⟨2354⟩ (by native_decide) (by evm_ov)
  have rd2335 := rd2332.push2 ⟨2344⟩ (by native_decide) (by evm_ov)
  have rd2338 := rd2335.dup6 (by native_decide) (by evm_ov)
  have rd2339 := rd2338.dup13 (by native_decide) (by evm_ov)
  have rd2340 := rd2339.push2 ⟨3720⟩ (by native_decide) (by evm_ov)
  have rd3720a := rd2340.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd2344⟩ := RD.catBiteCheckedMul rd3720a hRateFit (by native_decide) (by evm_ov)
  rw [hDartRate] at rd2344
  have rd2344j := rd2344.jumpdest (by native_decide) (by evm_ov)
  have rd2345 := rd2344j.dup7 (by native_decide) (by evm_ov)
  have rd2346 := rd2345.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd2348 := rd2346.add (by native_decide) (by evm_ov)
  have rd2349 := RD.mload 0 milkChop aw rd2348 (by native_decide) (catBiteMloadCost0 hChopAw)
    hChop hChopAw (by evm_ov)
  exact RD.catBiteReachMul3720Tail rd2349 (by native_decide) (by native_decide) (by evm_ov)

/-! ## Seg 6 (`1620`) `checkedSub` guard: `room = box - litter` @ pc `3762`

`Seg6` allocates the `milk` struct (`ilks[ilk]`), then computes `room = box.sub(litter)` via the
shared `@3762` `checkedSub`.  This reach replays the whole `milk`-struct build (so the concrete
`catBiteMilkMem` memory + the box/litter loads land) up to the `checkedSub` entry — WITHOUT the
`litter ≤ box` success hypothesis, so the underflow (`box < litter`) branch is exactly the divergence
the leaf handles. -/

/-- **`room` checkedSub-underflow guard** (`Seg6`, `@3762`): reach the `box.sub(litter)` `checkedSub`
frame `litter :: box :: 1708 :: …` (with the `milk` struct in memory).  Feeds
`catBiteRoomUnderflowRevertLeaf` (`b = litter`, `a = box`; underflow `box.toNat < litter.toNat`). -/
theorem catBiteReachGuardRoomSub {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {art ink iDust iSpot iRate urn ilk fp q : UInt256} {R : List UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1620⟩
      (art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R) mem aw o (cA', σ') k C)
    (hFp : (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = fp)
    (hQ : (if (⟨64⟩ : UInt256).toNat ≥ (catBiteScratchMem mem fp ilk).size
          ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        ((catBiteScratchMem mem fp ilk).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = q)
    (hKec : (catBiteScratchMem mem fp ilk).readWithPadding 0 64 =
        UInt256.toByteArray ilk ++ UInt256.toByteArray ⟨1⟩)
    (hawFp : fp.toNat + 96 ≤ aw.toNat * 32)
    (hawQ : q.toNat + 96 ≤ aw.toNat * 32)
    (hfpsz : fp.toNat + 96 < UInt256.size)
    (hqsz : q.toNat + 96 < UInt256.size)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3762⟩
      (solcSlotWord σ' I ⟨6⟩ :: solcSlotWord σ' I ⟨5⟩ :: ⟨1708⟩ :: ⟨0⟩ :: ⟨0⟩ :: q :: art :: ink ::
        iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      (catBiteMilkMem mem fp ilk q
        (UInt256.land biteAddrMaskWord (solcSlotWord σ' I (solcMappingSlot ⟨1⟩ ilk)))
        (solcSlotWord σ' I (solcMappingSlot ⟨1⟩ ilk + ⟨1⟩))
        (solcSlotWord σ' I (solcMappingSlot ⟨1⟩ ilk + ⟨2⟩)))
      aw o (cA', σ') k' C' := by
  -- offset arithmetic
  have e32fp : (⟨32⟩ + fp).toNat = fp.toNat + 32 := uadd_lit32_toNat fp (by omega)
  have e64fp : (⟨32⟩ + (⟨32⟩ + fp)).toNat = fp.toNat + 64 := by
    rw [uadd_lit32_toNat _ (by omega)]; omega
  have eq32 : (q + ⟨32⟩).toNat = q.toNat + 32 := uadd_word_lit32_toNat q (by omega)
  have eq64 : (q + ⟨64⟩).toNat = q.toNat + 64 := by
    rw [uadd_toNat, show (⟨64⟩ : UInt256).toNat = 64 from by decide, Nat.mod_eq_of_lt (by omega)]
  -- active-words invariance witnesses
  have hM0 : UInt256.ofNat (MachineState.M aw.toNat 0 32) = aw := catBiteAwMInv32 aw (by omega)
  have hM32 : UInt256.ofNat (MachineState.M aw.toNat 32 32) = aw := catBiteAwMInv32 aw (by omega)
  have hM64 : UInt256.ofNat (MachineState.M aw.toNat 64 32) = aw := catBiteAwMInv32 aw (by omega)
  have hMfp : UInt256.ofNat (MachineState.M aw.toNat fp.toNat 32) = aw := catBiteAwMInv32 aw (by omega)
  have hM32fp : UInt256.ofNat (MachineState.M aw.toNat (⟨32⟩ + fp).toNat 32) = aw :=
    catBiteAwMInv32 aw (by omega)
  have hM64fp : UInt256.ofNat (MachineState.M aw.toNat (⟨32⟩ + (⟨32⟩ + fp)).toNat 32) = aw :=
    catBiteAwMInv32 aw (by omega)
  have hMq : UInt256.ofNat (MachineState.M aw.toNat q.toNat 32) = aw := catBiteAwMInv32 aw (by omega)
  have hMq32 : UInt256.ofNat (MachineState.M aw.toNat (q + ⟨32⟩).toNat 32) = aw :=
    catBiteAwMInv32 aw (by omega)
  have hMq64 : UInt256.ofNat (MachineState.M aw.toNat (q + ⟨64⟩).toNat 32) = aw :=
    catBiteAwMInv32 aw (by omega)
  have hMkec : UInt256.ofNat (MachineState.M aw.toNat 0 64) = aw := catBiteAwMInv64 aw (by omega)
  have hmask0 : UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) ⟨0⟩ = ⟨0⟩ :=
    by native_decide
  -- 1620 → 3818 (call the 96-byte allocator)
  have rd1621 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd1624 := rd1621.push2 ⟨1628⟩ (by native_decide) (by evm_ov)
  have rd1627 := rd1624.push2 ⟨3818⟩ (by native_decide) (by evm_ov)
  have rd3818 := rd1627.jump (by native_decide) (by jump_dest) (by evm_ov)
  -- 3818 allocator body
  have rd3819 := rd3818.jumpdest (by native_decide) (by evm_ov)
  have rd3821 := rd3819.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd3822 := RD.mload 0 fp aw rd3821 (by native_decide) (catBiteMloadCost0 hM64) hFp hM64
    (by evm_ov)
  have rd3823 := rd3822.dup1 (by native_decide) (by evm_ov)
  have rd3825 := rd3823.push1 ⟨96⟩ (by native_decide) (by evm_ov)
  have rd3826 := rd3825.add (by native_decide) (by evm_ov)
  have rd3828 := rd3826.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd3829 := RD.mstore 0 ((UInt256.toByteArray (⟨96⟩ + fp)).write 0 mem 64 32) aw rd3828
    (by native_decide) (catBiteMstoreCost0 hM64) (by rfl) hM64 (by evm_ov)
  have rd3830 := rd3829.dup1 (by native_decide) (by evm_ov)
  have rd3832 := rd3830.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3834 := rd3832.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd3836 := rd3834.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd3838 := rd3836.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd3839 := rd3838.shl (by native_decide) (by evm_ov)
  have rd3840 := rd3839.sub (by native_decide) (by evm_ov)
  have rd3841 := rd3840.and (by native_decide) (by evm_ov)
  rw [hmask0] at rd3841
  have rd3842 := rd3841.dup2 (by native_decide) (by evm_ov)
  have rd3843 := RD.mstore 0 ((UInt256.toByteArray ⟨0⟩).write 0
      ((UInt256.toByteArray (⟨96⟩ + fp)).write 0 mem 64 32) fp.toNat 32) aw rd3842
    (by native_decide) (catBiteMstoreCost0 hMfp) (by rfl) hMfp (by evm_ov)
  have rd3845 := rd3843.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd3846 := rd3845.add (by native_decide) (by evm_ov)
  have rd3848 := rd3846.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3849 := rd3848.dup2 (by native_decide) (by evm_ov)
  have rd3850 := RD.mstore 0 ((UInt256.toByteArray ⟨0⟩).write 0
      ((UInt256.toByteArray ⟨0⟩).write 0
        ((UInt256.toByteArray (⟨96⟩ + fp)).write 0 mem 64 32) fp.toNat 32)
      (⟨32⟩ + fp).toNat 32) aw rd3849
    (by native_decide) (catBiteMstoreCost0 hM32fp) (by rfl) hM32fp (by evm_ov)
  have rd3852 := rd3850.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd3853 := rd3852.add (by native_decide) (by evm_ov)
  have rd3855 := rd3853.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3856 := rd3855.dup2 (by native_decide) (by evm_ov)
  have rd3857 := RD.mstore 0 (catBiteHelperMem mem fp) aw rd3856
    (by native_decide) (catBiteMstoreCost0 hM64fp) (by rfl) hM64fp (by evm_ov)
  have rd3858 := rd3857.pop (by native_decide) (by evm_ov)
  have rd3859 := rd3858.swap1 (by native_decide) (by evm_ov)
  have rd1628 := rd3859.jump (by native_decide) (by jump_dest) (by evm_ov)
  -- 1628 → keccak scratch build
  have rd1629 := rd1628.jumpdest (by native_decide) (by evm_ov)
  have rd1630 := rd1629.pop (by native_decide) (by evm_ov)
  have rd1632 := rd1630.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd1633 := rd1632.dup9 (by native_decide) (by evm_ov)
  have rd1634 := rd1633.dup2 (by native_decide) (by evm_ov)
  have rd1635 := RD.mstore 0 ((UInt256.toByteArray ilk).write 0 (catBiteHelperMem mem fp) 0 32)
    aw rd1634 (by native_decide) (catBiteMstoreCost0 hM0) (by rfl) hM0 (by evm_ov)
  have rd1637 := rd1635.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd1639 := rd1637.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd1640 := rd1639.dup2 (by native_decide) (by evm_ov)
  have rd1641 := rd1640.dup2 (by native_decide) (by evm_ov)
  have rd1642 := RD.mstore 0 (catBiteScratchMem mem fp ilk) aw rd1641
    (by native_decide) (catBiteMstoreCost0 hM32) (by rfl) hM32 (by evm_ov)
  have rd1644 := rd1642.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd1645 := rd1644.dup1 (by native_decide) (by evm_ov)
  have rd1646 := rd1645.dup5 (by native_decide) (by evm_ov)
  have rd1647 := rd1646.keccak256 0 (solcMappingSlot ⟨1⟩ ilk) aw (by native_decide)
    (catBiteKeccakCost0 hMkec)
    (by simp only [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide, hKec]; exact mappingSlot_single ilk ⟨1⟩)
    hMkec (by evm_ov)
  -- 1647 → struct copy (flip@q, chop@q+32, dunk@q+64)
  have rd1648 := rd1647.dup2 (by native_decide) (by evm_ov)
  have rd1649 := RD.mload 0 q aw rd1648 (by native_decide) (catBiteMloadCost0 hM64) hQ hM64
    (by evm_ov)
  have rd1651 := rd1649.push1 ⟨96⟩ (by native_decide) (by evm_ov)
  have rd1652 := rd1651.dup2 (by native_decide) (by evm_ov)
  have rd1653 := rd1652.add (by native_decide) (by evm_ov)
  have rd1654 := rd1653.dup4 (by native_decide) (by evm_ov)
  have rd1655 := RD.mstore 0 ((UInt256.toByteArray (q + ⟨96⟩)).write 0
      (catBiteScratchMem mem fp ilk) 64 32) aw rd1654
    (by native_decide) (catBiteMstoreCost0 hM64) (by rfl) hM64 (by evm_ov)
  have rd1656 := rd1655.dup2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1657⟩ := rd1656.sload (by native_decide) (by evm_ov)
  have rd1659 := rd1657.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd1661 := rd1659.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd1663 := rd1661.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd1664 := rd1663.shl (by native_decide) (by evm_ov)
  have rd1665 := rd1664.sub (by native_decide) (by evm_ov)
  have rd1666 := rd1665.and (by native_decide) (by evm_ov)
  have rd1667 := rd1666.dup2 (by native_decide) (by evm_ov)
  have rd1668 := RD.mstore 0 ((UInt256.toByteArray
      (UInt256.land biteAddrMaskWord (solcSlotWord σ' I (solcMappingSlot ⟨1⟩ ilk)))).write 0
      ((UInt256.toByteArray (q + ⟨96⟩)).write 0 (catBiteScratchMem mem fp ilk) 64 32) q.toNat 32)
    aw rd1667 (by native_decide) (catBiteMstoreCost0 hMq) (by rfl) hMq (by evm_ov)
  have rd1669 := rd1668.swap4 (by native_decide) (by evm_ov)
  have rd1670 := rd1669.dup2 (by native_decide) (by evm_ov)
  have rd1671 := rd1670.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1672⟩ := rd1671.sload (by native_decide) (by evm_ov)
  have rd1673 := rd1672.swap3 (by native_decide) (by evm_ov)
  have rd1674 := rd1673.dup5 (by native_decide) (by evm_ov)
  have rd1675 := rd1674.add (by native_decide) (by evm_ov)
  have rd1676 := rd1675.swap3 (by native_decide) (by evm_ov)
  have rd1677 := rd1676.swap1 (by native_decide) (by evm_ov)
  have rd1678 := rd1677.swap3 (by native_decide) (by evm_ov)
  have rd1679 := RD.mstore 0 ((UInt256.toByteArray
      (solcSlotWord σ' I (solcMappingSlot ⟨1⟩ ilk + ⟨1⟩))).write 0
      ((UInt256.toByteArray
        (UInt256.land biteAddrMaskWord (solcSlotWord σ' I (solcMappingSlot ⟨1⟩ ilk)))).write 0
        ((UInt256.toByteArray (q + ⟨96⟩)).write 0 (catBiteScratchMem mem fp ilk) 64 32) q.toNat 32)
      (q + ⟨32⟩).toNat 32) aw rd1678
    (by native_decide) (catBiteMstoreCost0 hMq32) (by rfl) hMq32 (by evm_ov)
  have rd1681 := rd1679.push1 ⟨2⟩ (by native_decide) (by evm_ov)
  have rd1682 := rd1681.swap1 (by native_decide) (by evm_ov)
  have rd1683 := rd1682.swap2 (by native_decide) (by evm_ov)
  have rd1684 := rd1683.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1685⟩ := rd1684.sload (by native_decide) (by evm_ov)
  have rd1686 := rd1685.swap1 (by native_decide) (by evm_ov)
  have rd1687 := rd1686.dup3 (by native_decide) (by evm_ov)
  have rd1688 := rd1687.add (by native_decide) (by evm_ov)
  have rd1689 := RD.mstore 0 (catBiteMilkMem mem fp ilk q
      (UInt256.land biteAddrMaskWord (solcSlotWord σ' I (solcMappingSlot ⟨1⟩ ilk)))
      (solcSlotWord σ' I (solcMappingSlot ⟨1⟩ ilk + ⟨1⟩))
      (solcSlotWord σ' I (solcMappingSlot ⟨1⟩ ilk + ⟨2⟩))) aw rd1688
    (by native_decide) (catBiteMstoreCost0 hMq64) (by rfl) hMq64 (by evm_ov)
  -- 1689 → box/litter loads + checkedSub entry
  have rd1691 := rd1689.push1 ⟨5⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1692⟩ := rd1691.sload (by native_decide) (by evm_ov)
  have rd1694 := rd1692.push1 ⟨6⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1695⟩ := rd1694.sload (by native_decide) (by evm_ov)
  have rd1696 := rd1695.swap2 (by native_decide) (by evm_ov)
  have rd1697 := rd1696.swap3 (by native_decide) (by evm_ov)
  have rd1698 := rd1697.swap2 (by native_decide) (by evm_ov)
  have rd1699 := rd1698.dup3 (by native_decide) (by evm_ov)
  have rd1700 := rd1699.swap2 (by native_decide) (by evm_ov)
  have rd1703 := rd1700.push2 ⟨1708⟩ (by native_decide) (by evm_ov)
  have rd1704 := rd1703.swap2 (by native_decide) (by evm_ov)
  have rd1707 := rd1704.push2 ⟨3762⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1707.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

/-! ## Seg 7b (`1810`) div-by-zero `INVALID` guard: `milkChop != 0` @ pc `1865`

solc 0.6.12 compiles `dartDenomRate / milk.chop` with a `milk.chop != 0` guard whose false branch is
the `INVALID` opcode `0xfe` at pc `1865`.  This reach replays `Seg7b` through `dunkRoom = min(...)`,
the `dunkRoom*WAD` `checkedMul`, the `rate != 0` guard, and the `dunkRoomWad / rate` div, up to the
`milk.chop != 0` guard `PUSH2 1866; JUMPI` — then takes the `JUMPI`-not-taken (`milkChop = 0`) fall
through to the `INVALID` at pc `1865`.  Feeds `catBiteMilkChopZeroRevertLeaf`. -/

/-- **`milkChop` div-by-zero `INVALID` guard** (`Seg7b`, `@1865`): from the `1810` entry, past the
`dunkRoom*WAD` mul (`hFitWad`) and `rate != 0` guard (`hRatePos`), reach the `INVALID` at pc `1865` on
the `milkChop = 0` branch.  Feeds `catBiteMilkChopZeroRevertLeaf` (`invalidPc := 1865`). -/
theorem catBiteReachGuardMilkChopZero {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {room q art ink iDust iSpot iRate urn ilk : UInt256}
    {milkChop milkDunk dunkRoom dunkRoomWad dartDenomRate : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1810⟩
      (room :: ⟨0⟩ :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o acc k C)
    (hChop : (if (⟨32⟩ + q).toNat ≥ mem.size ∨ (⟨32⟩ + q) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨32⟩ + q).toNat 32)))
        = milkChop)
    (hDunk : (if (⟨64⟩ + q).toNat ≥ mem.size ∨ (⟨64⟩ + q) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ + q).toNat 32)))
        = milkDunk)
    (haw : q.toNat + 96 ≤ aw.toNat * 32) (hqsz : q.toNat + 96 < UInt256.size)
    (hRatePos : iRate ≠ ⟨0⟩)
    (hDunkRoom : (if UInt256.gt milkDunk room = ⟨0⟩ then milkDunk else room) = dunkRoom)
    (hFitWad : (⟨1000000000000000000⟩ : UInt256).toNat * dunkRoom.toNat < UInt256.size)
    (hDunkRoomWad : UInt256.mul dunkRoom ⟨1000000000000000000⟩ = dunkRoomWad)
    (hDartDenom : UInt256.div dunkRoomWad iRate = dartDenomRate)
    (hChopZero : milkChop = ⟨0⟩)
    (hov : R.length + 24 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1865⟩
      (dartDenomRate :: milkChop :: art :: ⟨1872⟩ :: room :: ⟨0⟩ :: q :: art :: ink :: iDust ::
        iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o acc k' C' := by
  have e32q : (⟨32⟩ + q).toNat = q.toNat + 32 := uadd_lit32_toNat q (by omega)
  have e64q : (⟨64⟩ + q).toNat = q.toNat + 64 := by
    rw [uadd_toNat, show (⟨64⟩ : UInt256).toNat = 64 from by decide, Nat.add_comm,
      Nat.mod_eq_of_lt (by omega)]
  have hChopAw : UInt256.ofNat (MachineState.M aw.toNat (⟨32⟩ + q).toNat 32) = aw :=
    catBiteAwMInv32 aw (by rw [e32q]; omega)
  have hDunkAw : UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ + q).toNat 32) = aw :=
    catBiteAwMInv32 aw (by rw [e64q]; omega)
  have rd1811 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd1814 := rd1811.push2 ⟨1872⟩ (by native_decide) (by evm_ov)
  have rd1815 := rd1814.dup5 (by native_decide) (by evm_ov)
  have rd1816 := rd1815.dup5 (by native_decide) (by evm_ov)
  have rd1818 := rd1816.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd1819 := rd1818.add (by native_decide) (by evm_ov)
  have rd1820 := RD.mload 0 milkChop aw rd1819 (by native_decide) (catBiteMloadCost0 hChopAw)
    hChop hChopAw (by evm_ov)
  have rd1821 := rd1820.dup11 (by native_decide) (by evm_ov)
  have rd1824 := rd1821.push2 ⟨1851⟩ (by native_decide) (by evm_ov)
  have rd1827 := rd1824.push2 ⟨1837⟩ (by native_decide) (by evm_ov)
  have rd1828 := rd1827.dup9 (by native_decide) (by evm_ov)
  have rd1830 := rd1828.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd1831 := rd1830.add (by native_decide) (by evm_ov)
  have rd1832 := RD.mload 0 milkDunk aw rd1831 (by native_decide) (catBiteMloadCost0 hDunkAw)
    hDunk hDunkAw (by evm_ov)
  have rd1833 := rd1832.dup8 (by native_decide) (by evm_ov)
  have rd1836 := rd1833.push2 ⟨3778⟩ (by native_decide) (by evm_ov)
  have rd3778a := rd1836.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd1837⟩ := RD.catBiteMin rd3778a (by native_decide) (by evm_ov)
  rw [hDunkRoom] at rd1837
  have rd1837j := rd1837.jumpdest (by native_decide) (by evm_ov)
  have rd1838 := RD.push8 rd1837j ⟨1000000000000000000⟩ (by native_decide) (by evm_ov)
  have rd1847 := rd1838.push2 ⟨3720⟩ (by native_decide) (by evm_ov)
  have rd3720a := rd1847.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd1851⟩ := RD.catBiteCheckedMul rd3720a hFitWad (by native_decide) (by evm_ov)
  rw [hDunkRoomWad] at rd1851
  have rd1851j := rd1851.jumpdest (by native_decide) (by evm_ov)
  have rd1852 := rd1851j.dup2 (by native_decide) (by evm_ov)
  have rd1853 := rd1852.push2 ⟨1858⟩ (by native_decide) (by evm_ov)
  have rd1858 := rd1853.jumpiT (by native_decide) hRatePos (by jump_dest) (by evm_ov)
  have rd1859 := rd1858.jumpdest (by native_decide) (by evm_ov)
  have rd1860 := rd1859.div (by native_decide) (by evm_ov)
  rw [hDartDenom] at rd1860
  have rd1861 := rd1860.dup2 (by native_decide) (by evm_ov)
  have rd1864 := rd1861.push2 ⟨1866⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1864.jumpiNT (by native_decide) hChopZero (by evm_ov)⟩

/-! ## `require` string-revert guards

Each `bite` `require(…, "msg")` compiles to `<cond>; PUSH2 okPc; JUMPI; <Error(string) tail>;
okPc: …`.  The revert leaf `RD.catBiteGuardStringRevert` (fired by `catBiteRequireStringRevertLeaf`)
takes a cursor at the `PUSH2 okPc` pc with the require boolean `cond` on top and `cond = ⟨0⟩`.  Each
reach below replays its segment to that `PUSH2 okPc` pc, leaving `cond` as the raw EVM boolean (NOT
rewritten to `1`), so the integrator can `by_cases (cond = ⟨0⟩)`: `⟨0⟩` → require leaf, else continue.
For the `&&` requires the reach assumes the FIRST conjunct holds (the short-circuit fall-through) and
exposes the SECOND conjunct's boolean; the first-conjunct short-circuit reaches are left for a
follow-up. -/

/-- **`live` require guard** (`Seg4`, `@1458`): `require(live == 1, "Cat/not-live")`.  Reach the
guard `PUSH2 1521` with `cond = (1 == live)` on top.  Feeds `catBiteRequireStringRevertLeaf`
(`guardPc := 1458`, `okPc := 1521`; `cond = ⟨0⟩ ⇔ live ≠ 1`). -/
theorem catBiteReachGuardLive {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {art ink iDust iSpot iRate urn ilk : UInt256} {R : List UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1447⟩
      (art :: ink :: ⟨0⟩ :: ⟨0⟩ :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o (cA', σ') k C)
    (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1458⟩
      (UInt256.eq ⟨1⟩ (catSlotWord ⟨2⟩ σ' I) :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ ::
        urn :: ilk :: R)
      mem aw o (cA', σ') k' C' := by
  have rd1449 := rd.push1 ⟨2⟩ (by native_decide) (by evm_ov)
  obtain ⟨k1450, C1450, rd1450raw⟩ := rd1449.sload (by native_decide) (by evm_ov)
  have rd1450 : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1450⟩
      (catSlotWord ⟨2⟩ σ' I :: art :: ink :: ⟨0⟩ :: ⟨0⟩ :: iDust :: iSpot :: iRate :: ⟨0⟩ ::
        urn :: ilk :: R) mem aw o (cA', σ') k1450 C1450 := rd1450raw
  have rd1451 := rd1450.swap2 (by native_decide) (by evm_ov)
  have rd1452 := rd1451.swap4 (by native_decide) (by evm_ov)
  have rd1453 := rd1452.pop (by native_decide) (by evm_ov)
  have rd1454 := rd1453.swap2 (by native_decide) (by evm_ov)
  have rd1455 := rd1454.pop (by native_decide) (by evm_ov)
  have rd1457 := rd1455.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1457.eq (by native_decide) (by evm_ov)⟩

/-- **`unsafe` require guard** (`Seg5`, `@1555`): `require(spot > 0 && ink*spot < art*rate,
"Cat/not-unsafe")`.  From the `1521` entry, past the `spot > 0` short-circuit (`hspotPos`) and both
non-overflowing `checkedMul`s (`hfitArtRate`, `hfitInkSpot`), reach the guard `PUSH2 1620` with
`cond = (ink*spot < art*rate)` on top.  Feeds `catBiteRequireStringRevertLeaf` (`guardPc := 1555`,
`okPc := 1620`; `cond = ⟨0⟩ ⇔ ink*spot ≥ art*rate`). -/
theorem catBiteReachGuardUnsafe {cA gh bl σ σ₀ A I} {g : UInt256}
    {art ink iDust iSpot iRate urn ilk : UInt256} {R : List UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1521⟩
      (art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R) mem aw o acc k C)
    (hspotPos : 0 < iSpot.toNat)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1555⟩
      (UInt256.lt (UInt256.mul ink iSpot) (UInt256.mul art iRate) :: art :: ink :: iDust :: iSpot ::
        iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o acc k' C' := by
  have rd1522 := rd.jumpdest (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1524 := rd1522.push1 ⟨0⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1525 := rd1524.dup5 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1526 := rd1525.gt (by native_decide) (by simp only [List.length_cons]; omega)
  rw [ugt_one (show (⟨0⟩ : UInt256).toNat < iSpot.toNat by simpa using hspotPos)] at rd1526
  have rd1527 := rd1526.dup1 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1528 := rd1527.iszero (by native_decide) (by simp only [List.length_cons]; omega)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by native_decide] at rd1528
  have rd1531 := rd1528.push2 ⟨1554⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1532 := rd1531.jumpiNT (by native_decide) rfl (by simp only [List.length_cons]; omega)
  have rd1533 := rd1532.pop (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1536 := rd1533.push2 ⟨1542⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1537 := rd1536.dup2 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1538 := rd1537.dup7 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1541 := rd1538.push2 ⟨3720⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd3720a := rd1541.jump (by native_decide) (by jump_dest) (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd1542⟩ := RD.catBiteCheckedMul rd3720a
    (by rw [Nat.mul_comm]; exact hfitArtRate) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1543 := rd1542.jumpdest (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1546 := rd1543.push2 ⟨1552⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1547 := rd1546.dup4 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1548 := rd1547.dup7 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1551 := rd1548.push2 ⟨3720⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd3720b := rd1551.jump (by native_decide) (by jump_dest) (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd1552⟩ := RD.catBiteCheckedMul rd3720b
    (by rw [Nat.mul_comm]; exact hfitInkSpot) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1553 := rd1552.jumpdest (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1554 := rd1553.lt (by native_decide) (by simp only [List.length_cons]; omega)
  exact ⟨_, _, rd1554.jumpdest (by native_decide) (by simp only [List.length_cons]; omega)⟩

/-- **`room ≥ dust` require guard** (`Seg7a`, `@1730`): `require(litter < box && room >= dust,
"Cat/liquidation-limit-hit")`.  From the `1708` entry, past the `litter < box` short-circuit
(`hlitterbox`), reach the guard `PUSH2 1810` with `cond = ¬(room < dust)` on top.  Feeds
`catBiteRequireStringRevertLeaf` (`guardPc := 1730`, `okPc := 1810`; `cond = ⟨0⟩ ⇔ room < dust`). -/
theorem catBiteReachGuardRoomDust {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {room q art ink iDust iSpot iRate urn ilk : UInt256} {R : List UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1708⟩
      (room :: ⟨0⟩ :: ⟨0⟩ :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o (cA', σ') k C)
    (hlitterbox : (solcSlotWord σ' I ⟨6⟩).toNat < (solcSlotWord σ' I ⟨5⟩).toNat)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1730⟩
      (UInt256.isZero (UInt256.lt room iDust) :: room :: ⟨0⟩ :: q :: art :: ink :: iDust :: iSpot ::
        iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o (cA', σ') k' C' := by
  have rd1709 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd1710 := rd1709.swap1 (by native_decide) (by evm_ov)
  have rd1711 := rd1710.pop (by native_decide) (by evm_ov)
  have rd1713 := rd1711.push1 ⟨5⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1714raw⟩ := rd1713.sload (by native_decide) (by evm_ov)
  have rd1714 : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1714⟩
      (solcSlotWord σ' I ⟨5⟩ :: room :: ⟨0⟩ :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ ::
        urn :: ilk :: R) mem aw o (cA', σ') _ _ := rd1714raw
  have rd1716 := rd1714.push1 ⟨6⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1717raw⟩ := rd1716.sload (by native_decide) (by evm_ov)
  have rd1717 : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1717⟩
      (solcSlotWord σ' I ⟨6⟩ :: solcSlotWord σ' I ⟨5⟩ :: room :: ⟨0⟩ :: q :: art :: ink :: iDust ::
        iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R) mem aw o (cA', σ') _ _ := rd1717raw
  have rd1718 := rd1717.lt (by native_decide) (by evm_ov)
  rw [ult_one hlitterbox] at rd1718
  have rd1719 := rd1718.dup1 (by native_decide) (by evm_ov)
  have rd1720 := rd1719.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd1720
  have rd1723 := rd1720.push2 ⟨1729⟩ (by native_decide) (by evm_ov)
  have rd1724 := rd1723.jumpiNT (by native_decide) rfl (by evm_ov)
  have rd1725 := rd1724.pop (by native_decide) (by evm_ov)
  have rd1726 := rd1725.dup6 (by native_decide) (by evm_ov)
  have rd1727 := rd1726.dup2 (by native_decide) (by evm_ov)
  have rd1728 := rd1727.lt (by native_decide) (by evm_ov)
  have rd1729 := rd1728.iszero (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1729.jumpdest (by native_decide) (by evm_ov)⟩

/-- **`dink > 0` require guard** (`Seg7c`, `@1918`): `require(dart > 0 && dink > 0,
"Cat/null-auction")`.  From the `1872` entry, past the `inkDart`/`dinkCandidate`/`dink = min(…)`
DSMath chain and the `dart > 0` short-circuit (`hDartPos`), reach the guard `PUSH2 1985` with
`cond = (dink > 0)` on top.  Feeds `catBiteRequireStringRevertLeaf` (`guardPc := 1918`,
`okPc := 1985`; `cond = ⟨0⟩ ⇔ dink = 0`). -/
theorem catBiteReachGuardDinkPos {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {room q art ink iDust iSpot iRate urn ilk : UInt256}
    {dart inkDart dinkCandidate dink : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1872⟩
      (dart :: room :: ⟨0⟩ :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o acc k C)
    (hArtPos : art ≠ ⟨0⟩)
    (hFitInkDart : dart.toNat * ink.toNat < UInt256.size)
    (hInkDart : UInt256.mul ink dart = inkDart)
    (hDinkCand : UInt256.div inkDart art = dinkCandidate)
    (hDink : (if UInt256.gt ink dinkCandidate = ⟨0⟩ then ink else dinkCandidate) = dink)
    (hDartPos : 0 < dart.toNat)
    (hov : R.length + 24 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1918⟩
      (UInt256.gt dink ⟨0⟩ :: dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ ::
        urn :: ilk :: R)
      mem aw o acc k' C' := by
  have rd1873 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd1874 := rd1873.swap2 (by native_decide) (by evm_ov)
  have rd1875 := rd1874.pop (by native_decide) (by evm_ov)
  have rd1876 := rd1875.pop (by native_decide) (by evm_ov)
  have rd1878 := rd1876.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd1881 := rd1878.push2 ⟨1899⟩ (by native_decide) (by evm_ov)
  have rd1882 := rd1881.dup6 (by native_decide) (by evm_ov)
  have rd1883 := rd1882.dup6 (by native_decide) (by evm_ov)
  have rd1886 := rd1883.push2 ⟨1892⟩ (by native_decide) (by evm_ov)
  have rd1887 := rd1886.dup9 (by native_decide) (by evm_ov)
  have rd1888 := rd1887.dup7 (by native_decide) (by evm_ov)
  have rd1891 := rd1888.push2 ⟨3720⟩ (by native_decide) (by evm_ov)
  have rd3720 := rd1891.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd1892⟩ := RD.catBiteCheckedMul rd3720 hFitInkDart (by native_decide) (by evm_ov)
  rw [hInkDart] at rd1892
  have rd1892j := rd1892.jumpdest (by native_decide) (by evm_ov)
  have rd1893 := rd1892j.dup2 (by native_decide) (by evm_ov)
  have rd1894 := rd1893.push2 ⟨1866⟩ (by native_decide) (by evm_ov)
  have rd1866 := rd1894.jumpiT (by native_decide) hArtPos (by jump_dest) (by evm_ov)
  have rd1867 := rd1866.jumpdest (by native_decide) (by evm_ov)
  have rd1868 := rd1867.div (by native_decide) (by evm_ov)
  rw [hDinkCand] at rd1868
  have rd1871 := rd1868.push2 ⟨3778⟩ (by native_decide) (by evm_ov)
  have rd3778 := rd1871.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd1899⟩ := RD.catBiteMin rd3778 (by native_decide) (by evm_ov)
  rw [hDink] at rd1899
  have rd1900 := rd1899.jumpdest (by native_decide) (by evm_ov)
  have rd1901 := rd1900.swap1 (by native_decide) (by evm_ov)
  have rd1902 := rd1901.pop (by native_decide) (by evm_ov)
  have rd1904 := rd1902.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd1905 := rd1904.dup3 (by native_decide) (by evm_ov)
  have rd1906 := rd1905.gt (by native_decide) (by evm_ov)
  rw [ugt_one (show (⟨0⟩ : UInt256).toNat < dart.toNat by simpa using hDartPos)] at rd1906
  have rd1907 := rd1906.dup1 (by native_decide) (by evm_ov)
  have rd1908 := rd1907.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd1908
  have rd1911 := rd1908.push2 ⟨1917⟩ (by native_decide) (by evm_ov)
  have rd1912 := rd1911.jumpiNT (by native_decide) rfl (by evm_ov)
  have rd1913 := rd1912.pop (by native_decide) (by evm_ov)
  have rd1915 := rd1913.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd1916 := rd1915.dup2 (by native_decide) (by evm_ov)
  have rd1917 := rd1916.gt (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1917.jumpdest (by native_decide) (by evm_ov)⟩

/-- **`dink ≤ 2²⁵⁵` require guard** (`Seg7d`, `@2010`): `require(dart <= 2**255 && dink <= 2**255,
"Cat/overflow")`.  From the `1985` entry, past the `dart <= 2**255` short-circuit (`hDartLim`), reach
the guard `PUSH2 2073` with `cond = (dink <= 2**255)` on top.  Feeds
`catBiteRequireStringRevertLeaf` (`guardPc := 2010`, `okPc := 2073`; `cond = ⟨0⟩ ⇔ dink > 2**255`). -/
theorem catBiteReachGuardDinkLimit {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {q art ink iDust iSpot iRate urn ilk dart dink : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1985⟩
      (dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o acc k C)
    (hDartLim : dart.toNat ≤ (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2010⟩
      (UInt256.isZero (UInt256.gt dink (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩)) :: dink :: dart ::
        q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o acc k' C' := by
  have rd1986 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd1988 := rd1986.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd1990 := rd1988.push1 ⟨255⟩ (by native_decide) (by evm_ov)
  have rd1991 := rd1990.shl (by native_decide) (by evm_ov)
  have rd1992 := rd1991.dup3 (by native_decide) (by evm_ov)
  have rd1993 := rd1992.gt (by native_decide) (by evm_ov)
  rw [ugt_zero hDartLim] at rd1993
  have rd1994 := rd1993.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd1994
  have rd1995 := rd1994.dup1 (by native_decide) (by evm_ov)
  have rd1996 := rd1995.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd1996
  have rd1999 := rd1996.push2 ⟨2009⟩ (by native_decide) (by evm_ov)
  have rd2000 := rd1999.jumpiNT (by native_decide) rfl (by evm_ov)
  have rd2001 := rd2000.pop (by native_decide) (by evm_ov)
  have rd2003 := rd2001.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2005 := rd2003.push1 ⟨255⟩ (by native_decide) (by evm_ov)
  have rd2006 := rd2005.shl (by native_decide) (by evm_ov)
  have rd2007 := rd2006.dup2 (by native_decide) (by evm_ov)
  have rd2008 := rd2007.gt (by native_decide) (by evm_ov)
  have rd2009 := rd2008.iszero (by native_decide) (by evm_ov)
  exact ⟨_, _, rd2009.jumpdest (by native_decide) (by evm_ov)⟩

/-! ### First-conjunct short-circuit reaches

For each `require(A && B)` the reach above assumed `A` holds and exposed `B`'s boolean.  The reaches
below cover the DUAL: `A` fails, so solc short-circuits — `DUP1; ISZERO; PUSH2 conv; JUMPI`-taken —
carrying the `A = 0` value to the convergence `JUMPDEST` and thence to the SAME require guard `PUSH2
okPc` with a literal `⟨0⟩` on top.  So the integrator's `by_cases` on the first conjunct feeds these
on the failing side and the `*Unsafe`/`*RoomDust`/`*DinkPos`/`*DinkLimit` reaches on the holding
side — both landing the require leaf's cursor at the same `guardPc`. -/

/-- **`spot > 0` short-circuit guard** (`Seg5`, `@1555`): the `spot = 0` first-conjunct failure of
`require(spot > 0 && …)`.  Reaches the `unsafe` guard `PUSH2 1620` with `cond = ⟨0⟩`.  Feeds
`catBiteRequireStringRevertLeaf` (`guardPc := 1555`, `okPc := 1620`, `cond = ⟨0⟩` by `rfl`). -/
theorem catBiteReachGuardSpot {cA gh bl σ σ₀ A I} {g : UInt256}
    {art ink iDust iSpot iRate urn ilk : UInt256} {R : List UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1521⟩
      (art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R) mem aw o acc k C)
    (hSpotZero : iSpot = ⟨0⟩)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1555⟩
      (⟨0⟩ :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o acc k' C' := by
  have rd1522 := rd.jumpdest (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1524 := rd1522.push1 ⟨0⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1525 := rd1524.dup5 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1526 := rd1525.gt (by native_decide) (by simp only [List.length_cons]; omega)
  rw [show UInt256.gt iSpot ⟨0⟩ = ⟨0⟩ from by rw [hSpotZero]; native_decide] at rd1526
  have rd1527 := rd1526.dup1 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1528 := rd1527.iszero (by native_decide) (by simp only [List.length_cons]; omega)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by native_decide] at rd1528
  have rd1531 := rd1528.push2 ⟨1554⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1554 := rd1531.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, rd1554.jumpdest (by native_decide) (by simp only [List.length_cons]; omega)⟩

/-- **`litter < box` short-circuit guard** (`Seg7a`, `@1730`): the `box ≤ litter` first-conjunct
failure of `require(litter < box && …)` (reachable only at `litter = box`, since `litter > box`
already underflowed the `Seg6` `checkedSub`).  Reaches the `room ≥ dust` guard `PUSH2 1810` with
`cond = ⟨0⟩`.  Feeds `catBiteRequireStringRevertLeaf` (`guardPc := 1730`, `okPc := 1810`). -/
theorem catBiteReachGuardLitter {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {room q art ink iDust iSpot iRate urn ilk : UInt256} {R : List UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1708⟩
      (room :: ⟨0⟩ :: ⟨0⟩ :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o (cA', σ') k C)
    (hLitterFail : (solcSlotWord σ' I ⟨5⟩).toNat ≤ (solcSlotWord σ' I ⟨6⟩).toNat)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1730⟩
      (⟨0⟩ :: room :: ⟨0⟩ :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o (cA', σ') k' C' := by
  have rd1709 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd1710 := rd1709.swap1 (by native_decide) (by evm_ov)
  have rd1711 := rd1710.pop (by native_decide) (by evm_ov)
  have rd1713 := rd1711.push1 ⟨5⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1714raw⟩ := rd1713.sload (by native_decide) (by evm_ov)
  have rd1714 : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1714⟩
      (solcSlotWord σ' I ⟨5⟩ :: room :: ⟨0⟩ :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ ::
        urn :: ilk :: R) mem aw o (cA', σ') _ _ := rd1714raw
  have rd1716 := rd1714.push1 ⟨6⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1717raw⟩ := rd1716.sload (by native_decide) (by evm_ov)
  have rd1717 : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1717⟩
      (solcSlotWord σ' I ⟨6⟩ :: solcSlotWord σ' I ⟨5⟩ :: room :: ⟨0⟩ :: q :: art :: ink :: iDust ::
        iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R) mem aw o (cA', σ') _ _ := rd1717raw
  have rd1718 := rd1717.lt (by native_decide) (by evm_ov)
  rw [ult_zero hLitterFail] at rd1718
  have rd1719 := rd1718.dup1 (by native_decide) (by evm_ov)
  have rd1720 := rd1719.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by native_decide] at rd1720
  have rd1723 := rd1720.push2 ⟨1729⟩ (by native_decide) (by evm_ov)
  have rd1729 := rd1723.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)
  exact ⟨_, _, rd1729.jumpdest (by native_decide) (by evm_ov)⟩

/-- **`dart > 0` short-circuit guard** (`Seg7c`, `@1918`): the `dart = 0` first-conjunct failure of
`require(dart > 0 && dink > 0)`.  Reaches the `dink > 0` guard `PUSH2 1985` with `cond = ⟨0⟩` (via
the `inkDart`/`dinkCandidate`/`dink = min(…)` chain, then the short-circuit).  Feeds
`catBiteRequireStringRevertLeaf` (`guardPc := 1918`, `okPc := 1985`). -/
theorem catBiteReachGuardDartPos {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {room q art ink iDust iSpot iRate urn ilk : UInt256}
    {dart inkDart dinkCandidate dink : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1872⟩
      (dart :: room :: ⟨0⟩ :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o acc k C)
    (hArtPos : art ≠ ⟨0⟩)
    (hFitInkDart : dart.toNat * ink.toNat < UInt256.size)
    (hInkDart : UInt256.mul ink dart = inkDart)
    (hDinkCand : UInt256.div inkDart art = dinkCandidate)
    (hDink : (if UInt256.gt ink dinkCandidate = ⟨0⟩ then ink else dinkCandidate) = dink)
    (hDartZero : dart = ⟨0⟩)
    (hov : R.length + 24 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1918⟩
      (⟨0⟩ :: dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o acc k' C' := by
  have rd1873 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd1874 := rd1873.swap2 (by native_decide) (by evm_ov)
  have rd1875 := rd1874.pop (by native_decide) (by evm_ov)
  have rd1876 := rd1875.pop (by native_decide) (by evm_ov)
  have rd1878 := rd1876.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd1881 := rd1878.push2 ⟨1899⟩ (by native_decide) (by evm_ov)
  have rd1882 := rd1881.dup6 (by native_decide) (by evm_ov)
  have rd1883 := rd1882.dup6 (by native_decide) (by evm_ov)
  have rd1886 := rd1883.push2 ⟨1892⟩ (by native_decide) (by evm_ov)
  have rd1887 := rd1886.dup9 (by native_decide) (by evm_ov)
  have rd1888 := rd1887.dup7 (by native_decide) (by evm_ov)
  have rd1891 := rd1888.push2 ⟨3720⟩ (by native_decide) (by evm_ov)
  have rd3720 := rd1891.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd1892⟩ := RD.catBiteCheckedMul rd3720 hFitInkDart (by native_decide) (by evm_ov)
  rw [hInkDart] at rd1892
  have rd1892j := rd1892.jumpdest (by native_decide) (by evm_ov)
  have rd1893 := rd1892j.dup2 (by native_decide) (by evm_ov)
  have rd1894 := rd1893.push2 ⟨1866⟩ (by native_decide) (by evm_ov)
  have rd1866 := rd1894.jumpiT (by native_decide) hArtPos (by jump_dest) (by evm_ov)
  have rd1867 := rd1866.jumpdest (by native_decide) (by evm_ov)
  have rd1868 := rd1867.div (by native_decide) (by evm_ov)
  rw [hDinkCand] at rd1868
  have rd1871 := rd1868.push2 ⟨3778⟩ (by native_decide) (by evm_ov)
  have rd3778 := rd1871.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd1899⟩ := RD.catBiteMin rd3778 (by native_decide) (by evm_ov)
  rw [hDink] at rd1899
  have rd1900 := rd1899.jumpdest (by native_decide) (by evm_ov)
  have rd1901 := rd1900.swap1 (by native_decide) (by evm_ov)
  have rd1902 := rd1901.pop (by native_decide) (by evm_ov)
  have rd1904 := rd1902.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd1905 := rd1904.dup3 (by native_decide) (by evm_ov)
  have rd1906 := rd1905.gt (by native_decide) (by evm_ov)
  rw [show UInt256.gt dart ⟨0⟩ = ⟨0⟩ from by rw [hDartZero]; native_decide] at rd1906
  have rd1907 := rd1906.dup1 (by native_decide) (by evm_ov)
  have rd1908 := rd1907.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by native_decide] at rd1908
  have rd1911 := rd1908.push2 ⟨1917⟩ (by native_decide) (by evm_ov)
  have rd1917 := rd1911.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)
  exact ⟨_, _, rd1917.jumpdest (by native_decide) (by evm_ov)⟩

/-- **`dart ≤ 2²⁵⁵` short-circuit guard** (`Seg7d`, `@2010`): the `dart > 2**255` first-conjunct
failure of `require(dart <= 2**255 && dink <= 2**255)`.  Reaches the `dink ≤ 2**255` guard
`PUSH2 2073` with `cond = ⟨0⟩`.  Feeds `catBiteRequireStringRevertLeaf` (`guardPc := 2010`,
`okPc := 2073`). -/
theorem catBiteReachGuardDartLimit {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {q art ink iDust iSpot iRate urn ilk dart dink : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1985⟩
      (dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o acc k C)
    (hDartLimFail : (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat < dart.toNat)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2010⟩
      (⟨0⟩ :: dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o acc k' C' := by
  have rd1986 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd1988 := rd1986.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd1990 := rd1988.push1 ⟨255⟩ (by native_decide) (by evm_ov)
  have rd1991 := rd1990.shl (by native_decide) (by evm_ov)
  have rd1992 := rd1991.dup3 (by native_decide) (by evm_ov)
  have rd1993 := rd1992.gt (by native_decide) (by evm_ov)
  rw [ugt_one hDartLimFail] at rd1993
  have rd1994 := rd1993.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by native_decide] at rd1994
  have rd1995 := rd1994.dup1 (by native_decide) (by evm_ov)
  have rd1996 := rd1995.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by native_decide] at rd1996
  have rd1999 := rd1996.push2 ⟨2009⟩ (by native_decide) (by evm_ov)
  have rd2009 := rd1999.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)
  exact ⟨_, _, rd2009.jumpdest (by native_decide) (by evm_ov)⟩

end Benchmarks.Dss.Cat
