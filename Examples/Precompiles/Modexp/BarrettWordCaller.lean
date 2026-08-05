import Examples.Precompiles.Modexp.Dispatcher

/-!
# Exact one-word Barrett caller path

This file starts the even-modulus Barrett backend after the shared PC 1592 nontrivial checks.  The
first theorem covers the direct leading-zero scan exit: the modulus payload is already positioned
at its first significant byte, so the backend keeps the one-word representation and proceeds
towards the existing `modexpWordInto` helper.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxHeartbeats 0
set_option maxRecDepth 500000
set_option Elab.async false

private theorem barrettScanDirectDecodes :
    [decode runtimeBytecode ⟨1592⟩, decode runtimeBytecode ⟨1593⟩,
      decode runtimeBytecode ⟨1594⟩, decode runtimeBytecode ⟨1595⟩,
      decode runtimeBytecode ⟨1597⟩, decode runtimeBytecode ⟨1598⟩,
      decode runtimeBytecode ⟨1599⟩, decode runtimeBytecode ⟨1601⟩,
      decode runtimeBytecode ⟨1602⟩, decode runtimeBytecode ⟨1603⟩,
      decode runtimeBytecode ⟨1604⟩, decode runtimeBytecode ⟨1605⟩,
      decode runtimeBytecode ⟨1606⟩, decode runtimeBytecode ⟨1607⟩,
      decode runtimeBytecode ⟨1608⟩, decode runtimeBytecode ⟨1609⟩,
      decode runtimeBytecode ⟨1610⟩, decode runtimeBytecode ⟨1611⟩,
      decode runtimeBytecode ⟨1612⟩, decode runtimeBytecode ⟨1613⟩,
      decode runtimeBytecode ⟨1614⟩, decode runtimeBytecode ⟨1617⟩,
      decode runtimeBytecode ⟨1625⟩, decode runtimeBytecode ⟨1626⟩,
      decode runtimeBytecode ⟨1627⟩, decode runtimeBytecode ⟨1628⟩,
      decode runtimeBytecode ⟨1629⟩, decode runtimeBytecode ⟨1630⟩,
      decode runtimeBytecode ⟨1631⟩, decode runtimeBytecode ⟨1632⟩,
      decode runtimeBytecode ⟨1633⟩, decode runtimeBytecode ⟨1634⟩,
      decode runtimeBytecode ⟨1635⟩, decode runtimeBytecode ⟨1636⟩,
      decode runtimeBytecode ⟨1638⟩, decode runtimeBytecode ⟨1639⟩,
      decode runtimeBytecode ⟨1640⟩, decode runtimeBytecode ⟨1641⟩,
      decode runtimeBytecode ⟨1642⟩, decode runtimeBytecode ⟨1645⟩] =
    [some (.DUP2, .none), some (.DUP2, .none), some (.ADD, .none),
      some (.Push .PUSH1, some (⟨31⟩, 1)), some (.ADD, .none),
      some (.SWAP5, .none), some (.Push .PUSH1, some (⟨32⟩, 1)),
      some (.DUP3, .none), some (.ADD, .none), some (.JUMPDEST, .none),
      some (.DUP1, .none), some (.MLOAD, .none), some (.PUSH0, .none),
      some (.BYTE, .none), some (.ISZERO, .none), some (.DUP8, .none),
      some (.DUP3, .none), some (.LT, .none), some (.AND, .none),
      some (.ISZERO, .none), some (.Push .PUSH2, some (⟨1625⟩, 2)),
      some (.JUMPI, .none), some (.JUMPDEST, .none), some (.DUP3, .none),
      some (.SWAP4, .none), some (.SWAP5, .none), some (.SWAP6, .none),
      some (.SWAP7, .none), some (.POP, .none), some (.SWAP2, .none),
      some (.SWAP1, .none), some (.SWAP2, .none), some (.SUB, .none),
      some (.Push .PUSH1, some (⟨31⟩, 1)), some (.NOT, .none),
      some (.DUP2, .none), some (.ADD, .none), some (.DUP1, .none),
      some (.Push .PUSH2, some (⟨1765⟩, 2)), some (.JUMPI, .none)] := by
  native_decide

private theorem barrettScanStepDecodes :
    [decode runtimeBytecode ⟨1603⟩, decode runtimeBytecode ⟨1604⟩,
      decode runtimeBytecode ⟨1605⟩, decode runtimeBytecode ⟨1606⟩,
      decode runtimeBytecode ⟨1607⟩, decode runtimeBytecode ⟨1608⟩,
      decode runtimeBytecode ⟨1609⟩, decode runtimeBytecode ⟨1610⟩,
      decode runtimeBytecode ⟨1611⟩, decode runtimeBytecode ⟨1612⟩,
      decode runtimeBytecode ⟨1613⟩, decode runtimeBytecode ⟨1614⟩,
      decode runtimeBytecode ⟨1617⟩, decode runtimeBytecode ⟨1618⟩,
      decode runtimeBytecode ⟨1620⟩, decode runtimeBytecode ⟨1621⟩,
      decode runtimeBytecode ⟨1624⟩] =
    [some (.JUMPDEST, .none), some (.DUP1, .none), some (.MLOAD, .none),
      some (.PUSH0, .none), some (.BYTE, .none), some (.ISZERO, .none),
      some (.DUP8, .none), some (.DUP3, .none), some (.LT, .none),
      some (.AND, .none), some (.ISZERO, .none),
      some (.Push .PUSH2, some (⟨1625⟩, 2)), some (.JUMPI, .none),
      some (.Push .PUSH1, some (⟨1⟩, 1)), some (.ADD, .none),
      some (.Push .PUSH2, some (⟨1603⟩, 2)), some (.JUMP, .none)] := by
  native_decide

private theorem jumpDest_1625_barrett :
    (D_J runtimeBytecode 0).contains ⟨1625⟩ = true := by native_decide

private theorem jumpDest_1603_barrett :
    (D_J runtimeBytecode 0).contains ⟨1603⟩ = true := by native_decide

private theorem barrettWordDispatchDecodesA :
    [decode runtimeBytecode ⟨1646⟩, decode runtimeBytecode ⟨1647⟩,
      decode runtimeBytecode ⟨1648⟩, decode runtimeBytecode ⟨1651⟩,
      decode runtimeBytecode ⟨1654⟩, decode runtimeBytecode ⟨1655⟩,
      decode runtimeBytecode ⟨1658⟩,
      decode runtimeBytecode ⟨1309⟩, decode runtimeBytecode ⟨1310⟩,
      decode runtimeBytecode ⟨1311⟩, decode runtimeBytecode ⟨1313⟩,
      decode runtimeBytecode ⟨1314⟩, decode runtimeBytecode ⟨1315⟩,
      decode runtimeBytecode ⟨1316⟩, decode runtimeBytecode ⟨1317⟩,
      decode runtimeBytecode ⟨1318⟩, decode runtimeBytecode ⟨1321⟩,
      decode runtimeBytecode ⟨1322⟩] =
    [some (.POP, .none), some (.POP, .none),
      some (.Push .PUSH2, some (⟨1665⟩, 2)),
      some (.Push .PUSH2, some (⟨1659⟩, 2)), some (.DUP5, .none),
      some (.Push .PUSH2, some (⟨1309⟩, 2)), some (.JUMP, .none),
      some (.JUMPDEST, .none), some (.SWAP1, .none),
      some (.Push .PUSH1, some (⟨31⟩, 1)), some (.DUP3, .none),
      some (.ADD, .none), some (.DUP1, .none), some (.SWAP3, .none),
      some (.GT, .none), some (.Push .PUSH2, some (⟨1037⟩, 2)),
      some (.JUMPI, .none), some (.JUMP, .none)] := by
  native_decide

private theorem barrettWordDispatchDecodesB :
    [decode runtimeBytecode ⟨1659⟩, decode runtimeBytecode ⟨1660⟩,
      decode runtimeBytecode ⟨1662⟩, decode runtimeBytecode ⟨1663⟩,
      decode runtimeBytecode ⟨1664⟩,
      decode runtimeBytecode ⟨1665⟩, decode runtimeBytecode ⟨1666⟩,
      decode runtimeBytecode ⟨1667⟩, decode runtimeBytecode ⟨1669⟩,
      decode runtimeBytecode ⟨1670⟩, decode runtimeBytecode ⟨1671⟩,
      decode runtimeBytecode ⟨1674⟩] =
    [some (.JUMPDEST, .none), some (.Push .PUSH1, some (⟨5⟩, 1)),
      some (.SHR, .none), some (.SWAP1, .none), some (.JUMP, .none),
      some (.JUMPDEST, .none), some (.SWAP2, .none),
      some (.Push .PUSH1, some (⟨1⟩, 1)), some (.DUP4, .none),
      some (.EQ, .none), some (.Push .PUSH2, some (⟨1750⟩, 2)),
      some (.JUMPI, .none)] := by
  native_decide

private theorem barrettWordCallDecodes :
    [decode runtimeBytecode ⟨1750⟩, decode runtimeBytecode ⟨1751⟩,
      decode runtimeBytecode ⟨1752⟩, decode runtimeBytecode ⟨1753⟩,
      decode runtimeBytecode ⟨1754⟩, decode runtimeBytecode ⟨1755⟩,
      decode runtimeBytecode ⟨1756⟩, decode runtimeBytecode ⟨1759⟩,
      decode runtimeBytecode ⟨1760⟩, decode runtimeBytecode ⟨1761⟩,
      decode runtimeBytecode ⟨1764⟩] =
    [some (.JUMPDEST, .none), some (.SWAP2, .none), some (.POP, .none),
      some (.DUP5, .none), some (.SWAP3, .none), some (.POP, .none),
      some (.Push .PUSH2, some (⟨1271⟩, 2)), some (.SWAP4, .none),
      some (.SWAP6, .none), some (.Push .PUSH2, some (⟨2574⟩, 2)),
      some (.JUMP, .none)] := by
  native_decide

private theorem jumpDest_1309_barrett :
    (D_J runtimeBytecode 0).contains ⟨1309⟩ = true := by native_decide
private theorem jumpDest_1659_barrett :
    (D_J runtimeBytecode 0).contains ⟨1659⟩ = true := by native_decide
private theorem jumpDest_1665_barrett :
    (D_J runtimeBytecode 0).contains ⟨1665⟩ = true := by native_decide
private theorem jumpDest_1750_barrett :
    (D_J runtimeBytecode 0).contains ⟨1750⟩ = true := by native_decide
private theorem jumpDest_2574_barrett :
    (D_J runtimeBytecode 0).contains ⟨2574⟩ = true := by native_decide

private theorem barrettReturnDecodes :
    [decode runtimeBytecode ⟨1271⟩, decode runtimeBytecode ⟨1272⟩,
      decode runtimeBytecode ⟨1273⟩] =
    [some (.JUMPDEST, .none), some (.SWAP1, .none), some (.JUMP, .none)] := by
  native_decide

private theorem jumpDest_1271_barrett :
    (D_J runtimeBytecode 0).contains ⟨1271⟩ = true := by native_decide

private theorem checkedSub1103Decodes :
    [decode runtimeBytecode ⟨1103⟩, decode runtimeBytecode ⟨1104⟩,
      decode runtimeBytecode ⟨1105⟩, decode runtimeBytecode ⟨1106⟩,
      decode runtimeBytecode ⟨1107⟩, decode runtimeBytecode ⟨1108⟩,
      decode runtimeBytecode ⟨1109⟩, decode runtimeBytecode ⟨1110⟩,
      decode runtimeBytecode ⟨1111⟩, decode runtimeBytecode ⟨1114⟩,
      decode runtimeBytecode ⟨1115⟩] =
    [some (.JUMPDEST, .none), some (.SWAP2, .none), some (.SWAP1, .none),
      some (.DUP3, .none), some (.SUB, .none), some (.SWAP2, .none),
      some (.DUP3, .none), some (.GT, .none),
      some (.Push .PUSH2, some (⟨1037⟩, 2)), some (.JUMPI, .none),
      some (.JUMP, .none)] := by
  native_decide

/-- Exact success path for the compiler's checked subtraction helper at PC 1103.

The helper enters with stack `[x, y, ret, …]`, checks that `x - y` did not underflow,
and returns to `ret` with `[x - y, …]`. -/
theorem reachCheckedSub1103Exact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {x y ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hle : y ≤ x) (hxWord : x < UInt256.size)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (htail : tail.length ≤ 1013)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1103⟩
      (UInt256.ofNat x :: UInt256.ofNat y :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat ret)
      (UInt256.ofNat (x - y) :: tail) mem aw rdata acc (k + 11) (C + 43) := by
  have hd := checkedSub1103Decodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
  have hyWord : y < UInt256.size := by omega
  have hxyWord : x - y < UInt256.size := by omega
  have hsub : UInt256.sub (UInt256.ofNat x) (UInt256.ofNat y) =
      UInt256.ofNat (x - y) := by
    apply u256_inj
    rw [usub_toNat]
    · rw [UInt256.toNat_ofNat_of_lt hxWord, UInt256.toNat_ofNat_of_lt hyWord,
        UInt256.toNat_ofNat_of_lt hxyWord]
    · rw [UInt256.toNat_ofNat_of_lt hxWord, UInt256.toNat_ofNat_of_lt hyWord]
      exact hle
  have hgt : UInt256.gt (UInt256.ofNat (x - y)) (UInt256.ofNat x) = ⟨0⟩ := by
    apply ugt_zero
    rw [UInt256.toNat_ofNat_of_lt hxyWord, UInt256.toNat_ofNat_of_lt hxWord]
    omega
  have rd1114raw := evm_run rd0 with [known jumpdest h0, known swap2 h1,
    known swap1 h2, known dup3 h3, known sub h4, known swap2 h5, known dup3 h6,
    known gt h7, known push2 h8 ⟨1037⟩]
  rw [hsub, hgt] at rd1114raw
  have rd1115 := rd1114raw.jumpiNT h9 (by native_decide) (by evm_ov)
  have rdret := rd1115.jump h10 hret (by evm_ov)
  exact rdret.withIndices (by omega) (by omega)

private theorem jumpDest_1103_barrett :
    (D_J runtimeBytecode 0).contains ⟨1103⟩ = true := by native_decide

private theorem jumpDest_1784_barrett :
    (D_J runtimeBytecode 0).contains ⟨1784⟩ = true := by native_decide

private theorem jumpDest_1796_barrett :
    (D_J runtimeBytecode 0).contains ⟨1796⟩ = true := by native_decide

private theorem jumpDest_1549_barrett :
    (D_J runtimeBytecode 0).contains ⟨1549⟩ = true := by native_decide

private theorem jumpDest_1570_barrett :
    (D_J runtimeBytecode 0).contains ⟨1570⟩ = true := by native_decide

private theorem jumpDest_1765_barrett :
    (D_J runtimeBytecode 0).contains ⟨1765⟩ = true := by native_decide

private theorem jumpDest_1808_barrett :
    (D_J runtimeBytecode 0).contains ⟨1808⟩ = true := by native_decide

private theorem barrettNormalizeEntryDecodes :
    [decode runtimeBytecode ⟨1765⟩, decode runtimeBytecode ⟨1766⟩,
      decode runtimeBytecode ⟨1769⟩, decode runtimeBytecode ⟨1770⟩,
      decode runtimeBytecode ⟨1773⟩, decode runtimeBytecode ⟨1774⟩,
      decode runtimeBytecode ⟨1775⟩, decode runtimeBytecode ⟨1776⟩,
      decode runtimeBytecode ⟨1777⟩, decode runtimeBytecode ⟨1778⟩,
      decode runtimeBytecode ⟨1779⟩, decode runtimeBytecode ⟨1780⟩,
      decode runtimeBytecode ⟨1783⟩,
      decode runtimeBytecode ⟨1784⟩, decode runtimeBytecode ⟨1785⟩,
      decode runtimeBytecode ⟨1786⟩, decode runtimeBytecode ⟨1787⟩,
      decode runtimeBytecode ⟨1788⟩, decode runtimeBytecode ⟨1791⟩,
      decode runtimeBytecode ⟨1792⟩, decode runtimeBytecode ⟨1795⟩] =
    [some (.JUMPDEST, .none), some (.Push .PUSH2, some (⟨1784⟩, 2)),
      some (.SWAP1, .none), some (.Push .PUSH2, some (⟨1808⟩, 2)),
      some (.SWAP5, .none), some (.SWAP4, .none), some (.SWAP3, .none),
      some (.SWAP6, .none), some (.SWAP9, .none), some (.SWAP7, .none),
      some (.SWAP9, .none), some (.Push .PUSH2, some (⟨1103⟩, 2)),
      some (.JUMP, .none),
      some (.JUMPDEST, .none), some (.SWAP5, .none), some (.DUP6, .none),
      some (.DUP6, .none), some (.Push .PUSH2, some (⟨1796⟩, 2)),
      some (.DUP3, .none), some (.Push .PUSH2, some (⟨581⟩, 2)),
      some (.JUMP, .none)] := by
  native_decide

private theorem barrettNormalizeCopyDecodes :
    [decode runtimeBytecode ⟨1796⟩, decode runtimeBytecode ⟨1797⟩,
      decode runtimeBytecode ⟨1798⟩, decode runtimeBytecode ⟨1799⟩,
      decode runtimeBytecode ⟨1801⟩, decode runtimeBytecode ⟨1802⟩,
      decode runtimeBytecode ⟨1803⟩, decode runtimeBytecode ⟨1804⟩,
      decode runtimeBytecode ⟨1807⟩] =
    [some (.JUMPDEST, .none), some (.SWAP5, .none), some (.ADD, .none),
      some (.Push .PUSH1, some (⟨32⟩, 1)), some (.DUP6, .none),
      some (.ADD, .none), some (.MCOPY, .none),
      some (.Push .PUSH2, some (⟨1549⟩, 2)), some (.JUMP, .none)] := by
  native_decide

private theorem barrettRestoreDecodes :
    [decode runtimeBytecode ⟨1808⟩, decode runtimeBytecode ⟨1809⟩,
      decode runtimeBytecode ⟨1811⟩, decode runtimeBytecode ⟨1812⟩,
      decode runtimeBytecode ⟨1813⟩, decode runtimeBytecode ⟨1814⟩,
      decode runtimeBytecode ⟨1815⟩, decode runtimeBytecode ⟨1816⟩,
      decode runtimeBytecode ⟨1817⟩] =
    [some (.JUMPDEST, .none), some (.Push .PUSH1, some (⟨32⟩, 1)),
      some (.ADD, .none), some (.SWAP1, .none), some (.DUP4, .none),
      some (.ADD, .none), some (.MCOPY, .none), some (.SWAP1, .none),
      some (.JUMP, .none)] := by
  native_decide

private theorem barrettEntryGenericDecodes :
    [decode runtimeBytecode ⟨1549⟩, decode runtimeBytecode ⟨1550⟩,
      decode runtimeBytecode ⟨1551⟩, decode runtimeBytecode ⟨1552⟩,
      decode runtimeBytecode ⟨1553⟩, decode runtimeBytecode ⟨1554⟩,
      decode runtimeBytecode ⟨1555⟩, decode runtimeBytecode ⟨1556⟩,
      decode runtimeBytecode ⟨1557⟩, decode runtimeBytecode ⟨1558⟩,
      decode runtimeBytecode ⟨1561⟩, decode runtimeBytecode ⟨1562⟩,
      decode runtimeBytecode ⟨1565⟩, decode runtimeBytecode ⟨1566⟩,
      decode runtimeBytecode ⟨1569⟩] =
    [some (.JUMPDEST, .none), some (.SWAP3, .none), some (.SWAP2, .none),
      some (.SWAP1, .none), some (.SWAP2, .none), some (.DUP2, .none),
      some (.MLOAD, .none), some (.DUP1, .none), some (.ISZERO, .none),
      some (.Push .PUSH2, some (⟨1842⟩, 2)), some (.JUMPI, .none),
      some (.Push .PUSH2, some (⟨1570⟩, 2)), some (.DUP2, .none),
      some (.Push .PUSH2, some (⟨581⟩, 2)), some (.JUMP, .none)] := by
  native_decide

def barrettNormalizedMemory (mem : ByteArray) (fp p offset len : Nat) : ByteArray :=
  let mem1 := storeBytesLength (setFreePtr mem (fp + bytesAllocationSize len)) fp len
  mem1.write (p + offset) mem1 (fp + 32) len

def barrettNormalizeCopyWords (aw : UInt256) (fp p offset len : Nat) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (newBytesWords aw fp len).toNat (max (fp + 32) (p + offset)) len)

def barrettNormalizeCopyExpansionGas (aw : UInt256) (fp p offset len : Nat) : Nat :=
  Cₘ (barrettNormalizeCopyWords aw fp p offset len) - Cₘ (newBytesWords aw fp len)

def barrettNormalizeCopyGas (aw : UInt256) (fp p offset len : Nat) : Nat :=
  barrettNormalizeCopyExpansionGas aw fp p offset len +
    GasConstants.Gverylow + GasConstants.Gcopy * ((len + 31) / 32)

def barrettNormalizeGas (aw : UInt256) (fp p offset len : Nat) : Nat :=
  139 + newBytesGas aw fp len + barrettNormalizeCopyGas aw fp p offset len

def barrettRestoreMemory (mem : ByteArray) (temp result offset len : Nat) : ByteArray :=
  mem.write (temp + 32) mem (result + offset) len

def barrettRestoreWords (aw : UInt256) (temp result offset len : Nat) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat (max (result + offset) (temp + 32)) len)

def barrettRestoreExpansionGas (aw : UInt256) (temp result offset len : Nat) : Nat :=
  Cₘ (barrettRestoreWords aw temp result offset len) - Cₘ aw

def barrettRestoreGas (aw : UInt256) (temp result offset len : Nat) : Nat :=
  27 + barrettRestoreExpansionGas aw temp result offset len +
    GasConstants.Gverylow + GasConstants.Gcopy * ((len + 31) / 32)

/-! ### Generic Barrett re-entry allocation

The dispatcher-level allocation theorem is specialized to the original operand layout.  The
normalization path re-enters PC 1549 with a freshly allocated modulus pointer, so it needs the same
bytecode fact stated only in terms of the current cursor's pointers, memory, and free pointer.
-/

/-- Allocate Barrett's result array from a generic PC 1549 entry.

Starting stack convention at PC 1549:
`[basePtr, exponentPtr, modulusPtr, ret, tail...]`.

The code reads `modulusPtr.length`, allocates `new bytes(length)` at `fp`, and reaches PC 1570 with
stack `[resultPtr, length, ret, modulusPtr, exponentPtr, basePtr, tail...]`. -/
theorem allocateBarrettResultExactGeneric
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {basePtr exponentPtr modulusPtr ret fp modulusSize : Nat}
    {tail : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 1024)
    (hmodAccess : (UInt256.ofNat modulusPtr).toNat + 32 ≤ 32 * aw.toNat)
    (hlength :
      wideLoadWord mem aw (UInt256.ofNat modulusPtr) = UInt256.ofNat modulusSize)
    (hfp : 96 ≤ fp)
    (hbound : fp + bytesAllocationSize modulusSize < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (htail : tail.length ≤ 1007)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1549⟩
      (UInt256.ofNat basePtr :: UInt256.ofNat exponentPtr ::
        UInt256.ofNat modulusPtr :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1570⟩
      (UInt256.ofNat fp :: UInt256.ofNat modulusSize :: UInt256.ofNat ret ::
        UInt256.ofNat modulusPtr :: UInt256.ofNat exponentPtr ::
        UInt256.ofNat basePtr :: tail)
      (storeBytesLength (setFreePtr mem (fp + bytesAllocationSize modulusSize))
        fp modulusSize)
      (newBytesWords aw fp modulusSize)
      rdata acc (k + 99)
      (C + 55 + newBytesGas aw fp modulusSize) := by
  have hd := barrettEntryGenericDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14⟩
  have rd1555 := evm_run rd0 with [known jumpdest h0, known swap3 h1,
    known swap2 h2, known swap1 h3, known swap2 h4, known dup2 h5]
  have rd1556 := RDx.mloadWithin rd1555 h6 hmodAccess
    (by simp only [List.length_cons]; omega)
  rw [hlength] at rd1556
  have hmodWord : modulusSize < UInt256.size :=
    lt_trans (lt_of_le_of_lt hm (by decide : 1024 < 2 ^ 64)) (by decide)
  have hmodNe : UInt256.ofNat modulusSize ≠ ⟨0⟩ := by
    intro hz
    have hzNat := congrArg UInt256.toNat hz
    rw [UInt256.toNat_ofNat_of_lt hmodWord] at hzNat
    simp at hzNat
    omega
  have rd581 := evm_run rd1556 with [known dup1 h7, known iszero h8,
    known push2 h9 ⟨1842⟩, known jumpiNT h10 (isZero_eq_zero_of_ne hmodNe),
    known push2 h11 ⟨1570⟩, known dup2 h12,
    known push2 h13 ⟨581⟩, known jump h14 jumpDest_581]
  have rd1570 := newBytesExact hm hfp hbound hmemSize hmemLe hgap
    haw3 haw64 hread hcalldata (by simp only [List.length_cons]; omega)
    jumpDest_1570_barrett rd581
  exact rd1570.withIndices (by omega) (by omega)

def barrettScanByteAt (mem : ByteArray) (aw : UInt256) (cur : Nat) : UInt256 :=
  UInt256.byteAt ⟨0⟩ (wideLoadWord mem aw (UInt256.ofNat cur))

def barrettScanStopAt (mem : ByteArray) (aw : UInt256) (end_ cur : Nat) : Nat :=
  if h : cur < end_ then
    if barrettScanByteAt mem aw cur = ⟨0⟩ then
      barrettScanStopAt mem aw end_ (cur + 1)
    else cur
  else cur
termination_by end_ - cur
decreasing_by omega

def barrettScanZeroStepsAt (mem : ByteArray) (aw : UInt256) (end_ cur : Nat) : Nat :=
  if h : cur < end_ then
    if barrettScanByteAt mem aw cur = ⟨0⟩ then
      1 + barrettScanZeroStepsAt mem aw end_ (cur + 1)
    else 0
  else 0
termination_by end_ - cur
decreasing_by omega

def barrettScanStepsAt (mem : ByteArray) (aw : UInt256) (end_ cur : Nat) : Nat :=
  17 * barrettScanZeroStepsAt mem aw end_ cur

def barrettScanGasAt (mem : ByteArray) (aw : UInt256) (end_ cur : Nat) : Nat :=
  60 * barrettScanZeroStepsAt mem aw end_ cur

/-- Bounds for the byte-wise Barrett scan: the computed stop point stays in the closed interval
`[cur, end_]`. -/
theorem barrettScanStopAt_bounds (mem : ByteArray) (aw : UInt256)
    (end_ cur : Nat) (hcur : cur ≤ end_) :
    cur ≤ barrettScanStopAt mem aw end_ cur ∧
      barrettScanStopAt mem aw end_ cur ≤ end_ := by
  by_cases hlt : cur < end_
  · by_cases hz : barrettScanByteAt mem aw cur = ⟨0⟩
    · rw [barrettScanStopAt, dif_pos hlt, if_pos hz]
      have ih := barrettScanStopAt_bounds mem aw end_ (cur + 1) (by omega)
      omega
    · rw [barrettScanStopAt, dif_pos hlt, if_neg hz]
      exact ⟨le_rfl, hcur⟩
  · rw [barrettScanStopAt, dif_neg hlt]
    exact ⟨le_rfl, hcur⟩
termination_by end_ - cur
decreasing_by omega

/-- The scan stop is either the end sentinel or a nonzero byte. -/
theorem barrettScanStopAt_stop (mem : ByteArray) (aw : UInt256)
    (end_ cur : Nat) :
    end_ ≤ barrettScanStopAt mem aw end_ cur ∨
      barrettScanByteAt mem aw (barrettScanStopAt mem aw end_ cur) ≠ ⟨0⟩ := by
  by_cases hlt : cur < end_
  · by_cases hz : barrettScanByteAt mem aw cur = ⟨0⟩
    · rw [barrettScanStopAt, dif_pos hlt, if_pos hz]
      exact barrettScanStopAt_stop mem aw end_ (cur + 1)
    · rw [barrettScanStopAt, dif_pos hlt, if_neg hz]
      exact Or.inr hz
  · rw [barrettScanStopAt, dif_neg hlt]
    exact Or.inl (Nat.le_of_not_gt hlt)
termination_by end_ - cur
decreasing_by omega

/-- Every byte strictly before the computed scan stop, inside the scanned interval, was zero. -/
theorem barrettScanStopAt_zero_before (mem : ByteArray) (aw : UInt256)
    (end_ cur i : Nat) (hcur : cur ≤ i)
    (hi : i < barrettScanStopAt mem aw end_ cur) :
    barrettScanByteAt mem aw i = ⟨0⟩ := by
  by_cases hlt : cur < end_
  · by_cases hz : barrettScanByteAt mem aw cur = ⟨0⟩
    · rw [barrettScanStopAt, dif_pos hlt, if_pos hz] at hi
      by_cases hci : i = cur
      · subst i
        exact hz
      · have hnext : cur + 1 ≤ i := by omega
        exact barrettScanStopAt_zero_before mem aw end_ (cur + 1) i hnext hi
    · rw [barrettScanStopAt, dif_pos hlt, if_neg hz] at hi
      omega
  · rw [barrettScanStopAt, dif_neg hlt] at hi
    omega
termination_by end_ - cur
decreasing_by omega

def barrettScanStart (p : Nat) : Nat := p + 32

def barrettScanEnd (p m : Nat) : Nat := p + m + 31

def barrettScanStop (mem : ByteArray) (aw : UInt256) (p m : Nat) : Nat :=
  barrettScanStopAt mem aw (barrettScanEnd p m) (barrettScanStart p)

def barrettScanNormalizeSteps (mem : ByteArray) (aw : UInt256) (p m : Nat) : Nat :=
  9 + barrettScanStepsAt mem aw (barrettScanEnd p m) (barrettScanStart p) + 31

def barrettScanNormalizeExitGas (mem : ByteArray) (aw : UInt256) (p m : Nat) : Nat :=
  27 + barrettScanGasAt mem aw (barrettScanEnd p m) (barrettScanStart p) + 101

def barrettScanNormalizeReentrySteps (mem : ByteArray) (aw : UInt256) (p m : Nat) : Nat :=
  barrettScanNormalizeSteps mem aw p m + 125

def barrettScanNormalizeReentryGas
    (mem : ByteArray) (aw : UInt256) (fp p m : Nat) : Nat :=
  let stop := barrettScanStop mem aw p m
  barrettScanNormalizeExitGas mem aw p m +
    barrettNormalizeGas aw fp p (stop - p) (m - (stop - p - 32))

def barrettNormalizedOffset (mem : ByteArray) (aw : UInt256) (p m : Nat) : Nat :=
  barrettScanStop mem aw p m - p

def barrettNormalizedLen (mem : ByteArray) (aw : UInt256) (p m : Nat) : Nat :=
  m - (barrettNormalizedOffset mem aw p m - 32)

/-- The normalized offset skips a prefix whose length plus the normalized suffix length is exactly
the original modulus length. -/
theorem barrettNormalizedSkippedPrefix_add_len
    (mem : ByteArray) (aw : UInt256) (p m : Nat) (hm : 0 < m) :
    (barrettNormalizedOffset mem aw p m - 32) +
      barrettNormalizedLen mem aw p m = m := by
  have hstartLeEnd : barrettScanStart p ≤ barrettScanEnd p m := by
    unfold barrettScanStart barrettScanEnd
    omega
  have hbounds := barrettScanStopAt_bounds mem aw
    (barrettScanEnd p m) (barrettScanStart p) hstartLeEnd
  have hstopLower : barrettScanStart p ≤ barrettScanStop mem aw p m := by
    simpa [barrettScanStop] using hbounds.1
  have hstopUpper : barrettScanStop mem aw p m ≤ barrettScanEnd p m := by
    simpa [barrettScanStop] using hbounds.2
  have hoffsetGe : 32 ≤ barrettNormalizedOffset mem aw p m := by
    change 32 ≤ barrettScanStop mem aw p m - p
    unfold barrettScanStart at hstopLower
    omega
  have hoffsetLe : barrettNormalizedOffset mem aw p m ≤ m + 31 := by
    change barrettScanStop mem aw p m - p ≤ m + 31
    unfold barrettScanEnd at hstopUpper
    omega
  unfold barrettNormalizedLen
  omega

def barrettNormalizedMem (mem : ByteArray) (aw : UInt256) (fp p m : Nat) : ByteArray :=
  barrettNormalizedMemory mem fp p (barrettNormalizedOffset mem aw p m)
    (barrettNormalizedLen mem aw p m)

def barrettNormalizedAw (aw : UInt256) (mem : ByteArray) (fp p m : Nat) : UInt256 :=
  barrettNormalizeCopyWords aw fp p (barrettNormalizedOffset mem aw p m)
    (barrettNormalizedLen mem aw p m)

def barrettNormalizedResultMem (mem : ByteArray) (aw : UInt256)
    (fp p m resultFp : Nat) : ByteArray :=
  storeBytesLength
    (setFreePtr (barrettNormalizedMem mem aw fp p m)
      (resultFp + bytesAllocationSize (barrettNormalizedLen mem aw p m)))
    resultFp (barrettNormalizedLen mem aw p m)

def barrettNormalizedResultAw (mem : ByteArray) (aw : UInt256)
    (fp p m resultFp : Nat) : UInt256 :=
  newBytesWords (barrettNormalizedAw aw mem fp p m) resultFp
    (barrettNormalizedLen mem aw p m)

def barrettNormalizeReentryChecksGas (mem : ByteArray) (aw : UInt256)
    (fp p m resultFp : Nat) : Nat :=
  barrettScanNormalizeReentryGas mem aw fp p m +
    55 + newBytesGas (barrettNormalizedAw aw mem fp p m) resultFp
      (barrettNormalizedLen mem aw p m) +
    wideWordChecksGas (barrettNormalizedResultMem mem aw fp p m resultFp)
      (barrettNormalizedResultAw mem aw fp p m resultFp) fp
      (barrettNormalizedLen mem aw p m)

def barrettNormalizeWordRestoreGas (mem : ByteArray) (aw : UInt256)
    (fp p m resultFp result baseSize exponentSize : Nat) : Nat :=
  barrettNormalizeReentryChecksGas mem aw fp p m resultFp +
    128 + 145 +
    wideWordHelperGasAt (barrettNormalizedResultMem mem aw fp p m resultFp)
      (barrettNormalizedResultAw mem aw fp p m resultFp)
      baseSize exponentSize (barrettNormalizedLen mem aw p m) +
    12 +
    barrettRestoreGas (barrettNormalizedResultAw mem aw fp p m resultFp)
      resultFp result (barrettNormalizedOffset mem aw p m)
      (barrettNormalizedLen mem aw p m)

/-- Exact normalization block for Barrett's leading-zero path.

Starting at PC 1765 with `delta = offset - 32`, the bytecode computes the shortened
modulus length `m - delta`, allocates a fresh bytes array at `fp`, copies the significant
suffix from `p + offset`, and re-enters Barrett at PC 1549 with an internal return to PC 1808.
This theorem intentionally stops at the re-entry point; the recursive normalized Barrett call and
the PC 1808 restoration suffix are separate obligations. -/
theorem reachBarrettNormalizeTo1549
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {delta offset exp p m retBar result base ret fp : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hdeltaLe : delta ≤ m) (hm : m ≤ 1024)
    (hfp : 96 ≤ fp) (hbound : fp + bytesAllocationSize (m - delta) < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hpOffsetWord : p + offset < UInt256.size)
    (hfp32Word : fp + 32 < UInt256.size)
    (htail : tail.length ≤ 1003)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1765⟩
      (UInt256.ofNat delta :: UInt256.ofNat offset :: UInt256.ofNat exp ::
        UInt256.ofNat p :: UInt256.ofNat m :: UInt256.ofNat retBar ::
        UInt256.ofNat result :: UInt256.ofNat base :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1549⟩
      (UInt256.ofNat base :: UInt256.ofNat exp :: UInt256.ofNat fp :: ⟨1808⟩ ::
        UInt256.ofNat offset :: UInt256.ofNat (m - delta) ::
        UInt256.ofNat result :: UInt256.ofNat retBar :: UInt256.ofNat ret :: tail)
      (barrettNormalizedMemory mem fp p offset (m - delta))
      (barrettNormalizeCopyWords aw fp p offset (m - delta))
      rdata acc (k + 125)
      (C + barrettNormalizeGas aw fp p offset (m - delta)) := by
  have hd := barrettNormalizeEntryDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with
    ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,
      h13,h14,h15,h16,h17,h18,h19,h20⟩
  have rd1103raw := evm_run rd0 with [known jumpdest h0,
    known push2 h1 ⟨1784⟩, known swap1 h2, known push2 h3 ⟨1808⟩,
    known swap5 h4, known swap4 h5, known swap3 h6, known swap6 h7,
    known swap9 h8, known swap7 h9, known swap9 h10,
    known push2 h11 ⟨1103⟩, known jump h12 jumpDest_1103_barrett]
  have rd1103 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1103⟩
      (UInt256.ofNat m :: UInt256.ofNat delta :: ⟨1784⟩ ::
        UInt256.ofNat exp :: UInt256.ofNat p :: ⟨1808⟩ ::
        UInt256.ofNat offset :: UInt256.ofNat base :: UInt256.ofNat result ::
        UInt256.ofNat retBar :: UInt256.ofNat ret :: tail)
      mem aw rdata acc (k + 13) (C + 42) :=
    (rd1103raw.withPC (by native_decide)).withIndices (by omega) (by omega)
  have hmWord : m < UInt256.size := lt_of_le_of_lt hm (by decide)
  have rd1784 := reachCheckedSub1103Exact
    (x := m) (y := delta) (ret := 1784)
    hdeltaLe hmWord jumpDest_1784_barrett (by simp only [List.length_cons]; omega) rd1103
  have rd581raw := evm_run rd1784 with [known jumpdest h13, known swap5 h14,
    known dup6 h15, known dup6 h16, known push2 h17 ⟨1796⟩,
    known dup3 h18, known push2 h19 ⟨581⟩, known jump h20 jumpDest_581]
  have rd581 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨581⟩
      (UInt256.ofNat (m - delta) :: ⟨1796⟩ ::
        UInt256.ofNat offset :: UInt256.ofNat (m - delta) ::
        UInt256.ofNat base :: UInt256.ofNat exp :: UInt256.ofNat p ::
        ⟨1808⟩ :: UInt256.ofNat offset :: UInt256.ofNat (m - delta) ::
        UInt256.ofNat result :: UInt256.ofNat retBar :: UInt256.ofNat ret :: tail)
      mem aw rdata acc (k + 32) (C + 112) :=
    (rd581raw.withPC (by native_decide)).withIndices (by omega) (by omega)
  have hlenLe : m - delta ≤ 1024 := by omega
  have rd1796raw := newBytesExact
    (n := m - delta) (fp := fp) (ret := 1796)
    hlenLe hfp hbound hmemSize hmemLe hgap haw3 haw64 hread hcalldata
    (by simp only [List.length_cons]; omega) jumpDest_1796_barrett rd581
  have hcopy := barrettNormalizeCopyDecodes
  simp only [List.cons.injEq, and_true] at hcopy
  rcases hcopy with ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8⟩
  have rd1803raw := evm_run rd1796raw with [known jumpdest c0, known swap5 c1,
    known add c2, known push1 c3 ⟨32⟩, known dup6 c4, known add c5]
  have hpWord : p < UInt256.size := by omega
  have hoffsetWord : offset < UInt256.size := by omega
  have hsrc :
      UInt256.ofNat p + UInt256.ofNat offset = UInt256.ofNat (p + offset) :=
    ofNat_add_bounded hpOffsetWord
  have hfpWord : fp < UInt256.size := by omega
  have hdst : UInt256.ofNat fp + ⟨32⟩ = UInt256.ofNat (fp + 32) := by
    simpa using (ofNat_add_bounded (a := fp) (b := 32) hfp32Word)
  rw [hsrc, hdst] at rd1803raw
  have hsrcNat : (UInt256.ofNat (p + offset)).toNat = p + offset :=
    UInt256.toNat_ofNat_of_lt hpOffsetWord
  have hdstNat : (UInt256.ofNat (fp + 32)).toNat = fp + 32 :=
    UInt256.toNat_ofNat_of_lt hfp32Word
  have hlenWord : m - delta < UInt256.size := by omega
  have hlenNat : (UInt256.ofNat (m - delta)).toNat = m - delta :=
    UInt256.toNat_ofNat_of_lt hlenWord
  have rd1804 := RDx.mcopy
    (barrettNormalizeCopyExpansionGas aw fp p offset (m - delta))
    (barrettNormalizedMemory mem fp p offset (m - delta))
    (barrettNormalizeCopyWords aw fp p offset (m - delta)) rd1803raw c6
    (by
      intro s hsaw hstk
      simp [barrettNormalizeCopyExpansionGas, barrettNormalizeCopyWords,
        memoryExpansionCost, memoryExpansionCost.μᵢ', hsaw, hstk, hsrcNat, hdstNat]
      rw [hlenNat])
    (by
      simp [barrettNormalizedMemory, hsrcNat, hdstNat]
      rw [hlenNat])
    (by
      simp [barrettNormalizeCopyWords, hsrcNat, hdstNat]
      rw [hlenNat])
    (by simp only [List.length_cons]; omega)
  have rd1549raw := evm_run rd1804 with [known push2 c7 ⟨1549⟩,
    known jump c8 jumpDest_1549_barrett]
  exact (rd1549raw.withPC (by native_decide)).withIndices (by omega) (by
    unfold barrettNormalizeGas barrettNormalizeCopyGas
    simp only [GasConstants.Gverylow, GasConstants.Gcopy]
    rw [hlenNat]
    omega)

/-- One recursive iteration of Barrett's leading-zero scan.  If `cur < end` and the current
byte is zero, the loop advances to `cur + 1` with exact gas and unchanged memory. -/
theorem reachBarrettScanZeroStep
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {cur end_ p m retBar result exp base ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hcurEnd : cur < end_) (hbyte : UInt256.byteAt ⟨0⟩
      (wideLoadWord mem aw (UInt256.ofNat cur)) = ⟨0⟩)
    (hcurWord : cur < UInt256.size) (hendWord : end_ < UInt256.size)
    (hcurNext : cur + 1 < UInt256.size)
    (hactive : cur + 32 ≤ 32 * aw.toNat)
    (htail : tail.length ≤ 1006)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1603⟩
      (UInt256.ofNat cur :: UInt256.ofNat exp :: UInt256.ofNat p ::
        UInt256.ofNat m :: UInt256.ofNat retBar :: UInt256.ofNat result ::
        UInt256.ofNat end_ :: UInt256.ofNat base :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1603⟩
      (UInt256.ofNat (cur + 1) :: UInt256.ofNat exp :: UInt256.ofNat p ::
        UInt256.ofNat m :: UInt256.ofNat retBar :: UInt256.ofNat result ::
        UInt256.ofNat end_ :: UInt256.ofNat base :: UInt256.ofNat ret :: tail)
      mem aw rdata acc (k + 17) (C + 60) := by
  have hd := barrettScanStepDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16⟩
  have rd1605 := evm_run rd0 with [known jumpdest h0, known dup1 h1]
  have rd1606 := RDx.mloadWithin rd1605 h2 (by
    rw [UInt256.toNat_ofNat_of_lt hcurWord]
    exact hactive) (by simp only [List.length_cons]; omega)
  have rd1614 := evm_run rd1606 with [known push0 h3, known byte h4,
    known iszero h5, known dup8 h6, known dup3 h7, known lt h8,
    known and h9, known iszero h10, known push2 h11 ⟨1625⟩]
  have hlt : UInt256.lt (UInt256.ofNat cur) (UInt256.ofNat end_) = ⟨1⟩ := by
    apply ult_one
    rw [UInt256.toNat_ofNat_of_lt hcurWord, UInt256.toNat_ofNat_of_lt hendWord]
    exact hcurEnd
  have hiz : UInt256.isZero
      (UInt256.byteAt ⟨0⟩ (wideLoadWord mem aw (UInt256.ofNat cur))) = ⟨1⟩ := by
    rw [hbyte]
    native_decide
  have hcond :
      UInt256.isZero
        (UInt256.land
          (UInt256.lt (UInt256.ofNat cur) (UInt256.ofNat end_))
          (UInt256.isZero
            (UInt256.byteAt ⟨0⟩ (wideLoadWord mem aw (UInt256.ofNat cur))))) =
        ⟨0⟩ := by
    rw [hlt, hiz]
    native_decide
  have rd1618 := rd1614.jumpiNT h12 hcond (by evm_ov)
  have rd1603raw := evm_run rd1618 with [known push1 h13 ⟨1⟩, known add h14,
    known push2 h15 ⟨1603⟩, known jump h16 jumpDest_1603_barrett]
  have hcurAdd : UInt256.ofNat cur + ⟨1⟩ = UInt256.ofNat (cur + 1) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (ofNat_add_bounded (a := cur) (b := 1) hcurNext)
  have hcurAdd' : ⟨1⟩ + UInt256.ofNat cur = UInt256.ofNat (cur + 1) := by
    rw [u256_add_comm]
    exact hcurAdd
  rw [hcurAdd'] at rd1603raw
  exact (rd1603raw.withPC (by native_decide)).withIndices (by omega) (by omega)

/-- Execute all zero-byte iterations of Barrett's leading-zero scan, stopping back at the loop
head.  The final branch is deliberately not consumed here: callers can then choose the direct
exit or normalization exit theorem based on the returned stop cursor. -/
theorem reachBarrettScanZerosToStop
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {cur end_ p m retBar result exp base ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hendWord : end_ < UInt256.size)
    (hactiveEnd : end_ + 32 ≤ 32 * aw.toNat)
    (htail : tail.length ≤ 1006)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1603⟩
      (UInt256.ofNat cur :: UInt256.ofNat exp :: UInt256.ofNat p ::
        UInt256.ofNat m :: UInt256.ofNat retBar :: UInt256.ofNat result ::
        UInt256.ofNat end_ :: UInt256.ofNat base :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1603⟩
      (UInt256.ofNat (barrettScanStopAt mem aw end_ cur) ::
        UInt256.ofNat exp :: UInt256.ofNat p :: UInt256.ofNat m ::
        UInt256.ofNat retBar :: UInt256.ofNat result :: UInt256.ofNat end_ ::
        UInt256.ofNat base :: UInt256.ofNat ret :: tail)
      mem aw rdata acc (k + barrettScanStepsAt mem aw end_ cur)
        (C + barrettScanGasAt mem aw end_ cur) := by
  by_cases hlt : cur < end_
  · by_cases hz : barrettScanByteAt mem aw cur = ⟨0⟩
    · have hcurWord : cur < UInt256.size := by omega
      have hcurNext : cur + 1 < UInt256.size := by omega
      have hactive : cur + 32 ≤ 32 * aw.toNat := by omega
      have rdNext := reachBarrettScanZeroStep
        (cur := cur) (end_ := end_) (p := p) (m := m)
        (retBar := retBar) (result := result) (exp := exp)
        (base := base) (ret := ret)
        hlt (by simpa [barrettScanByteAt] using hz)
        hcurWord hendWord hcurNext hactive htail rd0
      have ih := reachBarrettScanZerosToStop
        (cur := cur + 1) (end_ := end_) (p := p) (m := m)
        (retBar := retBar) (result := result) (exp := exp)
        (base := base) (ret := ret)
        hendWord hactiveEnd htail rdNext
      have hstopEq :
          barrettScanStopAt mem aw end_ cur =
            barrettScanStopAt mem aw end_ (cur + 1) := by
        rw [barrettScanStopAt, dif_pos hlt, if_pos hz]
      have hstepsEq :
          barrettScanStepsAt mem aw end_ cur =
            17 + barrettScanStepsAt mem aw end_ (cur + 1) := by
        unfold barrettScanStepsAt
        rw [barrettScanZeroStepsAt, dif_pos hlt, if_pos hz]
        omega
      have hgasEq :
          barrettScanGasAt mem aw end_ cur =
            60 + barrettScanGasAt mem aw end_ (cur + 1) := by
        unfold barrettScanGasAt
        rw [barrettScanZeroStepsAt, dif_pos hlt, if_pos hz]
        omega
      rw [hstopEq]
      exact ih.withIndices
        (by rw [hstepsEq]; omega)
        (by rw [hgasEq]; omega)
    · have hstopEq : barrettScanStopAt mem aw end_ cur = cur := by
        rw [barrettScanStopAt, dif_pos hlt, if_neg hz]
      rw [hstopEq]
      exact rd0.withIndices
        (by
          unfold barrettScanStepsAt
          rw [barrettScanZeroStepsAt, dif_pos hlt, if_neg hz]
          omega)
        (by
          unfold barrettScanGasAt
          rw [barrettScanZeroStepsAt, dif_pos hlt, if_neg hz]
          omega)
  · have hstopEq : barrettScanStopAt mem aw end_ cur = cur := by
      rw [barrettScanStopAt, dif_neg hlt]
    rw [hstopEq]
    exact rd0.withIndices
      (by
        unfold barrettScanStepsAt
        rw [barrettScanZeroStepsAt, dif_neg hlt]
        omega)
      (by
        unfold barrettScanGasAt
        rw [barrettScanZeroStepsAt, dif_neg hlt]
        omega)
termination_by end_ - cur
decreasing_by omega

/-- Exit Barrett's leading-zero scan into the normalization block.  This is the branch where
the scan stops at an offset strictly past the first payload word boundary, so the bytecode jumps
to PC 1765 carrying both `delta = offset - 32` and `offset`. -/
theorem reachBarrettScanNormalizeExit
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {cur end_ p m retBar result exp base ret offset delta : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hcurEq : cur = p + offset) (hoffsetEq : offset = 32 + delta)
    (hdeltaPos : 0 < delta)
    (hstop : end_ ≤ cur ∨
      UInt256.byteAt ⟨0⟩ (wideLoadWord mem aw (UInt256.ofNat cur)) ≠ ⟨0⟩)
    (hpWord : p < UInt256.size) (hcurWord : cur < UInt256.size)
    (hendWord : end_ < UInt256.size)
    (hactive : cur + 32 ≤ 32 * aw.toNat)
    (htail : tail.length ≤ 1006)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1603⟩
      (UInt256.ofNat cur :: UInt256.ofNat exp :: UInt256.ofNat p ::
        UInt256.ofNat m :: UInt256.ofNat retBar :: UInt256.ofNat result ::
        UInt256.ofNat end_ :: UInt256.ofNat base :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1765⟩
      (UInt256.ofNat delta :: UInt256.ofNat offset :: UInt256.ofNat exp ::
        UInt256.ofNat p :: UInt256.ofNat m :: UInt256.ofNat retBar ::
        UInt256.ofNat result :: UInt256.ofNat base :: UInt256.ofNat ret :: tail)
      mem aw rdata acc (k + 31) (C + 101) := by
  have hd := barrettScanDirectDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨_h1592,_h1593,_h1594,_h1595,_h1597,_h1598,_h1599,_h1601,
    _h1602,h1603,h1604,h1605,h1606,h1607,h1608,h1609,h1610,h1611,h1612,
    h1613,h1614,h1617,h1625,h1626,h1627,h1628,h1629,h1630,h1631,h1632,
    h1633,h1634,h1635,h1636,h1638,h1639,h1640,h1641,h1642,h1645⟩
  have rd1605 := evm_run rd0 with [known jumpdest h1603, known dup1 h1604]
  have rd1606 := RDx.mloadWithin rd1605 h1605 (by
    rw [UInt256.toNat_ofNat_of_lt hcurWord]
    exact hactive) (by simp only [List.length_cons]; omega)
  have rd1614 := evm_run rd1606 with [known push0 h1606, known byte h1607,
    known iszero h1608, known dup8 h1609, known dup3 h1610, known lt h1611,
    known and h1612, known iszero h1613, known push2 h1614 ⟨1625⟩]
  have hcond :
      UInt256.isZero
        (UInt256.land
          (UInt256.lt (UInt256.ofNat cur) (UInt256.ofNat end_))
          (UInt256.isZero
            (UInt256.byteAt ⟨0⟩ (wideLoadWord mem aw (UInt256.ofNat cur))))) =
        ⟨1⟩ := by
    rcases hstop with hend | hbyte
    · have hlt : UInt256.lt (UInt256.ofNat cur) (UInt256.ofNat end_) = ⟨0⟩ := by
        apply ult_zero
        rw [UInt256.toNat_ofNat_of_lt hcurWord, UInt256.toNat_ofNat_of_lt hendWord]
        exact hend
      rw [hlt]
      have hland : UInt256.land ⟨0⟩
          (UInt256.isZero
            (UInt256.byteAt ⟨0⟩ (wideLoadWord mem aw (UInt256.ofNat cur)))) =
          ⟨0⟩ := by
        apply u256_inj
        rw [uland_toNat]
        simp
      rw [hland]
      native_decide
    · have hiz : UInt256.isZero
          (UInt256.byteAt ⟨0⟩ (wideLoadWord mem aw (UInt256.ofNat cur))) =
          ⟨0⟩ := isZero_eq_zero_of_ne hbyte
      rw [hiz]
      have hland : UInt256.land
          (UInt256.lt (UInt256.ofNat cur) (UInt256.ofNat end_)) ⟨0⟩ = ⟨0⟩ := by
        apply u256_inj
        rw [uland_toNat]
        simp
      rw [hland]
      native_decide
  have rd1625 := rd1614.jumpiT h1617 (by rw [hcond]; native_decide)
    jumpDest_1625_barrett (by evm_ov)
  have rd1625' : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1625⟩
      (UInt256.ofNat cur :: UInt256.ofNat exp :: UInt256.ofNat p ::
        UInt256.ofNat m :: UInt256.ofNat retBar :: UInt256.ofNat result ::
        UInt256.ofNat end_ :: UInt256.ofNat base :: UInt256.ofNat ret :: tail)
      mem aw rdata acc (k + 13) (C + 43) :=
    (rd1625.withPC (by native_decide)).withIndices (by omega) (by omega)
  have rd1636raw := evm_run rd1625' with [
    known jumpdest h1625, known dup3 h1626, known swap4 h1627, known swap5 h1628,
    known swap6 h1629, known swap7 h1630, known pop h1631, known swap2 h1632,
    known swap1 h1633, known swap2 h1634, known sub h1635]
  have hoffsetWord : offset < UInt256.size := by omega
  have hsub : UInt256.sub (UInt256.ofNat cur) (UInt256.ofNat p) =
      UInt256.ofNat offset := by
    apply u256_inj
    rw [usub_toNat]
    · rw [UInt256.toNat_ofNat_of_lt hcurWord, UInt256.toNat_ofNat_of_lt hpWord,
        UInt256.toNat_ofNat_of_lt hoffsetWord]
      omega
    · rw [UInt256.toNat_ofNat_of_lt hcurWord, UInt256.toNat_ofNat_of_lt hpWord]
      omega
  rw [hsub] at rd1636raw
  have rd1636 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1636⟩
      (UInt256.ofNat offset :: UInt256.ofNat exp :: UInt256.ofNat p ::
        UInt256.ofNat m :: UInt256.ofNat retBar :: UInt256.ofNat result ::
        UInt256.ofNat base :: UInt256.ofNat ret :: tail)
      mem aw rdata acc (k + 24) (C + 73) :=
    (rd1636raw.withPC (by native_decide)).withIndices (by omega) (by omega)
  have rd1646raw := evm_run rd1636 with [
    known push1 h1636 ⟨31⟩, known not h1638, known dup2 h1639, known add h1640,
    known dup1 h1641, known push2 h1642 ⟨1765⟩]
  have hdeltaWord : delta < UInt256.size := by omega
  have hmask : UInt256.ofNat offset + UInt256.lnot ⟨31⟩ =
      UInt256.ofNat delta := by
    apply u256_inj
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt hoffsetWord, lnot31_toNat,
      UInt256.toNat_ofNat_of_lt hdeltaWord]
    rw [hoffsetEq]
    have hsize : UInt256.size = 2 ^ 256 := by decide
    rw [hsize]
    have hsum : 32 + delta + (2 ^ 256 - 32) = delta + 2 ^ 256 := by omega
    rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt (by simpa [hsize] using hdeltaWord)]
  rw [hmask] at rd1646raw
  have hdeltaNe : UInt256.ofNat delta ≠ ⟨0⟩ := by
    intro hz
    have hzNat := congrArg UInt256.toNat hz
    rw [UInt256.toNat_ofNat_of_lt hdeltaWord] at hzNat
    simp at hzNat
    omega
  have rd1765 := rd1646raw.jumpiT h1645 hdeltaNe jumpDest_1765_barrett (by evm_ov)
  exact (rd1765.withPC (by native_decide)).withIndices (by omega) (by omega)

/-- Set up Barrett's leading-zero scan from the shared PC 1592 entry.  The loop cursor starts
at the first payload byte `p + 32`, while the end sentinel is `p + m + 31`. -/
theorem reachBarrettScanSetup
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {p m retBar result exp base ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hp32 : p + 32 < UInt256.size) (hpend : p + m + 31 < UInt256.size)
    (htail : tail.length ≤ 1006)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1592⟩
      (UInt256.ofNat p :: UInt256.ofNat m :: UInt256.ofNat retBar ::
        UInt256.ofNat result :: UInt256.ofNat exp :: UInt256.ofNat base ::
        UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1603⟩
      (UInt256.ofNat (p + 32) :: UInt256.ofNat exp :: UInt256.ofNat p ::
        UInt256.ofNat m :: UInt256.ofNat retBar :: UInt256.ofNat result ::
        UInt256.ofNat (p + m + 31) :: UInt256.ofNat base ::
        UInt256.ofNat ret :: tail)
      mem aw rdata acc (k + 9) (C + 27) := by
  have hd := barrettScanDirectDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,_h9,_h10,_h11,_h12,_h13,_h14,
    _h15,_h16,_h17,_h18,_h19,_h20,_h21,_h22,_h23,_h24,_h25,_h26,_h27,_h28,
    _h29,_h30,_h31,_h32,_h33,_h34,_h35,_h36,_h37,_h38,_h39⟩
  have hp : p < UInt256.size := by omega
  have hpm : p + m < UInt256.size := by omega
  have hp32eq : UInt256.ofNat p + ⟨32⟩ = UInt256.ofNat (p + 32) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (ofNat_add_bounded (a := p) (b := 32) hp32)
  have hpmeq : UInt256.ofNat p + UInt256.ofNat m = UInt256.ofNat (p + m) :=
    ofNat_add_bounded hpm
  have hpendEq : ⟨31⟩ + UInt256.ofNat (p + m) =
      UInt256.ofNat (p + m + 31) := by
    rw [u256_add_comm]
    simpa [Nat.add_assoc] using
      (ofNat_add_bounded (a := p + m) (b := 31) hpend)
  have rd1603raw := evm_run rd0 with [known dup2 h0, known dup2 h1,
    known add h2, known push1 h3 ⟨31⟩, known add h4, known swap5 h5,
    known push1 h6 ⟨32⟩, known dup3 h7, known add h8]
  rw [hpmeq, hpendEq, hp32eq] at rd1603raw
  exact (rd1603raw.withPC (by native_decide)).withIndices (by omega) (by omega)

/-- Combined leading-zero scan theorem for the normalization case, from Barrett's PC 1592 entry
to the PC 1765 normalization block.  The premise `p + 32 < barrettScanStop …` selects exactly
the case where at least one payload byte was skipped, so the direct one-word path is not taken. -/
theorem reachBarrettScanToNormalize
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {p m retBar result exp base ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hmodPos : 0 < m)
    (hp32 : p + 32 < UInt256.size) (hpend : p + m + 31 < UInt256.size)
    (hactiveEnd : p + m + 31 + 32 ≤ 32 * aw.toNat)
    (hnorm : p + 32 < barrettScanStop mem aw p m)
    (htail : tail.length ≤ 1006)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1592⟩
      (UInt256.ofNat p :: UInt256.ofNat m :: UInt256.ofNat retBar ::
        UInt256.ofNat result :: UInt256.ofNat exp :: UInt256.ofNat base ::
        UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1765⟩
      (UInt256.ofNat (barrettScanStop mem aw p m - p - 32) ::
        UInt256.ofNat (barrettScanStop mem aw p m - p) ::
        UInt256.ofNat exp :: UInt256.ofNat p :: UInt256.ofNat m ::
        UInt256.ofNat retBar :: UInt256.ofNat result ::
        UInt256.ofNat base :: UInt256.ofNat ret :: tail)
      mem aw rdata acc (k + barrettScanNormalizeSteps mem aw p m)
        (C + barrettScanNormalizeExitGas mem aw p m) := by
  have rd1603 := reachBarrettScanSetup
    (p := p) (m := m) (retBar := retBar) (result := result)
    (exp := exp) (base := base) (ret := ret)
    hp32 hpend htail rd0
  have hstartLeEnd : barrettScanStart p ≤ barrettScanEnd p m := by
    unfold barrettScanStart barrettScanEnd
    omega
  have rdStop := reachBarrettScanZerosToStop
    (cur := barrettScanStart p) (end_ := barrettScanEnd p m)
    (p := p) (m := m) (retBar := retBar) (result := result)
    (exp := exp) (base := base) (ret := ret)
    (by simpa [barrettScanEnd] using hpend)
    (by simpa [barrettScanEnd] using hactiveEnd)
    htail rd1603
  have hstopBounds := barrettScanStopAt_bounds mem aw
    (barrettScanEnd p m) (barrettScanStart p) hstartLeEnd
  have hstopCond := barrettScanStopAt_stop mem aw
    (barrettScanEnd p m) (barrettScanStart p)
  have hstopLower : barrettScanStart p ≤ barrettScanStop mem aw p m := by
    simpa [barrettScanStop] using hstopBounds.1
  have hstopUpper : barrettScanStop mem aw p m ≤ barrettScanEnd p m := by
    simpa [barrettScanStop] using hstopBounds.2
  have hpWord : p < UInt256.size := by omega
  have hstopWord : barrettScanStop mem aw p m < UInt256.size := by
    unfold barrettScanEnd at hstopUpper
    omega
  have hactiveStop : barrettScanStop mem aw p m + 32 ≤ 32 * aw.toNat := by
    unfold barrettScanEnd at hstopUpper
    omega
  have hcurEq :
      barrettScanStop mem aw p m =
        p + (barrettScanStop mem aw p m - p) := by
    unfold barrettScanStart at hstopLower
    omega
  have hoffsetEq :
      barrettScanStop mem aw p m - p =
        32 + (barrettScanStop mem aw p m - p - 32) := by
    omega
  have hdeltaPos : 0 < barrettScanStop mem aw p m - p - 32 := by
    omega
  have rd1765 := reachBarrettScanNormalizeExit
    (cur := barrettScanStop mem aw p m) (end_ := barrettScanEnd p m)
    (p := p) (m := m) (retBar := retBar) (result := result)
    (exp := exp) (base := base) (ret := ret)
    (offset := barrettScanStop mem aw p m - p)
    (delta := barrettScanStop mem aw p m - p - 32)
    hcurEq hoffsetEq hdeltaPos
    (by
      have hstopCond' :
          barrettScanEnd p m ≤ barrettScanStop mem aw p m ∨
            barrettScanByteAt mem aw (barrettScanStop mem aw p m) ≠ ⟨0⟩ := by
        simpa [barrettScanStop] using hstopCond
      simpa [barrettScanByteAt] using hstopCond')
    hpWord hstopWord (by simpa [barrettScanEnd] using hpend)
    hactiveStop htail rdStop
  exact rd1765.withIndices
    (by unfold barrettScanNormalizeSteps; omega)
    (by unfold barrettScanNormalizeExitGas; omega)

/-- Combined leading-zero scan and normalization re-entry.  Starting at PC 1592, this covers the
case where the scan skips at least one leading zero byte, allocates/copies the normalized modulus,
and re-enters the Barrett backend at PC 1549 with return address PC 1808. -/
theorem reachBarrettScanNormalizeReentry
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {p m retBar result exp base ret fp : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hmodPos : 0 < m) (hm : m ≤ 1024)
    (hp32 : p + 32 < UInt256.size) (hpend : p + m + 31 < UInt256.size)
    (hactiveEnd : p + m + 31 + 32 ≤ 32 * aw.toNat)
    (hnorm : p + 32 < barrettScanStop mem aw p m)
    (hfp : 96 ≤ fp)
    (hbound : fp + bytesAllocationSize
      (m - (barrettScanStop mem aw p m - p - 32)) < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hfp32Word : fp + 32 < UInt256.size)
    (htail : tail.length ≤ 1003)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1592⟩
      (UInt256.ofNat p :: UInt256.ofNat m :: UInt256.ofNat retBar ::
        UInt256.ofNat result :: UInt256.ofNat exp :: UInt256.ofNat base ::
        UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1549⟩
      (UInt256.ofNat base :: UInt256.ofNat exp :: UInt256.ofNat fp :: ⟨1808⟩ ::
        UInt256.ofNat (barrettScanStop mem aw p m - p) ::
        UInt256.ofNat (m - (barrettScanStop mem aw p m - p - 32)) ::
        UInt256.ofNat result :: UInt256.ofNat retBar :: UInt256.ofNat ret :: tail)
      (barrettNormalizedMemory mem fp p (barrettScanStop mem aw p m - p)
        (m - (barrettScanStop mem aw p m - p - 32)))
      (barrettNormalizeCopyWords aw fp p (barrettScanStop mem aw p m - p)
        (m - (barrettScanStop mem aw p m - p - 32)))
      rdata acc (k + barrettScanNormalizeReentrySteps mem aw p m)
        (C + barrettScanNormalizeReentryGas mem aw fp p m) := by
  have rd1765 := reachBarrettScanToNormalize
    (p := p) (m := m) (retBar := retBar) (result := result)
    (exp := exp) (base := base) (ret := ret)
    hmodPos hp32 hpend hactiveEnd hnorm (by omega) rd0
  have hstartLeEnd : barrettScanStart p ≤ barrettScanEnd p m := by
    unfold barrettScanStart barrettScanEnd
    omega
  have hstopBounds := barrettScanStopAt_bounds mem aw
    (barrettScanEnd p m) (barrettScanStart p) hstartLeEnd
  have hstopLower : barrettScanStart p ≤ barrettScanStop mem aw p m := by
    simpa [barrettScanStop] using hstopBounds.1
  have hstopUpper : barrettScanStop mem aw p m ≤ barrettScanEnd p m := by
    simpa [barrettScanStop] using hstopBounds.2
  have hdeltaLe :
      barrettScanStop mem aw p m - p - 32 ≤ m := by
    unfold barrettScanStart at hstopLower
    unfold barrettScanEnd at hstopUpper
    omega
  have hpOffsetWord :
      p + (barrettScanStop mem aw p m - p) < UInt256.size := by
    unfold barrettScanStart at hstopLower
    unfold barrettScanEnd at hstopUpper
    omega
  have rd1549 := reachBarrettNormalizeTo1549
    (delta := barrettScanStop mem aw p m - p - 32)
    (offset := barrettScanStop mem aw p m - p)
    (exp := exp) (p := p) (m := m) (retBar := retBar)
    (result := result) (base := base) (ret := ret) (fp := fp)
    hdeltaLe hm hfp hbound hmemSize hmemLe hgap haw3 haw64 hread hcalldata
    hpOffsetWord hfp32Word htail rd1765
  exact rd1549.withIndices
    (by unfold barrettScanNormalizeReentrySteps; omega)
    (by
      unfold barrettScanNormalizeReentryGas
      dsimp only
      omega)

/-- Normalization plus Barrett's generic result allocation and nontrivial checks.

This is the reusable control-flow/gas bridge for the normalized even-modulus path.  It starts at
the first PC 1592 scan, normalizes the modulus into a fresh bytes array, re-enters PC 1549, allocates
the temporary normalized result buffer, and reaches PC 1592 again for the normalized modulus.

The theorem deliberately leaves the normalized-memory facts (`hlength`, `hzero`, `hone`, and the
active-word bounds) as explicit premises.  Those are pure `ByteArray.write`/slice facts, separate
from the bytecode control-flow proof. -/
theorem reachBarrettNormalizeReentryChecks
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {p m retBar result exp base ret fp resultFp : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hmodPos : 0 < m) (hm : m ≤ 1024)
    (hp32 : p + 32 < UInt256.size) (hpend : p + m + 31 < UInt256.size)
    (hactiveEnd : p + m + 31 + 32 ≤ 32 * aw.toNat)
    (hnorm : p + 32 < barrettScanStop mem aw p m)
    (hfp : 96 ≤ fp)
    (hbound : fp + bytesAllocationSize
      (m - (barrettScanStop mem aw p m - p - 32)) < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hfp32Word : fp + 32 < UInt256.size)
    (hnormLenPos : 0 < m - (barrettScanStop mem aw p m - p - 32))
    (hmodAccess :
      (UInt256.ofNat fp).toNat + 32 ≤
        32 * (barrettNormalizeCopyWords aw fp p
          (barrettScanStop mem aw p m - p)
          (m - (barrettScanStop mem aw p m - p - 32))).toNat)
    (hlength :
      wideLoadWord
        (barrettNormalizedMemory mem fp p (barrettScanStop mem aw p m - p)
          (m - (barrettScanStop mem aw p m - p - 32)))
        (barrettNormalizeCopyWords aw fp p (barrettScanStop mem aw p m - p)
          (m - (barrettScanStop mem aw p m - p - 32)))
        (UInt256.ofNat fp) =
          UInt256.ofNat (m - (barrettScanStop mem aw p m - p - 32)))
    (hresultFp : 96 ≤ resultFp)
    (hresultBound :
      resultFp + bytesAllocationSize
        (m - (barrettScanStop mem aw p m - p - 32)) < 2 ^ 64)
    (hresultMemSize :
      96 ≤
        (barrettNormalizedMemory mem fp p (barrettScanStop mem aw p m - p)
          (m - (barrettScanStop mem aw p m - p - 32))).size)
    (hresultMemLe :
      (barrettNormalizedMemory mem fp p (barrettScanStop mem aw p m - p)
        (m - (barrettScanStop mem aw p m - p - 32))).size ≤ resultFp)
    (hresultGap :
      resultFp -
        (barrettNormalizedMemory mem fp p (barrettScanStop mem aw p m - p)
          (m - (barrettScanStop mem aw p m - p - 32))).size < USize.size)
    (hresultAw3 :
      3 ≤
        (barrettNormalizeCopyWords aw fp p (barrettScanStop mem aw p m - p)
          (m - (barrettScanStop mem aw p m - p - 32))).toNat)
    (hresultAw64 :
      ¬ (⟨64⟩ : UInt256) ≥
        (barrettNormalizeCopyWords aw fp p (barrettScanStop mem aw p m - p)
          (m - (barrettScanStop mem aw p m - p - 32))) * ⟨32⟩)
    (hresultRead :
      (barrettNormalizedMemory mem fp p (barrettScanStop mem aw p m - p)
        (m - (barrettScanStop mem aw p m - p - 32))).readWithPadding 64 32 =
          UInt256.toByteArray (UInt256.ofNat resultFp))
    (hchecksBound :
      fp + 32 + (m - (barrettScanStop mem aw p m - p - 32)) + 32 <
        UInt256.size)
    (hchecksActive :
      fp + 32 + (m - (barrettScanStop mem aw p m - p - 32)) + 32 ≤
        32 * (newBytesWords
          (barrettNormalizeCopyWords aw fp p (barrettScanStop mem aw p m - p)
            (m - (barrettScanStop mem aw p m - p - 32)))
          resultFp (m - (barrettScanStop mem aw p m - p - 32))).toNat)
    (hchecksAw :
      32 * (newBytesWords
        (barrettNormalizeCopyWords aw fp p (barrettScanStop mem aw p m - p)
          (m - (barrettScanStop mem aw p m - p - 32)))
        resultFp (m - (barrettScanStop mem aw p m - p - 32))).toNat <
          UInt256.size)
    (hlengthAfterResult :
      wideLoadWord
        (storeBytesLength
          (setFreePtr
            (barrettNormalizedMemory mem fp p (barrettScanStop mem aw p m - p)
              (m - (barrettScanStop mem aw p m - p - 32)))
            (resultFp + bytesAllocationSize
              (m - (barrettScanStop mem aw p m - p - 32))))
          resultFp (m - (barrettScanStop mem aw p m - p - 32)))
        (newBytesWords
          (barrettNormalizeCopyWords aw fp p (barrettScanStop mem aw p m - p)
            (m - (barrettScanStop mem aw p m - p - 32)))
          resultFp (m - (barrettScanStop mem aw p m - p - 32)))
        (UInt256.ofNat fp) =
          UInt256.ofNat (m - (barrettScanStop mem aw p m - p - 32)))
    (hzero :
      memoryZeroResult
        (storeBytesLength
          (setFreePtr
            (barrettNormalizedMemory mem fp p (barrettScanStop mem aw p m - p)
              (m - (barrettScanStop mem aw p m - p - 32)))
            (resultFp + bytesAllocationSize
              (m - (barrettScanStop mem aw p m - p - 32))))
          resultFp (m - (barrettScanStop mem aw p m - p - 32)))
        (newBytesWords
          (barrettNormalizeCopyWords aw fp p (barrettScanStop mem aw p m - p)
            (m - (barrettScanStop mem aw p m - p - 32)))
          resultFp (m - (barrettScanStop mem aw p m - p - 32)))
        (fp + 32)
        (fp + 32 + (m - (barrettScanStop mem aw p m - p - 32))) = 0)
    (hone :
      memoryOneResult
        (storeBytesLength
          (setFreePtr
            (barrettNormalizedMemory mem fp p (barrettScanStop mem aw p m - p)
              (m - (barrettScanStop mem aw p m - p - 32)))
            (resultFp + bytesAllocationSize
              (m - (barrettScanStop mem aw p m - p - 32))))
          resultFp (m - (barrettScanStop mem aw p m - p - 32)))
        (newBytesWords
          (barrettNormalizeCopyWords aw fp p (barrettScanStop mem aw p m - p)
            (m - (barrettScanStop mem aw p m - p - 32)))
          resultFp (m - (barrettScanStop mem aw p m - p - 32)))
        fp (m - (barrettScanStop mem aw p m - p - 32)) = 0)
    (htail : tail.length ≤ 1002)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1592⟩
      (UInt256.ofNat p :: UInt256.ofNat m :: UInt256.ofNat retBar ::
        UInt256.ofNat result :: UInt256.ofNat exp :: UInt256.ofNat base ::
        UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1592⟩
      (UInt256.ofNat fp ::
        UInt256.ofNat (m - (barrettScanStop mem aw p m - p - 32)) ::
        ⟨1808⟩ :: UInt256.ofNat resultFp :: UInt256.ofNat exp ::
        UInt256.ofNat base :: UInt256.ofNat (barrettScanStop mem aw p m - p) ::
        UInt256.ofNat (m - (barrettScanStop mem aw p m - p - 32)) ::
        UInt256.ofNat result :: UInt256.ofNat retBar :: UInt256.ofNat ret :: tail)
      (storeBytesLength
        (setFreePtr
          (barrettNormalizedMemory mem fp p (barrettScanStop mem aw p m - p)
            (m - (barrettScanStop mem aw p m - p - 32)))
          (resultFp + bytesAllocationSize
            (m - (barrettScanStop mem aw p m - p - 32))))
        resultFp (m - (barrettScanStop mem aw p m - p - 32)))
      (newBytesWords
        (barrettNormalizeCopyWords aw fp p (barrettScanStop mem aw p m - p)
          (m - (barrettScanStop mem aw p m - p - 32)))
        resultFp (m - (barrettScanStop mem aw p m - p - 32)))
      rdata acc k'
        (C + barrettScanNormalizeReentryGas mem aw fp p m +
          55 + newBytesGas
            (barrettNormalizeCopyWords aw fp p (barrettScanStop mem aw p m - p)
              (m - (barrettScanStop mem aw p m - p - 32)))
            resultFp (m - (barrettScanStop mem aw p m - p - 32)) +
          wideWordChecksGas
            (storeBytesLength
              (setFreePtr
                (barrettNormalizedMemory mem fp p (barrettScanStop mem aw p m - p)
                  (m - (barrettScanStop mem aw p m - p - 32)))
                (resultFp + bytesAllocationSize
                  (m - (barrettScanStop mem aw p m - p - 32))))
              resultFp (m - (barrettScanStop mem aw p m - p - 32)))
            (newBytesWords
              (barrettNormalizeCopyWords aw fp p (barrettScanStop mem aw p m - p)
                (m - (barrettScanStop mem aw p m - p - 32)))
              resultFp (m - (barrettScanStop mem aw p m - p - 32)))
            fp (m - (barrettScanStop mem aw p m - p - 32))) := by
  have rd1549 := reachBarrettScanNormalizeReentry
    (p := p) (m := m) (retBar := retBar) (result := result)
    (exp := exp) (base := base) (ret := ret) (fp := fp)
    hmodPos hm hp32 hpend hactiveEnd hnorm hfp hbound hmemSize hmemLe hgap
    haw3 haw64 hread hcalldata hfp32Word (by omega) rd0
  have rd1549' : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1549⟩
      (UInt256.ofNat base :: UInt256.ofNat exp :: UInt256.ofNat fp ::
        UInt256.ofNat 1808 ::
        UInt256.ofNat (barrettScanStop mem aw p m - p) ::
        UInt256.ofNat (m - (barrettScanStop mem aw p m - p - 32)) ::
        UInt256.ofNat result :: UInt256.ofNat retBar :: UInt256.ofNat ret :: tail)
      (barrettNormalizedMemory mem fp p (barrettScanStop mem aw p m - p)
        (m - (barrettScanStop mem aw p m - p - 32)))
      (barrettNormalizeCopyWords aw fp p (barrettScanStop mem aw p m - p)
        (m - (barrettScanStop mem aw p m - p - 32)))
      rdata acc (k + barrettScanNormalizeReentrySteps mem aw p m)
        (C + barrettScanNormalizeReentryGas mem aw fp p m) := by
    simpa [show UInt256.ofNat 1808 = (⟨1808⟩ : UInt256) by native_decide] using rd1549
  have hnormLenLe : m - (barrettScanStop mem aw p m - p - 32) ≤ 1024 := by
    omega
  have rd1570 := allocateBarrettResultExactGeneric
    (basePtr := base) (exponentPtr := exp) (modulusPtr := fp) (ret := 1808)
    (fp := resultFp)
    (modulusSize := m - (barrettScanStop mem aw p m - p - 32))
    (tail := UInt256.ofNat (barrettScanStop mem aw p m - p) ::
      UInt256.ofNat (m - (barrettScanStop mem aw p m - p - 32)) ::
      UInt256.ofNat result :: UInt256.ofNat retBar :: UInt256.ofNat ret :: tail)
    hnormLenPos hnormLenLe hmodAccess hlength hresultFp hresultBound hresultMemSize
    hresultMemLe hresultGap hresultAw3 hresultAw64 hresultRead hcalldata
    (by simp only [List.length_cons]; omega) rd1549'
  obtain ⟨kChecks, rd1592⟩ := reachBarrettNontrivialChecks
    (basePtr := base) (exponentPtr := exp) (modulusPtr := fp) (resultPtr := resultFp)
    (modulusSize := m - (barrettScanStop mem aw p m - p - 32)) (ret := 1808)
    (tail := UInt256.ofNat (barrettScanStop mem aw p m - p) ::
      UInt256.ofNat (m - (barrettScanStop mem aw p m - p - 32)) ::
      UInt256.ofNat result :: UInt256.ofNat retBar :: UInt256.ofNat ret :: tail)
    hchecksBound hchecksActive hchecksAw hlengthAfterResult hzero hone
    (by simp only [List.length_cons]; omega) rd1570
  refine ⟨kChecks, rd1592.withIndices rfl ?_⟩
  omega

/-- Restore the result of a normalized recursive Barrett call.  PC 1808 copies `len` bytes from
the temporary normalized result payload `temp + 32` into the original result payload at
`result + offset`, then jumps to the saved Barrett return address. -/
theorem reachBarrettRestoreToRetBar
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {temp result offset len retBar ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hlenWord : len < UInt256.size)
    (htemp32Word : temp + 32 < UInt256.size)
    (hresultOffsetWord : result + offset < UInt256.size)
    (hretBar : (D_J runtimeBytecode 0).contains (UInt256.ofNat retBar) = true)
    (htail : tail.length ≤ 1017)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1808⟩
      (UInt256.ofNat temp :: UInt256.ofNat offset :: UInt256.ofNat len ::
        UInt256.ofNat result :: UInt256.ofNat retBar :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat retBar)
      (UInt256.ofNat result :: UInt256.ofNat ret :: tail)
      (barrettRestoreMemory mem temp result offset len)
      (barrettRestoreWords aw temp result offset len)
      rdata acc (k + 9) (C + barrettRestoreGas aw temp result offset len) := by
  have hd := barrettRestoreDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  have rd1815raw := evm_run rd0 with [known jumpdest h0, known push1 h1 ⟨32⟩,
    known add h2, known swap1 h3, known dup4 h4, known add h5]
  have htempWord : temp < UInt256.size := by omega
  have hoffsetWord : offset < UInt256.size := by omega
  have hresultWord : result < UInt256.size := by omega
  have hsrc :
      ⟨32⟩ + UInt256.ofNat temp = UInt256.ofNat (temp + 32) := by
    rw [u256_add_comm]
    simpa using (ofNat_add_bounded (a := temp) (b := 32) htemp32Word)
  have hdst :
      UInt256.ofNat result + UInt256.ofNat offset =
        UInt256.ofNat (result + offset) :=
    ofNat_add_bounded hresultOffsetWord
  rw [hsrc, hdst] at rd1815raw
  have hsrcNat : (UInt256.ofNat (temp + 32)).toNat = temp + 32 :=
    UInt256.toNat_ofNat_of_lt htemp32Word
  have hdstNat : (UInt256.ofNat (result + offset)).toNat = result + offset :=
    UInt256.toNat_ofNat_of_lt hresultOffsetWord
  have hlenNat : (UInt256.ofNat len).toNat = len :=
    UInt256.toNat_ofNat_of_lt hlenWord
  have rd1816 := RDx.mcopy (barrettRestoreExpansionGas aw temp result offset len)
    (barrettRestoreMemory mem temp result offset len)
    (barrettRestoreWords aw temp result offset len) rd1815raw h6
    (by
      intro s hsaw hstk
      simp [barrettRestoreExpansionGas, barrettRestoreWords,
        memoryExpansionCost, memoryExpansionCost.μᵢ', hsaw, hstk, hsrcNat, hdstNat,
        hlenNat])
    (by simp [barrettRestoreMemory, hsrcNat, hdstNat, hlenNat])
    (by simp [barrettRestoreWords, hsrcNat, hdstNat, hlenNat])
    (by simp only [List.length_cons]; omega)
  have rdRetRaw := evm_run rd1816 with [known swap1 h7, known jump h8 hretBar]
  exact rdRetRaw.withIndices (by omega) (by
    unfold barrettRestoreGas
    simp only [GasConstants.Gverylow, GasConstants.Gcopy]
    rw [hlenNat]
    omega)

/-- Direct exit of Barrett's leading-zero scan.  This is the path where the first modulus payload
byte is already significant, or the modulus length is one byte.  The theorem is intentionally
generic in the pointers so it can be reused before specializing to the copied ModExp operands. -/
theorem reachBarrettScanDirect
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {p m retBar result exp base ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hp32 : p + 32 < UInt256.size) (hpend : p + m + 31 < UInt256.size)
    (hactive : p + 64 ≤ 32 * aw.toNat)
    (hfirst : m = 1 ∨
      UInt256.byteAt ⟨0⟩ (wideLoadWord mem aw (UInt256.ofNat (p + 32))) ≠ ⟨0⟩)
    (htail : tail.length ≤ 1006)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1592⟩
      (UInt256.ofNat p :: UInt256.ofNat m :: UInt256.ofNat retBar ::
        UInt256.ofNat result :: UInt256.ofNat exp :: UInt256.ofNat base ::
        UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1646⟩
      (⟨0⟩ :: ⟨32⟩ :: UInt256.ofNat exp :: UInt256.ofNat p ::
        UInt256.ofNat m :: UInt256.ofNat retBar :: UInt256.ofNat result ::
        UInt256.ofNat base :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k' (C + 128) := by
  have hd := barrettScanDirectDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,
    h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,
    h36,h37,h38,h39⟩
  have hp : p < UInt256.size := by omega
  have hpm : p + m < UInt256.size := by omega
  have hp32eq : UInt256.ofNat p + ⟨32⟩ = UInt256.ofNat (p + 32) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (ofNat_add_bounded (a := p) (b := 32) hp32)
  have hpmeq : UInt256.ofNat p + UInt256.ofNat m = UInt256.ofNat (p + m) :=
    ofNat_add_bounded hpm
  have hpendEq : ⟨31⟩ + UInt256.ofNat (p + m) =
      UInt256.ofNat (p + m + 31) := by
    rw [u256_add_comm]
    simpa [Nat.add_assoc] using
      (ofNat_add_bounded (a := p + m) (b := 31) hpend)
  have rd1604raw := evm_run rd0 with [known dup2 h0, known dup2 h1,
    known add h2, known push1 h3 ⟨31⟩, known add h4, known swap5 h5,
    known push1 h6 ⟨32⟩, known dup3 h7, known add h8, known jumpdest h9,
    known dup1 h10]
  rw [hpmeq, hpendEq, hp32eq] at rd1604raw
  have rd1604 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1605⟩
      (UInt256.ofNat (p + 32) :: UInt256.ofNat (p + 32) ::
        UInt256.ofNat exp :: UInt256.ofNat p :: UInt256.ofNat m ::
        UInt256.ofNat retBar :: UInt256.ofNat result ::
        UInt256.ofNat (p + m + 31) :: UInt256.ofNat base ::
        UInt256.ofNat ret :: tail)
      mem aw rdata acc (k + 11) (C + 31) :=
    (rd1604raw.withPC (by native_decide)).withIndices (by omega) (by omega)
  have rd1606 := RDx.mloadWithin rd1604 h11 (by
    rw [UInt256.toNat_ofNat_of_lt hp32]
    exact hactive) (by simp only [List.length_cons]; omega)
  have rd1606' : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1606⟩
      (wideLoadWord mem aw (UInt256.ofNat (p + 32)) ::
        UInt256.ofNat (p + 32) :: UInt256.ofNat exp :: UInt256.ofNat p ::
        UInt256.ofNat m :: UInt256.ofNat retBar :: UInt256.ofNat result ::
        UInt256.ofNat (p + m + 31) :: UInt256.ofNat base ::
        UInt256.ofNat ret :: tail)
      mem aw rdata acc (k + 12) (C + 34) :=
    (rd1606.withPC (by native_decide)).withIndices (by omega) (by omega)
  have rd1614 := evm_run rd1606' with [known push0 h12, known byte h13,
    known iszero h14, known dup8 h15, known dup3 h16, known lt h17,
    known and h18, known iszero h19, known push2 h20 ⟨1625⟩]
  have hcond :
      UInt256.isZero
        (UInt256.land
          (UInt256.lt (UInt256.ofNat (p + 32)) (UInt256.ofNat (p + m + 31)))
          (UInt256.isZero
            (UInt256.byteAt ⟨0⟩ (wideLoadWord mem aw (UInt256.ofNat (p + 32)))))) =
        ⟨1⟩ := by
    rcases hfirst with hm1 | hbyte
    · have hlt : UInt256.lt (UInt256.ofNat (p + 32))
          (UInt256.ofNat (p + m + 31)) = ⟨0⟩ := by
        apply ult_zero
        rw [UInt256.toNat_ofNat_of_lt hp32, UInt256.toNat_ofNat_of_lt hpend]
        omega
      rw [hlt]
      have hland : UInt256.land ⟨0⟩
          (UInt256.isZero
            (UInt256.byteAt ⟨0⟩ (wideLoadWord mem aw (UInt256.ofNat (p + 32))))) =
          ⟨0⟩ := by
        apply u256_inj
        rw [uland_toNat]
        simp
      rw [hland]
      native_decide
    · have hiz : UInt256.isZero
          (UInt256.byteAt ⟨0⟩ (wideLoadWord mem aw (UInt256.ofNat (p + 32)))) =
          ⟨0⟩ := isZero_eq_zero_of_ne hbyte
      rw [hiz]
      have hland : UInt256.land
          (UInt256.lt (UInt256.ofNat (p + 32)) (UInt256.ofNat (p + m + 31))) ⟨0⟩ =
          ⟨0⟩ := by
        apply u256_inj
        rw [uland_toNat]
        simp
      rw [hland]
      native_decide
  have rd1625 := rd1614.jumpiT h21 (by rw [hcond]; native_decide)
    jumpDest_1625_barrett (by evm_ov)
  have rd1625' : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1625⟩
      (UInt256.ofNat (p + 32) :: UInt256.ofNat exp :: UInt256.ofNat p ::
        UInt256.ofNat m :: UInt256.ofNat retBar :: UInt256.ofNat result ::
        UInt256.ofNat (p + m + 31) :: UInt256.ofNat base ::
        UInt256.ofNat ret :: tail)
      mem aw rdata acc (k + 22) (C + 70) :=
    (rd1625.withPC (by native_decide)).withIndices (by omega) (by omega)
  have rd1636raw := evm_run rd1625' with [
    known jumpdest h22, known dup3 h23, known swap4 h24, known swap5 h25,
    known swap6 h26, known swap7 h27, known pop h28, known swap2 h29,
    known swap1 h30, known swap2 h31, known sub h32]
  have hsub : UInt256.sub (UInt256.ofNat (p + 32)) (UInt256.ofNat p) = ⟨32⟩ := by
    simpa using
      (ofNat_sub_bounded (a := p + 32) (b := p) (by omega) hp32)
  rw [hsub] at rd1636raw
  have rd1636 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1636⟩
      (⟨32⟩ :: UInt256.ofNat exp :: UInt256.ofNat p ::
        UInt256.ofNat m :: UInt256.ofNat retBar :: UInt256.ofNat result ::
        UInt256.ofNat base :: UInt256.ofNat ret :: tail)
      mem aw rdata acc (k + 33) (C + 100) :=
    (rd1636raw.withPC (by native_decide)).withIndices (by omega) (by omega)
  have rd1646raw := evm_run rd1636 with [
    known push1 h33 ⟨31⟩, known not h34, known dup2 h35, known add h36, known dup1 h37,
    known push2 h38 ⟨1765⟩, known jumpiNT h39 (by native_decide)]
  have hzero : (⟨32⟩ : UInt256) + UInt256.lnot ⟨31⟩ = ⟨0⟩ := by native_decide
  rw [hzero] at rd1646raw
  exact ⟨k + 40, (rd1646raw.withPC (by native_decide)).withIndices (by omega) (by omega)⟩

/-- From the direct scan exit, the Barrett backend computes that the modulus is one word and
calls the already verified `modexpWordInto` helper at PC 2574. -/
theorem reachBarrettDirectWordHelper
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {p m retBar result exp base ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hmPos : 0 < m) (hm : m ≤ 32)
    (htail : tail.length ≤ 1006)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1646⟩
      (⟨0⟩ :: ⟨32⟩ :: UInt256.ofNat exp :: UInt256.ofNat p ::
        UInt256.ofNat m :: UInt256.ofNat retBar :: UInt256.ofNat result ::
        UInt256.ofNat base :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2574⟩
      (UInt256.ofNat base :: UInt256.ofNat exp :: UInt256.ofNat p ::
        UInt256.ofNat result :: ⟨1271⟩ :: UInt256.ofNat result ::
        UInt256.ofNat retBar :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k' (C + 145) := by
  have ha := barrettWordDispatchDecodesA
  simp only [List.cons.injEq, and_true] at ha
  rcases ha with ⟨a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17⟩
  have rd1309 := evm_run rd0 with [known pop a0, known pop a1,
    known push2 a2 ⟨1665⟩, known push2 a3 ⟨1659⟩, known dup5 a4,
    known push2 a5 ⟨1309⟩, known jump a6 jumpDest_1309_barrett]
  have hsumBound : m + 31 < UInt256.size := by
    apply lt_of_le_of_lt (show m + 31 ≤ 63 by omega) (by decide)
  have hsum : UInt256.ofNat m + (⟨31⟩ : UInt256) =
      UInt256.ofNat (m + 31) := by
    simpa using ofNat_add_bounded hsumBound
  have hgt : UInt256.gt (UInt256.ofNat m)
      (UInt256.ofNat m + ⟨31⟩) = ⟨0⟩ := by
    rw [hsum]
    apply ugt_zero
    rw [UInt256.toNat_ofNat_of_lt (by omega : m < UInt256.size),
      UInt256.toNat_ofNat_of_lt hsumBound]
    omega
  have rd1659raw := evm_run rd1309 with [known jumpdest a7, known swap1 a8,
    known push1 a9 ⟨31⟩, known dup3 a10, known add a11, known dup1 a12,
    known swap3 a13, known gt a14, known push2 a15 ⟨1037⟩,
    known jumpiNT a16 hgt, known jump a17 jumpDest_1659_barrett]
  rw [hsum] at rd1659raw
  have hb := barrettWordDispatchDecodesB
  simp only [List.cons.injEq, and_true] at hb
  rcases hb with ⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11⟩
  have rd1665raw := evm_run rd1659raw with [known jumpdest b0,
    known push1 b1 ⟨5⟩, known shr b2, known swap1 b3,
    known jump b4 jumpDest_1665_barrett]
  have hone : UInt256.shiftRight (UInt256.ofNat (m + 31)) ⟨5⟩ = ⟨1⟩ := by
    apply u256_inj
    rw [shiftRight_toNat_of_lt256 _ _ (by decide),
      UInt256.toNat_ofNat_of_lt hsumBound]
    rw [show (⟨5⟩ : UInt256).toNat = 5 by decide,
      show (⟨1⟩ : UInt256).toNat = 1 by decide]
    norm_num
    omega
  rw [hone] at rd1665raw
  have rd1750 := evm_run rd1665raw with [known jumpdest b5, known swap2 b6,
    known push1 b7 ⟨1⟩, known dup4 b8, known eq b9,
    known push2 b10 ⟨1750⟩, known jumpiT b11 (by decide) jumpDest_1750_barrett]
  have hc := barrettWordCallDecodes
  simp only [List.cons.injEq, and_true] at hc
  rcases hc with ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10⟩
  have rd2574 := evm_run rd1750 with [known jumpdest c0, known swap2 c1,
    known pop c2, known dup5 c3, known swap3 c4, known pop c5,
    known push2 c6 ⟨1271⟩, known swap4 c7, known swap6 c8,
    known push2 c9 ⟨2574⟩, known jump c10 jumpDest_2574_barrett]
  exact ⟨k + 41, (rd2574.withPC (by native_decide)).withIndices (by omega) (by omega)⟩

/-- Complete the normalized one-word Barrett backend from the original PC 1592 scan to the
original Barrett return address.

This composes normalization, re-entry checks, the direct one-word scan on the normalized modulus,
the pointer-generic `modexpWordInto` helper, the PC 1271 trampoline into PC 1808, and the PC 1808
restore copy back into the original result buffer.  Memory/model facts about the normalized bytes
array are explicit premises; the theorem discharges the bytecode control-flow and exact-gas
accounting. -/
theorem reachBarrettNormalizedWordRestore
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize p m retBar result ret fp resultFp : Nat}
    {tail : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < m) (hm : m ≤ 1024)
    (hp32 : p + 32 < UInt256.size) (hpend : p + m + 31 < UInt256.size)
    (hactiveEnd : p + m + 31 + 32 ≤ 32 * aw.toNat)
    (hnorm : p + 32 < barrettScanStop mem aw p m)
    (hfp : 96 ≤ fp)
    (hbound : fp + bytesAllocationSize (barrettNormalizedLen mem aw p m) < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hfp32Word : fp + 32 < UInt256.size)
    (hnormLenPos : 0 < barrettNormalizedLen mem aw p m)
    (hnormLenWord : barrettNormalizedLen mem aw p m < UInt256.size)
    (hnormLenLe32 : barrettNormalizedLen mem aw p m ≤ 32)
    (hmodAccess :
      (UInt256.ofNat fp).toNat + 32 ≤
        32 * (barrettNormalizedAw aw mem fp p m).toNat)
    (hlength :
      wideLoadWord (barrettNormalizedMem mem aw fp p m)
        (barrettNormalizedAw aw mem fp p m) (UInt256.ofNat fp) =
          UInt256.ofNat (barrettNormalizedLen mem aw p m))
    (hresultFp : 96 ≤ resultFp)
    (hresultBound :
      resultFp + bytesAllocationSize (barrettNormalizedLen mem aw p m) < 2 ^ 64)
    (hresultMemSize : 96 ≤ (barrettNormalizedMem mem aw fp p m).size)
    (hresultMemLe : (barrettNormalizedMem mem aw fp p m).size ≤ resultFp)
    (hresultGap : resultFp - (barrettNormalizedMem mem aw fp p m).size < USize.size)
    (hresultAw3 : 3 ≤ (barrettNormalizedAw aw mem fp p m).toNat)
    (hresultAw64 : ¬ (⟨64⟩ : UInt256) ≥
      (barrettNormalizedAw aw mem fp p m) * ⟨32⟩)
    (hresultRead :
      (barrettNormalizedMem mem aw fp p m).readWithPadding 64 32 =
        UInt256.toByteArray (UInt256.ofNat resultFp))
    (hchecksBound :
      fp + 32 + barrettNormalizedLen mem aw p m + 32 < UInt256.size)
    (hchecksActive :
      fp + 32 + barrettNormalizedLen mem aw p m + 32 ≤
        32 * (barrettNormalizedResultAw mem aw fp p m resultFp).toNat)
    (hchecksAw :
      32 * (barrettNormalizedResultAw mem aw fp p m resultFp).toNat < UInt256.size)
    (hlengthAfterResult :
      wideLoadWord (barrettNormalizedResultMem mem aw fp p m resultFp)
        (barrettNormalizedResultAw mem aw fp p m resultFp) (UInt256.ofNat fp) =
          UInt256.ofNat (barrettNormalizedLen mem aw p m))
    (hzero :
      memoryZeroResult (barrettNormalizedResultMem mem aw fp p m resultFp)
        (barrettNormalizedResultAw mem aw fp p m resultFp)
        (fp + 32) (fp + 32 + barrettNormalizedLen mem aw p m) = 0)
    (hone :
      memoryOneResult (barrettNormalizedResultMem mem aw fp p m resultFp)
        (barrettNormalizedResultAw mem aw fp p m resultFp)
        fp (barrettNormalizedLen mem aw p m) = 0)
    (hfpEndWord : fp + barrettNormalizedLen mem aw p m + 31 < UInt256.size)
    (hfpActive : fp + 64 ≤
      32 * (barrettNormalizedResultAw mem aw fp p m resultFp).toNat)
    (hfirst :
      barrettNormalizedLen mem aw p m = 1 ∨
      UInt256.byteAt ⟨0⟩
        (wideLoadWord (barrettNormalizedResultMem mem aw fp p m resultFp)
          (barrettNormalizedResultAw mem aw fp p m resultFp)
          (UInt256.ofNat (fp + 32))) ≠ ⟨0⟩)
    (hbaseLength :
      wideLoadWord (barrettNormalizedResultMem mem aw fp p m resultFp)
        (barrettNormalizedResultAw mem aw fp p m resultFp)
        (UInt256.ofNat operandBasePtr) = UInt256.ofNat baseSize)
    (hexponentLength :
      wideLoadWord (barrettNormalizedResultMem mem aw fp p m resultFp)
        (barrettNormalizedResultAw mem aw fp p m resultFp)
        (UInt256.ofNat (operandExponentPtr baseSize)) = UInt256.ofNat exponentSize)
    (hbaseActive :
      operandBasePtr + 32 + baseSize ≤
        32 * (barrettNormalizedResultAw mem aw fp p m resultFp).toNat)
    (hbaseDataActive :
      operandBasePtr + 64 ≤
        32 * (barrettNormalizedResultAw mem aw fp p m resultFp).toNat)
    (hexponentActive :
      wideExponentDataPtr baseSize + exponentSize + 32 ≤
        32 * (barrettNormalizedResultAw mem aw fp p m resultFp).toNat)
    (hresultFpWord : resultFp + 32 < UInt256.size)
    (hresultPayloadActive :
      resultFp + 32 + barrettNormalizedLen mem aw p m ≤
        32 * (barrettNormalizedResultAw mem aw fp p m resultFp).toNat)
    (hresultOffsetWord : result + barrettNormalizedOffset mem aw p m < UInt256.size)
    (hretBar : (D_J runtimeBytecode 0).contains (UInt256.ofNat retBar) = true)
    (htail : tail.length ≤ 993)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1592⟩
      (UInt256.ofNat p :: UInt256.ofNat m :: UInt256.ofNat retBar ::
        UInt256.ofNat result :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat operandBasePtr :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat retBar)
      (UInt256.ofNat result :: UInt256.ofNat ret :: tail)
      (barrettRestoreMemory
        (wideWordReturnMemory
          (barrettNormalizedResultMem mem aw fp p m resultFp)
          (wideWordValueAtModulusPtr
            (barrettNormalizedResultMem mem aw fp p m resultFp)
            (barrettNormalizedResultAw mem aw fp p m resultFp)
            baseSize exponentSize fp (barrettNormalizedLen mem aw p m))
          (UInt256.ofNat resultFp) (barrettNormalizedLen mem aw p m))
        resultFp result (barrettNormalizedOffset mem aw p m)
        (barrettNormalizedLen mem aw p m))
      (barrettRestoreWords (barrettNormalizedResultAw mem aw fp p m resultFp)
        resultFp result (barrettNormalizedOffset mem aw p m)
        (barrettNormalizedLen mem aw p m))
      rdata acc k'
        (C + barrettNormalizeWordRestoreGas mem aw fp p m resultFp result
          baseSize exponentSize) := by
  obtain ⟨kChecks, rd1592⟩ := reachBarrettNormalizeReentryChecks
    (p := p) (m := m) (retBar := retBar) (result := result)
    (exp := operandExponentPtr baseSize) (base := operandBasePtr) (ret := ret)
    (fp := fp) (resultFp := resultFp) (tail := tail)
    hmodPos hm hp32 hpend hactiveEnd hnorm hfp
    (by simpa [barrettNormalizedLen, barrettNormalizedOffset] using hbound)
    (by simpa [barrettNormalizedMem, barrettNormalizedLen, barrettNormalizedOffset]
      using hmemSize)
    (by simpa [barrettNormalizedMem, barrettNormalizedLen, barrettNormalizedOffset]
      using hmemLe)
    hgap haw3 haw64 hread hcalldata hfp32Word
    (by simpa [barrettNormalizedLen, barrettNormalizedOffset] using hnormLenPos)
    (by simpa [barrettNormalizedAw, barrettNormalizedLen, barrettNormalizedOffset]
      using hmodAccess)
    (by simpa [barrettNormalizedMem, barrettNormalizedAw, barrettNormalizedLen,
        barrettNormalizedOffset] using hlength)
    hresultFp
    (by simpa [barrettNormalizedLen, barrettNormalizedOffset] using hresultBound)
    (by simpa [barrettNormalizedMem, barrettNormalizedLen, barrettNormalizedOffset]
      using hresultMemSize)
    (by simpa [barrettNormalizedMem, barrettNormalizedLen, barrettNormalizedOffset]
      using hresultMemLe)
    (by simpa [barrettNormalizedMem, barrettNormalizedLen, barrettNormalizedOffset]
      using hresultGap)
    (by simpa [barrettNormalizedAw, barrettNormalizedLen, barrettNormalizedOffset]
      using hresultAw3)
    (by simpa [barrettNormalizedAw, barrettNormalizedLen, barrettNormalizedOffset]
      using hresultAw64)
    (by simpa [barrettNormalizedMem, barrettNormalizedLen, barrettNormalizedOffset]
      using hresultRead)
    (by simpa [barrettNormalizedLen, barrettNormalizedOffset] using hchecksBound)
    (by simpa [barrettNormalizedResultAw, barrettNormalizedAw, barrettNormalizedLen,
        barrettNormalizedOffset] using hchecksActive)
    (by simpa [barrettNormalizedResultAw, barrettNormalizedAw, barrettNormalizedLen,
        barrettNormalizedOffset] using hchecksAw)
    (by simpa [barrettNormalizedResultMem, barrettNormalizedResultAw, barrettNormalizedMem,
        barrettNormalizedAw, barrettNormalizedLen, barrettNormalizedOffset]
      using hlengthAfterResult)
    (by simpa [barrettNormalizedResultMem, barrettNormalizedResultAw, barrettNormalizedMem,
        barrettNormalizedAw, barrettNormalizedLen, barrettNormalizedOffset]
      using hzero)
    (by simpa [barrettNormalizedResultMem, barrettNormalizedResultAw, barrettNormalizedMem,
        barrettNormalizedAw, barrettNormalizedLen, barrettNormalizedOffset]
      using hone)
    (by omega) rd0
  obtain ⟨kScan, rd1646⟩ := reachBarrettScanDirect
    (p := fp) (m := barrettNormalizedLen mem aw p m) (retBar := 1808)
    (result := resultFp) (exp := operandExponentPtr baseSize)
    (base := operandBasePtr) (ret := barrettNormalizedOffset mem aw p m)
    (tail := UInt256.ofNat (barrettNormalizedLen mem aw p m) ::
      UInt256.ofNat result :: UInt256.ofNat retBar :: UInt256.ofNat ret :: tail)
    hfp32Word hfpEndWord hfpActive hfirst
    (by simp only [List.length_cons]; omega) (by
      simpa [barrettNormalizedResultMem, barrettNormalizedResultAw, barrettNormalizedMem,
        barrettNormalizedAw, barrettNormalizedLen, barrettNormalizedOffset] using rd1592)
  obtain ⟨kCall, rd2574⟩ := reachBarrettDirectWordHelper
    (p := fp) (m := barrettNormalizedLen mem aw p m) (retBar := 1808)
    (result := resultFp) (exp := operandExponentPtr baseSize)
    (base := operandBasePtr) (ret := barrettNormalizedOffset mem aw p m)
    (tail := UInt256.ofNat (barrettNormalizedLen mem aw p m) ::
      UInt256.ofNat result :: UInt256.ofNat retBar :: UInt256.ofNat ret :: tail)
    hnormLenPos hnormLenLe32 (by simp only [List.length_cons]; omega) rd1646
  have rdHelper := runWideWordHelperModulusPtrExact
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusPtr := fp)
    (modulusSize := barrettNormalizedLen mem aw p m)
    (result := UInt256.ofNat resultFp) (ret := ⟨1271⟩)
    (tail := UInt256.ofNat resultFp :: ⟨1808⟩ ::
      UInt256.ofNat (barrettNormalizedOffset mem aw p m) ::
      UInt256.ofNat (barrettNormalizedLen mem aw p m) ::
      UInt256.ofNat result :: UInt256.ofNat retBar :: UInt256.ofNat ret :: tail)
    hb he hnormLenPos hnormLenLe32 (by omega) hfp32Word
    hbaseLength hexponentLength hlengthAfterResult hbaseActive hbaseDataActive
    hexponentActive (by omega) hfpActive
    (by
      rw [UInt256.toNat_ofNat_of_lt (by omega : resultFp < UInt256.size)]
      exact hresultFpWord)
    (by
      rw [UInt256.toNat_ofNat_of_lt (by omega : resultFp < UInt256.size)]
      exact hresultPayloadActive)
    jumpDest_1271_barrett (by simp only [List.length_cons]; omega)
    (by
      simpa [barrettNormalizedResultMem, barrettNormalizedResultAw, barrettNormalizedMem,
        barrettNormalizedAw, barrettNormalizedLen, barrettNormalizedOffset] using rd2574)
  have hd := barrettReturnDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2⟩
  have rd1808 := evm_run rdHelper with [known jumpdest h0, known swap1 h1,
    known jump h2 jumpDest_1808_barrett]
  have rdRestored := reachBarrettRestoreToRetBar
    (temp := resultFp) (result := result)
    (offset := barrettNormalizedOffset mem aw p m)
    (len := barrettNormalizedLen mem aw p m) (retBar := retBar) (ret := ret)
    (tail := tail) hnormLenWord hresultFpWord hresultOffsetWord hretBar
    (by omega)
    (by
      simpa [barrettNormalizedResultMem, barrettNormalizedResultAw, barrettNormalizedMem,
        barrettNormalizedAw, barrettNormalizedLen, barrettNormalizedOffset] using rd1808)
  refine ⟨_, rdRestored.withIndices rfl ?_⟩
  · unfold barrettNormalizeWordRestoreGas barrettNormalizeReentryChecksGas
    unfold barrettNormalizedResultMem barrettNormalizedResultAw
    unfold barrettNormalizedMem barrettNormalizedAw barrettNormalizedLen barrettNormalizedOffset
    simp only [Nat.add_assoc]
    omega

def preparedBarrettDirectWordGasFromAw (I : ExecutionEnv) (aw : UInt256)
    (baseSize exponentSize modulusSize : Nat) : Nat :=
  preparedBarrettPrefixGasFromAw I aw baseSize exponentSize modulusSize +
    128 + 145 + wideWordHelperGas I baseSize exponentSize modulusSize + 24

def preparedBarrettNormalizedWordGasFromAw (I : ExecutionEnv) (aw : UInt256)
    (baseSize exponentSize modulusSize fp resultFp : Nat) : Nat :=
  preparedBarrettPrefixGasFromAw I aw baseSize exponentSize modulusSize +
    barrettNormalizeWordRestoreGas
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize)
      fp (operandModulusPtr baseSize exponentSize) modulusSize resultFp
      (operandFreePtr baseSize exponentSize modulusSize) baseSize exponentSize +
    12

/-- Prepared-operand normalized Barrett one-word path, still exposing pure normalized-memory facts.

This is the branch-level bytecode composition from the common prepared operand entry at PC 1183 to
the caller-supplied return PC.  It covers the case where the first Barrett scan normalizes the
modulus, the normalized modulus is one word, and PC 1808 restores the shortened result bytes into
the original result buffer. -/
theorem runPreparedBarrettNormalizedWordExactAny
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize ret fp resultFp : Nat} {tail : List UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 32)
    (hmod : 1 < Model.bytesToNatPadded I.calldata
      (96 + baseSize + exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (heven : modulusLastByteParity
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize modulusSize = ⟨0⟩)
    (hnorm :
      operandModulusPtr baseSize exponentSize + 32 <
        barrettScanStop
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          (operandModulusPtr baseSize exponentSize) modulusSize)
    (hfp : 96 ≤ fp)
    (hbound : fp + bytesAllocationSize
      (barrettNormalizedLen
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize) < 2 ^ 64)
    (hmemSize : 96 ≤ (wideWordResultMemory I baseSize exponentSize modulusSize).size)
    (hmemLe : (wideWordResultMemory I baseSize exponentSize modulusSize).size ≤ fp)
    (hgap : fp - (wideWordResultMemory I baseSize exponentSize modulusSize).size <
      USize.size)
    (haw3 : 3 ≤ (wideWordResultWords baseSize exponentSize modulusSize).toNat)
    (haw64 : ¬ (⟨64⟩ : UInt256) ≥
      (wideWordResultWords baseSize exponentSize modulusSize) * ⟨32⟩)
    (hread :
      (wideWordResultMemory I baseSize exponentSize modulusSize).readWithPadding 64 32 =
        UInt256.toByteArray (UInt256.ofNat fp))
    (hfp32Word : fp + 32 < UInt256.size)
    (hnormLenPos : 0 <
      barrettNormalizedLen
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize)
    (hnormLenWord :
      barrettNormalizedLen
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize < UInt256.size)
    (hnormLenLe32 :
      barrettNormalizedLen
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize ≤ 32)
    (hmodAccess :
      (UInt256.ofNat fp).toNat + 32 ≤
        32 * (barrettNormalizedAw
          (wideWordResultWords baseSize exponentSize modulusSize)
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          fp (operandModulusPtr baseSize exponentSize) modulusSize).toNat)
    (hlength :
      wideLoadWord
        (barrettNormalizedMem
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          fp (operandModulusPtr baseSize exponentSize) modulusSize)
        (barrettNormalizedAw
          (wideWordResultWords baseSize exponentSize modulusSize)
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          fp (operandModulusPtr baseSize exponentSize) modulusSize)
        (UInt256.ofNat fp) =
          UInt256.ofNat
            (barrettNormalizedLen
              (wideWordResultMemory I baseSize exponentSize modulusSize)
              (wideWordResultWords baseSize exponentSize modulusSize)
              (operandModulusPtr baseSize exponentSize) modulusSize))
    (hresultFp : 96 ≤ resultFp)
    (hresultBound :
      resultFp + bytesAllocationSize
        (barrettNormalizedLen
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          (operandModulusPtr baseSize exponentSize) modulusSize) < 2 ^ 64)
    (hresultMemSize :
      96 ≤
        (barrettNormalizedMem
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          fp (operandModulusPtr baseSize exponentSize) modulusSize).size)
    (hresultMemLe :
      (barrettNormalizedMem
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        fp (operandModulusPtr baseSize exponentSize) modulusSize).size ≤ resultFp)
    (hresultGap :
      resultFp -
        (barrettNormalizedMem
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          fp (operandModulusPtr baseSize exponentSize) modulusSize).size < USize.size)
    (hresultAw3 :
      3 ≤
        (barrettNormalizedAw
          (wideWordResultWords baseSize exponentSize modulusSize)
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          fp (operandModulusPtr baseSize exponentSize) modulusSize).toNat)
    (hresultAw64 :
      ¬ (⟨64⟩ : UInt256) ≥
        (barrettNormalizedAw
          (wideWordResultWords baseSize exponentSize modulusSize)
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          fp (operandModulusPtr baseSize exponentSize) modulusSize) * ⟨32⟩)
    (hresultRead :
      (barrettNormalizedMem
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        fp (operandModulusPtr baseSize exponentSize) modulusSize).readWithPadding 64 32 =
          UInt256.toByteArray (UInt256.ofNat resultFp))
    (hchecksBound :
      fp + 32 +
        barrettNormalizedLen
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          (operandModulusPtr baseSize exponentSize) modulusSize + 32 < UInt256.size)
    (hchecksActive :
      fp + 32 +
        barrettNormalizedLen
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          (operandModulusPtr baseSize exponentSize) modulusSize + 32 ≤
        32 * (barrettNormalizedResultAw
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          fp (operandModulusPtr baseSize exponentSize) modulusSize resultFp).toNat)
    (hchecksAw :
      32 * (barrettNormalizedResultAw
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        fp (operandModulusPtr baseSize exponentSize) modulusSize resultFp).toNat <
          UInt256.size)
    (hlengthAfterResult :
      wideLoadWord
        (barrettNormalizedResultMem
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          fp (operandModulusPtr baseSize exponentSize) modulusSize resultFp)
        (barrettNormalizedResultAw
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          fp (operandModulusPtr baseSize exponentSize) modulusSize resultFp)
        (UInt256.ofNat fp) =
          UInt256.ofNat
            (barrettNormalizedLen
              (wideWordResultMemory I baseSize exponentSize modulusSize)
              (wideWordResultWords baseSize exponentSize modulusSize)
              (operandModulusPtr baseSize exponentSize) modulusSize))
    (hzero :
      memoryZeroResult
        (barrettNormalizedResultMem
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          fp (operandModulusPtr baseSize exponentSize) modulusSize resultFp)
        (barrettNormalizedResultAw
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          fp (operandModulusPtr baseSize exponentSize) modulusSize resultFp)
        (fp + 32)
        (fp + 32 +
          barrettNormalizedLen
            (wideWordResultMemory I baseSize exponentSize modulusSize)
            (wideWordResultWords baseSize exponentSize modulusSize)
            (operandModulusPtr baseSize exponentSize) modulusSize) = 0)
    (hone :
      memoryOneResult
        (barrettNormalizedResultMem
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          fp (operandModulusPtr baseSize exponentSize) modulusSize resultFp)
        (barrettNormalizedResultAw
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          fp (operandModulusPtr baseSize exponentSize) modulusSize resultFp)
        fp
        (barrettNormalizedLen
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          (operandModulusPtr baseSize exponentSize) modulusSize) = 0)
    (hfpEndWord :
      fp +
        barrettNormalizedLen
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          (operandModulusPtr baseSize exponentSize) modulusSize + 31 < UInt256.size)
    (hfpActive :
      fp + 64 ≤
        32 * (barrettNormalizedResultAw
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          fp (operandModulusPtr baseSize exponentSize) modulusSize resultFp).toNat)
    (hfirst :
      barrettNormalizedLen
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize = 1 ∨
      UInt256.byteAt ⟨0⟩
        (wideLoadWord
          (barrettNormalizedResultMem
            (wideWordResultMemory I baseSize exponentSize modulusSize)
            (wideWordResultWords baseSize exponentSize modulusSize)
            fp (operandModulusPtr baseSize exponentSize) modulusSize resultFp)
          (barrettNormalizedResultAw
            (wideWordResultMemory I baseSize exponentSize modulusSize)
            (wideWordResultWords baseSize exponentSize modulusSize)
            fp (operandModulusPtr baseSize exponentSize) modulusSize resultFp)
          (UInt256.ofNat (fp + 32))) ≠ ⟨0⟩)
    (hbaseLength :
      wideLoadWord
        (barrettNormalizedResultMem
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          fp (operandModulusPtr baseSize exponentSize) modulusSize resultFp)
        (barrettNormalizedResultAw
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          fp (operandModulusPtr baseSize exponentSize) modulusSize resultFp)
        (UInt256.ofNat operandBasePtr) = UInt256.ofNat baseSize)
    (hexponentLength :
      wideLoadWord
        (barrettNormalizedResultMem
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          fp (operandModulusPtr baseSize exponentSize) modulusSize resultFp)
        (barrettNormalizedResultAw
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          fp (operandModulusPtr baseSize exponentSize) modulusSize resultFp)
        (UInt256.ofNat (operandExponentPtr baseSize)) = UInt256.ofNat exponentSize)
    (hbaseActive :
      operandBasePtr + 32 + baseSize ≤
        32 * (barrettNormalizedResultAw
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          fp (operandModulusPtr baseSize exponentSize) modulusSize resultFp).toNat)
    (hbaseDataActive :
      operandBasePtr + 64 ≤
        32 * (barrettNormalizedResultAw
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          fp (operandModulusPtr baseSize exponentSize) modulusSize resultFp).toNat)
    (hexponentActive :
      wideExponentDataPtr baseSize + exponentSize + 32 ≤
        32 * (barrettNormalizedResultAw
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          fp (operandModulusPtr baseSize exponentSize) modulusSize resultFp).toNat)
    (hresultFpWord : resultFp + 32 < UInt256.size)
    (hresultPayloadActive :
      resultFp + 32 +
        barrettNormalizedLen
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          (operandModulusPtr baseSize exponentSize) modulusSize ≤
        32 * (barrettNormalizedResultAw
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          fp (operandModulusPtr baseSize exponentSize) modulusSize resultFp).toNat)
    (hresultOffsetWord :
      operandFreePtr baseSize exponentSize modulusSize +
        barrettNormalizedOffset
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          (operandModulusPtr baseSize exponentSize) modulusSize < UInt256.size)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (htail : tail.length ≤ 993)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1183⟩
      (UInt256.ofNat operandBasePtr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat ret :: tail)
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      ByteArray.empty acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat ret)
      (UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize) :: tail)
      (barrettRestoreMemory
        (wideWordReturnMemory
          (barrettNormalizedResultMem
            (wideWordResultMemory I baseSize exponentSize modulusSize)
            (wideWordResultWords baseSize exponentSize modulusSize)
            fp (operandModulusPtr baseSize exponentSize) modulusSize resultFp)
          (wideWordValueAtModulusPtr
            (barrettNormalizedResultMem
              (wideWordResultMemory I baseSize exponentSize modulusSize)
              (wideWordResultWords baseSize exponentSize modulusSize)
              fp (operandModulusPtr baseSize exponentSize) modulusSize resultFp)
            (barrettNormalizedResultAw
              (wideWordResultMemory I baseSize exponentSize modulusSize)
              (wideWordResultWords baseSize exponentSize modulusSize)
              fp (operandModulusPtr baseSize exponentSize) modulusSize resultFp)
            baseSize exponentSize fp
            (barrettNormalizedLen
              (wideWordResultMemory I baseSize exponentSize modulusSize)
              (wideWordResultWords baseSize exponentSize modulusSize)
              (operandModulusPtr baseSize exponentSize) modulusSize))
          (UInt256.ofNat resultFp)
          (barrettNormalizedLen
            (wideWordResultMemory I baseSize exponentSize modulusSize)
            (wideWordResultWords baseSize exponentSize modulusSize)
            (operandModulusPtr baseSize exponentSize) modulusSize))
        resultFp (operandFreePtr baseSize exponentSize modulusSize)
        (barrettNormalizedOffset
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          (operandModulusPtr baseSize exponentSize) modulusSize)
        (barrettNormalizedLen
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          (operandModulusPtr baseSize exponentSize) modulusSize))
      (barrettRestoreWords
        (barrettNormalizedResultAw
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          fp (operandModulusPtr baseSize exponentSize) modulusSize resultFp)
        resultFp (operandFreePtr baseSize exponentSize modulusSize)
        (barrettNormalizedOffset
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          (operandModulusPtr baseSize exponentSize) modulusSize)
        (barrettNormalizedLen
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          (operandModulusPtr baseSize exponentSize) modulusSize))
      ByteArray.empty acc k'
        (C + preparedBarrettNormalizedWordGasFromAw I
          (operandModulusActiveWords baseSize exponentSize modulusSize)
          baseSize exponentSize modulusSize fp resultFp) := by
  obtain ⟨kPrefix, rd1592⟩ := runPreparedBarrettPrefixExactAny
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (ret := ret) (tail := tail)
    hb he hmodPos (by omega) hmod hcalldata heven (by omega) rd0
  let mem0 := wideWordResultMemory I baseSize exponentSize modulusSize
  let aw0 := wideWordResultWords baseSize exponentSize modulusSize
  let p := operandModulusPtr baseSize exponentSize
  let result := operandFreePtr baseSize exponentSize modulusSize
  obtain ⟨kNorm, rd1271⟩ := reachBarrettNormalizedWordRestore
    (baseSize := baseSize) (exponentSize := exponentSize)
    (p := p) (m := modulusSize) (retBar := 1271) (result := result)
    (ret := ret) (fp := fp) (resultFp := resultFp) (tail := tail)
    (mem := mem0) (aw := aw0)
    hb he hmodPos (by omega) (by
      dsimp only [p]
      apply lt_of_le_of_lt
        (show operandModulusPtr baseSize exponentSize + 32 ≤ 2304 by
          unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
          omega)
        (by decide))
    (by
      dsimp only [p]
      apply lt_of_le_of_lt
        (show operandModulusPtr baseSize exponentSize + modulusSize + 31 ≤ 2303 by
          unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
          omega)
        (by decide))
    (by
      dsimp only [p, aw0]
      have hawNat : (wideWordResultWords baseSize exponentSize modulusSize).toNat =
          operandModulusWords baseSize exponentSize modulusSize +
            bytesAllocationWords modulusSize := by
        rw [wideWordResultWords_eq hb he (by omega)]
        exact UInt256.toNat_ofNat_of_lt (by
          apply lt_of_le_of_lt
            (show operandModulusWords baseSize exponentSize modulusSize +
                bytesAllocationWords modulusSize ≤ 137 by
              unfold operandModulusWords operandExponentWords operandBaseWords
                bytesAllocationWords
              omega)
            (by decide))
      rw [hawNat, operandModulusPtr_eq]
      unfold operandModulusWords bytesAllocationWords
      have hround : 1 ≤ (modulusSize + 31) / 32 := by omega
      omega)
    (by simpa [p, mem0, aw0] using hnorm)
    hfp hbound hmemSize hmemLe hgap haw3 haw64 hread hcalldata hfp32Word
    hnormLenPos hnormLenWord hnormLenLe32 hmodAccess hlength hresultFp
    hresultBound hresultMemSize hresultMemLe hresultGap hresultAw3 hresultAw64
    hresultRead hchecksBound hchecksActive hchecksAw hlengthAfterResult hzero hone
    hfpEndWord hfpActive hfirst hbaseLength hexponentLength hbaseActive
    hbaseDataActive hexponentActive hresultFpWord hresultPayloadActive
    hresultOffsetWord jumpDest_1271_barrett htail
    (by simpa [p, result, mem0, aw0] using rd1592)
  have hd := barrettReturnDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2⟩
  have rdRet := evm_run rd1271 with [known jumpdest h0, known swap1 h1, known jump h2 hret]
  refine ⟨_, rdRet.withIndices rfl ?_⟩
  unfold preparedBarrettNormalizedWordGasFromAw
  dsimp only [mem0, aw0, p, result]
  omega

/-- Complete exact execution of the even-modulus Barrett one-word direct-scan path from the
prepared operand arrays to the caller's return point.  This covers the subcase where the modulus
payload has no leading zero byte to normalize, or its length is exactly one byte. -/
theorem runPreparedBarrettDirectWordExactAny
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize ret : Nat} {tail : List UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 32)
    (hmod : 1 < Model.bytesToNatPadded I.calldata
      (96 + baseSize + exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (heven : modulusLastByteParity
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize modulusSize = ⟨0⟩)
    (hfirst :
      modulusSize = 1 ∨
      UInt256.byteAt ⟨0⟩
        (wideLoadWord
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          (UInt256.ofNat (operandModulusPtr baseSize exponentSize + 32))) ≠ ⟨0⟩)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (htail : tail.length ≤ 997)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1183⟩
      (UInt256.ofNat operandBasePtr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat ret :: tail)
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      ByteArray.empty acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat ret)
      (UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize) :: tail)
      (wideWordReturnMemory
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordValue I baseSize exponentSize modulusSize)
        (UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize)) modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize)
      ByteArray.empty acc k'
        (C + preparedBarrettDirectWordGasFromAw I
          (operandModulusActiveWords baseSize exponentSize modulusSize)
          baseSize exponentSize modulusSize) := by
  obtain ⟨kPrefix, rd1592⟩ := runPreparedBarrettPrefixExactAny
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (ret := ret) (tail := tail)
    hb he hmodPos (by omega) hmod hcalldata heven (by omega) rd0
  let p := operandModulusPtr baseSize exponentSize
  let result := operandFreePtr baseSize exponentSize modulusSize
  have hp32 : p + 32 < UInt256.size := by
    apply lt_of_le_of_lt
      (show p + 32 ≤ 2304 by
        unfold p operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
      (by decide)
  have hpend : p + modulusSize + 31 < UInt256.size := by
    apply lt_of_le_of_lt
      (show p + modulusSize + 31 ≤ 2303 by
        unfold p operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
      (by decide)
  have hawNat : (wideWordResultWords baseSize exponentSize modulusSize).toNat =
      operandModulusWords baseSize exponentSize modulusSize +
        bytesAllocationWords modulusSize := by
    rw [wideWordResultWords_eq hb he (by omega)]
    exact UInt256.toNat_ofNat_of_lt (by
      apply lt_of_le_of_lt
        (show operandModulusWords baseSize exponentSize modulusSize +
            bytesAllocationWords modulusSize ≤ 137 by
          unfold operandModulusWords operandExponentWords operandBaseWords
            bytesAllocationWords
          omega)
        (by decide))
  have hactive : p + 64 ≤
      32 * (wideWordResultWords baseSize exponentSize modulusSize).toNat := by
    rw [hawNat]
    dsimp only [p]
    rw [operandModulusPtr_eq]
    unfold operandModulusWords bytesAllocationWords
    have hround : 1 ≤ (modulusSize + 31) / 32 := by omega
    omega
  obtain ⟨kScan, rd1646⟩ := reachBarrettScanDirect
    (p := p) (m := modulusSize) (retBar := 1271) (result := result)
    (exp := operandExponentPtr baseSize) (base := operandBasePtr) (ret := ret)
    hp32 hpend hactive hfirst (by omega) rd1592
  obtain ⟨kCall, rd2574⟩ := reachBarrettDirectWordHelper
    (p := p) (m := modulusSize) (retBar := 1271) (result := result)
    (exp := operandExponentPtr baseSize) (base := operandBasePtr) (ret := ret)
    hmodPos hm (by omega) rd1646
  have rdHelper := runWideWordHelperAllocatedExact
    (ret := 1271)
    (tail := UInt256.ofNat result :: ⟨1271⟩ :: UInt256.ofNat ret :: tail)
    hb he hmodPos hm jumpDest_1271_barrett
    (by simp only [List.length_cons]; omega) rd2574
  have hd := barrettReturnDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2⟩
  have rd1271again := evm_run rdHelper with [known jumpdest h0, known swap1 h1,
    known jump h2 jumpDest_1271_barrett]
  have rdRet := evm_run rd1271again with [known jumpdest h0, known swap1 h1,
    known jump h2 hret]
  refine ⟨_, rdRet.withIndices rfl ?_⟩
  unfold preparedBarrettDirectWordGasFromAw
  omega

end Modexp
