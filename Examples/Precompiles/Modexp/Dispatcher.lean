import Examples.Precompiles.Modexp.MontgomeryWordCaller

/-!
# Exact parity dispatcher after operand preparation

After the wide-input fast paths fail, the deployed runtime copies the three operands to Solidity
`bytes` arrays and then dispatches to either Barrett or Montgomery according to the low bit of the
last modulus byte.  This file proves the odd branch, which is the branch needed to connect the
completed one-limb Montgomery caller to the prepared-operand state.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxRecDepth 500000
set_option maxHeartbeats 0
set_option Elab.async false

def modulusLastBytePtr (baseSize exponentSize modulusSize : Nat) : Nat :=
  operandModulusPtr baseSize exponentSize + 32 + modulusSize - 1

def modulusLastBytePtrWord (baseSize exponentSize modulusSize : Nat) : UInt256 :=
  UInt256.ofNat 32 +
    (UInt256.ofNat (modulusSize - 1) +
      UInt256.ofNat (operandModulusPtr baseSize exponentSize))

def modulusLastByteWord (mem : ByteArray) (aw : UInt256)
    (baseSize exponentSize modulusSize : Nat) : UInt256 :=
  wideLoadWord mem aw (modulusLastBytePtrWord baseSize exponentSize modulusSize)

def highByteMask : UInt256 :=
  ⟨115339776388732929035197660848497720713218148788040405586178452820382218977280⟩

def modulusLastByteMasked (mem : ByteArray) (aw : UInt256)
    (baseSize exponentSize modulusSize : Nat) : UInt256 :=
  UInt256.shiftRight
    (UInt256.land (modulusLastByteWord mem aw baseSize exponentSize modulusSize) highByteMask)
    ⟨248⟩

def modulusLastByteParity (mem : ByteArray) (aw : UInt256)
    (baseSize exponentSize modulusSize : Nat) : UInt256 :=
  UInt256.land (modulusLastByteMasked mem aw baseSize exponentSize modulusSize) ⟨1⟩

def modulusLastByteMloadAw (aw : UInt256)
    (baseSize exponentSize modulusSize : Nat) : UInt256 :=
  UInt256.ofNat
    (MachineState.M aw.toNat
      (modulusLastBytePtrWord baseSize exponentSize modulusSize).toNat 32)

def modulusLastByteMloadGas (aw : UInt256)
    (baseSize exponentSize modulusSize : Nat) : Nat :=
  Cₘ (modulusLastByteMloadAw aw baseSize exponentSize modulusSize) - Cₘ aw

theorem modulusLastBytePtrWord_toNat
    {baseSize exponentSize modulusSize : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024) :
    (modulusLastBytePtrWord baseSize exponentSize modulusSize).toNat =
      32 + ((modulusSize - 1) + operandModulusPtr baseSize exponentSize) := by
  have hinnerBound :
      (modulusSize - 1) + operandModulusPtr baseSize exponentSize < UInt256.size := by
    apply lt_of_le_of_lt
      (show (modulusSize - 1) + operandModulusPtr baseSize exponentSize ≤ 3295 by
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
      (by decide)
  have houterBound :
      32 + ((modulusSize - 1) + operandModulusPtr baseSize exponentSize) <
        UInt256.size := by
    apply lt_of_le_of_lt
      (show 32 + ((modulusSize - 1) + operandModulusPtr baseSize exponentSize) ≤ 3327 by
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
      (by decide)
  unfold modulusLastBytePtrWord
  have hinner :
      UInt256.ofNat (modulusSize - 1) +
          UInt256.ofNat (operandModulusPtr baseSize exponentSize) =
        UInt256.ofNat ((modulusSize - 1) + operandModulusPtr baseSize exponentSize) := by
    exact ofNat_add_bounded hinnerBound
  have houter :
      UInt256.ofNat 32 +
          UInt256.ofNat ((modulusSize - 1) + operandModulusPtr baseSize exponentSize) =
        UInt256.ofNat
          (32 + ((modulusSize - 1) + operandModulusPtr baseSize exponentSize)) := by
    exact ofNat_add_bounded houterBound
  rw [hinner, houter, UInt256.toNat_ofNat_of_lt houterBound]

theorem not_ge_mul32_of_access {aw off : UInt256}
    (haccess : off.toNat + 32 ≤ 32 * aw.toNat)
    (hNoWrap : aw.toNat * 32 < UInt256.size) :
    ¬ off ≥ aw * ⟨32⟩ := by
  intro hge
  have hmul : (aw * (⟨32⟩ : UInt256)).toNat = aw.toNat * 32 := by
    simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using
      umul_toNat (a := aw) (b := (⟨32⟩ : UInt256)) hNoWrap
  have hnat : (aw * (⟨32⟩ : UInt256)).toNat ≤ off.toNat := hge
  rw [hmul] at hnat
  omega

theorem modulusLastByteMloadAw_bound
    {baseSize exponentSize modulusSize : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 1024) :
    (modulusLastByteMloadAw
        (operandModulusActiveWords baseSize exponentSize modulusSize)
        baseSize exponentSize modulusSize).toNat ≤
      operandModulusWords baseSize exponentSize modulusSize + 1 := by
  have hwordsBound : operandModulusWords baseSize exponentSize modulusSize < UInt256.size := by
    apply lt_of_le_of_lt
      (show operandModulusWords baseSize exponentSize modulusSize ≤ 103 by
        unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
        omega)
      (by decide)
  have hptr := modulusLastBytePtrWord_toNat (baseSize := baseSize)
    (exponentSize := exponentSize) (modulusSize := modulusSize) hb he (by omega)
  unfold modulusLastByteMloadAw operandModulusActiveWords
  rw [UInt256.toNat_ofNat_of_lt hwordsBound, hptr]
  simp only [MachineState.M]
  rw [operandModulusPtr_eq]
  unfold operandModulusWords
  have hnat :
      max (operandExponentWords baseSize exponentSize + bytesAllocationWords modulusSize)
          ((32 + (modulusSize - 1 + 32 * operandExponentWords baseSize exponentSize) +
                32 + 31) / 32) ≤
        operandExponentWords baseSize exponentSize + bytesAllocationWords modulusSize + 1 := by
    unfold bytesAllocationWords
    omega
  exact Nat.le_trans (UInt256.toNat_ofNat_le _) hnat

theorem modulusLastByteMloadAw_ge_operand
    {baseSize exponentSize modulusSize : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 1024) :
    (operandModulusActiveWords baseSize exponentSize modulusSize).toNat ≤
      (modulusLastByteMloadAw
        (operandModulusActiveWords baseSize exponentSize modulusSize)
        baseSize exponentSize modulusSize).toNat := by
  have hwordsBound : operandModulusWords baseSize exponentSize modulusSize < UInt256.size := by
    apply lt_of_le_of_lt
      (show operandModulusWords baseSize exponentSize modulusSize ≤ 103 by
        unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
        omega)
      (by decide)
  have hptr := modulusLastBytePtrWord_toNat (baseSize := baseSize)
    (exponentSize := exponentSize) (modulusSize := modulusSize) hb he (by omega)
  have hinnerLt :
      MachineState.M (operandModulusWords baseSize exponentSize modulusSize)
        (32 + (modulusSize - 1 + operandModulusPtr baseSize exponentSize)) 32 <
        UInt256.size := by
    apply lt_of_le_of_lt
      (show MachineState.M (operandModulusWords baseSize exponentSize modulusSize)
          (32 + (modulusSize - 1 + operandModulusPtr baseSize exponentSize)) 32 ≤
          operandModulusWords baseSize exponentSize modulusSize + 1 by
        simp [MachineState.M]
        unfold operandModulusWords
        rw [operandModulusPtr_eq]
        unfold bytesAllocationWords
        omega)
      (by
        apply lt_of_le_of_lt
          (show operandModulusWords baseSize exponentSize modulusSize + 1 ≤ 104 by
            unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
            omega)
          (by decide))
  unfold modulusLastByteMloadAw operandModulusActiveWords
  rw [UInt256.toNat_ofNat_of_lt hwordsBound, hptr,
    UInt256.toNat_ofNat_of_lt hinnerLt]
  simp only [MachineState.M]
  exact le_max_left _ _

theorem newBytesWords_lastByteMloadAw_eq_result
    {baseSize exponentSize modulusSize : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 1024) :
    newBytesWords
        (modulusLastByteMloadAw
          (operandModulusActiveWords baseSize exponentSize modulusSize)
          baseSize exponentSize modulusSize)
        (operandFreePtr baseSize exponentSize modulusSize) modulusSize =
      wideWordResultWords baseSize exponentSize modulusSize := by
  have hwordsBound : operandModulusWords baseSize exponentSize modulusSize < UInt256.size := by
    apply lt_of_le_of_lt
      (show operandModulusWords baseSize exponentSize modulusSize ≤ 103 by
        unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
        omega)
      (by decide)
  have hptr := modulusLastBytePtrWord_toNat (baseSize := baseSize)
    (exponentSize := exponentSize) (modulusSize := modulusSize) hb he (by omega)
  have hq1 : operandModulusWords baseSize exponentSize modulusSize + 1 < UInt256.size := by
    apply lt_of_le_of_lt
      (show operandModulusWords baseSize exponentSize modulusSize + 1 ≤ 104 by
        unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
        omega)
      (by decide)
  have hq2 :
      operandModulusWords baseSize exponentSize modulusSize +
          bytesAllocationWords modulusSize < UInt256.size := by
    apply lt_of_le_of_lt
      (show operandModulusWords baseSize exponentSize modulusSize +
          bytesAllocationWords modulusSize ≤ 136 by
        unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
        omega)
      (by decide)
  unfold wideWordResultWords newBytesWords newBytesStoreWords modulusLastByteMloadAw
    operandModulusActiveWords
  rw [operandFreePtr_eq, UInt256.toNat_ofNat_of_lt hwordsBound,
    hptr, operandModulusPtr_eq]
  simp only [MachineState.M]
  have hinnerLt :
      max (operandModulusWords baseSize exponentSize modulusSize)
          ((32 + (modulusSize - 1 + 32 * operandExponentWords baseSize exponentSize) +
                32 + 31) / 32) < UInt256.size := by
    apply lt_of_le_of_lt
      (show max (operandModulusWords baseSize exponentSize modulusSize)
          ((32 + (modulusSize - 1 + 32 * operandExponentWords baseSize exponentSize) +
                32 + 31) / 32) ≤
          operandModulusWords baseSize exponentSize modulusSize + 1 by
        unfold operandModulusWords
        unfold bytesAllocationWords
        omega)
      hq1
  rw [UInt256.toNat_ofNat_of_lt hinnerLt]
  have hstoreLeft :
      max
          (max (operandModulusWords baseSize exponentSize modulusSize)
            ((32 + (modulusSize - 1 + 32 * operandExponentWords baseSize exponentSize) +
                  32 + 31) / 32))
          ((32 * operandModulusWords baseSize exponentSize modulusSize + 32 + 31) / 32) =
        operandModulusWords baseSize exponentSize modulusSize + 1 := by
    unfold operandModulusWords
    unfold bytesAllocationWords
    omega
  have hstoreRight :
      max (operandModulusWords baseSize exponentSize modulusSize)
          ((32 * operandModulusWords baseSize exponentSize modulusSize + 32 + 31) / 32) =
        operandModulusWords baseSize exponentSize modulusSize + 1 := by
    omega
  rw [hstoreLeft, hstoreRight, UInt256.toNat_ofNat_of_lt hq1]

private theorem dispatcherDecodesA :
    [decode runtimeBytecode ⟨1183⟩, decode runtimeBytecode ⟨1184⟩,
      decode runtimeBytecode ⟨1185⟩, decode runtimeBytecode ⟨1186⟩,
      decode runtimeBytecode ⟨1187⟩, decode runtimeBytecode ⟨1188⟩,
      decode runtimeBytecode ⟨1189⟩, decode runtimeBytecode ⟨1192⟩,
      decode runtimeBytecode ⟨1193⟩, decode runtimeBytecode ⟨1194⟩,
      decode runtimeBytecode ⟨1195⟩, decode runtimeBytecode ⟨1196⟩,
      decode runtimeBytecode ⟨1197⟩, decode runtimeBytecode ⟨1198⟩,
      decode runtimeBytecode ⟨1199⟩, decode runtimeBytecode ⟨1200⟩,
      decode runtimeBytecode ⟨1201⟩, decode runtimeBytecode ⟨1202⟩,
      decode runtimeBytecode ⟨1205⟩] =
    [some (.JUMPDEST, .none), some (.SWAP2, .none), some (.SWAP1, .none),
      some (.DUP2, .none), some (.MLOAD, .none), some (.ISZERO, .none),
      some (.Push .PUSH2, some (⟨1283⟩, 2)), some (.JUMPI, .none),
      some (.DUP2, .none), some (.MLOAD, .none), some (.PUSH0, .none),
      some (.NOT, .none), some (.DUP2, .none), some (.ADD, .none),
      some (.SWAP1, .none), some (.DUP2, .none), some (.GT, .none),
      some (.Push .PUSH2, some (⟨1037⟩, 2)), some (.JUMPI, .none)] := by
  native_decide

private theorem dispatcherDecodesB :
    [decode runtimeBytecode ⟨1206⟩, decode runtimeBytecode ⟨1208⟩,
      decode runtimeBytecode ⟨1241⟩, decode runtimeBytecode ⟨1244⟩,
      decode runtimeBytecode ⟨1245⟩, decode runtimeBytecode ⟨1246⟩,
      decode runtimeBytecode ⟨1247⟩, decode runtimeBytecode ⟨1250⟩,
      decode runtimeBytecode ⟨1251⟩, decode runtimeBytecode ⟨1252⟩,
      decode runtimeBytecode ⟨1253⟩, decode runtimeBytecode ⟨1254⟩,
      decode runtimeBytecode ⟨1256⟩, decode runtimeBytecode ⟨1257⟩,
      decode runtimeBytecode ⟨1258⟩, decode runtimeBytecode ⟨1259⟩,
      decode runtimeBytecode ⟨1262⟩, decode runtimeBytecode ⟨1263⟩,
      decode runtimeBytecode ⟨1266⟩, decode runtimeBytecode ⟨1267⟩,
      decode runtimeBytecode ⟨1270⟩] =
    [some (.Push .PUSH1, some (⟨1⟩, 1)),
      some (.Push .PUSH32,
      some (highByteMask, 32)),
      some (.Push .PUSH2, some (⟨1251⟩, 2)), some (.DUP3, .none),
      some (.SWAP4, .none), some (.DUP7, .none),
      some (.Push .PUSH2, some (⟨1161⟩, 2)), some (.JUMP, .none),
      some (.JUMPDEST, .none), some (.MLOAD, .none), some (.AND, .none),
      some (.Push .PUSH1, some (⟨248⟩, 1)), some (.SHR, .none),
      some (.AND, .none), some (.SUB, .none),
      some (.Push .PUSH2, some (⟨1274⟩, 2)), some (.JUMPI, .none),
      some (.Push .PUSH2, some (⟨1271⟩, 2)), some (.SWAP3, .none),
      some (.Push .PUSH2, some (⟨1925⟩, 2)), some (.JUMP, .none)] := by
  native_decide

private theorem dispatcherEvenReturnDecodes :
    [decode runtimeBytecode ⟨1274⟩, decode runtimeBytecode ⟨1275⟩,
      decode runtimeBytecode ⟨1278⟩, decode runtimeBytecode ⟨1279⟩,
      decode runtimeBytecode ⟨1282⟩] =
    [some (.JUMPDEST, .none), some (.Push .PUSH2, some (⟨1271⟩, 2)),
      some (.SWAP3, .none), some (.Push .PUSH2, some (⟨1549⟩, 2)),
      some (.JUMP, .none)] := by
  native_decide

private theorem barrettEntryDecodes :
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

private theorem lastBytePtrDecodes :
    [decode runtimeBytecode ⟨1161⟩, decode runtimeBytecode ⟨1162⟩,
      decode runtimeBytecode ⟨1163⟩, decode runtimeBytecode ⟨1164⟩,
      decode runtimeBytecode ⟨1165⟩, decode runtimeBytecode ⟨1166⟩,
      decode runtimeBytecode ⟨1167⟩, decode runtimeBytecode ⟨1168⟩,
      decode runtimeBytecode ⟨1171⟩, decode runtimeBytecode ⟨1172⟩,
      decode runtimeBytecode ⟨1173⟩, decode runtimeBytecode ⟨1175⟩,
      decode runtimeBytecode ⟨1176⟩, decode runtimeBytecode ⟨1177⟩] =
    [some (.JUMPDEST, .none), some (.SWAP1, .none), some (.DUP2, .none),
      some (.MLOAD, .none), some (.DUP2, .none), some (.LT, .none),
      some (.ISZERO, .none), some (.Push .PUSH2, some (⟨1178⟩, 2)),
      some (.JUMPI, .none), some (.ADD, .none),
      some (.Push .PUSH1, some (⟨32⟩, 1)), some (.ADD, .none),
      some (.SWAP1, .none), some (.JUMP, .none)] := by
  native_decide

private theorem jumpDest_1161 :
    (D_J runtimeBytecode 0).contains ⟨1161⟩ = true := by native_decide

private theorem jumpDest_1251 :
    (D_J runtimeBytecode 0).contains ⟨1251⟩ = true := by native_decide

private theorem jumpDest_1274 :
    (D_J runtimeBytecode 0).contains ⟨1274⟩ = true := by native_decide

private theorem jumpDest_1549_dispatcher :
    (D_J runtimeBytecode 0).contains ⟨1549⟩ = true := by native_decide

private theorem jumpDest_1570_dispatcher :
    (D_J runtimeBytecode 0).contains ⟨1570⟩ = true := by native_decide

private theorem jumpDest_1925_dispatcher :
    (D_J runtimeBytecode 0).contains ⟨1925⟩ = true := by native_decide

private theorem jumpDest_1283_dispatcher :
    (D_J runtimeBytecode 0).contains ⟨1283⟩ = true := by native_decide

private theorem jumpDest_1296_dispatcher :
    (D_J runtimeBytecode 0).contains ⟨1296⟩ = true := by native_decide

private theorem jumpDest_485_dispatcher :
    (D_J runtimeBytecode 0).contains ⟨485⟩ = true := by native_decide

private theorem ofNat_add_lnot_zero {n : Nat} (hpos : 0 < n) (hn : n < UInt256.size) :
    UInt256.ofNat n + UInt256.lnot ⟨0⟩ = UInt256.ofNat (n - 1) := by
  apply u256_inj
  rw [uadd_toNat, UInt256.toNat_ofNat_of_lt hn,
    UInt256.toNat_ofNat_of_lt (by omega : n - 1 < UInt256.size)]
  have hnot : (UInt256.lnot ⟨0⟩).toNat = UInt256.size - 1 := by native_decide
  rw [hnot]
  have hsum : n + (UInt256.size - 1) = (n - 1) + UInt256.size := by omega
  rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : n - 1 < UInt256.size)]

private theorem ofNat_add3_bounded {a b c : Nat} (h : a + b + c < UInt256.size) :
    UInt256.ofNat a + UInt256.ofNat b + UInt256.ofNat c =
      UInt256.ofNat (a + b + c) := by
  rw [ofNat_add_bounded (by omega : a + b < UInt256.size)]
  rw [ofNat_add_bounded h]

private theorem land_one_eq_one {e : UInt256} (hodd : e.toNat % 2 = 1) :
    UInt256.land e ⟨1⟩ = ⟨1⟩ := by
  apply u256_inj
  rw [uInt256_land_one_toNat, hodd]
  rfl

private theorem gt_pred_self_zero {n : Nat} (hpos : 0 < n) (hn : n < UInt256.size) :
    UInt256.gt (UInt256.ofNat (n - 1)) (UInt256.ofNat n) = ⟨0⟩ := by
  apply ugt_zero
  rw [UInt256.toNat_ofNat_of_lt (by omega : n - 1 < UInt256.size),
    UInt256.toNat_ofNat_of_lt hn]
  omega

private theorem lt_pred_self_one {n : Nat} (hpos : 0 < n) (hn : n < UInt256.size) :
    UInt256.lt (UInt256.ofNat (n - 1)) (UInt256.ofNat n) = ⟨1⟩ := by
  apply ult_one
  rw [UInt256.toNat_ofNat_of_lt (by omega : n - 1 < UInt256.size),
    UInt256.toNat_ofNat_of_lt hn]
  omega

theorem reachDispatcherNonemptyHead
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 1024)
    (hmodHeaderAccess :
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)).toNat + 32 ≤
        32 * aw.toNat)
    (hmodLength : wideLoadWord mem aw
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)) =
        UInt256.ofNat modulusSize)
    (htail : tail.length ≤ 1008)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1183⟩
      (UInt256.ofNat operandBasePtr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1206⟩
      (UInt256.ofNat (modulusSize - 1) ::
        UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat operandBasePtr :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k' (C + 68) := by
  have ha := dispatcherDecodesA
  simp only [List.cons.injEq, and_true] at ha
  rcases ha with ⟨a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18⟩
  have hmodSizeLt : modulusSize < UInt256.size :=
    lt_of_le_of_lt hm (by decide)
  have hmodWordNe : UInt256.ofNat modulusSize ≠ ⟨0⟩ := by
    intro hz
    have hzNat := congrArg UInt256.toNat hz
    rw [UInt256.toNat_ofNat_of_lt hmodSizeLt] at hzNat
    simp at hzNat
    omega
  have rd1187 := evm_run rd0 with [known jumpdest a0, known swap2 a1,
    known swap1 a2, known dup2 a3]
  have rd1188raw := RDx.mloadWithin rd1187 a4 hmodHeaderAccess
    (by simp only [List.length_cons]; omega)
  rw [hmodLength] at rd1188raw
  have hlenNZ := isZero_eq_zero_of_ne hmodWordNe
  have rd1193 := evm_run rd1188raw with [known iszero a5,
    known push2 a6 ⟨1283⟩, known jumpiNT a7 hlenNZ]
  have rd1195raw := evm_run rd1193 with [known dup2 a8]
  have rd1195m := RDx.mloadWithin rd1195raw a9 hmodHeaderAccess
    (by simp only [List.length_cons]; omega)
  rw [hmodLength] at rd1195m
  have rd1201raw := evm_run rd1195m with [known push0 a10, known not a11,
    known dup2 a12, known add a13]
  have hpred : UInt256.ofNat modulusSize + UInt256.lnot ⟨0⟩ =
      UInt256.ofNat (modulusSize - 1) :=
    ofNat_add_lnot_zero hmodPos hmodSizeLt
  rw [hpred] at rd1201raw
  have hgt := gt_pred_self_zero hmodPos hmodSizeLt
  have rd1206 := evm_run rd1201raw with [known swap1 a14, known dup2 a15,
    known gt a16, known push2 a17 ⟨1037⟩,
    known jumpiNT a18 (by rw [hgt])]
  exact ⟨_, (rd1206.withPC (by native_decide)).withIndices rfl (by omega)⟩

def preparedZeroModulusLengthReturnGasFromAw (aw : UInt256)
    (baseSize exponentSize : Nat) : Nat :=
  let fp := operandFreePtr baseSize exponentSize 0
  29 + 24 + 82 + newBytesStoreExpansionGas aw fp + 37

private theorem dispatcherEmptyReturnDecodes :
    [decode runtimeBytecode ⟨1283⟩, decode runtimeBytecode ⟨1284⟩,
      decode runtimeBytecode ⟨1285⟩, decode runtimeBytecode ⟨1286⟩,
      decode runtimeBytecode ⟨1287⟩, decode runtimeBytecode ⟨1290⟩,
      decode runtimeBytecode ⟨1292⟩, decode runtimeBytecode ⟨1295⟩,
      decode runtimeBytecode ⟨1296⟩, decode runtimeBytecode ⟨1297⟩,
      decode runtimeBytecode ⟨1298⟩, decode runtimeBytecode ⟨1299⟩,
      decode runtimeBytecode ⟨1300⟩, decode runtimeBytecode ⟨1301⟩,
      decode runtimeBytecode ⟨1302⟩, decode runtimeBytecode ⟨1304⟩,
      decode runtimeBytecode ⟨1305⟩, decode runtimeBytecode ⟨1306⟩,
      decode runtimeBytecode ⟨1307⟩, decode runtimeBytecode ⟨1308⟩] =
    [some (.JUMPDEST, .none), some (.POP, .none), some (.POP, .none),
      some (.POP, .none), some (.Push .PUSH2, some (⟨1296⟩, 2)),
      some (.Push .PUSH1, some (⟨32⟩, 1)),
      some (.Push .PUSH2, some (⟨485⟩, 2)), some (.JUMP, .none),
      some (.JUMPDEST, .none), some (.PUSH0, .none), some (.DUP1, .none),
      some (.DUP3, .none), some (.MSTORE, .none), some (.CALLDATASIZE, .none),
      some (.Push .PUSH1, some (⟨32⟩, 1)), some (.DUP4, .none),
      some (.ADD, .none), some (.CALLDATACOPY, .none), some (.SWAP1, .none),
      some (.JUMP, .none)] := by
  native_decide

/-- From prepared operand arrays, if the declared modulus byte length is zero, the dispatcher
allocates an empty Solidity `bytes` object and returns its pointer to the caller. -/
theorem runPreparedZeroModulusLengthReturnExactAny
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize ret : Nat} {tail : List UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (htail : tail.length ≤ 1008)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1183⟩
      (UInt256.ofNat operandBasePtr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat ret :: tail)
      (operandCopiedMemory I baseSize exponentSize 0)
      (operandModulusActiveWords baseSize exponentSize 0)
      ByteArray.empty acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat ret)
      (UInt256.ofNat (operandFreePtr baseSize exponentSize 0) :: tail)
      (wideWordResultMemory I baseSize exponentSize 0)
      (wideWordResultWords baseSize exponentSize 0)
      ByteArray.empty acc k'
        (C + preparedZeroModulusLengthReturnGasFromAw
          (operandModulusActiveWords baseSize exponentSize 0) baseSize exponentSize) := by
  let aw0 := operandModulusActiveWords baseSize exponentSize 0
  let fp := operandFreePtr baseSize exponentSize 0
  let mem0 := operandCopiedMemory I baseSize exponentSize 0
  have ha := dispatcherDecodesA
  simp only [List.cons.injEq, and_true] at ha
  rcases ha with ⟨a0,a1,a2,a3,a4,a5,a6,a7,_a8,_a9,_a10,_a11,_a12,_a13,
    _a14,_a15,_a16,_a17,_a18⟩
  have hd := dispatcherEmptyReturnDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨d0,d1,d2,d3,d4,d5,d6,d7,d8,d9,d10,d11,d12,d13,d14,d15,
    d16,d17,d18,d19⟩
  have hmodHeaderAccess :
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)).toNat + 32 ≤
        32 * aw0.toNat := by
    dsimp only [aw0]
    rw [UInt256.toNat_ofNat_of_lt (by
      apply lt_of_le_of_lt
        (show operandModulusPtr baseSize exponentSize ≤ 2272 by
          unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
          omega)
        (by decide))]
    unfold operandModulusActiveWords
    rw [UInt256.toNat_ofNat_of_lt (by
      apply lt_of_le_of_lt
        (show operandModulusWords baseSize exponentSize 0 ≤ 72 by
          unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
          omega)
        (by decide))]
    rw [operandModulusPtr_eq]
    unfold operandModulusWords bytesAllocationWords
    omega
  have hmodLength : wideLoadWord mem0 aw0
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)) = UInt256.ofNat 0 := by
    dsimp only [mem0, aw0]
    exact operandCopiedWideLoadModulusLength I
      baseSize exponentSize 0 hb he (by omega)
  have hzeroWord : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := by rfl
  have rd1187 := evm_run rd0 with [known jumpdest a0, known swap2 a1,
    known swap1 a2, known dup2 a3]
  have rd1188raw := RDx.mloadWithin rd1187 a4 hmodHeaderAccess
    (by simp only [List.length_cons]; omega)
  rw [hmodLength, hzeroWord] at rd1188raw
  have rd1283 := evm_run rd1188raw with [known iszero a5,
    known push2 a6 ⟨1283⟩, known jumpiT a7 (by native_decide) jumpDest_1283_dispatcher]
  have rd485raw := evm_run rd1283 with [
    known jumpdest d0, known pop d1, known pop d2, known pop d3,
    known push2 d4 ⟨1296⟩, known push1 d5 ⟨32⟩, known push2 d6 ⟨485⟩,
    known jump d7 jumpDest_485_dispatcher]
  have rd485 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨485⟩
      (UInt256.ofNat (bytesAllocationSize 0) :: ⟨1296⟩ :: UInt256.ofNat ret :: tail)
      mem0 aw0 ByteArray.empty acc (k + 16) (C + 53) := by
    simpa [bytesAllocationSize] using
      (rd485raw.withPC (by native_decide)).withIndices (by omega) (by omega)
  have hfpDef : fp = operandFreePtr baseSize exponentSize 0 := rfl
  have hfpMem : mem0.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp) := by
    dsimp only [mem0, fp]
    exact operandCopiedMemory_read64 I baseSize exponentSize 0 hb he
  have hmem96 : 96 ≤ mem0.size := by
    dsimp only [mem0]
    have hge := operandCopiedMemory_size_ge I baseSize exponentSize 0 hb he
    have hptr : 96 ≤ operandModulusPtr baseSize exponentSize + 32 := by
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega
    exact hptr.trans hge
  have haw3 : 3 ≤ aw0.toNat := by
    dsimp only [aw0]
    unfold operandModulusActiveWords
    rw [UInt256.toNat_ofNat_of_lt (by
      apply lt_of_le_of_lt
        (show operandModulusWords baseSize exponentSize 0 ≤ 72 by
          unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
          omega)
        (by decide))]
    unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
    omega
  have hawNoWrap : aw0.toNat * 32 < UInt256.size := by
    dsimp only [aw0]
    unfold operandModulusActiveWords
    rw [UInt256.toNat_ofNat_of_lt (by
      apply lt_of_le_of_lt
        (show operandModulusWords baseSize exponentSize 0 ≤ 72 by
          unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
          omega)
        (by decide))]
    apply lt_of_le_of_lt
      (show operandModulusWords baseSize exponentSize 0 * 32 ≤ 2304 by
        unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
        omega)
      (by decide)
  have rd1296raw := allocateMemoryExact
    (n := 0) (fp := fp) (ret := 1296) (tail := UInt256.ofNat ret :: tail)
    (mem := mem0) (aw := aw0)
    (by omega : 0 ≤ 1024)
    (by
      dsimp only [fp]
      unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega)
    (by
      dsimp only [fp]
      unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega)
    hmem96 haw3
    (wordMul32_not_le64_of_ge3 haw3 (by simpa [Nat.mul_comm] using hawNoWrap))
    hfpMem (by simp only [List.length_cons]; omega) jumpDest_1296_dispatcher rd485
  have rd1296 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1296⟩
      (UInt256.ofNat fp :: UInt256.ofNat ret :: tail)
      (setFreePtr mem0 (fp + bytesAllocationSize 0)) aw0 ByteArray.empty acc
      (k + 40) (C + 135) := by
    simpa using rd1296raw.withIndices (by omega) (by omega)
  have hfpWord : fp < UInt256.size := by
    dsimp only [fp]
    apply lt_of_le_of_lt
      (show operandFreePtr baseSize exponentSize 0 ≤ 2272 by
        unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
      (by decide)
  have hfp32Word : fp + 32 < UInt256.size := by
    apply lt_of_le_of_lt (by
      dsimp only [fp]
      show operandFreePtr baseSize exponentSize 0 + 32 ≤ 2304
      unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega) (by decide)
  have hcdWord : I.calldata.size < UInt256.size := lt_trans hcalldata (by decide)
  have hresultWords : newBytesStoreWords aw0 fp =
      wideWordResultWords baseSize exponentSize 0 := by
    apply u256_inj
    have haw0Nat : aw0.toNat = operandModulusWords baseSize exponentSize 0 := by
      dsimp only [aw0]
      unfold operandModulusActiveWords
      rw [UInt256.toNat_ofNat_of_lt (by
        apply lt_of_le_of_lt
          (show operandModulusWords baseSize exponentSize 0 ≤ 72 by
            unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
            omega)
          (by decide))]
    have hfpEq : fp = 32 * operandModulusWords baseSize exponentSize 0 := by
      dsimp only [fp]
      exact operandFreePtr_eq baseSize exponentSize 0
    have hnewNat : (newBytesStoreWords aw0 fp).toNat =
        operandModulusWords baseSize exponentSize 0 + 1 := by
      unfold newBytesStoreWords MachineState.M
      rw [haw0Nat, hfpEq]
      have hmax :
          max (operandModulusWords baseSize exponentSize 0)
              ((32 * operandModulusWords baseSize exponentSize 0 + 32 + 31) / 32) =
            operandModulusWords baseSize exponentSize 0 + 1 := by
        omega
      change (UInt256.ofNat
          (max (operandModulusWords baseSize exponentSize 0)
            ((32 * operandModulusWords baseSize exponentSize 0 + 32 + 31) / 32))).toNat =
        operandModulusWords baseSize exponentSize 0 + 1
      rw [hmax]
      rw [UInt256.toNat_ofNat_of_lt (by
        apply lt_of_le_of_lt
          (show operandModulusWords baseSize exponentSize 0 + 1 ≤ 73 by
            unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
            omega)
          (by decide))]
    have hwideNat := wideWordResultWords_toNat hb he (by omega : 0 ≤ 1024)
    rw [hnewNat, hwideNat]
    unfold bytesAllocationWords
    omega
  have hwideMem :
      storeBytesLength (setFreePtr mem0 (fp + bytesAllocationSize 0)) fp 0 =
        wideWordResultMemory I baseSize exponentSize 0 := by
    dsimp only [mem0, fp]
    rfl
  have rd1300pre := evm_run rd1296 with [known jumpdest d8,
    known push0 d9, known dup1 d10, known dup3 d11]
  have rd1300 := RDx.mstore (newBytesStoreExpansionGas aw0 fp)
    (wideWordResultMemory I baseSize exponentSize 0)
    (wideWordResultWords baseSize exponentSize 0) rd1300pre d12
    (by
      intro s hsaw hstk
      simp [newBytesStoreExpansionGas, newBytesStoreWords,
        memoryExpansionCost, memoryExpansionCost.μᵢ', hsaw, hstk]
      rw [UInt256.toNat_ofNat_of_lt hfpWord])
    (by
      rw [UInt256.toNat_ofNat_of_lt hfpWord]
      exact hwideMem.symm)
    (by
      rw [UInt256.toNat_ofNat_of_lt hfpWord]
      exact hresultWords)
    (by simp only [List.length_cons]; omega)
  have rd1306preRaw := evm_run rd1300 with [known calldatasize d13,
    known push1 d14 ⟨32⟩, known dup4 d15, known add d16]
  have hfp32 : UInt256.ofNat fp + ⟨32⟩ = UInt256.ofNat (fp + 32) := by
    apply u256_inj
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt hfpWord,
      show (⟨32⟩ : UInt256).toNat = 32 by decide,
      UInt256.toNat_ofNat_of_lt hfp32Word, Nat.mod_eq_of_lt hfp32Word]
  rw [hfp32] at rd1306preRaw
  have rd1306 := RDx.calldatacopy 0
    (wideWordResultMemory I baseSize exponentSize 0)
    (wideWordResultWords baseSize exponentSize 0) rd1306preRaw d17
    (by
      intro s hsaw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hsaw, hstk]
      rw [UInt256.toNat_ofNat_of_lt hfp32Word]
      rw [show MachineState.M (wideWordResultWords baseSize exponentSize 0).toNat
          (fp + 32) 0 = (wideWordResultWords baseSize exponentSize 0).toNat by
        simp [MachineState.M]]
      rw [u256_ofNat_toNat]
      omega)
    (by
      rw [UInt256.toNat_ofNat_of_lt hfp32Word,
        UInt256.toNat_ofNat_of_lt hcdWord,
        show (⟨0⟩ : UInt256).toNat = 0 by decide]
      rw [byteArray_write_len_zero])
    (by
      simp [MachineState.M]
      exact u256_ofNat_toNat (wideWordResultWords baseSize exponentSize 0))
    (by simp only [List.length_cons]; omega)
  have rdretRaw := evm_run rd1306 with [known swap1 d18, known jump d19 hret]
  refine ⟨_, rdretRaw.withIndices rfl ?_⟩
  unfold preparedZeroModulusLengthReturnGasFromAw
  dsimp only [aw0, fp]
  simp [GasConstants.Gverylow, GasConstants.Gcopy]
  omega

/-- Build the internal call frame for the last-byte pointer helper. -/
theorem reachDispatcherLastBytePtrCall
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (htail : tail.length ≤ 1008)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1206⟩
      (UInt256.ofNat (modulusSize - 1) ::
        UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat operandBasePtr :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1161⟩
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat (modulusSize - 1) :: ⟨1251⟩ ::
        highByteMask ::
        ⟨1⟩ :: ⟨1⟩ :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat operandBasePtr :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k' (C + 29) := by
  have hb := dispatcherDecodesB
  simp only [List.cons.injEq, and_true] at hb
  rcases hb with ⟨b0,b1,b2,b3,b4,b5,b6,b7,_b8,_b9,_b10,_b11,_b12,_b13,_b14,_b15,_b16,_b17,_b18,_b19,_b20⟩
  have rd1208 := RDx.push1 ⟨1⟩ rd0 b0 (by simp only [List.length_cons]; omega)
  have rd1241 := RDx.pushConst rd1208
    highByteMask
    (by decide) b1 (by simp only [List.length_cons]; omega)
  have rd1161 := evm_run rd1241 with [
    known push2 b2 ⟨1251⟩, known dup3 b3, known swap4 b4, known dup7 b5,
    known push2 b6 ⟨1161⟩, known jump b7 jumpDest_1161]
  exact ⟨_, (rd1161.withPC (by native_decide)).withIndices rfl (by omega)⟩

/-- Execute the bounds-check branch of the last-byte pointer helper. -/
theorem reachDispatcherLastBytePtrHelperBranch
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 1024)
    (hmodHeaderAccess :
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)).toNat + 32 ≤
        32 * aw.toNat)
    (hmodLength : wideLoadWord mem aw
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)) =
        UInt256.ofNat modulusSize)
    (htail : tail.length ≤ 1008)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1161⟩
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat (modulusSize - 1) :: ⟨1251⟩ ::
        highByteMask ::
        ⟨1⟩ :: ⟨1⟩ :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat operandBasePtr :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1172⟩
      (UInt256.ofNat (modulusSize - 1) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) :: ⟨1251⟩ ::
        highByteMask ::
        ⟨1⟩ :: ⟨1⟩ :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat operandBasePtr :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k' (C + 32) := by
  have hh := lastBytePtrDecodes
  simp only [List.cons.injEq, and_true] at hh
  rcases hh with ⟨p0,p1,p2,p3,p4,p5,p6,p7,p8,_p9,_p10,_p11,_p12,_p13⟩
  have hmodSizeLt : modulusSize < UInt256.size :=
    lt_of_le_of_lt hm (by decide)
  have rd1165raw := evm_run rd0 with [known jumpdest p0, known swap1 p1,
    known dup2 p2]
  have rd1165m := RDx.mloadWithin rd1165raw p3 hmodHeaderAccess
    (by simp only [List.length_cons]; omega)
  rw [hmodLength] at rd1165m
  have hlt := lt_pred_self_one hmodPos hmodSizeLt
  have rd1172 := evm_run rd1165m with [known dup2 p4, known lt p5,
    known iszero p6, known push2 p7 ⟨1178⟩,
    known jumpiNT p8 (by rw [hlt]; native_decide)]
  exact ⟨_, (rd1172.withPC (by native_decide)).withIndices rfl (by omega)⟩

/-- Finish the last-byte pointer helper by computing `modulus + 32 + modulusSize - 1`. -/
theorem reachDispatcherLastBytePtrHelperReturn
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (htail : tail.length ≤ 1008)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1172⟩
      (UInt256.ofNat (modulusSize - 1) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) :: ⟨1251⟩ ::
        highByteMask ::
        ⟨1⟩ :: ⟨1⟩ :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat operandBasePtr :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1251⟩
      (modulusLastBytePtrWord baseSize exponentSize modulusSize ::
        highByteMask ::
        ⟨1⟩ :: ⟨1⟩ :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat operandBasePtr :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k' (C + 20) := by
  have hh := lastBytePtrDecodes
  simp only [List.cons.injEq, and_true] at hh
  rcases hh with ⟨_p0,_p1,_p2,_p3,_p4,_p5,_p6,_p7,_p8,p9,p10,p11,p12,p13⟩
  have rd1251raw := evm_run rd0 with [known add p9, known push1 p10 ⟨32⟩,
    known add p11, known swap1 p12, known jump p13 jumpDest_1251]
  refine ⟨k + 5, ?_⟩
  simpa [modulusLastBytePtrWord] using
    (rd1251raw.withPC (by native_decide)).withIndices (by omega) (by omega)

/-- Execute the last-byte pointer helper and return to PC 1251. -/
theorem reachDispatcherLastBytePtrHelper
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 1024)
    (hmodHeaderAccess :
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)).toNat + 32 ≤
        32 * aw.toNat)
    (hmodLength : wideLoadWord mem aw
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)) =
        UInt256.ofNat modulusSize)
    (htail : tail.length ≤ 1008)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1161⟩
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat (modulusSize - 1) :: ⟨1251⟩ ::
        highByteMask ::
        ⟨1⟩ :: ⟨1⟩ :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat operandBasePtr :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1251⟩
      (modulusLastBytePtrWord baseSize exponentSize modulusSize ::
        highByteMask ::
        ⟨1⟩ :: ⟨1⟩ :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat operandBasePtr :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k' (C + 52) := by
  obtain ⟨k1, rd1172⟩ := reachDispatcherLastBytePtrHelperBranch
    hmodPos hm hmodHeaderAccess hmodLength htail rd0
  obtain ⟨k2, rd1251⟩ := reachDispatcherLastBytePtrHelperReturn
    htail rd1172
  exact ⟨k2, rd1251.withIndices rfl (by omega)⟩

/-- From PC 1206, compute `modulus + 32 + modulusSize - 1` and return to PC 1251. -/
theorem reachDispatcherLastBytePtr
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 1024)
    (hmodHeaderAccess :
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)).toNat + 32 ≤
        32 * aw.toNat)
    (hmodLength : wideLoadWord mem aw
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)) =
        UInt256.ofNat modulusSize)
    (htail : tail.length ≤ 1008)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1206⟩
      (UInt256.ofNat (modulusSize - 1) ::
        UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat operandBasePtr :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1251⟩
      (modulusLastBytePtrWord baseSize exponentSize modulusSize ::
        highByteMask ::
        ⟨1⟩ :: ⟨1⟩ :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat operandBasePtr :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k' (C + 81) := by
  obtain ⟨k1, rd1161⟩ := reachDispatcherLastBytePtrCall htail rd0
  obtain ⟨k2, rd1251⟩ := reachDispatcherLastBytePtrHelper
    hmodPos hm hmodHeaderAccess hmodLength htail rd1161
  exact ⟨k2, rd1251.withIndices rfl (by omega)⟩

/-- From PC 1251, load the final modulus byte, test oddness, and jump to Montgomery. -/
theorem reachMontgomeryDispatcherOddFinish
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hlastAccess :
      (modulusLastBytePtrWord baseSize exponentSize modulusSize).toNat + 32 ≤
        32 * aw.toNat)
    (hodd : modulusLastByteParity mem aw baseSize exponentSize modulusSize = ⟨1⟩)
    (htail : tail.length ≤ 1008)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1251⟩
      (modulusLastBytePtrWord baseSize exponentSize modulusSize ::
        highByteMask ::
        ⟨1⟩ :: ⟨1⟩ :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat operandBasePtr :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1925⟩
      (UInt256.ofNat operandBasePtr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) :: ⟨1271⟩ ::
        UInt256.ofNat ret :: tail)
      mem aw rdata acc k' (C + 49) := by
  have hb := dispatcherDecodesB
  simp only [List.cons.injEq, and_true] at hb
  rcases hb with ⟨_b0,_b1,_b2,_b3,_b4,_b5,_b6,_b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,b20⟩
  have rd1253raw := evm_run rd0 with [known jumpdest b8]
  have rd1253m := RDx.mloadWithin rd1253raw b9 hlastAccess
    (by simp only [List.length_cons]; omega)
  have rd1262raw := evm_run rd1253m with [known and b10, known push1 b11 ⟨248⟩,
    known shr b12, known and b13, known sub b14, known push2 b15 ⟨1274⟩]
  have hcond :
      UInt256.sub (modulusLastByteParity mem aw baseSize exponentSize modulusSize) ⟨1⟩ = ⟨0⟩ := by
    rw [hodd]
    native_decide
  have hcondRaw :
      UInt256.sub
        (UInt256.land
          (UInt256.shiftRight
            (UInt256.land
              (wideLoadWord mem aw (modulusLastBytePtrWord baseSize exponentSize modulusSize))
              highByteMask)
            ⟨248⟩)
          ⟨1⟩)
        ⟨1⟩ = ⟨0⟩ := by
    simpa [modulusLastByteParity, modulusLastByteMasked, modulusLastByteWord] using hcond
  rw [hcondRaw] at rd1262raw
  have rd1925 := evm_run rd1262raw with [known jumpiNT b16 (by native_decide),
    known push2 b17 ⟨1271⟩, known swap3 b18, known push2 b19 ⟨1925⟩,
    known jump b20 jumpDest_1925_dispatcher]
  exact ⟨_, (rd1925.withPC (by native_decide)).withIndices rfl (by omega)⟩

/-- Variant of `reachMontgomeryDispatcherOddFinish` for the general case where loading the final
modulus byte may expand active memory.  The loaded word is still computed against the pre-load
active frontier, matching the EVM semantics of `MLOAD`; the returned cursor carries the expanded
active-word value and the exact extra memory-expansion gas. -/
theorem reachMontgomeryDispatcherOddFinishAny
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hodd : modulusLastByteParity mem aw baseSize exponentSize modulusSize = ⟨1⟩)
    (htail : tail.length ≤ 1008)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1251⟩
      (modulusLastBytePtrWord baseSize exponentSize modulusSize ::
        highByteMask ::
        ⟨1⟩ :: ⟨1⟩ :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat operandBasePtr :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1925⟩
      (UInt256.ofNat operandBasePtr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) :: ⟨1271⟩ ::
        UInt256.ofNat ret :: tail)
      mem (modulusLastByteMloadAw aw baseSize exponentSize modulusSize) rdata acc k'
        (C + (modulusLastByteMloadGas aw baseSize exponentSize modulusSize + 49)) := by
  have hb := dispatcherDecodesB
  simp only [List.cons.injEq, and_true] at hb
  rcases hb with ⟨_b0,_b1,_b2,_b3,_b4,_b5,_b6,_b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,b20⟩
  have rd1253raw := evm_run rd0 with [known jumpdest b8]
  have rd1253m := RDx.mloadAny rd1253raw b9
    (by simp only [List.length_cons]; omega)
  have rd1262raw := evm_run rd1253m with [known and b10, known push1 b11 ⟨248⟩,
    known shr b12, known and b13, known sub b14, known push2 b15 ⟨1274⟩]
  have hcond :
      UInt256.sub (modulusLastByteParity mem aw baseSize exponentSize modulusSize) ⟨1⟩ = ⟨0⟩ := by
    rw [hodd]
    native_decide
  have hcondRaw :
      UInt256.sub
        (UInt256.land
          (UInt256.shiftRight
            (UInt256.land
              (wideLoadWord mem aw (modulusLastBytePtrWord baseSize exponentSize modulusSize))
              highByteMask)
            ⟨248⟩)
          ⟨1⟩)
        ⟨1⟩ = ⟨0⟩ := by
    simpa [modulusLastByteParity, modulusLastByteMasked, modulusLastByteWord] using hcond
  rw [hcondRaw] at rd1262raw
  have rd1925 := evm_run rd1262raw with [known jumpiNT b16 (by native_decide),
    known push2 b17 ⟨1271⟩, known swap3 b18, known push2 b19 ⟨1925⟩,
    known jump b20 jumpDest_1925_dispatcher]
  refine ⟨_, (rd1925.withPC (by native_decide)).withIndices rfl ?_⟩
  unfold modulusLastByteMloadGas modulusLastByteMloadAw
  omega

/-- Variant for the even branch: loading the final modulus byte may expand active memory, and the
parity test jumps to the Barrett entry at PC 1549. -/
theorem reachBarrettDispatcherEvenFinishAny
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (heven : modulusLastByteParity mem aw baseSize exponentSize modulusSize = ⟨0⟩)
    (htail : tail.length ≤ 1008)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1251⟩
      (modulusLastBytePtrWord baseSize exponentSize modulusSize ::
        highByteMask ::
        ⟨1⟩ :: ⟨1⟩ :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat operandBasePtr :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1549⟩
      (UInt256.ofNat operandBasePtr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) :: ⟨1271⟩ ::
        UInt256.ofNat ret :: tail)
      mem (modulusLastByteMloadAw aw baseSize exponentSize modulusSize) rdata acc k'
        (C + (modulusLastByteMloadGas aw baseSize exponentSize modulusSize + 50)) := by
  have hb := dispatcherDecodesB
  simp only [List.cons.injEq, and_true] at hb
  rcases hb with ⟨_b0,_b1,_b2,_b3,_b4,_b5,_b6,_b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,_b17,_b18,_b19,_b20⟩
  have rd1253raw := evm_run rd0 with [known jumpdest b8]
  have rd1253m := RDx.mloadAny rd1253raw b9
    (by simp only [List.length_cons]; omega)
  have rd1262raw := evm_run rd1253m with [known and b10, known push1 b11 ⟨248⟩,
    known shr b12, known and b13, known sub b14, known push2 b15 ⟨1274⟩]
  have hcond :
      UInt256.sub (modulusLastByteParity mem aw baseSize exponentSize modulusSize) ⟨1⟩ =
        UInt256.sub ⟨0⟩ ⟨1⟩ := by
    rw [heven]
  have hcondRaw :
      UInt256.sub
        (UInt256.land
          (UInt256.shiftRight
            (UInt256.land
              (wideLoadWord mem aw (modulusLastBytePtrWord baseSize exponentSize modulusSize))
              highByteMask)
            ⟨248⟩)
          ⟨1⟩)
        ⟨1⟩ = UInt256.sub ⟨0⟩ ⟨1⟩ := by
    simpa [modulusLastByteParity, modulusLastByteMasked, modulusLastByteWord] using hcond
  rw [hcondRaw] at rd1262raw
  have rd1274 := evm_run rd1262raw with [known jumpiT b16 (by native_decide) jumpDest_1274]
  have hc := dispatcherEvenReturnDecodes
  simp only [List.cons.injEq, and_true] at hc
  rcases hc with ⟨c0,c1,c2,c3,c4⟩
  have rd1549 := evm_run rd1274 with [known jumpdest c0, known push2 c1 ⟨1271⟩,
    known swap3 c2, known push2 c3 ⟨1549⟩, known jump c4 jumpDest_1549_dispatcher]
  refine ⟨_, (rd1549.withPC (by native_decide)).withIndices rfl ?_⟩
  unfold modulusLastByteMloadGas modulusLastByteMloadAw
  omega

/-- The odd branch of the post-copy dispatcher from the final-byte setup point. -/
theorem reachMontgomeryDispatcherOddTail
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 1024)
    (hmodHeaderAccess :
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)).toNat + 32 ≤
        32 * aw.toNat)
    (hlastAccess :
      (modulusLastBytePtrWord baseSize exponentSize modulusSize).toNat + 32 ≤
        32 * aw.toNat)
    (hmodLength : wideLoadWord mem aw
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)) =
        UInt256.ofNat modulusSize)
    (hodd : modulusLastByteParity mem aw baseSize exponentSize modulusSize = ⟨1⟩)
    (htail : tail.length ≤ 1008)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1206⟩
      (UInt256.ofNat (modulusSize - 1) ::
        UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat operandBasePtr :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1925⟩
      (UInt256.ofNat operandBasePtr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) :: ⟨1271⟩ ::
        UInt256.ofNat ret :: tail)
      mem aw rdata acc k' (C + 130) := by
  obtain ⟨k1, rd1251⟩ := reachDispatcherLastBytePtr
    hmodPos hm hmodHeaderAccess hmodLength htail rd0
  obtain ⟨k2, rd1925⟩ := reachMontgomeryDispatcherOddFinish
    hlastAccess hodd htail rd1251
  exact ⟨k2, rd1925.withIndices rfl (by omega)⟩

/-- General odd tail variant: the final-byte `MLOAD` may expand active memory. -/
theorem reachMontgomeryDispatcherOddTailAny
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 1024)
    (hmodHeaderAccess :
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)).toNat + 32 ≤
        32 * aw.toNat)
    (hmodLength : wideLoadWord mem aw
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)) =
        UInt256.ofNat modulusSize)
    (hodd : modulusLastByteParity mem aw baseSize exponentSize modulusSize = ⟨1⟩)
    (htail : tail.length ≤ 1008)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1206⟩
      (UInt256.ofNat (modulusSize - 1) ::
        UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat operandBasePtr :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1925⟩
      (UInt256.ofNat operandBasePtr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) :: ⟨1271⟩ ::
        UInt256.ofNat ret :: tail)
      mem (modulusLastByteMloadAw aw baseSize exponentSize modulusSize) rdata acc k'
        (C + (modulusLastByteMloadGas aw baseSize exponentSize modulusSize + 130)) := by
  obtain ⟨k1, rd1251⟩ := reachDispatcherLastBytePtr
    hmodPos hm hmodHeaderAccess hmodLength htail rd0
  obtain ⟨k2, rd1925⟩ := reachMontgomeryDispatcherOddFinishAny
    hodd htail rd1251
  refine ⟨k2, rd1925.withIndices rfl ?_⟩
  unfold modulusLastByteMloadGas modulusLastByteMloadAw
  omega

theorem reachBarrettDispatcherEvenTailAny
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 1024)
    (hmodHeaderAccess :
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)).toNat + 32 ≤
        32 * aw.toNat)
    (hmodLength : wideLoadWord mem aw
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)) =
        UInt256.ofNat modulusSize)
    (heven : modulusLastByteParity mem aw baseSize exponentSize modulusSize = ⟨0⟩)
    (htail : tail.length ≤ 1008)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1206⟩
      (UInt256.ofNat (modulusSize - 1) ::
        UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat operandBasePtr :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1549⟩
      (UInt256.ofNat operandBasePtr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) :: ⟨1271⟩ ::
        UInt256.ofNat ret :: tail)
      mem (modulusLastByteMloadAw aw baseSize exponentSize modulusSize) rdata acc k'
        (C + (modulusLastByteMloadGas aw baseSize exponentSize modulusSize + 131)) := by
  obtain ⟨k1, rd1251⟩ := reachDispatcherLastBytePtr
    hmodPos hm hmodHeaderAccess hmodLength htail rd0
  obtain ⟨k2, rd1549⟩ := reachBarrettDispatcherEvenFinishAny
    heven htail rd1251
  refine ⟨k2, rd1549.withIndices rfl ?_⟩
  unfold modulusLastByteMloadGas modulusLastByteMloadAw
  omega

/-- The odd branch of the post-copy dispatcher.  Its parity premise is intentionally operational:
it is exactly the word expression computed by the bytecode from the current memory. -/
theorem reachMontgomeryDispatcherOdd
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 1024)
    (hmodHeaderAccess :
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)).toNat + 32 ≤
        32 * aw.toNat)
    (hlastAccess :
      (modulusLastBytePtrWord baseSize exponentSize modulusSize).toNat + 32 ≤
        32 * aw.toNat)
    (hmodLength : wideLoadWord mem aw
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)) =
        UInt256.ofNat modulusSize)
    (hodd : modulusLastByteParity mem aw baseSize exponentSize modulusSize = ⟨1⟩)
    (htail : tail.length ≤ 1008)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1183⟩
      (UInt256.ofNat operandBasePtr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1925⟩
      (UInt256.ofNat operandBasePtr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) :: ⟨1271⟩ ::
        UInt256.ofNat ret :: tail)
      mem aw rdata acc k' (C + 198) := by
  obtain ⟨k1, rd1206⟩ := reachDispatcherNonemptyHead
    hmodPos hm hmodHeaderAccess hmodLength htail rd0
  obtain ⟨k2, rd1925⟩ := reachMontgomeryDispatcherOddTail
    hmodPos hm hmodHeaderAccess hlastAccess hmodLength hodd htail rd1206
  exact ⟨k2, rd1925.withIndices rfl (by omega)⟩

/-- General odd dispatcher variant: the final-byte `MLOAD` may expand active memory. -/
theorem reachMontgomeryDispatcherOddAny
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 1024)
    (hmodHeaderAccess :
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)).toNat + 32 ≤
        32 * aw.toNat)
    (hmodLength : wideLoadWord mem aw
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)) =
        UInt256.ofNat modulusSize)
    (hodd : modulusLastByteParity mem aw baseSize exponentSize modulusSize = ⟨1⟩)
    (htail : tail.length ≤ 1008)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1183⟩
      (UInt256.ofNat operandBasePtr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1925⟩
      (UInt256.ofNat operandBasePtr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) :: ⟨1271⟩ ::
        UInt256.ofNat ret :: tail)
      mem (modulusLastByteMloadAw aw baseSize exponentSize modulusSize) rdata acc k'
        (C + (modulusLastByteMloadGas aw baseSize exponentSize modulusSize + 198)) := by
  obtain ⟨k1, rd1206⟩ := reachDispatcherNonemptyHead
    hmodPos hm hmodHeaderAccess hmodLength htail rd0
  obtain ⟨k2, rd1925⟩ := reachMontgomeryDispatcherOddTailAny
    hmodPos hm hmodHeaderAccess hmodLength hodd htail rd1206
  refine ⟨k2, rd1925.withIndices rfl ?_⟩
  unfold modulusLastByteMloadGas modulusLastByteMloadAw
  omega

theorem reachBarrettDispatcherEvenAny
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 1024)
    (hmodHeaderAccess :
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)).toNat + 32 ≤
        32 * aw.toNat)
    (hmodLength : wideLoadWord mem aw
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)) =
        UInt256.ofNat modulusSize)
    (heven : modulusLastByteParity mem aw baseSize exponentSize modulusSize = ⟨0⟩)
    (htail : tail.length ≤ 1008)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1183⟩
      (UInt256.ofNat operandBasePtr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1549⟩
      (UInt256.ofNat operandBasePtr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) :: ⟨1271⟩ ::
        UInt256.ofNat ret :: tail)
      mem (modulusLastByteMloadAw aw baseSize exponentSize modulusSize) rdata acc k'
        (C + (modulusLastByteMloadGas aw baseSize exponentSize modulusSize + 199)) := by
  obtain ⟨k1, rd1206⟩ := reachDispatcherNonemptyHead
    hmodPos hm hmodHeaderAccess hmodLength htail rd0
  obtain ⟨k2, rd1549⟩ := reachBarrettDispatcherEvenTailAny
    hmodPos hm hmodHeaderAccess hmodLength heven htail rd1206
  refine ⟨k2, rd1549.withIndices rfl ?_⟩
  unfold modulusLastByteMloadGas modulusLastByteMloadAw
  omega

/-- Allocate Barrett's result array from the even-modulus branch entry.  This is the Barrett
counterpart of `allocateMontgomeryResultExactFromAw`: it stops at the shared nontrivial checks
entry PC 1570, with the real caller return address kept under the Barrett internal return. -/
theorem allocateBarrettResultExactFromAw
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize ret : Nat} {tail : List UInt256} {aw0 : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 1024)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hmodAccess :
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)).toNat + 32 ≤
        32 * aw0.toNat)
    (hlength : wideLoadWord
      (operandCopiedMemory I baseSize exponentSize modulusSize) aw0
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)) =
        UInt256.ofNat modulusSize)
    (haw3 : 3 ≤ aw0.toNat)
    (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw0 * ⟨32⟩)
    (hresultWords :
      newBytesWords aw0 (operandFreePtr baseSize exponentSize modulusSize) modulusSize =
        wideWordResultWords baseSize exponentSize modulusSize)
    (htail : tail.length ≤ 1007)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1549⟩
      (UInt256.ofNat operandBasePtr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) :: ⟨1271⟩ ::
        UInt256.ofNat ret :: tail)
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      aw0 ByteArray.empty acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1570⟩
      (UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize) ::
        UInt256.ofNat modulusSize :: ⟨1271⟩ ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat (operandExponentPtr baseSize) :: UInt256.ofNat operandBasePtr ::
        UInt256.ofNat ret :: tail)
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize)
      ByteArray.empty acc (k + 99)
      (C + 55 + newBytesGas aw0
        (operandFreePtr baseSize exponentSize modulusSize) modulusSize) := by
  have hd := barrettEntryDecodes
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
  let mem := operandCopiedMemory I baseSize exponentSize modulusSize
  let aw := aw0
  let fp := operandFreePtr baseSize exponentSize modulusSize
  have hfpBound : fp + bytesAllocationSize modulusSize < 2 ^ 64 := by
    apply lt_of_le_of_lt
      (show fp + bytesAllocationSize modulusSize ≤ 4352 by
        unfold fp operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega)
      (by decide)
  have hmem96 : 96 ≤ mem.size := by
    have hge := operandCopiedMemory_size_ge I baseSize exponentSize modulusSize hb he
    dsimp only [mem]
    exact (by
      apply le_trans (show 96 ≤ operandModulusPtr baseSize exponentSize + 32 by
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega) hge)
  have hmemLe : mem.size ≤ fp := by
    exact operandCopiedMemory_size_le_freePtr I baseSize exponentSize modulusSize hb he
  have rd1570 := newBytesExact (by omega) (by
      unfold fp operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega) hfpBound hmem96 hmemLe
    (lt_usize _ (by
      apply lt_of_le_of_lt (Nat.sub_le fp mem.size)
      apply lt_of_le_of_lt
        (show fp ≤ 3296 by
          unfold fp operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
            bytesAllocationSize
          omega)
        (by decide)))
    (by simpa [aw] using haw3) (by simpa [aw] using haw64)
    (operandCopiedMemory_read64 I baseSize exponentSize modulusSize hb he)
    hcalldata (by simp only [List.length_cons]; omega) jumpDest_1570_dispatcher rd581
  dsimp only [mem, aw, fp] at rd1570
  rw [hresultWords] at rd1570
  have rd1570' : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1570⟩
      (UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize) ::
        UInt256.ofNat modulusSize :: ⟨1271⟩ ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat (operandExponentPtr baseSize) :: UInt256.ofNat operandBasePtr ::
        UInt256.ofNat ret :: tail)
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize)
      ByteArray.empty acc (k + 99)
      (C + 55 + newBytesGas aw0
        (operandFreePtr baseSize exponentSize modulusSize) modulusSize) :=
    by
      simpa [wideWordResultMemory, wideWordResultWords,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        rd1570.withIndices (by omega) (by omega)
  exact rd1570'

def preparedBarrettPrefixGasFromAw (I : ExecutionEnv) (aw : UInt256)
    (baseSize exponentSize modulusSize : Nat) : Nat :=
  let aw1 := modulusLastByteMloadAw aw baseSize exponentSize modulusSize
  modulusLastByteMloadGas aw baseSize exponentSize modulusSize + 199 +
    55 + newBytesGas aw1 (operandFreePtr baseSize exponentSize modulusSize) modulusSize +
    wideWordChecksGas
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize)
      (operandModulusPtr baseSize exponentSize) modulusSize

/-- Verified exact-gas prefix of the even-modulus Barrett path: from the prepared operand arrays
through the parity dispatcher, result allocation, and shared nontrivial modulus checks.  The proof
intentionally stops at PC 1592, which is the first unproved Barrett backend block. -/
theorem runPreparedBarrettPrefixExactAny
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize ret : Nat} {tail : List UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 1024)
    (hmod : 1 < Model.bytesToNatPadded I.calldata
      (96 + baseSize + exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (heven : modulusLastByteParity
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize modulusSize = ⟨0⟩)
    (htail : tail.length ≤ 1006)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1183⟩
      (UInt256.ofNat operandBasePtr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat ret :: tail)
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      ByteArray.empty acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1592⟩
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat modulusSize :: ⟨1271⟩ ::
        UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize) ::
        UInt256.ofNat (operandExponentPtr baseSize) :: UInt256.ofNat operandBasePtr ::
        UInt256.ofNat ret :: tail)
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize)
      ByteArray.empty acc k'
        (C + preparedBarrettPrefixGasFromAw I
          (operandModulusActiveWords baseSize exponentSize modulusSize)
          baseSize exponentSize modulusSize) := by
  let oldAw := operandModulusActiveWords baseSize exponentSize modulusSize
  let aw1 := modulusLastByteMloadAw oldAw baseSize exponentSize modulusSize
  have hmodHeaderAccess :
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)).toNat + 32 ≤
        32 * oldAw.toNat := by
    dsimp only [oldAw]
    rw [UInt256.toNat_ofNat_of_lt (by
      apply lt_of_le_of_lt
        (show operandModulusPtr baseSize exponentSize ≤ 2272 by
          unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
          omega)
        (by decide))]
    unfold operandModulusActiveWords
    rw [UInt256.toNat_ofNat_of_lt (by
      apply lt_of_le_of_lt
        (show operandModulusWords baseSize exponentSize modulusSize ≤ 103 by
          unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
          omega)
        (by decide))]
    rw [operandModulusPtr_eq]
    unfold operandModulusWords bytesAllocationWords
    omega
  have hmodLengthOld : wideLoadWord
      (operandCopiedMemory I baseSize exponentSize modulusSize) oldAw
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)) =
        UInt256.ofNat modulusSize := by
    dsimp only [oldAw]
    exact operandCopiedWideLoadModulusLength I
      baseSize exponentSize modulusSize hb he (by omega)
  obtain ⟨kDisp, rd1549⟩ := reachBarrettDispatcherEvenAny
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (ret := ret) (tail := tail)
    hmodPos (by omega : modulusSize ≤ 1024) hmodHeaderAccess hmodLengthOld heven
    (by omega) rd0
  have hawLe : oldAw.toNat ≤ aw1.toNat := by
    dsimp only [oldAw, aw1]
    exact modulusLastByteMloadAw_ge_operand hb he hmodPos (by omega)
  have haw1Bound : aw1.toNat ≤ operandModulusWords baseSize exponentSize modulusSize + 1 := by
    dsimp only [oldAw, aw1]
    exact modulusLastByteMloadAw_bound hb he hmodPos (by omega)
  have haw1NoWrap : aw1.toNat * 32 < UInt256.size := by
    apply lt_of_le_of_lt
      (show aw1.toNat * 32 ≤
          (operandModulusWords baseSize exponentSize modulusSize + 1) * 32 by
        nlinarith)
    apply lt_of_le_of_lt
      (show (operandModulusWords baseSize exponentSize modulusSize + 1) * 32 ≤ 3328 by
        unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
        omega)
      (by decide)
  have holdNoWrap : oldAw.toNat * 32 < UInt256.size := by
    dsimp only [oldAw]
    unfold operandModulusActiveWords
    rw [UInt256.toNat_ofNat_of_lt (by
      apply lt_of_le_of_lt
        (show operandModulusWords baseSize exponentSize modulusSize ≤ 103 by
          unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
          omega)
        (by decide))]
    apply lt_of_le_of_lt
      (show operandModulusWords baseSize exponentSize modulusSize * 32 ≤ 3296 by
        unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
        omega)
      (by decide)
  have hmodHeaderAccess1 :
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)).toNat + 32 ≤
        32 * aw1.toNat := by
    omega
  have hbelowOld :
      ¬ UInt256.ofNat (operandModulusPtr baseSize exponentSize) ≥ oldAw * ⟨32⟩ :=
    not_ge_mul32_of_access hmodHeaderAccess holdNoWrap
  have hbelow1 :
      ¬ UInt256.ofNat (operandModulusPtr baseSize exponentSize) ≥ aw1 * ⟨32⟩ :=
    not_ge_mul32_of_access hmodHeaderAccess1 haw1NoWrap
  have hmodLength1 : wideLoadWord
      (operandCopiedMemory I baseSize exponentSize modulusSize) aw1
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)) =
        UInt256.ofNat modulusSize := by
    rw [wideLoadWord_eq_decode_bounded hbelow1]
    rw [← wideLoadWord_eq_decode_bounded hbelowOld]
    exact hmodLengthOld
  have haw1Three : 3 ≤ aw1.toNat := by
    have holdThree : 3 ≤ oldAw.toNat := by
      dsimp only [oldAw]
      unfold operandModulusActiveWords
      rw [UInt256.toNat_ofNat_of_lt (by
        apply lt_of_le_of_lt
          (show operandModulusWords baseSize exponentSize modulusSize ≤ 103 by
            unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
            omega)
          (by decide))]
      unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
      omega
    omega
  have hresultWords : newBytesWords aw1
      (operandFreePtr baseSize exponentSize modulusSize) modulusSize =
        wideWordResultWords baseSize exponentSize modulusSize := by
    dsimp only [oldAw, aw1]
    exact newBytesWords_lastByteMloadAw_eq_result hb he hmodPos (by omega)
  have rd1570 := allocateBarrettResultExactFromAw
    (aw0 := aw1) (ret := ret) (tail := tail)
    hb he hmodPos (by omega) hcalldata hmodHeaderAccess1 hmodLength1 haw1Three
    (wordMul32_not_le64_of_ge3 haw1Three (by simpa [Nat.mul_comm] using haw1NoWrap))
    hresultWords (by omega) rd1549
  obtain ⟨kChecks, rd1592⟩ := reachBarrettNontrivialChecksTrusted
    (ret := 1271) (tail := UInt256.ofNat ret :: tail)
    hb he hmodPos (by omega) hmod (by simp only [List.length_cons]; omega) rd1570
  refine ⟨kChecks, rd1592.withIndices rfl ?_⟩
  unfold preparedBarrettPrefixGasFromAw
  dsimp only [oldAw, aw1]
  omega

theorem dispatcherReturnDecodes :
    [decode runtimeBytecode ⟨1271⟩, decode runtimeBytecode ⟨1272⟩,
      decode runtimeBytecode ⟨1273⟩] =
    [some (.JUMPDEST, .none), some (.SWAP1, .none), some (.JUMP, .none)] := by
  native_decide

def preparedBarrettZeroReturnGasFromAw (I : ExecutionEnv) (aw : UInt256)
    (baseSize exponentSize modulusSize : Nat) : Nat :=
  let aw1 := modulusLastByteMloadAw aw baseSize exponentSize modulusSize
  modulusLastByteMloadGas aw baseSize exponentSize modulusSize + 199 +
    55 + newBytesGas aw1 (operandFreePtr baseSize exponentSize modulusSize) modulusSize +
    wideWordChecksZeroReturnGas
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize)
      (operandModulusPtr baseSize exponentSize) modulusSize +
    12

/-- From prepared operand arrays, the even dispatcher branch allocates the result bytes object,
observes a zero modulus, and returns that zero-filled object pointer to the caller. -/
theorem runPreparedBarrettZeroReturnExactAny
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize ret : Nat} {tail : List UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 1024)
    (hmodZero : Model.bytesToNatPadded I.calldata
      (96 + baseSize + exponentSize) modulusSize = 0)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (heven : modulusLastByteParity
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize modulusSize = ⟨0⟩)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (htail : tail.length ≤ 1006)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1183⟩
      (UInt256.ofNat operandBasePtr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat ret :: tail)
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      ByteArray.empty acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat ret)
      (UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize) :: tail)
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize)
      ByteArray.empty acc k'
        (C + preparedBarrettZeroReturnGasFromAw I
          (operandModulusActiveWords baseSize exponentSize modulusSize)
          baseSize exponentSize modulusSize) := by
  let oldAw := operandModulusActiveWords baseSize exponentSize modulusSize
  let aw1 := modulusLastByteMloadAw oldAw baseSize exponentSize modulusSize
  have hmodHeaderAccess :
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)).toNat + 32 ≤
        32 * oldAw.toNat := by
    dsimp only [oldAw]
    rw [UInt256.toNat_ofNat_of_lt (by
      apply lt_of_le_of_lt
        (show operandModulusPtr baseSize exponentSize ≤ 2272 by
          unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
          omega)
        (by decide))]
    unfold operandModulusActiveWords
    rw [UInt256.toNat_ofNat_of_lt (by
      apply lt_of_le_of_lt
        (show operandModulusWords baseSize exponentSize modulusSize ≤ 103 by
          unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
          omega)
        (by decide))]
    rw [operandModulusPtr_eq]
    unfold operandModulusWords bytesAllocationWords
    omega
  have hmodLengthOld : wideLoadWord
      (operandCopiedMemory I baseSize exponentSize modulusSize) oldAw
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)) =
        UInt256.ofNat modulusSize := by
    dsimp only [oldAw]
    exact operandCopiedWideLoadModulusLength I
      baseSize exponentSize modulusSize hb he (by omega)
  obtain ⟨kDisp, rd1549⟩ := reachBarrettDispatcherEvenAny
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (ret := ret) (tail := tail)
    hmodPos (by omega : modulusSize ≤ 1024) hmodHeaderAccess hmodLengthOld heven
    (by omega) rd0
  have hawLe : oldAw.toNat ≤ aw1.toNat := by
    dsimp only [oldAw, aw1]
    exact modulusLastByteMloadAw_ge_operand hb he hmodPos (by omega)
  have haw1Bound : aw1.toNat ≤ operandModulusWords baseSize exponentSize modulusSize + 1 := by
    dsimp only [oldAw, aw1]
    exact modulusLastByteMloadAw_bound hb he hmodPos (by omega)
  have haw1NoWrap : aw1.toNat * 32 < UInt256.size := by
    apply lt_of_le_of_lt
      (show aw1.toNat * 32 ≤
          (operandModulusWords baseSize exponentSize modulusSize + 1) * 32 by
        nlinarith)
    apply lt_of_le_of_lt
      (show (operandModulusWords baseSize exponentSize modulusSize + 1) * 32 ≤ 3328 by
        unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
        omega)
      (by decide)
  have holdNoWrap : oldAw.toNat * 32 < UInt256.size := by
    dsimp only [oldAw]
    unfold operandModulusActiveWords
    rw [UInt256.toNat_ofNat_of_lt (by
      apply lt_of_le_of_lt
        (show operandModulusWords baseSize exponentSize modulusSize ≤ 103 by
          unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
          omega)
        (by decide))]
    apply lt_of_le_of_lt
      (show operandModulusWords baseSize exponentSize modulusSize * 32 ≤ 3296 by
        unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
        omega)
      (by decide)
  have hmodHeaderAccess1 :
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)).toNat + 32 ≤
        32 * aw1.toNat := by
    omega
  have hbelowOld :
      ¬ UInt256.ofNat (operandModulusPtr baseSize exponentSize) ≥ oldAw * ⟨32⟩ :=
    not_ge_mul32_of_access hmodHeaderAccess holdNoWrap
  have hbelow1 :
      ¬ UInt256.ofNat (operandModulusPtr baseSize exponentSize) ≥ aw1 * ⟨32⟩ :=
    not_ge_mul32_of_access hmodHeaderAccess1 haw1NoWrap
  have hmodLength1 : wideLoadWord
      (operandCopiedMemory I baseSize exponentSize modulusSize) aw1
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)) =
        UInt256.ofNat modulusSize := by
    rw [wideLoadWord_eq_decode_bounded hbelow1]
    rw [← wideLoadWord_eq_decode_bounded hbelowOld]
    exact hmodLengthOld
  have haw1Three : 3 ≤ aw1.toNat := by
    have holdThree : 3 ≤ oldAw.toNat := by
      dsimp only [oldAw]
      unfold operandModulusActiveWords
      rw [UInt256.toNat_ofNat_of_lt (by
        apply lt_of_le_of_lt
          (show operandModulusWords baseSize exponentSize modulusSize ≤ 103 by
            unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
            omega)
          (by decide))]
      unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
      omega
    omega
  have hresultWords : newBytesWords aw1
      (operandFreePtr baseSize exponentSize modulusSize) modulusSize =
        wideWordResultWords baseSize exponentSize modulusSize := by
    dsimp only [oldAw, aw1]
    exact newBytesWords_lastByteMloadAw_eq_result hb he hmodPos (by omega)
  have rd1570 := allocateBarrettResultExactFromAw
    (aw0 := aw1) (ret := ret) (tail := tail)
    hb he hmodPos (by omega) hcalldata hmodHeaderAccess1 hmodLength1 haw1Three
    (wordMul32_not_le64_of_ge3 haw1Three (by simpa [Nat.mul_comm] using haw1NoWrap))
    hresultWords (by omega) rd1549
  have hzero := wideWordResultMemoryZero_eq_one_of_model_zero I
    baseSize exponentSize modulusSize hb he hmodPos hm hmodZero
  obtain ⟨kChecks, rd1271⟩ := reachBarrettZeroChecksReturn
    (basePtr := operandBasePtr) (exponentPtr := operandExponentPtr baseSize)
    (modulusPtr := operandModulusPtr baseSize exponentSize)
    (resultPtr := operandFreePtr baseSize exponentSize modulusSize)
    (modulusSize := modulusSize) (ret := 1271) (tail := UInt256.ofNat ret :: tail)
    (by
      apply lt_trans
      · show operandModulusPtr baseSize exponentSize + 32 + modulusSize + 32 < 2 ^ 64
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega
      · decide)
    (by
      rw [wideWordResultWords_toNat hb he (by omega : modulusSize ≤ 1024)]
      simp only [operandModulusPtr, operandExponentPtr, operandBasePtr, bytesAllocationSize,
        operandModulusWords, operandExponentWords, operandBaseWords, bytesAllocationWords]
      have hround := bytesSize_le_roundedPayload modulusSize
      omega)
    (by
      rw [wideLoadWord_result_eq I hb he (by omega : modulusSize ≤ 1024)
        (by unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize; omega)
        (by unfold operandFreePtr bytesAllocationSize; omega)]
      exact operandCopiedWideLoadModulusLength I baseSize exponentSize modulusSize
        hb he (by omega : modulusSize ≤ 1024))
    hzero (by simp only [List.length_cons]; omega) jumpDest_1271 rd1570
  have hd := dispatcherReturnDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2⟩
  have rdRet := evm_run rd1271 with [known jumpdest h0, known swap1 h1,
    known jump h2 hret]
  refine ⟨_, rdRet.withIndices rfl ?_⟩
  unfold preparedBarrettZeroReturnGasFromAw
  dsimp only [oldAw, aw1]
  omega

def preparedMontgomeryWordGas (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat) : Nat :=
  198 + montgomeryWordCallerGas I baseSize exponentSize modulusSize + 12

def preparedMontgomeryWordGasFromAw (I : ExecutionEnv) (aw : UInt256)
    (baseSize exponentSize modulusSize : Nat) : Nat :=
  modulusLastByteMloadGas aw baseSize exponentSize modulusSize + 198 +
    montgomeryWordCallerGasFromAw I
      (modulusLastByteMloadAw aw baseSize exponentSize modulusSize)
      baseSize exponentSize modulusSize +
    12

def preparedMontgomeryOneReturnGasFromAw (I : ExecutionEnv) (aw : UInt256)
    (baseSize exponentSize modulusSize : Nat) : Nat :=
  let aw1 := modulusLastByteMloadAw aw baseSize exponentSize modulusSize
  modulusLastByteMloadGas aw baseSize exponentSize modulusSize + 198 +
    55 + newBytesGas aw1 (operandFreePtr baseSize exponentSize modulusSize) modulusSize +
    montgomeryChecksOneReturnGas
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize)
      (operandModulusPtr baseSize exponentSize) modulusSize +
    12

/-- From prepared operand arrays, the odd dispatcher branch allocates the result bytes object,
observes a one modulus, and returns that zero-filled object pointer to the caller. -/
theorem runPreparedMontgomeryOneReturnExactAny
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize ret : Nat} {tail : List UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 1024)
    (hmodOne : Model.bytesToNatPadded I.calldata
      (96 + baseSize + exponentSize) modulusSize = 1)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hodd : modulusLastByteParity
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize modulusSize = ⟨1⟩)
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
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize)
      ByteArray.empty acc k'
        (C + preparedMontgomeryOneReturnGasFromAw I
          (operandModulusActiveWords baseSize exponentSize modulusSize)
          baseSize exponentSize modulusSize) := by
  let oldAw := operandModulusActiveWords baseSize exponentSize modulusSize
  let aw1 := modulusLastByteMloadAw oldAw baseSize exponentSize modulusSize
  have hmodHeaderAccess :
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)).toNat + 32 ≤
        32 * oldAw.toNat := by
    dsimp only [oldAw]
    rw [UInt256.toNat_ofNat_of_lt (by
      apply lt_of_le_of_lt
        (show operandModulusPtr baseSize exponentSize ≤ 2272 by
          unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
          omega)
        (by decide))]
    unfold operandModulusActiveWords
    rw [UInt256.toNat_ofNat_of_lt (by
      apply lt_of_le_of_lt
        (show operandModulusWords baseSize exponentSize modulusSize ≤ 103 by
          unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
          omega)
        (by decide))]
    rw [operandModulusPtr_eq]
    unfold operandModulusWords bytesAllocationWords
    omega
  have hmodLengthOld : wideLoadWord
      (operandCopiedMemory I baseSize exponentSize modulusSize) oldAw
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)) =
        UInt256.ofNat modulusSize := by
    dsimp only [oldAw]
    exact operandCopiedWideLoadModulusLength I
      baseSize exponentSize modulusSize hb he (by omega)
  obtain ⟨kDisp, rd1925⟩ := reachMontgomeryDispatcherOddAny
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (ret := ret) (tail := tail)
    hmodPos (by omega : modulusSize ≤ 1024) hmodHeaderAccess hmodLengthOld hodd
    (by omega) rd0
  have hawLe : oldAw.toNat ≤ aw1.toNat := by
    dsimp only [oldAw, aw1]
    exact modulusLastByteMloadAw_ge_operand hb he hmodPos (by omega)
  have haw1Bound : aw1.toNat ≤ operandModulusWords baseSize exponentSize modulusSize + 1 := by
    dsimp only [oldAw, aw1]
    exact modulusLastByteMloadAw_bound hb he hmodPos (by omega)
  have haw1NoWrap : aw1.toNat * 32 < UInt256.size := by
    apply lt_of_le_of_lt
      (show aw1.toNat * 32 ≤
          (operandModulusWords baseSize exponentSize modulusSize + 1) * 32 by
        nlinarith)
    apply lt_of_le_of_lt
      (show (operandModulusWords baseSize exponentSize modulusSize + 1) * 32 ≤ 3328 by
        unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
        omega)
      (by decide)
  have holdNoWrap : oldAw.toNat * 32 < UInt256.size := by
    dsimp only [oldAw]
    unfold operandModulusActiveWords
    rw [UInt256.toNat_ofNat_of_lt (by
      apply lt_of_le_of_lt
        (show operandModulusWords baseSize exponentSize modulusSize ≤ 103 by
          unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
          omega)
        (by decide))]
    apply lt_of_le_of_lt
      (show operandModulusWords baseSize exponentSize modulusSize * 32 ≤ 3296 by
        unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
        omega)
      (by decide)
  have hmodHeaderAccess1 :
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)).toNat + 32 ≤
        32 * aw1.toNat := by
    omega
  have hbelowOld :
      ¬ UInt256.ofNat (operandModulusPtr baseSize exponentSize) ≥ oldAw * ⟨32⟩ :=
    not_ge_mul32_of_access hmodHeaderAccess holdNoWrap
  have hbelow1 :
      ¬ UInt256.ofNat (operandModulusPtr baseSize exponentSize) ≥ aw1 * ⟨32⟩ :=
    not_ge_mul32_of_access hmodHeaderAccess1 haw1NoWrap
  have hmodLength1 : wideLoadWord
      (operandCopiedMemory I baseSize exponentSize modulusSize) aw1
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)) =
        UInt256.ofNat modulusSize := by
    rw [wideLoadWord_eq_decode_bounded hbelow1]
    rw [← wideLoadWord_eq_decode_bounded hbelowOld]
    exact hmodLengthOld
  have haw1Three : 3 ≤ aw1.toNat := by
    have holdThree : 3 ≤ oldAw.toNat := by
      dsimp only [oldAw]
      unfold operandModulusActiveWords
      rw [UInt256.toNat_ofNat_of_lt (by
        apply lt_of_le_of_lt
          (show operandModulusWords baseSize exponentSize modulusSize ≤ 103 by
            unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
            omega)
          (by decide))]
      unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
      omega
    omega
  have hresultWords : newBytesWords aw1
      (operandFreePtr baseSize exponentSize modulusSize) modulusSize =
        wideWordResultWords baseSize exponentSize modulusSize := by
    dsimp only [oldAw, aw1]
    exact newBytesWords_lastByteMloadAw_eq_result hb he hmodPos (by omega)
  have rd1946 := allocateMontgomeryResultExactFromAw
    (aw0 := aw1) (ret := 1271) (tail := UInt256.ofNat ret :: tail)
    hb he hmodPos (by omega) hcalldata hmodHeaderAccess1 hmodLength1 haw1Three
    (wordMul32_not_le64_of_ge3 haw1Three (by simpa [Nat.mul_comm] using haw1NoWrap))
    hresultWords (by simp only [List.length_cons]; omega) rd1925
  have hzero := wideWordResultMemoryZero_eq_zero_of_model_one I
    baseSize exponentSize modulusSize hb he hmodPos hm hmodOne
  have hone := wideWordResultMemoryOne_eq_one_of_model_one I
    baseSize exponentSize modulusSize hb he hmodPos hm hmodOne
  obtain ⟨kChecks, rd1271⟩ := reachMontgomeryOneChecksReturn
    (basePtr := operandBasePtr) (exponentPtr := operandExponentPtr baseSize)
    (modulusPtr := operandModulusPtr baseSize exponentSize)
    (resultPtr := operandFreePtr baseSize exponentSize modulusSize)
    (modulusSize := modulusSize) (ret := 1271) (tail := UInt256.ofNat ret :: tail)
    (by
      apply lt_trans
      · show operandModulusPtr baseSize exponentSize + 32 + modulusSize + 32 < 2 ^ 64
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega
      · decide)
    (by
      rw [wideWordResultWords_toNat hb he (by omega : modulusSize ≤ 1024)]
      simp only [operandModulusPtr, operandExponentPtr, operandBasePtr, bytesAllocationSize,
        operandModulusWords, operandExponentWords, operandBaseWords, bytesAllocationWords]
      have hround := bytesSize_le_roundedPayload modulusSize
      omega)
    (by
      rw [wideLoadWord_result_eq I hb he (by omega : modulusSize ≤ 1024)
        (by unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize; omega)
        (by unfold operandFreePtr bytesAllocationSize; omega)]
      exact operandCopiedWideLoadModulusLength I baseSize exponentSize modulusSize
        hb he (by omega : modulusSize ≤ 1024))
    hzero hone (by simp only [List.length_cons]; omega) jumpDest_1271 rd1946
  have hd := dispatcherReturnDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2⟩
  have rdRet := evm_run rd1271 with [known jumpdest h0, known swap1 h1,
    known jump h2 hret]
  refine ⟨_, rdRet.withIndices rfl ?_⟩
  unfold preparedMontgomeryOneReturnGasFromAw
  dsimp only [oldAw, aw1]
  omega

/-- From the prepared operand arrays, execute the odd-modulus one-limb Montgomery implementation
and return to the caller-supplied internal return address. -/
theorem runPreparedMontgomeryWordExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize ret : Nat} {tail : List UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 32)
    (hmod : 1 < Model.bytesToNatPadded I.calldata
      (96 + baseSize + exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hlastAccess :
      (modulusLastBytePtrWord baseSize exponentSize modulusSize).toNat + 32 ≤
        32 * (operandModulusActiveWords baseSize exponentSize modulusSize).toNat)
    (hodd : modulusLastByteParity
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize modulusSize = ⟨1⟩)
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
        (C + preparedMontgomeryWordGas I baseSize exponentSize modulusSize) := by
  have hmodHeaderAccess :
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)).toNat + 32 ≤
        32 * (operandModulusActiveWords baseSize exponentSize modulusSize).toNat := by
    rw [UInt256.toNat_ofNat_of_lt (by
      apply lt_of_le_of_lt
        (show operandModulusPtr baseSize exponentSize ≤ 2272 by
          unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
          omega)
        (by decide))]
    unfold operandModulusActiveWords
    rw [UInt256.toNat_ofNat_of_lt (by
      apply lt_of_le_of_lt
        (show operandModulusWords baseSize exponentSize modulusSize ≤ 72 by
          unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
          omega)
        (by decide))]
    rw [operandModulusPtr_eq]
    unfold operandModulusWords bytesAllocationWords
    omega
  have hmodLength := operandCopiedWideLoadModulusLength I
    baseSize exponentSize modulusSize hb he (by omega)
  obtain ⟨kDisp, rd1925⟩ := reachMontgomeryDispatcherOdd
    hmodPos (by omega : modulusSize ≤ 1024) hmodHeaderAccess hlastAccess
    hmodLength hodd (by omega) rd0
  obtain ⟨kMont, rd1271⟩ := runMontgomeryWordCallerExact
    (ret := 1271) (tail := UInt256.ofNat ret :: tail)
    hb he hmodPos hm hmod hcalldata jumpDest_1271
    (by simp only [List.length_cons]; omega) rd1925
  have hd := dispatcherReturnDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2⟩
  have rdRet := evm_run rd1271 with [known jumpdest h0, known swap1 h1,
    known jump h2 hret]
  refine ⟨_, rdRet.withIndices rfl ?_⟩
  unfold preparedMontgomeryWordGas
  omega

/-- From the prepared operand arrays, execute the odd-modulus one-limb Montgomery implementation
and return to the caller-supplied internal return address.  Unlike
`runPreparedMontgomeryWordExact`, this theorem does not require the dispatcher's final-byte
`MLOAD` to be within the current active-memory frontier; the exact gas expression includes that
expansion and then continues the caller from the expanded frontier. -/
theorem runPreparedMontgomeryWordExactAny
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize ret : Nat} {tail : List UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 32)
    (hmod : 1 < Model.bytesToNatPadded I.calldata
      (96 + baseSize + exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hodd : modulusLastByteParity
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize modulusSize = ⟨1⟩)
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
        (C + preparedMontgomeryWordGasFromAw I
          (operandModulusActiveWords baseSize exponentSize modulusSize)
          baseSize exponentSize modulusSize) := by
  let oldAw := operandModulusActiveWords baseSize exponentSize modulusSize
  let aw1 := modulusLastByteMloadAw oldAw baseSize exponentSize modulusSize
  have hmodHeaderAccess :
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)).toNat + 32 ≤
        32 * oldAw.toNat := by
    dsimp only [oldAw]
    rw [UInt256.toNat_ofNat_of_lt (by
      apply lt_of_le_of_lt
        (show operandModulusPtr baseSize exponentSize ≤ 2272 by
          unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
          omega)
        (by decide))]
    unfold operandModulusActiveWords
    rw [UInt256.toNat_ofNat_of_lt (by
      apply lt_of_le_of_lt
        (show operandModulusWords baseSize exponentSize modulusSize ≤ 72 by
          unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
          omega)
        (by decide))]
    rw [operandModulusPtr_eq]
    unfold operandModulusWords bytesAllocationWords
    omega
  have hmodLengthOld : wideLoadWord
      (operandCopiedMemory I baseSize exponentSize modulusSize) oldAw
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)) =
        UInt256.ofNat modulusSize := by
    dsimp only [oldAw]
    exact operandCopiedWideLoadModulusLength I
      baseSize exponentSize modulusSize hb he (by omega)
  obtain ⟨kDisp, rd1925⟩ := reachMontgomeryDispatcherOddAny
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (ret := ret) (tail := tail)
    hmodPos (by omega : modulusSize ≤ 1024) hmodHeaderAccess hmodLengthOld hodd
    (by omega) rd0
  have hawLe : oldAw.toNat ≤ aw1.toNat := by
    dsimp only [oldAw, aw1]
    exact modulusLastByteMloadAw_ge_operand hb he hmodPos (by omega)
  have haw1Bound : aw1.toNat ≤ operandModulusWords baseSize exponentSize modulusSize + 1 := by
    dsimp only [oldAw, aw1]
    exact modulusLastByteMloadAw_bound hb he hmodPos (by omega)
  have haw1NoWrap : aw1.toNat * 32 < UInt256.size := by
    apply lt_of_le_of_lt
      (show aw1.toNat * 32 ≤
          (operandModulusWords baseSize exponentSize modulusSize + 1) * 32 by
        nlinarith)
    apply lt_of_le_of_lt
      (show (operandModulusWords baseSize exponentSize modulusSize + 1) * 32 ≤ 2336 by
        unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
        omega)
      (by decide)
  have holdNoWrap : oldAw.toNat * 32 < UInt256.size := by
    dsimp only [oldAw]
    unfold operandModulusActiveWords
    rw [UInt256.toNat_ofNat_of_lt (by
      apply lt_of_le_of_lt
        (show operandModulusWords baseSize exponentSize modulusSize ≤ 72 by
          unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
          omega)
        (by decide))]
    apply lt_of_le_of_lt
      (show operandModulusWords baseSize exponentSize modulusSize * 32 ≤ 2304 by
        unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
        omega)
      (by decide)
  have hmodHeaderAccess1 :
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)).toNat + 32 ≤
        32 * aw1.toNat := by
    omega
  have hbelowOld :
      ¬ UInt256.ofNat (operandModulusPtr baseSize exponentSize) ≥ oldAw * ⟨32⟩ :=
    not_ge_mul32_of_access hmodHeaderAccess holdNoWrap
  have hbelow1 :
      ¬ UInt256.ofNat (operandModulusPtr baseSize exponentSize) ≥ aw1 * ⟨32⟩ :=
    not_ge_mul32_of_access hmodHeaderAccess1 haw1NoWrap
  have hmodLength1 : wideLoadWord
      (operandCopiedMemory I baseSize exponentSize modulusSize) aw1
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)) =
        UInt256.ofNat modulusSize := by
    rw [wideLoadWord_eq_decode_bounded hbelow1]
    rw [← wideLoadWord_eq_decode_bounded hbelowOld]
    exact hmodLengthOld
  have haw1Three : 3 ≤ aw1.toNat := by
    have holdThree : 3 ≤ oldAw.toNat := by
      dsimp only [oldAw]
      unfold operandModulusActiveWords
      rw [UInt256.toNat_ofNat_of_lt (by
        apply lt_of_le_of_lt
          (show operandModulusWords baseSize exponentSize modulusSize ≤ 72 by
            unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
            omega)
          (by decide))]
      unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
      omega
    omega
  have hresultWords : newBytesWords aw1
      (operandFreePtr baseSize exponentSize modulusSize) modulusSize =
        wideWordResultWords baseSize exponentSize modulusSize := by
    dsimp only [oldAw, aw1]
    exact newBytesWords_lastByteMloadAw_eq_result hb he hmodPos (by omega)
  obtain ⟨kMont, rd1271⟩ := runMontgomeryWordCallerExactFromAw
    (ret := 1271) (tail := UInt256.ofNat ret :: tail) (aw0 := aw1)
    hb he hmodPos hm hmod hcalldata hmodHeaderAccess1 hmodLength1 haw1Three
    (wordMul32_not_le64_of_ge3 haw1Three (by simpa [Nat.mul_comm] using haw1NoWrap))
    hresultWords jumpDest_1271
    (by simp only [List.length_cons]; omega) rd1925
  have hd := dispatcherReturnDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2⟩
  have rdRet := evm_run rd1271 with [known jumpdest h0, known swap1 h1,
    known jump h2 hret]
  refine ⟨_, rdRet.withIndices rfl ?_⟩
  unfold preparedMontgomeryWordGasFromAw
  dsimp only [oldAw, aw1]
  omega

end Modexp
