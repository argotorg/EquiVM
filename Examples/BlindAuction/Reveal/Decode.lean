import Examples.BlindAuction.Storage
import Examples.BlindAuction.Bids
import Examples.BlindAuction.BiddingEnd
import Examples.BlindAuction.HighestBidder
import Examples.BlindAuction.RevealEnd
import Examples.SimpleAuction.Withdraw
import Reasoning.ExternalCall
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 800000
namespace Reasoning.Theory

-- PROMOTE -> Reasoning.Stepping: generic `DUP10` xstep, matching the existing `DUP2`-`DUP8`.
theorem blindAuctionDup10_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg h i j : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP10, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: t)
    (hov : t.length + 11 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (j :: a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: t),
           .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP10, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_dup10 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: t).length - 10 + 11 >
          1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

-- PROMOTE -> Reasoning.Stepping: generic `DUP11` xstep.
theorem blindAuctionDup11_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg h i j k : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP11, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: k :: t)
    (hov : t.length + 12 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok
          (stSwap s (k :: a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: k :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP11, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_dup11 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: k :: t).length - 11 + 12 >
          1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

-- PROMOTE -> Reasoning.Stepping: generic `SWAP6` xstep.
theorem blindAuctionSwap6_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f h : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP6, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: h :: t)
    (hov : t.length + 7 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (h :: b :: c :: d :: e :: f :: a :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP6, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_swap6 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: e :: f :: h :: t).length - 7 + 7 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

-- PROMOTE -> Reasoning.Stepping: generic `SWAP7` xstep.
theorem blindAuctionSwap7_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg h : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP7, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: gg :: h :: t)
    (hov : t.length + 8 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (h :: b :: c :: d :: e :: f :: gg :: a :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP7, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_swap7 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: e :: f :: gg :: h :: t).length - 8 + 8 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

-- PROMOTE -> Reasoning.Stepping: generic `SWAP8` xstep.
theorem blindAuctionSwap8_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg h i : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP8, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: gg :: h :: i :: t)
    (hov : t.length + 9 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (i :: b :: c :: d :: e :: f :: gg :: h :: a :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP8, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_swap8 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: h :: i :: t).length - 9 + 9 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

-- PROMOTE -> Reasoning.Stepping: generic `SWAP10` xstep.
theorem blindAuctionSwap10_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg h i j k : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP10, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: k :: t)
    (hov : t.length + 11 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (k :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: a :: t),
           .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP10, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_swap10 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: k :: t).length - 11 + 11 >
          1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

-- PROMOTE -> Reasoning.Stepping: generic `SWAP11` xstep.
theorem blindAuctionSwap11_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg h i j k l : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP11, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: k :: l :: t)
    (hov : t.length + 12 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok
          (stSwap s (l :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: k :: a :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP11, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_swap11 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: k :: l :: t).length - 12 + 12 >
          1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

end Reasoning.Theory

namespace Reasoning.Reach

-- PROMOTE -> Reasoning.Reach: generic `RD.dup10`, matching the existing `RD.dup2`-`RD.dup8`.
theorem RD.dup10 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg h i j : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: t) mem aw
      rdata acc k C)
    (hdec : decode code pc = some (.DUP10, .none)) (hov : t.length + 11 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (j :: a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => blindAuctionDup10_xstep hc hp hdec hs hov)

theorem RD.dup11 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg h i j l : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: l :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP11, .none)) (hov : t.length + 12 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (l :: a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: l :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => blindAuctionDup11_xstep hc hp hdec hs hov)

theorem RD.swap5 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP5, .none)) (hov : t.length + 6 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (f :: b :: c :: d :: e :: a :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  RD.blindAuctionSwap5 rd hdec hov

theorem RD.swap6 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f h : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: h :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP6, .none)) (hov : t.length + 7 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (h :: b :: c :: d :: e :: f :: a :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => blindAuctionSwap6_xstep hc hp hdec hs hov)

theorem RD.swap7 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg h : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: h :: t) mem aw rdata acc
      k C)
    (hdec : decode code pc = some (.SWAP7, .none)) (hov : t.length + 8 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (h :: b :: c :: d :: e :: f :: gg :: a :: t) mem aw
      rdata acc (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => blindAuctionSwap7_xstep hc hp hdec hs hov)

theorem RD.swap8 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg h i : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: h :: i :: t) mem aw
      rdata acc k C)
    (hdec : decode code pc = some (.SWAP8, .none)) (hov : t.length + 9 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (i :: b :: c :: d :: e :: f :: gg :: h :: a :: t) mem
      aw rdata acc (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => blindAuctionSwap8_xstep hc hp hdec hs hov)

theorem RD.swap10 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg h i j l : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: l :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP10, .none)) (hov : t.length + 11 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (l :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: a :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => blindAuctionSwap10_xstep hc hp hdec hs hov)

theorem RD.swap11 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg h i j l m : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: l :: m :: t) mem aw rdata acc
      k C)
    (hdec : decode code pc = some (.SWAP11, .none)) (hov : t.length + 12 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (m :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: l :: a :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => blindAuctionSwap11_xstep hc hp hdec hs hov)

open BlindAuction

theorem RD.blindAuctionRevealDecodeEmptyArray1713 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {start ennd ret headOff : UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd : RD blindAuctionBytecode ee g s0 ⟨1713⟩
        (start :: ennd :: ret :: headOff :: R) mem aw rdata acc k C)
    (hstart : UInt256.slt (start + ⟨31⟩) ennd = ⟨1⟩)
    (hlen : uInt256OfByteArray (ee.calldata.readBytes start.toNat 32) = ⟨0⟩)
    (hend : UInt256.gt (start + ⟨0⟩ + ⟨32⟩) ennd = ⟨0⟩)
    (hret : (D_J blindAuctionBytecode 0).contains ret = true) (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD blindAuctionBytecode ee g s0 ret
      (⟨0⟩ :: (start + ⟨32⟩) :: headOff :: R) mem aw rdata acc k' C' := by
  have rd1729 := evm_run rd with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt,
    push2 ⟨1729⟩, jumpiT (by rw [hstart]; decide) (by jump_dest)]
  have rd1733 := evm_run rd1729 with [jumpdest, pop, dup2, calldataload]
  have rd1742 := RD.pushConst rd1733 ⟨18446744073709551615⟩ (width := 8) (op := .PUSH8)
    (by decide) (by native_decide) (by evm_ov)
  have rd1752 := evm_run rd1742 with [
    dup2, gt, iszero, push2 ⟨1752⟩, jumpiT (by rw [hlen]; decide) (by jump_dest)]
  obtain ⟨_, _, rd1752z⟩ : ∃ k' C', RD blindAuctionBytecode ee g s0 ⟨1752⟩
      (⟨0⟩ :: ⟨0⟩ :: start :: ennd :: ret :: headOff :: R) mem aw rdata acc k' C' :=
    ⟨_, _, by simpa [hlen] using rd1752⟩
  have rd1778 := evm_run rd1752z with [
    jumpdest, push1 ⟨32⟩, dup4, add, swap2, pop, dup4, push1 ⟨32⟩,
    dup3, push1 ⟨5⟩, shl, dup6, add, add, gt, iszero, push2 ⟨1778⟩,
    jumpiT
      (by
        rw [show UInt256.shiftLeft (⟨0⟩ : UInt256) ⟨5⟩ = ⟨0⟩ by decide]
        rw [hend]
        decide)
      (by jump_dest)]
  exact ⟨_, _, evm_run rd1778 with [
    jumpdest, swap3, pop, swap3, swap1, pop, jump hret]⟩

theorem RD.blindAuctionRevealDecodeArray1713 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {start ennd ret headOff len : UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd : RD blindAuctionBytecode ee g s0 ⟨1713⟩
        (start :: ennd :: ret :: headOff :: R) mem aw rdata acc k C)
    (hstart : UInt256.slt (start + ⟨31⟩) ennd = ⟨1⟩)
    (hlen : uInt256OfByteArray (ee.calldata.readBytes start.toNat 32) = len)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hend : UInt256.gt ((start + UInt256.shiftLeft len ⟨5⟩) + ⟨32⟩) ennd = ⟨0⟩)
    (hret : (D_J blindAuctionBytecode 0).contains ret = true) (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD blindAuctionBytecode ee g s0 ret
      (len :: (start + ⟨32⟩) :: headOff :: R) mem aw rdata acc k' C' := by
  have rd1729 := evm_run rd with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt,
    push2 ⟨1729⟩, jumpiT (by rw [hstart]; decide) (by jump_dest)]
  have rd1733 := evm_run rd1729 with [jumpdest, pop, dup2, calldataload]
  have rd1742 := RD.pushConst rd1733 ⟨18446744073709551615⟩ (width := 8) (op := .PUSH8)
    (by decide) (by native_decide) (by evm_ov)
  have rd1752 := evm_run rd1742 with [
    dup2, gt, iszero, push2 ⟨1752⟩, jumpiT
      (by
        rw [hlen, hlenMax]
        decide)
      (by jump_dest)]
  obtain ⟨_, _, rd1752z⟩ : ∃ k' C', RD blindAuctionBytecode ee g s0 ⟨1752⟩
      (len :: ⟨0⟩ :: start :: ennd :: ret :: headOff :: R) mem aw rdata acc k' C' :=
    ⟨_, _, by simpa [hlen] using rd1752⟩
  have rd1778 := evm_run rd1752z with [
    jumpdest, push1 ⟨32⟩, dup4, add, swap2, pop, dup4, push1 ⟨32⟩,
    dup3, push1 ⟨5⟩, shl, dup6, add, add, gt, iszero, push2 ⟨1778⟩,
    jumpiT
      (by
        rw [hend]
        decide)
      (by jump_dest)]
  exact ⟨_, _, evm_run rd1778 with [
    jumpdest, swap3, pop, swap3, swap1, pop, jump hret]⟩

theorem RD.blindAuctionRevealDecodeArray1713_startRevert {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat}
    {start ennd ret headOff : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd : RD blindAuctionBytecode ee g s0 ⟨1713⟩
      (start :: ennd :: ret :: headOff :: R) mem aw rdata acc k C)
    (hstart : UInt256.slt (start + ⟨31⟩) ennd = ⟨0⟩)
    (hov : R.length + 12 ≤ 1024) :
    RDrev blindAuctionBytecode g s0 := by
  have rd1728 := evm_run rd with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt,
    push2 ⟨1729⟩, jumpiNT
      (by exact hstart),
    push0, push0]
  exact RD.rev _ rd1728 (by decide)
    (fun s haws hstks => by rw [memExpRevertZeroOff s hstks, haws])
    (by evm_ov)

theorem RD.blindAuctionRevealDecodeArray1713_lengthRevert {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat}
    {start ennd ret headOff len : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd : RD blindAuctionBytecode ee g s0 ⟨1713⟩
      (start :: ennd :: ret :: headOff :: R) mem aw rdata acc k C)
    (hstart : UInt256.slt (start + ⟨31⟩) ennd = ⟨1⟩)
    (hlen : uInt256OfByteArray (ee.calldata.readBytes start.toNat 32) = len)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨1⟩)
    (hov : R.length + 12 ≤ 1024) :
    RDrev blindAuctionBytecode g s0 := by
  have rd1729 := evm_run rd with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt,
    push2 ⟨1729⟩, jumpiT
      (by
        rw [hstart]
        decide)
      (by jump_dest)]
  have rd1733 := evm_run rd1729 with [jumpdest, pop, dup2, calldataload]
  have rd1742 := RD.pushConst rd1733 ⟨18446744073709551615⟩ (width := 8) (op := .PUSH8)
    (by decide) (by native_decide) (by evm_ov)
  have rd1751 := evm_run rd1742 with [
    dup2, gt, iszero, push2 ⟨1752⟩, jumpiNT
      (by
        rw [hlen, hlenMax]
        decide),
    push0, push0]
  exact RD.rev _ rd1751 (by decide)
    (fun s haws hstks => by rw [memExpRevertZeroOff s hstks, haws])
    (by evm_ov)

theorem RD.blindAuctionRevealDecodeArray1713_endRevert {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat}
    {start ennd ret headOff len : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd : RD blindAuctionBytecode ee g s0 ⟨1713⟩
      (start :: ennd :: ret :: headOff :: R) mem aw rdata acc k C)
    (hstart : UInt256.slt (start + ⟨31⟩) ennd = ⟨1⟩)
    (hlen : uInt256OfByteArray (ee.calldata.readBytes start.toNat 32) = len)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hend : UInt256.gt ((start + UInt256.shiftLeft len ⟨5⟩) + ⟨32⟩) ennd = ⟨1⟩)
    (hov : R.length + 12 ≤ 1024) :
    RDrev blindAuctionBytecode g s0 := by
  have rd1729 := evm_run rd with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt,
    push2 ⟨1729⟩, jumpiT
      (by
        rw [hstart]
        decide)
      (by jump_dest)]
  have rd1733 := evm_run rd1729 with [jumpdest, pop, dup2, calldataload]
  have rd1742 := RD.pushConst rd1733 ⟨18446744073709551615⟩ (width := 8) (op := .PUSH8)
    (by decide) (by native_decide) (by evm_ov)
  have rd1752 := evm_run rd1742 with [
    dup2, gt, iszero, push2 ⟨1752⟩, jumpiT
      (by
        rw [hlen, hlenMax]
        decide)
      (by jump_dest)]
  obtain ⟨_, _, rd1752z⟩ : ∃ k' C', RD blindAuctionBytecode ee g s0 ⟨1752⟩
      (len :: ⟨0⟩ :: start :: ennd :: ret :: headOff :: R) mem aw rdata acc k' C' :=
    ⟨_, _, by simpa [hlen] using rd1752⟩
  have rd1777 := evm_run rd1752z with [
    jumpdest, push1 ⟨32⟩, dup4, add, swap2, pop, dup4, push1 ⟨32⟩,
    dup3, push1 ⟨5⟩, shl, dup6, add, add, gt, iszero, push2 ⟨1778⟩,
    jumpiNT
      (by
        rw [hend]
        decide),
    push0, push0]
  exact RD.rev _ rd1777 (by decide)
    (fun s haws hstks => by rw [memExpRevertZeroOff s hstks, haws])
    (by evm_ov)

end Reasoning.Reach

namespace BlindAuction

/-! ## `reveal(uint256[],bool[],bytes32[])` outer body facts -/

abbrev revealMaxU64 : UInt256 := ⟨18446744073709551615⟩

abbrev revealValuesOffsetWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev revealFakesOffsetWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev revealSecretsOffsetWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

theorem blindAuctionRevealSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x90, 0x0f, 0x08, 0x0a]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x90, 0x0f, 0x08, 0x0a]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem blindAuctionDispatch_reveal {cd : ByteArray}
    (hsel : ((⟨#[0x90, 0x0f, 0x08, 0x0a]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg blindAuctionContract cd = some revealTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x90, 0x0f, 0x08, 0x0a]⟩ : ByteArray) :=
    (blindAuctionByteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [bidTransition])
    (post := [withdrawTransition, auctionEndTransition, beneficiaryGetter, biddingEndGetter,
      revealEndGetter, endedGetter, highestBidderGetter, highestBidGetter, bidsGetter])
    rfl ?_ (by rw [selectorOf, blindAuctionRevealSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl
  rw [selectorOf, blindAuctionBidSelectorBytes, hcd]
  decide

theorem blindAuctionX_reveal_nonpayable {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue ≠ ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨387⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd387⟩ := hreach
  have rd395 := evm_run rd387 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨398⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv)]
  exact rd395.revertStub (by decide) (by decide) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem blindAuctionX_reveal_decodeEntry {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨387⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1785⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨413⟩, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd387⟩ := hreach
  have rd1785 := evm_run rd387 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨398⟩,
    jumpiT (by rw [hwv]; decide) (by jump_dest),
    jumpdest, pop, push2 ⟨276⟩, push2 ⟨413⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨1785⟩, jump (by jump_dest)]
  exact ⟨_, _, rd1785⟩

theorem blindAuctionRevealX_decode_head_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩)
    (hentry : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1785⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨413⟩, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1785⟩ := hentry
  exact evm_run rd1785 with [
    jumpdest, push0, push0, push0, push0, push0, push0, push1 ⟨96⟩,
    dup8, dup10, sub, slt, iszero, push2 ⟨1806⟩,
    jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem blindAuctionRevealX_decode_head_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨0⟩)
    (hentry : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1785⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨413⟩, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1806⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨413⟩, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1785⟩ := hentry
  have rd1806 := evm_run rd1785 with [
    jumpdest, push0, push0, push0, push0, push0, push0, push1 ⟨96⟩,
    dup8, dup10, sub, slt, iszero, push2 ⟨1806⟩,
    jumpiT (by rw [hslt]; decide) (by jump_dest) ]
  exact ⟨_, _, rd1806⟩

theorem blindAuctionRevealX_decode_valuesOffset_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hgt : UInt256.gt (revealValuesOffsetWord I) revealMaxU64 = ⟨1⟩)
    (hhead : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1806⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨413⟩, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1806⟩ := hhead
  have rd1809 := evm_run rd1806 with [jumpdest, dup7, calldataload]
  have rd1818 := RD.pushConst rd1809 revealMaxU64 (width := 8) (op := .PUSH8)
    (by decide) (by native_decide) (by evm_ov)
  exact evm_run rd1818 with [
    dup2, gt, iszero, push2 ⟨1828⟩, jumpiNT (by
      have hgt' :
          UInt256.gt
              (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
              revealMaxU64 = ⟨1⟩ := by
        simpa [revealValuesOffsetWord, calldataWord] using hgt
      rw [hgt']; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem blindAuctionRevealX_decode_valuesOffset_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hgt : UInt256.gt (revealValuesOffsetWord I) revealMaxU64 = ⟨0⟩)
    (hhead : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1806⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨413⟩, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1828⟩
      [revealValuesOffsetWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨413⟩, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1806⟩ := hhead
  have rd1809 := evm_run rd1806 with [jumpdest, dup7, calldataload]
  have rd1818 := RD.pushConst rd1809 revealMaxU64 (width := 8) (op := .PUSH8)
    (by decide) (by native_decide) (by evm_ov)
  have rd1828 := evm_run rd1818 with [
    dup2, gt, iszero, push2 ⟨1828⟩, jumpiT (by
      have hgt' :
          UInt256.gt
              (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
              revealMaxU64 = ⟨0⟩ := by
        simpa [revealValuesOffsetWord, calldataWord] using hgt
      rw [hgt']; decide) (by jump_dest) ]
  exact ⟨_, _, by simpa [revealValuesOffsetWord, calldataWord] using rd1828⟩

theorem ugt_eq_zero_of_ne_one {a b : UInt256}
    (h : ¬ UInt256.gt a b = ⟨1⟩) : UInt256.gt a b = ⟨0⟩ := by
  by_cases hab : a > b
  · exact False.elim (h (by
      simp [UInt256.gt, UInt256.fromBool, Bool.toUInt256, hab]
      decide))
  · simp [UInt256.gt, UInt256.fromBool, Bool.toUInt256, hab]
    decide

theorem slt_zero_low_high {a b : UInt256}
    (ha : a.toNat < 2 ^ 255) (hb : 2 ^ 255 ≤ b.toNat) :
    UInt256.slt a b = ⟨0⟩ := by
  unfold UInt256.slt UInt256.sltBool UInt256.fromBool Bool.toUInt256
  rw [if_neg (by omega : ¬ a.toNat ≥ 2 ^ 255), if_pos hb]
  rfl

theorem blindAuctionRevealDecodeValuesCall1806_to_1713
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : Nat}
    {sel : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd : RD blindAuctionBytecode ee g s0 ⟨1806⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat ee.calldata.size, ⟨413⟩, ⟨276⟩, sel]
      mem aw rdata acc k C)
    (hvaluesGt : UInt256.gt (revealValuesOffsetWord ee) revealMaxU64 = ⟨0⟩) :
    ∃ k' C', RD blindAuctionBytecode ee g s0 ⟨1713⟩
      [⟨4⟩ + revealValuesOffsetWord ee, UInt256.ofNat ee.calldata.size, ⟨1840⟩,
        revealValuesOffsetWord ee, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat ee.calldata.size, ⟨413⟩, ⟨276⟩, sel]
      mem aw rdata acc k' C' := by
  have rd1809 := evm_run rd with [jumpdest, dup7, calldataload]
  have rd1818 := RD.pushConst rd1809 revealMaxU64 (width := 8) (op := .PUSH8)
    (by decide) (by native_decide) (by evm_ov)
  have rd1828 := evm_run rd1818 with [
    dup2, gt, iszero, push2 ⟨1828⟩, jumpiT
      (by
        have hgt' :
            UInt256.gt
                (uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
                revealMaxU64 = ⟨0⟩ := by
          simpa [revealValuesOffsetWord, calldataWord] using hvaluesGt
        rw [hgt']
        decide)
      (by jump_dest)]
  have rd1829 := evm_run rd1828 with [jumpdest, push2 ⟨1840⟩]
  have rd1833 := RD.dup10 rd1829 (by decide) (by simp)
  have rd1834 := evm_run rd1833 with [dup3]
  have rd1835 := RD.dup11 rd1834 (by decide) (by simp)
  have rd1839 := evm_run rd1835 with [add, push2 ⟨1713⟩, jump (by jump_dest)]
  exact ⟨_, _, by simpa [revealValuesOffsetWord, calldataWord] using rd1839⟩

theorem uslt_eq_zero_of_ne_one {a b : UInt256}
    (h : ¬ UInt256.slt a b = ⟨1⟩) : UInt256.slt a b = ⟨0⟩ := by
  unfold UInt256.slt UInt256.sltBool UInt256.fromBool Bool.toUInt256
  by_cases ha : a.toNat ≥ 2 ^ 255
  · rw [if_pos ha]
    by_cases hb : b.toNat ≥ 2 ^ 255
    · rw [if_pos hb]
      by_cases hab : a < b
      · exfalso
        apply h
        unfold UInt256.slt UInt256.sltBool UInt256.fromBool Bool.toUInt256
        rw [if_pos ha, if_pos hb, if_pos (decide_eq_true hab)]
        native_decide
      · have hdf : ¬ decide (a < b) = true := by
          rw [decide_eq_false hab]
          decide
        rw [if_neg hdf]
        native_decide
    · rw [if_neg hb]
      exfalso
      apply h
      unfold UInt256.slt UInt256.sltBool UInt256.fromBool Bool.toUInt256
      rw [if_pos ha, if_neg hb]
      native_decide
  · rw [if_neg ha]
    by_cases hb : b.toNat ≥ 2 ^ 255
    · rw [if_pos hb]
      native_decide
    · rw [if_neg hb]
      by_cases hab : a < b
      · exfalso
        apply h
        unfold UInt256.slt UInt256.sltBool UInt256.fromBool Bool.toUInt256
        rw [if_neg ha, if_neg hb, if_pos (decide_eq_true hab)]
        native_decide
      · have hdf : ¬ decide (a < b) = true := by
          rw [decide_eq_false hab]
          decide
        rw [if_neg hdf]
        native_decide

theorem blindAuctionRevealDecodeFakesOffset1840_reverts
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {I} {g : Sat256}
    {s0 : State} {k C : Nat}
    {valuesLen valuesEnd : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1840⟩
      [valuesLen, valuesEnd, revealValuesOffsetWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩,
        ⟨0⟩, ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨413⟩, ⟨276⟩,
        blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hfakesGt : UInt256.gt (revealFakesOffsetWord I) revealMaxU64 = ⟨1⟩) :
    RDrev blindAuctionBytecode g s0 := by
  have rd1841 := evm_run rd with [jumpdest, swap1]
  have rd1843 := RD.swap8 rd1841 (by decide) (by simp)
  have rd1844 := evm_run rd1843 with [pop]
  have rd1845 := RD.swap6 rd1844 (by decide) (by simp)
  have rd1847 := evm_run rd1845 with [pop, pop]
  have rd1852 := evm_run rd1847 with [push1 ⟨32⟩, dup8, add, calldataload]
  have rd1861 := RD.pushConst rd1852 revealMaxU64 (width := 8) (op := .PUSH8)
    (by decide) (by native_decide) (by evm_ov)
  exact evm_run rd1861 with [
    dup2, gt, iszero, push2 ⟨1871⟩, jumpiNT
      (by
        have hgt' :
            UInt256.gt
                (uInt256OfByteArray
                  (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨32⟩).toNat 32))
                revealMaxU64 = ⟨1⟩ := by
          simpa [revealFakesOffsetWord, calldataWord] using hfakesGt
        rw [hgt']
        decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov)]

theorem blindAuctionRevealDecodeFakesCall1840_to_1713
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : Nat}
    {valuesLen valuesEnd sel : UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd : RD blindAuctionBytecode ee g s0 ⟨1840⟩
      [valuesLen, valuesEnd, revealValuesOffsetWord ee, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩,
        ⟨0⟩, ⟨0⟩, ⟨4⟩, UInt256.ofNat ee.calldata.size, ⟨413⟩, ⟨276⟩, sel]
      mem aw rdata acc k C)
    (hfakesGt : UInt256.gt (revealFakesOffsetWord ee) revealMaxU64 = ⟨0⟩) :
    ∃ k' C', RD blindAuctionBytecode ee g s0 ⟨1713⟩
      [⟨4⟩ + revealFakesOffsetWord ee, UInt256.ofNat ee.calldata.size, ⟨1883⟩,
        revealFakesOffsetWord ee, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, valuesLen, valuesEnd,
        ⟨4⟩, UInt256.ofNat ee.calldata.size, ⟨413⟩, ⟨276⟩, sel]
      mem aw rdata acc k' C' := by
  have rd1841 := evm_run rd with [jumpdest, swap1]
  have rd1843 := RD.swap8 rd1841 (by decide) (by simp)
  have rd1844 := evm_run rd1843 with [pop]
  have rd1845 := RD.swap6 rd1844 (by decide) (by simp)
  have rd1847 := evm_run rd1845 with [pop, pop]
  have rd1852 := evm_run rd1847 with [push1 ⟨32⟩, dup8, add, calldataload]
  have rd1861 := RD.pushConst rd1852 revealMaxU64 (width := 8) (op := .PUSH8)
    (by decide) (by native_decide) (by evm_ov)
  have rd1871 := evm_run rd1861 with [
    dup2, gt, iszero, push2 ⟨1871⟩, jumpiT
      (by
        have hgt' :
            UInt256.gt
                (uInt256OfByteArray
                  (ee.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨32⟩).toNat 32))
                revealMaxU64 = ⟨0⟩ := by
          simpa [revealFakesOffsetWord, calldataWord] using hfakesGt
        rw [hgt']
        decide)
      (by jump_dest)]
  have rd1875 := evm_run rd1871 with [jumpdest, push2 ⟨1883⟩]
  have rd1876 := RD.dup10 rd1875 (by decide) (by simp)
  have rd1877 := evm_run rd1876 with [dup3]
  have rd1878 := RD.dup11 rd1877 (by decide) (by simp)
  have rd1882 := evm_run rd1878 with [add, push2 ⟨1713⟩, jump (by jump_dest)]
  exact ⟨_, _, by simpa [revealFakesOffsetWord, calldataWord] using rd1882⟩

theorem blindAuctionRevealDecodeSecretsOffset1883_reverts
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {I} {g : Sat256}
    {s0 : State} {k C : Nat}
    {valuesLen valuesEnd fakesLen fakesEnd : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1883⟩
      [fakesLen, fakesEnd, revealFakesOffsetWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩,
        ⟨0⟩, valuesLen, valuesEnd, ⟨4⟩, UInt256.ofNat I.calldata.size,
        ⟨413⟩, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsecretsGt : UInt256.gt (revealSecretsOffsetWord I) revealMaxU64 = ⟨1⟩) :
    RDrev blindAuctionBytecode g s0 := by
  have rd1884 := evm_run rd with [jumpdest, swap1]
  have rd1885 := RD.swap6 rd1884 (by decide) (by simp)
  have rd1886 := evm_run rd1885 with [pop, swap4, pop, pop]
  have rd1895 := evm_run rd1886 with [push1 ⟨64⟩, dup8, add, calldataload]
  have rd1904 := RD.pushConst rd1895 revealMaxU64 (width := 8) (op := .PUSH8)
    (by decide) (by native_decide) (by evm_ov)
  exact evm_run rd1904 with [
    dup2, gt, iszero, push2 ⟨1914⟩, jumpiNT
      (by
        have hgt' :
            UInt256.gt
                (uInt256OfByteArray
                  (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨64⟩).toNat 32))
                revealMaxU64 = ⟨1⟩ := by
          simpa [revealSecretsOffsetWord, calldataWord] using hsecretsGt
        rw [hgt']
        decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov)]

theorem blindAuctionRevealDecodeSecretsCall1883_to_1713
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : Nat}
    {valuesLen valuesEnd fakesLen fakesEnd sel : UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd : RD blindAuctionBytecode ee g s0 ⟨1883⟩
      [fakesLen, fakesEnd, revealFakesOffsetWord ee, ⟨0⟩, ⟨0⟩, ⟨0⟩,
        ⟨0⟩, valuesLen, valuesEnd, ⟨4⟩, UInt256.ofNat ee.calldata.size,
        ⟨413⟩, ⟨276⟩, sel]
      mem aw rdata acc k C)
    (hsecretsGt : UInt256.gt (revealSecretsOffsetWord ee) revealMaxU64 = ⟨0⟩) :
    ∃ k' C', RD blindAuctionBytecode ee g s0 ⟨1713⟩
      [⟨4⟩ + revealSecretsOffsetWord ee, UInt256.ofNat ee.calldata.size, ⟨1926⟩,
        revealSecretsOffsetWord ee, ⟨0⟩, ⟨0⟩, fakesLen, fakesEnd, valuesLen,
        valuesEnd, ⟨4⟩, UInt256.ofNat ee.calldata.size, ⟨413⟩, ⟨276⟩, sel]
      mem aw rdata acc k' C' := by
  have rd1884 := evm_run rd with [jumpdest, swap1]
  have rd1885 := RD.swap6 rd1884 (by decide) (by simp)
  have rd1886 := evm_run rd1885 with [pop, swap4, pop, pop]
  have rd1895 := evm_run rd1886 with [push1 ⟨64⟩, dup8, add, calldataload]
  have rd1904 := RD.pushConst rd1895 revealMaxU64 (width := 8) (op := .PUSH8)
    (by decide) (by native_decide) (by evm_ov)
  have rd1914 := evm_run rd1904 with [
    dup2, gt, iszero, push2 ⟨1914⟩, jumpiT
      (by
        have hgt' :
            UInt256.gt
                (uInt256OfByteArray
                  (ee.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨64⟩).toNat 32))
                revealMaxU64 = ⟨0⟩ := by
          simpa [revealSecretsOffsetWord, calldataWord] using hsecretsGt
        rw [hgt']
        decide)
      (by jump_dest)]
  have rd1918 := evm_run rd1914 with [jumpdest, push2 ⟨1926⟩]
  have rd1919 := RD.dup10 rd1918 (by decide) (by simp)
  have rd1920 := evm_run rd1919 with [dup3]
  have rd1921 := RD.dup11 rd1920 (by decide) (by simp)
  have rd1925 := evm_run rd1921 with [add, push2 ⟨1713⟩, jump (by jump_dest)]
  exact ⟨_, _, by simpa [revealSecretsOffsetWord, calldataWord] using rd1925⟩

theorem blindAuctionRevealDecode1806_hugeDynamic_reverts
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : Nat}
    (rd : RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1806⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨413⟩, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcalldataGe : 2 ^ 255 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) :
    RDrev blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  by_cases hvaluesGt : UInt256.gt (revealValuesOffsetWord I) revealMaxU64 = ⟨1⟩
  · exact blindAuctionRevealX_decode_valuesOffset_revert
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hvaluesGt ⟨k, C, rd⟩
  · have hvaluesGt0 :
        UInt256.gt (revealValuesOffsetWord I) revealMaxU64 = ⟨0⟩ :=
      ugt_eq_zero_of_ne_one hvaluesGt
    obtain ⟨_, _, rd1713⟩ :=
      blindAuctionRevealDecodeValuesCall1806_to_1713 rd hvaluesGt0
    have hoffLe : (revealValuesOffsetWord I).toNat ≤ revealMaxU64.toNat := by
      by_contra hle
      have hgt1 : UInt256.gt (revealValuesOffsetWord I) revealMaxU64 = ⟨1⟩ := by
        exact ugt_one (Nat.lt_of_not_ge hle)
      exact hvaluesGt hgt1
    have hstartNat :
        (((⟨4⟩ : UInt256) + revealValuesOffsetWord I) + ⟨31⟩).toNat =
          4 + (revealValuesOffsetWord I).toNat + 31 := by
      rw [uadd_toNat, uadd_toNat]
      rw [show (⟨4⟩ : UInt256).toNat = 4 by decide,
        show (⟨31⟩ : UInt256).toNat = 31 by decide]
      have hleft :
          (4 + (revealValuesOffsetWord I).toNat) % UInt256.size =
            4 + (revealValuesOffsetWord I).toNat := by
        apply Nat.mod_eq_of_lt
        have hmax : revealMaxU64.toNat = 18446744073709551615 := by decide
        omega
      rw [hleft]
      apply Nat.mod_eq_of_lt
      have hmax : revealMaxU64.toNat = 18446744073709551615 := by decide
      omega
    have hstartSmall :
        (((⟨4⟩ : UInt256) + revealValuesOffsetWord I) + ⟨31⟩).toNat < 2 ^ 255 := by
      rw [hstartNat]
      have hmax : revealMaxU64.toNat = 18446744073709551615 := by decide
      omega
    have hendHigh : 2 ^ 255 ≤ (UInt256.ofNat I.calldata.size).toNat := by
      rw [ulit_toNat' I.calldata.size hsize]
      exact hcalldataGe
    have hstart :
        UInt256.slt (((⟨4⟩ : UInt256) + revealValuesOffsetWord I) + ⟨31⟩)
          (UInt256.ofNat I.calldata.size) = ⟨0⟩ :=
      slt_zero_low_high hstartSmall hendHigh
    exact RD.blindAuctionRevealDecodeArray1713_startRevert rd1713 hstart (by simp)

theorem blindAuctionRevealDecodeEmptyArrays1806_to_413
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : Nat}
    {sel : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd : RD blindAuctionBytecode ee g s0 ⟨1806⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat ee.calldata.size, ⟨413⟩, ⟨276⟩, sel]
      mem aw rdata acc k C)
    (hvaluesGt : UInt256.gt (revealValuesOffsetWord ee) revealMaxU64 = ⟨0⟩)
    (hvaluesStart :
      UInt256.slt ((⟨4⟩ + revealValuesOffsetWord ee) + ⟨31⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨1⟩)
    (hvaluesLen :
      uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ + revealValuesOffsetWord ee).toNat 32)
        = ⟨0⟩)
    (hvaluesEnd :
      UInt256.gt (((⟨4⟩ + revealValuesOffsetWord ee) + ⟨0⟩) + ⟨32⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨0⟩)
    (hfakesGt : UInt256.gt (revealFakesOffsetWord ee) revealMaxU64 = ⟨0⟩)
    (hfakesStart :
      UInt256.slt ((⟨4⟩ + revealFakesOffsetWord ee) + ⟨31⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨1⟩)
    (hfakesLen :
      uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ + revealFakesOffsetWord ee).toNat 32)
        = ⟨0⟩)
    (hfakesEnd :
      UInt256.gt (((⟨4⟩ + revealFakesOffsetWord ee) + ⟨0⟩) + ⟨32⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨0⟩)
    (hsecretsGt : UInt256.gt (revealSecretsOffsetWord ee) revealMaxU64 = ⟨0⟩)
    (hsecretsStart :
      UInt256.slt ((⟨4⟩ + revealSecretsOffsetWord ee) + ⟨31⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨1⟩)
    (hsecretsLen :
      uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ + revealSecretsOffsetWord ee).toNat 32)
        = ⟨0⟩)
    (hsecretsEnd :
      UInt256.gt (((⟨4⟩ + revealSecretsOffsetWord ee) + ⟨0⟩) + ⟨32⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨0⟩) :
    ∃ k' C', RD blindAuctionBytecode ee g s0 ⟨413⟩
      [⟨0⟩, (⟨4⟩ + revealSecretsOffsetWord ee) + ⟨32⟩,
        ⟨0⟩, (⟨4⟩ + revealFakesOffsetWord ee) + ⟨32⟩,
        ⟨0⟩, (⟨4⟩ + revealValuesOffsetWord ee) + ⟨32⟩, ⟨276⟩, sel]
      mem aw rdata acc k' C' := by
  obtain ⟨_, _, rd1713v⟩ := blindAuctionRevealDecodeValuesCall1806_to_1713 rd hvaluesGt
  obtain ⟨_, _, rd1840⟩ :=
    RD.blindAuctionRevealDecodeEmptyArray1713 rd1713v hvaluesStart hvaluesLen
      hvaluesEnd (by jump_dest) (by simp)
  have rd1841 := evm_run rd1840 with [jumpdest, swap1]
  have rd1843 := RD.swap8 rd1841 (by decide) (by simp)
  have rd1844 := evm_run rd1843 with [pop]
  have rd1845 := RD.swap6 rd1844 (by decide) (by simp)
  have rd1847 := evm_run rd1845 with [pop, pop]
  have rd1852 := evm_run rd1847 with [push1 ⟨32⟩, dup8, add, calldataload]
  have rd1861 := RD.pushConst rd1852 revealMaxU64 (width := 8) (op := .PUSH8)
    (by decide) (by native_decide) (by evm_ov)
  have rd1871 := evm_run rd1861 with [
    dup2, gt, iszero, push2 ⟨1871⟩, jumpiT
      (by
        have hgt' :
            UInt256.gt
                (uInt256OfByteArray
                  (ee.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨32⟩).toNat 32))
                revealMaxU64 = ⟨0⟩ := by
          simpa [revealFakesOffsetWord, calldataWord] using hfakesGt
        rw [hgt']
        decide)
      (by jump_dest)]
  have rd1875 := evm_run rd1871 with [jumpdest, push2 ⟨1883⟩]
  have rd1876 := RD.dup10 rd1875 (by decide) (by simp)
  have rd1877 := evm_run rd1876 with [dup3]
  have rd1878 := RD.dup11 rd1877 (by decide) (by simp)
  have rd1882 := evm_run rd1878 with [add, push2 ⟨1713⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd1883⟩ :=
    RD.blindAuctionRevealDecodeEmptyArray1713 rd1882 hfakesStart hfakesLen
      hfakesEnd (by jump_dest) (by simp)
  have rd1884 := evm_run rd1883 with [jumpdest, swap1]
  have rd1885 := RD.swap6 rd1884 (by decide) (by simp)
  have rd1886 := evm_run rd1885 with [pop, swap4, pop, pop]
  have rd1895 := evm_run rd1886 with [push1 ⟨64⟩, dup8, add, calldataload]
  have rd1904 := RD.pushConst rd1895 revealMaxU64 (width := 8) (op := .PUSH8)
    (by decide) (by native_decide) (by evm_ov)
  have rd1914 := evm_run rd1904 with [
    dup2, gt, iszero, push2 ⟨1914⟩, jumpiT
      (by
        have hgt' :
            UInt256.gt
                (uInt256OfByteArray
                  (ee.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨64⟩).toNat 32))
                revealMaxU64 = ⟨0⟩ := by
          simpa [revealSecretsOffsetWord, calldataWord] using hsecretsGt
        rw [hgt']
        decide)
      (by jump_dest)]
  have rd1918 := evm_run rd1914 with [jumpdest, push2 ⟨1926⟩]
  have rd1919 := RD.dup10 rd1918 (by decide) (by simp)
  have rd1920 := evm_run rd1919 with [dup3]
  have rd1921 := RD.dup11 rd1920 (by decide) (by simp)
  have rd1925 := evm_run rd1921 with [add, push2 ⟨1713⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd1926⟩ :=
    RD.blindAuctionRevealDecodeEmptyArray1713 rd1925 hsecretsStart hsecretsLen
      hsecretsEnd (by jump_dest) (by simp)
  have rd1927 := evm_run rd1926 with [jumpdest]
  have rd1928 := RD.swap8 rd1927 (by decide) (by simp)
  have rd1929 := RD.swap11 rd1928 (by decide) (by simp)
  have rd1930 := RD.swap7 rd1929 (by decide) (by simp)
  have rd1931 := RD.swap10 rd1930 (by decide) (by simp)
  have rd1932 := evm_run rd1931 with [pop]
  have rd1933 := RD.swap5 rd1932 (by decide) (by simp)
  have rd1934 := RD.swap8 rd1933 (by decide) (by simp)
  have rd1935 := evm_run rd1934 with [pop, swap3]
  have rd1937 := RD.swap6 rd1935 (by decide) (by simp)
  have rd1939 := evm_run rd1937 with [swap4]
  have rd1940 := RD.swap5 rd1939 (by decide) (by simp)
  have rd1943 := evm_run rd1940 with [swap3, pop, pop, pop, jump (by jump_dest)]
  exact ⟨_, _, by simpa using rd1943⟩

theorem blindAuctionRevealDecodeEmptyArrays1806_to_887
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : Nat}
    {sel : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd : RD blindAuctionBytecode ee g s0 ⟨1806⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat ee.calldata.size, ⟨413⟩, ⟨276⟩, sel]
      mem aw rdata acc k C)
    (hvaluesGt : UInt256.gt (revealValuesOffsetWord ee) revealMaxU64 = ⟨0⟩)
    (hvaluesStart :
      UInt256.slt ((⟨4⟩ + revealValuesOffsetWord ee) + ⟨31⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨1⟩)
    (hvaluesLen :
      uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ + revealValuesOffsetWord ee).toNat 32)
        = ⟨0⟩)
    (hvaluesEnd :
      UInt256.gt (((⟨4⟩ + revealValuesOffsetWord ee) + ⟨0⟩) + ⟨32⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨0⟩)
    (hfakesGt : UInt256.gt (revealFakesOffsetWord ee) revealMaxU64 = ⟨0⟩)
    (hfakesStart :
      UInt256.slt ((⟨4⟩ + revealFakesOffsetWord ee) + ⟨31⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨1⟩)
    (hfakesLen :
      uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ + revealFakesOffsetWord ee).toNat 32)
        = ⟨0⟩)
    (hfakesEnd :
      UInt256.gt (((⟨4⟩ + revealFakesOffsetWord ee) + ⟨0⟩) + ⟨32⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨0⟩)
    (hsecretsGt : UInt256.gt (revealSecretsOffsetWord ee) revealMaxU64 = ⟨0⟩)
    (hsecretsStart :
      UInt256.slt ((⟨4⟩ + revealSecretsOffsetWord ee) + ⟨31⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨1⟩)
    (hsecretsLen :
      uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ + revealSecretsOffsetWord ee).toNat 32)
        = ⟨0⟩)
    (hsecretsEnd :
      UInt256.gt (((⟨4⟩ + revealSecretsOffsetWord ee) + ⟨0⟩) + ⟨32⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨0⟩) :
    ∃ k' C', RD blindAuctionBytecode ee g s0 ⟨887⟩
      [⟨0⟩, (⟨4⟩ + revealSecretsOffsetWord ee) + ⟨32⟩,
        ⟨0⟩, (⟨4⟩ + revealFakesOffsetWord ee) + ⟨32⟩,
        ⟨0⟩, (⟨4⟩ + revealValuesOffsetWord ee) + ⟨32⟩, ⟨276⟩, sel]
      mem aw rdata acc k' C' := by
  obtain ⟨_, _, rd413⟩ :=
    blindAuctionRevealDecodeEmptyArrays1806_to_413 rd hvaluesGt hvaluesStart hvaluesLen
      hvaluesEnd hfakesGt hfakesStart hfakesLen hfakesEnd hsecretsGt hsecretsStart
      hsecretsLen hsecretsEnd
  have rd887 := evm_run rd413 with [jumpdest, push2 ⟨887⟩, jump (by jump_dest)]
  exact ⟨_, _, rd887⟩

theorem blindAuctionRevealParamNames :
    revealTransition.params.map Param.name = ["values", "fakes", "secrets"] := rfl

theorem blindAuctionRevealParamTypes :
    (transitionSignature revealTransition).paramTypes =
      [.dynamicArray uint256, .dynamicArray boolTy, .dynamicArray bytes32] := rfl

theorem blindAuctionDecode_reveal_none_short {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    decodeCalldata (revealTransition.params.map Param.name)
      (transitionSignature revealTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["values", "fakes", "secrets"]
    [.dynamicArray uint256, .dynamicArray boolTy, .dynamicArray bytes32] I.calldata = none
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  simp only [List.isEmpty_cons]
  rw [if_neg]
  · rw [if_neg]
    · simp only [decodeCalldata.decodeArgs]
      have hargsShort : (List.drop 4 I.calldata.toList).length < 96 := by
        rw [List.length_drop, htlen]
        omega
      simp only [abiTupleHeadSize?, isDynamicABIType, reduceIte, Option.bind, bind]
      rw [if_pos hargsShort]
    · rintro ⟨_, hhuge⟩
      rw [List.length_drop, htlen] at hhuge
      omega
  · rintro ⟨_, hhuge⟩
    rw [htlen] at hhuge
    omega

theorem blindAuctionDecode_reveal_none_huge_dynamic {I : ExecutionEnv}
    (hhuge : 2 ^ 255 ≤ I.calldata.size) :
    decodeCalldata (revealTransition.params.map Param.name)
      (transitionSignature revealTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["values", "fakes", "secrets"]
    [.dynamicArray uint256, .dynamicArray boolTy, .dynamicArray bytes32] I.calldata = none
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_pos (show
    [.dynamicArray uint256, .dynamicArray boolTy, .dynamicArray bytes32].any
        isDynamicABIType = true ∧ 2 ^ 255 ≤ I.calldata.toList.length from by
      constructor
      · decide
      · rw [htlen]; exact hhuge)]

theorem blindAuctionDecode_reveal_none_huge {I : ExecutionEnv}
    (hhuge : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (revealTransition.params.map Param.name)
      (transitionSignature revealTransition).paramTypes I.calldata = none := by
  exact blindAuctionDecode_reveal_none_huge_dynamic (I := I) (by omega)

theorem decodeABIValue_dynamicArray_is_array {elemTy : ABIType} {bytes : List UInt8}
    {start : Nat} {v : Value} {endOffset : Nat}
    (h : decodeABIValue? (.dynamicArray elemTy) bytes start = some (v, endOffset)) :
    ∃ xs, v = .array xs := by
  unfold decodeABIValue? at h
  cases hsize : readNat? bytes start with
  | none => simp [hsize] at h
  | some size =>
      by_cases hmax : solcMaxU64 < size
      · simp [hsize, hmax] at h
      · by_cases hbool : elemTy = .elem .bool
        · subst elemTy
          simp [hsize, hmax] at h
          cases helems : decodeABIRawBoolArrayElems? size bytes (start + 32) with
          | none => simp [helems] at h
          | some p =>
              rcases p with ⟨xs, _⟩
              simp [helems] at h
              exact ⟨xs, h.1.symm⟩
        · by_cases hdyn : isDynamicABIType elemTy
          · simp [hsize, hmax, hdyn] at h
            cases helems : decodeABIArrayDynamicElems? elemTy size bytes (start + 32) with
            | none => simp [helems] at h
            | some p =>
                rcases p with ⟨xs, _⟩
                simp [helems] at h
                exact ⟨xs, h.1.symm⟩
          · simp [hsize, hmax, hdyn] at h
            cases hstatic : staticABIEncodedSize? elemTy with
            | none => simp [hstatic] at h
            | some elemSize =>
                simp [hstatic] at h
                cases helems : decodeABIArrayStaticElems? elemTy size elemSize bytes (start + 32) with
                | none => simp [helems] at h
                | some p =>
                    rcases p with ⟨xs, _⟩
                    simp [helems] at h
                    exact ⟨xs, h.1.symm⟩

theorem readBytes32_some_length {bytes : List UInt8} {off : Nat} {out : List UInt8}
    (h : readBytes? bytes off 32 = some out) : off + 32 ≤ bytes.length := by
  unfold readBytes? at h
  by_cases hle : 32 ≤ bytes.length - off
  · omega
  · simp [hle] at h

theorem readWord?_some_length {bytes : List UInt8} {off : Nat} {word : EVM.Word}
    (h : readWord? bytes off = some word) : off + 32 ≤ bytes.length := by
  unfold readWord? at h
  cases hbytes : readBytes? bytes off 32 with
  | none => simp [hbytes] at h
  | some _ => exact readBytes32_some_length hbytes

theorem readNat?_some_length {bytes : List UInt8} {off n : Nat}
    (h : readNat? bytes off = some n) : off + 32 ≤ bytes.length := by
  unfold readNat? readWord? at h
  cases hbytes : readBytes? bytes off 32 with
  | none => simp [hbytes] at h
  | some _ => exact readBytes32_some_length hbytes

theorem readNat?_exists_of_length {bytes : List UInt8} {off : Nat}
    (h : off + 32 ≤ bytes.length) : ∃ n, readNat? bytes off = some n := by
  unfold readNat? readWord? readBytes?
  have hlen : ((bytes.drop off).take 32).length = 32 := by
    rw [List.length_take, List.length_drop]
    omega
  simp [hlen]

theorem readNat?_some_bytesToWord {bytes : List UInt8} {off n : Nat}
    (h : readNat? bytes off = some n) :
    ABI.bytesToWord ((bytes.drop off).take 32) = UInt256.ofNat n := by
  unfold readNat? readWord? readBytes? at h
  by_cases hle : 32 ≤ bytes.length - off
  · simp [hle] at h
    cases h
    exact (u256_ofNat_toNat _).symm
  · simp [hle] at h

theorem decodeABIValue_uint256_exists {bytes : List UInt8} {start : Nat}
    (h : start + 32 ≤ bytes.length) :
    ∃ v, decodeABIValue? uint256 bytes start = some (v, start + 32) := by
  have hlen : ((bytes.drop start).take 32).length = 32 := by
    rw [List.length_take, List.length_drop]
    omega
  refine ⟨.int (Int.ofNat (ABI.bytesToWord ((bytes.drop start).take 32)).toNat), ?_⟩
  simpa [uint256, uint256Int, abiUInt256] using
    decodeABIValue_uint256_ok (bytes := bytes) (start := start) hlen

theorem decodeABIValue_bytes32_exists {bytes : List UInt8} {start : Nat}
    (h : start + 32 ≤ bytes.length) :
    ∃ v, decodeABIValue? bytes32 bytes start = some (v, start + 32) := by
  unfold decodeABIValue? bytes32
  unfold readBytes?
  have hlen : ((bytes.drop start).take 32).length = 32 := by
    rw [List.length_take, List.length_drop]
    omega
  refine ⟨.fixedBytes ⟨31, by decide⟩ ((bytes.drop start).take 32), ?_⟩
  simp [hlen, zeroPadding?, readBytes?]

theorem decode_word_at_eq_any (cd : ByteArray) (off : ℕ) (hsz : off + 32 ≤ cd.size) :
    ABI.bytesToWord ((cd.toList.drop off).take 32) =
      uInt256OfByteArray (cd.readBytes off 32) := by
  by_cases hoff : off < 2 ^ 64
  · exact decode_word_at_eq cd off hsz hoff
  · rw [uInt256OfByteArray_eq]
    unfold ABI.bytesToWord fromByteArrayBigEndian
    congr 2
    rw [byteArray_toList_eq (cd.readBytes off 32)]
    unfold ByteArray.readBytes
    rw [if_neg]
    · simp only [ByteArray.toList_data_append, byteArray_zeroes_toList]
      have hreadSize : (ByteArray.mk (((cd.toList.drop off).take 32).toArray)).size = 32 := by
        show (((cd.toList.drop off).take 32).toArray).size = 32
        have hlen : ((cd.toList.drop off).take 32).length = 32 := by
          rw [List.length_take, List.length_drop]
          rw [byteArray_toList_eq, Array.length_toList]
          have hds : cd.data.size = cd.size := rfl
          rw [hds]
          omega
        simp [hlen]
      rw [hreadSize]
      simp [byteArray_toList_eq]
    · simp
      exact Nat.le_of_not_gt hoff

theorem readNat?_calldataWord_eq {I : ExecutionEnv} {headOff off : Nat}
    (hread : readNat? (List.drop 4 I.calldata.toList) headOff = some off) :
    calldataWord I.calldata (4 + headOff) = UInt256.ofNat off := by
  have hreadLen := readNat?_some_length hread
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hsz : 4 + headOff + 32 ≤ I.calldata.size := by
    rw [List.length_drop, htlen] at hreadLen
    omega
  rw [calldataWord]
  rw [← decode_word_at_eq_any I.calldata (4 + headOff) hsz]
  have hword := readNat?_some_bytesToWord hread
  simpa [List.drop_drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hword

theorem decodeABIValue_elem_end_le {elem : ElemType} {bytes : List UInt8}
    {start : Nat} {v : Value} {endOffset : Nat}
    (h : decodeABIValue? (.elem elem) bytes start = some (v, endOffset)) :
    endOffset = start + 32 ∧ start + 32 ≤ bytes.length := by
  cases elem <;> unfold decodeABIValue? at h
  case bool =>
    cases hread : readWord? bytes start with
    | none => simp [hread] at h
    | some word =>
        cases hdec : decodeABIWord? (.elem .bool) word with
        | none => simp [hread, hdec] at h
        | some value =>
            simp [hread, hdec] at h
            exact ⟨h.2.symm, readWord?_some_length hread⟩
  case address =>
    cases hread : readWord? bytes start with
    | none => simp [hread] at h
    | some word =>
        cases hdec : decodeABIWord? (.elem .address) word with
        | none => simp [hread, hdec] at h
        | some value =>
            simp [hread, hdec] at h
            exact ⟨h.2.symm, readWord?_some_length hread⟩
  case int it =>
    cases hread : readWord? bytes start with
    | none => simp [hread] at h
    | some word =>
        cases hdec : decodeABIWord? (.elem (.int it)) word with
        | none => simp [hread, hdec] at h
        | some value =>
            simp [hread, hdec] at h
            exact ⟨h.2.symm, readWord?_some_length hread⟩
  case fixed ft =>
    cases hread : readWord? bytes start with
    | none => simp [hread] at h
    | some word => simp [decodeABIWord?] at h
  case bytes n =>
    cases hread : readBytes? bytes start 32 with
    | none => simp [hread] at h
    | some wordBytes =>
        simp [hread] at h
        cases hzero : zeroPadding? wordBytes (n.val + 1) (31 - n.val) with
        | none => simp [hzero] at h
        | some u =>
            simp [hzero] at h
            exact ⟨h.2.symm, readBytes32_some_length hread⟩
  case function =>
    cases hread : readBytes? bytes start 32 with
    | none => simp [hread] at h
    | some wordBytes =>
        cases hzero : zeroPadding? wordBytes 24 8 with
        | none => simp [hread, hzero] at h
        | some u =>
            simp [hread, hzero] at h
            exact ⟨h.2.symm, readBytes32_some_length hread⟩

theorem decodeABIArrayStaticElems_elem32_facts {elem : ElemType} {n : Nat}
    {bytes : List UInt8} {start : Nat} {values : List Value} {endOffset : Nat}
    (hstart : start ≤ bytes.length)
    (h : decodeABIArrayStaticElems? (.elem elem) n 32 bytes start = some (values, endOffset)) :
    endOffset = start + 32 * n ∧ endOffset ≤ bytes.length ∧ values.length = n := by
  induction n generalizing start values endOffset with
  | zero =>
      simp [decodeABIArrayStaticElems?] at h
      rcases h with ⟨hvalues, hend⟩
      cases hvalues
      cases hend
      exact ⟨by omega, hstart, rfl⟩
  | succ n ih =>
      rw [decodeABIArrayStaticElems?] at h
      cases hval : decodeABIValue? (.elem elem) bytes start with
      | none => simp [hval] at h
      | some p =>
          rcases p with ⟨value, end0⟩
          obtain ⟨hend0, hend0le⟩ := decodeABIValue_elem_end_le hval
          simp [hval] at h
          cases hrest : decodeABIArrayStaticElems? (.elem elem) n 32 bytes end0 with
          | none => simp [hrest] at h
          | some q =>
              rcases q with ⟨valuesRest, restEnd⟩
              simp [hrest] at h
              rcases h with ⟨hend0', htail⟩
              rcases htail with ⟨hvalues, hend⟩
              cases hvalues
              cases hend
              obtain ⟨ihEq, ihLe, ihLen⟩ := ih (by omega) hrest
              exact ⟨by omega, ihLe, by simp [ihLen]⟩

theorem decodeABIArrayStaticElems_uint256_exists_of_length {n : Nat}
    {bytes : List UInt8} {start : Nat} (h : start + 32 * n ≤ bytes.length) :
    ∃ values, decodeABIArrayStaticElems? uint256 n 32 bytes start =
        some (values, start + 32 * n) ∧ values.length = n := by
  induction n generalizing start with
  | zero =>
      refine ⟨[], ?_, rfl⟩
      simp [decodeABIArrayStaticElems?]
  | succ n ih =>
      obtain ⟨v, hv⟩ := decodeABIValue_uint256_exists (bytes := bytes) (start := start) (by omega)
      obtain ⟨values, hvalues, hlen⟩ := ih (start := start + 32) (by omega)
      refine ⟨v :: values, ?_, by simp [hlen]⟩
      rw [decodeABIArrayStaticElems?, hv]
      have hmul : 32 + 32 * n = 32 * (n + 1) := by omega
      simpa [hvalues, hmul, Nat.add_assoc]

theorem decodeABIArrayStaticElems_bytes32_exists_of_length {n : Nat}
    {bytes : List UInt8} {start : Nat} (h : start + 32 * n ≤ bytes.length) :
    ∃ values, decodeABIArrayStaticElems? bytes32 n 32 bytes start =
        some (values, start + 32 * n) ∧ values.length = n := by
  induction n generalizing start with
  | zero =>
      refine ⟨[], ?_, rfl⟩
      simp [decodeABIArrayStaticElems?]
  | succ n ih =>
      obtain ⟨v, hv⟩ := decodeABIValue_bytes32_exists (bytes := bytes) (start := start) (by omega)
      obtain ⟨values, hvalues, hlen⟩ := ih (start := start + 32) (by omega)
      refine ⟨v :: values, ?_, by simp [hlen]⟩
      rw [decodeABIArrayStaticElems?, hv]
      have hmul : 32 + 32 * n = 32 * (n + 1) := by omega
      simpa [hvalues, hmul, Nat.add_assoc]

theorem decodeABIRawBoolArrayElems_facts {n : Nat} {bytes : List UInt8}
    {start : Nat} {values : List Value} {endOffset : Nat}
    (hstart : start ≤ bytes.length)
    (h : decodeABIRawBoolArrayElems? n bytes start = some (values, endOffset)) :
    endOffset = start + 32 * n ∧ endOffset ≤ bytes.length ∧ values.length = n := by
  induction n generalizing start values endOffset with
  | zero =>
      simp [decodeABIRawBoolArrayElems?] at h
      rcases h with ⟨hvalues, hend⟩
      cases hvalues
      cases hend
      exact ⟨by omega, hstart, rfl⟩
  | succ n ih =>
      rw [decodeABIRawBoolArrayElems?] at h
      cases hread : readNat? bytes start with
      | none => simp [hread] at h
      | some word =>
          simp [hread] at h
          cases hrest : decodeABIRawBoolArrayElems? n bytes (start + 32) with
          | none => simp [hrest] at h
          | some p =>
              rcases p with ⟨valuesRest, restEnd⟩
              simp [hrest] at h
              rcases h with ⟨hvalues, hend⟩
              cases hvalues
              cases hend
              obtain ⟨ihEq, ihLe, ihLen⟩ :=
                ih (readNat?_some_length hread) hrest
              exact ⟨by omega, ihLe, by simp [ihLen]⟩

theorem decodeABIRawBoolArrayElems_exists_of_length {n : Nat} {bytes : List UInt8}
    {start : Nat} (h : start + 32 * n ≤ bytes.length) :
    ∃ values, decodeABIRawBoolArrayElems? n bytes start =
        some (values, start + 32 * n) ∧ values.length = n := by
  induction n generalizing start with
  | zero =>
      refine ⟨[], ?_, rfl⟩
      simp [decodeABIRawBoolArrayElems?]
  | succ n ih =>
      have hreadLen : start + 32 ≤ bytes.length := by omega
      obtain ⟨word, hread⟩ := readNat?_exists_of_length hreadLen
      have htail : start + 32 + 32 * n ≤ bytes.length := by omega
      obtain ⟨values, hvalues, hlen⟩ := ih htail
      refine ⟨rawBoolWordValue word :: values, ?_, by simp [hlen]⟩
      rw [decodeABIRawBoolArrayElems?, hread, hvalues]
      have hmul : 32 + 32 * n = 32 * (n + 1) := by omega
      simpa [hmul, Nat.add_assoc]

theorem decodeABIValue_dynamicArray_uint256_exists {bytes : List UInt8}
    {start len : Nat}
    (hread : readNat? bytes start = some len)
    (hmax : ¬ solcMaxU64 < len)
    (hend : start + 32 + 32 * len ≤ bytes.length) :
    ∃ values, decodeABIValue? (.dynamicArray uint256) bytes start =
        some (.array values, start + 32 + 32 * len) ∧ values.length = len := by
  obtain ⟨values, hvalues, hlen⟩ :=
    decodeABIArrayStaticElems_uint256_exists_of_length (bytes := bytes) (start := start + 32)
      (n := len) (by omega)
  refine ⟨values, ?_, hlen⟩
  have hvalues' :
      decodeABIArrayStaticElems? (.elem (.int uint256Int)) len 32 bytes (start + 32) =
        some (values, start + 32 + 32 * len) := by
    simpa [uint256] using hvalues
  unfold decodeABIValue? uint256
  simp [hread, hmax, isDynamicABIType, staticABIEncodedSize?, hvalues', Nat.add_assoc]

theorem decodeABIValue_dynamicArray_bool_exists {bytes : List UInt8}
    {start len : Nat}
    (hread : readNat? bytes start = some len)
    (hmax : ¬ solcMaxU64 < len)
    (hend : start + 32 + 32 * len ≤ bytes.length) :
    ∃ values, decodeABIValue? (.dynamicArray boolTy) bytes start =
        some (.array values, start + 32 + 32 * len) ∧ values.length = len := by
  obtain ⟨values, hvalues, hlen⟩ :=
    decodeABIRawBoolArrayElems_exists_of_length (bytes := bytes) (start := start + 32)
      (n := len) (by omega)
  refine ⟨values, ?_, hlen⟩
  unfold decodeABIValue? boolTy
  simp [hread, hmax, hvalues, Nat.add_assoc]

theorem decodeABIValue_dynamicArray_bytes32_exists {bytes : List UInt8}
    {start len : Nat}
    (hread : readNat? bytes start = some len)
    (hmax : ¬ solcMaxU64 < len)
    (hend : start + 32 + 32 * len ≤ bytes.length) :
    ∃ values, decodeABIValue? (.dynamicArray bytes32) bytes start =
        some (.array values, start + 32 + 32 * len) ∧ values.length = len := by
  obtain ⟨values, hvalues, hlen⟩ :=
    decodeABIArrayStaticElems_bytes32_exists_of_length (bytes := bytes) (start := start + 32)
      (n := len) (by omega)
  refine ⟨values, ?_, hlen⟩
  unfold bytes32 at hvalues
  unfold decodeABIValue? bytes32
  simp [hread, hmax, isDynamicABIType, staticABIEncodedSize?]
  rw [show (ABIType.elem (ElemType.bytes 31)) =
      (ABIType.elem (ElemType.bytes ⟨31, bytes32._proof_1⟩)) by
    congr]
  rw [hvalues]
  simp [Nat.add_assoc]

theorem decodeABIValue_dynamicArray_elem32_facts {elem : ElemType}
    {bytes : List UInt8} {start : Nat} {values : List Value} {endOffset : Nat}
    (h : decodeABIValue? (.dynamicArray (.elem elem)) bytes start =
      some (.array values, endOffset)) :
    ∃ len, readNat? bytes start = some len ∧ ¬ solcMaxU64 < len ∧
      endOffset = start + 32 + 32 * len ∧ endOffset ≤ bytes.length ∧ values.length = len := by
  unfold decodeABIValue? at h
  cases hread : readNat? bytes start with
  | none => simp [hread] at h
  | some len =>
      by_cases hmax : solcMaxU64 < len
      · simp [hread, hmax] at h
      · by_cases hbool : elem = .bool
        · subst elem
          simp [hread, hmax] at h
          cases hraw : decodeABIRawBoolArrayElems? len bytes (start + 32) with
          | none => simp [hraw] at h
          | some p =>
              rcases p with ⟨values', end'⟩
              simp [hraw] at h
              rcases h with ⟨hvalues, hendOffset⟩
              obtain ⟨hend, hle, hlen⟩ :=
                decodeABIRawBoolArrayElems_facts (readNat?_some_length hread) hraw
              refine ⟨len, rfl, hmax, ?_, ?_, ?_⟩
              · rw [← hendOffset]
                exact hend
              · rwa [hendOffset] at hle
              · rwa [hvalues] at hlen
        · simp [hread, hmax, hbool, staticABIEncodedSize?, isDynamicABIType] at h
          cases hstatic : decodeABIArrayStaticElems? (.elem elem) len 32 bytes (start + 32) with
          | none => simp [hstatic] at h
          | some p =>
              rcases p with ⟨values', end'⟩
              simp [hstatic] at h
              rcases h with ⟨hvalues, hendOffset⟩
              obtain ⟨hend, hle, hlen⟩ :=
                decodeABIArrayStaticElems_elem32_facts (readNat?_some_length hread) hstatic
              refine ⟨len, rfl, hmax, ?_, ?_, ?_⟩
              · rw [← hendOffset]
                exact hend
              · rwa [hendOffset] at hle
              · rwa [hvalues] at hlen

theorem uadd3_ofNat_toNat {a b c : Nat}
    (ha : a < UInt256.size) (hb : b < UInt256.size) (hc : c < UInt256.size)
    (hab : a + b < UInt256.size) (habc : a + b + c < UInt256.size) :
    ((UInt256.ofNat a + UInt256.ofNat b) + UInt256.ofNat c).toNat = a + b + c := by
  rw [uadd_toNat]
  have habWord : (UInt256.ofNat a + UInt256.ofNat b).toNat = a + b :=
    uadd_ofNat_toNat ha hb hab
  rw [habWord, ulit_toNat' c hc]
  exact Nat.mod_eq_of_lt habc

theorem shiftLeft5_ofNat_eq {n : Nat} (h : 32 * n < UInt256.size) :
    UInt256.shiftLeft (UInt256.ofNat n) ⟨5⟩ = UInt256.ofNat (32 * n) := by
  apply u256_inj
  unfold UInt256.shiftLeft
  rw [if_neg (by decide : ¬ ((⟨5⟩ : UInt256).val ≥ 256))]
  change (((UInt256.ofNat n).val.val <<< (⟨5⟩ : UInt256).val.val) % UInt256.size) =
    (UInt256.ofNat (32 * n)).val.val
  rw [show (⟨5⟩ : UInt256).val.val = 5 by decide]
  rw [show (UInt256.ofNat n).val.val = n by
    exact ulit_toNat' n (by
      have : n ≤ 32 * n := by omega
      exact lt_of_le_of_lt this h)]
  rw [show (UInt256.ofNat (32 * n)).val.val = 32 * n by exact ulit_toNat' (32 * n) h]
  rw [Nat.shiftLeft_eq, Nat.mul_comm]
  exact Nat.mod_eq_of_lt h

theorem revealArrayGuards_of_decode_elem32 {I : ExecutionEnv} {headOff off : Nat}
    {elem : ElemType} {values : List Value} {endOffset : Nat}
    (hcalldataSign : I.calldata.size < 2 ^ 255)
    (hreadHead : readNat? (List.drop 4 I.calldata.toList) headOff = some off)
    (hoffMax : ¬ solcMaxU64 < off)
    (hdecode : decodeABIValue? (.dynamicArray (.elem elem)) (List.drop 4 I.calldata.toList)
      off = some (.array values, endOffset)) :
    ∃ lenWord : UInt256,
      values.length = lenWord.toNat ∧
      UInt256.gt (calldataWord I.calldata (4 + headOff)) revealMaxU64 = ⟨0⟩ ∧
      UInt256.slt (((⟨4⟩ : UInt256) + calldataWord I.calldata (4 + headOff)) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩ ∧
      uInt256OfByteArray
          (I.calldata.readBytes
            (((⟨4⟩ : UInt256) + calldataWord I.calldata (4 + headOff)).toNat) 32) =
        lenWord ∧
      UInt256.gt lenWord revealMaxU64 = ⟨0⟩ ∧
      UInt256.gt ((((⟨4⟩ : UInt256) + calldataWord I.calldata (4 + headOff)) +
            UInt256.shiftLeft lenWord ⟨5⟩) + ⟨32⟩)
          (UInt256.ofNat I.calldata.size) = ⟨0⟩ := by
  obtain ⟨len, hreadLen, hlenMax, hendEq, hendLe, hvaluesLen⟩ :=
    decodeABIValue_dynamicArray_elem32_facts hdecode
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hargsLen : (List.drop 4 I.calldata.toList).length = I.calldata.size - 4 := by
    rw [List.length_drop, htlen]
  have hoffEnd : 4 + off + 32 + 32 * len ≤ I.calldata.size := by
    rw [hargsLen] at hendLe
    omega
  have hoffSmall : off < 2 ^ 64 := by
    unfold solcMaxU64 at hoffMax
    omega
  have hlenSmall : len < 2 ^ 64 := by
    unfold solcMaxU64 at hlenMax
    omega
  have h32lenSmall : 32 * len < UInt256.size := by
    have : 32 * len < 2 ^ 69 := by omega
    norm_num [UInt256.size]
    omega
  have hword : calldataWord I.calldata (4 + headOff) = UInt256.ofNat off :=
    readNat?_calldataWord_eq hreadHead
  have hstartToNat :
      (((⟨4⟩ : UInt256) + calldataWord I.calldata (4 + headOff)).toNat) = 4 + off := by
    rw [hword]
    simpa using (uadd_ofNat_toNat (a := 4) (b := off) (by norm_num [UInt256.size])
      (lt_size_of_lt_sign (by omega : off < 2 ^ 255))
      (lt_size_of_lt_sign (by omega : 4 + off < 2 ^ 255)))
  have hlenWordEq :
      uInt256OfByteArray
          (I.calldata.readBytes
            (((⟨4⟩ : UInt256) + calldataWord I.calldata (4 + headOff)).toNat) 32) =
        UInt256.ofNat len := by
    have hlenWord := readNat?_calldataWord_eq (I := I) (headOff := off) hreadLen
    rw [hstartToNat]
    simpa [calldataWord] using hlenWord
  refine ⟨UInt256.ofNat len, ?_, ?_, ?_, hlenWordEq, ?_, ?_⟩
  · rw [hvaluesLen]
    exact (ulit_toNat' len (lt_size_of_lt_sign (by omega : len < 2 ^ 255))).symm
  · rw [hword]
    apply ugt_zero
    rw [ulit_toNat' off (lt_size_of_lt_sign (by omega : off < 2 ^ 255))]
    rw [show revealMaxU64.toNat = solcMaxU64 by native_decide]
    unfold solcMaxU64 at hoffMax ⊢
    omega
  · have hstart31ToNat :
        ((((⟨4⟩ : UInt256) + calldataWord I.calldata (4 + headOff)) + ⟨31⟩).toNat) =
          4 + off + 31 := by
      rw [hword]
      simpa using (uadd3_ofNat_toNat (a := 4) (b := off) (c := 31)
        (by norm_num [UInt256.size])
        (lt_size_of_lt_sign (by omega : off < 2 ^ 255))
        (by norm_num [UInt256.size])
        (lt_size_of_lt_sign (by omega : 4 + off < 2 ^ 255))
        (lt_size_of_lt_sign (by omega : 4 + off + 31 < 2 ^ 255)))
    apply slt_lit_one_low (m := I.calldata.size)
    · exact hcalldataSign
    · rw [hstart31ToNat]
      omega
  · apply ugt_zero
    rw [ulit_toNat' len (lt_size_of_lt_sign (by omega : len < 2 ^ 255))]
    rw [show revealMaxU64.toNat = solcMaxU64 by native_decide]
    unfold solcMaxU64 at hlenMax ⊢
    omega
  · have hendToNat :
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata (4 + headOff)) +
              UInt256.shiftLeft (UInt256.ofNat len) ⟨5⟩) + ⟨32⟩).toNat) =
          4 + off + 32 * len + 32 := by
      rw [hword, shiftLeft5_ofNat_eq h32lenSmall]
      have h4off :
          ((UInt256.ofNat 4 + UInt256.ofNat off) + UInt256.ofNat (32 * len) +
              UInt256.ofNat 32).toNat = 4 + off + 32 * len + 32 := by
        rw [uadd_toNat]
        have hleft :
            ((UInt256.ofNat 4 + UInt256.ofNat off) + UInt256.ofNat (32 * len)).toNat =
              4 + off + 32 * len := by
          exact uadd3_ofNat_toNat
            (by norm_num [UInt256.size])
            (lt_size_of_lt_sign (by omega : off < 2 ^ 255))
            h32lenSmall
            (lt_size_of_lt_sign (by omega : 4 + off < 2 ^ 255))
            (lt_size_of_lt_sign (by omega : 4 + off + 32 * len < 2 ^ 255))
        rw [hleft, ulit_toNat' 32 (by norm_num [UInt256.size])]
        exact Nat.mod_eq_of_lt
          (lt_size_of_lt_sign (by omega : 4 + off + 32 * len + 32 < 2 ^ 255))
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h4off
    apply ugt_zero
    rw [hendToNat]
    rw [ulit_toNat' I.calldata.size (lt_size_of_lt_sign hcalldataSign)]
    omega

theorem blindAuctionDecode_reveal_callargs_shape {I : ExecutionEnv} {callargs : Store}
    (hdec : decodeCalldata (revealTransition.params.map Param.name)
      (transitionSignature revealTransition).paramTypes I.calldata = some callargs) :
    ∃ values fakes secrets : List Value,
      callargs.get? "values" = some (.array values) ∧
      callargs.get? "fakes" = some (.array fakes) ∧
      callargs.get? "secrets" = some (.array secrets) := by
  change decodeCalldata ["values", "fakes", "secrets"]
    [.dynamicArray uint256, .dynamicArray boolTy, .dynamicArray bytes32] I.calldata =
      some callargs at hdec
  unfold decodeCalldata at hdec
  simp only [List.isEmpty_cons] at hdec
  split at hdec
  · contradiction
  next _ =>
    split at hdec
    · contradiction
    next _ =>
      simp [decodeCalldata.decodeArgs, decodeABIValues?, abiTupleHeadSize?, isDynamicABIType,
        Option.bind, bind] at hdec
      cases h0 : readNat? (List.drop 4 I.calldata.toList) 0 with
      | none => simp [h0] at hdec
      | some off0 =>
          by_cases hmax0 : solcMaxU64 < off0
          · simp [h0, hmax0] at hdec
          ·
              simp [h0, hmax0] at hdec
              cases hval0 : decodeABIValue? (.dynamicArray uint256)
                  (List.drop 4 I.calldata.toList) off0 with
              | none => simp [hval0] at hdec
              | some p0 =>
                  rcases p0 with ⟨v0, _⟩
                  rcases decodeABIValue_dynamicArray_is_array hval0 with ⟨values, rfl⟩
                  simp [hval0] at hdec
                  cases h1 : readNat? (List.drop 4 I.calldata.toList) 32 with
                  | none => simp [h1] at hdec
                  | some off1 =>
                      by_cases hmax1 : solcMaxU64 < off1
                      · simp [h1, hmax1] at hdec
                      ·
                          simp [h1, hmax1] at hdec
                          cases hval1 : decodeABIValue? (.dynamicArray boolTy)
                              (List.drop 4 I.calldata.toList) off1 with
                          | none => simp [hval1] at hdec
                          | some p1 =>
                              rcases p1 with ⟨v1, _⟩
                              rcases decodeABIValue_dynamicArray_is_array hval1 with ⟨fakes, rfl⟩
                              simp [hval1] at hdec
                              cases h2 : readNat? (List.drop 4 I.calldata.toList) 64 with
                              | none => simp [h2] at hdec
                              | some off2 =>
                                  by_cases hmax2 : solcMaxU64 < off2
                                  · simp [h2, hmax2] at hdec
                                  ·
                                      simp [h2, hmax2] at hdec
                                      cases hval2 : decodeABIValue? (.dynamicArray bytes32)
                                          (List.drop 4 I.calldata.toList) off2 with
                                      | none => simp [hval2] at hdec
                                      | some p2 =>
                                          rcases p2 with ⟨v2, _⟩
                                          rcases decodeABIValue_dynamicArray_is_array hval2 with
                                            ⟨secrets, rfl⟩
                                          simp [hval2] at hdec
                                          simp [decodeCalldata.insertValues] at hdec
                                          by_cases hargsShort : I.calldata.toList.length - 4 < 96
                                          · simp [hargsShort] at hdec
                                          · simp [hargsShort] at hdec
                                            rcases hdec with ⟨_, hstore⟩
                                            cases hstore.symm
                                            refine ⟨values, fakes, secrets, ?_, ?_, ?_⟩
                                            · rw [store_get_ne, store_get_ne, store_get_self]
                                              · decide
                                              · decide
                                            · rw [store_get_ne, store_get_self]
                                              decide
                                            · rw [store_get_self]

theorem blindAuctionDecode_reveal_callargs_store_shape {I : ExecutionEnv} {callargs : Store}
    (hdec : decodeCalldata (revealTransition.params.map Param.name)
      (transitionSignature revealTransition).paramTypes I.calldata = some callargs) :
    ∃ values fakes secrets : List Value,
      callargs =
        (((∅ : Store).insert "values" (.array values)).insert "fakes" (.array fakes)).insert
          "secrets" (.array secrets) := by
  change decodeCalldata ["values", "fakes", "secrets"]
    [.dynamicArray uint256, .dynamicArray boolTy, .dynamicArray bytes32] I.calldata =
      some callargs at hdec
  unfold decodeCalldata at hdec
  simp only [List.isEmpty_cons] at hdec
  split at hdec
  · contradiction
  next _ =>
    split at hdec
    · contradiction
    next _ =>
      simp [decodeCalldata.decodeArgs, decodeABIValues?, abiTupleHeadSize?, isDynamicABIType,
        Option.bind, bind] at hdec
      cases h0 : readNat? (List.drop 4 I.calldata.toList) 0 with
      | none => simp [h0] at hdec
      | some off0 =>
          by_cases hmax0 : solcMaxU64 < off0
          · simp [h0, hmax0] at hdec
          · simp [h0, hmax0] at hdec
            cases hval0 : decodeABIValue? (.dynamicArray uint256)
                  (List.drop 4 I.calldata.toList) off0 with
              | none => simp [hval0] at hdec
              | some p0 =>
                  rcases p0 with ⟨v0, _⟩
                  rcases decodeABIValue_dynamicArray_is_array hval0 with ⟨values, rfl⟩
                  simp [hval0] at hdec
                  cases h1 : readNat? (List.drop 4 I.calldata.toList) 32 with
                  | none => simp [h1] at hdec
                  | some off1 =>
                      by_cases hmax1 : solcMaxU64 < off1
                      · simp [h1, hmax1] at hdec
                      · simp [h1, hmax1] at hdec
                        cases hval1 : decodeABIValue? (.dynamicArray boolTy)
                              (List.drop 4 I.calldata.toList) off1 with
                          | none => simp [hval1] at hdec
                          | some p1 =>
                              rcases p1 with ⟨v1, _⟩
                              rcases decodeABIValue_dynamicArray_is_array hval1 with ⟨fakes, rfl⟩
                              simp [hval1] at hdec
                              cases h2 : readNat? (List.drop 4 I.calldata.toList) 64 with
                              | none => simp [h2] at hdec
                              | some off2 =>
                                  by_cases hmax2 : solcMaxU64 < off2
                                  · simp [h2, hmax2] at hdec
                                  · simp [h2, hmax2] at hdec
                                    cases hval2 : decodeABIValue? (.dynamicArray bytes32)
                                          (List.drop 4 I.calldata.toList) off2 with
                                      | none => simp [hval2] at hdec
                                      | some p2 =>
                                          rcases p2 with ⟨v2, _⟩
                                          rcases decodeABIValue_dynamicArray_is_array hval2 with
                                            ⟨secrets, rfl⟩
                                          simp [hval2] at hdec
                                          simp [decodeCalldata.insertValues] at hdec
                                          by_cases hargsShort : I.calldata.toList.length - 4 < 96
                                          · simp [hargsShort] at hdec
                                          · simp [hargsShort] at hdec
                                            rcases hdec with ⟨_, hstore⟩
                                            cases hstore.symm
                                            exact ⟨values, fakes, secrets, rfl⟩

def RevealArrayGuardFacts (I : ExecutionEnv) (headOff : Nat) (xs : List Value) : Prop :=
  ∃ lenWord : UInt256,
    xs.length = lenWord.toNat ∧
    UInt256.gt (calldataWord I.calldata (4 + headOff)) revealMaxU64 = ⟨0⟩ ∧
    UInt256.slt (((⟨4⟩ : UInt256) + calldataWord I.calldata (4 + headOff)) + ⟨31⟩)
      (UInt256.ofNat I.calldata.size) = ⟨1⟩ ∧
    uInt256OfByteArray
      (I.calldata.readBytes
        (((⟨4⟩ : UInt256) + calldataWord I.calldata (4 + headOff)).toNat) 32) = lenWord ∧
    UInt256.gt lenWord revealMaxU64 = ⟨0⟩ ∧
    UInt256.gt ((((⟨4⟩ : UInt256) + calldataWord I.calldata (4 + headOff)) +
          UInt256.shiftLeft lenWord ⟨5⟩) + ⟨32⟩)
        (UInt256.ofNat I.calldata.size) = ⟨0⟩

def RevealDecodeGuardFacts (I : ExecutionEnv)
    (values fakes secrets : List Value) : Prop :=
  RevealArrayGuardFacts I 0 values ∧
  RevealArrayGuardFacts I 32 fakes ∧
  RevealArrayGuardFacts I 64 secrets

theorem revealArrayGuardFacts_of_decode_elem32 {I : ExecutionEnv} {headOff off : Nat}
    {elem : ElemType} {xs : List Value} {endOffset : Nat}
    (hcalldataSign : I.calldata.size < 2 ^ 255)
    (hreadHead : readNat? (List.drop 4 I.calldata.toList) headOff = some off)
    (hoffMax : ¬ solcMaxU64 < off)
    (hdecode : decodeABIValue? (.dynamicArray (.elem elem)) (List.drop 4 I.calldata.toList)
      off = some (.array xs, endOffset)) :
    RevealArrayGuardFacts I headOff xs := by
  rcases revealArrayGuards_of_decode_elem32 hcalldataSign hreadHead hoffMax hdecode with
    ⟨lenWord, hlen, hhead, hstart, hload, hmax, hend⟩
  exact ⟨lenWord, hlen, hhead, hstart, hload, hmax, hend⟩

theorem blindAuctionDecode_reveal_guard_facts {I : ExecutionEnv} {callargs : Store}
    (hcalldataSign : I.calldata.size < 2 ^ 255)
    (hdec : decodeCalldata (revealTransition.params.map Param.name)
      (transitionSignature revealTransition).paramTypes I.calldata = some callargs) :
    ∃ values fakes secrets : List Value,
      callargs =
        (((∅ : Store).insert "values" (.array values)).insert "fakes" (.array fakes)).insert
          "secrets" (.array secrets) ∧
      RevealDecodeGuardFacts I values fakes secrets := by
  change decodeCalldata ["values", "fakes", "secrets"]
    [.dynamicArray uint256, .dynamicArray boolTy, .dynamicArray bytes32] I.calldata =
      some callargs at hdec
  unfold decodeCalldata at hdec
  simp only [List.isEmpty_cons] at hdec
  split at hdec
  · contradiction
  next _ =>
    split at hdec
    · contradiction
    next _ =>
      simp [decodeCalldata.decodeArgs, decodeABIValues?, abiTupleHeadSize?, isDynamicABIType,
        Option.bind, bind] at hdec
      cases h0 : readNat? (List.drop 4 I.calldata.toList) 0 with
      | none => simp [h0] at hdec
      | some off0 =>
          by_cases hmax0 : solcMaxU64 < off0
          · simp [h0, hmax0] at hdec
          · simp [h0, hmax0] at hdec
            cases hval0 : decodeABIValue? (.dynamicArray uint256)
                  (List.drop 4 I.calldata.toList) off0 with
              | none => simp [hval0] at hdec
              | some p0 =>
                  rcases p0 with ⟨v0, end0⟩
                  rcases decodeABIValue_dynamicArray_is_array hval0 with ⟨values, rfl⟩
                  simp [hval0] at hdec
                  cases h1 : readNat? (List.drop 4 I.calldata.toList) 32 with
                  | none => simp [h1] at hdec
                  | some off1 =>
                      by_cases hmax1 : solcMaxU64 < off1
                      · simp [h1, hmax1] at hdec
                      · simp [h1, hmax1] at hdec
                        cases hval1 : decodeABIValue? (.dynamicArray boolTy)
                              (List.drop 4 I.calldata.toList) off1 with
                          | none => simp [hval1] at hdec
                          | some p1 =>
                              rcases p1 with ⟨v1, end1⟩
                              rcases decodeABIValue_dynamicArray_is_array hval1 with
                                ⟨fakes, rfl⟩
                              simp [hval1] at hdec
                              cases h2 : readNat? (List.drop 4 I.calldata.toList) 64 with
                              | none => simp [h2] at hdec
                              | some off2 =>
                                  by_cases hmax2 : solcMaxU64 < off2
                                  · simp [h2, hmax2] at hdec
                                  · simp [h2, hmax2] at hdec
                                    cases hval2 : decodeABIValue? (.dynamicArray bytes32)
                                          (List.drop 4 I.calldata.toList) off2 with
                                      | none => simp [hval2] at hdec
                                      | some p2 =>
                                          rcases p2 with ⟨v2, end2⟩
                                          rcases decodeABIValue_dynamicArray_is_array hval2 with
                                            ⟨secrets, rfl⟩
                                          simp [hval2] at hdec
                                          simp [decodeCalldata.insertValues] at hdec
                                          by_cases hargsShort : I.calldata.toList.length - 4 < 96
                                          · simp [hargsShort] at hdec
                                          · simp [hargsShort] at hdec
                                            rcases hdec with ⟨_, hstore⟩
                                            cases hstore.symm
                                            refine ⟨values, fakes, secrets, rfl, ?_⟩
                                            exact
                                              ⟨revealArrayGuardFacts_of_decode_elem32
                                                  hcalldataSign h0 hmax0 hval0,
                                                revealArrayGuardFacts_of_decode_elem32
                                                  hcalldataSign h1 hmax1 hval1,
                                                revealArrayGuardFacts_of_decode_elem32
                                                  hcalldataSign h2 hmax2 hval2⟩

theorem blindAuctionDecode_reveal_callargs_absent {I : ExecutionEnv} {callargs : Store}
    {name : Ident}
    (hdec : decodeCalldata (revealTransition.params.map Param.name)
      (transitionSignature revealTransition).paramTypes I.calldata = some callargs)
    (hvalues : ("values" == name) = false)
    (hfakes : ("fakes" == name) = false)
    (hsecrets : ("secrets" == name) = false) :
    callargs.get? name = none := by
  change decodeCalldata ["values", "fakes", "secrets"]
    [.dynamicArray uint256, .dynamicArray boolTy, .dynamicArray bytes32] I.calldata =
      some callargs at hdec
  unfold decodeCalldata at hdec
  simp only [List.isEmpty_cons] at hdec
  split at hdec
  · contradiction
  next _ =>
    split at hdec
    · contradiction
    next _ =>
      simp [decodeCalldata.decodeArgs, abiTupleHeadSize?, isDynamicABIType, Option.bind, bind]
        at hdec
      cases hvals : decodeABIValues?
          [.dynamicArray uint256, .dynamicArray boolTy, .dynamicArray bytes32]
          (List.drop 4 I.calldata.toList) 0 0 96 96 with
      | none => simp [hvals] at hdec
      | some p =>
          rcases p with ⟨vals, _⟩
          cases vals with
          | nil => simp [hvals, decodeCalldata.insertValues] at hdec
          | cons v0 vals =>
              cases vals with
              | nil => simp [hvals, decodeCalldata.insertValues] at hdec
              | cons v1 vals =>
                  cases vals with
                  | nil => simp [hvals, decodeCalldata.insertValues] at hdec
                  | cons v2 vals =>
                      cases vals with
                      | nil =>
                          simp [hvals, decodeCalldata.insertValues] at hdec
                          by_cases hargsShort : I.calldata.toList.length - 4 < 96
                          · simp [hargsShort] at hdec
                          · simp [hargsShort] at hdec
                            rcases hdec with ⟨_, hstore⟩
                            cases hstore.symm
                            rw [store_get_ne, store_get_ne, store_get_ne]
                            · simp
                            · exact hvalues
                            · exact hfakes
                            · exact hsecrets
                      | cons v3 vals =>
                          simp [hvals, decodeCalldata.insertValues] at hdec


theorem scratch_decodeABIValue_uint256_readNat {bytes : List UInt8} {start endOffset : Nat}
    {value : UInt256}
    (h :
      decodeABIValue? uint256 bytes start =
        some (.int (Int.ofNat value.toNat), endOffset)) :
    readNat? bytes start = some value.toNat ∧ endOffset = start + 32 := by
  obtain ⟨hend, hle⟩ := decodeABIValue_elem_end_le h
  have htake : ((bytes.drop start).take 32).length = 32 := by
    rw [List.length_take, List.length_drop]
    omega
  have hok :
      decodeABIValue? uint256 bytes start =
        some (.int (Int.ofNat (ABI.bytesToWord ((bytes.drop start).take 32)).toNat),
          start + 32) := by
    simpa [uint256, uint256Int, abiUInt256] using
      decodeABIValue_uint256_ok (bytes := bytes) (start := start) htake
  rw [hok] at h
  injection h with hpair
  injection hpair with hval hend'
  injection hval with hint
  have hword :
      (ABI.bytesToWord ((bytes.drop start).take 32)).toNat = value.toNat :=
    Int.ofNat.inj hint
  constructor
  · unfold readNat? readWord? readBytes?
    simp [htake]
    simpa [UInt256.toNat] using hword
  · exact hend'.symm

-- LIBRARY CANDIDATE: dynamic-array decoder nth/read bridge for raw bool ABI arrays.
theorem scratch_decodeABIRawBoolArrayElems_lookup_readNat {n : Nat}
    {bytes : List UInt8} {start endOffset i word : Nat} {values : List Value}
    (hdec : decodeABIRawBoolArrayElems? n bytes start = some (values, endOffset))
    (hlookup : lookupNth? values i = some (rawBoolWordValue word)) :
    readNat? bytes (start + 32 * i) = some word := by
  induction n generalizing start endOffset i values with
  | zero =>
      simp [decodeABIRawBoolArrayElems?] at hdec
      rcases hdec with ⟨hvalues, _hend⟩
      cases hvalues
      cases i <;> simp [lookupNth?] at hlookup
  | succ n ih =>
      rw [decodeABIRawBoolArrayElems?] at hdec
      cases hread : readNat? bytes start with
      | none => simp [hread] at hdec
      | some headWord =>
          simp [hread] at hdec
          cases hrest : decodeABIRawBoolArrayElems? n bytes (start + 32) with
          | none => simp [hrest] at hdec
          | some p =>
              rcases p with ⟨tailValues, restEnd⟩
              simp [hrest] at hdec
              rcases hdec with ⟨hvalues, hend⟩
              cases hvalues
              cases hend
              cases i with
              | zero =>
                  simp [lookupNth?, rawBoolWordValue] at hlookup
                  cases hlookup
                  simpa using hread
              | succ i =>
                  simp [lookupNth?] at hlookup
                  have htail := ih hrest hlookup
                  have hoff : start + 32 * (i + 1) = start + 32 + 32 * i := by omega
                  simpa [hoff, Nat.add_assoc] using htail

-- LIBRARY CANDIDATE: dynamic-array decoder nth/read bridge for uint256 arrays.
theorem scratch_decodeABIArrayStaticElems_uint256_lookup_readNat {n : Nat}
    {bytes : List UInt8} {start endOffset i : Nat} {value : UInt256}
    {values : List Value}
    (hdec : decodeABIArrayStaticElems? uint256 n 32 bytes start = some (values, endOffset))
    (hlookup : lookupNth? values i = some (.int (Int.ofNat value.toNat))) :
    readNat? bytes (start + 32 * i) = some value.toNat := by
  induction n generalizing start endOffset i values with
  | zero =>
      simp [decodeABIArrayStaticElems?] at hdec
      rcases hdec with ⟨hvalues, _hend⟩
      cases hvalues
      cases i <;> simp [lookupNth?] at hlookup
  | succ n ih =>
      rw [decodeABIArrayStaticElems?] at hdec
      cases hval : decodeABIValue? uint256 bytes start with
      | none => simp [hval] at hdec
      | some p =>
          rcases p with ⟨headValue, headEnd⟩
          by_cases hendHead : headEnd = start + 32
          · simp [hval, hendHead] at hdec
            cases hrest : decodeABIArrayStaticElems? uint256 n 32 bytes headEnd with
            | none =>
                have hrest' :
                    decodeABIArrayStaticElems? uint256 n 32 bytes (start + 32) = none := by
                  simpa [hendHead] using hrest
                simp [hrest'] at hdec
            | some q =>
                rcases q with ⟨tailValues, restEnd⟩
                have hrest' :
                    decodeABIArrayStaticElems? uint256 n 32 bytes (start + 32) =
                      some (tailValues, restEnd) := by
                  simpa [hendHead] using hrest
                simp [hrest'] at hdec
                rcases hdec with ⟨hvalues, hend⟩
                cases hvalues
                cases hend
                cases i with
                | zero =>
                    simp [lookupNth?] at hlookup
                    cases hlookup
                    exact (scratch_decodeABIValue_uint256_readNat hval).1
                | succ i =>
                    simp [lookupNth?] at hlookup
                    have htail := ih hrest hlookup
                    have hoff : start + 32 * (i + 1) = headEnd + 32 * i := by omega
                    simpa [hoff] using htail
          · simp [hval, hendHead] at hdec

-- LIBRARY CANDIDATE: fixed bytes32 ABI words round-trip through the EVM word encoding.
theorem scratch_bytesToWord_toBytesBE (w : UInt256) :
    ABI.bytesToWord (EVM.Word.toBytesBE w) = w := by
  unfold ABI.bytesToWord
  rw [← toByteArray_eq_toBytesBE w, fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

theorem scratch_word_toBytesBE_length_32 (w : UInt256) :
    (EVM.Word.toBytesBE w).length = 32 := by
  simpa using word_toBytesBE_toByteArray_size w

-- LIBRARY CANDIDATE: scalar bytes32 decoder/read bridge.
theorem scratch_decodeABIValue_bytes32_readNat {bytes : List UInt8} {start endOffset : Nat}
    {value : UInt256}
    (h :
      decodeABIValue? bytes32 bytes start =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE value), endOffset)) :
    readNat? bytes start = some value.toNat ∧ endOffset = start + 32 := by
  obtain ⟨_hend, hle⟩ := decodeABIValue_elem_end_le h
  have htake : ((bytes.drop start).take 32).length = 32 := by
    rw [List.length_take, List.length_drop]
    omega
  have hok :
      decodeABIValue? bytes32 bytes start =
        some (.fixedBytes ⟨31, by decide⟩ ((bytes.drop start).take 32), start + 32) := by
    unfold bytes32
    simp only [decodeABIValue?, readBytes?, bind, Option.bind]
    rw [if_pos htake]
    simp only
    unfold zeroPadding? readBytes?
    simp
  rw [hok] at h
  injection h with hpair
  injection hpair with hval hend'
  injection hval with _ hbytes
  constructor
  · unfold readNat? readWord? readBytes?
    rw [if_pos htake]
    simp only [bind, Option.bind]
    rw [hbytes]
    simp [scratch_word_toBytesBE_length_32, scratch_bytesToWord_toBytesBE, UInt256.toNat]
  · exact hend'.symm

-- LIBRARY CANDIDATE: dynamic-array decoder nth/read bridge for bytes32 arrays.
theorem scratch_decodeABIArrayStaticElems_bytes32_lookup_readNat {n : Nat}
    {bytes : List UInt8} {start endOffset i : Nat} {value : UInt256}
    {values : List Value}
    (hdec : decodeABIArrayStaticElems? bytes32 n 32 bytes start = some (values, endOffset))
    (hlookup :
      lookupNth? values i =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE value))) :
    readNat? bytes (start + 32 * i) = some value.toNat := by
  induction n generalizing start endOffset i values with
  | zero =>
      simp [decodeABIArrayStaticElems?] at hdec
      rcases hdec with ⟨hvalues, _hend⟩
      cases hvalues
      cases i <;> simp [lookupNth?] at hlookup
  | succ n ih =>
      rw [decodeABIArrayStaticElems?] at hdec
      cases hval : decodeABIValue? bytes32 bytes start with
      | none => simp [hval] at hdec
      | some p =>
          rcases p with ⟨headValue, headEnd⟩
          by_cases hendHead : headEnd = start + 32
          · simp [hval, hendHead] at hdec
            cases hrest : decodeABIArrayStaticElems? bytes32 n 32 bytes headEnd with
            | none =>
                have hrest' :
                    decodeABIArrayStaticElems? bytes32 n 32 bytes (start + 32) = none := by
                  simpa [hendHead] using hrest
                simp [hrest'] at hdec
            | some q =>
                rcases q with ⟨tailValues, restEnd⟩
                have hrest' :
                    decodeABIArrayStaticElems? bytes32 n 32 bytes (start + 32) =
                      some (tailValues, restEnd) := by
                  simpa [hendHead] using hrest
                simp [hrest'] at hdec
                rcases hdec with ⟨hvalues, hend⟩
                cases hvalues
                cases hend
                cases i with
                | zero =>
                    simp [lookupNth?] at hlookup
                    cases hlookup
                    exact (scratch_decodeABIValue_bytes32_readNat hval).1
                | succ i =>
                    simp [lookupNth?] at hlookup
                    have htail := ih hrest hlookup
                    have hoff : start + 32 * (i + 1) = headEnd + 32 * i := by omega
                    simpa [hoff] using htail
          · simp [hval, hendHead] at hdec

theorem revealDecode_dynamicArray_uint256_lookup_readNat {bytes : List UInt8}
    {start endOffset i : Nat} {values : List Value} {value : UInt256}
    (hdec :
      decodeABIValue? (.dynamicArray uint256) bytes start = some (.array values, endOffset))
    (hlookup : lookupNth? values i = some (.int (Int.ofNat value.toNat))) :
    readNat? bytes (start + 32 + 32 * i) = some value.toNat := by
  unfold decodeABIValue? at hdec
  cases hread : readNat? bytes start with
  | none => simp [hread] at hdec
  | some len =>
      by_cases hmax : solcMaxU64 < len
      · simp [hread, hmax] at hdec
      · simp [hread, hmax, staticABIEncodedSize?, isDynamicABIType] at hdec
        cases hstatic : decodeABIArrayStaticElems? uint256 len 32 bytes (start + 32) with
        | none =>
            change ((decodeABIArrayStaticElems? uint256 len 32 bytes (start + 32)).bind
                fun p => some (Value.array p.1, p.2)) =
                  some (Value.array values, endOffset) at hdec
            rw [hstatic] at hdec
            simp at hdec
        | some p =>
            rcases p with ⟨values0, end0⟩
            change ((decodeABIArrayStaticElems? uint256 len 32 bytes (start + 32)).bind
                fun p => some (Value.array p.1, p.2)) =
                  some (Value.array values, endOffset) at hdec
            rw [hstatic] at hdec
            simp at hdec
            rcases hdec with ⟨hvalues, _hend⟩
            cases hvalues
            exact scratch_decodeABIArrayStaticElems_uint256_lookup_readNat hstatic hlookup

theorem revealDecode_dynamicArray_bool_lookup_readNat {bytes : List UInt8}
    {start endOffset i word : Nat} {values : List Value}
    (hdec :
      decodeABIValue? (.dynamicArray boolTy) bytes start = some (.array values, endOffset))
    (hlookup : lookupNth? values i = some (rawBoolWordValue word)) :
    readNat? bytes (start + 32 + 32 * i) = some word := by
  unfold decodeABIValue? at hdec
  cases hread : readNat? bytes start with
  | none => simp [hread] at hdec
  | some len =>
      by_cases hmax : solcMaxU64 < len
      · simp [hread, hmax] at hdec
      · simp [hread, hmax, boolTy, staticABIEncodedSize?, isDynamicABIType] at hdec
        cases hraw : decodeABIRawBoolArrayElems? len bytes (start + 32) with
        | none => simp [hraw] at hdec
        | some p =>
            rcases p with ⟨values0, end0⟩
            simp [hraw] at hdec
            rcases hdec with ⟨hvalues, _hend⟩
            cases hvalues
            exact scratch_decodeABIRawBoolArrayElems_lookup_readNat hraw hlookup

theorem revealDecode_dynamicArray_bytes32_lookup_readNat {bytes : List UInt8}
    {start endOffset i : Nat} {values : List Value} {value : UInt256}
    (hdec :
      decodeABIValue? (.dynamicArray bytes32) bytes start = some (.array values, endOffset))
    (hlookup :
      lookupNth? values i =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE value))) :
    readNat? bytes (start + 32 + 32 * i) = some value.toNat := by
  unfold decodeABIValue? at hdec
  cases hread : readNat? bytes start with
  | none => simp [hread] at hdec
  | some len =>
      by_cases hmax : solcMaxU64 < len
      · simp [hread, hmax] at hdec
      · simp [hread, hmax, staticABIEncodedSize?, isDynamicABIType] at hdec
        cases hstatic : decodeABIArrayStaticElems? bytes32 len 32 bytes (start + 32) with
        | none =>
            change ((decodeABIArrayStaticElems? bytes32 len 32 bytes (start + 32)).bind
                fun p => some (Value.array p.1, p.2)) =
                  some (Value.array values, endOffset) at hdec
            rw [hstatic] at hdec
            simp at hdec
        | some p =>
            rcases p with ⟨values0, end0⟩
            change ((decodeABIArrayStaticElems? bytes32 len 32 bytes (start + 32)).bind
                fun p => some (Value.array p.1, p.2)) =
                  some (Value.array values, endOffset) at hdec
            rw [hstatic] at hdec
            simp at hdec
            rcases hdec with ⟨hvalues, _hend⟩
            cases hvalues
            exact scratch_decodeABIArrayStaticElems_bytes32_lookup_readNat hstatic hlookup

-- LIBRARY CANDIDATE: fixed-length byte arrays are injectively decoded as base-256 words.
theorem scratch_fromBytes'_inj_of_length {xs ys : List UInt8}
    (hlen : xs.length = ys.length)
    (h : fromBytes' xs = fromBytes' ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons _ _ => simp at hlen
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          simp at hlen
          unfold fromBytes' at h
          have hx : x.toFin.val < 2^8 := x.toFin.isLt
          have hy : y.toFin.val < 2^8 := y.toFin.isLt
          have hheadNat : x.toFin.val = y.toFin.val := by
            have hmod := congrArg (fun n => n % 2^8) h
            omega
          have htail : fromBytes' xs = fromBytes' ys := by
            have hdiv := congrArg (fun n => n / 2^8) h
            omega
          have hxy : x = y := UInt8.toNat_inj.mp hheadNat
          rw [hxy]
          congr
          exact ih hlen htail

-- LIBRARY CANDIDATE: fixed-length big-endian byte arrays are injectively decoded.
theorem scratch_fromBytesBigEndian_inj_of_length {xs ys : List UInt8}
    (hlen : xs.length = ys.length)
    (h : fromBytesBigEndian xs = fromBytesBigEndian ys) : xs = ys := by
  unfold fromBytesBigEndian at h
  apply List.reverse_injective
  apply scratch_fromBytes'_inj_of_length
  · simpa [hlen]
  · exact h

-- LIBRARY CANDIDATE: bytes32 decoder words round-trip to their original 32 bytes.
theorem scratch_toBytesBE_bytesToWord_of_length {bs : List UInt8}
    (hlen : bs.length = 32) :
    EVM.Word.toBytesBE (ABI.bytesToWord bs) = bs := by
  apply scratch_fromBytesBigEndian_inj_of_length
  · rw [show (EVM.Word.toBytesBE (ABI.bytesToWord bs)).length = 32 by
        simpa using word_toBytesBE_toByteArray_size (ABI.bytesToWord bs), hlen]
  · have hleft :
        fromBytesBigEndian (EVM.Word.toBytesBE (ABI.bytesToWord bs)) =
          (ABI.bytesToWord bs).toNat := by
      have h := congrArg fromByteArrayBigEndian
        (word_toBytesBE_toByteArray_eq_toByteArray (ABI.bytesToWord bs))
      simpa [fromByteArrayBigEndian, byteArray_toList_eq] using
        h.trans (fromByteArrayBigEndian_toByteArray (ABI.bytesToWord bs))
    have hright : (ABI.bytesToWord bs).toNat = fromBytesBigEndian bs := by
      unfold ABI.bytesToWord
      have hlt : fromBytesBigEndian bs < UInt256.size := by
        unfold fromBytesBigEndian
        have hle := fromBytes'_le (bs := bs.reverse)
        rw [List.length_reverse, hlen] at hle
        simpa [UInt256.size] using hle
      simpa [fromByteArrayBigEndian, byteArray_toList_eq] using
        (ulit_toNat' (fromBytesBigEndian bs) hlt)
    rw [hleft, hright]

theorem scratch_decodeABIValue_uint256_shape {bytes : List UInt8} {start endOffset : Nat}
    {value : Value}
    (h : decodeABIValue? uint256 bytes start = some (value, endOffset)) :
    ∃ word : UInt256, value = .int (Int.ofNat word.toNat) ∧ endOffset = start + 32 := by
  obtain ⟨_hend, hle⟩ := decodeABIValue_elem_end_le h
  have htake : ((bytes.drop start).take 32).length = 32 := by
    rw [List.length_take, List.length_drop]
    omega
  have hok :
      decodeABIValue? uint256 bytes start =
        some (.int (Int.ofNat (ABI.bytesToWord ((bytes.drop start).take 32)).toNat),
          start + 32) := by
    simpa [uint256, uint256Int, abiUInt256] using
      decodeABIValue_uint256_ok (bytes := bytes) (start := start) htake
  rw [hok] at h
  injection h with hpair
  injection hpair with hvalue hend
  exact ⟨ABI.bytesToWord ((bytes.drop start).take 32), hvalue.symm, hend.symm⟩

theorem scratch_decodeABIValue_bytes32_shape {bytes : List UInt8} {start endOffset : Nat}
    {value : Value}
    (h : decodeABIValue? bytes32 bytes start = some (value, endOffset)) :
    ∃ word : UInt256,
      value = .fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE word) ∧
        endOffset = start + 32 := by
  obtain ⟨_hend, hle⟩ := decodeABIValue_elem_end_le h
  have htake : ((bytes.drop start).take 32).length = 32 := by
    rw [List.length_take, List.length_drop]
    omega
  have hok :
      decodeABIValue? bytes32 bytes start =
        some (.fixedBytes ⟨31, by decide⟩ ((bytes.drop start).take 32), start + 32) := by
    unfold bytes32
    simp only [decodeABIValue?, readBytes?, bind, Option.bind]
    rw [if_pos htake]
    simp only
    unfold zeroPadding? readBytes?
    simp
  rw [hok] at h
  injection h with hpair
  injection hpair with hvalue hend
  refine ⟨ABI.bytesToWord ((bytes.drop start).take 32), ?_, hend.symm⟩
  rw [← hvalue]
  congr 2
  exact (scratch_toBytesBE_bytesToWord_of_length htake).symm

theorem scratch_decodeABIArrayStaticElems_uint256_lookup_shape {n : Nat}
    {bytes : List UInt8} {start endOffset i : Nat} {values : List Value}
    (hdec : decodeABIArrayStaticElems? uint256 n 32 bytes start = some (values, endOffset))
    (hbound : i < values.length) :
    ∃ value : UInt256, lookupNth? values i = some (.int (Int.ofNat value.toNat)) := by
  induction n generalizing start endOffset i values with
  | zero =>
      simp [decodeABIArrayStaticElems?] at hdec
      rcases hdec with ⟨hvalues, _hend⟩
      cases hvalues
      simp at hbound
  | succ n ih =>
      rw [decodeABIArrayStaticElems?] at hdec
      cases hval : decodeABIValue? uint256 bytes start with
      | none => simp [hval] at hdec
      | some p =>
          rcases p with ⟨headValue, headEnd⟩
          by_cases hendHead : headEnd = start + 32
          · simp [hval, hendHead] at hdec
            cases hrest : decodeABIArrayStaticElems? uint256 n 32 bytes headEnd with
            | none =>
                have hrest' :
                    decodeABIArrayStaticElems? uint256 n 32 bytes (start + 32) = none := by
                  simpa [hendHead] using hrest
                simp [hrest'] at hdec
            | some q =>
                rcases q with ⟨tailValues, restEnd⟩
                have hrest' :
                    decodeABIArrayStaticElems? uint256 n 32 bytes (start + 32) =
                      some (tailValues, restEnd) := by
                  simpa [hendHead] using hrest
                simp [hrest'] at hdec
                rcases hdec with ⟨hvalues, _hend⟩
                cases hvalues
                cases i with
                | zero =>
                    obtain ⟨value, hshape, _hend⟩ :=
                      scratch_decodeABIValue_uint256_shape hval
                    refine ⟨value, ?_⟩
                    simp [lookupNth?, hshape]
                | succ i =>
                    simp at hbound
                    obtain ⟨value, hlookup⟩ := ih hrest hbound
                    refine ⟨value, ?_⟩
                    simpa [lookupNth?] using hlookup
          · simp [hval, hendHead] at hdec

theorem scratch_decodeABIRawBoolArrayElems_lookup_shape {n : Nat}
    {bytes : List UInt8} {start endOffset i : Nat} {values : List Value}
    (hdec : decodeABIRawBoolArrayElems? n bytes start = some (values, endOffset))
    (hbound : i < values.length) :
    ∃ word : Nat, lookupNth? values i = some (rawBoolWordValue word) := by
  induction n generalizing start endOffset i values with
  | zero =>
      simp [decodeABIRawBoolArrayElems?] at hdec
      rcases hdec with ⟨hvalues, _hend⟩
      cases hvalues
      simp at hbound
  | succ n ih =>
      rw [decodeABIRawBoolArrayElems?] at hdec
      cases hread : readNat? bytes start with
      | none => simp [hread] at hdec
      | some word =>
          simp [hread] at hdec
          cases hrest : decodeABIRawBoolArrayElems? n bytes (start + 32) with
          | none => simp [hrest] at hdec
          | some p =>
              rcases p with ⟨tailValues, restEnd⟩
              simp [hrest] at hdec
              rcases hdec with ⟨hvalues, _hend⟩
              cases hvalues
              cases i with
              | zero =>
                  refine ⟨word, ?_⟩
                  simp [lookupNth?]
              | succ i =>
                  simp at hbound
                  obtain ⟨word', hlookup⟩ := ih hrest hbound
                  refine ⟨word', ?_⟩
                  simpa [lookupNth?] using hlookup

theorem scratch_decodeABIArrayStaticElems_bytes32_lookup_shape {n : Nat}
    {bytes : List UInt8} {start endOffset i : Nat} {values : List Value}
    (hdec : decodeABIArrayStaticElems? bytes32 n 32 bytes start = some (values, endOffset))
    (hbound : i < values.length) :
    ∃ value : UInt256,
      lookupNth? values i =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE value)) := by
  induction n generalizing start endOffset i values with
  | zero =>
      simp [decodeABIArrayStaticElems?] at hdec
      rcases hdec with ⟨hvalues, _hend⟩
      cases hvalues
      simp at hbound
  | succ n ih =>
      rw [decodeABIArrayStaticElems?] at hdec
      cases hval : decodeABIValue? bytes32 bytes start with
      | none => simp [hval] at hdec
      | some p =>
          rcases p with ⟨headValue, headEnd⟩
          by_cases hendHead : headEnd = start + 32
          · simp [hval, hendHead] at hdec
            cases hrest : decodeABIArrayStaticElems? bytes32 n 32 bytes headEnd with
            | none =>
                have hrest' :
                    decodeABIArrayStaticElems? bytes32 n 32 bytes (start + 32) = none := by
                  simpa [hendHead] using hrest
                simp [hrest'] at hdec
            | some q =>
                rcases q with ⟨tailValues, restEnd⟩
                have hrest' :
                    decodeABIArrayStaticElems? bytes32 n 32 bytes (start + 32) =
                      some (tailValues, restEnd) := by
                  simpa [hendHead] using hrest
                simp [hrest'] at hdec
                rcases hdec with ⟨hvalues, _hend⟩
                cases hvalues
                cases i with
                | zero =>
                    obtain ⟨value, hshape, _hend⟩ :=
                      scratch_decodeABIValue_bytes32_shape hval
                    refine ⟨value, ?_⟩
                    simp [lookupNth?, hshape]
                | succ i =>
                    simp at hbound
                    obtain ⟨value, hlookup⟩ := ih hrest hbound
                    refine ⟨value, ?_⟩
                    simpa [lookupNth?] using hlookup
          · simp [hval, hendHead] at hdec

theorem revealDecode_dynamicArray_uint256_lookup_shape {bytes : List UInt8}
    {start endOffset i : Nat} {values : List Value}
    (hdec :
      decodeABIValue? (.dynamicArray uint256) bytes start = some (.array values, endOffset))
    (hbound : i < values.length) :
    ∃ value : UInt256, lookupNth? values i = some (.int (Int.ofNat value.toNat)) := by
  unfold decodeABIValue? at hdec
  cases hread : readNat? bytes start with
  | none => simp [hread] at hdec
  | some len =>
      by_cases hmax : solcMaxU64 < len
      · simp [hread, hmax] at hdec
      · simp [hread, hmax, staticABIEncodedSize?, isDynamicABIType] at hdec
        cases hstatic : decodeABIArrayStaticElems? uint256 len 32 bytes (start + 32) with
        | none =>
            change ((decodeABIArrayStaticElems? uint256 len 32 bytes (start + 32)).bind
                fun p => some (Value.array p.1, p.2)) =
                  some (Value.array values, endOffset) at hdec
            rw [hstatic] at hdec
            simp at hdec
        | some p =>
            rcases p with ⟨values0, end0⟩
            change ((decodeABIArrayStaticElems? uint256 len 32 bytes (start + 32)).bind
                fun p => some (Value.array p.1, p.2)) =
                  some (Value.array values, endOffset) at hdec
            rw [hstatic] at hdec
            simp at hdec
            rcases hdec with ⟨hvalues, _hend⟩
            cases hvalues
            exact scratch_decodeABIArrayStaticElems_uint256_lookup_shape hstatic hbound

theorem revealDecode_dynamicArray_bool_lookup_shape {bytes : List UInt8}
    {start endOffset i : Nat} {values : List Value}
    (hdec :
      decodeABIValue? (.dynamicArray boolTy) bytes start = some (.array values, endOffset))
    (hbound : i < values.length) :
    ∃ word : Nat, lookupNth? values i = some (rawBoolWordValue word) := by
  unfold decodeABIValue? at hdec
  cases hread : readNat? bytes start with
  | none => simp [hread] at hdec
  | some len =>
      by_cases hmax : solcMaxU64 < len
      · simp [hread, hmax] at hdec
      · simp [hread, hmax, boolTy, staticABIEncodedSize?, isDynamicABIType] at hdec
        cases hraw : decodeABIRawBoolArrayElems? len bytes (start + 32) with
        | none => simp [hraw] at hdec
        | some p =>
            rcases p with ⟨values0, end0⟩
            simp [hraw] at hdec
            rcases hdec with ⟨hvalues, _hend⟩
            cases hvalues
            exact scratch_decodeABIRawBoolArrayElems_lookup_shape hraw hbound

theorem revealDecode_dynamicArray_bytes32_lookup_shape {bytes : List UInt8}
    {start endOffset i : Nat} {values : List Value}
    (hdec :
      decodeABIValue? (.dynamicArray bytes32) bytes start = some (.array values, endOffset))
    (hbound : i < values.length) :
    ∃ value : UInt256,
      lookupNth? values i =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE value)) := by
  unfold decodeABIValue? at hdec
  cases hread : readNat? bytes start with
  | none => simp [hread] at hdec
  | some len =>
      by_cases hmax : solcMaxU64 < len
      · simp [hread, hmax] at hdec
      · simp [hread, hmax, staticABIEncodedSize?, isDynamicABIType] at hdec
        cases hstatic : decodeABIArrayStaticElems? bytes32 len 32 bytes (start + 32) with
        | none =>
            change ((decodeABIArrayStaticElems? bytes32 len 32 bytes (start + 32)).bind
                fun p => some (Value.array p.1, p.2)) =
                  some (Value.array values, endOffset) at hdec
            rw [hstatic] at hdec
            simp at hdec
        | some p =>
            rcases p with ⟨values0, end0⟩
            change ((decodeABIArrayStaticElems? bytes32 len 32 bytes (start + 32)).bind
                fun p => some (Value.array p.1, p.2)) =
                  some (Value.array values, endOffset) at hdec
            rw [hstatic] at hdec
            simp at hdec
            rcases hdec with ⟨hvalues, _hend⟩
            cases hvalues
            exact scratch_decodeABIArrayStaticElems_bytes32_lookup_shape hstatic hbound

theorem blindAuctionDecode_reveal_array_decodes {I : ExecutionEnv} {callargs : Store}
    {values fakes secrets : List Value}
    (hdec : decodeCalldata (revealTransition.params.map Param.name)
      (transitionSignature revealTransition).paramTypes I.calldata = some callargs)
    (hstore :
      callargs =
        (((∅ : Store).insert "values" (.array values)).insert "fakes" (.array fakes)).insert
          "secrets" (.array secrets)) :
    ∃ e0 e1 e2,
      decodeABIValue? (.dynamicArray uint256) (List.drop 4 I.calldata.toList)
          (revealValuesOffsetWord I).toNat = some (.array values, e0) ∧
      decodeABIValue? (.dynamicArray boolTy) (List.drop 4 I.calldata.toList)
          (revealFakesOffsetWord I).toNat = some (.array fakes, e1) ∧
      decodeABIValue? (.dynamicArray bytes32) (List.drop 4 I.calldata.toList)
          (revealSecretsOffsetWord I).toNat = some (.array secrets, e2) := by
  change decodeCalldata ["values", "fakes", "secrets"]
    [.dynamicArray uint256, .dynamicArray boolTy, .dynamicArray bytes32] I.calldata =
      some callargs at hdec
  unfold decodeCalldata at hdec
  simp only [List.isEmpty_cons] at hdec
  split at hdec
  · contradiction
  next _ =>
    split at hdec
    · contradiction
    next _ =>
      simp [decodeCalldata.decodeArgs, decodeABIValues?, abiTupleHeadSize?, isDynamicABIType,
        Option.bind, bind] at hdec
      cases h0 : readNat? (List.drop 4 I.calldata.toList) 0 with
      | none => simp [h0] at hdec
      | some off0 =>
          by_cases hmax0 : solcMaxU64 < off0
          · simp [h0, hmax0] at hdec
          · simp [h0, hmax0] at hdec
            cases hval0 : decodeABIValue? (.dynamicArray uint256)
                (List.drop 4 I.calldata.toList) off0 with
            | none => simp [hval0] at hdec
            | some p0 =>
                rcases p0 with ⟨v0, e0⟩
                rcases decodeABIValue_dynamicArray_is_array hval0 with ⟨values0, rfl⟩
                simp [hval0] at hdec
                cases h1 : readNat? (List.drop 4 I.calldata.toList) 32 with
                | none => simp [h1] at hdec
                | some off1 =>
                    by_cases hmax1 : solcMaxU64 < off1
                    · simp [h1, hmax1] at hdec
                    · simp [h1, hmax1] at hdec
                      cases hval1 : decodeABIValue? (.dynamicArray boolTy)
                          (List.drop 4 I.calldata.toList) off1 with
                      | none => simp [hval1] at hdec
                      | some p1 =>
                          rcases p1 with ⟨v1, e1⟩
                          rcases decodeABIValue_dynamicArray_is_array hval1 with ⟨fakes0, rfl⟩
                          simp [hval1] at hdec
                          cases h2 : readNat? (List.drop 4 I.calldata.toList) 64 with
                          | none => simp [h2] at hdec
                          | some off2 =>
                              by_cases hmax2 : solcMaxU64 < off2
                              · simp [h2, hmax2] at hdec
                              · simp [h2, hmax2] at hdec
                                cases hval2 : decodeABIValue? (.dynamicArray bytes32)
                                    (List.drop 4 I.calldata.toList) off2 with
                                | none => simp [hval2] at hdec
                                | some p2 =>
                                    rcases p2 with ⟨v2, e2⟩
                                    rcases decodeABIValue_dynamicArray_is_array hval2 with
                                      ⟨secrets0, rfl⟩
                                    simp [hval2] at hdec
                                    simp [decodeCalldata.insertValues] at hdec
                                    by_cases hargsShort : I.calldata.toList.length - 4 < 96
                                    · simp [hargsShort] at hdec
                                    · simp [hargsShort] at hdec
                                      rcases hdec with ⟨_, hstore0⟩
                                      have hcall :
                                          (((∅ : Store).insert "values"
                                                (.array values0)).insert "fakes"
                                                (.array fakes0)).insert "secrets"
                                                (.array secrets0) =
                                            (((∅ : Store).insert "values"
                                                (.array values)).insert "fakes"
                                                (.array fakes)).insert "secrets"
                                                (.array secrets) := by
                                        rw [hstore0, hstore]
                                      have hv : values0 = values := by
                                        have := congrArg (fun m => m.get? "values") hcall
                                        change
                                          ((((∅ : Store).insert "values"
                                                (.array values0)).insert "fakes"
                                                (.array fakes0)).insert "secrets"
                                                (.array secrets0)).get? "values" =
                                            ((((∅ : Store).insert "values"
                                                (.array values)).insert "fakes"
                                                (.array fakes)).insert "secrets"
                                                (.array secrets)).get? "values" at this
                                        rw [store_get_ne, store_get_ne, store_get_self,
                                          store_get_ne, store_get_ne, store_get_self] at this
                                          <;> try decide
                                        injection this with hsome
                                        injection hsome with hv
                                      have hf : fakes0 = fakes := by
                                        have := congrArg (fun m => m.get? "fakes") hcall
                                        change
                                          ((((∅ : Store).insert "values"
                                                (.array values0)).insert "fakes"
                                                (.array fakes0)).insert "secrets"
                                                (.array secrets0)).get? "fakes" =
                                            ((((∅ : Store).insert "values"
                                                (.array values)).insert "fakes"
                                                (.array fakes)).insert "secrets"
                                                (.array secrets)).get? "fakes" at this
                                        rw [store_get_ne, store_get_self, store_get_ne,
                                          store_get_self] at this <;> try decide
                                        injection this with hsome
                                        injection hsome with hf
                                      have hs : secrets0 = secrets := by
                                        have := congrArg (fun m => m.get? "secrets") hcall
                                        change
                                          ((((∅ : Store).insert "values"
                                                (.array values0)).insert "fakes"
                                                (.array fakes0)).insert "secrets"
                                                (.array secrets0)).get? "secrets" =
                                            ((((∅ : Store).insert "values"
                                                (.array values)).insert "fakes"
                                                (.array fakes)).insert "secrets"
                                                (.array secrets)).get? "secrets" at this
                                        rw [store_get_self, store_get_self] at this
                                        injection this with hsome
                                        injection hsome with hs
                                      subst values
                                      subst fakes
                                      subst secrets
                                      have hoff0Word :=
                                        readNat?_calldataWord_eq (I := I) (headOff := 0) h0
                                      have hoff1Word :=
                                        readNat?_calldataWord_eq (I := I) (headOff := 32) h1
                                      have hoff2Word :=
                                        readNat?_calldataWord_eq (I := I) (headOff := 64) h2
                                      have hoff0ToNat :
                                          (revealValuesOffsetWord I).toNat = off0 := by
                                        unfold revealValuesOffsetWord
                                        rw [hoff0Word]
                                        exact ulit_toNat' off0 (by
                                          have : off0 ≤ solcMaxU64 := by omega
                                          unfold solcMaxU64 at this
                                          exact lt_size_of_lt_sign
                                            (by omega : off0 < 2 ^ 255))
                                      have hoff1ToNat :
                                          (revealFakesOffsetWord I).toNat = off1 := by
                                        unfold revealFakesOffsetWord
                                        rw [hoff1Word]
                                        exact ulit_toNat' off1 (by
                                          have : off1 ≤ solcMaxU64 := by omega
                                          unfold solcMaxU64 at this
                                          exact lt_size_of_lt_sign
                                            (by omega : off1 < 2 ^ 255))
                                      have hoff2ToNat :
                                          (revealSecretsOffsetWord I).toNat = off2 := by
                                        unfold revealSecretsOffsetWord
                                        rw [hoff2Word]
                                        exact ulit_toNat' off2 (by
                                          have : off2 ≤ solcMaxU64 := by omega
                                          unfold solcMaxU64 at this
                                          exact lt_size_of_lt_sign
                                            (by omega : off2 < 2 ^ 255))
                                      refine ⟨e0, e1, e2, ?_, ?_, ?_⟩
                                      · simpa [hoff0ToNat] using hval0
                                      · simpa [hoff1ToNat] using hval1
                                      · simpa [hoff2ToNat] using hval2

theorem revealCalldataLoad_of_readNat {I : ExecutionEnv} {headOff : Nat}
    {addr value : UInt256}
    (hread : readNat? (List.drop 4 I.calldata.toList) headOff = some value.toNat)
    (haddr : addr.toNat = 4 + headOff) :
    uInt256OfByteArray (I.calldata.readBytes addr.toNat 32) = value := by
  have hword := readNat?_calldataWord_eq (I := I) (headOff := headOff) hread
  have hcalldata : calldataWord I.calldata (4 + headOff) = value := by
    rw [hword, u256_ofNat_toNat]
  unfold calldataWord at hcalldata
  rw [haddr]
  exact hcalldata

theorem revealArrayElemAddr_toNat {off i : UInt256} {lim : Nat}
    (hbound : 4 + (off.toNat + 32 + 32 * i.toNat) + 32 ≤ lim)
    (hsize : lim < UInt256.size) :
    (UInt256.mul ⟨32⟩ i + (((⟨4⟩ : UInt256) + off) + ⟨32⟩)).toNat =
      4 + (off.toNat + 32 + 32 * i.toNat) := by
  have hmul : (UInt256.mul (⟨32⟩ : UInt256) i).toNat = 32 * i.toNat := by
    unfold UInt256.mul
    change (((⟨32⟩ : UInt256).val * i.val).val) = 32 * i.toNat
    rw [Fin.val_mul]
    have hprod : 32 * i.toNat < UInt256.size := by omega
    rw [show (⟨32⟩ : UInt256).val.val = 32 by decide]
    exact Nat.mod_eq_of_lt hprod
  have h4off32 : (((⟨4⟩ : UInt256) + off) + ⟨32⟩).toNat =
      4 + off.toNat + 32 := by
    rw [← u256_ofNat_toNat off]
    simpa [u256_ofNat_toNat, Nat.add_assoc] using
      (uadd3_ofNat_toNat (a := 4) (b := off.toNat) (c := 32)
        (by norm_num [UInt256.size]) off.val.isLt (by norm_num [UInt256.size])
        (by omega) (by omega))
  rw [uadd_toNat, hmul, h4off32]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem blindAuctionDecode_reveal_values_load {I : ExecutionEnv} {callargs : Store}
    {values fakes secrets : List Value} {i value : UInt256}
    (hsize : I.calldata.size < UInt256.size)
    (hdec : decodeCalldata (revealTransition.params.map Param.name)
      (transitionSignature revealTransition).paramTypes I.calldata = some callargs)
    (hstore :
      callargs =
        (((∅ : Store).insert "values" (.array values)).insert "fakes" (.array fakes)).insert
          "secrets" (.array secrets))
    (hlookup : lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat))) :
    uInt256OfByteArray
      (I.calldata.readBytes
        (UInt256.mul ⟨32⟩ i + (((⟨4⟩ : UInt256) + revealValuesOffsetWord I) + ⟨32⟩)).toNat
        32) = value := by
  obtain ⟨e0, _e1, _e2, hval0, _hval1, _hval2⟩ :=
    blindAuctionDecode_reveal_array_decodes hdec hstore
  have hread :
      readNat? (List.drop 4 I.calldata.toList)
        ((revealValuesOffsetWord I).toNat + 32 + 32 * i.toNat) = some value.toNat := by
    exact revealDecode_dynamicArray_uint256_lookup_readNat hval0 hlookup
  have hreadLen := readNat?_some_length hread
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hbound :
      4 + ((revealValuesOffsetWord I).toNat + 32 + 32 * i.toNat) + 32 ≤
        I.calldata.size := by
    rw [List.length_drop, htlen] at hreadLen
    omega
  exact revealCalldataLoad_of_readNat hread
    (revealArrayElemAddr_toNat (off := revealValuesOffsetWord I) (i := i)
      (lim := I.calldata.size) hbound hsize)

theorem blindAuctionDecode_reveal_fakes_load {I : ExecutionEnv} {callargs : Store}
    {values fakes secrets : List Value} {i : UInt256} {word : Nat}
    (hsize : I.calldata.size < UInt256.size)
    (hdec : decodeCalldata (revealTransition.params.map Param.name)
      (transitionSignature revealTransition).paramTypes I.calldata = some callargs)
    (hstore :
      callargs =
        (((∅ : Store).insert "values" (.array values)).insert "fakes" (.array fakes)).insert
          "secrets" (.array secrets))
    (hlookup : lookupNth? fakes i.toNat = some (rawBoolWordValue word)) :
    uInt256OfByteArray
      (I.calldata.readBytes
        (UInt256.mul ⟨32⟩ i + (((⟨4⟩ : UInt256) + revealFakesOffsetWord I) + ⟨32⟩)).toNat
        32) = UInt256.ofNat word := by
  obtain ⟨_e0, e1, _e2, _hval0, hval1, _hval2⟩ :=
    blindAuctionDecode_reveal_array_decodes hdec hstore
  have hread :
      readNat? (List.drop 4 I.calldata.toList)
        ((revealFakesOffsetWord I).toNat + 32 + 32 * i.toNat) = some word := by
    exact revealDecode_dynamicArray_bool_lookup_readNat hval1 hlookup
  have hreadLen := readNat?_some_length hread
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hbound :
      4 + ((revealFakesOffsetWord I).toNat + 32 + 32 * i.toNat) + 32 ≤
        I.calldata.size := by
    rw [List.length_drop, htlen] at hreadLen
    omega
  have hwordSmall : (UInt256.ofNat word).toNat = word := by
    unfold readNat? readWord? readBytes? at hread
    have hle :
        32 ≤ (List.drop 4 I.calldata.toList).length -
          ((revealFakesOffsetWord I).toNat + 32 + 32 * i.toNat) := by
      omega
    have hleFull :
        32 ≤ I.calldata.toList.length -
          (4 + ((revealFakesOffsetWord I).toNat + 32 + 32 * i.toNat)) := by
      rw [htlen]
      omega
    simp [hle, hleFull, List.drop_drop] at hread
    cases hread
    exact ulit_toNat' _
      (bytesToWord
        (List.take 32
          (List.drop (4 + ((revealFakesOffsetWord I).toNat + 32 + 32 * i.toNat))
            I.calldata.toList))).val.isLt
  have hreadWord :
      readNat? (List.drop 4 I.calldata.toList)
        ((revealFakesOffsetWord I).toNat + 32 + 32 * i.toNat) =
          some (UInt256.ofNat word).toNat := by
    simpa [hwordSmall] using hread
  exact revealCalldataLoad_of_readNat hreadWord
    (revealArrayElemAddr_toNat (off := revealFakesOffsetWord I) (i := i)
      (lim := I.calldata.size) hbound hsize)

theorem blindAuctionDecode_reveal_secrets_load {I : ExecutionEnv} {callargs : Store}
    {values fakes secrets : List Value} {i secret : UInt256}
    (hsize : I.calldata.size < UInt256.size)
    (hdec : decodeCalldata (revealTransition.params.map Param.name)
      (transitionSignature revealTransition).paramTypes I.calldata = some callargs)
    (hstore :
      callargs =
        (((∅ : Store).insert "values" (.array values)).insert "fakes" (.array fakes)).insert
          "secrets" (.array secrets))
    (hlookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret))) :
    uInt256OfByteArray
      (I.calldata.readBytes
        (UInt256.mul ⟨32⟩ i + (((⟨4⟩ : UInt256) + revealSecretsOffsetWord I) + ⟨32⟩)).toNat
        32) = secret := by
  obtain ⟨_e0, _e1, e2, _hval0, _hval1, hval2⟩ :=
    blindAuctionDecode_reveal_array_decodes hdec hstore
  have hread :
      readNat? (List.drop 4 I.calldata.toList)
        ((revealSecretsOffsetWord I).toNat + 32 + 32 * i.toNat) = some secret.toNat := by
    exact revealDecode_dynamicArray_bytes32_lookup_readNat hval2 hlookup
  have hreadLen := readNat?_some_length hread
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hbound :
      4 + ((revealSecretsOffsetWord I).toNat + 32 + 32 * i.toNat) + 32 ≤
        I.calldata.size := by
    rw [List.length_drop, htlen] at hreadLen
    omega
  exact revealCalldataLoad_of_readNat hread
    (revealArrayElemAddr_toNat (off := revealSecretsOffsetWord I) (i := i)
      (lim := I.calldata.size) hbound hsize)

end BlindAuction
