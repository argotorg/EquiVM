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

abbrev revealScratchTimestampWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.header.timestamp

def revealScratchBiddingEndWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)

def revealScratchRevealEndWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)

def revealScratchBidsLengthSlot (I : ExecutionEnv) : UInt256 :=
  bidsBase (.address I.source)

def revealScratchBidsLengthWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (revealScratchBidsLengthSlot I) ⟨0⟩)

theorem revealScratchBiddingEndWord_accountMapEquiv {σ τ : AccountMap}
    (hστ : accountMapEquiv σ τ) (I : ExecutionEnv) :
    revealScratchBiddingEndWord σ I = revealScratchBiddingEndWord τ I := by
  exact accountMapEquiv_storage_findD hστ I.codeOwner ⟨1⟩ ⟨0⟩

theorem revealScratchRevealEndWord_accountMapEquiv {σ τ : AccountMap}
    (hστ : accountMapEquiv σ τ) (I : ExecutionEnv) :
    revealScratchRevealEndWord σ I = revealScratchRevealEndWord τ I := by
  exact accountMapEquiv_storage_findD hστ I.codeOwner ⟨2⟩ ⟨0⟩

theorem revealScratchBidsLengthWord_accountMapEquiv {σ τ : AccountMap}
    (hστ : accountMapEquiv σ τ) (I : ExecutionEnv) :
    revealScratchBidsLengthWord σ I = revealScratchBidsLengthWord τ I := by
  exact accountMapEquiv_storage_findD hστ I.codeOwner (revealScratchBidsLengthSlot I) ⟨0⟩

abbrev revealScratchSenderWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

abbrev revealScratchEmptyDecodedStack
    (I : ExecutionEnv) (valuesEnd fakesEnd secretsEnd : UInt256) : List UInt256 :=
  [⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd, ⟨276⟩, blindAuctionSelWord I]

abbrev revealDecodedStack (I : ExecutionEnv)
    (valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd : UInt256) : List UInt256 :=
  [secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩,
    blindAuctionSelWord I]

theorem blindAuctionRevealDecodeArrays1806_to_413
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : Nat}
    {sel valuesLen fakesLen secretsLen : UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
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
        = valuesLen)
    (hvaluesLenMax : UInt256.gt valuesLen revealMaxU64 = ⟨0⟩)
    (hvaluesEnd :
      UInt256.gt (((⟨4⟩ + revealValuesOffsetWord ee) + UInt256.shiftLeft valuesLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat ee.calldata.size) = ⟨0⟩)
    (hfakesGt : UInt256.gt (revealFakesOffsetWord ee) revealMaxU64 = ⟨0⟩)
    (hfakesStart :
      UInt256.slt ((⟨4⟩ + revealFakesOffsetWord ee) + ⟨31⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨1⟩)
    (hfakesLen :
      uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ + revealFakesOffsetWord ee).toNat 32)
        = fakesLen)
    (hfakesLenMax : UInt256.gt fakesLen revealMaxU64 = ⟨0⟩)
    (hfakesEnd :
      UInt256.gt (((⟨4⟩ + revealFakesOffsetWord ee) + UInt256.shiftLeft fakesLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat ee.calldata.size) = ⟨0⟩)
    (hsecretsGt : UInt256.gt (revealSecretsOffsetWord ee) revealMaxU64 = ⟨0⟩)
    (hsecretsStart :
      UInt256.slt ((⟨4⟩ + revealSecretsOffsetWord ee) + ⟨31⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨1⟩)
    (hsecretsLen :
      uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ + revealSecretsOffsetWord ee).toNat 32)
        = secretsLen)
    (hsecretsLenMax : UInt256.gt secretsLen revealMaxU64 = ⟨0⟩)
    (hsecretsEnd :
      UInt256.gt (((⟨4⟩ + revealSecretsOffsetWord ee) + UInt256.shiftLeft secretsLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat ee.calldata.size) = ⟨0⟩) :
    ∃ k' C', RD blindAuctionBytecode ee g s0 ⟨413⟩
      [secretsLen, (⟨4⟩ + revealSecretsOffsetWord ee) + ⟨32⟩,
        fakesLen, (⟨4⟩ + revealFakesOffsetWord ee) + ⟨32⟩,
        valuesLen, (⟨4⟩ + revealValuesOffsetWord ee) + ⟨32⟩, ⟨276⟩, sel]
      mem aw rdata acc k' C' := by
  obtain ⟨_, _, rd1713v⟩ := blindAuctionRevealDecodeValuesCall1806_to_1713 rd hvaluesGt
  obtain ⟨_, _, rd1840⟩ :=
    RD.blindAuctionRevealDecodeArray1713 rd1713v hvaluesStart hvaluesLen
      (by simpa [revealMaxU64] using hvaluesLenMax) hvaluesEnd (by jump_dest) (by simp)
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
    RD.blindAuctionRevealDecodeArray1713 rd1882 hfakesStart hfakesLen
      (by simpa [revealMaxU64] using hfakesLenMax) hfakesEnd (by jump_dest) (by simp)
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
    RD.blindAuctionRevealDecodeArray1713 rd1925 hsecretsStart hsecretsLen
      (by simpa [revealMaxU64] using hsecretsLenMax) hsecretsEnd (by jump_dest) (by simp)
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
  exact ⟨_, _, by simpa [revealDecodedStack] using rd1943⟩

theorem blindAuctionRevealDecodeArrays1806_to_887
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : Nat}
    {valuesLen fakesLen secretsLen : UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd : RD blindAuctionBytecode ee g s0 ⟨1806⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat ee.calldata.size, ⟨413⟩, ⟨276⟩, blindAuctionSelWord ee]
      mem aw rdata acc k C)
    (hvaluesGt : UInt256.gt (revealValuesOffsetWord ee) revealMaxU64 = ⟨0⟩)
    (hvaluesStart :
      UInt256.slt ((⟨4⟩ + revealValuesOffsetWord ee) + ⟨31⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨1⟩)
    (hvaluesLen :
      uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ + revealValuesOffsetWord ee).toNat 32)
        = valuesLen)
    (hvaluesLenMax : UInt256.gt valuesLen revealMaxU64 = ⟨0⟩)
    (hvaluesEnd :
      UInt256.gt (((⟨4⟩ + revealValuesOffsetWord ee) + UInt256.shiftLeft valuesLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat ee.calldata.size) = ⟨0⟩)
    (hfakesGt : UInt256.gt (revealFakesOffsetWord ee) revealMaxU64 = ⟨0⟩)
    (hfakesStart :
      UInt256.slt ((⟨4⟩ + revealFakesOffsetWord ee) + ⟨31⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨1⟩)
    (hfakesLen :
      uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ + revealFakesOffsetWord ee).toNat 32)
        = fakesLen)
    (hfakesLenMax : UInt256.gt fakesLen revealMaxU64 = ⟨0⟩)
    (hfakesEnd :
      UInt256.gt (((⟨4⟩ + revealFakesOffsetWord ee) + UInt256.shiftLeft fakesLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat ee.calldata.size) = ⟨0⟩)
    (hsecretsGt : UInt256.gt (revealSecretsOffsetWord ee) revealMaxU64 = ⟨0⟩)
    (hsecretsStart :
      UInt256.slt ((⟨4⟩ + revealSecretsOffsetWord ee) + ⟨31⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨1⟩)
    (hsecretsLen :
      uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ + revealSecretsOffsetWord ee).toNat 32)
        = secretsLen)
    (hsecretsLenMax : UInt256.gt secretsLen revealMaxU64 = ⟨0⟩)
    (hsecretsEnd :
      UInt256.gt (((⟨4⟩ + revealSecretsOffsetWord ee) + UInt256.shiftLeft secretsLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat ee.calldata.size) = ⟨0⟩) :
    ∃ k' C', RD blindAuctionBytecode ee g s0 ⟨887⟩
      (revealDecodedStack ee valuesLen ((⟨4⟩ + revealValuesOffsetWord ee) + ⟨32⟩)
        fakesLen ((⟨4⟩ + revealFakesOffsetWord ee) + ⟨32⟩)
        secretsLen ((⟨4⟩ + revealSecretsOffsetWord ee) + ⟨32⟩))
      mem aw rdata acc k' C' := by
  obtain ⟨_, _, rd413⟩ :=
    blindAuctionRevealDecodeArrays1806_to_413 rd hvaluesGt hvaluesStart hvaluesLen
      hvaluesLenMax hvaluesEnd hfakesGt hfakesStart hfakesLen hfakesLenMax hfakesEnd
      hsecretsGt hsecretsStart hsecretsLen hsecretsLenMax hsecretsEnd
  have rd887 := evm_run rd413 with [jumpdest, push2 ⟨887⟩, jump (by jump_dest)]
  exact ⟨_, _, by simpa [revealDecodedStack] using rd887⟩

noncomputable def revealScratchBidsSourceMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (UInt256.ofNat I.source.val)).write 0 solcFreePtrMem 0 32

noncomputable def revealScratchBidsHashMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (⟨4⟩ : UInt256)).write 0 (revealScratchBidsSourceMem I) 32 32

theorem revealScratch_readWithPadding_zero (mem : ByteArray) (addr : ℕ) :
    mem.readWithPadding addr 0 = ByteArray.empty := by
  unfold ByteArray.readWithPadding ByteArray.readWithoutPadding
  by_cases h : addr ≥ mem.size
  · simp [h]
    exact zeroes_zero (n := (OfNat.ofNat 0 : USize)) (by rfl)
  · simp [h]
    exact zeroes_zero (n := (OfNat.ofNat 0 : USize)) (by rfl)

theorem revealScratch_write_len_zero (src base : ByteArray) (sa da : ℕ) :
    src.write sa base da 0 = base := by
  unfold ByteArray.write
  simp

theorem revealScratchBidsSourceMem_size (I : ExecutionEnv) :
    (revealScratchBidsSourceMem I).size = 96 := by
  unfold revealScratchBidsSourceMem
  rw [write32_eq _ _ 0 (by rw [toByteArray_size]) (by omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, solcFreePtrMem_size, toByteArray_size]
  norm_num

theorem revealScratchBidsSourceMem_read0 (I : ExecutionEnv) :
    (revealScratchBidsSourceMem I).readWithPadding 0 32 =
      UInt256.toByteArray (UInt256.ofNat I.source.val) := by
  unfold revealScratchBidsSourceMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [solcFreePtrMem_size]; omega),
    show (UInt256.toByteArray (UInt256.ofNat I.source.val)).extract 0 32 =
      UInt256.toByteArray (UInt256.ofNat I.source.val) from by
        apply ByteArray.ext
        rw [ByteArray.data_extract]
        exact Array.extract_eq_self_of_le (by
          change (UInt256.toByteArray (UInt256.ofNat I.source.val)).size ≤ 32
          rw [toByteArray_size])]

theorem revealScratchBidsHashMem_size (I : ExecutionEnv) :
    (revealScratchBidsHashMem I).size = 96 := by
  unfold revealScratchBidsHashMem
  rw [write32_eq _ _ 32 (by rw [toByteArray_size])
      (by rw [revealScratchBidsSourceMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, revealScratchBidsSourceMem_size,
    toByteArray_size]
  norm_num

theorem revealScratchBidsHashMem_read0 (I : ExecutionEnv) :
    (revealScratchBidsHashMem I).readWithPadding 0 32 =
      UInt256.toByteArray (UInt256.ofNat I.source.val) := by
  unfold revealScratchBidsHashMem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [revealScratchBidsSourceMem_size]; omega) (by omega)]
  unfold revealScratchBidsSourceMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [solcFreePtrMem_size]; omega),
    show (UInt256.toByteArray (UInt256.ofNat I.source.val)).extract 0 32 =
      UInt256.toByteArray (UInt256.ofNat I.source.val) from by
        apply ByteArray.ext
        rw [ByteArray.data_extract]
        exact Array.extract_eq_self_of_le (by
          change (UInt256.toByteArray (UInt256.ofNat I.source.val)).size ≤ 32
          rw [toByteArray_size])]

theorem revealScratchBidsHashMem_read32 (I : ExecutionEnv) :
    (revealScratchBidsHashMem I).readWithPadding 32 32 =
      UInt256.toByteArray (⟨4⟩ : UInt256) := by
  unfold revealScratchBidsHashMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [revealScratchBidsSourceMem_size]; omega),
    show (UInt256.toByteArray (⟨4⟩ : UInt256)).extract 0 32 =
      UInt256.toByteArray (⟨4⟩ : UInt256) from by
        apply ByteArray.ext
        rw [ByteArray.data_extract]
        exact Array.extract_eq_self_of_le (by
          change (UInt256.toByteArray (⟨4⟩ : UInt256)).size ≤ 32
          rw [toByteArray_size])]

theorem revealScratchBidsHashMem_read64 (I : ExecutionEnv) :
    (revealScratchBidsHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold revealScratchBidsHashMem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [revealScratchBidsSourceMem_size]; norm_num) (by omega)
      (by rw [revealScratchBidsSourceMem_size])]
  unfold revealScratchBidsSourceMem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by rw [solcFreePtrMem_size]; norm_num) (by omega)
      (by rw [solcFreePtrMem_size])]
  exact solcFreePtrMem_read64

theorem revealScratchBidsHashMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (revealScratchBidsHashMem I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((revealScratchBidsHashMem I).readWithPadding
         (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
  mloadFreePtrValue (by rw [revealScratchBidsHashMem_size]; decide) (by decide)
    (revealScratchBidsHashMem_read64 I)

theorem revealScratchBidsHashMem_read0_64 (I : ExecutionEnv) :
    (revealScratchBidsHashMem I).readWithPadding 0 64 =
      UInt256.toByteArray (UInt256.ofNat I.source.val) ++
        UInt256.toByteArray (⟨4⟩ : UInt256) := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
    (by rw [revealScratchBidsHashMem_size]; omega)]
  rw [show 0 + 64 = 64 by norm_num]
  unfold revealScratchBidsHashMem
  rw [write32_eq _ _ 32 (by rw [toByteArray_size])
      (by rw [revealScratchBidsSourceMem_size]; omega)]
  have hsource :
      (revealScratchBidsSourceMem I).extract 0 32 =
        UInt256.toByteArray (UInt256.ofNat I.source.val) := by
    rw [← readWithPadding_eq_extract (revealScratchBidsSourceMem I) 0
      (by rw [revealScratchBidsSourceMem_size]; omega)]
    exact revealScratchBidsSourceMem_read0 I
  have hslot :
      (UInt256.toByteArray (⟨4⟩ : UInt256)).extract 0 32 =
        UInt256.toByteArray (⟨4⟩ : UInt256) := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray (⟨4⟩ : UInt256)).size ≤ 32
      rw [toByteArray_size])
  rw [hsource, hslot]
  rw [extract_append_left
      (UInt256.toByteArray (UInt256.ofNat I.source.val) ++
        UInt256.toByteArray (⟨4⟩ : UInt256))
      ((revealScratchBidsSourceMem I).extract (32 + 32) (revealScratchBidsSourceMem I).size)
      0 64 (by rw [ByteArray.size_append, toByteArray_size, toByteArray_size])]
  rw [extract_append_span (UInt256.toByteArray (UInt256.ofNat I.source.val))
      (UInt256.toByteArray (⟨4⟩ : UInt256)) 0 64
      (by rw [toByteArray_size]; omega)
      (by rw [toByteArray_size]; omega)]
  rw [show (UInt256.toByteArray (UInt256.ofNat I.source.val)).extract 0
      (UInt256.toByteArray (UInt256.ofNat I.source.val)).size =
        UInt256.toByteArray (UInt256.ofNat I.source.val) by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      show (UInt256.toByteArray (UInt256.ofNat I.source.val)).data.size ≤
        (UInt256.toByteArray (UInt256.ofNat I.source.val)).size
      rfl)]
  rw [show 64 - (UInt256.toByteArray (UInt256.ofNat I.source.val)).size = 32 by
    rw [toByteArray_size]]
  rw [hslot]

theorem revealScratchKeyValueToWord_address_source (I : ExecutionEnv) :
    keyValueToWord (.address I.source) = UInt256.ofNat I.source.val := by
  apply u256_inj
  unfold keyValueToWord UInt256.ofNat
  change I.source.val = (Fin.ofNat UInt256.size I.source.val).val
  rw [Fin.val_ofNat]
  exact (Nat.mod_eq_of_lt
    (lt_of_lt_of_le I.source.isLt (show AccountAddress.size ≤ UInt256.size from by decide))).symm

theorem revealScratchBidsMappingBaseKeccak (I : ExecutionEnv) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
      revealScratchBidsLengthSlot I := by
  rw [revealScratchBidsHashMem_read0_64]
  unfold revealScratchBidsLengthSlot bidsBase blindAuctionMappingSlot
  rw [revealScratchKeyValueToWord_address_source]
  exact keccakSlot_eq _

def revealScratchStTimestamp (s : State) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩,
      stack := UInt256.ofNat s.executionEnv.header.timestamp :: s.machineState.stack,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable.subNat 2 } }

theorem revealScratchTimestamp_xstep {s : State} {code : ByteArray} {pcv : UInt256}
    {rest : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.TIMESTAMP, .none))
    (hstk : s.machineState.stack = rest) (hov : rest.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s =
      (if s.machineState.gasAvailable.toNat < 2 then .error .OutOfGass
       else .ok (revealScratchStTimestamp s, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.TIMESTAMP, .none) := by
    rw [hcode, hpc]
    exact hdec
  have hov' : ¬ (s.machineState.stack.length - 0 + 1 > 1024) := by
    rw [hstk]
    omega
  rw [← hcode, step_timestamp s hd, if_neg hov']
  simp only [GasConstants.Gbase, revealScratchStTimestamp]

theorem RD.revealScratchTimestamp {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD code ee g s0 pc stk mem aw rdata acc k C)
    (hdec : decode code pc = some (.TIMESTAMP, .none)) (hov : stk.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.ofNat ee.header.timestamp :: stk) mem aw rdata acc
      (k + 1) (C + 2) := by
  unfold RD at rd ⊢
  rcases rd with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee,
      hworld⟩
  · exact Or.inl hoog
  · have st := revealScratchTimestamp_xstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 2
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨revealScratchStTimestamp s,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega,
        by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [revealScratchStTimestamp]
        exact hcode
      · simp only [revealScratchStTimestamp]
        rw [hpc]
      · simp only [revealScratchStTimestamp]
        rw [hstk, hee]
      · simp only [revealScratchStTimestamp]
        rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [revealScratchStTimestamp]
        exact hmem
      · simp only [revealScratchStTimestamp]
        exact haw
      · simp only [revealScratchStTimestamp]
        exact hrdata
      · simp only [revealScratchStTimestamp]
        exact hacc
      · simp only [revealScratchStTimestamp]
        exact hee
      · simp only [revealScratchStTimestamp]
        exact hworld

noncomputable def revealTimeRevertMem (arg errSel : UInt256) : ByteArray :=
  (UInt256.toByteArray arg).write 0 (solcReturnMem errSel) 132 32

theorem revealTimeRevertMem_size (arg errSel : UInt256) :
    (revealTimeRevertMem arg errSel).size = 164 := by
  unfold revealTimeRevertMem
  rw [write32_eq _ _ 132 (by rw [toByteArray_size])
      (by rw [solcReturnMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, solcReturnMem_size, toByteArray_size]
  rw [show ((solcReturnMem errSel).extract (132 + 32) 160).size = 0 by
    rw [ByteArray.size_extract, solcReturnMem_size]
    norm_num]
  omega

theorem revealTimeRevertMem_mload64 (arg errSel : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (revealTimeRevertMem arg errSel).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((revealTimeRevertMem arg errSel).readWithPadding
         (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
  mloadFreePtrValue (by rw [revealTimeRevertMem_size]; decide) (by decide) (by
    unfold revealTimeRevertMem
    rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
      (by rw [solcReturnMem_size]; omega) (by omega)]
    exact solcReturnMem_read64 errSel)

theorem blindAuctionRevealX_from887_tooEarly {cA σ I} {g : Sat256}
    {s0 : State} {k C : ℕ} {valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨887⟩
      (revealDecodedStack I valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (htime :
      (revealScratchTimestampWord I).toNat ≤
        (revealScratchBiddingEndWord σ I).toNat) :
    RDrev blindAuctionBytecode g s0 := by
  have rd890 := evm_run rd with [jumpdest, push1 ⟨1⟩]
  obtain ⟨_, _, rd891₀⟩ := rd890.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd891⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨891⟩
      [revealScratchBiddingEndWord σ I, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [revealScratchBiddingEndWord, revealDecodedStack] using rd891₀⟩
  have hgt : UInt256.gt (revealScratchTimestampWord I)
      (revealScratchBiddingEndWord σ I) = ⟨0⟩ :=
    ugt_zero htime
  have rd893₀ := RD.revealScratchTimestamp (evm_run rd891 with [dup1]) (by decide) (by evm_ov)
  have rd894₀ := evm_run rd893₀ with [gt]
  have rd894 := rd894₀
  rw [show UInt256.gt (UInt256.ofNat I.header.timestamp) (revealScratchBiddingEndWord σ I) =
      ⟨0⟩ from by simpa [revealScratchTimestampWord] using hgt] at rd894
  have rd898 := evm_run rd894 with [push2 ⟨925⟩, jumpiNT (by decide)]
  let errSel : UInt256 := UInt256.shiftLeft (⟨0x0a8d68c9⟩ : UInt256) ⟨226⟩
  have rd911 := evm_run rd898 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push4 ⟨0x0a8d68c9⟩, push1 ⟨226⟩, shl, dup2,
    raw mstore 6 (solcReturnMem errSel) (UInt256.ofNat 5) (by decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov)]
  have rd600 := evm_run rd911 with [
    push1 ⟨4⟩, dup2, add, dup3, swap1,
    raw mstore 3 (revealTimeRevertMem (revealScratchBiddingEndWord σ I) errSel)
      (UInt256.ofNat 6) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨36⟩, add, push2 ⟨600⟩, jump (by jump_dest)]
  have rd608 := evm_run rd600 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (revealTimeRevertMem_mload64 (revealScratchBiddingEndWord σ I) errSel)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  exact rd608.rev 0 (by decide) mem_cost (by evm_ov)

theorem blindAuctionRevealX_from887_tooLate {cA σ I} {g : Sat256}
    {s0 : State} {k C : ℕ} {valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨887⟩
      (revealDecodedStack I valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hafter :
      (revealScratchBiddingEndWord σ I).toNat < (revealScratchTimestampWord I).toNat)
    (htime :
      (revealScratchRevealEndWord σ I).toNat ≤
        (revealScratchTimestampWord I).toNat) :
    RDrev blindAuctionBytecode g s0 := by
  have rd890 := evm_run rd with [jumpdest, push1 ⟨1⟩]
  obtain ⟨_, _, rd891₀⟩ := rd890.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd891⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨891⟩
      [revealScratchBiddingEndWord σ I, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [revealScratchBiddingEndWord, revealDecodedStack] using rd891₀⟩
  have hgt : UInt256.gt (revealScratchTimestampWord I)
      (revealScratchBiddingEndWord σ I) = ⟨1⟩ :=
    ugt_one hafter
  have rd893₀ := RD.revealScratchTimestamp (evm_run rd891 with [dup1]) (by decide) (by evm_ov)
  have rd894₀ := evm_run rd893₀ with [gt]
  have rd894 := rd894₀
  rw [show UInt256.gt (UInt256.ofNat I.header.timestamp) (revealScratchBiddingEndWord σ I) =
      ⟨1⟩ from by simpa [revealScratchTimestampWord] using hgt] at rd894
  have rd925 := evm_run rd894 with [push2 ⟨925⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have rd928 := evm_run rd925 with [jumpdest, push1 ⟨2⟩]
  obtain ⟨_, _, rd929₀⟩ := rd928.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd929⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨929⟩
      [revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd,
        ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [revealScratchRevealEndWord] using rd929₀⟩
  have hlt : UInt256.lt (revealScratchTimestampWord I)
      (revealScratchRevealEndWord σ I) = ⟨0⟩ :=
    ult_zero htime
  have rd931₀ := RD.revealScratchTimestamp (evm_run rd929 with [dup1]) (by decide) (by evm_ov)
  have rd932₀ := evm_run rd931₀ with [lt]
  have rd932 := rd932₀
  rw [show UInt256.lt (UInt256.ofNat I.header.timestamp) (revealScratchRevealEndWord σ I) =
      ⟨0⟩ from by simpa [revealScratchTimestampWord] using hlt] at rd932
  have rd936 := evm_run rd932 with [push2 ⟨963⟩, jumpiNT (by decide)]
  let errSel : UInt256 := UInt256.shiftLeft (⟨0x348f2b41⟩ : UInt256) ⟨225⟩
  have rd949 := evm_run rd936 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push4 ⟨0x348f2b41⟩, push1 ⟨225⟩, shl, dup2,
    raw mstore 6 (solcReturnMem errSel) (UInt256.ofNat 5) (by decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov)]
  have rd600 := evm_run rd949 with [
    push1 ⟨4⟩, dup2, add, dup3, swap1,
    raw mstore 3 (revealTimeRevertMem (revealScratchRevealEndWord σ I) errSel)
      (UInt256.ofNat 6) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨36⟩, add, push2 ⟨600⟩, jump (by jump_dest)]
  have rd608 := evm_run rd600 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (revealTimeRevertMem_mload64 (revealScratchRevealEndWord σ I) errSel)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  exact rd608.rev 0 (by decide) mem_cost (by evm_ov)

theorem blindAuctionRevealX_from887_afterTimeGuards_empty {cA σ I} {g : Sat256}
    {s0 : State} {k C : ℕ} {valuesEnd fakesEnd secretsEnd : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨887⟩
      (revealScratchEmptyDecodedStack I valuesEnd fakesEnd secretsEnd) solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hafter :
      (revealScratchBiddingEndWord σ I).toNat < (revealScratchTimestampWord I).toNat)
    (hbefore :
      (revealScratchTimestampWord I).toNat < (revealScratchRevealEndWord σ I).toNat) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨963⟩
      [revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I,
        ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd890 := evm_run rd with [jumpdest, push1 ⟨1⟩]
  obtain ⟨_, _, rd891₀⟩ := rd890.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd891⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨891⟩
      [revealScratchBiddingEndWord σ I, ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd,
        ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [revealScratchBiddingEndWord,
      revealScratchEmptyDecodedStack] using rd891₀⟩
  have hgt : UInt256.gt (revealScratchTimestampWord I) (revealScratchBiddingEndWord σ I) = ⟨1⟩ :=
    ugt_one hafter
  have rd893₀ := RD.revealScratchTimestamp (evm_run rd891 with [dup1]) (by decide) (by evm_ov)
  have rd894₀ := evm_run rd893₀ with [gt]
  have rd894 := rd894₀
  rw [show UInt256.gt (UInt256.ofNat I.header.timestamp) (revealScratchBiddingEndWord σ I) =
      ⟨1⟩ from by simpa [revealScratchTimestampWord] using hgt] at rd894
  have rd925 := evm_run rd894 with [push2 ⟨925⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have rd928 := evm_run rd925 with [jumpdest, push1 ⟨2⟩]
  obtain ⟨_, _, rd929₀⟩ := rd928.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd929⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨929⟩
      [revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I,
        ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [revealScratchRevealEndWord] using rd929₀⟩
  have hlt : UInt256.lt (revealScratchTimestampWord I) (revealScratchRevealEndWord σ I) = ⟨1⟩ :=
    ult_one hbefore
  have rd931₀ := RD.revealScratchTimestamp (evm_run rd929 with [dup1]) (by decide) (by evm_ov)
  have rd932₀ := evm_run rd931₀ with [lt]
  have rd932 := rd932₀
  rw [show UInt256.lt (UInt256.ofNat I.header.timestamp) (revealScratchRevealEndWord σ I) =
      ⟨1⟩ from by simpa [revealScratchTimestampWord] using hlt] at rd932
  exact ⟨_, _, evm_run rd932 with [push2 ⟨963⟩, jumpiT one_ne_zero_uint (by jump_dest)]⟩

theorem blindAuctionRevealX_from887_lengthMismatch_empty {cA σ I} {g : Sat256}
    {s0 : State} {k C : ℕ} {valuesEnd fakesEnd secretsEnd : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨887⟩
      (revealScratchEmptyDecodedStack I valuesEnd fakesEnd secretsEnd) solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hafter :
      (revealScratchBiddingEndWord σ I).toNat < (revealScratchTimestampWord I).toNat)
    (hbefore :
      (revealScratchTimestampWord I).toNat < (revealScratchRevealEndWord σ I).toNat)
    (hbidsNonzero : revealScratchBidsLengthWord σ I ≠ ⟨0⟩)
    (hbidsHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
          revealScratchBidsLengthSlot I) :
    RDrev blindAuctionBytecode g s0 := by
  obtain ⟨_, _, rd963⟩ :=
    blindAuctionRevealX_from887_afterTimeGuards_empty (cA := cA) (σ := σ) (I := I)
      (g := g) (s0 := s0) rd hafter hbefore
  have rd968 := evm_run rd963 with [jumpdest, caller, push0, swap1, dup2]
  have rd969 := evm_run rd968 with [
    raw mstore 0 (revealScratchBidsSourceMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd978 := evm_run rd969 with [
    push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0 (revealScratchBidsHashMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1,
    raw keccak256 0 (revealScratchBidsLengthSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost hbidsHash (by decide) (by evm_ov)]
  obtain ⟨_, _, rd979₀⟩ := rd978.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd979⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨979⟩
      [revealScratchBidsLengthWord σ I, revealScratchRevealEndWord σ I,
        revealScratchBiddingEndWord σ I, ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩,
        valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      (revealScratchBidsHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [revealScratchBidsLengthWord,
      revealScratchBidsLengthSlot] using rd979₀⟩
  have heq0 : UInt256.eq (revealScratchBidsLengthWord σ I) (⟨0⟩ : UInt256) = ⟨0⟩ :=
    u256_eq_of_ne hbidsNonzero
  have rd982₀ := evm_run rd979 with [dup8, dup2, eq]
  have rd982 := rd982₀
  rw [heq0] at rd982
  have rd988 := evm_run rd982 with [push2 ⟨989⟩, jumpiNT (by decide), push0, push0]
  exact RD.rev _ rd988 (by decide)
    (fun s haws hstks => by rw [memExpRevertZeroOff s hstks, haws])
    (by evm_ov)

theorem blindAuctionRevealX_from887_afterTimeGuards {cA σ I} {g : Sat256}
    {s0 : State} {k C : ℕ} {valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨887⟩
      (revealDecodedStack I valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hafter :
      (revealScratchBiddingEndWord σ I).toNat < (revealScratchTimestampWord I).toNat)
    (hbefore :
      (revealScratchTimestampWord I).toNat < (revealScratchRevealEndWord σ I).toNat) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨963⟩
      [revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd,
        ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd890 := evm_run rd with [jumpdest, push1 ⟨1⟩]
  obtain ⟨_, _, rd891₀⟩ := rd890.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd891⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨891⟩
      [revealScratchBiddingEndWord σ I, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [revealScratchBiddingEndWord, revealDecodedStack] using rd891₀⟩
  have hgt : UInt256.gt (revealScratchTimestampWord I) (revealScratchBiddingEndWord σ I) = ⟨1⟩ :=
    ugt_one hafter
  have rd893₀ := RD.revealScratchTimestamp (evm_run rd891 with [dup1]) (by decide) (by evm_ov)
  have rd894₀ := evm_run rd893₀ with [gt]
  have rd894 := rd894₀
  rw [show UInt256.gt (UInt256.ofNat I.header.timestamp) (revealScratchBiddingEndWord σ I) =
      ⟨1⟩ from by simpa [revealScratchTimestampWord] using hgt] at rd894
  have rd925 := evm_run rd894 with [push2 ⟨925⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have rd928 := evm_run rd925 with [jumpdest, push1 ⟨2⟩]
  obtain ⟨_, _, rd929₀⟩ := rd928.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd929⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨929⟩
      [revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd,
        ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [revealScratchRevealEndWord] using rd929₀⟩
  have hlt : UInt256.lt (revealScratchTimestampWord I) (revealScratchRevealEndWord σ I) = ⟨1⟩ :=
    ult_one hbefore
  have rd931₀ := RD.revealScratchTimestamp (evm_run rd929 with [dup1]) (by decide) (by evm_ov)
  have rd932₀ := evm_run rd931₀ with [lt]
  have rd932 := rd932₀
  rw [show UInt256.lt (UInt256.ofNat I.header.timestamp) (revealScratchRevealEndWord σ I) =
      ⟨1⟩ from by simpa [revealScratchTimestampWord] using hlt] at rd932
  exact ⟨_, _, evm_run rd932 with [push2 ⟨963⟩, jumpiT one_ne_zero_uint (by jump_dest)]⟩

theorem blindAuctionRevealX_from887_valuesLengthMismatch {cA σ I} {g : Sat256}
    {s0 : State} {k C : ℕ} {valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨887⟩
      (revealDecodedStack I valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hafter :
      (revealScratchBiddingEndWord σ I).toNat < (revealScratchTimestampWord I).toNat)
    (hbefore :
      (revealScratchTimestampWord I).toNat < (revealScratchRevealEndWord σ I).toNat)
    (hvaluesNe : revealScratchBidsLengthWord σ I ≠ valuesLen)
    (hbidsHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
          revealScratchBidsLengthSlot I) :
    RDrev blindAuctionBytecode g s0 := by
  obtain ⟨_, _, rd963⟩ :=
    blindAuctionRevealX_from887_afterTimeGuards (cA := cA) (σ := σ) (I := I)
      (g := g) (s0 := s0) rd hafter hbefore
  have rd968 := evm_run rd963 with [jumpdest, caller, push0, swap1, dup2]
  have rd969 := evm_run rd968 with [
    raw mstore 0 (revealScratchBidsSourceMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd978 := evm_run rd969 with [
    push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0 (revealScratchBidsHashMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1,
    raw keccak256 0 (revealScratchBidsLengthSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost hbidsHash (by decide) (by evm_ov)]
  obtain ⟨_, _, rd979₀⟩ := rd978.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd979⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨979⟩
      [revealScratchBidsLengthWord σ I, revealScratchRevealEndWord σ I,
        revealScratchBiddingEndWord σ I, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      (revealScratchBidsHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [revealScratchBidsLengthWord,
      revealScratchBidsLengthSlot] using rd979₀⟩
  have heq0 : UInt256.eq (revealScratchBidsLengthWord σ I) valuesLen = ⟨0⟩ :=
    u256_eq_of_ne hvaluesNe
  have rd982₀ := evm_run rd979 with [dup8, dup2, eq]
  have rd982 := rd982₀
  rw [heq0] at rd982
  have rd988 := evm_run rd982 with [push2 ⟨989⟩, jumpiNT (by decide), push0, push0]
  exact RD.rev _ rd988 (by decide)
    (fun s haws hstks => by rw [memExpRevertZeroOff s hstks, haws])
    (by evm_ov)

theorem blindAuctionRevealX_from887_fakesLengthMismatch {cA σ I} {g : Sat256}
    {s0 : State} {k C : ℕ} {valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨887⟩
      (revealDecodedStack I valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hafter :
      (revealScratchBiddingEndWord σ I).toNat < (revealScratchTimestampWord I).toNat)
    (hbefore :
      (revealScratchTimestampWord I).toNat < (revealScratchRevealEndWord σ I).toNat)
    (hvaluesEq : revealScratchBidsLengthWord σ I = valuesLen)
    (hfakesNe : revealScratchBidsLengthWord σ I ≠ fakesLen)
    (hbidsHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
          revealScratchBidsLengthSlot I) :
    RDrev blindAuctionBytecode g s0 := by
  obtain ⟨_, _, rd963⟩ :=
    blindAuctionRevealX_from887_afterTimeGuards (cA := cA) (σ := σ) (I := I)
      (g := g) (s0 := s0) rd hafter hbefore
  have rd968 := evm_run rd963 with [jumpdest, caller, push0, swap1, dup2]
  have rd969 := evm_run rd968 with [
    raw mstore 0 (revealScratchBidsSourceMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd978 := evm_run rd969 with [
    push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0 (revealScratchBidsHashMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1,
    raw keccak256 0 (revealScratchBidsLengthSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost hbidsHash (by decide) (by evm_ov)]
  obtain ⟨_, _, rd979₀⟩ := rd978.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd979⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨979⟩
      [revealScratchBidsLengthWord σ I, revealScratchRevealEndWord σ I,
        revealScratchBiddingEndWord σ I, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      (revealScratchBidsHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [revealScratchBidsLengthWord,
      revealScratchBidsLengthSlot] using rd979₀⟩
  have heqValues :
      UInt256.eq (revealScratchBidsLengthWord σ I) valuesLen = ⟨1⟩ := by
    rw [← hvaluesEq]
    exact u256_eq_refl _
  have rd982₀ := evm_run rd979 with [dup8, dup2, eq]
  have rd982 := rd982₀
  rw [heqValues] at rd982
  have rd989 := evm_run rd982 with [push2 ⟨989⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have heqFakes : UInt256.eq (revealScratchBidsLengthWord σ I) fakesLen = ⟨0⟩ :=
    u256_eq_of_ne hfakesNe
  have rd993₀ := evm_run rd989 with [jumpdest, dup6, dup2, eq]
  have rd993 := rd993₀
  rw [heqFakes] at rd993
  have rd999 := evm_run rd993 with [push2 ⟨1000⟩, jumpiNT (by decide), push0, push0]
  exact RD.rev _ rd999 (by decide)
    (fun s haws hstks => by rw [memExpRevertZeroOff s hstks, haws])
    (by evm_ov)

theorem blindAuctionRevealX_from887_secretsLengthMismatch {cA σ I} {g : Sat256}
    {s0 : State} {k C : ℕ} {valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨887⟩
      (revealDecodedStack I valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hafter :
      (revealScratchBiddingEndWord σ I).toNat < (revealScratchTimestampWord I).toNat)
    (hbefore :
      (revealScratchTimestampWord I).toNat < (revealScratchRevealEndWord σ I).toNat)
    (hvaluesEq : revealScratchBidsLengthWord σ I = valuesLen)
    (hfakesEq : revealScratchBidsLengthWord σ I = fakesLen)
    (hsecretsNe : revealScratchBidsLengthWord σ I ≠ secretsLen)
    (hbidsHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
          revealScratchBidsLengthSlot I) :
    RDrev blindAuctionBytecode g s0 := by
  obtain ⟨_, _, rd963⟩ :=
    blindAuctionRevealX_from887_afterTimeGuards (cA := cA) (σ := σ) (I := I)
      (g := g) (s0 := s0) rd hafter hbefore
  have rd968 := evm_run rd963 with [jumpdest, caller, push0, swap1, dup2]
  have rd969 := evm_run rd968 with [
    raw mstore 0 (revealScratchBidsSourceMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd978 := evm_run rd969 with [
    push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0 (revealScratchBidsHashMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1,
    raw keccak256 0 (revealScratchBidsLengthSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost hbidsHash (by decide) (by evm_ov)]
  obtain ⟨_, _, rd979₀⟩ := rd978.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd979⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨979⟩
      [revealScratchBidsLengthWord σ I, revealScratchRevealEndWord σ I,
        revealScratchBiddingEndWord σ I, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      (revealScratchBidsHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [revealScratchBidsLengthWord,
      revealScratchBidsLengthSlot] using rd979₀⟩
  have heqValues :
      UInt256.eq (revealScratchBidsLengthWord σ I) valuesLen = ⟨1⟩ := by
    rw [← hvaluesEq]
    exact u256_eq_refl _
  have rd982₀ := evm_run rd979 with [dup8, dup2, eq]
  have rd982 := rd982₀
  rw [heqValues] at rd982
  have rd989 := evm_run rd982 with [push2 ⟨989⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have heqFakes :
      UInt256.eq (revealScratchBidsLengthWord σ I) fakesLen = ⟨1⟩ := by
    rw [← hfakesEq]
    exact u256_eq_refl _
  have rd993₀ := evm_run rd989 with [jumpdest, dup6, dup2, eq]
  have rd993 := rd993₀
  rw [heqFakes] at rd993
  have rd1000 := evm_run rd993 with [push2 ⟨1000⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have heqSecrets : UInt256.eq (revealScratchBidsLengthWord σ I) secretsLen = ⟨0⟩ :=
    u256_eq_of_ne hsecretsNe
  have rd1004₀ := evm_run rd1000 with [jumpdest, dup4, dup2, eq]
  have rd1004 := rd1004₀
  rw [heqSecrets] at rd1004
  have rd1010 := evm_run rd1004 with [push2 ⟨1011⟩, jumpiNT (by decide), push0, push0]
  exact RD.rev _ rd1010 (by decide)
    (fun s haws hstks => by rw [memExpRevertZeroOff s hstks, haws])
    (by evm_ov)

theorem blindAuctionRevealDecodeArrays1806_valuesLengthMismatch_reverts
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {I : ExecutionEnv}
    {g : Sat256}
    {s0 : State} {k C : Nat}
    {valuesLen fakesLen secretsLen : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1806⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨413⟩, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hvaluesGt : UInt256.gt (revealValuesOffsetWord I) revealMaxU64 = ⟨0⟩)
    (hvaluesStart :
      UInt256.slt ((⟨4⟩ + revealValuesOffsetWord I) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hvaluesLen :
      uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + revealValuesOffsetWord I).toNat 32)
        = valuesLen)
    (hvaluesLenMax : UInt256.gt valuesLen revealMaxU64 = ⟨0⟩)
    (hvaluesEnd :
      UInt256.gt (((⟨4⟩ + revealValuesOffsetWord I) + UInt256.shiftLeft valuesLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hfakesGt : UInt256.gt (revealFakesOffsetWord I) revealMaxU64 = ⟨0⟩)
    (hfakesStart :
      UInt256.slt ((⟨4⟩ + revealFakesOffsetWord I) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hfakesLen :
      uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + revealFakesOffsetWord I).toNat 32)
        = fakesLen)
    (hfakesLenMax : UInt256.gt fakesLen revealMaxU64 = ⟨0⟩)
    (hfakesEnd :
      UInt256.gt (((⟨4⟩ + revealFakesOffsetWord I) + UInt256.shiftLeft fakesLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hsecretsGt : UInt256.gt (revealSecretsOffsetWord I) revealMaxU64 = ⟨0⟩)
    (hsecretsStart :
      UInt256.slt ((⟨4⟩ + revealSecretsOffsetWord I) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hsecretsLen :
      uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + revealSecretsOffsetWord I).toNat 32)
        = secretsLen)
    (hsecretsLenMax : UInt256.gt secretsLen revealMaxU64 = ⟨0⟩)
    (hsecretsEnd :
      UInt256.gt (((⟨4⟩ + revealSecretsOffsetWord I) + UInt256.shiftLeft secretsLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hafter :
      (revealScratchBiddingEndWord σ I).toNat < (revealScratchTimestampWord I).toNat)
    (hbefore :
      (revealScratchTimestampWord I).toNat < (revealScratchRevealEndWord σ I).toNat)
    (hvaluesNe : revealScratchBidsLengthWord σ I ≠ valuesLen)
    (hbidsHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
          revealScratchBidsLengthSlot I) :
    RDrev blindAuctionBytecode g s0 := by
  obtain ⟨_, _, rd887⟩ :=
    blindAuctionRevealDecodeArrays1806_to_887 (ee := I) rd hvaluesGt hvaluesStart
      hvaluesLen hvaluesLenMax hvaluesEnd hfakesGt hfakesStart hfakesLen hfakesLenMax
      hfakesEnd hsecretsGt hsecretsStart hsecretsLen hsecretsLenMax hsecretsEnd
  exact blindAuctionRevealX_from887_valuesLengthMismatch (cA := cA) (σ := σ) (I := I)
    (g := g) (s0 := s0) rd887 hafter hbefore hvaluesNe hbidsHash

theorem blindAuctionRevealDecodeArrays1806_fakesLengthMismatch_reverts
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {I : ExecutionEnv}
    {g : Sat256}
    {s0 : State} {k C : Nat}
    {valuesLen fakesLen secretsLen : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1806⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨413⟩, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hvaluesGt : UInt256.gt (revealValuesOffsetWord I) revealMaxU64 = ⟨0⟩)
    (hvaluesStart :
      UInt256.slt ((⟨4⟩ + revealValuesOffsetWord I) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hvaluesLen :
      uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + revealValuesOffsetWord I).toNat 32)
        = valuesLen)
    (hvaluesLenMax : UInt256.gt valuesLen revealMaxU64 = ⟨0⟩)
    (hvaluesEnd :
      UInt256.gt (((⟨4⟩ + revealValuesOffsetWord I) + UInt256.shiftLeft valuesLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hfakesGt : UInt256.gt (revealFakesOffsetWord I) revealMaxU64 = ⟨0⟩)
    (hfakesStart :
      UInt256.slt ((⟨4⟩ + revealFakesOffsetWord I) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hfakesLen :
      uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + revealFakesOffsetWord I).toNat 32)
        = fakesLen)
    (hfakesLenMax : UInt256.gt fakesLen revealMaxU64 = ⟨0⟩)
    (hfakesEnd :
      UInt256.gt (((⟨4⟩ + revealFakesOffsetWord I) + UInt256.shiftLeft fakesLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hsecretsGt : UInt256.gt (revealSecretsOffsetWord I) revealMaxU64 = ⟨0⟩)
    (hsecretsStart :
      UInt256.slt ((⟨4⟩ + revealSecretsOffsetWord I) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hsecretsLen :
      uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + revealSecretsOffsetWord I).toNat 32)
        = secretsLen)
    (hsecretsLenMax : UInt256.gt secretsLen revealMaxU64 = ⟨0⟩)
    (hsecretsEnd :
      UInt256.gt (((⟨4⟩ + revealSecretsOffsetWord I) + UInt256.shiftLeft secretsLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hafter :
      (revealScratchBiddingEndWord σ I).toNat < (revealScratchTimestampWord I).toNat)
    (hbefore :
      (revealScratchTimestampWord I).toNat < (revealScratchRevealEndWord σ I).toNat)
    (hvaluesEq : revealScratchBidsLengthWord σ I = valuesLen)
    (hfakesNe : revealScratchBidsLengthWord σ I ≠ fakesLen)
    (hbidsHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
          revealScratchBidsLengthSlot I) :
    RDrev blindAuctionBytecode g s0 := by
  obtain ⟨_, _, rd887⟩ :=
    blindAuctionRevealDecodeArrays1806_to_887 (ee := I) rd hvaluesGt hvaluesStart
      hvaluesLen hvaluesLenMax hvaluesEnd hfakesGt hfakesStart hfakesLen hfakesLenMax
      hfakesEnd hsecretsGt hsecretsStart hsecretsLen hsecretsLenMax hsecretsEnd
  exact blindAuctionRevealX_from887_fakesLengthMismatch (cA := cA) (σ := σ) (I := I)
    (g := g) (s0 := s0) rd887 hafter hbefore hvaluesEq hfakesNe hbidsHash

theorem blindAuctionRevealDecodeArrays1806_secretsLengthMismatch_reverts
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {I : ExecutionEnv}
    {g : Sat256}
    {s0 : State} {k C : Nat}
    {valuesLen fakesLen secretsLen : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1806⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨413⟩, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hvaluesGt : UInt256.gt (revealValuesOffsetWord I) revealMaxU64 = ⟨0⟩)
    (hvaluesStart :
      UInt256.slt ((⟨4⟩ + revealValuesOffsetWord I) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hvaluesLen :
      uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + revealValuesOffsetWord I).toNat 32)
        = valuesLen)
    (hvaluesLenMax : UInt256.gt valuesLen revealMaxU64 = ⟨0⟩)
    (hvaluesEnd :
      UInt256.gt (((⟨4⟩ + revealValuesOffsetWord I) + UInt256.shiftLeft valuesLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hfakesGt : UInt256.gt (revealFakesOffsetWord I) revealMaxU64 = ⟨0⟩)
    (hfakesStart :
      UInt256.slt ((⟨4⟩ + revealFakesOffsetWord I) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hfakesLen :
      uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + revealFakesOffsetWord I).toNat 32)
        = fakesLen)
    (hfakesLenMax : UInt256.gt fakesLen revealMaxU64 = ⟨0⟩)
    (hfakesEnd :
      UInt256.gt (((⟨4⟩ + revealFakesOffsetWord I) + UInt256.shiftLeft fakesLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hsecretsGt : UInt256.gt (revealSecretsOffsetWord I) revealMaxU64 = ⟨0⟩)
    (hsecretsStart :
      UInt256.slt ((⟨4⟩ + revealSecretsOffsetWord I) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hsecretsLen :
      uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + revealSecretsOffsetWord I).toNat 32)
        = secretsLen)
    (hsecretsLenMax : UInt256.gt secretsLen revealMaxU64 = ⟨0⟩)
    (hsecretsEnd :
      UInt256.gt (((⟨4⟩ + revealSecretsOffsetWord I) + UInt256.shiftLeft secretsLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hafter :
      (revealScratchBiddingEndWord σ I).toNat < (revealScratchTimestampWord I).toNat)
    (hbefore :
      (revealScratchTimestampWord I).toNat < (revealScratchRevealEndWord σ I).toNat)
    (hvaluesEq : revealScratchBidsLengthWord σ I = valuesLen)
    (hfakesEq : revealScratchBidsLengthWord σ I = fakesLen)
    (hsecretsNe : revealScratchBidsLengthWord σ I ≠ secretsLen)
    (hbidsHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
          revealScratchBidsLengthSlot I) :
    RDrev blindAuctionBytecode g s0 := by
  obtain ⟨_, _, rd887⟩ :=
    blindAuctionRevealDecodeArrays1806_to_887 (ee := I) rd hvaluesGt hvaluesStart
      hvaluesLen hvaluesLenMax hvaluesEnd hfakesGt hfakesStart hfakesLen hfakesLenMax
      hfakesEnd hsecretsGt hsecretsStart hsecretsLen hsecretsLenMax hsecretsEnd
  exact blindAuctionRevealX_from887_secretsLengthMismatch (cA := cA) (σ := σ) (I := I)
    (g := g) (s0 := s0) rd887 hafter hbefore hvaluesEq hfakesEq hsecretsNe hbidsHash

theorem blindAuctionRevealX_from963_lengthsOk_toLoopInit {cA σ I} {g : Sat256}
    {s0 : State} {k C : ℕ} {valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨963⟩
      [revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd,
        ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hvaluesEq : revealScratchBidsLengthWord σ I = valuesLen)
    (hfakesEq : revealScratchBidsLengthWord σ I = fakesLen)
    (hsecretsEq : revealScratchBidsLengthWord σ I = secretsLen)
    (hbidsHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
          revealScratchBidsLengthSlot I) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1014⟩
      [⟨0⟩, ⟨0⟩, revealScratchBidsLengthWord σ I,
        revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd,
        ⟨276⟩, blindAuctionSelWord I]
      (revealScratchBidsHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd968 := evm_run rd with [jumpdest, caller, push0, swap1, dup2]
  have rd969 := evm_run rd968 with [
    raw mstore 0 (revealScratchBidsSourceMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd978 := evm_run rd969 with [
    push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0 (revealScratchBidsHashMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1,
    raw keccak256 0 (revealScratchBidsLengthSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost hbidsHash (by decide) (by evm_ov)]
  obtain ⟨_, _, rd979₀⟩ := rd978.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd979⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨979⟩
      [revealScratchBidsLengthWord σ I, revealScratchRevealEndWord σ I,
        revealScratchBiddingEndWord σ I, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      (revealScratchBidsHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [revealScratchBidsLengthWord,
      revealScratchBidsLengthSlot] using rd979₀⟩
  have heqValues :
      UInt256.eq (revealScratchBidsLengthWord σ I) valuesLen = ⟨1⟩ := by
    rw [← hvaluesEq]
    exact u256_eq_refl _
  have rd982₀ := evm_run rd979 with [dup8, dup2, eq]
  have rd982 := rd982₀
  rw [heqValues] at rd982
  have rd989 := evm_run rd982 with [push2 ⟨989⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have heqFakes :
      UInt256.eq (revealScratchBidsLengthWord σ I) fakesLen = ⟨1⟩ := by
    rw [← hfakesEq]
    exact u256_eq_refl _
  have rd993₀ := evm_run rd989 with [jumpdest, dup6, dup2, eq]
  have rd993 := rd993₀
  rw [heqFakes] at rd993
  have rd1000 := evm_run rd993 with [push2 ⟨1000⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have heqSecrets :
      UInt256.eq (revealScratchBidsLengthWord σ I) secretsLen = ⟨1⟩ := by
    rw [← hsecretsEq]
    exact u256_eq_refl _
  have rd1004₀ := evm_run rd1000 with [jumpdest, dup4, dup2, eq]
  have rd1004 := rd1004₀
  rw [heqSecrets] at rd1004
  have rd1011 := evm_run rd1004 with [push2 ⟨1011⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have rd1014 := evm_run rd1011 with [jumpdest, push0, dup1]
  exact ⟨_, _, rd1014⟩

theorem blindAuctionRevealX_from963_lengthsOk_zero_toCall {cA σ I} {g : Sat256}
    {s0 : State} {k C : ℕ} {valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨963⟩
      [revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd,
        ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbidsZero : revealScratchBidsLengthWord σ I = ⟨0⟩)
    (hvaluesEq : revealScratchBidsLengthWord σ I = valuesLen)
    (hfakesEq : revealScratchBidsLengthWord σ I = fakesLen)
    (hsecretsEq : revealScratchBidsLengthWord σ I = secretsLen)
    (hbidsHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
          revealScratchBidsLengthSlot I) :
    ∃ gasArg k' C', RD blindAuctionBytecode I g s0 ⟨1349⟩
      [gasArg, revealScratchSenderWord I, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, revealScratchSenderWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩,
        revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      (revealScratchBidsHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd1014⟩ :=
    blindAuctionRevealX_from963_lengthsOk_toLoopInit (cA := cA) (σ := σ) (I := I)
      (g := g) (s0 := s0) rd hvaluesEq hfakesEq hsecretsEq hbidsHash
  have hlt : UInt256.lt (⟨0⟩ : UInt256) (revealScratchBidsLengthWord σ I) = ⟨0⟩ := by
    rw [hbidsZero]
    decide
  have rd1019₀ := evm_run rd1014 with [jumpdest, dup3, dup2, lt, iszero]
  have rd1019 := rd1019₀
  rw [hlt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by decide] at rd1019
  have rd1331 := evm_run rd1019 with [push2 ⟨1331⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have rd1348₀ := evm_run rd1331 with [
    jumpdest, pop, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (revealScratchBidsHashMem_mload64 I)
      (by decide) (by evm_ov),
    push0, swap1, caller, swap1, dup4, swap1, dup4, dup2, dup2, dup2, dup6, dup8]
  obtain ⟨gasArg, rd1349⟩ := rd1348₀.gas (by decide) (by evm_ov)
  exact ⟨gasArg, _, _, by
    simpa [revealScratchSenderWord, hbidsZero, hvaluesEq, hfakesEq, hsecretsEq] using rd1349⟩

theorem blindAuctionRevealX_loopCond_taken {I} {g : Sat256} {s0 : State}
    {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen
      valuesEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1014⟩
      [i, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C)
    (hbound : i.toNat < len.toNat) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1023⟩
      [i, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k' C' := by
  have hlt : UInt256.lt i len = ⟨1⟩ := ult_one hbound
  have rd1019₀ := evm_run rd with [jumpdest, dup3, dup2, lt, iszero]
  have rd1019 := rd1019₀
  rw [hlt, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ by decide] at rd1019
  exact ⟨_, _, evm_run rd1019 with [push2 ⟨1331⟩, jumpiNT (by decide)]⟩

theorem blindAuctionRevealX_from963_lengthsOk_nonzero_toLoopBody {cA σ I}
    {g : Sat256} {s0 : State} {k C : ℕ}
    {valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨963⟩
      [revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd,
        ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbidsNonzero : revealScratchBidsLengthWord σ I ≠ ⟨0⟩)
    (hvaluesEq : revealScratchBidsLengthWord σ I = valuesLen)
    (hfakesEq : revealScratchBidsLengthWord σ I = fakesLen)
    (hsecretsEq : revealScratchBidsLengthWord σ I = secretsLen)
    (hbidsHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
          revealScratchBidsLengthSlot I) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1023⟩
      [⟨0⟩, ⟨0⟩, revealScratchBidsLengthWord σ I,
        revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd,
        ⟨276⟩, blindAuctionSelWord I]
      (revealScratchBidsHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd1014⟩ :=
    blindAuctionRevealX_from963_lengthsOk_toLoopInit (cA := cA) (σ := σ) (I := I)
      (g := g) (s0 := s0) rd hvaluesEq hfakesEq hsecretsEq hbidsHash
  have hbound : (⟨0⟩ : UInt256).toNat < (revealScratchBidsLengthWord σ I).toNat := by
    have hneNat : (revealScratchBidsLengthWord σ I).toNat ≠ 0 := by
      intro hnat
      apply hbidsNonzero
      apply u256_inj
      change (revealScratchBidsLengthWord σ I).toNat = (⟨0⟩ : UInt256).toNat
      simpa using hnat
    simpa using Nat.pos_of_ne_zero hneNat
  exact blindAuctionRevealX_loopCond_taken rd1014 hbound

set_option maxHeartbeats 1000000 in
theorem blindAuctionRevealX_from963_empty_toCall {cA σ I} {g : Sat256}
    {s0 : State} {k C : ℕ} {valuesEnd fakesEnd secretsEnd : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨963⟩
      [revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I,
        ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd, ⟨276⟩,
        blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbidsZero : revealScratchBidsLengthWord σ I = ⟨0⟩)
    (hbidsHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
          revealScratchBidsLengthSlot I) :
    ∃ gasArg k' C', RD blindAuctionBytecode I g s0 ⟨1349⟩
      [gasArg, revealScratchSenderWord I, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, revealScratchSenderWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩,
        revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I, ⟨0⟩,
        secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      (revealScratchBidsHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd968 := evm_run rd with [jumpdest, caller, push0, swap1, dup2]
  have rd969 := evm_run rd968 with [
    raw mstore 0 (revealScratchBidsSourceMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd978 := evm_run rd969 with [
    push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0 (revealScratchBidsHashMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1,
    raw keccak256 0 (revealScratchBidsLengthSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost hbidsHash (by decide) (by evm_ov)]
  obtain ⟨_, _, rd979₀⟩ := rd978.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd979⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨979⟩
      [⟨0⟩, revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I, ⟨0⟩,
        secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      (revealScratchBidsHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    have hpc979 :
        (⟨963⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
                    UInt256.ofNat 2 +
                  UInt256.ofNat 2 +
                ⟨1⟩ +
              UInt256.ofNat 2 +
            ⟨1⟩ +
          ⟨1⟩ +
        ⟨1⟩ : UInt256) = ⟨979⟩ := by
      native_decide
    have hload0 :
        Option.option (⟨0⟩ : UInt256)
          (fun ac => Batteries.RBMap.findD ac.storage (revealScratchBidsLengthSlot I) ⟨0⟩)
          (Batteries.RBMap.find? σ I.codeOwner) = ⟨0⟩ := by
      simpa [revealScratchBidsLengthWord, revealScratchBidsLengthSlot] using hbidsZero
    exact ⟨_, _, by simpa [hpc979, hload0] using rd979₀⟩
  have rd982₀ := evm_run rd979 with [dup8, dup2, eq]
  have rd982 := rd982₀
  rw [show UInt256.eq (⟨0⟩ : UInt256) (⟨0⟩ : UInt256) = ⟨1⟩ by decide] at rd982
  have rd989 := evm_run rd982 with [push2 ⟨989⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have rd993₀ := evm_run rd989 with [jumpdest, dup6, dup2, eq]
  have rd993 := rd993₀
  rw [show UInt256.eq (⟨0⟩ : UInt256) (⟨0⟩ : UInt256) = ⟨1⟩ by decide] at rd993
  have rd1000 := evm_run rd993 with [push2 ⟨1000⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have rd1004₀ := evm_run rd1000 with [jumpdest, dup4, dup2, eq]
  have rd1004 := rd1004₀
  rw [show UInt256.eq (⟨0⟩ : UInt256) (⟨0⟩ : UInt256) = ⟨1⟩ by decide] at rd1004
  have rd1011 := evm_run rd1004 with [push2 ⟨1011⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have rd1019₀ := evm_run rd1011 with [
    jumpdest, push0, dup1, jumpdest, dup3, dup2, lt, iszero]
  have rd1019 := rd1019₀
  rw [show UInt256.lt (⟨0⟩ : UInt256) (⟨0⟩ : UInt256) = ⟨0⟩ by decide,
    show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by decide] at rd1019
  have rd1331 := evm_run rd1019 with [push2 ⟨1331⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have rd1348₀ := evm_run rd1331 with [
    jumpdest, pop, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (revealScratchBidsHashMem_mload64 I)
      (by decide) (by evm_ov),
    push0, swap1, caller, swap1, dup4, swap1, dup4, dup2, dup2, dup2, dup6, dup8]
  obtain ⟨gasArg, rd1349⟩ := rd1348₀.gas (by decide) (by evm_ov)
  exact ⟨gasArg, _, _, by simpa [revealScratchSenderWord] using rd1349⟩

theorem blindAuctionRevealX_from963_empty_callMade {cA gh bl σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {valuesEnd fakesEnd secretsEnd : UInt256}
    (hdepth : I.depth.val < 1024)
    (rd : RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨963⟩
      [revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I,
        ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd, ⟨276⟩,
        blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbidsZero : revealScratchBidsLengthWord σ I = ⟨0⟩)
    (hbidsHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
          revealScratchBidsLengthSlot I) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA
          (initState cA gh bl σ σ₀ g A I).genesisBlockHeader
          (initState cA gh bl σ σ₀ g A I).blocks
          σ (initState cA gh bl σ σ₀ g A I).σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (revealScratchSenderWord I))
          (toExecute σ (AccountAddress.ofUInt256 (revealScratchSenderWord I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ByteArray.empty (I.depth + 1) I.header I.perm)
      ∧ o.size < 2 ^ 255
      ∧ RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1350⟩
          [(if z then ⟨1⟩ else ⟨0⟩), ⟨128⟩, ⟨0⟩, revealScratchSenderWord I,
            ⟨0⟩, ⟨0⟩, ⟨0⟩, revealScratchRevealEndWord σ I,
            revealScratchBiddingEndWord σ I, ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩,
            valuesEnd, ⟨276⟩, blindAuctionSelWord I]
          (revealScratchBidsHashMem I) (UInt256.ofNat 3) o (cA', σ') k' C' := by
  obtain ⟨gasArg, _, _, rd1349⟩ :=
    blindAuctionRevealX_from963_empty_toCall (cA := cA) (σ := σ) (I := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I) rd hbidsZero hbidsHash
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ, rd1350₀⟩ :=
    rd1349.call (by decide) hdepth (by evm_ov)
  have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat o.size := by
      show (0 : Nat) ≤ (UInt256.ofNat o.size).val.val
      exact Nat.zero_le _
    simp [min, hle]
  have hcd : (revealScratchBidsHashMem I).readWithPadding
      (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat = ByteArray.empty := by
    exact revealScratch_readWithPadding_zero _ _
  have hΘ' : ∃ (g'' : UInt256) (A' : Substate),
      (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA
        (initState cA gh bl σ σ₀ g A I).genesisBlockHeader
        (initState cA gh bl σ σ₀ g A I).blocks
        σ (initState cA gh bl σ σ₀ g A I).σ₀ A_in
        (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
        (AccountAddress.ofUInt256 (revealScratchSenderWord I))
        (toExecute σ (AccountAddress.ofUInt256 (revealScratchSenderWord I)))
        callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
        ByteArray.empty (I.depth + 1) I.header I.perm := by
    rcases hΘ with ⟨g'', A', hΘeq⟩
    refine ⟨g'', A', ?_⟩
    rw [hcd] at hΘeq
    exact hΘeq
  have ho255 : o.size < 2 ^ 255 := by
    rcases hΘ' with ⟨g'', A', hΘeq⟩
    have ho : o = (Ethereum.EVM.Θ I.blobVersionedHashes cA
        (initState cA gh bl σ σ₀ g A I).genesisBlockHeader
        (initState cA gh bl σ σ₀ g A I).blocks
        σ (initState cA gh bl σ σ₀ g A I).σ₀ A_in
        (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
        (AccountAddress.ofUInt256 (revealScratchSenderWord I))
        (toExecute σ (AccountAddress.ofUInt256 (revealScratchSenderWord I)))
        callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
        ByteArray.empty (I.depth + 1) I.header I.perm).2.2.2.2.2 :=
      congrArg (fun t => t.2.2.2.2.2) hΘeq
    rw [ho]
    exact Theta_returnData_size_lt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have haw : UInt256.ofNat
      (MachineState.M (MachineState.M (UInt256.ofNat 3).toNat (⟨128⟩ : UInt256).toNat
        (⟨0⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) =
      (UInt256.ofNat 3) := by
    decide
  rw [hmin, revealScratch_write_len_zero, haw] at rd1350₀
  exact ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ', ho255,
    by simpa [revealScratchSenderWord] using rd1350₀⟩

set_option maxHeartbeats 1000000 in
theorem blindAuctionRevealX_from963_empty_callDepth {cA gh bl σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {valuesEnd fakesEnd secretsEnd : UInt256}
    (hdepth : I.depth = 1024)
    (rd : RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨963⟩
      [revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I,
        ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd, ⟨276⟩,
        blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbidsZero : revealScratchBidsLengthWord σ I = ⟨0⟩)
    (hbidsHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
          revealScratchBidsLengthSlot I) :
    ∃ k' C', RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1350⟩
      [⟨0⟩, ⟨128⟩, ⟨0⟩, revealScratchSenderWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩,
        revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I, ⟨0⟩,
        secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      (revealScratchBidsHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨gasArg, _, _, rd1349⟩ :=
    blindAuctionRevealX_from963_empty_toCall (cA := cA) (σ := σ) (I := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I) rd hbidsZero hbidsHash
  obtain ⟨k', C', rd1350₀⟩ := rd1349.callDepthLimit (by decide) hdepth (by evm_ov)
  have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw : UInt256.ofNat
      (MachineState.M (MachineState.M (UInt256.ofNat 3).toNat (⟨128⟩ : UInt256).toNat
        (⟨0⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) =
      (UInt256.ofNat 3) := by
    decide
  rw [hmin, revealScratch_write_len_zero, haw] at rd1350₀
  exact ⟨k', C', by simpa [revealScratchSenderWord] using rd1350₀⟩

theorem blindAuctionRevealX_postCallEmpty_toRequire {I} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    {z senderWord revealEnd biddingEnd valuesEnd fakesEnd secretsEnd : UInt256}
    {sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1350⟩
      [z, ⟨128⟩, ⟨0⟩, senderWord, ⟨0⟩, ⟨0⟩, ⟨0⟩, revealEnd, biddingEnd,
        ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd, ⟨276⟩, sel]
      mem aw ByteArray.empty acc k C) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1405⟩
      [z, ⟨0⟩, ⟨0⟩, revealEnd, biddingEnd, ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd,
        ⟨0⟩, valuesEnd, ⟨276⟩, sel]
      mem aw ByteArray.empty acc k' C' := by
    refine ⟨_, _, evm_run rd with [
      swap3, pop, pop, pop, returndatasize, dup1, push0, dup2, eq, push2 ⟨1395⟩,
      jumpiT (by decide) (by jump_dest), jumpdest, push1 ⟨96⟩, swap2, pop,
      jumpdest, pop, pop, swap1, pop]⟩

set_option maxHeartbeats 1000000 in
theorem blindAuctionRevealX_postCallNonempty_toRequire {I} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ} {z senderWord revealEnd biddingEnd valuesEnd fakesEnd secretsEnd sel : UInt256}
    {o : ByteArray}
    (rd : RD blindAuctionBytecode I g s0 ⟨1350⟩
      [z, ⟨128⟩, ⟨0⟩, senderWord, ⟨0⟩, ⟨0⟩, ⟨0⟩, revealEnd, biddingEnd,
        ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd, ⟨276⟩, sel]
      (revealScratchBidsHashMem I) (UInt256.ofNat 3) o acc k C)
    (ho0 : o.size ≠ 0) (hosz : o.size < UInt256.size) :
    ∃ mem' aw' k' C', RD blindAuctionBytecode I g s0 ⟨1405⟩
      [z, ⟨0⟩, ⟨0⟩, revealEnd, biddingEnd, ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd,
        ⟨0⟩, valuesEnd, ⟨276⟩, sel]
      mem' aw' o acc k' C' := by
  let rdsz : UInt256 := UInt256.ofNat o.size
  have hrdsz_toNat : rdsz.toNat = o.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt hosz
  have hrdsz_ne : rdsz ≠ ⟨0⟩ := by
    intro h
    have hnat : rdsz.toNat = 0 := by rw [h]; rfl
    exact ho0 (by rwa [hrdsz_toNat] at hnat)
  have heq0 : UInt256.eq rdsz (⟨0⟩ : UInt256) = ⟨0⟩ := u256_eq_of_ne hrdsz_ne
  have rd1359₀ := evm_run rd with [swap3, pop, pop, pop, returndatasize, dup1, push0, dup2, eq]
  have rd1359 := rd1359₀
  change UInt256.eq rdsz (⟨0⟩ : UInt256) = ⟨0⟩ at heq0
  rw [show UInt256.ofNat o.size = rdsz from rfl, heq0] at rd1359
  have rd1363 := evm_run rd1359 with [push2 ⟨1395⟩, jumpiNT (by decide)]
  let rounded : UInt256 := UInt256.land (UInt256.add rdsz ⟨63⟩) (UInt256.lnot ⟨31⟩)
  let mem2 : ByteArray :=
    (UInt256.toByteArray (UInt256.add ⟨128⟩ rounded)).write 0
      (revealScratchBidsHashMem I) 64 32
  have rd1381 := evm_run rd1363 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost (revealScratchBidsHashMem_mload64 I) (by decide) (by evm_ov),
    swap2, pop, push1 ⟨31⟩, not, push1 ⟨63⟩, returndatasize, add, and, dup3, add,
    push1 ⟨64⟩,
    raw mstore 0 mem2 (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  let mem3 : ByteArray := (UInt256.toByteArray rdsz).write 0 mem2 128 32
  have rd1384 := evm_run rd1381 with [
    returndatasize, dup3,
    raw mstore (Cₘ (UInt256.ofNat 5) - Cₘ (UInt256.ofNat 3))
      mem3 (UInt256.ofNat 5) (by decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        decide)
      (by rfl) (by decide) (by evm_ov)]
  have rd1390 := evm_run rd1384 with [returndatasize, push0, push1 ⟨32⟩, dup5, add]
  let copyDest : UInt256 := (⟨128⟩ : UInt256) + ⟨32⟩
  let copyLen : UInt256 := UInt256.ofNat o.size
  have hcopyDest_toNat : copyDest.toNat = 160 := by
    decide
  have hcopyLen_toNat : copyLen.toNat = o.size := by
    simpa [copyLen] using UInt256.toNat_ofNat_of_lt hosz
  let mem4 : ByteArray := o.write 0 mem3 copyDest.toNat copyLen.toNat
  have haw4 :
      UInt256.ofNat (MachineState.M (UInt256.ofNat 5).toNat copyDest.toNat copyLen.toNat) =
        SimpleAuction.withdrawReturnDataActiveWords o := by
    simp [SimpleAuction.withdrawReturnDataActiveWords, copyDest, copyLen, hcopyDest_toNat,
      hcopyLen_toNat]
  have rd1391 := SimpleAuction.withdrawRDReturndatacopy
    (Cₘ (SimpleAuction.withdrawReturnDataActiveWords o) - Cₘ (UInt256.ofNat 5))
    mem4
    (SimpleAuction.withdrawReturnDataActiveWords o)
    rd1390 (by decide)
    (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, hcopyLen_toNat]; omega)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, copyDest, copyLen,
        SimpleAuction.withdrawReturnDataActiveWords, hcopyDest_toNat, hcopyLen_toNat])
    (by rfl)
    haw4
    (by evm_ov)
  have rd1400 := evm_run rd1391 with [push2 ⟨1400⟩, jump (by jump_dest), jumpdest]
  exact ⟨_, _, _, _, evm_run rd1400 with [pop, pop, swap1, pop]⟩

theorem blindAuctionRevealX_postCallRequire_success_stop {I} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {revealEnd biddingEnd valuesEnd fakesEnd secretsEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1405⟩
      [⟨1⟩, ⟨0⟩, ⟨0⟩, revealEnd, biddingEnd, ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd,
        ⟨0⟩, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C) :
    RDret blindAuctionBytecode g s0 acc ByteArray.empty := by
  have rd1413 := evm_run rd with [
    dup1, push2 ⟨1413⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have rd276 := evm_run rd1413 with [
    jumpdest, pop, pop, pop, pop, pop, pop, pop, pop, pop, pop, pop,
    jump (by jump_dest), jumpdest]
  exact rd276.stop (by decide) (by evm_ov)

theorem blindAuctionRevealX_postCallRequire_failure_revert {I} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {revealEnd biddingEnd valuesEnd fakesEnd secretsEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1405⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, revealEnd, biddingEnd, ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd,
        ⟨0⟩, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C) :
    RDrev blindAuctionBytecode g s0 := by
  have rd1410 := evm_run rd with [
    dup1, push2 ⟨1413⟩, jumpiNT (by decide), push0, push0]
  exact RD.rev _ rd1410 (by decide)
    (fun s haws hstks => by rw [memExpRevertZeroOff s hstks, haws])
    (by evm_ov)

theorem scratch_blindAuctionRevealX_postCallRequire_success_stop_general {I} {g : Sat256}
    {s0 : State} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {refund len revealEnd biddingEnd valuesLen valuesEnd fakesLen fakesEnd secretsLen
      secretsEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1405⟩
      [⟨1⟩, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen,
        fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C) :
    RDret blindAuctionBytecode g s0 acc ByteArray.empty := by
  have rd1413 := evm_run rd with [
    dup1, push2 ⟨1413⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have rd276 := evm_run rd1413 with [
    jumpdest, pop, pop, pop, pop, pop, pop, pop, pop, pop, pop, pop,
    jump (by jump_dest), jumpdest]
  exact rd276.stop (by decide) (by evm_ov)

theorem scratch_blindAuctionRevealX_postCallRequire_failure_revert_general {I} {g : Sat256}
    {s0 : State} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {refund len revealEnd biddingEnd valuesLen valuesEnd fakesLen fakesEnd secretsLen
      secretsEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1405⟩
      [⟨0⟩, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen,
        fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C) :
    RDrev blindAuctionBytecode g s0 := by
  have rd1410 := evm_run rd with [
    dup1, push2 ⟨1413⟩, jumpiNT (by decide), push0, push0]
  exact RD.rev _ rd1410 (by decide)
    (fun s haws hstks => by rw [memExpRevertZeroOff s hstks, haws])
    (by evm_ov)

theorem blindAuctionRevealX_postCallEmpty_success_stop {I} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    {senderWord revealEnd biddingEnd valuesEnd fakesEnd secretsEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1350⟩
        [⟨1⟩, ⟨128⟩, ⟨0⟩, senderWord, ⟨0⟩, ⟨0⟩, ⟨0⟩, revealEnd, biddingEnd,
          ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd, ⟨276⟩, sel]
        mem aw ByteArray.empty acc k C) :
      RDret blindAuctionBytecode g s0 acc ByteArray.empty := by
    obtain ⟨_, _, rd1405⟩ := blindAuctionRevealX_postCallEmpty_toRequire rd
    exact blindAuctionRevealX_postCallRequire_success_stop rd1405

theorem blindAuctionRevealX_postCallEmpty_failure_revert {I} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    {senderWord revealEnd biddingEnd valuesEnd fakesEnd secretsEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1350⟩
        [⟨0⟩, ⟨128⟩, ⟨0⟩, senderWord, ⟨0⟩, ⟨0⟩, ⟨0⟩, revealEnd, biddingEnd,
          ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd, ⟨276⟩, sel]
        mem aw ByteArray.empty acc k C) :
      RDrev blindAuctionBytecode g s0 := by
    obtain ⟨_, _, rd1405⟩ := blindAuctionRevealX_postCallEmpty_toRequire rd
    exact blindAuctionRevealX_postCallRequire_failure_revert rd1405

theorem blindAuctionRevealBodyReverts_nonpayable {evm : EVM.State} {locals : Store}
    (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm locals
      revealTransition.body .reverted := by
  dsimp [revealTransition]
  exact bodyReverts_nonPayable h

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

theorem blindAuctionRevealCallvalueRequire_ok {evm : EVM.State} {locals : Store}
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecStmt blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.require (.binary .eq (.env .callvalue) (.intLit 0)))
      (.ok { contract := blindAuctionContract, locals := locals } evm) := by
  exact ExecStmt.requireTrue (evalCallvalueEq_true h)

theorem blindAuctionRevealBody_of_zero_tail {evm : EVM.State} {locals : Store} {result}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (htail : ExecFuncBody blindAuctionConfig
      { contract := blindAuctionContract, locals := locals } evm
      (List.drop 1 revealTransition.body) result) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm locals
      revealTransition.body result := by
  dsimp [ExecTransitionBody, revealTransition] at htail ⊢
  have hreq := blindAuctionRevealCallvalueRequire_ok (locals := locals) h
  cases htail with
  | execBlockOK hblk => exact ExecFuncBody.execBlockOK (ExecBlock.consNormal hreq hblk)
  | execBlockRet hblk => exact ExecFuncBody.execBlockRet (ExecBlock.consNormal hreq hblk)
  | execBlockRevert hblk => exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal hreq hblk)
  | execBlockBreak hblk => exact ExecFuncBody.execBlockBreak (ExecBlock.consNormal hreq hblk)
  | execBlockContinue hblk => exact ExecFuncBody.execBlockContinue (ExecBlock.consNormal hreq hblk)

theorem evalExpr_reveal_biddingEnd (evm : EVM.State) (locals : Store)
    (hbase : locals.get? biddingEndRef.base = none) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.storage biddingEndRef) =
        .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat)) := by
  have her : evalStorageRef blindAuctionConfig
      { contract := blindAuctionContract, locals := locals } evm biddingEndRef =
      .ok { base := "biddingEnd", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, biddingEndRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? blindAuctionContract.storage
      ({ base := "biddingEnd", steps := [] } : EvaledStorageRef) =
      some (.elem (.int uint256Int)) := by
    decide
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase) (her := her)
    (hty := hty) (hloc := blindAuctionConfig_storage_biddingEnd)]
  rw [blindAuctionBiddingEndStorageLocLoad_uint256]

theorem evalExpr_reveal_revealEnd (evm : EVM.State) (locals : Store)
    (hbase : locals.get? revealEndRef.base = none) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.storage revealEndRef) =
        .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)) := by
  have her : evalStorageRef blindAuctionConfig
      { contract := blindAuctionContract, locals := locals } evm revealEndRef =
      .ok { base := "revealEnd", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, revealEndRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? blindAuctionContract.storage
      ({ base := "revealEnd", steps := [] } : EvaledStorageRef) =
      some (.elem (.int uint256Int)) := by
    decide
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase) (her := her)
    (hty := hty) (hloc := blindAuctionConfig_storage_revealEnd)]
  rw [blindAuctionRevealEndStorageLocLoad_uint256]

theorem evalExpr_reveal_afterBiddingEnd_true (evm : EVM.State) (locals : Store)
    (hbase : locals.get? biddingEndRef.base = none)
    (htime :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .gt now (.storage biddingEndRef)) = .ok (.bool true) := by
  simp only [evalExpr?, now, envValue, evalExpr_reveal_biddingEnd evm locals hbase, bind,
    EvalResult.bind, pure]
  simpa [evalBinaryOp?, UInt256.toNat] using htime

theorem evalExpr_reveal_afterBiddingEnd_false (evm : EVM.State) (locals : Store)
    (hbase : locals.get? biddingEndRef.base = none)
    (htime :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat ≤
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .gt now (.storage biddingEndRef)) = .ok (.bool false) := by
  simp only [evalExpr?, now, envValue, evalExpr_reveal_biddingEnd evm locals hbase, bind,
    EvalResult.bind, pure]
  simpa [evalBinaryOp?, UInt256.toNat] using htime

theorem evalExpr_reveal_beforeRevealEnd_true (evm : EVM.State) (locals : Store)
    (hbase : locals.get? revealEndRef.base = none)
    (htime :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .lt now (.storage revealEndRef)) = .ok (.bool true) := by
  simp only [evalExpr?, now, envValue, evalExpr_reveal_revealEnd evm locals hbase, bind,
    EvalResult.bind, pure]
  simpa [evalBinaryOp?, UInt256.toNat] using htime

theorem evalExpr_reveal_beforeRevealEnd_false (evm : EVM.State) (locals : Store)
    (hbase : locals.get? revealEndRef.base = none)
    (htime :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat ≤
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .lt now (.storage revealEndRef)) = .ok (.bool false) := by
  simp only [evalExpr?, now, envValue, evalExpr_reveal_revealEnd evm locals hbase, bind,
    EvalResult.bind, pure]
  simpa [evalBinaryOp?, UInt256.toNat] using htime

theorem blindAuctionRevealBodyReverts_tooEarly {evm : EVM.State} {locals : Store}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbidding : locals.get? biddingEndRef.base = none)
    (htime :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat ≤
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm locals
      revealTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  dsimp [revealTransition]
  exact (ABlock.start
    |>.requireStep (evalCallvalueEq_true hwv)
    |>.requireRevert (evalExpr_reveal_afterBiddingEnd_false evm locals hbidding htime))

theorem blindAuctionRevealBodyReverts_tooLate {evm : EVM.State} {locals : Store}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbidding : locals.get? biddingEndRef.base = none)
    (hreveal : locals.get? revealEndRef.base = none)
    (hafter :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (htime :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat ≤
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm locals
      revealTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  dsimp [revealTransition]
  exact (ABlock.start
    |>.requireStep (evalCallvalueEq_true hwv)
    |>.requireStep (evalExpr_reveal_afterBiddingEnd_true evm locals hbidding hafter)
    |>.requireRevert (evalExpr_reveal_beforeRevealEnd_false evm locals hreveal htime))

/-! ### Source-side base facts for an empty decoded reveal loop -/

def revealEmptyStore : Store :=
  (((∅ : Store).insert "values" (.array [])).insert "fakes" (.array [])).insert "secrets" (.array [])

theorem blindAuctionDecode_reveal_callargs_empty_eq {I : ExecutionEnv} {callargs : Store}
    (hdec : decodeCalldata (revealTransition.params.map Param.name)
      (transitionSignature revealTransition).paramTypes I.calldata = some callargs)
    (hvalues : callargs.get? "values" = some (.array []))
    (hfakes : callargs.get? "fakes" = some (.array []))
    (hsecrets : callargs.get? "secrets" = some (.array [])) :
    callargs = revealEmptyStore := by
  obtain ⟨values, fakes, secrets, rfl⟩ :=
    blindAuctionDecode_reveal_callargs_store_shape hdec
  have hvaluesNil : values = [] := by
    rw [store_get_ne, store_get_ne, store_get_self] at hvalues
    · cases hvalues
      rfl
    · decide
    · decide
  have hfakesNil : fakes = [] := by
    rw [store_get_ne, store_get_self] at hfakes
    · cases hfakes
      rfl
    · decide
  have hsecretsNil : secrets = [] := by
    rw [store_get_self] at hsecrets
    cases hsecrets
    rfl
  simp [revealEmptyStore, hvaluesNil, hfakesNil, hsecretsNil]

def revealLengthStore : Store :=
  revealEmptyStore.insert "length" (.int 0)

def revealRefundStore (refund : UInt256) : Store :=
  revealLengthStore.insert "refund" (.int (Int.ofNat refund.toNat))

def revealLoopStore (refund i : UInt256) : Store :=
  (revealRefundStore refund).insert "i" (.int (Int.ofNat i.toNat))

def revealCallStore (refund i : UInt256) (success : Bool) (out : ByteArray) : Store :=
  (revealLoopStore refund i).insert "success" (.bool success) |>.insert "_data" (.bytes out)

theorem revealEmptyStore_values :
    revealEmptyStore.get? "values" = some (.array []) := by
  native_decide

theorem revealEmptyStore_fakes :
    revealEmptyStore.get? "fakes" = some (.array []) := by
  native_decide

theorem revealEmptyStore_secrets :
    revealEmptyStore.get? "secrets" = some (.array []) := by
  native_decide

theorem revealEmptyStore_bids_none :
    revealEmptyStore.get? "bids" = none := by
  native_decide

theorem evalExpr_reveal_empty_values_length (evm : EVM.State) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := revealEmptyStore } evm
      (.arrayLength .localVar { base := "values" }) = .ok (.int 0) := by
  rw [evalExpr?]
  rw [revealEmptyStore_values]
  simp [readLocalPath?, EvalResult.bind, bind, pure]

theorem evalExpr_reveal_empty_fakes_length (evm : EVM.State) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := revealEmptyStore } evm
      (.arrayLength .localVar { base := "fakes" }) = .ok (.int 0) := by
  rw [evalExpr?]
  rw [revealEmptyStore_fakes]
  simp [readLocalPath?, EvalResult.bind, bind, pure]

theorem evalExpr_reveal_empty_secrets_length (evm : EVM.State) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := revealEmptyStore } evm
      (.arrayLength .localVar { base := "secrets" }) = .ok (.int 0) := by
  rw [evalExpr?]
  rw [revealEmptyStore_secrets]
  simp [readLocalPath?, EvalResult.bind, bind, pure]

theorem evalExpr_reveal_local_empty_array_length (evm : EVM.State) (locals : Store)
    (name : Ident) (h : locals.get? name = some (.array [])) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.arrayLength .localVar { base := name }) = .ok (.int 0) := by
  rw [evalExpr?]
  rw [h]
  simp [readLocalPath?, EvalResult.bind, bind, pure]

theorem evalExpr_reveal_local_array_length (evm : EVM.State) (locals : Store)
    (name : Ident) (xs : List Value) (h : locals.get? name = some (.array xs)) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.arrayLength .localVar { base := name }) = .ok (.int xs.length) := by
  rw [evalExpr?]
  rw [h]
  simp [readLocalPath?, EvalResult.bind, bind, pure]

theorem evalExpr_reveal_var_value (evm : EVM.State) (locals : Store) (name : Ident) (v : Value)
    (h : locals.get? name = some v) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.var name) = .ok v := by
  rw [evalExpr?]
  change EvalResult.ofOption .unboundVariable (locals.get? name) = .ok v
  rw [h]
  rfl

theorem evalExpr_reveal_var_int (evm : EVM.State) (locals : Store) (name : Ident) (n : Int)
    (h : locals.get? name = some (.int n)) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.var name) = .ok (.int n) := by
  exact evalExpr_reveal_var_value evm locals name (.int n) h

theorem evalExpr_reveal_local_empty_length_eq_zero_var (evm : EVM.State) (locals : Store)
    (name : Ident) (harr : locals.get? name = some (.array []))
    (hlen : locals.get? "length" = some (.int 0)) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .eq (.arrayLength .localVar { base := name }) (.var "length")) =
        .ok (.bool true) := by
  rw [evalExpr?]
  simp only [evalExpr_reveal_local_empty_array_length evm locals name harr,
    evalExpr_reveal_var_int evm locals "length" 0 hlen, EvalResult.bind, bind]
  rfl

theorem evalExpr_reveal_local_array_length_eq_var_false (evm : EVM.State) (locals : Store)
    (name : Ident) (xs : List Value) (len : UInt256)
    (harr : locals.get? name = some (.array xs))
    (hlen : locals.get? "length" = some (.int (Int.ofNat len.toNat)))
    (hne : xs.length ≠ len.toNat) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .eq (.arrayLength .localVar { base := name }) (.var "length")) =
        .ok (.bool false) := by
  rw [evalExpr?]
  simp only [evalExpr_reveal_local_array_length evm locals name xs harr,
    evalExpr_reveal_var_int evm locals "length" (Int.ofNat len.toNat) hlen,
    EvalResult.bind, bind]
  simp [evalBinaryOp?]
  have hint : (Int.ofNat xs.length == Int.ofNat len.toNat) = false := by
    simp [beq_eq_false_iff_ne, hne]
  simpa [hint] using hne

theorem evalExpr_reveal_local_array_length_eq_var_true (evm : EVM.State) (locals : Store)
    (name : Ident) (xs : List Value) (len : UInt256)
    (harr : locals.get? name = some (.array xs))
    (hlen : locals.get? "length" = some (.int (Int.ofNat len.toNat)))
    (heq : xs.length = len.toNat) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .eq (.arrayLength .localVar { base := name }) (.var "length")) =
        .ok (.bool true) := by
  rw [evalExpr?]
  simp only [evalExpr_reveal_local_array_length evm locals name xs harr,
    evalExpr_reveal_var_int evm locals "length" (Int.ofNat len.toNat) hlen,
    EvalResult.bind, bind]
  simp [evalBinaryOp?, heq]

theorem evalExpr_reveal_loop_cond_false (evm : EVM.State) (locals : Store)
    (hi : locals.get? "i" = some (.int 0))
    (hlen : locals.get? "length" = some (.int 0)) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .lt (.var "i") (.var "length")) = .ok (.bool false) := by
  rw [evalExpr?]
  simp only [evalExpr_reveal_var_int evm locals "i" 0 hi,
    evalExpr_reveal_var_int evm locals "length" 0 hlen, EvalResult.bind, bind]
  rfl

theorem evalExpr_reveal_local_array_index_any (evm : EVM.State) (locals : Store)
    (name : Ident) (xs : List Value) (idx : UInt256) (v : Value)
    (harr : locals.get? name = some (.array xs))
    (hi : locals.get? "i" = some (.int (Int.ofNat idx.toNat)))
    (hbound : idx.toNat < xs.length)
    (hlookup : lookupNth? xs idx.toNat = some v)
    (hnorm : normalizeRawBoolWord? v = .ok v) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.index (.var name) (.var "i")) = .ok v := by
  rw [evalExpr?]
  simp only [evalExpr_reveal_var_value evm locals name (.array xs) harr,
    evalExpr_reveal_var_value evm locals "i" (.int (Int.ofNat idx.toNat)) hi,
    EvalResult.bind, bind]
  unfold evalIndex?
  simp only
  rw [if_pos]
  · simp [hlookup, hnorm]
  · constructor
    · exact Int.natCast_nonneg idx.toNat
    · simpa using hbound

theorem evalExpr_reveal_sender (evm : EVM.State) (locals : Store) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      sender = .ok (.address evm.executionEnv.source) := by
  simp [sender, evalExpr?, envValue, pure]

theorem evalExpr_reveal_refund (evm : EVM.State) (locals : Store) (refund : UInt256)
    (hrefund : locals.get? "refund" = some (.int (Int.ofNat refund.toNat))) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.var "refund") = .ok (.int (Int.ofNat refund.toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption .unboundVariable (locals.get? "refund") =
    .ok (.int (Int.ofNat refund.toNat))
  rw [hrefund]
  rfl

theorem evalExpr_reveal_emptyBytes (evm : EVM.State) (locals : Store) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.newBytes (.intLit 0)) = .ok (.bytes ByteArray.empty) := by
  simp [evalExpr?, pure, bind, EvalResult.bind]
  rfl

theorem revealCallStore_success_get (refund i : UInt256) (success : Bool) (out : ByteArray) :
    (revealCallStore refund i success out).get? "success" = some (.bool success) := by
  unfold revealCallStore
  rw [store_get_ne]
  · exact store_get_self _ _ _
  · decide

theorem evalExpr_reveal_success (evm : EVM.State) (refund i : UInt256) (success : Bool)
    (out : ByteArray) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract, locals := revealCallStore refund i success out } evm
      (.var "success") = .ok (.bool success) := by
  rw [evalExpr?]
  change EvalResult.ofOption .unboundVariable
    ((revealCallStore refund i success out).get? "success") = .ok (.bool success)
  rw [revealCallStore_success_get]
  rfl

theorem evalExpr_reveal_bids_length_zero (evm : EVM.State) (locals : Store)
    (hbids : locals.get? "bids" = none)
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = ⟨0⟩) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.arrayLength .storage (bidsRef sender)) = .ok (.int 0) := by
  let er : EvaledStorageRef :=
    { base := "bids", steps := [.mindex (.address evm.executionEnv.source)] }
  have her : evalStorageRef blindAuctionConfig
      { contract := blindAuctionContract, locals := locals } evm (bidsRef sender) = .ok er := by
    simp [er, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, bidsRef, sender,
      evalExpr?, envValue, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]
  have hty : storageTypeAt? blindAuctionContract.storage er = some (.dynamicArray bidStructTy) := by
    simp [er, storageTypeAt?, blindAuctionContract, storageDecls, storageTypeStep?, bidStructTy]
  have hres :
      resolveStorageRef? blindAuctionConfig
        { contract := blindAuctionContract, locals := locals } evm (bidsRef sender) =
        .ok (er, .dynamicArray bidStructTy) :=
    resolveStorageRef?_ok hbids her hty
  rw [evalExpr?]
  simp only [hres, bind, EvalResult.bind]
  change readStorageArrayLength? blindAuctionConfig evm er (.dynamicArray bidStructTy) =
    .ok (.int 0)
  simp only [readStorageArrayLength?, er, List.cons_append, List.nil_append]
  change (match some (blindAuctionUint256Loc (bidsBase (.address evm.executionEnv.source))) with
    | some lenLoc =>
        match storageLocLoad evm lenLoc with
        | Value.int n => pure (Value.int n)
        | _ => EvalResult.error .storageError
    | none => EvalResult.error .storageError) = EvalResult.ok (Value.int 0)
  change (match storageLocLoad evm (blindAuctionUint256Loc (bidsBase (.address evm.executionEnv.source))) with
    | Value.int n => pure (Value.int n)
    | _ => EvalResult.error .storageError) = EvalResult.ok (Value.int 0)
  rw [blindAuctionBiddingEndStorageLocLoad_uint256, hlen]
  rfl

theorem evalExpr_reveal_bids_length_any (evm : EVM.State) (locals : Store) (len : UInt256)
    (hbids : locals.get? "bids" = none)
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.arrayLength .storage (bidsRef sender)) = .ok (.int (Int.ofNat len.toNat)) := by
  let er : EvaledStorageRef :=
    { base := "bids", steps := [.mindex (.address evm.executionEnv.source)] }
  have her : evalStorageRef blindAuctionConfig
      { contract := blindAuctionContract, locals := locals } evm (bidsRef sender) = .ok er := by
    simp [er, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, bidsRef, sender,
      evalExpr?, envValue, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]
  have hty : storageTypeAt? blindAuctionContract.storage er = some (.dynamicArray bidStructTy) := by
    simp [er, storageTypeAt?, blindAuctionContract, storageDecls, storageTypeStep?, bidStructTy]
  have hres :
      resolveStorageRef? blindAuctionConfig
        { contract := blindAuctionContract, locals := locals } evm (bidsRef sender) =
        .ok (er, .dynamicArray bidStructTy) :=
    resolveStorageRef?_ok hbids her hty
  rw [evalExpr?]
  simp only [hres, bind, EvalResult.bind]
  change readStorageArrayLength? blindAuctionConfig evm er (.dynamicArray bidStructTy) =
    .ok (.int (Int.ofNat len.toNat))
  simp only [readStorageArrayLength?, er, List.cons_append, List.nil_append]
  change (match some (blindAuctionUint256Loc (bidsBase (.address evm.executionEnv.source))) with
    | some lenLoc =>
        match storageLocLoad evm lenLoc with
        | Value.int n => pure (Value.int n)
        | _ => EvalResult.error .storageError
    | none => EvalResult.error .storageError) = EvalResult.ok (Value.int (Int.ofNat len.toNat))
  change (match storageLocLoad evm (blindAuctionUint256Loc (bidsBase (.address evm.executionEnv.source))) with
    | Value.int n => pure (Value.int n)
    | _ => EvalResult.error .storageError) = EvalResult.ok (Value.int (Int.ofNat len.toNat))
  rw [blindAuctionBiddingEndStorageLocLoad_uint256, hlen]
  rfl

theorem blindAuctionRevealBodyReturns_empty_callSuccess
    (evm evm' : EVM.State) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hafter :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbefore :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = ⟨0⟩)
    (hcall :
      callViaEVM evm (EVM.address evm.executionEnv.source) 0 ByteArray.empty
        (true, evm', out)) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm revealEmptyStore
      revealTransition.body
      (.returned { contract := blindAuctionContract, locals := revealCallStore ⟨0⟩ ⟨0⟩ true out }
        evm' none) := by
  refine ExecFuncBody.execBlockOK ?_
  unfold revealTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_afterBiddingEnd_true evm revealEmptyStore (by native_decide) hafter)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_beforeRevealEnd_true evm revealEmptyStore (by native_decide) hbefore)) ?_
  have hlengthEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := revealEmptyStore }
        evm (.arrayLength .storage (bidsRef sender)) = .ok (.int 0) := by
    exact evalExpr_reveal_bids_length_zero evm revealEmptyStore revealEmptyStore_bids_none hlen
  refine ExecBlock.consNormal (ExecStmt.letDecl hlengthEval) ?_
  change ExecBlock blindAuctionConfig
    { contract := blindAuctionContract, locals := revealLengthStore } evm
    [ .require (.binary .eq (.arrayLength .localVar { base := "values" }) (.var "length")),
      .require (.binary .eq (.arrayLength .localVar { base := "fakes" }) (.var "length")),
      .require (.binary .eq (.arrayLength .localVar { base := "secrets" }) (.var "length")),
      .letDecl "refund" (some uint256) (.intLit 0),
      .for [ .letDecl "i" (some uint256) (.intLit 0) ]
        (.binary .lt (.var "i") (.var "length"))
        [ .assign .localVar { base := "i" } (.binary .add (.var "i") (.intLit 1)) ]
        [ .letStorage "bidToCheck" (bidElemRef sender (.var "i")),
          .letDecl "value" (some uint256) (.index (.var "values") (.var "i")),
          .letDecl "fake" (some boolTy) (.index (.var "fakes") (.var "i")),
          .letDecl "secret" (some bytes32) (.index (.var "secrets") (.var "i")),
          .ite
            (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
              (.keccak256 (.abiEncodePacked
                [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
            [.continue] [],
          .assign .localVar { base := "refund" }
            (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
          .ite
            (.binary .and (.unary .not (.var "fake"))
              (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
            [ .internalCall "placeBid" [sender, .var "value"] "ok",
              .ite (.var "ok")
                [ .assign .localVar { base := "refund" }
                    (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
          .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ],
      .lowLevelCall sender (.var "refund") (.newBytes (.intLit 0)) "success" "_data",
      .require (.var "success") ]
    (.ok { contract := blindAuctionContract, locals := revealCallStore ⟨0⟩ ⟨0⟩ true out }
      evm')
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_empty_length_eq_zero_var evm revealLengthStore "values"
        (by native_decide) (by native_decide))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_empty_length_eq_zero_var evm revealLengthStore "fakes"
        (by native_decide) (by native_decide))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_empty_length_eq_zero_var evm revealLengthStore "secrets"
        (by native_decide) (by native_decide))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (value := .int 0) (by simp [evalExpr?, pure])) ?_
  change ExecBlock blindAuctionConfig
    { contract := blindAuctionContract, locals := revealRefundStore ⟨0⟩ } evm
    [ .for [ .letDecl "i" (some uint256) (.intLit 0) ]
        (.binary .lt (.var "i") (.var "length"))
        [ .assign .localVar { base := "i" } (.binary .add (.var "i") (.intLit 1)) ]
        [ .letStorage "bidToCheck" (bidElemRef sender (.var "i")),
          .letDecl "value" (some uint256) (.index (.var "values") (.var "i")),
          .letDecl "fake" (some boolTy) (.index (.var "fakes") (.var "i")),
          .letDecl "secret" (some bytes32) (.index (.var "secrets") (.var "i")),
          .ite
            (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
              (.keccak256 (.abiEncodePacked
                [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
            [.continue] [],
          .assign .localVar { base := "refund" }
            (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
          .ite
            (.binary .and (.unary .not (.var "fake"))
              (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
            [ .internalCall "placeBid" [sender, .var "value"] "ok",
              .ite (.var "ok")
                [ .assign .localVar { base := "refund" }
                    (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
          .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ],
      .lowLevelCall sender (.var "refund") (.newBytes (.intLit 0)) "success" "_data",
      .require (.var "success") ]
    (.ok { contract := blindAuctionContract, locals := revealCallStore ⟨0⟩ ⟨0⟩ true out }
      evm')
  have hfor :
      ExecStmt blindAuctionConfig
        { contract := blindAuctionContract, locals := revealRefundStore ⟨0⟩ } evm
        (.for [ .letDecl "i" (some uint256) (.intLit 0) ]
          (.binary .lt (.var "i") (.var "length"))
          [ .assign .localVar { base := "i" } (.binary .add (.var "i") (.intLit 1)) ]
          [ .letStorage "bidToCheck" (bidElemRef sender (.var "i")),
            .letDecl "value" (some uint256) (.index (.var "values") (.var "i")),
            .letDecl "fake" (some boolTy) (.index (.var "fakes") (.var "i")),
            .letDecl "secret" (some bytes32) (.index (.var "secrets") (.var "i")),
            .ite
              (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
                (.keccak256 (.abiEncodePacked
                  [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
              [.continue] [],
            .assign .localVar { base := "refund" }
              (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
            .ite
              (.binary .and (.unary .not (.var "fake"))
                (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
              [ .internalCall "placeBid" [sender, .var "value"] "ok",
                .ite (.var "ok")
                  [ .assign .localVar { base := "refund" }
                      (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
            .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ])
        (.ok { contract := blindAuctionContract, locals := revealLoopStore ⟨0⟩ ⟨0⟩ } evm) := by
    have hinit :
        ExecBlock blindAuctionConfig
          { contract := blindAuctionContract, locals := revealRefundStore ⟨0⟩ } evm
          [ .letDecl "i" (some uint256) (.intLit 0) ]
          (.ok { contract := blindAuctionContract, locals := revealLoopStore ⟨0⟩ ⟨0⟩ } evm) := by
      refine ExecBlock.consNormal
        (ExecStmt.letDecl (value := .int 0) (by simp [evalExpr?, pure])) ?_
      exact ExecBlock.nil
    have hloop :
        ExecForLoop blindAuctionConfig
          { contract := blindAuctionContract, locals := revealLoopStore ⟨0⟩ ⟨0⟩ } evm
          (.binary .lt (.var "i") (.var "length"))
          [ .assign .localVar { base := "i" } (.binary .add (.var "i") (.intLit 1)) ]
          [ .letStorage "bidToCheck" (bidElemRef sender (.var "i")),
            .letDecl "value" (some uint256) (.index (.var "values") (.var "i")),
            .letDecl "fake" (some boolTy) (.index (.var "fakes") (.var "i")),
            .letDecl "secret" (some bytes32) (.index (.var "secrets") (.var "i")),
            .ite
              (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
                (.keccak256 (.abiEncodePacked
                  [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
              [.continue] [],
            .assign .localVar { base := "refund" }
              (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
            .ite
              (.binary .and (.unary .not (.var "fake"))
                (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
              [ .internalCall "placeBid" [sender, .var "value"] "ok",
                .ite (.var "ok")
                  [ .assign .localVar { base := "refund" }
                      (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
            .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]
          (.ok { contract := blindAuctionContract, locals := revealLoopStore ⟨0⟩ ⟨0⟩ } evm) := by
      exact ExecForLoop.falseDone
        (evalExpr_reveal_loop_cond_false evm (revealLoopStore ⟨0⟩ ⟨0⟩)
          (by native_decide) (by native_decide))
    exact ExecStmt.for hinit hloop
  refine ExecBlock.consNormal hfor ?_
  refine ExecBlock.consNormal
    (ExecStmt.lowLevelCallSuccess
      (evalExpr_reveal_sender evm (revealLoopStore ⟨0⟩ ⟨0⟩))
      (evalExpr_reveal_refund evm (revealLoopStore ⟨0⟩ ⟨0⟩) ⟨0⟩ (by native_decide))
      (evalExpr_reveal_emptyBytes evm (revealLoopStore ⟨0⟩ ⟨0⟩))
      hcall) ?_
  exact ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_reveal_success evm' ⟨0⟩ ⟨0⟩ true out))
    ExecBlock.nil

theorem blindAuctionRevealBodyReverts_empty_callFailure
    (evm evm' : EVM.State) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hafter :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbefore :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = ⟨0⟩)
    (hcall :
      callViaEVM evm (EVM.address evm.executionEnv.source) 0 ByteArray.empty
        (false, evm', out)) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm revealEmptyStore
      revealTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  unfold revealTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_afterBiddingEnd_true evm revealEmptyStore (by native_decide) hafter)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_beforeRevealEnd_true evm revealEmptyStore (by native_decide) hbefore)) ?_
  have hlengthEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := revealEmptyStore }
        evm (.arrayLength .storage (bidsRef sender)) = .ok (.int 0) := by
    exact evalExpr_reveal_bids_length_zero evm revealEmptyStore revealEmptyStore_bids_none hlen
  refine ExecBlock.consNormal (ExecStmt.letDecl hlengthEval) ?_
  change ExecBlock blindAuctionConfig
    { contract := blindAuctionContract, locals := revealLengthStore } evm
    (List.drop 4 revealTransition.body) .reverted
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_empty_length_eq_zero_var evm revealLengthStore "values"
        (by native_decide) (by native_decide))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_empty_length_eq_zero_var evm revealLengthStore "fakes"
        (by native_decide) (by native_decide))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_empty_length_eq_zero_var evm revealLengthStore "secrets"
        (by native_decide) (by native_decide))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (value := .int 0) (by simp [evalExpr?, pure])) ?_
  change ExecBlock blindAuctionConfig
    { contract := blindAuctionContract, locals := revealRefundStore ⟨0⟩ } evm
    (List.drop 8 revealTransition.body) .reverted
  have hfor :
      ExecStmt blindAuctionConfig
        { contract := blindAuctionContract, locals := revealRefundStore ⟨0⟩ } evm
        (.for [ .letDecl "i" (some uint256) (.intLit 0) ]
          (.binary .lt (.var "i") (.var "length"))
          [ .assign .localVar { base := "i" } (.binary .add (.var "i") (.intLit 1)) ]
          [ .letStorage "bidToCheck" (bidElemRef sender (.var "i")),
            .letDecl "value" (some uint256) (.index (.var "values") (.var "i")),
            .letDecl "fake" (some boolTy) (.index (.var "fakes") (.var "i")),
            .letDecl "secret" (some bytes32) (.index (.var "secrets") (.var "i")),
            .ite
              (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
                (.keccak256 (.abiEncodePacked
                  [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
              [.continue] [],
            .assign .localVar { base := "refund" }
              (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
            .ite
              (.binary .and (.unary .not (.var "fake"))
                (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
              [ .internalCall "placeBid" [sender, .var "value"] "ok",
                .ite (.var "ok")
                  [ .assign .localVar { base := "refund" }
                      (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
            .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ])
        (.ok { contract := blindAuctionContract, locals := revealLoopStore ⟨0⟩ ⟨0⟩ } evm) := by
    have hinit :
        ExecBlock blindAuctionConfig
          { contract := blindAuctionContract, locals := revealRefundStore ⟨0⟩ } evm
          [ .letDecl "i" (some uint256) (.intLit 0) ]
          (.ok { contract := blindAuctionContract, locals := revealLoopStore ⟨0⟩ ⟨0⟩ } evm) := by
      refine ExecBlock.consNormal
        (ExecStmt.letDecl (value := .int 0) (by simp [evalExpr?, pure])) ?_
      exact ExecBlock.nil
    have hloop :
        ExecForLoop blindAuctionConfig
          { contract := blindAuctionContract, locals := revealLoopStore ⟨0⟩ ⟨0⟩ } evm
          (.binary .lt (.var "i") (.var "length"))
          [ .assign .localVar { base := "i" } (.binary .add (.var "i") (.intLit 1)) ]
          [ .letStorage "bidToCheck" (bidElemRef sender (.var "i")),
            .letDecl "value" (some uint256) (.index (.var "values") (.var "i")),
            .letDecl "fake" (some boolTy) (.index (.var "fakes") (.var "i")),
            .letDecl "secret" (some bytes32) (.index (.var "secrets") (.var "i")),
            .ite
              (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
                (.keccak256 (.abiEncodePacked
                  [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
              [.continue] [],
            .assign .localVar { base := "refund" }
              (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
            .ite
              (.binary .and (.unary .not (.var "fake"))
                (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
              [ .internalCall "placeBid" [sender, .var "value"] "ok",
                .ite (.var "ok")
                  [ .assign .localVar { base := "refund" }
                      (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
            .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]
          (.ok { contract := blindAuctionContract, locals := revealLoopStore ⟨0⟩ ⟨0⟩ } evm) := by
      exact ExecForLoop.falseDone
        (evalExpr_reveal_loop_cond_false evm (revealLoopStore ⟨0⟩ ⟨0⟩)
          (by native_decide) (by native_decide))
    exact ExecStmt.for hinit hloop
  refine ExecBlock.consNormal hfor ?_
  refine ExecBlock.consNormal
    (ExecStmt.lowLevelCallFailure
      (evalExpr_reveal_sender evm (revealLoopStore ⟨0⟩ ⟨0⟩))
      (evalExpr_reveal_refund evm (revealLoopStore ⟨0⟩ ⟨0⟩) ⟨0⟩ (by native_decide))
      (evalExpr_reveal_emptyBytes evm (revealLoopStore ⟨0⟩ ⟨0⟩))
      hcall) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_reveal_success evm' ⟨0⟩ ⟨0⟩ false out))

theorem blindAuctionRevealBodyReverts_valuesLengthMismatch (evm : EVM.State)
    (callargs : Store) (values : List Value) (len : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbidding : callargs.get? biddingEndRef.base = none)
    (hreveal : callargs.get? revealEndRef.base = none)
    (hbids : callargs.get? "bids" = none)
    (hvalues : callargs.get? "values" = some (.array values))
    (hafter :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbefore :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hne : values.length ≠ len.toNat) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm callargs
      revealTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  unfold revealTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_afterBiddingEnd_true evm callargs hbidding hafter)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_beforeRevealEnd_true evm callargs hreveal hbefore)) ?_
  have hlengthEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := callargs }
        evm (.arrayLength .storage (bidsRef sender)) = .ok (.int (Int.ofNat len.toNat)) := by
    exact evalExpr_reveal_bids_length_any evm callargs len hbids hlen
  refine ExecBlock.consNormal (ExecStmt.letDecl hlengthEval) ?_
  change ExecBlock blindAuctionConfig
    { contract := blindAuctionContract,
      locals := callargs.insert "length" (.int (Int.ofNat len.toNat)) } evm
    (List.drop 4 revealTransition.body) .reverted
  refine ExecBlock.consRevert ?_
  refine ExecStmt.requireFalse ?_
  apply evalExpr_reveal_local_array_length_eq_var_false
  · rw [store_get_ne]
    · exact hvalues
    · decide
  · rw [store_get_self]
  · exact hne

theorem blindAuctionRevealBodyReverts_fakesLengthMismatch (evm : EVM.State)
    (callargs : Store) (values fakes : List Value) (len : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbidding : callargs.get? biddingEndRef.base = none)
    (hreveal : callargs.get? revealEndRef.base = none)
    (hbids : callargs.get? "bids" = none)
    (hvalues : callargs.get? "values" = some (.array values))
    (hfakes : callargs.get? "fakes" = some (.array fakes))
    (hafter :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbefore :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hvaluesLen : values.length = len.toNat)
    (hfakesNe : fakes.length ≠ len.toNat) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm callargs
      revealTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  unfold revealTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_afterBiddingEnd_true evm callargs hbidding hafter)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_beforeRevealEnd_true evm callargs hreveal hbefore)) ?_
  have hlengthEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := callargs } evm
        (.arrayLength .storage (bidsRef sender)) = .ok (.int (Int.ofNat len.toNat)) := by
    exact evalExpr_reveal_bids_length_any evm callargs len hbids hlen
  refine ExecBlock.consNormal (ExecStmt.letDecl hlengthEval) ?_
  change ExecBlock blindAuctionConfig
    { contract := blindAuctionContract,
      locals := callargs.insert "length" (.int (Int.ofNat len.toNat)) } evm
    (List.drop 4 revealTransition.body) .reverted
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_array_length_eq_var_true evm
        (callargs.insert "length" (.int (Int.ofNat len.toNat))) "values" values len
        (by
          rw [store_get_ne]
          · exact hvalues
          · decide)
        (by rw [store_get_self]) hvaluesLen)) ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.requireFalse ?_
  apply evalExpr_reveal_local_array_length_eq_var_false
  · rw [store_get_ne]
    · exact hfakes
    · decide
  · rw [store_get_self]
  · exact hfakesNe

theorem blindAuctionRevealBodyReverts_secretsLengthMismatch (evm : EVM.State)
    (callargs : Store) (values fakes secrets : List Value) (len : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbidding : callargs.get? biddingEndRef.base = none)
    (hreveal : callargs.get? revealEndRef.base = none)
    (hbids : callargs.get? "bids" = none)
    (hvalues : callargs.get? "values" = some (.array values))
    (hfakes : callargs.get? "fakes" = some (.array fakes))
    (hsecrets : callargs.get? "secrets" = some (.array secrets))
    (hafter :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbefore :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hvaluesLen : values.length = len.toNat)
    (hfakesLen : fakes.length = len.toNat)
    (hsecretsNe : secrets.length ≠ len.toNat) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm callargs
      revealTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  unfold revealTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_afterBiddingEnd_true evm callargs hbidding hafter)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_beforeRevealEnd_true evm callargs hreveal hbefore)) ?_
  have hlengthEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := callargs } evm
        (.arrayLength .storage (bidsRef sender)) = .ok (.int (Int.ofNat len.toNat)) := by
    exact evalExpr_reveal_bids_length_any evm callargs len hbids hlen
  refine ExecBlock.consNormal (ExecStmt.letDecl hlengthEval) ?_
  change ExecBlock blindAuctionConfig
    { contract := blindAuctionContract,
      locals := callargs.insert "length" (.int (Int.ofNat len.toNat)) } evm
    (List.drop 4 revealTransition.body) .reverted
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_array_length_eq_var_true evm
        (callargs.insert "length" (.int (Int.ofNat len.toNat))) "values" values len
        (by
          rw [store_get_ne]
          · exact hvalues
          · decide)
        (by rw [store_get_self]) hvaluesLen)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_array_length_eq_var_true evm
        (callargs.insert "length" (.int (Int.ofNat len.toNat))) "fakes" fakes len
        (by
          rw [store_get_ne]
          · exact hfakes
          · decide)
        (by rw [store_get_self]) hfakesLen)) ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.requireFalse ?_
  apply evalExpr_reveal_local_array_length_eq_var_false
  · rw [store_get_ne]
    · exact hsecrets
    · decide
  · rw [store_get_self]
  · exact hsecretsNe

theorem blindAuctionRevealBodyReverts_decoded_lengthMismatch
    (evm : EVM.State) {I : ExecutionEnv} {callargs : Store} {len : UInt256}
    {values fakes secrets : List Value}
    (hdec : decodeCalldata (revealTransition.params.map Param.name)
      (transitionSignature revealTransition).paramTypes I.calldata = some callargs)
    (hvalues : callargs.get? "values" = some (.array values))
    (hfakes : callargs.get? "fakes" = some (.array fakes))
    (hsecrets : callargs.get? "secrets" = some (.array secrets))
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hafter :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbefore :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hmismatch :
      values.length ≠ len.toNat ∨ fakes.length ≠ len.toNat ∨
        secrets.length ≠ len.toNat) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm callargs
      revealTransition.body .reverted := by
  have hbids : callargs.get? "bids" = none :=
    blindAuctionDecode_reveal_callargs_absent hdec (by decide) (by decide) (by decide)
  have hbidding : callargs.get? biddingEndRef.base = none :=
    blindAuctionDecode_reveal_callargs_absent hdec (by decide) (by decide) (by decide)
  have hreveal : callargs.get? revealEndRef.base = none :=
    blindAuctionDecode_reveal_callargs_absent hdec (by decide) (by decide) (by decide)
  by_cases hvaluesEq : values.length = len.toNat
  · by_cases hfakesEq : fakes.length = len.toNat
    · have hsecretsNe : secrets.length ≠ len.toNat := by
        rcases hmismatch with hvaluesNe | htail
        · exact False.elim (hvaluesNe hvaluesEq)
        · rcases htail with hfakesNe | hsecretsNe
          · exact False.elim (hfakesNe hfakesEq)
          · exact hsecretsNe
      exact blindAuctionRevealBodyReverts_secretsLengthMismatch evm callargs values fakes
        secrets len hwv hbidding hreveal hbids hvalues hfakes hsecrets hafter hbefore hlen
        hvaluesEq hfakesEq hsecretsNe
    · exact blindAuctionRevealBodyReverts_fakesLengthMismatch evm callargs values fakes len
        hwv hbidding hreveal hbids hvalues hfakes hafter hbefore hlen hvaluesEq hfakesEq
  · exact blindAuctionRevealBodyReverts_valuesLengthMismatch evm callargs values len hwv
      hbidding hreveal hbids hvalues hafter hbefore hlen hvaluesEq

end BlindAuction

/-! ### Ported reveal nonempty loop execution helpers -/


namespace BlindAuction

-- LIBRARY CANDIDATE: `Reasoning.Reach`.
-- Variant-indexed loop rule carrying stack, memory/active words, and account state.
theorem scratch_RD_whileLoopCarryAcc {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {rdata : ByteArray} {α : Type}
    (header exit : UInt256) (Inv : ℕ → α → Prop) (stk : α → List UInt256)
    (mem : α → ByteArray) (aw : α → UInt256)
    (acc : α → Batteries.RBSet AccountAddress compare × AccountMap)
    (exitStk : α → List UInt256)
    (hexit : ∀ a, Inv 0 a → ∀ k C,
        RD code ee g s0 header (stk a) (mem a) (aw a) rdata (acc a) k C →
        ∃ k' C', RD code ee g s0 exit (exitStk a) (mem a) (aw a) rdata (acc a) k' C')
    (hbody : ∀ v a, Inv (v + 1) a → ∀ k C,
        RD code ee g s0 header (stk a) (mem a) (aw a) rdata (acc a) k C →
        ∃ a' k' C',
          Inv v a' ∧
            RD code ee g s0 header (stk a') (mem a') (aw a') rdata (acc a') k' C') :
    ∀ v a, Inv v a → ∀ k C,
      RD code ee g s0 header (stk a) (mem a) (aw a) rdata (acc a) k C →
      ∃ a' k' C',
        Inv 0 a' ∧ RD code ee g s0 exit (exitStk a') (mem a') (aw a') rdata (acc a') k' C' := by
  intro v
  induction v with
  | zero =>
      intro a hInv k C h
      obtain ⟨k', C', h'⟩ := hexit a hInv k C h
      exact ⟨a, k', C', hInv, h'⟩
  | succ v ih =>
      intro a hInv k C h
      obtain ⟨a', k', C', hInv', h'⟩ := hbody v a hInv k C h
      exact ih a' hInv' k' C' h'

-- LIBRARY CANDIDATE: `Reasoning.SolmBody`.
-- Variant-indexed for-loop rule that carries both locals and EVM state.
theorem scratch_execFor_varEVM {cfg : Config} {C : ContractDecl}
    {condExpr : Expr} {post body : List Stmt}
    (P : ℕ → Solm.Store → EVM.State → Prop)
    (hfalse : ∀ L evm, P 0 L evm →
        evalExpr? cfg { contract := C, locals := L } evm condExpr = .ok (.bool false))
    (htrue : ∀ v L evm, P (v + 1) L evm →
        evalExpr? cfg { contract := C, locals := L } evm condExpr = .ok (.bool true))
    (hstep : ∀ v L evm, P (v + 1) L evm →
        ∃ L1 evm1, ExecBlock cfg { contract := C, locals := L } evm body
              (.ok { contract := C, locals := L1 } evm1) ∧
            ∃ L2 evm2, ExecBlock cfg { contract := C, locals := L1 } evm1 post
              (.ok { contract := C, locals := L2 } evm2) ∧ P v L2 evm2) :
    ∀ v L evm, P v L evm → ∃ L' evm',
      ExecForLoop cfg { contract := C, locals := L } evm condExpr post body
        (.ok { contract := C, locals := L' } evm') ∧ P 0 L' evm' := by
  intro v
  induction v with
  | zero =>
      intro L evm hP
      exact ⟨L, evm, ExecForLoop.falseDone (hfalse L evm hP), hP⟩
  | succ v ih =>
      intro L evm hP
      obtain ⟨L1, evm1, hbody, L2, evm2, hpost, hP1⟩ := hstep v L evm hP
      obtain ⟨L', evm', hloop, hP'⟩ := ih L2 evm2 hP1
      exact ⟨L', evm', ExecForLoop.iterate (htrue v L evm hP) hbody hpost hloop, hP'⟩

theorem scratch_blindAuctionRevealX_postCallEmpty_toRequire_general {I} {g : Sat256}
    {s0 : State} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    {z senderWord refund len revealEnd biddingEnd valuesLen valuesEnd fakesLen fakesEnd
      secretsLen secretsEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1350⟩
      [z, ⟨128⟩, refund, senderWord, ⟨0⟩, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw ByteArray.empty acc k C) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1405⟩
      [z, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw ByteArray.empty acc k' C' := by
  refine ⟨_, _, evm_run rd with [
    swap3, pop, pop, pop, returndatasize, dup1, push0, dup2, eq, push2 ⟨1395⟩,
    jumpiT (by decide) (by jump_dest), jumpdest, push1 ⟨96⟩, swap2, pop,
    jumpdest, pop, pop, swap1, pop]⟩

theorem scratch_blindAuctionRevealX_postCallEmpty_toRequire_freePtr {I} {g : Sat256}
    {s0 : State} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    {z senderWord refund len freePtr revealEnd biddingEnd valuesLen valuesEnd fakesLen fakesEnd
      secretsLen secretsEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1350⟩
      [z, freePtr, refund, senderWord, ⟨0⟩, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw ByteArray.empty acc k C) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1405⟩
      [z, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw ByteArray.empty acc k' C' := by
  refine ⟨_, _, evm_run rd with [
    swap3, pop, pop, pop, returndatasize, dup1, push0, dup2, eq, push2 ⟨1395⟩,
    jumpiT (by decide) (by jump_dest), jumpdest, push1 ⟨96⟩, swap2, pop,
    jumpdest, pop, pop, swap1, pop]⟩

set_option maxHeartbeats 1000000 in
theorem scratch_blindAuctionRevealX_postCallNonempty_toRequire_general {I} {g : Sat256}
    {s0 : State} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ} {z senderWord refund len revealEnd biddingEnd valuesLen valuesEnd fakesLen
      fakesEnd secretsLen secretsEnd sel : UInt256}
    {o : ByteArray}
    (rd : RD blindAuctionBytecode I g s0 ⟨1350⟩
      [z, ⟨128⟩, refund, senderWord, ⟨0⟩, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      (revealScratchBidsHashMem I) (UInt256.ofNat 3) o acc k C)
    (ho0 : o.size ≠ 0) (hosz : o.size < UInt256.size) :
    ∃ mem' aw' k' C', RD blindAuctionBytecode I g s0 ⟨1405⟩
      [z, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, sel]
      mem' aw' o acc k' C' := by
  let rdsz : UInt256 := UInt256.ofNat o.size
  have hrdsz_toNat : rdsz.toNat = o.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt hosz
  have hrdsz_ne : rdsz ≠ ⟨0⟩ := by
    intro h
    have hnat : rdsz.toNat = 0 := by rw [h]; rfl
    exact ho0 (by rwa [hrdsz_toNat] at hnat)
  have heq0 : UInt256.eq rdsz (⟨0⟩ : UInt256) = ⟨0⟩ := u256_eq_of_ne hrdsz_ne
  have rd1359₀ := evm_run rd with [swap3, pop, pop, pop, returndatasize, dup1, push0, dup2, eq]
  have rd1359 := rd1359₀
  change UInt256.eq rdsz (⟨0⟩ : UInt256) = ⟨0⟩ at heq0
  rw [show UInt256.ofNat o.size = rdsz from rfl, heq0] at rd1359
  have rd1363 := evm_run rd1359 with [push2 ⟨1395⟩, jumpiNT (by decide)]
  let rounded : UInt256 := UInt256.land (UInt256.add rdsz ⟨63⟩) (UInt256.lnot ⟨31⟩)
  let mem2 : ByteArray :=
    (UInt256.toByteArray (UInt256.add ⟨128⟩ rounded)).write 0
      (revealScratchBidsHashMem I) 64 32
  have rd1381 := evm_run rd1363 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost (revealScratchBidsHashMem_mload64 I) (by decide) (by evm_ov),
    swap2, pop, push1 ⟨31⟩, not, push1 ⟨63⟩, returndatasize, add, and, dup3, add,
    push1 ⟨64⟩,
    raw mstore 0 mem2 (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  let mem3 : ByteArray := (UInt256.toByteArray rdsz).write 0 mem2 128 32
  have rd1384 := evm_run rd1381 with [
    returndatasize, dup3,
    raw mstore (Cₘ (UInt256.ofNat 5) - Cₘ (UInt256.ofNat 3))
      mem3 (UInt256.ofNat 5) (by decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        decide)
      (by rfl) (by decide) (by evm_ov)]
  have rd1390 := evm_run rd1384 with [returndatasize, push0, push1 ⟨32⟩, dup5, add]
  let copyDest : UInt256 := (⟨128⟩ : UInt256) + ⟨32⟩
  let copyLen : UInt256 := UInt256.ofNat o.size
  have hcopyDest_toNat : copyDest.toNat = 160 := by
    decide
  have hcopyLen_toNat : copyLen.toNat = o.size := by
    simpa [copyLen] using UInt256.toNat_ofNat_of_lt hosz
  let mem4 : ByteArray := o.write 0 mem3 copyDest.toNat copyLen.toNat
  have haw4 :
      UInt256.ofNat (MachineState.M (UInt256.ofNat 5).toNat copyDest.toNat copyLen.toNat) =
        SimpleAuction.withdrawReturnDataActiveWords o := by
    simp [SimpleAuction.withdrawReturnDataActiveWords, copyDest, copyLen, hcopyDest_toNat,
      hcopyLen_toNat]
  have rd1391 := SimpleAuction.withdrawRDReturndatacopy
    (Cₘ (SimpleAuction.withdrawReturnDataActiveWords o) - Cₘ (UInt256.ofNat 5))
    mem4
    (SimpleAuction.withdrawReturnDataActiveWords o)
    rd1390 (by decide)
    (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, hcopyLen_toNat]; omega)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, copyDest, copyLen,
        SimpleAuction.withdrawReturnDataActiveWords, hcopyDest_toNat, hcopyLen_toNat])
    (by rfl)
    haw4
    (by evm_ov)
  have rd1400 := evm_run rd1391 with [push2 ⟨1400⟩, jump (by jump_dest), jumpdest]
  exact ⟨_, _, _, _, evm_run rd1400 with [pop, pop, swap1, pop]⟩

set_option maxHeartbeats 1000000 in
theorem scratch_blindAuctionRevealX_postCallNonempty_toRequire_freePtr {I} {g : Sat256}
    {s0 : State} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ} {z senderWord refund len freePtr revealEnd biddingEnd valuesLen valuesEnd fakesLen
      fakesEnd secretsLen secretsEnd sel : UInt256}
    {mem : ByteArray} {aw : UInt256} {o : ByteArray}
    (rd : RD blindAuctionBytecode I g s0 ⟨1350⟩
      [z, freePtr, refund, senderWord, ⟨0⟩, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw o acc k C)
    (ho0 : o.size ≠ 0) (hosz : o.size < UInt256.size)
    (hfree :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          (mem.readWithPadding (⟨64⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat))) =
        freePtr) :
    ∃ mem' aw' k' C', RD blindAuctionBytecode I g s0 ⟨1405⟩
      [z, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, sel]
      mem' aw' o acc k' C' := by
  let rdsz : UInt256 := UInt256.ofNat o.size
  have hrdsz_toNat : rdsz.toNat = o.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt hosz
  have hrdsz_ne : rdsz ≠ ⟨0⟩ := by
    intro h
    have hnat : rdsz.toNat = 0 := by rw [h]; rfl
    exact ho0 (by rwa [hrdsz_toNat] at hnat)
  have heq0 : UInt256.eq rdsz (⟨0⟩ : UInt256) = ⟨0⟩ := u256_eq_of_ne hrdsz_ne
  have rd1359₀ := evm_run rd with [swap3, pop, pop, pop, returndatasize, dup1, push0, dup2, eq]
  have rd1359 := rd1359₀
  change UInt256.eq rdsz (⟨0⟩ : UInt256) = ⟨0⟩ at heq0
  rw [show UInt256.ofNat o.size = rdsz from rfl, heq0] at rd1359
  have rd1363 := evm_run rd1359 with [push2 ⟨1395⟩, jumpiNT (by decide)]
  let rounded : UInt256 := UInt256.land (UInt256.add rdsz ⟨63⟩) (UInt256.lnot ⟨31⟩)
  let aw1 : UInt256 :=
    UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  let mem2 : ByteArray := (UInt256.toByteArray (UInt256.add freePtr rounded)).write 0 mem 64 32
  let aw2 : UInt256 :=
    UInt256.ofNat (MachineState.M aw1.toNat (⟨64⟩ : UInt256).toNat 32)
  have rd1381 := evm_run rd1363 with [
    push1 ⟨64⟩,
    raw mload (Cₘ aw1 - Cₘ aw) freePtr aw1 (by decide)
      (fun s haws hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk, aw1])
      hfree (by rfl) (by evm_ov),
    swap2, pop, push1 ⟨31⟩, not, push1 ⟨63⟩, returndatasize, add, and, dup3, add,
    push1 ⟨64⟩,
    raw mstore (Cₘ aw2 - Cₘ aw1) mem2 aw2 (by decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw2])
      (by rfl) (by rfl) (by evm_ov)]
  let mem3 : ByteArray := (UInt256.toByteArray rdsz).write 0 mem2 freePtr.toNat 32
  let aw3 : UInt256 := UInt256.ofNat (MachineState.M aw2.toNat freePtr.toNat 32)
  have rd1384 := evm_run rd1381 with [
    returndatasize, dup3,
    raw mstore (Cₘ aw3 - Cₘ aw2) mem3 aw3 (by decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw3])
      (by rfl) (by rfl) (by evm_ov)]
  have rd1390 := evm_run rd1384 with [returndatasize, push0, push1 ⟨32⟩, dup5, add]
  let copyDest : UInt256 := freePtr + ⟨32⟩
  let copyLen : UInt256 := UInt256.ofNat o.size
  have hcopyLen_toNat : copyLen.toNat = o.size := by
    simpa [copyLen] using UInt256.toNat_ofNat_of_lt hosz
  let mem4 : ByteArray := o.write 0 mem3 copyDest.toNat copyLen.toNat
  let aw4 : UInt256 := UInt256.ofNat (MachineState.M aw3.toNat copyDest.toNat copyLen.toNat)
  have rd1391 := SimpleAuction.withdrawRDReturndatacopy
    (Cₘ aw4 - Cₘ aw3) mem4 aw4
    rd1390 (by decide)
    (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, hcopyLen_toNat]; omega)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, copyDest, copyLen, aw4,
        hcopyLen_toNat])
    (by rfl) (by rfl) (by evm_ov)
  have rd1400 := evm_run rd1391 with [push2 ⟨1400⟩, jump (by jump_dest), jumpdest]
  exact ⟨_, _, _, _, evm_run rd1400 with [pop, pop, swap1, pop]⟩

theorem scratch_blindAuctionRevealX_loopExit_toCall {I} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : ℕ}
    {i refund len revealEnd biddingEnd valuesLen valuesEnd fakesLen fakesEnd secretsLen
      secretsEnd sel freePtr : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1331⟩
      [i, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C)
    (hfree :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          (mem.readWithPadding (⟨64⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat))) =
        freePtr)
    (hawM :
      UInt256.ofNat
        (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat) = aw) :
    ∃ gasArg k' C', RD blindAuctionBytecode I g s0 ⟨1349⟩
      [gasArg, revealScratchSenderWord I, refund, freePtr, ⟨0⟩, freePtr, ⟨0⟩,
        freePtr, refund, revealScratchSenderWord I, ⟨0⟩, refund, len,
        revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen,
        valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k' C' := by
  have hawM' :
      UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32) = aw := by
    simpa using hawM
  have rd1348₀ := evm_run rd with [
    jumpdest, pop, push1 ⟨64⟩,
    raw mload 0 freePtr aw
      (by decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        rw [hawM']
        simp)
      hfree
      hawM'
      (by simp),
    push0, swap1, caller, swap1, dup4, swap1, dup4, dup2, dup2, dup2, dup6, dup8]
  obtain ⟨gasArg, rd1349⟩ := rd1348₀.gas (by decide) (by evm_ov)
  exact ⟨gasArg, _, _, by simpa [revealScratchSenderWord] using rd1349⟩

def scratch_revealEvmLoopStack (i refund len revealEnd biddingEnd secretsLen secretsEnd
    fakesLen fakesEnd valuesLen valuesEnd sel : UInt256) : List UInt256 :=
  [i, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd,
    valuesLen, valuesEnd, ⟨276⟩, sel]

noncomputable def scratch_revealBidsArrayDataMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (revealScratchBidsLengthSlot I)).write 0
    (revealScratchBidsHashMem I) 0 32

theorem scratch_revealBidsArrayDataMem_size (I : ExecutionEnv) :
    (scratch_revealBidsArrayDataMem I).size = 96 := by
  unfold scratch_revealBidsArrayDataMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [revealScratchBidsHashMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, revealScratchBidsHashMem_size,
    toByteArray_size]
  omega

theorem scratch_revealBidsArrayDataMem_read0 (I : ExecutionEnv) :
    (scratch_revealBidsArrayDataMem I).readWithPadding 0 32 =
      UInt256.toByteArray (revealScratchBidsLengthSlot I) := by
  unfold scratch_revealBidsArrayDataMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by omega),
    show (UInt256.toByteArray (revealScratchBidsLengthSlot I)).extract 0 32 =
      UInt256.toByteArray (revealScratchBidsLengthSlot I) from by
        apply ByteArray.ext
        rw [ByteArray.data_extract]
        exact Array.extract_eq_self_of_le (by
          change (UInt256.toByteArray (revealScratchBidsLengthSlot I)).size ≤ 32
          rw [toByteArray_size])]

theorem scratch_revealBidsArrayDataMem_read64 (I : ExecutionEnv) :
    (scratch_revealBidsArrayDataMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold scratch_revealBidsArrayDataMem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by rw [revealScratchBidsHashMem_size]; omega) (by omega)
      (by rw [revealScratchBidsHashMem_size]),
    revealScratchBidsHashMem_read64]

theorem scratch_revealBidsArrayDataMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (scratch_revealBidsArrayDataMem I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((scratch_revealBidsArrayDataMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [scratch_revealBidsArrayDataMem_size]; decide) (by decide)
    (scratch_revealBidsArrayDataMem_read64 I)

theorem scratch_revealBidsArrayDataKeccak (I : ExecutionEnv) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((scratch_revealBidsArrayDataMem I).readWithPadding 0 32))) =
      uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (revealScratchBidsLengthSlot I))) := by
  rw [scratch_revealBidsArrayDataMem_read0]
  exact keccakSlot_eq _

theorem scratch_revealBidsElemSlot_eq (I : ExecutionEnv) (i : UInt256) :
    uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (revealScratchBidsLengthSlot I))) +
        UInt256.mul i ⟨2⟩ =
      bidsElemSlot (.address I.source) (.int (Int.ofNat i.toNat)) := by
  unfold revealScratchBidsLengthSlot bidsElemSlot
  rw [blindAuctionKeyValueToWord_int_ofNat_toNat]
  apply congrArg (fun x => x + UInt256.ofNat (i.toNat * 2)) rfl

end BlindAuction

namespace Reasoning.Theory

-- LIBRARY CANDIDATE: generic `DUP9` xstep, matching the existing `DUP` RD pattern.
theorem scratchDup9_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg h i : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP9, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: gg :: h :: i :: t)
    (hov : t.length + 10 ≤ 1024) :
    Xstep (D_J code 0) s =
      (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
       else .ok (stSwap s (i :: a :: b :: c :: d :: e :: f :: gg :: h :: i :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP9, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_dup9 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: h :: i :: t).length - 9 + 10 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

-- LIBRARY CANDIDATE: generic high `DUP13` xstep, matching `DUP10`/`DUP11`.
theorem scratchDup13_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg h i j k l m : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP13, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: k :: l :: m :: t)
    (hov : t.length + 14 ≤ 1024) :
    Xstep (D_J code 0) s =
      (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
       else .ok
        (stSwap s (m :: a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: k :: l :: m :: t),
          .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP13, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_dup13 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: k :: l :: m :: t).length -
          13 + 14 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

-- LIBRARY CANDIDATE: generic high `DUP14` xstep, matching `DUP10`/`DUP11`.
theorem scratchDup14_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg h i j k l m n : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP14, .none))
    (hstk : s.machineState.stack =
      a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: k :: l :: m :: n :: t)
    (hov : t.length + 15 ≤ 1024) :
    Xstep (D_J code 0) s =
      (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
       else .ok
        (stSwap s
          (n :: a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: k :: l :: m :: n :: t),
          .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP14, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_dup14 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: k :: l :: m :: n :: t).length -
          14 + 15 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

-- LIBRARY CANDIDATE: generic high `DUP15` xstep, matching `DUP10`/`DUP11`.
theorem scratchDup15_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg h i j k l m n o : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP15, .none))
    (hstk : s.machineState.stack =
      a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: k :: l :: m :: n :: o :: t)
    (hov : t.length + 16 ≤ 1024) :
    Xstep (D_J code 0) s =
      (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
       else .ok
        (stSwap s
          (o :: a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: k :: l :: m :: n :: o :: t),
          .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP15, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_dup15 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: k :: l :: m :: n :: o :: t).length -
          15 + 16 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

end Reasoning.Theory

namespace Reasoning.Reach

-- LIBRARY CANDIDATE: generic `RD.dup9`, matching `RD.dup10`/`RD.dup11`.
theorem RD.dup9 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg h i : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: h :: i :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP9, .none)) (hov : t.length + 10 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (i :: a :: b :: c :: d :: e :: f :: gg :: h :: i :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => Reasoning.Theory.scratchDup9_xstep hc hp hdec hs hov)

-- LIBRARY CANDIDATE: generic high `RD.dup13`, matching `RD.dup10`/`RD.dup11`.
theorem RD.dup13 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg h i j l m n : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: l :: m :: n :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP13, .none)) (hov : t.length + 14 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (n :: a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: l :: m :: n :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => Reasoning.Theory.scratchDup13_xstep hc hp hdec hs hov)

-- LIBRARY CANDIDATE: generic high `RD.dup14`, matching `RD.dup10`/`RD.dup11`.
theorem RD.dup14 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg h i j l m n o : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: l :: m :: n :: o :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP14, .none)) (hov : t.length + 15 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (o :: a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: l :: m :: n :: o :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => Reasoning.Theory.scratchDup14_xstep hc hp hdec hs hov)

-- LIBRARY CANDIDATE: generic high `RD.dup15`, matching `RD.dup10`/`RD.dup11`.
theorem RD.dup15 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg h i j l m n o p : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: l :: m :: n :: o :: p :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP15, .none)) (hov : t.length + 16 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (p :: a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: l :: m :: n :: o :: p :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => Reasoning.Theory.scratchDup15_xstep hc hp hdec hs hov)

end Reasoning.Reach

namespace BlindAuction

theorem scratch_blindAuctionRevealX_loopCond_exit {I} {g : Sat256} {s0 : State}
    {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen
      valuesEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1014⟩
      (scratch_revealEvmLoopStack i refund len revealEnd biddingEnd secretsLen secretsEnd
        fakesLen fakesEnd valuesLen valuesEnd sel)
      mem aw rdata acc k C)
    (hbound : len.toNat ≤ i.toNat) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1331⟩
      (scratch_revealEvmLoopStack i refund len revealEnd biddingEnd secretsLen secretsEnd
        fakesLen fakesEnd valuesLen valuesEnd sel)
      mem aw rdata acc k' C' := by
  have hlt : UInt256.lt i len = ⟨0⟩ := ult_zero hbound
  have rd' : RD blindAuctionBytecode I g s0 ⟨1014⟩
      [i, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C := by
    simpa [scratch_revealEvmLoopStack] using rd
  have rd1019₀ := evm_run rd' with [jumpdest, dup3, dup2, lt, iszero]
  have rd1019 := rd1019₀
  rw [hlt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by decide] at rd1019
  exact ⟨_, _, by
    simpa [scratch_revealEvmLoopStack] using
      (evm_run rd1019 with [push2 ⟨1331⟩, jumpiT one_ne_zero_uint (by jump_dest)])⟩

theorem scratch_blindAuctionRevealX_loop_from_body {I} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {α : Type}
    (len revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd
      sel : UInt256)
    (Inv : ℕ → α → Prop) (idx refund : α → UInt256)
    (mem : α → ByteArray) (aw : α → UInt256)
    (acc : α → Batteries.RBSet AccountAddress compare × AccountMap)
    (hvariant : ∀ v a, Inv v a → (idx a).toNat + v = len.toNat ∧
      (idx a).toNat ≤ len.toNat)
    (hbody : ∀ v a, Inv (v + 1) a → ∀ k C,
        RD blindAuctionBytecode I g s0 ⟨1023⟩
          (scratch_revealEvmLoopStack (idx a) (refund a) len revealEnd biddingEnd
            secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
          (mem a) (aw a) rdata (acc a) k C →
        ∃ a' k' C',
          Inv v a' ∧
          RD blindAuctionBytecode I g s0 ⟨1014⟩
            (scratch_revealEvmLoopStack (idx a') (refund a') len revealEnd biddingEnd
              secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
            (mem a') (aw a') rdata (acc a') k' C') :
    ∀ v a, Inv v a → ∀ k C,
      RD blindAuctionBytecode I g s0 ⟨1014⟩
        (scratch_revealEvmLoopStack (idx a) (refund a) len revealEnd biddingEnd
          secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
        (mem a) (aw a) rdata (acc a) k C →
      ∃ a' k' C',
        Inv 0 a' ∧
        RD blindAuctionBytecode I g s0 ⟨1331⟩
          (scratch_revealEvmLoopStack (idx a') (refund a') len revealEnd biddingEnd
            secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
          (mem a') (aw a') rdata (acc a') k' C' := by
  refine scratch_RD_whileLoopCarryAcc (code := blindAuctionBytecode) (ee := I) (g := g)
    (s0 := s0) (rdata := rdata) (header := ⟨1014⟩) (exit := ⟨1331⟩)
    (Inv := Inv)
    (stk := fun a =>
      scratch_revealEvmLoopStack (idx a) (refund a) len revealEnd biddingEnd secretsLen
        secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
    (mem := mem) (aw := aw) (acc := acc)
    (exitStk := fun a =>
      scratch_revealEvmLoopStack (idx a) (refund a) len revealEnd biddingEnd secretsLen
        secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel) ?_ ?_
  · intro a hInv k C rd
    rcases hvariant 0 a hInv with ⟨hvar, _hle⟩
    exact scratch_blindAuctionRevealX_loopCond_exit rd (by omega)
  · intro v a hInv k C rd
    rcases hvariant (v + 1) a hInv with ⟨hvar, _hle⟩
    obtain ⟨k1, C1, rd1023⟩ := blindAuctionRevealX_loopCond_taken
      (I := I) (g := g) (s0 := s0) (k := k) (C := C)
      (mem := mem a) (aw := aw a) (rdata := rdata) (acc := acc a)
      (i := idx a) (refund := refund a) (len := len) (revealEnd := revealEnd)
      (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
      (valuesEnd := valuesEnd) (sel := sel) (by simpa [scratch_revealEvmLoopStack] using rd)
      (by omega)
    exact hbody v a hInv k1 C1 (by simpa [scratch_revealEvmLoopStack] using rd1023)

theorem scratch_blindAuctionRevealX_loopBody_toElemSlot {I} {g : Sat256} {s0 : State}
    {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen
      valuesEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1023⟩
      (scratch_revealEvmLoopStack i refund len revealEnd biddingEnd secretsLen secretsEnd
        fakesLen fakesEnd valuesLen valuesEnd sel)
      mem aw rdata acc k C)
    (haw0 : UInt256.ofNat (MachineState.M aw.toNat 0 32) = aw)
    (haw32 : UInt256.ofNat (MachineState.M aw.toNat 32 32) = aw)
    (haw64 : UInt256.ofNat (MachineState.M aw.toNat 0 64) = aw)
    (hbaseHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC
          (((UInt256.toByteArray (⟨4⟩ : UInt256)).write 0
            ((UInt256.toByteArray (revealScratchSenderWord I)).write 0 mem 0 32)
              32 32).readWithPadding 0 64))) =
        revealScratchBidsLengthSlot I)
    (hlenLoad :
      (acc.2.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (revealScratchBidsLengthSlot I) ⟨0⟩) = len)
    (hbound : i.toNat < len.toNat)
    (hdataHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC
          (((UInt256.toByteArray (revealScratchBidsLengthSlot I)).write 0
            ((UInt256.toByteArray (⟨4⟩ : UInt256)).write 0
              ((UInt256.toByteArray (revealScratchSenderWord I)).write 0 mem 0 32)
              32 32) 0 32).readWithPadding 0 32))) =
        uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (revealScratchBidsLengthSlot I)))) :
    ∃ mem' aw' k' C', RD blindAuctionBytecode I g s0 ⟨1069⟩
      [bidsElemSlot (.address I.source) (.int (Int.ofNat i.toNat)), i, refund, len, revealEnd,
        biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem' aw' rdata acc k' C' := by
  let mem1 : ByteArray := (UInt256.toByteArray (revealScratchSenderWord I)).write 0 mem 0 32
  let mem2 : ByteArray := (UInt256.toByteArray (⟨4⟩ : UInt256)).write 0 mem1 32 32
  let mem3 : ByteArray := (UInt256.toByteArray (revealScratchBidsLengthSlot I)).write 0 mem2 0 32
  have rd' : RD blindAuctionBytecode I g s0 ⟨1023⟩
      [i, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C := by
    simpa [scratch_revealEvmLoopStack] using rd
  have rd1027 := evm_run rd' with [
    caller, push0, swap1, dup2,
    raw mstore 0 mem1 aw (by decide)
      (fun s haws hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
        rw [haw0]
        simp)
      (by rfl) haw0 (by evm_ov)]
  have rd1033 := evm_run rd1027 with [
    push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0 mem2 aw (by decide)
      (fun s haws hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
        rw [show (⟨32⟩ : UInt256).toNat = 32 by native_decide]
        rw [haw32]
        simp)
      (by rfl) haw32 (by evm_ov),
    push1 ⟨64⟩, dup2,
    raw keccak256 0 (revealScratchBidsLengthSlot I) aw (by decide)
      (fun s haws hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
        rw [show (⟨64⟩ : UInt256).toNat = 64 by native_decide]
        rw [haw64]
        simp)
      (by simpa [mem2, mem1, revealScratchSenderWord] using hbaseHash) haw64
      (by evm_ov),
    dup1]
  obtain ⟨_, _, rd1039₀⟩ := rd1033.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1039⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1039⟩
      [len, revealScratchBidsLengthSlot I, ⟨0⟩, i, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem2 aw rdata acc k' C' := by
    exact ⟨_, _, by simpa [hlenLoad] using rd1039₀⟩
  have hlt : UInt256.lt i len = ⟨1⟩ := ult_one hbound
  have rd1047₀ := evm_run rd1039 with [dup4, swap1, dup2, lt]
  have rd1047 := rd1047₀
  rw [hlt] at rd1047
  have rd1054 := evm_run rd1047 with [
    push2 ⟨1054⟩, jumpiT one_ne_zero_uint (by jump_dest), jumpdest]
  have rd1062 := evm_run rd1054 with [
    swap1, push0,
    raw mstore 0 mem3 aw (by decide)
      (fun s haws hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
        rw [haw0]
        simp)
      (by rfl) haw0 (by evm_ov),
    push1 ⟨32⟩, push0,
    raw keccak256 0
      (uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (revealScratchBidsLengthSlot I))))
      aw (by decide)
      (fun s haws hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
        rw [show (⟨32⟩ : UInt256).toNat = 32 by native_decide]
        rw [haw0]
        simp)
      (by simpa [mem3, mem2, mem1, revealScratchSenderWord] using hdataHash) haw0
      (by evm_ov)]
  have hslot :
      UInt256.mul ⟨2⟩ i +
          uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (revealScratchBidsLengthSlot I))) =
        bidsElemSlot (.address I.source) (.int (Int.ofNat i.toNat)) := by
    have hmul : UInt256.mul ⟨2⟩ i = UInt256.mul i ⟨2⟩ := by
      apply u256_inj
      show ((⟨2⟩ : UInt256).val * i.val).val = (i.val * (⟨2⟩ : UInt256).val).val
      rw [Fin.val_mul, Fin.val_mul, Nat.mul_comm]
    rw [hmul]
    rw [blindAuctionU256_add_comm]
    exact scratch_revealBidsElemSlot_eq I i
  have rd1069 := evm_run rd1062 with [swap1, push1 ⟨2⟩, mul, add, swap1, pop]
  have hpc1069 :
      (⟨1054⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ :
          UInt256) = ⟨1069⟩ := by
    native_decide
  exact ⟨mem3, aw, _, _, by simpa [hslot, hpc1069] using rd1069⟩

theorem scratch_RD_decodeRawBool_zero {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {start endOffset ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    (rd : RD blindAuctionBytecode I g s0 ⟨1987⟩ (start :: endOffset :: ret :: R)
      mem aw rdata acc k C)
    (hslt : UInt256.slt (UInt256.sub endOffset start) ⟨32⟩ = ⟨0⟩)
    (hword : uInt256OfByteArray (I.calldata.readBytes start.toNat 32) = ⟨0⟩)
    (hret : (D_J blindAuctionBytecode 0).contains ret = true)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ret (⟨0⟩ :: R)
      mem aw rdata acc k' C' := by
  have rd2003 := evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero,
    push2 ⟨2003⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, dup2, calldataload, dup1, iszero, iszero, dup2, eq]
  have rd2003' := rd2003
  rw [hword] at rd2003'
  have rd2018 := evm_run rd2003' with [
    push2 ⟨2018⟩, jumpiT (by decide) (by jump_dest), jumpdest]
  exact ⟨_, _, evm_run rd2018 with [swap4, swap3, pop, pop, pop, jump hret]⟩

theorem scratch_RD_decodeRawBool_one {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {start endOffset ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    (rd : RD blindAuctionBytecode I g s0 ⟨1987⟩ (start :: endOffset :: ret :: R)
      mem aw rdata acc k C)
    (hslt : UInt256.slt (UInt256.sub endOffset start) ⟨32⟩ = ⟨0⟩)
    (hword : uInt256OfByteArray (I.calldata.readBytes start.toNat 32) = ⟨1⟩)
    (hret : (D_J blindAuctionBytecode 0).contains ret = true)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ret (⟨1⟩ :: R)
      mem aw rdata acc k' C' := by
  have rd2003 := evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero,
    push2 ⟨2003⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, dup2, calldataload, dup1, iszero, iszero, dup2, eq]
  have rd2003' := rd2003
  rw [hword] at rd2003'
  have rd2018 := evm_run rd2003' with [
    push2 ⟨2018⟩, jumpiT (by decide) (by jump_dest), jumpdest]
  exact ⟨_, _, evm_run rd2018 with [swap4, swap3, pop, pop, pop, jump hret]⟩

theorem scratch_RD_decodeRawBool_invalid_revert {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {start endOffset ret word : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    (rd : RD blindAuctionBytecode I g s0 ⟨1987⟩ (start :: endOffset :: ret :: R)
      mem aw rdata acc k C)
    (hslt : UInt256.slt (UInt256.sub endOffset start) ⟨32⟩ = ⟨0⟩)
    (hword : uInt256OfByteArray (I.calldata.readBytes start.toNat 32) = word)
    (hzero : word ≠ ⟨0⟩)
    (hone : word ≠ ⟨1⟩)
    (hov : R.length + 10 ≤ 1024) :
    RDrev blindAuctionBytecode g s0 := by
  have hboolWord :
      UInt256.eq word (UInt256.isZero (UInt256.isZero word)) = ⟨0⟩ := by
    have hz : UInt256.isZero word = ⟨0⟩ := isZero_eq_zero_of_ne hzero
    have ho : UInt256.isZero (UInt256.isZero word) = ⟨1⟩ := by
      rw [hz]
      rfl
    rw [ho]
    exact u256_eq_of_ne hone
  have rd2003 := evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero,
    push2 ⟨2003⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, dup2, calldataload, dup1, iszero, iszero, dup2, eq]
  have rd2003' := rd2003
  rw [hword, hboolWord] at rd2003'
  have rd2015 := evm_run rd2003' with [push2 ⟨2018⟩, jumpiNT (by decide)]
  exact rd2015.revertStub (by decide) (by decide) (by decide) (by simp; omega)

set_option maxHeartbeats 2000000 in
theorem scratch_blindAuctionRevealX_loopBody_loads_toFakeDecoder {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen
      valuesEnd sel value : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1069⟩
      [slot, i, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen,
        fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C)
    (hvalueBound : i.toNat < valuesLen.toNat)
    (hfakesBound : i.toNat < fakesLen.toNat)
    (hvalueLoad :
      uInt256OfByteArray
          (I.calldata.readBytes (UInt256.mul ⟨32⟩ i + valuesEnd).toNat 32) =
        value) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1987⟩
      [UInt256.mul ⟨32⟩ i + fakesEnd, UInt256.mul ⟨32⟩ i + fakesEnd + ⟨32⟩, ⟨1135⟩,
        value, ⟨0⟩, ⟨0⟩, ⟨0⟩, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k' C' := by
  have hvalueLt : UInt256.lt i valuesLen = ⟨1⟩ := ult_one hvalueBound
  have rd1078₀ := evm_run rd with [
    push0, push0, push0, dup15, dup15, dup7, dup2, dup2, lt]
  have rd1078 := rd1078₀
  rw [hvalueLt] at rd1078
  have rd1096₀ := evm_run rd1078 with [
    push2 ⟨1089⟩, jumpiT one_ne_zero_uint (by jump_dest), jumpdest, swap1, pop,
    push1 ⟨32⟩, mul, add, calldataload]
  have rd1096 := rd1096₀
  rw [hvalueLoad] at rd1096
  have hfakesLt : UInt256.lt i fakesLen = ⟨1⟩ := ult_one hfakesBound
  have rd1102₀ := evm_run rd1096 with [dup14, dup14, dup8, dup2, dup2, lt]
  have rd1102 := rd1102₀
  rw [hfakesLt] at rd1102
  have rd1134 := evm_run rd1102 with [
    push2 ⟨1114⟩, jumpiT one_ne_zero_uint (by jump_dest), jumpdest, swap1, pop,
    push1 ⟨32⟩, mul, add, push1 ⟨32⟩, dup2, add, swap1, push2 ⟨1135⟩, swap2,
    swap1, push2 ⟨1987⟩, jump (by jump_dest)]
  exact ⟨_, _, by simpa using rd1134⟩

set_option maxHeartbeats 3000000 in
theorem scratch_blindAuctionRevealX_loopBody_fakeDecoder_zero_toBool {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen
      valuesEnd sel value : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1987⟩
      [UInt256.mul ⟨32⟩ i + fakesEnd, UInt256.mul ⟨32⟩ i + fakesEnd + ⟨32⟩, ⟨1135⟩,
        value, ⟨0⟩, ⟨0⟩, ⟨0⟩, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C)
    (hfakeSlt :
      UInt256.slt
          (UInt256.sub
            (UInt256.mul ⟨32⟩ i + fakesEnd + ⟨32⟩)
            (UInt256.mul ⟨32⟩ i + fakesEnd)) ⟨32⟩ = ⟨0⟩)
    (hfakeLoad :
      uInt256OfByteArray
          (I.calldata.readBytes (UInt256.mul ⟨32⟩ i + fakesEnd).toNat 32) = ⟨0⟩) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1135⟩
      [⟨0⟩, value, ⟨0⟩, ⟨0⟩, ⟨0⟩, slot, i, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k' C' := by
  have rd2003 := evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero,
    push2 ⟨2003⟩, jumpiT (by rw [hfakeSlt]; decide) (by jump_dest),
    jumpdest, dup2, calldataload, dup1, iszero, iszero, dup2, eq]
  have rd2003' := rd2003
  rw [hfakeLoad] at rd2003'
  have rd2018 := evm_run rd2003' with [
    push2 ⟨2018⟩, jumpiT (by decide) (by jump_dest), jumpdest]
  exact ⟨_, _, evm_run rd2018 with [swap4, swap3, pop, pop, pop, jump (by jump_dest)]⟩

set_option maxHeartbeats 3000000 in
theorem scratch_blindAuctionRevealX_loopBody_fakeDecoder_one_toBool {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen
      valuesEnd sel value : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1987⟩
      [UInt256.mul ⟨32⟩ i + fakesEnd, UInt256.mul ⟨32⟩ i + fakesEnd + ⟨32⟩, ⟨1135⟩,
        value, ⟨0⟩, ⟨0⟩, ⟨0⟩, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C)
    (hfakeSlt :
      UInt256.slt
          (UInt256.sub
            (UInt256.mul ⟨32⟩ i + fakesEnd + ⟨32⟩)
            (UInt256.mul ⟨32⟩ i + fakesEnd)) ⟨32⟩ = ⟨0⟩)
    (hfakeLoad :
      uInt256OfByteArray
          (I.calldata.readBytes (UInt256.mul ⟨32⟩ i + fakesEnd).toNat 32) = ⟨1⟩) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1135⟩
      [⟨1⟩, value, ⟨0⟩, ⟨0⟩, ⟨0⟩, slot, i, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k' C' := by
  have rd2003 := evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero,
    push2 ⟨2003⟩, jumpiT (by rw [hfakeSlt]; decide) (by jump_dest),
    jumpdest, dup2, calldataload, dup1, iszero, iszero, dup2, eq]
  have rd2003' := rd2003
  rw [hfakeLoad] at rd2003'
  have rd2018 := evm_run rd2003' with [
    push2 ⟨2018⟩, jumpiT (by decide) (by jump_dest), jumpdest]
  exact ⟨_, _, evm_run rd2018 with [swap4, swap3, pop, pop, pop, jump (by jump_dest)]⟩

set_option maxHeartbeats 3000000 in
theorem scratch_blindAuctionRevealX_loopBody_fakeDecoder_invalid_revert {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen
      valuesEnd sel value word : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1987⟩
      [UInt256.mul ⟨32⟩ i + fakesEnd, UInt256.mul ⟨32⟩ i + fakesEnd + ⟨32⟩, ⟨1135⟩,
        value, ⟨0⟩, ⟨0⟩, ⟨0⟩, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C)
    (hfakeSlt :
      UInt256.slt
          (UInt256.sub
            (UInt256.mul ⟨32⟩ i + fakesEnd + ⟨32⟩)
            (UInt256.mul ⟨32⟩ i + fakesEnd)) ⟨32⟩ = ⟨0⟩)
    (hfakeLoad :
      uInt256OfByteArray
          (I.calldata.readBytes (UInt256.mul ⟨32⟩ i + fakesEnd).toNat 32) = word)
    (hzero : word ≠ ⟨0⟩)
    (hone : word ≠ ⟨1⟩) :
    RDrev blindAuctionBytecode g s0 := by
  have hboolWord :
      UInt256.eq word (UInt256.isZero (UInt256.isZero word)) = ⟨0⟩ := by
    have hz : UInt256.isZero word = ⟨0⟩ := isZero_eq_zero_of_ne hzero
    have ho : UInt256.isZero (UInt256.isZero word) = ⟨1⟩ := by
      rw [hz]
      rfl
    rw [ho]
    exact u256_eq_of_ne hone
  have rd2003 := evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero,
    push2 ⟨2003⟩, jumpiT (by rw [hfakeSlt]; decide) (by jump_dest),
    jumpdest, dup2, calldataload, dup1, iszero, iszero, dup2, eq]
  have rd2003' := rd2003
  rw [hfakeLoad, hboolWord] at rd2003'
  have rd2015 := evm_run rd2003' with [push2 ⟨2018⟩, jumpiNT (by decide)]
  exact rd2015.revertStub (by decide) (by decide) (by decide) (by simp)

set_option maxHeartbeats 2000000 in
theorem scratch_blindAuctionRevealX_loopBody_secret_toPacked {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {fakeWord value slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd
      valuesLen valuesEnd sel secret : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1135⟩
      [fakeWord, value, ⟨0⟩, ⟨0⟩, ⟨0⟩, slot, i, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C)
    (hsecretsBound : i.toNat < secretsLen.toNat)
    (hsecretLoad :
      uInt256OfByteArray
          (I.calldata.readBytes (UInt256.mul ⟨32⟩ i + secretsEnd).toNat 32) =
        secret) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1167⟩
      [secret, fakeWord, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k' C' := by
  have hsecretsLt : UInt256.lt i secretsLen = ⟨1⟩ := ult_one hsecretsBound
  have rd1141₀ := evm_run rd with [jumpdest, dup13, dup13, dup9, dup2, dup2, lt]
  have rd1141 := rd1141₀
  rw [hsecretsLt] at rd1141
  have rd1160₀ := evm_run rd1141 with [
    push2 ⟨1153⟩, jumpiT one_ne_zero_uint (by jump_dest), jumpdest, swap1, pop,
    push1 ⟨32⟩, mul, add, calldataload]
  have rd1160 := rd1160₀
  rw [hsecretLoad] at rd1160
  have rd1167 := evm_run rd1160 with [swap3, pop, swap3, pop, swap3, pop]
  exact ⟨_, _, by simpa using rd1167⟩

noncomputable def scratch_revealPackedValueMem (mem : ByteArray) (base value : UInt256) :
    ByteArray :=
  (UInt256.toByteArray value).write 0 mem base.toNat 32

noncomputable def scratch_revealPackedFakeMem (mem : ByteArray) (base fakeWord : UInt256) :
    ByteArray :=
  (UInt256.toByteArray (UInt256.shiftLeft (UInt256.isZero (UInt256.isZero fakeWord)) ⟨248⟩)).write
    0 mem base.toNat 32

noncomputable def scratch_revealPackedSecretMem (mem : ByteArray) (base secret : UInt256) :
    ByteArray :=
  (UInt256.toByteArray secret).write 0 mem base.toNat 32

noncomputable def scratch_revealPackedLenMem (mem : ByteArray) (base len : UInt256) :
    ByteArray :=
  (UInt256.toByteArray len).write 0 mem base.toNat 32

noncomputable def scratch_revealPackedFreePtrMem (mem : ByteArray) (freePtr : UInt256) :
    ByteArray :=
  (UInt256.toByteArray freePtr).write 0 mem 64 32

set_option maxHeartbeats 1200000 in
theorem scratch_blindAuctionRevealX_loopBody_packed_prefix {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {secret fakeWord value slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen
      fakesEnd valuesLen valuesEnd sel fp : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1167⟩
      [secret, fakeWord, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C)
    (hfp :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = fp) :
    ∃ k' C',
      let aw1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
      let base := (⟨32⟩ : UInt256) + fp
      let fakeBase := base + ⟨32⟩
      let secretBase := base + ⟨33⟩
      let newFree := (⟨65⟩ : UInt256) + base
      let mem1 := scratch_revealPackedValueMem mem base value
      let aw2 := UInt256.ofNat (MachineState.M aw1.toNat base.toNat 32)
      let mem2 := scratch_revealPackedFakeMem mem1 fakeBase fakeWord
      let aw3 := UInt256.ofNat (MachineState.M aw2.toNat fakeBase.toNat 32)
      let mem3 := scratch_revealPackedSecretMem mem2 secretBase secret
      let aw4 := UInt256.ofNat (MachineState.M aw3.toNat secretBase.toNat 32)
      RD blindAuctionBytecode I g s0 ⟨1207⟩
        [newFree, secret, fakeWord, value, slot, i, refund, len, revealEnd, biddingEnd,
          secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
        mem3 aw4 rdata acc k' C' := by
  let aw1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  let base := (⟨32⟩ : UInt256) + fp
  let fakeBase := base + ⟨32⟩
  let secretBase := base + ⟨33⟩
  let newFree := (⟨65⟩ : UInt256) + base
  let mem1 := scratch_revealPackedValueMem mem base value
  let aw2 := UInt256.ofNat (MachineState.M aw1.toNat base.toNat 32)
  let mem2 := scratch_revealPackedFakeMem mem1 fakeBase fakeWord
  let aw3 := UInt256.ofNat (MachineState.M aw2.toNat fakeBase.toNat 32)
  let mem3 := scratch_revealPackedSecretMem mem2 secretBase secret
  let aw4 := UInt256.ofNat (MachineState.M aw3.toNat secretBase.toNat 32)
  have rd1185 := evm_run rd with [
    dup3, dup3, dup3, push1 ⟨64⟩,
    raw mload (Cₘ aw1 - Cₘ aw) fp aw1 (by decide)
      (fun s haws hstks => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, aw1])
      hfp (by rfl) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨1207⟩, swap4, swap3, swap2, swap1, swap3, dup4,
    raw mstore (Cₘ aw2 - Cₘ aw1) mem1 aw2 (by decide)
      (fun s haws hstks => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, base, aw2])
      (by rfl) (by rfl) (by evm_ov)]
  have rd1207 := evm_run rd1185 with [
    swap1, iszero, iszero, push1 ⟨248⟩, shl, push1 ⟨32⟩, dup4, add,
    raw mstore (Cₘ aw3 - Cₘ aw2) mem2 aw3 (by decide)
      (fun s haws hstks => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, base, fakeBase,
          aw3])
      (by rfl) (by rfl) (by evm_ov),
    push1 ⟨33⟩, dup3, add,
    raw mstore (Cₘ aw4 - Cₘ aw3) mem3 aw4 (by decide)
      (fun s haws hstks => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, base, secretBase,
          aw4])
      (by rfl) (by rfl) (by evm_ov),
    push1 ⟨65⟩, add, swap1, jump (by jump_dest)]
  exact ⟨_, _, by
    simpa [aw1, base, fakeBase, secretBase, newFree, mem1, mem2, mem3, aw2, aw3, aw4]
      using rd1207⟩

set_option maxHeartbeats 1200000 in
theorem scratch_blindAuctionRevealX_loopBody_packed_suffix {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {secret fakeWord value slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen
      fakesEnd valuesLen valuesEnd sel fp hash blinded flag : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1207⟩
      [((⟨65⟩ : UInt256) + ((⟨32⟩ : UInt256) + fp)), secret, fakeWord, value, slot,
        i, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen,
        fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hfp :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = fp)
    (hlen :
      let base := (⟨32⟩ : UInt256) + fp
      let newFree := (⟨65⟩ : UInt256) + base
      let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
      let mem4 := scratch_revealPackedLenMem mem fp packedLen
      let aw1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
      let aw2 := UInt256.ofNat (MachineState.M aw1.toNat fp.toNat 32)
      let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
      let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨64⟩ : UInt256).toNat 32)
      (if fp.toNat ≥ mem5.size ∨ fp ≥ aw3 * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem5.readWithPadding fp.toNat 32))) =
        packedLen)
    (hhash :
      let base := (⟨32⟩ : UInt256) + fp
      let newFree := (⟨65⟩ : UInt256) + base
      let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
      let mem4 := scratch_revealPackedLenMem mem fp packedLen
      let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
      UInt256.ofNat
          (fromByteArrayBigEndian (ffi.KEC (mem5.readWithPadding base.toNat packedLen.toNat))) =
        hash)
    (hstore :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD ((⟨0⟩ : UInt256) + slot) ⟨0⟩) = blinded)
    (hflag : UInt256.eq blinded hash = flag) :
    ∃ k' C',
      let base := (⟨32⟩ : UInt256) + fp
      let newFree := (⟨65⟩ : UInt256) + base
      let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
      let mem4 := scratch_revealPackedLenMem mem fp packedLen
      let aw1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
      let aw2 := UInt256.ofNat (MachineState.M aw1.toNat fp.toNat 32)
      let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
      let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨64⟩ : UInt256).toNat 32)
      let aw4 := UInt256.ofNat (MachineState.M aw3.toNat fp.toNat 32)
      let aw5 := UInt256.ofNat (MachineState.M aw4.toNat base.toNat packedLen.toNat)
      RD blindAuctionBytecode I g s0 ⟨1235⟩
        [flag, secret, fakeWord, value, slot, i, refund, len, revealEnd, biddingEnd,
          secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
        mem5 aw5 rdata (cA, σ) k' C' := by
  let base := (⟨32⟩ : UInt256) + fp
  let newFree := (⟨65⟩ : UInt256) + base
  let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
  let mem4 := scratch_revealPackedLenMem mem fp packedLen
  let aw1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  let aw2 := UInt256.ofNat (MachineState.M aw1.toNat fp.toNat 32)
  let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
  let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨64⟩ : UInt256).toNat 32)
  let aw4 := UInt256.ofNat (MachineState.M aw3.toNat fp.toNat 32)
  let aw5 := UInt256.ofNat (MachineState.M aw4.toNat base.toNat packedLen.toNat)
  have rd1224 := evm_run rd with [
    jumpdest, push1 ⟨64⟩,
    raw mload (Cₘ aw1 - Cₘ aw) fp aw1 (by decide)
      (fun s haws hstks => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, aw1])
      hfp (by rfl) (by evm_ov),
    push1 ⟨32⟩, dup2, dup4, sub, sub, dup2,
    raw mstore (Cₘ aw2 - Cₘ aw1) mem4 aw2 (by decide)
      (fun s haws hstks => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, aw2])
      (by rfl) (by rfl) (by evm_ov),
    swap1, push1 ⟨64⟩,
    raw mstore (Cₘ aw3 - Cₘ aw2) mem5 aw3 (by decide)
      (fun s haws hstks => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, aw3])
      (by rfl) (by rfl) (by evm_ov),
    dup1,
    raw mload (Cₘ aw4 - Cₘ aw3) packedLen aw4 (by decide)
      (fun s haws hstks => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, aw4])
      (by simpa [base, newFree, packedLen, mem4, mem5, aw1, aw2, aw3] using hlen)
      (by rfl) (by evm_ov)]
  have rd1233₀ := evm_run rd1224 with [
    swap1, push1 ⟨32⟩, add,
    raw keccak256 (Cₘ aw5 - Cₘ aw4) hash aw5 (by decide)
      (fun s haws hstks => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, base, aw5])
      (by simpa [base, newFree, packedLen, mem4, mem5] using hhash)
      (by rfl) (by evm_ov),
    dup5, push0, add]
  obtain ⟨_, _, rd1234₀⟩ := rd1233₀.sload (by decide) (by evm_ov)
  have rd1234 := rd1234₀
  rw [hstore] at rd1234
  have rd1235₀ := evm_run rd1234 with [eq]
  have rd1235 := rd1235₀
  rw [hflag] at rd1235
  exact ⟨_, _, by
    simpa [base, newFree, packedLen, mem4, mem5, aw1, aw2, aw3, aw4, aw5] using rd1235⟩

theorem scratch_blindAuctionRevealX_zeroBlinded_toNext {I} {g : Sat256} {s0 : State}
    {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {secret fake value slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen
      fakesEnd valuesLen valuesEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1315⟩
      [secret, fake, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hperm : I.perm = true) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1014⟩
      (scratch_revealEvmLoopStack (i + ⟨1⟩) refund len revealEnd biddingEnd secretsLen
        secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
      mem aw rdata (cA, sstoreAccountMap I.codeOwner σ slot ⟨0⟩) k' C' := by
  have rd1321₀ := evm_run rd with [jumpdest, pop, pop, push0, swap1, swap2]
  obtain ⟨_, _, rd1322₀⟩ := rd1321₀.sstore hperm (by decide) (by evm_ov)
  have rd1323 := evm_run rd1322₀ with [pop, jumpdest, push1 ⟨1⟩, add,
    push2 ⟨1014⟩, jump (by jump_dest)]
  have hidx : (⟨1⟩ : UInt256) + i = i + ⟨1⟩ := blindAuctionU256_add_comm _ _
  exact ⟨_, _, by simpa [scratch_revealEvmLoopStack, sstoreAccountMap, hidx] using rd1323⟩

theorem scratch_blindAuctionRevealX_hashMismatch_toNext {I} {g : Sat256} {s0 : State}
    {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {secret fake value slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen
      fakesEnd valuesLen valuesEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1239⟩
      [secret, fake, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1014⟩
      (scratch_revealEvmLoopStack (i + ⟨1⟩) refund len revealEnd biddingEnd secretsLen
        secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
      mem aw rdata acc k' C' := by
  have rd1323 := evm_run rd with [pop, pop, pop, pop, push2 ⟨1323⟩,
    jump (by jump_dest), jumpdest, push1 ⟨1⟩, add, push2 ⟨1014⟩,
    jump (by jump_dest)]
  have hidx : (⟨1⟩ : UInt256) + i = i + ⟨1⟩ := blindAuctionU256_add_comm _ _
  exact ⟨_, _, by simpa [scratch_revealEvmLoopStack, hidx] using rd1323⟩

theorem scratch_blindAuctionRevealX_hashGuard_mismatch_toNext {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {secret fake value slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen
      fakesEnd valuesLen valuesEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1235⟩
      [⟨0⟩, secret, fake, value, slot, i, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1014⟩
      (scratch_revealEvmLoopStack (i + ⟨1⟩) refund len revealEnd biddingEnd secretsLen
        secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
      mem aw rdata acc k' C' := by
  have rd1239 := evm_run rd with [push2 ⟨1247⟩, jumpiNT (by decide)]
  exact scratch_blindAuctionRevealX_hashMismatch_toNext rd1239

theorem scratch_blindAuctionRevealX_hashGuard_match_to1247 {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {secret fake value slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen
      fakesEnd valuesLen valuesEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1235⟩
      [⟨1⟩, secret, fake, value, slot, i, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1247⟩
      [secret, fake, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k' C' := by
  exact ⟨_, _, evm_run rd with [push2 ⟨1247⟩, jumpiT one_ne_zero_uint (by jump_dest)]⟩

theorem scratch_blindAuctionRevealX_callMade_fromCall {cA gh bl σ σ₀ A I} {g : Sat256}
    {k C : ℕ}
    {gasArg refund len freePtr revealEnd biddingEnd valuesLen valuesEnd fakesLen fakesEnd
      secretsLen secretsEnd sel : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hbalance : refund ≤ (σ.find? I.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hdepth : I.depth.val < 1024)
    (rd : RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1349⟩
      [gasArg, revealScratchSenderWord I, refund, freePtr, ⟨0⟩, freePtr, ⟨0⟩,
        freePtr, refund, revealScratchSenderWord I, ⟨0⟩, refund, len,
        revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen,
        valuesEnd, ⟨276⟩, sel]
      mem aw ByteArray.empty (cA, σ) k C)
    (hawCall :
      UInt256.ofNat
        (MachineState.M (MachineState.M aw.toNat freePtr.toNat (⟨0⟩ : UInt256).toNat)
          freePtr.toNat (⟨0⟩ : UInt256).toNat) = aw) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA
          (initState cA gh bl σ σ₀ g A I).genesisBlockHeader
          (initState cA gh bl σ σ₀ g A I).blocks
          σ (initState cA gh bl σ σ₀ g A I).σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (revealScratchSenderWord I))
          (toExecute σ (AccountAddress.ofUInt256 (revealScratchSenderWord I)))
          callGas (UInt256.ofNat I.gasPrice) refund refund
          ByteArray.empty (I.depth + 1) I.header I.perm)
      ∧ o.size < 2 ^ 255
      ∧ RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1350⟩
          [(if z then ⟨1⟩ else ⟨0⟩), freePtr, refund, revealScratchSenderWord I,
            ⟨0⟩, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen,
            fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
          mem aw o (cA', σ') k' C' := by
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ, rd1350₀⟩ :=
    RD.callValueMade rd (by decide) hperm hbalance hdepth (by simp)
  have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat o.size := by
      show (0 : Nat) ≤ (UInt256.ofNat o.size).val.val
      exact Nat.zero_le _
    simp [min, hle]
  have hcd : mem.readWithPadding freePtr.toNat (⟨0⟩ : UInt256).toNat = ByteArray.empty := by
    exact revealScratch_readWithPadding_zero _ _
  have hΘ' : ∃ (g'' : UInt256) (A' : Substate),
      (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA
        (initState cA gh bl σ σ₀ g A I).genesisBlockHeader
        (initState cA gh bl σ σ₀ g A I).blocks
        σ (initState cA gh bl σ σ₀ g A I).σ₀ A_in
        (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
        (AccountAddress.ofUInt256 (revealScratchSenderWord I))
        (toExecute σ (AccountAddress.ofUInt256 (revealScratchSenderWord I)))
        callGas (UInt256.ofNat I.gasPrice) refund refund
        ByteArray.empty (I.depth + 1) I.header I.perm := by
    rcases hΘ with ⟨g'', A', hΘeq⟩
    refine ⟨g'', A', ?_⟩
    rw [hcd] at hΘeq
    exact hΘeq
  have ho255 : o.size < 2 ^ 255 := by
    rcases hΘ' with ⟨g'', A', hΘeq⟩
    have ho : o = (Ethereum.EVM.Θ I.blobVersionedHashes cA
        (initState cA gh bl σ σ₀ g A I).genesisBlockHeader
        (initState cA gh bl σ σ₀ g A I).blocks
        σ (initState cA gh bl σ σ₀ g A I).σ₀ A_in
        (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
        (AccountAddress.ofUInt256 (revealScratchSenderWord I))
        (toExecute σ (AccountAddress.ofUInt256 (revealScratchSenderWord I)))
        callGas (UInt256.ofNat I.gasPrice) refund refund
        ByteArray.empty (I.depth + 1) I.header I.perm).2.2.2.2.2 :=
      congrArg (fun t => t.2.2.2.2.2) hΘeq
    rw [ho]
    exact Theta_returnData_size_lt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  rw [hmin, revealScratch_write_len_zero, hawCall] at rd1350₀
  exact ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ', ho255,
    by simpa [revealScratchSenderWord] using rd1350₀⟩

def scratch_revealPackedBytes (value : UInt256) (fake : Bool) (secret : UInt256) : List UInt8 :=
  EVM.Word.toBytesBE value ++ [if fake then (1 : UInt8) else 0] ++ EVM.Word.toBytesBE secret

def scratch_revealPackedHashExpr : Expr :=
  .keccak256 (.abiEncodePacked
    [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])

def scratch_revealPackedHashValue (value : UInt256) (fake : Bool) (secret : UInt256) : Value :=
  .fixedBytes ⟨31, bytes32._proof_1⟩
    (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray)).toList

theorem scratch_encodePacked_uint256 (value : UInt256) :
    encodePackedValue? uint256 (.int (Int.ofNat value.toNat)) =
      some (EVM.Word.toBytesBE value) := by
  have hword : EVM.word value.toNat = value := u256_ofNat_toNat value
  have hlt : value.toNat < EVM.twoPow 256 := by
    change value.val.val < EVM.twoPow 256
    exact value.val.isLt
  simp [encodePackedValue?, uint256, uint256Int, encodeABIWord?, hword, hlt]

theorem scratch_encodePacked_bool (fake : Bool) :
    encodePackedValue? boolTy (.bool fake) = some [if fake then (1 : UInt8) else 0] := by
  cases fake <;> simp [encodePackedValue?, boolTy]

theorem scratch_word_toBytesBE_length_32 (w : UInt256) :
    (EVM.Word.toBytesBE w).length = 32 := by
  simpa using word_toBytesBE_toByteArray_size w

theorem scratch_encodePacked_bytes32 (secret : UInt256) :
    encodePackedValue? bytes32
      (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)) =
        some (EVM.Word.toBytesBE secret) := by
  have hlen := scratch_word_toBytesBE_length_32 secret
  simp [encodePackedValue?, bytes32, fixedBytesSize, hlen]

/-! ### Ported dynamic decode failure bridge -/

theorem scratch_word_le_solcMax_of_ugt_zero {w : UInt256}
    (h : UInt256.gt w revealMaxU64 = ⟨0⟩) :
    w.toNat ≤ solcMaxU64 := by
  by_contra hle
  have hgt : UInt256.gt w revealMaxU64 = ⟨1⟩ := by
    apply ugt_one
    rw [show revealMaxU64.toNat = solcMaxU64 by native_decide]
    omega
  rw [h] at hgt
  have hnat := congrArg UInt256.toNat hgt
  change (0 : Nat) = 1 at hnat
  omega

theorem scratch_not_solcMax_lt_of_ugt_zero {w : UInt256}
    (h : UInt256.gt w revealMaxU64 = ⟨0⟩) :
    ¬ solcMaxU64 < w.toNat := by
  have hle := scratch_word_le_solcMax_of_ugt_zero h
  omega

theorem scratch_add4_word_add31_toNat (w : UInt256)
    (hle : w.toNat ≤ solcMaxU64) :
    (((⟨4⟩ : UInt256) + w) + ⟨31⟩).toNat = 4 + w.toNat + 31 := by
  rw [← u256_ofNat_toNat w]
  simpa [u256_ofNat_toNat] using
    (uadd3_ofNat_toNat (a := 4) (b := w.toNat) (c := 31)
    (by norm_num [UInt256.size])
    w.val.isLt
    (by norm_num [UInt256.size])
    (by
      rw [show solcMaxU64 = 18446744073709551615 by rfl] at hle
      norm_num [UInt256.size]
      omega)
    (by
      rw [show solcMaxU64 = 18446744073709551615 by rfl] at hle
      norm_num [UInt256.size]
      omega))

theorem scratch_add4_word_toNat (w : UInt256)
    (hle : w.toNat ≤ solcMaxU64) :
    ((⟨4⟩ : UInt256) + w).toNat = 4 + w.toNat := by
  rw [← u256_ofNat_toNat w]
  simpa [u256_ofNat_toNat] using
    (uadd_ofNat_toNat (a := 4) (b := w.toNat)
      (by norm_num [UInt256.size])
      w.val.isLt
      (by
        rw [show solcMaxU64 = 18446744073709551615 by rfl] at hle
        norm_num [UInt256.size]
        omega))

theorem scratch_start_bound_of_slt_one {I : ExecutionEnv} {off : UInt256}
    (hcalldataSign : I.calldata.size < 2 ^ 255)
    (hoff : off.toNat ≤ solcMaxU64)
    (hstart : UInt256.slt (((⟨4⟩ : UInt256) + off) + ⟨31⟩)
      (UInt256.ofNat I.calldata.size) = ⟨1⟩) :
    4 + off.toNat + 31 < I.calldata.size := by
  by_contra hnot
  have hleft :
      (((⟨4⟩ : UInt256) + off) + ⟨31⟩).toNat = 4 + off.toNat + 31 :=
    scratch_add4_word_add31_toNat off hoff
  have hhi : (((⟨4⟩ : UInt256) + off) + ⟨31⟩).toNat < 2 ^ 255 := by
    rw [hleft]
    rw [show solcMaxU64 = 18446744073709551615 by rfl] at hoff
    omega
  have hzero :
      UInt256.slt (((⟨4⟩ : UInt256) + off) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨0⟩ := by
    apply slt_lit_zero hcalldataSign
    · rw [hleft]
      omega
    · exact hhi
  rw [hstart] at hzero
  have hnat := congrArg UInt256.toNat hzero
  change (1 : Nat) = 0 at hnat
  omega

theorem scratch_array_end_bound_of_ugt_zero {I : ExecutionEnv} {off len : UInt256}
    (hoff : off.toNat ≤ solcMaxU64)
    (hlen : len.toNat ≤ solcMaxU64)
    (hend : UInt256.gt (((((⟨4⟩ : UInt256) + off) +
          UInt256.shiftLeft len ⟨5⟩) + ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) :
    4 + off.toNat + 32 + 32 * len.toNat ≤ I.calldata.size := by
  have h32lenSmall : 32 * len.toNat < UInt256.size := by
    rw [show solcMaxU64 = 18446744073709551615 by rfl] at hlen
    norm_num [UInt256.size]
    omega
  have hleft :
      (((((⟨4⟩ : UInt256) + off) + UInt256.shiftLeft len ⟨5⟩) + ⟨32⟩)).toNat =
        4 + off.toNat + 32 * len.toNat + 32 := by
    rw [← u256_ofNat_toNat off, ← u256_ofNat_toNat len,
      shiftLeft5_ofNat_eq h32lenSmall]
    have h4off32len :
        ((UInt256.ofNat 4 + UInt256.ofNat off.toNat) +
            UInt256.ofNat (32 * len.toNat)).toNat =
          4 + off.toNat + 32 * len.toNat := by
      apply uadd3_ofNat_toNat
      · norm_num [UInt256.size]
      · exact off.val.isLt
      · exact h32lenSmall
      · rw [show solcMaxU64 = 18446744073709551615 by rfl] at hoff
        norm_num [UInt256.size]
        omega
      · rw [show solcMaxU64 = 18446744073709551615 by rfl] at hoff hlen
        norm_num [UInt256.size]
        omega
    rw [uadd_toNat]
    change
      (((UInt256.ofNat 4 + UInt256.ofNat off.toNat) +
            UInt256.ofNat (32 * len.toNat)).toNat + (UInt256.ofNat 32).toNat) %
          UInt256.size =
        4 + (UInt256.ofNat off.toNat).toNat +
          32 * (UInt256.ofNat len.toNat).toNat + 32
    rw [h4off32len, ulit_toNat' 32 (by norm_num [UInt256.size]),
      ulit_toNat' off.toNat off.val.isLt, ulit_toNat' len.toNat len.val.isLt]
    apply Nat.mod_eq_of_lt
    rw [show solcMaxU64 = 18446744073709551615 by rfl] at hoff hlen
    norm_num [UInt256.size]
    omega
  by_contra hnot
  have hgt : UInt256.gt
      (((((⟨4⟩ : UInt256) + off) + UInt256.shiftLeft len ⟨5⟩) + ⟨32⟩))
      (UInt256.ofNat I.calldata.size) = ⟨1⟩ := by
    apply ugt_one
    rw [hleft, ulit_toNat' I.calldata.size hsize]
    omega
  rw [hend] at hgt
  have hnat := congrArg UInt256.toNat hgt
  change (0 : Nat) = 1 at hnat
  omega

theorem scratch_readNat_drop4_eq_calldataWord {I : ExecutionEnv} {headOff : Nat}
    (h : 4 + headOff + 32 ≤ I.calldata.size) :
    readNat? (List.drop 4 I.calldata.toList) headOff =
      some (calldataWord I.calldata (4 + headOff)).toNat := by
  unfold readNat? readWord? readBytes?
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hslice :
      (List.take 32 (List.drop headOff (List.drop 4 I.calldata.toList))).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  rw [if_pos hslice]
  rw [calldataWord]
  rw [List.drop_drop]
  rw [← decode_word_at_eq_any I.calldata (4 + headOff) h]
  rfl

theorem scratch_readNat_drop4_array_len_eq {I : ExecutionEnv} {off len : UInt256}
    (hoff : off.toNat ≤ solcMaxU64)
    (hbound : 4 + off.toNat + 32 ≤ I.calldata.size)
    (hlenWord :
      uInt256OfByteArray (I.calldata.readBytes (((⟨4⟩ : UInt256) + off).toNat) 32) =
        len) :
    readNat? (List.drop 4 I.calldata.toList) off.toNat = some len.toNat := by
  have hread :=
    scratch_readNat_drop4_eq_calldataWord (I := I) (headOff := off.toNat)
      (by simpa [Nat.add_assoc] using hbound)
  have hstart : ((⟨4⟩ : UInt256) + off).toNat = 4 + off.toNat :=
    scratch_add4_word_toNat off hoff
  have hword : calldataWord I.calldata (4 + off.toNat) = len := by
    unfold calldataWord
    rw [← hstart]
    exact hlenWord
  rw [hread, hword]

theorem scratch_blindAuctionDecode_reveal_some_of_guards {I : ExecutionEnv}
    {valuesLen fakesLen secretsLen : UInt256}
    (hheadSize : 100 ≤ I.calldata.size)
    (hcalldataSign : I.calldata.size < 2 ^ 255)
    (hvaluesGt : UInt256.gt (revealValuesOffsetWord I) revealMaxU64 = ⟨0⟩)
    (hvaluesStart :
      UInt256.slt (((⟨4⟩ : UInt256) + revealValuesOffsetWord I) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hvaluesLen :
      uInt256OfByteArray
        (I.calldata.readBytes (((⟨4⟩ : UInt256) + revealValuesOffsetWord I).toNat) 32) =
        valuesLen)
    (hvaluesLenMax : UInt256.gt valuesLen revealMaxU64 = ⟨0⟩)
    (hvaluesEnd :
      UInt256.gt
        ((((⟨4⟩ : UInt256) + revealValuesOffsetWord I) +
          UInt256.shiftLeft valuesLen ⟨5⟩) + ⟨32⟩)
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hfakesGt : UInt256.gt (revealFakesOffsetWord I) revealMaxU64 = ⟨0⟩)
    (hfakesStart :
      UInt256.slt (((⟨4⟩ : UInt256) + revealFakesOffsetWord I) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hfakesLen :
      uInt256OfByteArray
        (I.calldata.readBytes (((⟨4⟩ : UInt256) + revealFakesOffsetWord I).toNat) 32) =
        fakesLen)
    (hfakesLenMax : UInt256.gt fakesLen revealMaxU64 = ⟨0⟩)
    (hfakesEnd :
      UInt256.gt
        ((((⟨4⟩ : UInt256) + revealFakesOffsetWord I) +
          UInt256.shiftLeft fakesLen ⟨5⟩) + ⟨32⟩)
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hsecretsGt : UInt256.gt (revealSecretsOffsetWord I) revealMaxU64 = ⟨0⟩)
    (hsecretsStart :
      UInt256.slt (((⟨4⟩ : UInt256) + revealSecretsOffsetWord I) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hsecretsLen :
      uInt256OfByteArray
        (I.calldata.readBytes (((⟨4⟩ : UInt256) + revealSecretsOffsetWord I).toNat) 32) =
        secretsLen)
    (hsecretsLenMax : UInt256.gt secretsLen revealMaxU64 = ⟨0⟩)
    (hsecretsEnd :
      UInt256.gt
        ((((⟨4⟩ : UInt256) + revealSecretsOffsetWord I) +
          UInt256.shiftLeft secretsLen ⟨5⟩) + ⟨32⟩)
        (UInt256.ofNat I.calldata.size) = ⟨0⟩) :
    ∃ callargs,
      decodeCalldata (revealTransition.params.map Param.name)
        (transitionSignature revealTransition).paramTypes I.calldata = some callargs := by
  let args := List.drop 4 I.calldata.toList
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hargsLen : args.length = I.calldata.size - 4 := by
    dsimp [args]
    rw [List.length_drop, htlen]
  have hsize256 : I.calldata.size < UInt256.size := lt_size_of_lt_sign hcalldataSign
  have hvaluesOffLe := scratch_word_le_solcMax_of_ugt_zero hvaluesGt
  have hfakesOffLe := scratch_word_le_solcMax_of_ugt_zero hfakesGt
  have hsecretsOffLe := scratch_word_le_solcMax_of_ugt_zero hsecretsGt
  have hvaluesLenLe := scratch_word_le_solcMax_of_ugt_zero hvaluesLenMax
  have hfakesLenLe := scratch_word_le_solcMax_of_ugt_zero hfakesLenMax
  have hsecretsLenLe := scratch_word_le_solcMax_of_ugt_zero hsecretsLenMax
  have hvaluesStartBound :
      4 + (revealValuesOffsetWord I).toNat + 32 ≤ I.calldata.size := by
    have h := scratch_start_bound_of_slt_one
      (I := I) (off := revealValuesOffsetWord I) hcalldataSign hvaluesOffLe hvaluesStart
    omega
  have hfakesStartBound :
      4 + (revealFakesOffsetWord I).toNat + 32 ≤ I.calldata.size := by
    have h := scratch_start_bound_of_slt_one
      (I := I) (off := revealFakesOffsetWord I) hcalldataSign hfakesOffLe hfakesStart
    omega
  have hsecretsStartBound :
      4 + (revealSecretsOffsetWord I).toNat + 32 ≤ I.calldata.size := by
    have h := scratch_start_bound_of_slt_one
      (I := I) (off := revealSecretsOffsetWord I) hcalldataSign hsecretsOffLe
        hsecretsStart
    omega
  have hvaluesHead :
      readNat? args 0 = some (revealValuesOffsetWord I).toNat := by
    dsimp [args]
    simpa [revealValuesOffsetWord] using
      (scratch_readNat_drop4_eq_calldataWord (I := I) (headOff := 0) (by omega))
  have hfakesHead :
      readNat? args 32 = some (revealFakesOffsetWord I).toNat := by
    dsimp [args]
    simpa [revealFakesOffsetWord, Nat.add_assoc] using
      (scratch_readNat_drop4_eq_calldataWord (I := I) (headOff := 32) (by omega))
  have hsecretsHead :
      readNat? args 64 = some (revealSecretsOffsetWord I).toNat := by
    dsimp [args]
    simpa [revealSecretsOffsetWord, Nat.add_assoc] using
      (scratch_readNat_drop4_eq_calldataWord (I := I) (headOff := 64) (by omega))
  have hvaluesLenRead :
      readNat? args (revealValuesOffsetWord I).toNat = some valuesLen.toNat := by
    dsimp [args]
    exact scratch_readNat_drop4_array_len_eq
      (I := I) (off := revealValuesOffsetWord I) (len := valuesLen)
      hvaluesOffLe hvaluesStartBound hvaluesLen
  have hfakesLenRead :
      readNat? args (revealFakesOffsetWord I).toNat = some fakesLen.toNat := by
    dsimp [args]
    exact scratch_readNat_drop4_array_len_eq
      (I := I) (off := revealFakesOffsetWord I) (len := fakesLen)
      hfakesOffLe hfakesStartBound hfakesLen
  have hsecretsLenRead :
      readNat? args (revealSecretsOffsetWord I).toNat = some secretsLen.toNat := by
    dsimp [args]
    exact scratch_readNat_drop4_array_len_eq
      (I := I) (off := revealSecretsOffsetWord I) (len := secretsLen)
      hsecretsOffLe hsecretsStartBound hsecretsLen
  have hvaluesEndBound :
      (revealValuesOffsetWord I).toNat + 32 + 32 * valuesLen.toNat ≤ args.length := by
    have h := scratch_array_end_bound_of_ugt_zero
      (I := I) (off := revealValuesOffsetWord I) (len := valuesLen)
      hvaluesOffLe hvaluesLenLe hvaluesEnd hsize256
    rw [hargsLen]
    omega
  have hfakesEndBound :
      (revealFakesOffsetWord I).toNat + 32 + 32 * fakesLen.toNat ≤ args.length := by
    have h := scratch_array_end_bound_of_ugt_zero
      (I := I) (off := revealFakesOffsetWord I) (len := fakesLen)
      hfakesOffLe hfakesLenLe hfakesEnd hsize256
    rw [hargsLen]
    omega
  have hsecretsEndBound :
      (revealSecretsOffsetWord I).toNat + 32 + 32 * secretsLen.toNat ≤ args.length := by
    have h := scratch_array_end_bound_of_ugt_zero
      (I := I) (off := revealSecretsOffsetWord I) (len := secretsLen)
      hsecretsOffLe hsecretsLenLe hsecretsEnd hsize256
    rw [hargsLen]
    omega
  obtain ⟨values, hvaluesDecode, _hvaluesLength⟩ :=
    decodeABIValue_dynamicArray_uint256_exists
      (bytes := args) (start := (revealValuesOffsetWord I).toNat)
      (len := valuesLen.toNat) hvaluesLenRead
      (scratch_not_solcMax_lt_of_ugt_zero hvaluesLenMax) hvaluesEndBound
  obtain ⟨fakes, hfakesDecode, _hfakesLength⟩ :=
    decodeABIValue_dynamicArray_bool_exists
      (bytes := args) (start := (revealFakesOffsetWord I).toNat)
      (len := fakesLen.toNat) hfakesLenRead
      (scratch_not_solcMax_lt_of_ugt_zero hfakesLenMax) hfakesEndBound
  obtain ⟨secrets, hsecretsDecode, _hsecretsLength⟩ :=
    decodeABIValue_dynamicArray_bytes32_exists
      (bytes := args) (start := (revealSecretsOffsetWord I).toNat)
      (len := secretsLen.toNat) hsecretsLenRead
      (scratch_not_solcMax_lt_of_ugt_zero hsecretsLenMax) hsecretsEndBound
  let callargs : Store :=
    (((∅ : Store).insert "values" (.array values)).insert "fakes" (.array fakes)).insert
      "secrets" (.array secrets)
  refine ⟨callargs, ?_⟩
  change decodeCalldata ["values", "fakes", "secrets"]
    [.dynamicArray uint256, .dynamicArray boolTy, .dynamicArray bytes32] I.calldata =
      some callargs
  have hnotHugeFull :
      ¬([ABIType.dynamicArray uint256, ABIType.dynamicArray boolTy,
            ABIType.dynamicArray bytes32].any isDynamicABIType = true ∧
          2 ^ 255 ≤ I.calldata.toList.length) := by
    intro hhuge
    rcases hhuge with ⟨_, hhuge⟩
    rw [htlen] at hhuge
    omega
  have hnotHugeArgs :
      ¬([ABIType.dynamicArray uint256, ABIType.dynamicArray boolTy,
            ABIType.dynamicArray bytes32].isEmpty = false ∧
          2 ^ 255 ≤ (List.drop 4 I.calldata.toList).length) := by
    intro hhuge
    rcases hhuge with ⟨_, hhuge⟩
    rw [List.length_drop, htlen] at hhuge
    omega
  have hnotArgsShort : ¬ (List.drop 4 I.calldata.toList).length < 96 := by
    rw [List.length_drop, htlen]
    omega
  have hnotArgsShortSub : ¬ I.calldata.toList.length - 4 < 96 := by
    rw [htlen]
    omega
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_neg hnotHugeFull]
  rw [if_neg hnotHugeArgs]
  simp [decodeCalldata.decodeArgs, decodeABIValues?, abiTupleHeadSize?,
    isDynamicABIType, Option.bind, bind, args, hvaluesHead,
    scratch_not_solcMax_lt_of_ugt_zero hvaluesGt, hvaluesDecode, hfakesHead,
    scratch_not_solcMax_lt_of_ugt_zero hfakesGt, hfakesDecode, hsecretsHead,
    scratch_not_solcMax_lt_of_ugt_zero hsecretsGt, hsecretsDecode,
    decodeCalldata.insertValues, callargs, hnotArgsShortSub]

theorem scratch_blindAuctionRevealDecode1806_none_reverts
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : Nat}
    (rd : RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1806⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨413⟩, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hheadSize : 100 ≤ I.calldata.size)
    (hcalldataSign : I.calldata.size < 2 ^ 255)
    (hdecNone :
      decodeCalldata (revealTransition.params.map Param.name)
        (transitionSignature revealTransition).paramTypes I.calldata = none) :
    RDrev blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  by_cases hvaluesGt : UInt256.gt (revealValuesOffsetWord I) revealMaxU64 = ⟨1⟩
  · exact blindAuctionRevealX_decode_valuesOffset_revert
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hvaluesGt ⟨k, C, rd⟩
  · have hvaluesGt0 :
        UInt256.gt (revealValuesOffsetWord I) revealMaxU64 = ⟨0⟩ :=
      ugt_eq_zero_of_ne_one hvaluesGt
    obtain ⟨_, _, rd1713v⟩ :=
      blindAuctionRevealDecodeValuesCall1806_to_1713 rd hvaluesGt0
    by_cases hvaluesStart :
        UInt256.slt (((⟨4⟩ : UInt256) + revealValuesOffsetWord I) + ⟨31⟩)
          (UInt256.ofNat I.calldata.size) = ⟨1⟩
    · let valuesLen : UInt256 :=
        uInt256OfByteArray
          (I.calldata.readBytes (((⟨4⟩ : UInt256) + revealValuesOffsetWord I).toNat) 32)
      have hvaluesLen :
          uInt256OfByteArray
            (I.calldata.readBytes (((⟨4⟩ : UInt256) + revealValuesOffsetWord I).toNat) 32) =
            valuesLen := rfl
      by_cases hvaluesLenMax : UInt256.gt valuesLen revealMaxU64 = ⟨1⟩
      · exact RD.blindAuctionRevealDecodeArray1713_lengthRevert
          rd1713v hvaluesStart hvaluesLen hvaluesLenMax (by simp)
      · have hvaluesLenMax0 : UInt256.gt valuesLen revealMaxU64 = ⟨0⟩ :=
          ugt_eq_zero_of_ne_one hvaluesLenMax
        by_cases hvaluesEnd :
            UInt256.gt
              ((((⟨4⟩ : UInt256) + revealValuesOffsetWord I) +
                UInt256.shiftLeft valuesLen ⟨5⟩) + ⟨32⟩)
              (UInt256.ofNat I.calldata.size) = ⟨1⟩
        · exact RD.blindAuctionRevealDecodeArray1713_endRevert
            rd1713v hvaluesStart hvaluesLen hvaluesLenMax0 hvaluesEnd (by simp)
        · have hvaluesEnd0 :
              UInt256.gt
                ((((⟨4⟩ : UInt256) + revealValuesOffsetWord I) +
                  UInt256.shiftLeft valuesLen ⟨5⟩) + ⟨32⟩)
                (UInt256.ofNat I.calldata.size) = ⟨0⟩ :=
            ugt_eq_zero_of_ne_one hvaluesEnd
          obtain ⟨_, _, rd1840⟩ :=
            RD.blindAuctionRevealDecodeArray1713 rd1713v hvaluesStart hvaluesLen
              hvaluesLenMax0 hvaluesEnd0 (by jump_dest) (by simp)
          by_cases hfakesGt : UInt256.gt (revealFakesOffsetWord I) revealMaxU64 = ⟨1⟩
          · exact blindAuctionRevealDecodeFakesOffset1840_reverts rd1840 hfakesGt
          · have hfakesGt0 :
                UInt256.gt (revealFakesOffsetWord I) revealMaxU64 = ⟨0⟩ :=
              ugt_eq_zero_of_ne_one hfakesGt
            obtain ⟨_, _, rd1713f⟩ :=
              blindAuctionRevealDecodeFakesCall1840_to_1713 rd1840 hfakesGt0
            by_cases hfakesStart :
                UInt256.slt (((⟨4⟩ : UInt256) + revealFakesOffsetWord I) + ⟨31⟩)
                  (UInt256.ofNat I.calldata.size) = ⟨1⟩
            · let fakesLen : UInt256 :=
                uInt256OfByteArray
                  (I.calldata.readBytes
                    (((⟨4⟩ : UInt256) + revealFakesOffsetWord I).toNat) 32)
              have hfakesLen :
                  uInt256OfByteArray
                    (I.calldata.readBytes
                      (((⟨4⟩ : UInt256) + revealFakesOffsetWord I).toNat) 32) =
                    fakesLen := rfl
              by_cases hfakesLenMax : UInt256.gt fakesLen revealMaxU64 = ⟨1⟩
              · exact RD.blindAuctionRevealDecodeArray1713_lengthRevert
                  rd1713f hfakesStart hfakesLen hfakesLenMax (by simp)
              · have hfakesLenMax0 : UInt256.gt fakesLen revealMaxU64 = ⟨0⟩ :=
                  ugt_eq_zero_of_ne_one hfakesLenMax
                by_cases hfakesEnd :
                    UInt256.gt
                      ((((⟨4⟩ : UInt256) + revealFakesOffsetWord I) +
                        UInt256.shiftLeft fakesLen ⟨5⟩) + ⟨32⟩)
                      (UInt256.ofNat I.calldata.size) = ⟨1⟩
                · exact RD.blindAuctionRevealDecodeArray1713_endRevert
                    rd1713f hfakesStart hfakesLen hfakesLenMax0 hfakesEnd (by simp)
                · have hfakesEnd0 :
                      UInt256.gt
                        ((((⟨4⟩ : UInt256) + revealFakesOffsetWord I) +
                          UInt256.shiftLeft fakesLen ⟨5⟩) + ⟨32⟩)
                        (UInt256.ofNat I.calldata.size) = ⟨0⟩ :=
                    ugt_eq_zero_of_ne_one hfakesEnd
                  obtain ⟨_, _, rd1883⟩ :=
                    RD.blindAuctionRevealDecodeArray1713 rd1713f hfakesStart hfakesLen
                      hfakesLenMax0 hfakesEnd0 (by jump_dest) (by simp)
                  by_cases hsecretsGt :
                      UInt256.gt (revealSecretsOffsetWord I) revealMaxU64 = ⟨1⟩
                  · exact blindAuctionRevealDecodeSecretsOffset1883_reverts rd1883 hsecretsGt
                  · have hsecretsGt0 :
                        UInt256.gt (revealSecretsOffsetWord I) revealMaxU64 = ⟨0⟩ :=
                      ugt_eq_zero_of_ne_one hsecretsGt
                    obtain ⟨_, _, rd1713s⟩ :=
                      blindAuctionRevealDecodeSecretsCall1883_to_1713 rd1883 hsecretsGt0
                    by_cases hsecretsStart :
                        UInt256.slt
                          (((⟨4⟩ : UInt256) + revealSecretsOffsetWord I) + ⟨31⟩)
                          (UInt256.ofNat I.calldata.size) = ⟨1⟩
                    · let secretsLen : UInt256 :=
                        uInt256OfByteArray
                          (I.calldata.readBytes
                            (((⟨4⟩ : UInt256) + revealSecretsOffsetWord I).toNat) 32)
                      have hsecretsLen :
                          uInt256OfByteArray
                            (I.calldata.readBytes
                              (((⟨4⟩ : UInt256) + revealSecretsOffsetWord I).toNat) 32) =
                            secretsLen := rfl
                      by_cases hsecretsLenMax :
                          UInt256.gt secretsLen revealMaxU64 = ⟨1⟩
                      · exact RD.blindAuctionRevealDecodeArray1713_lengthRevert
                          rd1713s hsecretsStart hsecretsLen hsecretsLenMax (by simp)
                      · have hsecretsLenMax0 :
                            UInt256.gt secretsLen revealMaxU64 = ⟨0⟩ :=
                          ugt_eq_zero_of_ne_one hsecretsLenMax
                        by_cases hsecretsEnd :
                            UInt256.gt
                              ((((⟨4⟩ : UInt256) + revealSecretsOffsetWord I) +
                                UInt256.shiftLeft secretsLen ⟨5⟩) + ⟨32⟩)
                              (UInt256.ofNat I.calldata.size) = ⟨1⟩
                        · exact RD.blindAuctionRevealDecodeArray1713_endRevert
                            rd1713s hsecretsStart hsecretsLen hsecretsLenMax0 hsecretsEnd
                            (by simp)
                        · have hsecretsEnd0 :
                              UInt256.gt
                                ((((⟨4⟩ : UInt256) + revealSecretsOffsetWord I) +
                                  UInt256.shiftLeft secretsLen ⟨5⟩) + ⟨32⟩)
                                (UInt256.ofNat I.calldata.size) = ⟨0⟩ :=
                            ugt_eq_zero_of_ne_one hsecretsEnd
                          obtain ⟨callargs, hdecSome⟩ :=
                            scratch_blindAuctionDecode_reveal_some_of_guards
                              (I := I) (valuesLen := valuesLen) (fakesLen := fakesLen)
                              (secretsLen := secretsLen)
                              hheadSize hcalldataSign hvaluesGt0 hvaluesStart hvaluesLen
                              hvaluesLenMax0 hvaluesEnd0 hfakesGt0 hfakesStart hfakesLen
                              hfakesLenMax0 hfakesEnd0 hsecretsGt0 hsecretsStart hsecretsLen
                              hsecretsLenMax0 hsecretsEnd0
                          have hbad : (none : Option Store) = some callargs :=
                            hdecNone.symm.trans hdecSome
                          cases hbad
                    · have hsecretsStart0 :
                          UInt256.slt
                            (((⟨4⟩ : UInt256) + revealSecretsOffsetWord I) + ⟨31⟩)
                            (UInt256.ofNat I.calldata.size) = ⟨0⟩ :=
                        uslt_eq_zero_of_ne_one hsecretsStart
                      exact RD.blindAuctionRevealDecodeArray1713_startRevert rd1713s
                        hsecretsStart0 (by simp)
            · have hfakesStart0 :
                  UInt256.slt (((⟨4⟩ : UInt256) + revealFakesOffsetWord I) + ⟨31⟩)
                    (UInt256.ofNat I.calldata.size) = ⟨0⟩ :=
                uslt_eq_zero_of_ne_one hfakesStart
              exact RD.blindAuctionRevealDecodeArray1713_startRevert rd1713f hfakesStart0
                (by simp)
    · have hvaluesStart0 :
          UInt256.slt (((⟨4⟩ : UInt256) + revealValuesOffsetWord I) + ⟨31⟩)
            (UInt256.ofNat I.calldata.size) = ⟨0⟩ :=
        uslt_eq_zero_of_ne_one hvaluesStart
      exact RD.blindAuctionRevealDecodeArray1713_startRevert rd1713v hvaluesStart0 (by simp)

/-! ### Scratch placeBid source-side routine -/


def scratch_placeBidStore (bidder : AccountAddress) (value : UInt256) : Store :=
  ((∅ : Store).insert "value" (.int (Int.ofNat value.toNat))).insert "bidder" (.address bidder)

def scratch_placeBidAfterPending (evm : EVM.State) (oldAddr : AccountAddress)
    (sum : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (pendingReturnsSlot (.address oldAddr)) sum

def scratch_placeBidAfterHigh (evm : EVM.State) (value : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩ value

def scratch_placeBidAfterBidder (evm : EVM.State) (bidder : AccountAddress) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩
    (SimpleAuction.simpleAuctionSetAddressWord
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩)
      (UInt256.ofNat bidder.val))

theorem scratch_addressWord_canonical (a : AccountAddress) :
    (UInt256.ofNat a.val).toNat < EVM.addressModulus := by
  rw [UInt256.toNat_ofNat_of_lt
    (lt_of_lt_of_le a.isLt (by decide : AccountAddress.size ≤ UInt256.size))]
  simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using a.isLt

theorem scratch_placeBidStore_value (bidder : AccountAddress) (value : UInt256) :
    (scratch_placeBidStore bidder value).get? "value" =
      some (.int (Int.ofNat value.toNat)) := by
  unfold scratch_placeBidStore
  rw [store_get_ne]
  · exact store_get_self _ _ _
  · decide

theorem scratch_placeBidStore_bidder (bidder : AccountAddress) (value : UInt256) :
    (scratch_placeBidStore bidder value).get? "bidder" = some (.address bidder) := by
  unfold scratch_placeBidStore
  exact store_get_self _ _ _

theorem scratch_placeBidStore_base_none (bidder : AccountAddress) (value : UInt256)
    {name : Ident} (hname : name ≠ "value") (hname' : name ≠ "bidder") :
    (scratch_placeBidStore bidder value).get? name = none := by
  unfold scratch_placeBidStore
  rw [store_get_ne]
  · rw [store_get_ne]
    · simp
    · simp [beq_eq_false_iff_ne]
      exact fun h => hname h.symm
  · simp [beq_eq_false_iff_ne]
    exact fun h => hname' h.symm

theorem scratch_placeBid_lookup :
    lookupCallable? blindAuctionContract "placeBid" = some placeBidFn.toCallable := by
  rfl

theorem scratch_placeBid_bind (bidder : AccountAddress) (value : UInt256) :
    bindParams? placeBidFn.params [.address bidder, .int (Int.ofNat value.toNat)] =
      some (scratch_placeBidStore bidder value) := by
  rfl

theorem scratch_blindAuctionStorageLocStore_address_offset0 (evm : EVM.State)
    (slot addr : UInt256) (hcanon : addr.toNat < EVM.addressModulus) :
    storageLocStore evm (blindAuctionAddrLoc slot)
        (.address (AccountAddress.ofNat addr.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (SimpleAuction.simpleAuctionSetAddressWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) addr)) := by
  simpa [blindAuctionAddrLoc, SimpleAuction.simpleAuctionAddrLoc] using
    SimpleAuction.simpleAuctionStorageLocStore_address_offset0 evm slot addr hcanon

theorem scratch_eval_placeBid_highestBid
    (evm : EVM.State) (bidder : AccountAddress) (value high : UInt256)
    (hhigh : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩ = high) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value } evm
      (.storage highestBidRef) = .ok (.int (Int.ofNat high.toNat)) := by
  rw [evalExpr_storage_scalar (cfg := blindAuctionConfig)
    (solm := { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value })
    (evm := evm)
    (slot := highestBidRef)
    (er := { base := "highestBid", steps := [] })
    (t := .int uint256Int)
    (loc := blindAuctionUint256Loc ⟨6⟩)]
  · rw [blindAuctionBiddingEndStorageLocLoad_uint256, hhigh]
  · exact scratch_placeBidStore_base_none bidder value (by decide) (by decide)
  · simp [evalStorageRef, evalStorageRefSteps, highestBidRef, EvalResult.bind, pure, bind]
  · simp [storageTypeAt?, blindAuctionContract, storageDecls, highestBidRef, uint256St]
  · exact blindAuctionConfig_storage_highestBid

theorem scratch_eval_placeBid_value_le_highestBid_true
    (evm : EVM.State) (bidder : AccountAddress) (value high : UInt256)
    (hhigh : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩ = high)
    (hle : value.toNat ≤ high.toNat) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value } evm
      (.binary .le (.var "value") (.storage highestBidRef)) = .ok (.bool true) := by
  rw [evalExpr?]
  simp only [evalExpr_reveal_var_int evm (scratch_placeBidStore bidder value) "value"
    (Int.ofNat value.toNat) (scratch_placeBidStore_value bidder value), EvalResult.bind, bind]
  rw [scratch_eval_placeBid_highestBid evm bidder value high hhigh]
  simp [evalBinaryOp?, hle]

theorem scratch_eval_placeBid_value_le_highestBid_false
    (evm : EVM.State) (bidder : AccountAddress) (value high : UInt256)
    (hhigh : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩ = high)
    (hlt : high.toNat < value.toNat) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value } evm
      (.binary .le (.var "value") (.storage highestBidRef)) = .ok (.bool false) := by
  rw [evalExpr?]
  simp only [evalExpr_reveal_var_int evm (scratch_placeBidStore bidder value) "value"
    (Int.ofNat value.toNat) (scratch_placeBidStore_value bidder value), EvalResult.bind, bind]
  rw [scratch_eval_placeBid_highestBid evm bidder value high hhigh]
  have hltInt : (Int.ofNat high.toNat) < Int.ofNat value.toNat := Int.ofNat_lt.mpr hlt
  have hnot : ¬ Int.ofNat value.toNat ≤ Int.ofNat high.toNat := not_le_of_gt hltInt
  simp [evalBinaryOp?, hnot, hlt]

theorem scratch_eval_placeBid_highestBidder
    (evm : EVM.State) (bidder : AccountAddress) (value old : UInt256)
    (hold : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = old) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value } evm
      (.storage highestBidderRef) =
        .ok (.address (AccountAddress.ofNat (UInt256.land old solcAddrMask).toNat)) := by
  rw [evalExpr_storage_scalar (cfg := blindAuctionConfig)
    (solm := { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value })
    (evm := evm)
    (slot := highestBidderRef)
    (er := { base := "highestBidder", steps := [] })
    (t := .address)
    (loc := blindAuctionAddrLoc ⟨5⟩)]
  · rw [highestBidderStorageLocLoad_address_offset0, hold]
  · exact scratch_placeBidStore_base_none bidder value (by decide) (by decide)
  · simp [evalStorageRef, evalStorageRefSteps, highestBidderRef, EvalResult.bind, pure, bind]
  · simp [storageTypeAt?, blindAuctionContract, storageDecls, highestBidderRef, addrSt]
  · exact blindAuctionConfig_storage_highestBidder

theorem scratch_eval_placeBid_highestBidder_ne_zero_false
    (evm : EVM.State) (bidder : AccountAddress) (value old : UInt256)
    (hold : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = old)
    (hzero : UInt256.land old solcAddrMask = ⟨0⟩) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value } evm
      (.binary .ne (.storage highestBidderRef) zeroAddr) = .ok (.bool false) := by
  rw [evalExpr?]
  simp only [scratch_eval_placeBid_highestBidder evm bidder value old hold,
    EvalResult.bind, bind]
  simp [zeroAddr, addrSt, evalExpr?, hzero, evalBinaryOp?, castValue?,
    EvalResult.ofOption, EvalResult.bind, bind, pure, AccountAddress.ofNat]

theorem scratch_eval_placeBid_highestBidder_ne_zero_true
    (evm : EVM.State) (bidder : AccountAddress) (value old : UInt256)
    (hold : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = old)
    (hnonzero : UInt256.land old solcAddrMask ≠ ⟨0⟩) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value } evm
      (.binary .ne (.storage highestBidderRef) zeroAddr) = .ok (.bool true) := by
  rw [evalExpr?]
  simp only [scratch_eval_placeBid_highestBidder evm bidder value old hold,
    EvalResult.bind, bind]
  by_cases haddr :
      AccountAddress.ofNat (UInt256.land old solcAddrMask).toNat = (0 : AccountAddress)
  · exfalso
    apply hnonzero
    apply u256_inj
    have hcanon := highestBidderSolcAddrMask_result_canonical old
    have hmod : (UInt256.land old solcAddrMask).toNat % AccountAddress.size =
        (UInt256.land old solcAddrMask).toNat := by
      apply Nat.mod_eq_of_lt
      simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon
    have hnat := congrArg Fin.val haddr
    simp [AccountAddress.ofNat, hmod] at hnat
    exact hnat
  · have hnotdiv : ¬ AccountAddress.size ∣ (UInt256.land old solcAddrMask).toNat := by
      intro hdiv
      have hcanon := highestBidderSolcAddrMask_result_canonical old
      have hltSize : (UInt256.land old solcAddrMask).toNat < AccountAddress.size := by
        simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon
      obtain ⟨k, hk⟩ := hdiv
      cases k with
      | zero =>
          apply hnonzero
          apply u256_inj
          simp [hk]
      | succ k =>
          have hle : AccountAddress.size ≤ (UInt256.land old solcAddrMask).toNat := by
            rw [hk]
            nlinarith [show 0 < AccountAddress.size by decide]
          omega
    simp [zeroAddr, addrSt, evalExpr?, evalBinaryOp?, castValue?, EvalResult.ofOption,
      EvalResult.bind, bind, pure, AccountAddress.ofNat, haddr, hnotdiv]

theorem scratch_evalStorageRef_placeBid_pendingReturns
    (evm : EVM.State) (bidder oldAddr : AccountAddress) (value old : UInt256)
    (hold : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = old)
    (holdAddr : oldAddr = AccountAddress.ofNat (UInt256.land old solcAddrMask).toNat) :
    evalStorageRef blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value } evm
      (pendingReturnsRef (.storage highestBidderRef)) =
    .ok { base := "pendingReturns", steps := [.mindex (.address oldAddr)] } := by
  subst oldAddr
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, pendingReturnsRef,
    scratch_eval_placeBid_highestBidder evm bidder value old hold, valueToKey?,
    EvalResult.ofOption, EvalResult.bind, pure, bind]

theorem scratch_eval_placeBid_pendingReturns
    (evm : EVM.State) (bidder oldAddr : AccountAddress) (value old pending : UInt256)
    (hold : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = old)
    (holdAddr : oldAddr = AccountAddress.ofNat (UInt256.land old solcAddrMask).toNat)
    (hpending : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (pendingReturnsSlot (.address oldAddr)) = pending) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value } evm
      (.storage (pendingReturnsRef (.storage highestBidderRef))) =
        .ok (.int (Int.ofNat pending.toNat)) := by
  rw [evalExpr_storage_scalar (cfg := blindAuctionConfig)
    (solm := { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value })
    (evm := evm)
    (slot := pendingReturnsRef (.storage highestBidderRef))
    (er := { base := "pendingReturns", steps := [.mindex (.address oldAddr)] })
    (t := .int uint256Int)
    (loc := blindAuctionUint256Loc (pendingReturnsSlot (.address oldAddr)))]
  · rw [blindAuctionBiddingEndStorageLocLoad_uint256, hpending]
  · exact scratch_placeBidStore_base_none bidder value (by decide) (by decide)
  · exact scratch_evalStorageRef_placeBid_pendingReturns evm bidder oldAddr value old hold holdAddr
  · simp [storageTypeAt?, blindAuctionContract, storageDecls, storageTypeStep?,
      pendingReturnsRef, uint256St]
  · exact blindAuctionConfig_storage_pendingReturns (.address oldAddr)

theorem scratch_eval_placeBid_pending_add
    (evm : EVM.State) (bidder oldAddr : AccountAddress) (value old high pending : UInt256)
    (hhigh : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩ = high)
    (hold : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = old)
    (holdAddr : oldAddr = AccountAddress.ofNat (UInt256.land old solcAddrMask).toNat)
    (hpending : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (pendingReturnsSlot (.address oldAddr)) = pending)
    (hsum : pending.toNat + high.toNat < UInt256.size) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value } evm
      (u256 (.binary .add (.storage (pendingReturnsRef (.storage highestBidderRef)))
        (.storage highestBidRef))) =
        .ok (.int (Int.ofNat (pending.toNat + high.toNat))) := by
  unfold u256
  rw [evalExpr?]
  rw [evalExpr?]
  simp only [scratch_eval_placeBid_pendingReturns evm bidder oldAddr value old pending hold
      holdAddr hpending,
    scratch_eval_placeBid_highestBid evm bidder value high hhigh,
    EvalResult.bind, bind]
  simp [evalBinaryOp?]
  have hnonneg : ¬ (((pending.toNat : Int) + (high.toNat : Int)) < 0) := by
    exact not_lt_of_ge (Int.add_nonneg (Int.ofNat_nonneg _) (Int.ofNat_nonneg _))
  have hlt : ¬ ((2 : Int) ^ 256 ≤ (pending.toNat : Int) + (high.toNat : Int)) := by
    norm_num [UInt256.size] at hsum ⊢
    omega
  have hif :
      ¬ ((pending.toNat : Int) + (high.toNat : Int) < 0 ∨
        (2 : Int) ^ 256 ≤ (pending.toNat : Int) + (high.toNat : Int)) := by
    intro hcond
    rcases hcond with hneg | hge
    · exact hnonneg hneg
    · apply hlt
      norm_num at hge ⊢
      exact hge
  simp only [uint256Int]
  rw [if_neg hif]
  rfl

theorem scratch_eval_placeBid_pending_add_revert
    (evm : EVM.State) (bidder oldAddr : AccountAddress) (value old high pending : UInt256)
    (hhigh : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩ = high)
    (hold : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = old)
    (holdAddr : oldAddr = AccountAddress.ofNat (UInt256.land old solcAddrMask).toNat)
    (hpending : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (pendingReturnsSlot (.address oldAddr)) = pending)
    (hover : UInt256.size ≤ pending.toNat + high.toNat) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value } evm
      (u256 (.binary .add (.storage (pendingReturnsRef (.storage highestBidderRef)))
        (.storage highestBidRef))) = .revert := by
  unfold u256
  rw [evalExpr?]
  rw [evalExpr?]
  simp only [scratch_eval_placeBid_pendingReturns evm bidder oldAddr value old pending hold
      holdAddr hpending,
    scratch_eval_placeBid_highestBid evm bidder value high hhigh,
    EvalResult.bind, bind]
  simp [evalBinaryOp?]
  have hnonneg : ¬ (((pending.toNat : Int) + (high.toNat : Int)) < 0) := by
    exact not_lt_of_ge (Int.add_nonneg (Int.ofNat_nonneg _) (Int.ofNat_nonneg _))
  have hge : (2 : Int) ^ 256 ≤ (pending.toNat : Int) + (high.toNat : Int) := by
    norm_num [UInt256.size] at hover ⊢
    omega
  have hif :
      (pending.toNat : Int) + (high.toNat : Int) < 0 ∨
        (2 : Int) ^ 256 ≤ (pending.toNat : Int) + (high.toNat : Int) := by
    right
    norm_num at hge ⊢
    exact hge
  simp only [uint256Int]
  rw [if_pos hif]

theorem scratch_assign_placeBid_pendingReturns
    (evm : EVM.State) (bidder oldAddr : AccountAddress)
    (value old pending high : UInt256)
    (hold : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = old)
    (holdAddr : oldAddr = AccountAddress.ofNat (UInt256.land old solcAddrMask).toNat)
    (hsum : pending.toNat + high.toNat < UInt256.size) :
    assignStorageRef? blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value } evm
      .storage (pendingReturnsRef (.storage highestBidderRef))
      (.int (Int.ofNat (pending.toNat + high.toNat))) =
    .ok ({ contract := blindAuctionContract, locals := scratch_placeBidStore bidder value },
      scratch_placeBidAfterPending evm oldAddr (UInt256.ofNat (pending.toNat + high.toNat))) := by
  unfold scratch_placeBidAfterPending
  have hsumToNat : (UInt256.ofNat (pending.toNat + high.toNat)).toNat =
      pending.toNat + high.toNat := UInt256.toNat_ofNat_of_lt hsum
  exact assignStorageRef_storage_scalar
    (cfg := blindAuctionConfig)
    (solm := { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value })
    (evm := evm)
    (evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (pendingReturnsSlot (.address oldAddr)) (UInt256.ofNat (pending.toNat + high.toNat)))
    (slot := pendingReturnsRef (.storage highestBidderRef))
    (er := { base := "pendingReturns", steps := [.mindex (.address oldAddr)] })
    (ty := uint256St)
    (loc := blindAuctionUint256Loc (pendingReturnsSlot (.address oldAddr)))
    (n := Int.ofNat (pending.toNat + high.toNat))
    (scratch_placeBidStore_base_none bidder value (by decide) (by decide))
    (scratch_evalStorageRef_placeBid_pendingReturns evm bidder oldAddr value old hold holdAddr)
    (by simp [storageTypeAt?, blindAuctionContract, storageDecls, storageTypeStep?, pendingReturnsRef])
    (blindAuctionConfig_storage_pendingReturns (.address oldAddr))
    (by
      simpa [hsumToNat] using
        blindAuctionStorageLocStore_uint256_natCast evm
          (pendingReturnsSlot (.address oldAddr))
          (UInt256.ofNat (pending.toNat + high.toNat)))

theorem scratch_assign_placeBid_highestBid
    (evm : EVM.State) (bidder : AccountAddress) (value : UInt256) :
    assignStorageRef? blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value } evm
      .storage highestBidRef (.int (Int.ofNat value.toNat)) =
    .ok ({ contract := blindAuctionContract, locals := scratch_placeBidStore bidder value },
      scratch_placeBidAfterHigh evm value) := by
  unfold scratch_placeBidAfterHigh
  exact assignStorageRef_storage_scalar
    (cfg := blindAuctionConfig)
    (solm := { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value })
    (evm := evm)
    (evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩ value)
    (slot := highestBidRef)
    (er := { base := "highestBid", steps := [] })
    (ty := uint256St)
    (loc := blindAuctionUint256Loc ⟨6⟩)
    (n := Int.ofNat value.toNat)
    (scratch_placeBidStore_base_none bidder value (by decide) (by decide))
    (by simp [evalStorageRef, evalStorageRefSteps, highestBidRef, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, blindAuctionContract, storageDecls, highestBidRef])
    blindAuctionConfig_storage_highestBid
    (blindAuctionStorageLocStore_uint256_natCast evm ⟨6⟩ value)

theorem scratch_assign_placeBid_highestBidder
    (evm : EVM.State) (bidder : AccountAddress) (value : UInt256) :
    assignStorageRef? blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value } evm
      .storage highestBidderRef (.address bidder) =
    .ok ({ contract := blindAuctionContract, locals := scratch_placeBidStore bidder value },
      scratch_placeBidAfterBidder evm bidder) := by
  unfold scratch_placeBidAfterBidder
  have haddrOfNat : AccountAddress.ofNat (UInt256.ofNat bidder.val).toNat = bidder := by
    apply Fin.ext
    rw [UInt256.toNat_ofNat_of_lt
      (lt_of_lt_of_le bidder.isLt (by decide : AccountAddress.size ≤ UInt256.size))]
    simp [AccountAddress.ofNat, Nat.mod_eq_of_lt bidder.isLt]
  have hstore :
      storageLocStore evm (blindAuctionAddrLoc ⟨5⟩) (.address bidder) =
        some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩
          (SimpleAuction.simpleAuctionSetAddressWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩)
            (UInt256.ofNat bidder.val))) := by
    simpa [haddrOfNat] using
      scratch_blindAuctionStorageLocStore_address_offset0 evm ⟨5⟩ (UInt256.ofNat bidder.val)
        (scratch_addressWord_canonical bidder)
  exact assignStorageRef_storage_scalar_value
    (cfg := blindAuctionConfig)
    (solm := { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value })
    (evm := evm)
    (evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩
      (SimpleAuction.simpleAuctionSetAddressWord
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩) (UInt256.ofNat bidder.val)))
    (slot := highestBidderRef)
    (er := { base := "highestBidder", steps := [] })
    (ty := addrSt)
    (loc := blindAuctionAddrLoc ⟨5⟩)
    (value := .address bidder)
    (scratch_placeBidStore_base_none bidder value (by decide) (by decide))
    (by simp [evalStorageRef, evalStorageRefSteps, highestBidderRef, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, blindAuctionContract, storageDecls, highestBidderRef, addrSt])
    blindAuctionConfig_storage_highestBidder
    (by trivial)
    hstore

theorem scratch_blindAuctionPlaceBidBodyReturns_false
    (evm : EVM.State) (bidder : AccountAddress) (value high : UInt256)
    (hhigh : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩ = high)
    (hle : value.toNat ≤ high.toNat) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm
      (scratch_placeBidStore bidder value) placeBidFn.body
      (.returned { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value }
        evm (some (.bool false))) := by
  refine ExecFuncBody.execBlockRet ?_
  unfold placeBidFn
  refine ExecBlock.consReturn ?_
  refine ExecStmt.iteTrue ?_ ?_
  · exact scratch_eval_placeBid_value_le_highestBid_true evm bidder value high hhigh hle
  · exact ExecBlock.consReturn (ExecStmt.return (by simp [evalExpr?, pure]))

theorem scratch_blindAuctionPlaceBidBodyReturns_true_zero
    (evm : EVM.State) (bidder : AccountAddress) (value high old : UInt256)
    (hhigh : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩ = high)
    (hold : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = old)
    (hlt : high.toNat < value.toNat)
    (hzero : UInt256.land old solcAddrMask = ⟨0⟩) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm
      (scratch_placeBidStore bidder value) placeBidFn.body
      (.returned { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value }
        (scratch_placeBidAfterBidder (scratch_placeBidAfterHigh evm value) bidder)
        (some (.bool true))) := by
  refine ExecFuncBody.execBlockRet ?_
  unfold placeBidFn
  change ExecBlock blindAuctionConfig
    { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value } evm
    [ .ite (.binary .le (.var "value") (.storage highestBidRef))
        [ .return (.boolLit false) ] [],
      .ite (.binary .ne (.storage highestBidderRef) zeroAddr)
        [ .assign .storage (pendingReturnsRef (.storage highestBidderRef))
            (u256 (.binary .add
              (.storage (pendingReturnsRef (.storage highestBidderRef)))
              (.storage highestBidRef))) ] [],
      .assign .storage highestBidRef (.var "value"),
      .assign .storage highestBidderRef (.var "bidder"),
      .return (.boolLit true) ]
    (.returned { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value }
      (scratch_placeBidAfterBidder (scratch_placeBidAfterHigh evm value) bidder)
      (some (.bool true)))
  refine ExecBlock.consNormal
    (solm' := { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value })
    (evm' := evm) ?_ ?_
  · exact ExecStmt.iteFalse
      (scratch_eval_placeBid_value_le_highestBid_false evm bidder value high hhigh hlt)
      ExecBlock.nil
  refine ExecBlock.consNormal
    (solm' := { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value })
    (evm' := evm) ?_ ?_
  · exact ExecStmt.iteFalse
      (scratch_eval_placeBid_highestBidder_ne_zero_false evm bidder value old hold hzero)
      ExecBlock.nil
  refine ExecBlock.consNormal
    (solm' := { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value })
    (evm' := scratch_placeBidAfterHigh evm value) ?_ ?_
  · exact ExecStmt.assign
      (evalExpr_reveal_var_int evm (scratch_placeBidStore bidder value) "value"
        (Int.ofNat value.toNat) (scratch_placeBidStore_value bidder value))
      (scratch_assign_placeBid_highestBid evm bidder value)
  refine ExecBlock.consNormal
    (solm' := { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value })
    (evm' := scratch_placeBidAfterBidder (scratch_placeBidAfterHigh evm value) bidder) ?_ ?_
  · exact ExecStmt.assign
      (evalExpr_reveal_var_value (scratch_placeBidAfterHigh evm value)
        (scratch_placeBidStore bidder value) "bidder" (.address bidder)
        (scratch_placeBidStore_bidder bidder value))
      (scratch_assign_placeBid_highestBidder (scratch_placeBidAfterHigh evm value) bidder value)
  exact ExecBlock.consReturn (ExecStmt.return (by simp [evalExpr?, pure]))

theorem scratch_blindAuctionPlaceBidBodyReturns_true_nonzero
    (evm : EVM.State) (bidder oldAddr : AccountAddress)
    (value high old pending : UInt256)
    (hhigh : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩ = high)
    (hold : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = old)
    (holdAddr : oldAddr = AccountAddress.ofNat (UInt256.land old solcAddrMask).toNat)
    (hpending : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (pendingReturnsSlot (.address oldAddr)) = pending)
    (hlt : high.toNat < value.toNat)
    (hnonzero : UInt256.land old solcAddrMask ≠ ⟨0⟩)
    (hsum : pending.toNat + high.toNat < UInt256.size) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm
      (scratch_placeBidStore bidder value) placeBidFn.body
      (.returned { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value }
        (scratch_placeBidAfterBidder
          (scratch_placeBidAfterHigh
            (scratch_placeBidAfterPending evm oldAddr
              (UInt256.ofNat (pending.toNat + high.toNat))) value) bidder)
        (some (.bool true))) := by
  refine ExecFuncBody.execBlockRet ?_
  unfold placeBidFn
  change ExecBlock blindAuctionConfig
    { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value } evm
    [ .ite (.binary .le (.var "value") (.storage highestBidRef))
        [ .return (.boolLit false) ] [],
      .ite (.binary .ne (.storage highestBidderRef) zeroAddr)
        [ .assign .storage (pendingReturnsRef (.storage highestBidderRef))
            (u256 (.binary .add
              (.storage (pendingReturnsRef (.storage highestBidderRef)))
              (.storage highestBidRef))) ] [],
      .assign .storage highestBidRef (.var "value"),
      .assign .storage highestBidderRef (.var "bidder"),
      .return (.boolLit true) ]
    (.returned { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value }
      (scratch_placeBidAfterBidder
        (scratch_placeBidAfterHigh
          (scratch_placeBidAfterPending evm oldAddr
            (UInt256.ofNat (pending.toNat + high.toNat))) value) bidder)
      (some (.bool true)))
  refine ExecBlock.consNormal
    (solm' := { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value })
    (evm' := evm) ?_ ?_
  · exact ExecStmt.iteFalse
      (scratch_eval_placeBid_value_le_highestBid_false evm bidder value high hhigh hlt)
      ExecBlock.nil
  refine ExecBlock.consNormal
    (solm' := { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value })
    (evm' := scratch_placeBidAfterPending evm oldAddr
      (UInt256.ofNat (pending.toNat + high.toNat))) ?_ ?_
  · refine ExecStmt.iteTrue
      (scratch_eval_placeBid_highestBidder_ne_zero_true evm bidder value old hold hnonzero) ?_
    refine ExecBlock.consNormal
      (solm' := { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value })
      (evm' := scratch_placeBidAfterPending evm oldAddr
        (UInt256.ofNat (pending.toNat + high.toNat))) ?_
      (ExecBlock.nil (cfg := blindAuctionConfig)
        (solm := { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value })
        (evm := scratch_placeBidAfterPending evm oldAddr
          (UInt256.ofNat (pending.toNat + high.toNat))))
    exact ExecStmt.assign
      (scratch_eval_placeBid_pending_add evm bidder oldAddr value old high pending hhigh hold
        holdAddr hpending hsum)
      (scratch_assign_placeBid_pendingReturns evm bidder oldAddr value old pending high hold
        holdAddr hsum)
  refine ExecBlock.consNormal
    (solm' := { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value })
    (evm' := scratch_placeBidAfterHigh
      (scratch_placeBidAfterPending evm oldAddr
        (UInt256.ofNat (pending.toNat + high.toNat))) value) ?_ ?_
  · exact ExecStmt.assign
      (evalExpr_reveal_var_int (scratch_placeBidAfterPending evm oldAddr
          (UInt256.ofNat (pending.toNat + high.toNat)))
        (scratch_placeBidStore bidder value) "value" (Int.ofNat value.toNat)
        (scratch_placeBidStore_value bidder value))
      (scratch_assign_placeBid_highestBid
        (scratch_placeBidAfterPending evm oldAddr (UInt256.ofNat (pending.toNat + high.toNat)))
        bidder value)
  refine ExecBlock.consNormal
    (solm' := { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value })
    (evm' := scratch_placeBidAfterBidder
      (scratch_placeBidAfterHigh
        (scratch_placeBidAfterPending evm oldAddr
          (UInt256.ofNat (pending.toNat + high.toNat))) value) bidder) ?_ ?_
  · exact ExecStmt.assign
      (evalExpr_reveal_var_value
        (scratch_placeBidAfterHigh
          (scratch_placeBidAfterPending evm oldAddr
            (UInt256.ofNat (pending.toNat + high.toNat))) value)
        (scratch_placeBidStore bidder value) "bidder" (.address bidder)
        (scratch_placeBidStore_bidder bidder value))
      (scratch_assign_placeBid_highestBidder
        (scratch_placeBidAfterHigh
          (scratch_placeBidAfterPending evm oldAddr
            (UInt256.ofNat (pending.toNat + high.toNat))) value)
        bidder value)
  exact ExecBlock.consReturn (ExecStmt.return (by simp [evalExpr?, pure]))

/-! ### Scratch placeBid EVM-side routine -/

def scratch_placeBidHighestBidWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨6⟩ ⟨0⟩)

def scratch_placeBidHighestBidderWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨5⟩ ⟨0⟩)

def scratch_placeBidStoreHighMap (σ : AccountMap) (I : ExecutionEnv) (value : UInt256) :
    AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨6⟩ value

def scratch_placeBidStoreBidderMap (σ : AccountMap) (I : ExecutionEnv) (bidder : UInt256) :
    AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨5⟩
    (SimpleAuction.simpleAuctionSetAddressWord
      (scratch_placeBidHighestBidderWord σ I) bidder)

set_option maxHeartbeats 1000000 in
theorem scratch_RD_placeBid_false {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {k C : Nat} {value bidder ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    (rd : RD blindAuctionBytecode I g s0 ⟨1534⟩ (value :: bidder :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hle : value.toNat ≤ (scratch_placeBidHighestBidWord σ I).toNat)
    (hret : (D_J blindAuctionBytecode 0).contains ret = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ret (⟨0⟩ :: R)
      mem aw rdata (cA, σ) k' C' := by
  have rd1538 := evm_run rd with [jumpdest, push0, push1 ⟨6⟩]
  obtain ⟨_, _, rd1539₀⟩ := rd1538.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1539⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1539⟩
      (scratch_placeBidHighestBidWord σ I :: ⟨0⟩ :: value :: bidder :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidHighestBidWord] using rd1539₀⟩
  have hgt : UInt256.gt value (scratch_placeBidHighestBidWord σ I) = ⟨0⟩ := ugt_zero hle
  have rd1540₀ := evm_run rd1539 with [dup3, gt]
  have rd1540 := rd1540₀
  rw [hgt] at rd1540
  have rd1544 := evm_run rd1540 with [push2 ⟨1551⟩, jumpiNT (by decide)]
  have rd1655 := evm_run rd1544 with [pop, push0, push2 ⟨1654⟩,
    jump (by jump_dest), jumpdest]
  exact ⟨_, _, evm_run rd1655 with [swap3, swap2, pop, pop, jump hret]⟩

theorem scratch_blindAuctionCheckedAddNoOverflowGt (a b : UInt256)
    (hfit : a.toNat + b.toNat < UInt256.size) :
    UInt256.gt a (b + a) = ⟨0⟩ := by
  have hsum : (b + a).toNat = b.toNat + a.toNat := by
    rw [uadd_toNat]
    have hfit' : b.toNat + a.toNat < UInt256.size := by omega
    exact Nat.mod_eq_of_lt hfit'
  have hle : a.toNat ≤ (b + a).toNat := by
    rw [hsum]
    omega
  exact ugt_zero hle

theorem scratch_blindAuctionCheckedAddOverflowGt (a b : UInt256)
    (hover : UInt256.size ≤ a.toNat + b.toNat) :
    UInt256.gt a (b + a) = ⟨1⟩ := by
  have hover' : UInt256.size ≤ b.toNat + a.toNat := by omega
  have hsum_lt2 : b.toNat + a.toNat < 2 * UInt256.size := by
    have ha : a.toNat < UInt256.size := a.val.isLt
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega
  have hmod : (b.toNat + a.toNat) % UInt256.size =
      b.toNat + a.toNat - UInt256.size := by
    rw [Nat.mod_eq_sub_mod hover']
    rw [Nat.mod_eq_of_lt (by omega)]
  have hsum : (b + a).toNat = b.toNat + a.toNat - UInt256.size := by
    rw [uadd_toNat, hmod]
  show UInt256.fromBool (decide (a > b + a)) = ⟨1⟩
  rw [decide_eq_true]
  · rfl
  · show a.toNat > (b + a).toNat
    rw [hsum]
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega

set_option maxHeartbeats 1000000 in
theorem scratch_blindAuctionCheckedAddOk {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {a b ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    (rd : RD blindAuctionBytecode ee g s0 ⟨2045⟩ (a :: b :: ret :: R)
      mem aw rdata acc k C)
    (hfit : a.toNat + b.toNat < UInt256.size)
    (hret : (D_J blindAuctionBytecode 0).contains ret = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD blindAuctionBytecode ee g s0 ret ((b + a) :: R)
      mem aw rdata acc k' C' := by
  have hgt := scratch_blindAuctionCheckedAddNoOverflowGt a b hfit
  have rd2052₀ := evm_run rd with [jumpdest, dup1, dup3, add, dup1, dup3, gt]
  have rd2052 := rd2052₀
  rw [hgt] at rd2052
  have rd2056 := evm_run rd2052 with [iszero, push2 ⟨1654⟩,
    jumpiT one_ne_zero_uint (by jump_dest)]
  exact ⟨_, _, evm_run rd2056 with [jumpdest, swap3, swap2, pop, pop, jump hret]⟩

theorem scratch_blindAuctionCheckedSubOk {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {a b ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    (rd : RD blindAuctionBytecode ee g s0 ⟨2064⟩ (a :: b :: ret :: R)
      mem aw rdata acc k C)
    (hle : b.toNat ≤ a.toNat)
    (hret : (D_J blindAuctionBytecode 0).contains ret = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD blindAuctionBytecode ee g s0 ret (UInt256.sub a b :: R)
      mem aw rdata acc k' C' := by
  have hsubNat : (UInt256.sub a b).toNat = a.toNat - b.toNat := usub_toNat hle
  have hgt : UInt256.gt (UInt256.sub a b) a = ⟨0⟩ :=
    Reasoning.Theory.ugt_zero (by rw [hsubNat]; omega)
  have rd2071₀ := evm_run rd with [jumpdest, dup2, dup2, sub, dup2, dup2, gt]
  have rd2071 := rd2071₀
  rw [hgt] at rd2071
  have rd2072₀ := evm_run rd2071 with [iszero]
  have rd2072 := rd2072₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd2072
  have rd1654 := evm_run rd2072 with [push2 ⟨1654⟩,
    jumpiT one_ne_zero_uint (by jump_dest)]
  exact ⟨_, _, evm_run rd1654 with [jumpdest, swap3, swap2, pop, pop, jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem scratch_blindAuctionRevealX_refundAdd_toPlaceCond {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {secret fake value slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen
      fakesEnd valuesLen valuesEnd sel deposit : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1247⟩
      [secret, fake, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hdeposit :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (slot + ⟨1⟩) ⟨0⟩) = deposit)
    (hfit : refund.toNat + deposit.toNat < UInt256.size) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1265⟩
      [secret, fake, value, slot, i, deposit + refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k' C' := by
  have rd1252₀ := evm_run rd with [jumpdest, push1 ⟨1⟩, dup5, add]
  obtain ⟨_, _, rd1253₀⟩ := rd1252₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1253⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1253⟩
      [deposit, secret, fake, value, slot, i, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [hdeposit] using rd1253₀⟩
  have rd2045 := evm_run rd1253 with [push2 ⟨1262⟩, swap1, dup8, push2 ⟨2045⟩,
    jump (by jump_dest)]
  obtain ⟨_, _, rd1262⟩ :=
    scratch_blindAuctionCheckedAddOk
      (a := refund) (b := deposit) (ret := ⟨1262⟩)
      (R := [secret, fake, value, slot, i, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel])
      rd2045 hfit (by jump_dest) (by simp)
  have rd1265 := evm_run rd1262 with [jumpdest, swap6, pop]
  exact ⟨_, _, by simpa using rd1265⟩

theorem scratch_blindAuctionRevealX_placeCond_fake_toZero {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {secret value slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen
      fakesEnd valuesLen valuesEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1265⟩
      [secret, ⟨1⟩, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1315⟩
      [secret, ⟨1⟩, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k' C' := by
  have rd1283 := evm_run rd with [dup2, iszero, dup1, iszero, push2 ⟨1282⟩,
    jumpiT one_ne_zero_uint (by jump_dest), jumpdest]
  exact ⟨_, _, evm_run rd1283 with [iszero, push2 ⟨1315⟩,
    jumpiT one_ne_zero_uint (by jump_dest)]⟩

theorem scratch_blindAuctionRevealX_placeCond_depositLt_toZero {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {secret value slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen
      fakesEnd valuesLen valuesEnd sel deposit : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1265⟩
      [secret, ⟨0⟩, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hdeposit :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (slot + ⟨1⟩) ⟨0⟩) = deposit)
    (hlt : deposit.toNat < value.toNat) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1315⟩
      [secret, ⟨0⟩, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k' C' := by
  have rd1273 := evm_run rd with [dup2, iszero, dup1, iszero, push2 ⟨1282⟩,
    jumpiNT (by decide), pop, dup3, dup5, push1 ⟨1⟩, add]
  obtain ⟨_, _, rd1280₀⟩ := rd1273.sload (by decide) (by evm_ov)
  have hdeposit' :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (⟨1⟩ + slot) ⟨0⟩) = deposit := by
    simpa [blindAuctionU256_add_comm] using hdeposit
  have hltw : UInt256.lt deposit value = ⟨1⟩ := ult_one hlt
  have rd1281₀ := evm_run rd1280₀ with [lt]
  have rd1281 := rd1281₀
  rw [hdeposit', hltw] at rd1281
  have rd1283 := evm_run rd1281 with [iszero, jumpdest]
  exact ⟨_, _, evm_run rd1283 with [iszero, push2 ⟨1315⟩,
    jumpiT one_ne_zero_uint (by jump_dest)]⟩

theorem scratch_blindAuctionRevealX_placeCond_place_toRoutine {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {secret value slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen
      fakesEnd valuesLen valuesEnd sel deposit : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1265⟩
      [secret, ⟨0⟩, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hdeposit :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (slot + ⟨1⟩) ⟨0⟩) = deposit)
    (hge : value.toNat ≤ deposit.toNat) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1534⟩
      [value, UInt256.ofNat I.source.val, ⟨1297⟩, secret, ⟨0⟩, value, slot, i, refund,
        len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen,
        valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k' C' := by
  have rd1273 := evm_run rd with [dup2, iszero, dup1, iszero, push2 ⟨1282⟩,
    jumpiNT (by decide), pop, dup3, dup5, push1 ⟨1⟩, add]
  obtain ⟨_, _, rd1280₀⟩ := rd1273.sload (by decide) (by evm_ov)
  have hdeposit' :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (⟨1⟩ + slot) ⟨0⟩) = deposit := by
    simpa [blindAuctionU256_add_comm] using hdeposit
  have hltw : UInt256.lt deposit value = ⟨0⟩ := ult_zero hge
  have rd1281₀ := evm_run rd1280₀ with [lt]
  have rd1281 := rd1281₀
  rw [hdeposit', hltw] at rd1281
  have rd1288 := evm_run rd1281 with [iszero, jumpdest, iszero, push2 ⟨1315⟩,
    jumpiNT (by decide)]
  exact ⟨_, _, evm_run rd1288 with [push2 ⟨1297⟩, caller, dup5, push2 ⟨1534⟩,
    jump (by jump_dest)]⟩

theorem scratch_blindAuctionRevealX_placeCond_fake_toNext {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {secret value slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen
      fakesEnd valuesLen valuesEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1265⟩
      [secret, ⟨1⟩, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hperm : I.perm = true) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1014⟩
      (scratch_revealEvmLoopStack (i + ⟨1⟩) refund len revealEnd biddingEnd secretsLen
        secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
      mem aw rdata (cA, sstoreAccountMap I.codeOwner σ slot ⟨0⟩) k' C' := by
  obtain ⟨_, _, rd1315⟩ := scratch_blindAuctionRevealX_placeCond_fake_toZero rd
  exact scratch_blindAuctionRevealX_zeroBlinded_toNext rd1315 hperm

theorem scratch_blindAuctionRevealX_placeCond_depositLt_toNext {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {secret value slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen
      fakesEnd valuesLen valuesEnd sel deposit : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1265⟩
      [secret, ⟨0⟩, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hdeposit :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (slot + ⟨1⟩) ⟨0⟩) = deposit)
    (hlt : deposit.toNat < value.toNat)
    (hperm : I.perm = true) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1014⟩
      (scratch_revealEvmLoopStack (i + ⟨1⟩) refund len revealEnd biddingEnd secretsLen
        secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
      mem aw rdata (cA, sstoreAccountMap I.codeOwner σ slot ⟨0⟩) k' C' := by
  obtain ⟨_, _, rd1315⟩ :=
    scratch_blindAuctionRevealX_placeCond_depositLt_toZero rd hdeposit hlt
  exact scratch_blindAuctionRevealX_zeroBlinded_toNext rd1315 hperm

theorem scratch_blindAuctionRevealX_placeBidFalse_toNext {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {secret value slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen
      fakesEnd valuesLen valuesEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1297⟩
      [⟨0⟩, secret, ⟨0⟩, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hperm : I.perm = true) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1014⟩
      (scratch_revealEvmLoopStack (i + ⟨1⟩) refund len revealEnd biddingEnd secretsLen
        secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
      mem aw rdata (cA, sstoreAccountMap I.codeOwner σ slot ⟨0⟩) k' C' := by
  have rd1315 := evm_run rd with [jumpdest, iszero, push2 ⟨1315⟩,
    jumpiT one_ne_zero_uint (by jump_dest)]
  exact scratch_blindAuctionRevealX_zeroBlinded_toNext rd1315 hperm

theorem scratch_blindAuctionRevealX_placeBidTrue_toNext {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {secret value slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen
      fakesEnd valuesLen valuesEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1297⟩
      [⟨1⟩, secret, ⟨0⟩, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hrefund : value.toNat ≤ refund.toNat)
    (hperm : I.perm = true) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1014⟩
      (scratch_revealEvmLoopStack (i + ⟨1⟩) (UInt256.sub refund value) len revealEnd
        biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
      mem aw rdata (cA, sstoreAccountMap I.codeOwner σ slot ⟨0⟩) k' C' := by
  have rd1303 := evm_run rd with [jumpdest, iszero, push2 ⟨1315⟩, jumpiNT (by decide)]
  have rd2064 := evm_run rd1303 with [push2 ⟨1312⟩, dup4, dup8, push2 ⟨2064⟩,
    jump (by jump_dest)]
  obtain ⟨_, _, rd1312⟩ :=
    scratch_blindAuctionCheckedSubOk
      (a := refund) (b := value) (ret := ⟨1312⟩)
      (R := [secret, ⟨0⟩, value, slot, i, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel])
      rd2064 hrefund (by jump_dest) (by simp)
  have rd1315 := evm_run rd1312 with [jumpdest, swap6, pop]
  exact scratch_blindAuctionRevealX_zeroBlinded_toNext rd1315 hperm

-- LIBRARY CANDIDATE: generic OR xstep/RD.or, analogous to the other binary-op wrappers.
theorem scratchOr_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.OR, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s =
      (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
       else .ok (stBinop s (UInt256.lor a b) t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.OR, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_or s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 1 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stBinop]

theorem RD.scratchOr {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.OR, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.lor a b :: t) mem aw rdata acc (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => scratchOr_xstep hc hp hdec hs hov)

-- LIBRARY CANDIDATE: `Reasoning.EVMWord`, same proof shape as SimpleAuction's local lemma.
theorem scratchNat_lor_comm (a b : Nat) : Nat.lor a b = Nat.lor b a := by
  apply Nat.eq_of_testBit_eq
  intro i
  show (a ||| b).testBit i = (b ||| a).testBit i
  rw [Nat.testBit_or, Nat.testBit_or, Bool.or_comm]

-- LIBRARY CANDIDATE: `Reasoning.EVMWord`, same proof shape as SimpleAuction's local lemma.
theorem scratchU256_lor_comm (a b : UInt256) : UInt256.lor a b = UInt256.lor b a := by
  apply u256_inj
  show Nat.lor a.toNat b.toNat % UInt256.size =
    Nat.lor b.toNat a.toNat % UInt256.size
  rw [scratchNat_lor_comm]

theorem scratch_placeBidPackedBidderWord_eq_setAddress (old bidder : UInt256)
    (hcanon : bidder.toNat < EVM.addressModulus) :
    UInt256.lor (UInt256.land bidder solcAddrMask)
        (UInt256.land (UInt256.lnot solcAddrMask) old) =
      SimpleAuction.simpleAuctionSetAddressWord old bidder := by
  unfold SimpleAuction.simpleAuctionSetAddressWord
  rw [highestBidderU256_land_comm (UInt256.lnot solcAddrMask) old]
  rw [solcAddrMask_clean hcanon]
  exact scratchU256_lor_comm bidder (UInt256.land old (UInt256.lnot solcAddrMask))

set_option maxHeartbeats 1000000 in
theorem scratch_RD_placeBid_true_zero {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {k C : Nat} {value bidder ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    (rd : RD blindAuctionBytecode I g s0 ⟨1534⟩ (value :: bidder :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hperm : I.perm = true)
    (hlt : (scratch_placeBidHighestBidWord σ I).toNat < value.toNat)
    (hzero : UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask = ⟨0⟩)
    (hbidderCanon : bidder.toNat < EVM.addressModulus)
    (hret : (D_J blindAuctionBytecode 0).contains ret = true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ret (⟨1⟩ :: R)
      mem aw rdata
      (cA, scratch_placeBidStoreBidderMap
        (scratch_placeBidStoreHighMap σ I value) I bidder) k' C' := by
  have rd1538 := evm_run rd with [jumpdest, push0, push1 ⟨6⟩]
  obtain ⟨_, _, rd1539₀⟩ := rd1538.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1539⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1539⟩
      (scratch_placeBidHighestBidWord σ I :: ⟨0⟩ :: value :: bidder :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidHighestBidWord] using rd1539₀⟩
  have hgt : UInt256.gt value (scratch_placeBidHighestBidWord σ I) = ⟨1⟩ := ugt_one hlt
  have rd1540₀ := evm_run rd1539 with [dup3, gt]
  have rd1540 := rd1540₀
  rw [hgt] at rd1540
  have rd1554 := evm_run rd1540 with [push2 ⟨1551⟩, jumpiT one_ne_zero_uint (by jump_dest),
    jumpdest, push1 ⟨5⟩]
  obtain ⟨_, _, rd1555₀⟩ := rd1554.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1555⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1555⟩
      (scratch_placeBidHighestBidderWord σ I :: ⟨0⟩ :: value :: bidder :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidHighestBidderWord] using rd1555₀⟩
  have rd1564₀ := evm_run rd1555 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and]
  have rd1564 := rd1564₀
  have hzero' :
      UInt256.land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)
        (scratch_placeBidHighestBidderWord σ I) = ⟨0⟩ := by
    change UInt256.land solcAddrMask (scratch_placeBidHighestBidderWord σ I) = ⟨0⟩
    rw [highestBidderU256_land_comm solcAddrMask (scratch_placeBidHighestBidderWord σ I)]
    exact hzero
  rw [hzero'] at rd1564
  have rd1619 := evm_run rd1564 with [
    iszero, push2 ⟨1618⟩, jumpiT one_ne_zero_uint (by jump_dest), jumpdest, pop,
    push1 ⟨6⟩, dup2, swap1]
  obtain ⟨_, _, rd1625₀⟩ := rd1619.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd1625⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1625⟩
      (value :: bidder :: ret :: R) mem aw rdata
      (cA, scratch_placeBidStoreHighMap σ I value) k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidStoreHighMap] using rd1625₀⟩
  have rd1628 := evm_run rd1625 with [push1 ⟨5⟩, dup1]
  obtain ⟨_, _, rd1629₀⟩ := rd1628.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1629⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1629⟩
      (scratch_placeBidHighestBidderWord (scratch_placeBidStoreHighMap σ I value) I ::
        ⟨5⟩ :: value :: bidder :: ret :: R)
      mem aw rdata (cA, scratch_placeBidStoreHighMap σ I value) k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidHighestBidderWord] using rd1629₀⟩
  have rd1649 := evm_run rd1629 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, and,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and]
  have rd1650 := RD.scratchOr rd1649 (by decide) (by evm_ov)
  have hpack :
      UInt256.lor
          (UInt256.land bidder (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩))
          (UInt256.land (UInt256.lnot (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩))
            (scratch_placeBidHighestBidderWord (scratch_placeBidStoreHighMap σ I value) I)
          ) =
        SimpleAuction.simpleAuctionSetAddressWord
          (scratch_placeBidHighestBidderWord (scratch_placeBidStoreHighMap σ I value) I)
          bidder :=
    by
      change UInt256.lor (UInt256.land bidder solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask)
            (scratch_placeBidHighestBidderWord (scratch_placeBidStoreHighMap σ I value) I)) =
        SimpleAuction.simpleAuctionSetAddressWord
          (scratch_placeBidHighestBidderWord (scratch_placeBidStoreHighMap σ I value) I)
          bidder
      exact scratch_placeBidPackedBidderWord_eq_setAddress
        (scratch_placeBidHighestBidderWord (scratch_placeBidStoreHighMap σ I value) I)
        bidder hbidderCanon
  have rd1650' := rd1650
  rw [hpack] at rd1650'
  have rd1651 := evm_run rd1650' with [swap1]
  obtain ⟨_, _, rd1652₀⟩ := rd1651.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd1652⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1652⟩
      (value :: bidder :: ret :: R) mem aw rdata
      (cA, scratch_placeBidStoreBidderMap
        (scratch_placeBidStoreHighMap σ I value) I bidder) k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidStoreBidderMap] using rd1652₀⟩
  have rd1655 := evm_run rd1652 with [push1 ⟨1⟩, jumpdest]
  exact ⟨_, _, evm_run rd1655 with [swap3, swap2, pop, pop, jump hret]⟩

noncomputable def scratch_placeBidPendingKeyMem (mem : ByteArray) (key : UInt256) : ByteArray :=
  (UInt256.toByteArray key).write 0 mem 0 32

noncomputable def scratch_placeBidPendingHashMem (mem : ByteArray) (key : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨7⟩ : UInt256)).write 0
    (scratch_placeBidPendingKeyMem mem key) 32 32

theorem scratch_placeBidPendingKeyMem_size (mem : ByteArray) (key : UInt256)
    (hmem : mem.size = 96) :
    (scratch_placeBidPendingKeyMem mem key).size = 96 := by
  unfold scratch_placeBidPendingKeyMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, hmem, toByteArray_size]
  norm_num

theorem scratch_placeBidPendingHashMem_size (mem : ByteArray) (key : UInt256)
    (hmem : mem.size = 96) :
    (scratch_placeBidPendingHashMem mem key).size = 96 := by
  unfold scratch_placeBidPendingHashMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [scratch_placeBidPendingKeyMem_size mem key hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    scratch_placeBidPendingKeyMem_size mem key hmem, toByteArray_size]
  norm_num

theorem scratch_placeBidPendingKeyMem_read0 (mem : ByteArray) (key : UInt256)
    (hmem : mem.size = 96) :
    (scratch_placeBidPendingKeyMem mem key).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  unfold scratch_placeBidPendingKeyMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega)]
  rw [show (UInt256.toByteArray key).extract 0 32 = UInt256.toByteArray key from by
    apply ByteArray.ext
    rw [ByteArray.data_extract, Array.extract_eq_self_of_le]
    show (UInt256.toByteArray key).data.size ≤ 32
    rw [show (UInt256.toByteArray key).data.size = (UInt256.toByteArray key).size from rfl,
      toByteArray_size]]

set_option maxHeartbeats 1000000 in
theorem scratch_placeBidPendingHashMem_read0_64 (mem : ByteArray) (key : UInt256)
    (hmem : mem.size = 96) :
    (scratch_placeBidPendingHashMem mem key).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray (⟨7⟩ : UInt256) := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [scratch_placeBidPendingHashMem_size mem key hmem]; norm_num)]
  unfold scratch_placeBidPendingHashMem
  rw [write32_eq _ _ 32 (by rw [toByteArray_size])
    (by rw [scratch_placeBidPendingKeyMem_size mem key hmem]; omega)]
  let M := scratch_placeBidPendingKeyMem mem key
  let S := UInt256.toByteArray (⟨7⟩ : UInt256)
  change (M.extract 0 32 ++ S.extract 0 32 ++ M.extract (32 + 32) M.size).extract
        0 (0 + 64) =
      UInt256.toByteArray key ++ S
  rw [show 0 + 64 = 64 by norm_num]
  rw [SimpleAuction.withdraw_extract_two_chunks_0]
  · have hM0 : M.extract 0 32 = UInt256.toByteArray key := by
      dsimp [M]
      rw [← readWithPadding_eq_extract (scratch_placeBidPendingKeyMem mem key) 0
        (by rw [scratch_placeBidPendingKeyMem_size mem key hmem]; omega)]
      exact scratch_placeBidPendingKeyMem_read0 mem key hmem
    have hSself : S.extract 0 32 = S := by
      dsimp [S]
      rw [show 32 = (UInt256.toByteArray (⟨7⟩ : UInt256)).size by rw [toByteArray_size]]
      exact SimpleAuction.withdrawByteArray_extract_self _
    rw [hM0, hSself]
  · rw [ByteArray.size_extract]
    dsimp [M]
    rw [scratch_placeBidPendingKeyMem_size mem key hmem]
    norm_num
  · rw [ByteArray.size_extract]
    dsimp [S]
    rw [toByteArray_size]
    norm_num

theorem scratch_placeBidPendingKeyMem_size_ge32 (mem : ByteArray) (key : UInt256) :
    32 ≤ (scratch_placeBidPendingKeyMem mem key).size := by
  unfold scratch_placeBidPendingKeyMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
  omega

theorem scratch_placeBidPendingHashMem_size_ge64 (mem : ByteArray) (key : UInt256) :
    64 ≤ (scratch_placeBidPendingHashMem mem key).size := by
  have hkeySize : 32 ≤ (scratch_placeBidPendingKeyMem mem key).size :=
    scratch_placeBidPendingKeyMem_size_ge32 mem key
  unfold scratch_placeBidPendingHashMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      hkeySize,
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
  omega

theorem scratch_placeBidPendingKeyMem_read0_any (mem : ByteArray) (key : UInt256) :
    (scratch_placeBidPendingKeyMem mem key).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  unfold scratch_placeBidPendingKeyMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray key).size ≤ 32
    rw [toByteArray_size])

theorem scratch_placeBidPendingHashMem_read0_any (mem : ByteArray) (key : UInt256) :
    (scratch_placeBidPendingHashMem mem key).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  unfold scratch_placeBidPendingHashMem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (scratch_placeBidPendingKeyMem_size_ge32 mem key) (by omega)]
  exact scratch_placeBidPendingKeyMem_read0_any mem key

theorem scratch_placeBidPendingHashMem_read32_any (mem : ByteArray) (key : UInt256) :
    (scratch_placeBidPendingHashMem mem key).readWithPadding 32 32 =
      UInt256.toByteArray (⟨7⟩ : UInt256) := by
  unfold scratch_placeBidPendingHashMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (scratch_placeBidPendingKeyMem_size_ge32 mem key)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray (⟨7⟩ : UInt256)).size ≤ 32
    rw [toByteArray_size])

theorem scratch_placeBidPendingHashMem_read0_64_any (mem : ByteArray) (key : UInt256) :
    (scratch_placeBidPendingHashMem mem key).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray (⟨7⟩ : UInt256) := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (scratch_placeBidPendingHashMem_size_ge64 mem key)]
  have hleft :
      (scratch_placeBidPendingHashMem mem key).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0 (by
        exact le_trans (by norm_num : 32 ≤ 64)
          (scratch_placeBidPendingHashMem_size_ge64 mem key)),
      scratch_placeBidPendingHashMem_read0_any]
  have hright :
      (scratch_placeBidPendingHashMem mem key).extract 32 64 =
        UInt256.toByteArray (⟨7⟩ : UInt256) := by
    rw [← readWithPadding_eq_extract _ 32 (scratch_placeBidPendingHashMem_size_ge64 mem key),
      scratch_placeBidPendingHashMem_read32_any]
  rw [show (scratch_placeBidPendingHashMem mem key).extract 0 64 =
      (scratch_placeBidPendingHashMem mem key).extract 0 32 ++
        (scratch_placeBidPendingHashMem mem key).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem scratch_placeBidPendingKeccak (mem : ByteArray) (key : UInt256)
    (hmem : mem.size = 96) (hcanon : key.toNat < EVM.addressModulus) :
    UInt256.ofNat
        (fromByteArrayBigEndian
          (ffi.KEC ((scratch_placeBidPendingHashMem mem key).readWithPadding 0 64))) =
      pendingReturnsSlot (.address (AccountAddress.ofNat key.toNat)) := by
  rw [scratch_placeBidPendingHashMem_read0_64 mem key hmem]
  unfold pendingReturnsSlot blindAuctionMappingSlot
  have hkey : keyValueToWord (.address (AccountAddress.ofNat key.toNat)) = key := by
    apply u256_inj
    unfold keyValueToWord AccountAddress.ofNat
    exact Nat.mod_eq_of_lt (by
      simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon)
  rw [hkey]
  exact mappingSlot_single key ⟨7⟩

theorem scratch_placeBidPendingKeccak_any (mem : ByteArray) (key : UInt256)
    (hcanon : key.toNat < EVM.addressModulus) :
    UInt256.ofNat
        (fromByteArrayBigEndian
          (ffi.KEC ((scratch_placeBidPendingHashMem mem key).readWithPadding 0 64))) =
      pendingReturnsSlot (.address (AccountAddress.ofNat key.toNat)) := by
  rw [scratch_placeBidPendingHashMem_read0_64_any mem key]
  unfold pendingReturnsSlot blindAuctionMappingSlot
  have hkey : keyValueToWord (.address (AccountAddress.ofNat key.toNat)) = key := by
    apply u256_inj
    unfold keyValueToWord AccountAddress.ofNat
    exact Nat.mod_eq_of_lt (by
      simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon)
  rw [hkey]
  exact mappingSlot_single key ⟨7⟩

def scratch_placeBidPendingSlot (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  pendingReturnsSlot
    (.address (AccountAddress.ofNat
      (UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask).toNat))

def scratch_placeBidPendingWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (scratch_placeBidPendingSlot σ I) ⟨0⟩)

def scratch_placeBidStorePendingMap (σ : AccountMap) (I : ExecutionEnv) (sum : UInt256) :
    AccountMap :=
  sstoreAccountMap I.codeOwner σ (scratch_placeBidPendingSlot σ I) sum

set_option maxHeartbeats 1000000 in
theorem scratch_RD_placeBid_true_nonzero {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {k C : Nat} {value bidder ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {rdata : ByteArray}
    (rd : RD blindAuctionBytecode I g s0 ⟨1534⟩ (value :: bidder :: ret :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hperm : I.perm = true)
    (hmem : mem.size = 96)
    (hlt : (scratch_placeBidHighestBidWord σ I).toNat < value.toNat)
    (hnonzero : UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask ≠ ⟨0⟩)
    (hbidderCanon : bidder.toNat < EVM.addressModulus)
    (hsum :
      (scratch_placeBidPendingWord σ I).toNat +
        (scratch_placeBidHighestBidWord σ I).toNat < UInt256.size)
    (hret : (D_J blindAuctionBytecode 0).contains ret = true)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ret (⟨1⟩ :: R)
      (scratch_placeBidPendingHashMem mem
        (UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask))
      (UInt256.ofNat 3) rdata
      (cA, scratch_placeBidStoreBidderMap
        (scratch_placeBidStoreHighMap
          (scratch_placeBidStorePendingMap σ I
            (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I)) I value) I
        bidder) k' C' := by
  have rd1538 := evm_run rd with [jumpdest, push0, push1 ⟨6⟩]
  obtain ⟨_, _, rd1539₀⟩ := rd1538.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1539⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1539⟩
      (scratch_placeBidHighestBidWord σ I :: ⟨0⟩ :: value :: bidder :: ret :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidHighestBidWord] using rd1539₀⟩
  have hgt : UInt256.gt value (scratch_placeBidHighestBidWord σ I) = ⟨1⟩ := ugt_one hlt
  have rd1540₀ := evm_run rd1539 with [dup3, gt]
  have rd1540 := rd1540₀
  rw [hgt] at rd1540
  have rd1554 := evm_run rd1540 with [push2 ⟨1551⟩, jumpiT one_ne_zero_uint (by jump_dest),
    jumpdest, push1 ⟨5⟩]
  obtain ⟨_, _, rd1555₀⟩ := rd1554.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1555⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1555⟩
      (scratch_placeBidHighestBidderWord σ I :: ⟨0⟩ :: value :: bidder :: ret :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidHighestBidderWord] using rd1555₀⟩
  have rd1564₀ := evm_run rd1555 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and]
  have hmaskNonzero :
      UInt256.land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)
        (scratch_placeBidHighestBidderWord σ I) ≠ ⟨0⟩ := by
    change UInt256.land solcAddrMask (scratch_placeBidHighestBidderWord σ I) ≠ ⟨0⟩
    rw [highestBidderU256_land_comm solcAddrMask (scratch_placeBidHighestBidderWord σ I)]
    exact hnonzero
  have rd1564 := rd1564₀
  have rd1565₀ := evm_run rd1564 with [iszero]
  have rd1565 := rd1565₀
  rw [isZero_eq_zero_of_ne hmaskNonzero] at rd1565
  have rd1571 := evm_run rd1565 with [push2 ⟨1618⟩, jumpiNT (by decide), push1 ⟨6⟩]
  obtain ⟨_, _, rd1572₀⟩ := rd1571.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1572⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1572⟩
      (scratch_placeBidHighestBidWord σ I :: ⟨0⟩ :: value :: bidder :: ret :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidHighestBidWord] using rd1572₀⟩
  have rd1574 := evm_run rd1572 with [push1 ⟨5⟩]
  obtain ⟨_, _, rd1575₀⟩ := rd1574.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1575⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1575⟩
      (scratch_placeBidHighestBidderWord σ I :: scratch_placeBidHighestBidWord σ I ::
        ⟨0⟩ :: value :: bidder :: ret :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidHighestBidderWord] using rd1575₀⟩
  have rd1587₀ := evm_run rd1575 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, push0, swap1, dup2]
  have hmask :
      UInt256.land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)
        (scratch_placeBidHighestBidderWord σ I) =
        UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask := by
    change UInt256.land solcAddrMask (scratch_placeBidHighestBidderWord σ I) =
      UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask
    exact highestBidderU256_land_comm solcAddrMask (scratch_placeBidHighestBidderWord σ I)
  have rd1587 := rd1587₀
  rw [hmask] at rd1587
  have rd1588 := evm_run rd1587 with [
    raw mstore 0
      (scratch_placeBidPendingKeyMem mem
        (UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask))
      (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd1593 := evm_run rd1588 with [
    push1 ⟨7⟩, push1 ⟨32⟩,
    raw mstore 0
      (scratch_placeBidPendingHashMem mem
        (UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask))
      (UInt256.ofNat 3) (by decide)
      mem_cost
      (by
        change (UInt256.toByteArray (⟨7⟩ : UInt256)).write 0
            (scratch_placeBidPendingKeyMem mem
              (UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask)) 32 32 =
          scratch_placeBidPendingHashMem mem
            (UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask)
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨64⟩, dup2]
  have hkeyCanon := highestBidderSolcAddrMask_result_canonical
    (scratch_placeBidHighestBidderWord σ I)
  have hslot := scratch_placeBidPendingKeccak mem
    (UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask) hmem hkeyCanon
  have rd1597 := evm_run rd1593 with [
    raw keccak256 0 (scratch_placeBidPendingSlot σ I) (UInt256.ofNat 3) (by decide)
      mem_cost (by simpa [scratch_placeBidPendingSlot] using hslot) (by decide) (by evm_ov),
    dup1]
  obtain ⟨_, _, rd1598₀⟩ := rd1597.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1599⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1599⟩
      (scratch_placeBidPendingWord σ I :: scratch_placeBidPendingSlot σ I ::
        ⟨0⟩ :: scratch_placeBidHighestBidWord σ I :: ⟨0⟩ :: value :: bidder :: ret :: R)
      (scratch_placeBidPendingHashMem mem
        (UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask))
      (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidPendingWord, scratch_placeBidPendingSlot] using rd1598₀⟩
  have rd1611 := evm_run rd1599 with [
    swap1, swap2, swap1, push2 ⟨1612⟩, swap1, dup5, swap1, push2 ⟨2045⟩,
    jump (by jump_dest)]
  obtain ⟨_, _, rd1612₀⟩ :=
    scratch_blindAuctionCheckedAddOk rd1611 hsum (by jump_dest) (by evm_ov)
  have rd1615 := evm_run rd1612₀ with [jumpdest, swap1, swap2]
  obtain ⟨_, _, rd1616₀⟩ := rd1615.sstore hperm (by decide) (by evm_ov)
  have rd1619 := evm_run rd1616₀ with [
    pop, pop, jumpdest, pop, push1 ⟨6⟩, dup2, swap1]
  obtain ⟨_, _, rd1625₀⟩ := rd1619.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd1625⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1625⟩
      (value :: bidder :: ret :: R)
      (scratch_placeBidPendingHashMem mem
        (UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask))
      (UInt256.ofNat 3) rdata
      (cA, scratch_placeBidStoreHighMap
        (scratch_placeBidStorePendingMap σ I
          (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I)) I value)
      k' C' := by
    exact ⟨_, _, by
      simpa [scratch_placeBidStoreHighMap, scratch_placeBidStorePendingMap] using rd1625₀⟩
  have rd1628 := evm_run rd1625 with [push1 ⟨5⟩, dup1]
  obtain ⟨_, _, rd1629₀⟩ := rd1628.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1629⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1629⟩
      (scratch_placeBidHighestBidderWord
          (scratch_placeBidStoreHighMap
            (scratch_placeBidStorePendingMap σ I
              (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I)) I value)
          I ::
        ⟨5⟩ :: value :: bidder :: ret :: R)
      (scratch_placeBidPendingHashMem mem
        (UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask))
      (UInt256.ofNat 3) rdata
      (cA, scratch_placeBidStoreHighMap
        (scratch_placeBidStorePendingMap σ I
          (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I)) I value)
      k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidHighestBidderWord] using rd1629₀⟩
  have rd1649 := evm_run rd1629 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, and,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and]
  have rd1650 := RD.scratchOr rd1649 (by decide) (by evm_ov)
  have hpack :
      UInt256.lor
          (UInt256.land bidder (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩))
          (UInt256.land (UInt256.lnot (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩))
            (scratch_placeBidHighestBidderWord
              (scratch_placeBidStoreHighMap
                (scratch_placeBidStorePendingMap σ I
                  (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I))
                I value)
              I)
          ) =
        SimpleAuction.simpleAuctionSetAddressWord
          (scratch_placeBidHighestBidderWord
            (scratch_placeBidStoreHighMap
              (scratch_placeBidStorePendingMap σ I
                (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I))
              I value)
            I)
          bidder :=
    by
      change UInt256.lor (UInt256.land bidder solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask)
            (scratch_placeBidHighestBidderWord
              (scratch_placeBidStoreHighMap
                (scratch_placeBidStorePendingMap σ I
                  (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I))
                I value)
              I)) =
        SimpleAuction.simpleAuctionSetAddressWord
          (scratch_placeBidHighestBidderWord
            (scratch_placeBidStoreHighMap
              (scratch_placeBidStorePendingMap σ I
                (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I))
              I value)
            I)
          bidder
      exact scratch_placeBidPackedBidderWord_eq_setAddress
        (scratch_placeBidHighestBidderWord
          (scratch_placeBidStoreHighMap
            (scratch_placeBidStorePendingMap σ I
              (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I)) I value)
          I)
        bidder hbidderCanon
  have rd1650' := rd1650
  rw [hpack] at rd1650'
  have rd1651 := evm_run rd1650' with [swap1]
  obtain ⟨_, _, rd1652₀⟩ := rd1651.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd1652⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1652⟩
      (value :: bidder :: ret :: R)
      (scratch_placeBidPendingHashMem mem
        (UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask))
      (UInt256.ofNat 3) rdata
      (cA, scratch_placeBidStoreBidderMap
        (scratch_placeBidStoreHighMap
          (scratch_placeBidStorePendingMap σ I
            (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I)) I value) I
        bidder)
      k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidStoreBidderMap] using rd1652₀⟩
  have rd1655 := evm_run rd1652 with [push1 ⟨1⟩, jumpdest]
  exact ⟨_, _, evm_run rd1655 with [swap3, swap2, pop, pop, jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem scratch_RD_placeBid_true_nonzero_anyMem {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {k C : Nat} {value bidder ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    (rd : RD blindAuctionBytecode I g s0 ⟨1534⟩ (value :: bidder :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hperm : I.perm = true)
    (hlt : (scratch_placeBidHighestBidWord σ I).toNat < value.toNat)
    (hnonzero : UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask ≠ ⟨0⟩)
    (hbidderCanon : bidder.toNat < EVM.addressModulus)
    (hsum :
      (scratch_placeBidPendingWord σ I).toNat +
        (scratch_placeBidHighestBidWord σ I).toNat < UInt256.size)
    (hret : (D_J blindAuctionBytecode 0).contains ret = true)
    (hov : R.length + 16 ≤ 1024) :
    ∃ aw' k' C', RD blindAuctionBytecode I g s0 ret (⟨1⟩ :: R)
      (scratch_placeBidPendingHashMem mem
        (UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask))
      aw' rdata
      (cA, scratch_placeBidStoreBidderMap
        (scratch_placeBidStoreHighMap
          (scratch_placeBidStorePendingMap σ I
            (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I)) I value) I
        bidder) k' C' := by
  let key := UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask
  let memKey := scratch_placeBidPendingKeyMem mem key
  let memHash := scratch_placeBidPendingHashMem mem key
  let aw1 := UInt256.ofNat (MachineState.M aw.toNat (⟨0⟩ : UInt256).toNat 32)
  let aw2 := UInt256.ofNat (MachineState.M aw1.toNat (⟨32⟩ : UInt256).toNat 32)
  let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨0⟩ : UInt256).toNat 64)
  have rd1538 := evm_run rd with [jumpdest, push0, push1 ⟨6⟩]
  obtain ⟨_, _, rd1539₀⟩ := rd1538.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1539⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1539⟩
      (scratch_placeBidHighestBidWord σ I :: ⟨0⟩ :: value :: bidder :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidHighestBidWord] using rd1539₀⟩
  have hgt : UInt256.gt value (scratch_placeBidHighestBidWord σ I) = ⟨1⟩ := ugt_one hlt
  have rd1540₀ := evm_run rd1539 with [dup3, gt]
  have rd1540 := rd1540₀
  rw [hgt] at rd1540
  have rd1554 := evm_run rd1540 with [push2 ⟨1551⟩, jumpiT one_ne_zero_uint (by jump_dest),
    jumpdest, push1 ⟨5⟩]
  obtain ⟨_, _, rd1555₀⟩ := rd1554.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1555⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1555⟩
      (scratch_placeBidHighestBidderWord σ I :: ⟨0⟩ :: value :: bidder :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidHighestBidderWord] using rd1555₀⟩
  have rd1564₀ := evm_run rd1555 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and]
  have hmaskNonzero :
      UInt256.land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)
        (scratch_placeBidHighestBidderWord σ I) ≠ ⟨0⟩ := by
    change UInt256.land solcAddrMask (scratch_placeBidHighestBidderWord σ I) ≠ ⟨0⟩
    rw [highestBidderU256_land_comm solcAddrMask (scratch_placeBidHighestBidderWord σ I)]
    exact hnonzero
  have rd1564 := rd1564₀
  have rd1565₀ := evm_run rd1564 with [iszero]
  have rd1565 := rd1565₀
  rw [isZero_eq_zero_of_ne hmaskNonzero] at rd1565
  have rd1571 := evm_run rd1565 with [push2 ⟨1618⟩, jumpiNT (by decide), push1 ⟨6⟩]
  obtain ⟨_, _, rd1572₀⟩ := rd1571.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1572⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1572⟩
      (scratch_placeBidHighestBidWord σ I :: ⟨0⟩ :: value :: bidder :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidHighestBidWord] using rd1572₀⟩
  have rd1574 := evm_run rd1572 with [push1 ⟨5⟩]
  obtain ⟨_, _, rd1575₀⟩ := rd1574.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1575⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1575⟩
      (scratch_placeBidHighestBidderWord σ I :: scratch_placeBidHighestBidWord σ I ::
        ⟨0⟩ :: value :: bidder :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidHighestBidderWord] using rd1575₀⟩
  have rd1587₀ := evm_run rd1575 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, push0, swap1, dup2]
  have hmask :
      UInt256.land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)
        (scratch_placeBidHighestBidderWord σ I) =
        UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask := by
    change UInt256.land solcAddrMask (scratch_placeBidHighestBidderWord σ I) =
      UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask
    exact highestBidderU256_land_comm solcAddrMask (scratch_placeBidHighestBidderWord σ I)
  have rd1587 := rd1587₀
  rw [hmask] at rd1587
  have rd1588 := evm_run rd1587 with [
    raw mstore (Cₘ aw1 - Cₘ aw) memKey aw1 (by decide)
      (fun s haws hstks => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, aw1])
      (by simp [memKey, scratch_placeBidPendingKeyMem, key])
      (by rfl) (by evm_ov)]
  have rd1593 := evm_run rd1588 with [
    push1 ⟨7⟩, push1 ⟨32⟩,
    raw mstore (Cₘ aw2 - Cₘ aw1) memHash aw2 (by decide)
      (fun s haws hstks => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, aw2])
      (by
        rw [show (⟨32⟩ : UInt256).toNat = 32 by native_decide]
        simp [memHash, scratch_placeBidPendingHashMem, memKey])
      (by rfl) (by evm_ov),
    push1 ⟨64⟩, dup2]
  have hkeyCanon := highestBidderSolcAddrMask_result_canonical
    (scratch_placeBidHighestBidderWord σ I)
  have hslot := scratch_placeBidPendingKeccak_any mem key hkeyCanon
  have rd1597 := evm_run rd1593 with [
    raw keccak256 (Cₘ aw3 - Cₘ aw2) (scratch_placeBidPendingSlot σ I) aw3 (by decide)
      (fun s haws hstks => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, aw3,
          show (⟨64⟩ : UInt256).toNat = 64 by native_decide])
      (by simpa [memHash, key, scratch_placeBidPendingSlot] using hslot) (by rfl) (by evm_ov),
    dup1]
  obtain ⟨_, _, rd1598₀⟩ := rd1597.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1599⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1599⟩
      (scratch_placeBidPendingWord σ I :: scratch_placeBidPendingSlot σ I ::
        ⟨0⟩ :: scratch_placeBidHighestBidWord σ I :: ⟨0⟩ :: value :: bidder :: ret :: R)
      memHash aw3 rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidPendingWord, scratch_placeBidPendingSlot,
      memHash] using rd1598₀⟩
  have rd1611 := evm_run rd1599 with [
    swap1, swap2, swap1, push2 ⟨1612⟩, swap1, dup5, swap1, push2 ⟨2045⟩,
    jump (by jump_dest)]
  obtain ⟨_, _, rd1612₀⟩ :=
    scratch_blindAuctionCheckedAddOk rd1611 hsum (by jump_dest) (by evm_ov)
  have rd1615 := evm_run rd1612₀ with [jumpdest, swap1, swap2]
  obtain ⟨_, _, rd1616₀⟩ := rd1615.sstore hperm (by decide) (by evm_ov)
  have rd1619 := evm_run rd1616₀ with [
    pop, pop, jumpdest, pop, push1 ⟨6⟩, dup2, swap1]
  obtain ⟨_, _, rd1625₀⟩ := rd1619.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd1625⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1625⟩
      (value :: bidder :: ret :: R)
      memHash aw3 rdata
      (cA, scratch_placeBidStoreHighMap
        (scratch_placeBidStorePendingMap σ I
          (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I)) I value)
      k' C' := by
    exact ⟨_, _, by
      simpa [scratch_placeBidStoreHighMap, scratch_placeBidStorePendingMap, memHash] using
        rd1625₀⟩
  have rd1628 := evm_run rd1625 with [push1 ⟨5⟩, dup1]
  obtain ⟨_, _, rd1629₀⟩ := rd1628.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1629⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1629⟩
      (scratch_placeBidHighestBidderWord
          (scratch_placeBidStoreHighMap
            (scratch_placeBidStorePendingMap σ I
              (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I)) I value)
          I ::
        ⟨5⟩ :: value :: bidder :: ret :: R)
      memHash aw3 rdata
      (cA, scratch_placeBidStoreHighMap
        (scratch_placeBidStorePendingMap σ I
          (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I)) I value)
      k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidHighestBidderWord, memHash] using rd1629₀⟩
  have rd1649 := evm_run rd1629 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, and,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and]
  have rd1650 := RD.scratchOr rd1649 (by decide) (by evm_ov)
  have hpack :
      UInt256.lor
          (UInt256.land bidder (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩))
          (UInt256.land (UInt256.lnot (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩))
            (scratch_placeBidHighestBidderWord
              (scratch_placeBidStoreHighMap
                (scratch_placeBidStorePendingMap σ I
                  (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I))
                I value)
              I)
          ) =
        SimpleAuction.simpleAuctionSetAddressWord
          (scratch_placeBidHighestBidderWord
            (scratch_placeBidStoreHighMap
              (scratch_placeBidStorePendingMap σ I
                (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I))
              I value)
            I)
          bidder :=
    by
      change UInt256.lor (UInt256.land bidder solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask)
            (scratch_placeBidHighestBidderWord
              (scratch_placeBidStoreHighMap
                (scratch_placeBidStorePendingMap σ I
                  (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I))
                I value)
              I)) =
        SimpleAuction.simpleAuctionSetAddressWord
          (scratch_placeBidHighestBidderWord
            (scratch_placeBidStoreHighMap
              (scratch_placeBidStorePendingMap σ I
                (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I))
              I value)
            I)
          bidder
      exact scratch_placeBidPackedBidderWord_eq_setAddress
        (scratch_placeBidHighestBidderWord
          (scratch_placeBidStoreHighMap
            (scratch_placeBidStorePendingMap σ I
              (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I)) I value)
          I)
        bidder hbidderCanon
  have rd1650' := rd1650
  rw [hpack] at rd1650'
  have rd1651 := evm_run rd1650' with [swap1]
  obtain ⟨_, _, rd1652₀⟩ := rd1651.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd1652⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1652⟩
      (value :: bidder :: ret :: R)
      memHash aw3 rdata
      (cA, scratch_placeBidStoreBidderMap
        (scratch_placeBidStoreHighMap
          (scratch_placeBidStorePendingMap σ I
            (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I)) I value) I
        bidder)
      k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidStoreBidderMap, memHash] using rd1652₀⟩
  have rd1655 := evm_run rd1652 with [push1 ⟨1⟩, jumpdest]
  exact ⟨aw3, _, _, by simpa [memHash] using
    (evm_run rd1655 with [swap3, swap2, pop, pop, jump hret])⟩

theorem scratch_revealSourceWord_canonical (I : ExecutionEnv) :
    (UInt256.ofNat I.source.val).toNat < EVM.addressModulus := by
  rw [ulit_toNat' _ (lt_of_lt_of_le I.source.isLt
    (show AccountAddress.size ≤ UInt256.size from by decide))]
  simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using I.source.isLt

theorem scratch_blindAuctionRevealX_placeCond_placeBid_false_toNext {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {secret value slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen
      fakesEnd valuesLen valuesEnd sel deposit : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1265⟩
      [secret, ⟨0⟩, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hdeposit :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (slot + ⟨1⟩) ⟨0⟩) = deposit)
    (hdepositGe : value.toNat ≤ deposit.toNat)
    (hplaceFalse : value.toNat ≤ (scratch_placeBidHighestBidWord σ I).toNat)
    (hperm : I.perm = true) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1014⟩
      (scratch_revealEvmLoopStack (i + ⟨1⟩) refund len revealEnd biddingEnd secretsLen
        secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
      mem aw rdata (cA, sstoreAccountMap I.codeOwner σ slot ⟨0⟩) k' C' := by
  obtain ⟨_, _, rd1534⟩ :=
    scratch_blindAuctionRevealX_placeCond_place_toRoutine rd hdeposit hdepositGe
  obtain ⟨_, _, rd1297⟩ :=
    scratch_RD_placeBid_false
      (value := value) (bidder := UInt256.ofNat I.source.val) (ret := ⟨1297⟩)
      (R := [secret, ⟨0⟩, value, slot, i, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel])
      rd1534 hplaceFalse (by jump_dest) (by simp)
  exact scratch_blindAuctionRevealX_placeBidFalse_toNext rd1297 hperm

theorem scratch_blindAuctionRevealX_placeCond_placeBid_true_zero_toNext {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {secret value slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen
      fakesEnd valuesLen valuesEnd sel deposit : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1265⟩
      [secret, ⟨0⟩, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hdeposit :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (slot + ⟨1⟩) ⟨0⟩) = deposit)
    (hdepositGe : value.toNat ≤ deposit.toNat)
    (hplaceTrue : (scratch_placeBidHighestBidWord σ I).toNat < value.toNat)
    (hhighestBidderZero :
      UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask = ⟨0⟩)
    (hrefund : value.toNat ≤ refund.toNat)
    (hperm : I.perm = true) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1014⟩
      (scratch_revealEvmLoopStack (i + ⟨1⟩) (UInt256.sub refund value) len revealEnd
        biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
      mem aw rdata
      (cA, sstoreAccountMap I.codeOwner
        (scratch_placeBidStoreBidderMap (scratch_placeBidStoreHighMap σ I value) I
          (UInt256.ofNat I.source.val)) slot ⟨0⟩) k' C' := by
  obtain ⟨_, _, rd1534⟩ :=
    scratch_blindAuctionRevealX_placeCond_place_toRoutine rd hdeposit hdepositGe
  obtain ⟨_, _, rd1297⟩ :=
    scratch_RD_placeBid_true_zero
      (value := value) (bidder := UInt256.ofNat I.source.val) (ret := ⟨1297⟩)
      (R := [secret, ⟨0⟩, value, slot, i, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel])
      rd1534 hperm hplaceTrue hhighestBidderZero (scratch_revealSourceWord_canonical I)
      (by jump_dest) (by simp)
  exact scratch_blindAuctionRevealX_placeBidTrue_toNext rd1297 hrefund hperm

theorem scratch_blindAuctionRevealX_placeCond_placeBid_true_nonzero_toNext {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {secret value slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen
      fakesEnd valuesLen valuesEnd sel deposit : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1265⟩
      [secret, ⟨0⟩, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hdeposit :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (slot + ⟨1⟩) ⟨0⟩) = deposit)
    (hdepositGe : value.toNat ≤ deposit.toNat)
    (hplaceTrue : (scratch_placeBidHighestBidWord σ I).toNat < value.toNat)
    (hhighestBidderNonzero :
      UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask ≠ ⟨0⟩)
    (hsum :
      (scratch_placeBidPendingWord σ I).toNat +
        (scratch_placeBidHighestBidWord σ I).toNat < UInt256.size)
    (hrefund : value.toNat ≤ refund.toNat)
    (hperm : I.perm = true) :
    ∃ aw' k' C', RD blindAuctionBytecode I g s0 ⟨1014⟩
      (scratch_revealEvmLoopStack (i + ⟨1⟩) (UInt256.sub refund value) len revealEnd
        biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
      (scratch_placeBidPendingHashMem mem
        (UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask))
      aw' rdata
      (cA, sstoreAccountMap I.codeOwner
        (scratch_placeBidStoreBidderMap
          (scratch_placeBidStoreHighMap
            (scratch_placeBidStorePendingMap σ I
              (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I)) I value)
          I (UInt256.ofNat I.source.val)) slot ⟨0⟩) k' C' := by
  obtain ⟨_, _, rd1534⟩ :=
    scratch_blindAuctionRevealX_placeCond_place_toRoutine rd hdeposit hdepositGe
  obtain ⟨aw', _, _, rd1297⟩ :=
    scratch_RD_placeBid_true_nonzero_anyMem
      (value := value) (bidder := UInt256.ofNat I.source.val) (ret := ⟨1297⟩)
      (R := [secret, ⟨0⟩, value, slot, i, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel])
      rd1534 hperm hplaceTrue hhighestBidderNonzero (scratch_revealSourceWord_canonical I)
      hsum (by jump_dest) (by simp)
  obtain ⟨k', C', rd1014⟩ := scratch_blindAuctionRevealX_placeBidTrue_toNext rd1297 hrefund hperm
  exact ⟨aw', k', C', rd1014⟩

/-! ### Scratch reveal nonempty loop source-side scaffolding -/

def scratch_revealLengthStore (callargs : Store) (len : UInt256) : Store :=
  callargs.insert "length" (.int (Int.ofNat len.toNat))

def scratch_revealRefundStore (callargs : Store) (len refund : UInt256) : Store :=
  (scratch_revealLengthStore callargs len).insert "refund" (.int (Int.ofNat refund.toNat))

def scratch_revealLoopStore (callargs : Store) (len refund i : UInt256) : Store :=
  (scratch_revealRefundStore callargs len refund).insert "i" (.int (Int.ofNat i.toNat))

def scratch_revealCallStore (callargs : Store) (len refund i : UInt256)
    (success : Bool) (out : ByteArray) : Store :=
  (scratch_revealLoopStore callargs len refund i).insert "success" (.bool success)
    |>.insert "_data" (.bytes out)

def scratch_revealCallStoreOf (locals : Store) (success : Bool) (out : ByteArray) : Store :=
  locals.insert "success" (.bool success) |>.insert "_data" (.bytes out)

theorem scratch_revealCallStore_success_get (callargs : Store) (len refund i : UInt256)
    (success : Bool) (out : ByteArray) :
    (scratch_revealCallStore callargs len refund i success out).get? "success" =
      some (.bool success) := by
  unfold scratch_revealCallStore
  rw [store_get_ne]
  · exact store_get_self _ _ _
  · decide

theorem scratch_evalExpr_reveal_success (evm : EVM.State) (callargs : Store)
    (len refund i : UInt256) (success : Bool) (out : ByteArray) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract,
        locals := scratch_revealCallStore callargs len refund i success out } evm
      (.var "success") = .ok (.bool success) := by
  rw [evalExpr?]
  change EvalResult.ofOption .unboundVariable
    ((scratch_revealCallStore callargs len refund i success out).get? "success") =
      .ok (.bool success)
  rw [scratch_revealCallStore_success_get]
  rfl

theorem scratch_revealCallStoreOf_success_get (locals : Store) (success : Bool)
    (out : ByteArray) :
    (scratch_revealCallStoreOf locals success out).get? "success" =
      some (.bool success) := by
  unfold scratch_revealCallStoreOf
  rw [store_get_ne]
  · exact store_get_self _ _ _
  · decide

theorem scratch_evalExpr_reveal_success_of (evm : EVM.State) (locals : Store)
    (success : Bool) (out : ByteArray) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract,
        locals := scratch_revealCallStoreOf locals success out } evm
      (.var "success") = .ok (.bool success) := by
  rw [evalExpr?]
  change EvalResult.ofOption .unboundVariable
    ((scratch_revealCallStoreOf locals success out).get? "success") =
      .ok (.bool success)
  rw [scratch_revealCallStoreOf_success_get]
  rfl

def scratch_revealLoopPostStmts : List Stmt :=
  [ .assign .localVar { base := "i" } (.binary .add (.var "i") (.intLit 1)) ]

def scratch_revealLoopBodyStmts : List Stmt :=
  [ .letStorage "bidToCheck" (bidElemRef sender (.var "i")),
    .letDecl "value" (some uint256) (.index (.var "values") (.var "i")),
    .letDecl "fake" (some boolTy) (.index (.var "fakes") (.var "i")),
    .letDecl "secret" (some bytes32) (.index (.var "secrets") (.var "i")),
    .ite
      (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
        (.keccak256 (.abiEncodePacked
          [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
      [.continue] [],
    .assign .localVar { base := "refund" }
      (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
    .ite
      (.binary .and (.unary .not (.var "fake"))
        (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
      [ .internalCall "placeBid" [sender, .var "value"] "ok",
        .ite (.var "ok")
          [ .assign .localVar { base := "refund" }
              (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
    .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]

def scratch_revealForStmt : Stmt :=
  .for [ .letDecl "i" (some uint256) (.intLit 0) ]
    (.binary .lt (.var "i") (.var "length"))
    scratch_revealLoopPostStmts
    scratch_revealLoopBodyStmts

theorem scratch_revealLoopStore_length_get (callargs : Store) (len refund i : UInt256) :
    (scratch_revealLoopStore callargs len refund i).get? "length" =
      some (.int (Int.ofNat len.toNat)) := by
  unfold scratch_revealLoopStore scratch_revealRefundStore scratch_revealLengthStore
  rw [store_get_ne, store_get_ne, store_get_self]
  · decide
  · decide

theorem scratch_revealLoopStore_refund_get (callargs : Store) (len refund i : UInt256) :
    (scratch_revealLoopStore callargs len refund i).get? "refund" =
      some (.int (Int.ofNat refund.toNat)) := by
  unfold scratch_revealLoopStore scratch_revealRefundStore
  rw [store_get_ne, store_get_self]
  decide

theorem scratch_revealLoopStore_i_get (callargs : Store) (len refund i : UInt256) :
    (scratch_revealLoopStore callargs len refund i).get? "i" =
      some (.int (Int.ofNat i.toNat)) := by
  unfold scratch_revealLoopStore
  rw [store_get_self]

theorem scratch_revealLoopStore_values_get {callargs : Store} {values : List Value}
    {len refund i : UInt256}
    (hvalues : callargs.get? "values" = some (.array values)) :
    (scratch_revealLoopStore callargs len refund i).get? "values" = some (.array values) := by
  unfold scratch_revealLoopStore scratch_revealRefundStore scratch_revealLengthStore
  rw [store_get_ne, store_get_ne, store_get_ne]
  · exact hvalues
  · decide
  · decide
  · decide

theorem scratch_revealLoopStore_fakes_get {callargs : Store} {fakes : List Value}
    {len refund i : UInt256}
    (hfakes : callargs.get? "fakes" = some (.array fakes)) :
    (scratch_revealLoopStore callargs len refund i).get? "fakes" = some (.array fakes) := by
  unfold scratch_revealLoopStore scratch_revealRefundStore scratch_revealLengthStore
  rw [store_get_ne, store_get_ne, store_get_ne]
  · exact hfakes
  · decide
  · decide
  · decide

theorem scratch_revealLoopStore_secrets_get {callargs : Store} {secrets : List Value}
    {len refund i : UInt256}
    (hsecrets : callargs.get? "secrets" = some (.array secrets)) :
    (scratch_revealLoopStore callargs len refund i).get? "secrets" = some (.array secrets) := by
  unfold scratch_revealLoopStore scratch_revealRefundStore scratch_revealLengthStore
  rw [store_get_ne, store_get_ne, store_get_ne]
  · exact hsecrets
  · decide
  · decide
  · decide

theorem scratch_revealLoopStore_bids_none {callargs : Store} {len refund i : UInt256}
    (hbids : callargs.get? "bids" = none) :
    (scratch_revealLoopStore callargs len refund i).get? "bids" = none := by
  unfold scratch_revealLoopStore scratch_revealRefundStore scratch_revealLengthStore
  rw [store_get_ne, store_get_ne, store_get_ne]
  · exact hbids
  · decide
  · decide
  · decide

theorem scratch_evalExpr_reveal_loop_cond_true (evm : EVM.State) (callargs : Store)
    (len refund i : UInt256) (hbound : i.toNat < len.toNat) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_revealLoopStore callargs len refund i }
      evm (.binary .lt (.var "i") (.var "length")) = .ok (.bool true) := by
  rw [evalExpr?]
  simp only [
    evalExpr_reveal_var_int evm (scratch_revealLoopStore callargs len refund i) "i"
      (Int.ofNat i.toNat) (scratch_revealLoopStore_i_get callargs len refund i),
    evalExpr_reveal_var_int evm (scratch_revealLoopStore callargs len refund i) "length"
      (Int.ofNat len.toNat) (scratch_revealLoopStore_length_get callargs len refund i),
    EvalResult.bind, bind]
  simp [evalBinaryOp?]
  exact hbound

theorem scratch_evalExpr_reveal_loop_cond_false (evm : EVM.State) (callargs : Store)
    (len refund i : UInt256) (hbound : len.toNat ≤ i.toNat) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_revealLoopStore callargs len refund i }
      evm (.binary .lt (.var "i") (.var "length")) = .ok (.bool false) := by
  rw [evalExpr?]
  simp only [
    evalExpr_reveal_var_int evm (scratch_revealLoopStore callargs len refund i) "i"
      (Int.ofNat i.toNat) (scratch_revealLoopStore_i_get callargs len refund i),
    evalExpr_reveal_var_int evm (scratch_revealLoopStore callargs len refund i) "length"
      (Int.ofNat len.toNat) (scratch_revealLoopStore_length_get callargs len refund i),
    EvalResult.bind, bind]
  simp [evalBinaryOp?]
  exact hbound

theorem scratch_evalExpr_reveal_loop_cond_true_of_get (evm : EVM.State) (locals : Store)
    (len i : UInt256)
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hlen : locals.get? "length" = some (.int (Int.ofNat len.toNat)))
    (hbound : i.toNat < len.toNat) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .lt (.var "i") (.var "length")) = .ok (.bool true) := by
  rw [evalExpr?]
  simp only [
    evalExpr_reveal_var_int evm locals "i" (Int.ofNat i.toNat) hi,
    evalExpr_reveal_var_int evm locals "length" (Int.ofNat len.toNat) hlen,
    EvalResult.bind, bind]
  simp [evalBinaryOp?]
  exact hbound

theorem scratch_evalExpr_reveal_loop_cond_false_of_get (evm : EVM.State) (locals : Store)
    (len i : UInt256)
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hlen : locals.get? "length" = some (.int (Int.ofNat len.toNat)))
    (hbound : len.toNat ≤ i.toNat) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .lt (.var "i") (.var "length")) = .ok (.bool false) := by
  rw [evalExpr?]
  simp only [
    evalExpr_reveal_var_int evm locals "i" (Int.ofNat i.toNat) hi,
    evalExpr_reveal_var_int evm locals "length" (Int.ofNat len.toNat) hlen,
    EvalResult.bind, bind]
  simp [evalBinaryOp?]
  exact hbound

theorem scratch_evalExpr_reveal_local_array_index_norm (evm : EVM.State) (locals : Store)
    (name : Ident) (xs : List Value) (idx : UInt256) (rawv v : Value)
    (harr : locals.get? name = some (.array xs))
    (hi : locals.get? "i" = some (.int (Int.ofNat idx.toNat)))
    (hbound : idx.toNat < xs.length)
    (hlookup : lookupNth? xs idx.toNat = some rawv)
    (hnorm : normalizeRawBoolWord? rawv = .ok v) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.index (.var name) (.var "i")) = .ok v := by
  rw [evalExpr?]
  simp only [evalExpr_reveal_var_value evm locals name (.array xs) harr,
    evalExpr_reveal_var_value evm locals "i" (.int (Int.ofNat idx.toNat)) hi,
    EvalResult.bind, bind]
  unfold evalIndex?
  simp only
  rw [if_pos]
  · simp [hlookup, hnorm]
  · constructor
    · exact Int.natCast_nonneg idx.toNat
    · simpa using hbound

theorem scratch_evalExpr_reveal_local_array_index_revert (evm : EVM.State) (locals : Store)
    (name : Ident) (xs : List Value) (idx : UInt256) (rawv : Value)
    (harr : locals.get? name = some (.array xs))
    (hi : locals.get? "i" = some (.int (Int.ofNat idx.toNat)))
    (hbound : idx.toNat < xs.length)
    (hlookup : lookupNth? xs idx.toNat = some rawv)
    (hnorm : normalizeRawBoolWord? rawv = .revert) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.index (.var name) (.var "i")) = .revert := by
  rw [evalExpr?]
  simp only [evalExpr_reveal_var_value evm locals name (.array xs) harr,
    evalExpr_reveal_var_value evm locals "i" (.int (Int.ofNat idx.toNat)) hi,
    EvalResult.bind, bind]
  unfold evalIndex?
  simp only
  rw [if_pos]
  · simp [hlookup, hnorm]
  · constructor
    · exact Int.natCast_nonneg idx.toNat
    · simpa using hbound

def scratch_revealBidEvaledRef (evm : EVM.State) (i : UInt256) : EvaledStorageRef :=
  { base := "bids",
    steps := [.mindex (.address evm.executionEnv.source),
      .aindex (.int (Int.ofNat i.toNat))] }

def scratch_revealBidToCheckStore (callargs : Store) (evm : EVM.State)
    (len refund i : UInt256) : Store :=
  (scratch_revealLoopStore callargs len refund i).insert "bidToCheck"
    (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy)

def scratch_revealValueStore (callargs : Store) (evm : EVM.State)
    (len refund i value : UInt256) : Store :=
  (scratch_revealBidToCheckStore callargs evm len refund i).insert "value"
    (.int (Int.ofNat value.toNat))

def scratch_revealFakeStore (callargs : Store) (evm : EVM.State)
    (len refund i value : UInt256) (fake : Bool) : Store :=
  (scratch_revealValueStore callargs evm len refund i value).insert "fake" (.bool fake)

def scratch_revealSecretStore (callargs : Store) (evm : EVM.State)
    (len refund i value secret : UInt256) (fake : Bool) : Store :=
  (scratch_revealFakeStore callargs evm len refund i value fake).insert "secret"
    (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret))

def scratch_revealRefundAddedStore (callargs : Store) (evm : EVM.State)
    (len refund i value secret deposit : UInt256) (fake : Bool) : Store :=
  (scratch_revealSecretStore callargs evm len refund i value secret fake).insert "refund"
    (.int (Int.ofNat (refund.toNat + deposit.toNat)))

def scratch_revealRefundPlacedStore (callargs : Store) (evm : EVM.State)
    (len refund i value secret deposit : UInt256) : Store :=
  ((scratch_revealRefundAddedStore callargs evm len refund i value secret deposit false).insert
      "ok" (.bool true)).insert "refund"
    (.int (Int.ofNat (refund.toNat + deposit.toNat - value.toNat)))

def scratch_revealBidFieldRef (evm : EVM.State) (i : UInt256) (field : Ident) :
    EvaledStorageRef :=
  { scratch_revealBidEvaledRef evm i with
    steps := (scratch_revealBidEvaledRef evm i).steps ++ [.field field] }

def scratch_revealBidBlindedSlot (evm : EVM.State) (i : UInt256) : UInt256 :=
  bidsElemSlot (.address evm.executionEnv.source) (.int (Int.ofNat i.toNat))

def scratch_revealBidDepositSlot (evm : EVM.State) (i : UInt256) : UInt256 :=
  scratch_revealBidBlindedSlot evm i + ⟨1⟩

theorem scratch_revealBid_arrayIndexInBounds_ok (evm : EVM.State) (i len : UInt256)
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hbound : i.toNat < len.toNat) :
    arrayIndexInBounds? blindAuctionConfig evm blindAuctionContract.storage "bids"
      [.mindex (.address evm.executionEnv.source)] (.int (Int.ofNat i.toNat)) = .ok () := by
  simp [arrayIndexInBounds?, storageTypeAt?, storageTypeStep?, blindAuctionConfig,
    blindAuctionStorageLayout, blindAuctionContract, storageDecls, bidStructTy, uint256St,
    bytes32St, blindAuctionStorageLocLoad_uint256, hlen, hbound]

theorem scratch_evalStorageRef_reveal_bid_ok (evm : EVM.State) (callargs : Store)
    (len refund i : UInt256)
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hbound : i.toNat < len.toNat) :
    evalStorageRef blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_revealLoopStore callargs len refund i }
      evm (bidElemRef sender (.var "i")) =
        .ok (scratch_revealBidEvaledRef evm i) := by
  have hbounds := scratch_revealBid_arrayIndexInBounds_ok evm i len hlen hbound
  simp only [bidElemRef, sender, evalStorageRef, evalStorageRefSteps.eq_def,
    evalStorageRefStep.eq_def, evalExpr?, envValue, valueToKey?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, List.nil_append, scratch_revealBidEvaledRef,
    scratch_revealLoopStore_i_get]
  rw [hbounds]

theorem scratch_revealBid_storageType (evm : EVM.State) (i : UInt256) :
    storageTypeAt? blindAuctionContract.storage (scratch_revealBidEvaledRef evm i) =
      some bidStructTy := by
  simp [scratch_revealBidEvaledRef, storageTypeAt?, storageTypeStep?, blindAuctionContract,
    storageDecls, bidStructTy]

theorem scratch_resolveStorageRef_reveal_bid_ok (evm : EVM.State) (callargs : Store)
    (len refund i : UInt256)
    (hbids : callargs.get? "bids" = none)
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hbound : i.toNat < len.toNat) :
    resolveStorageRef? blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_revealLoopStore callargs len refund i }
      evm (bidElemRef sender (.var "i")) =
        .ok (scratch_revealBidEvaledRef evm i, bidStructTy) := by
  exact resolveStorageRef?_ok
    (scratch_revealLoopStore_bids_none (len := len) (refund := refund) (i := i) hbids)
    (scratch_evalStorageRef_reveal_bid_ok evm callargs len refund i hlen hbound)
    (scratch_revealBid_storageType evm i)

theorem scratch_letStorage_reveal_bidToCheck (evm : EVM.State) (callargs : Store)
    (len refund i : UInt256)
    (hbids : callargs.get? "bids" = none)
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hbound : i.toNat < len.toNat) :
    ExecStmt blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_revealLoopStore callargs len refund i }
      evm (.letStorage "bidToCheck" (bidElemRef sender (.var "i")))
      (.ok
        { contract := blindAuctionContract,
          locals := (scratch_revealLoopStore callargs len refund i).insert "bidToCheck"
            (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) }
        evm) := by
  exact ExecStmt.letStorage
    (scratch_resolveStorageRef_reveal_bid_ok evm callargs len refund i hbids hlen hbound)

theorem scratch_revealBidToCheckStore_bid_get (callargs : Store) (evm : EVM.State)
    (len refund i : UInt256) :
    (scratch_revealBidToCheckStore callargs evm len refund i).get? "bidToCheck" =
      some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
  unfold scratch_revealBidToCheckStore
  rw [store_get_self]

theorem scratch_revealSecretStore_bid_get (callargs : Store) (evm : EVM.State)
    (len refund i value secret : UInt256) (fake : Bool) :
    (scratch_revealSecretStore callargs evm len refund i value secret fake).get? "bidToCheck" =
      some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
  unfold scratch_revealSecretStore scratch_revealFakeStore scratch_revealValueStore
  rw [store_get_ne, store_get_ne, store_get_ne]
  · exact scratch_revealBidToCheckStore_bid_get callargs evm len refund i
  · decide
  · decide
  · decide

theorem scratch_revealSecretStore_value_get (callargs : Store) (evm : EVM.State)
    (len refund i value secret : UInt256) (fake : Bool) :
    (scratch_revealSecretStore callargs evm len refund i value secret fake).get? "value" =
      some (.int (Int.ofNat value.toNat)) := by
  unfold scratch_revealSecretStore scratch_revealFakeStore scratch_revealValueStore
  rw [store_get_ne, store_get_ne, store_get_self]
  · decide
  · decide

theorem scratch_revealSecretStore_fake_get (callargs : Store) (evm : EVM.State)
    (len refund i value secret : UInt256) (fake : Bool) :
    (scratch_revealSecretStore callargs evm len refund i value secret fake).get? "fake" =
      some (.bool fake) := by
  unfold scratch_revealSecretStore scratch_revealFakeStore
  rw [store_get_ne, store_get_self]
  decide

theorem scratch_revealSecretStore_refund_get (callargs : Store) (evm : EVM.State)
    (len refund i value secret : UInt256) (fake : Bool) :
    (scratch_revealSecretStore callargs evm len refund i value secret fake).get? "refund" =
      some (.int (Int.ofNat refund.toNat)) := by
  unfold scratch_revealSecretStore scratch_revealFakeStore scratch_revealValueStore
  rw [store_get_ne, store_get_ne, store_get_ne]
  · unfold scratch_revealBidToCheckStore
    rw [store_get_ne]
    · exact scratch_revealLoopStore_refund_get callargs len refund i
    · decide
  · decide
  · decide
  · decide

theorem scratch_revealRefundAddedStore_bid_get (callargs : Store) (evm : EVM.State)
    (len refund i value secret deposit : UInt256) (fake : Bool) :
    (scratch_revealRefundAddedStore callargs evm len refund i value secret deposit fake).get?
      "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
  unfold scratch_revealRefundAddedStore
  rw [store_get_ne]
  · exact scratch_revealSecretStore_bid_get callargs evm len refund i value secret fake
  · decide

theorem scratch_revealRefundAddedStore_value_get (callargs : Store) (evm : EVM.State)
    (len refund i value secret deposit : UInt256) (fake : Bool) :
    (scratch_revealRefundAddedStore callargs evm len refund i value secret deposit fake).get?
      "value" = some (.int (Int.ofNat value.toNat)) := by
  unfold scratch_revealRefundAddedStore
  rw [store_get_ne]
  · exact scratch_revealSecretStore_value_get callargs evm len refund i value secret fake
  · decide

theorem scratch_revealRefundAddedStore_fake_get (callargs : Store) (evm : EVM.State)
    (len refund i value secret deposit : UInt256) (fake : Bool) :
    (scratch_revealRefundAddedStore callargs evm len refund i value secret deposit fake).get?
      "fake" = some (.bool fake) := by
  unfold scratch_revealRefundAddedStore
  rw [store_get_ne]
  · exact scratch_revealSecretStore_fake_get callargs evm len refund i value secret fake
  · decide

theorem scratch_revealRefundAddedStore_refund_get (callargs : Store) (evm : EVM.State)
    (len refund i value secret deposit : UInt256) (fake : Bool) :
    (scratch_revealRefundAddedStore callargs evm len refund i value secret deposit fake).get?
      "refund" = some (.int (Int.ofNat (refund.toNat + deposit.toNat))) := by
  unfold scratch_revealRefundAddedStore
  rw [store_get_self]

theorem scratch_resolveStorageRef_reveal_bid_blinded_ok (evm : EVM.State)
    (locals : Store) (i : UInt256)
    (hbid :
      locals.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy)) :
    resolveStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := locals }
      evm (aliasF "bidToCheck" "blindedBid") =
        .ok (scratch_revealBidFieldRef evm i "blindedBid", bytes32St) := by
  have hbid' :
      locals["bidToCheck"]? =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    simpa [← Std.HashMap.get?_eq_getElem?] using hbid
  simp [resolveStorageRef?, aliasF, evalStorageRefFrom?, evalStorageRefStep,
    EvalResult.ofOption, EvalResult.bind, bind, pure,
    hbid',
    scratch_revealBidEvaledRef, scratch_revealBidFieldRef, storageTypeStep?, bidStructTy,
    bytes32St]

theorem scratch_resolveStorageRef_reveal_bid_deposit_ok (evm : EVM.State)
    (locals : Store) (i : UInt256)
    (hbid :
      locals.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy)) :
    resolveStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := locals }
      evm (aliasF "bidToCheck" "deposit") =
        .ok (scratch_revealBidFieldRef evm i "deposit", uint256St) := by
  have hbid' :
      locals["bidToCheck"]? =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    simpa [← Std.HashMap.get?_eq_getElem?] using hbid
  simp [resolveStorageRef?, aliasF, evalStorageRefFrom?, evalStorageRefStep,
    EvalResult.ofOption, EvalResult.bind, bind, pure,
    hbid',
    scratch_revealBidEvaledRef, scratch_revealBidFieldRef, storageTypeStep?, bidStructTy,
    uint256St]

theorem scratch_revealBid_blinded_layout (evm : EVM.State) (i : UInt256) :
    blindAuctionConfig.storage.layout (scratch_revealBidFieldRef evm i "blindedBid") =
      fun _ => some (blindAuctionBytes32Loc (scratch_revealBidBlindedSlot evm i)) := by
  funext evm'
  simp [scratch_revealBidFieldRef, scratch_revealBidEvaledRef, scratch_revealBidBlindedSlot]

theorem scratch_revealBid_deposit_layout (evm : EVM.State) (i : UInt256) :
    blindAuctionConfig.storage.layout (scratch_revealBidFieldRef evm i "deposit") =
      fun _ => some (blindAuctionUint256Loc (scratch_revealBidDepositSlot evm i)) := by
  funext evm'
  simp [scratch_revealBidFieldRef, scratch_revealBidEvaledRef, scratch_revealBidDepositSlot,
    scratch_revealBidBlindedSlot]

theorem scratch_evalExpr_reveal_bid_blinded (evm : EVM.State) (locals : Store)
    (i blinded : UInt256)
    (hbid :
      locals.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.storage (aliasF "bidToCheck" "blindedBid")) =
        .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE blinded)) := by
  rw [evalExpr?]
  simp only [scratch_resolveStorageRef_reveal_bid_blinded_ok evm locals i hbid,
    EvalResult.bind, bind]
  unfold bytes32St
  rw [readStorage?_elem (cfg := blindAuctionConfig)
    (evm := evm) (er := scratch_revealBidFieldRef evm i "blindedBid")
    (t := .bytes ⟨31, by decide⟩)
    (loc := blindAuctionBytes32Loc (scratch_revealBidBlindedSlot evm i))
    (scratch_revealBid_blinded_layout evm i)]
  rw [blindAuctionStorageLocLoad_bytes32, hblinded]

theorem scratch_evalExpr_reveal_hash_guard_true (evm : EVM.State) (locals : Store)
    (i blinded : UInt256) (hashBytes : List UInt8)
    (hbid :
      locals.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hhash :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
        scratch_revealPackedHashExpr =
        .ok (.fixedBytes ⟨31, by decide⟩ hashBytes))
    (hne : EVM.Word.toBytesBE blinded ≠ hashBytes) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
        scratch_revealPackedHashExpr) = .ok (.bool true) := by
  rw [evalExpr?]
  simp only [scratch_evalExpr_reveal_bid_blinded evm locals i blinded hbid hblinded,
    hhash, EvalResult.bind, bind]
  simp [evalBinaryOp?, hne]

theorem scratch_evalExpr_reveal_hash_guard_false (evm : EVM.State) (locals : Store)
    (i blinded : UInt256) (hashBytes : List UInt8)
    (hbid :
      locals.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hhash :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
        scratch_revealPackedHashExpr =
        .ok (.fixedBytes ⟨31, by decide⟩ hashBytes))
    (heq : EVM.Word.toBytesBE blinded = hashBytes) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
        scratch_revealPackedHashExpr) = .ok (.bool false) := by
  rw [evalExpr?]
  simp only [scratch_evalExpr_reveal_bid_blinded evm locals i blinded hbid hblinded,
    hhash, EvalResult.bind, bind]
  subst hashBytes
  simp [evalBinaryOp?]

theorem scratch_revealLoopBody_continue_hash_mismatch (evm : EVM.State) (callargs : Store)
    (values fakes secrets : List Value) (len refund i value secret blinded : UInt256)
    (fake : Bool) (fakeRaw : Value) (hashBytes : List UInt8)
    (hbids : callargs.get? "bids" = none)
    (hvalues : callargs.get? "values" = some (.array values))
    (hfakes : callargs.get? "fakes" = some (.array fakes))
    (hsecrets : callargs.get? "secrets" = some (.array secrets))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hboundBids : i.toNat < len.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool fake))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hhash :
      evalExpr? blindAuctionConfig
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStore callargs evm len refund i value secret fake } evm
        scratch_revealPackedHashExpr =
        .ok (.fixedBytes ⟨31, by decide⟩ hashBytes))
    (hne : EVM.Word.toBytesBE blinded ≠ hashBytes) :
    ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_revealLoopStore callargs len refund i }
      evm scratch_revealLoopBodyStmts
      (.continue
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStore callargs evm len refund i value secret fake }
        evm) := by
  unfold scratch_revealLoopBodyStmts
  refine ExecBlock.consNormal
    (scratch_letStorage_reveal_bidToCheck evm callargs len refund i hbids hlen hboundBids) ?_
  let L1 := scratch_revealBidToCheckStore callargs evm len refund i
  let L2 := scratch_revealValueStore callargs evm len refund i value
  let L3 := scratch_revealFakeStore callargs evm len refund i value fake
  let L4 := scratch_revealSecretStore callargs evm len refund i value secret fake
  change ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L1 } evm
    [ .letDecl "value" (some uint256) (.index (.var "values") (.var "i")),
      .letDecl "fake" (some boolTy) (.index (.var "fakes") (.var "i")),
      .letDecl "secret" (some bytes32) (.index (.var "secrets") (.var "i")),
      .ite
        (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
          (.keccak256 (.abiEncodePacked
            [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
        [.continue] [],
      .assign .localVar { base := "refund" }
        (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
      .ite
        (.binary .and (.unary .not (.var "fake"))
          (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
        [ .internalCall "placeBid" [sender, .var "value"] "ok",
          .ite (.var "ok")
            [ .assign .localVar { base := "refund" }
                (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
      .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]
    (.continue { contract := blindAuctionContract, locals := L4 } evm)
  have hvaluesL1 : L1.get? "values" = some (.array values) := by
    simpa [L1, scratch_revealBidToCheckStore, Std.HashMap.getElem?_insert,
      Std.HashMap.get?_eq_getElem?] using
      (scratch_revealLoopStore_values_get (len := len) (refund := refund) (i := i) hvalues)
  have hiL1 : L1.get? "i" = some (.int (Int.ofNat i.toNat)) := by
    simpa [L1, scratch_revealBidToCheckStore, Std.HashMap.getElem?_insert,
      Std.HashMap.get?_eq_getElem?] using
      (scratch_revealLoopStore_i_get callargs len refund i)
  have hvalueEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L1 } evm
        (.index (.var "values") (.var "i")) =
          .ok (.int (Int.ofNat value.toNat)) := by
    exact scratch_evalExpr_reveal_local_array_index_norm evm L1 "values" values i
      (.int (Int.ofNat value.toNat)) (.int (Int.ofNat value.toNat)) hvaluesL1 hiL1
      hboundValues hvalueLookup (by simp [normalizeRawBoolWord?])
  refine ExecBlock.consNormal (ExecStmt.letDecl hvalueEval) ?_
  change ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L2 } evm
    [ .letDecl "fake" (some boolTy) (.index (.var "fakes") (.var "i")),
      .letDecl "secret" (some bytes32) (.index (.var "secrets") (.var "i")),
      .ite
        (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
          (.keccak256 (.abiEncodePacked
            [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
        [.continue] [],
      .assign .localVar { base := "refund" }
        (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
      .ite
        (.binary .and (.unary .not (.var "fake"))
          (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
        [ .internalCall "placeBid" [sender, .var "value"] "ok",
          .ite (.var "ok")
            [ .assign .localVar { base := "refund" }
                (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
      .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]
    (.continue { contract := blindAuctionContract, locals := L4 } evm)
  have hfakesL2 : L2.get? "fakes" = some (.array fakes) := by
    simpa [L2, scratch_revealValueStore, L1, scratch_revealBidToCheckStore,
      Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using
      (scratch_revealLoopStore_fakes_get (len := len) (refund := refund) (i := i) hfakes)
  have hiL2 : L2.get? "i" = some (.int (Int.ofNat i.toNat)) := by
    simpa [L2, scratch_revealValueStore, L1, scratch_revealBidToCheckStore,
      Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using
      (scratch_revealLoopStore_i_get callargs len refund i)
  have hfakeEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L2 } evm
        (.index (.var "fakes") (.var "i")) = .ok (.bool fake) := by
    exact scratch_evalExpr_reveal_local_array_index_norm evm L2 "fakes" fakes i
      fakeRaw (.bool fake) hfakesL2 hiL2 hboundFakes hfakeLookup hfakeNorm
  refine ExecBlock.consNormal (ExecStmt.letDecl hfakeEval) ?_
  change ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L3 } evm
    [ .letDecl "secret" (some bytes32) (.index (.var "secrets") (.var "i")),
      .ite
        (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
          (.keccak256 (.abiEncodePacked
            [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
        [.continue] [],
      .assign .localVar { base := "refund" }
        (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
      .ite
        (.binary .and (.unary .not (.var "fake"))
          (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
        [ .internalCall "placeBid" [sender, .var "value"] "ok",
          .ite (.var "ok")
            [ .assign .localVar { base := "refund" }
                (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
      .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]
    (.continue { contract := blindAuctionContract, locals := L4 } evm)
  have hsecretsL3 : L3.get? "secrets" = some (.array secrets) := by
    simpa [L3, scratch_revealFakeStore, scratch_revealValueStore, L1,
      scratch_revealBidToCheckStore, Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?]
      using
        (scratch_revealLoopStore_secrets_get (len := len) (refund := refund) (i := i)
          hsecrets)
  have hiL3 : L3.get? "i" = some (.int (Int.ofNat i.toNat)) := by
    simpa [L3, scratch_revealFakeStore, scratch_revealValueStore, L1,
      scratch_revealBidToCheckStore, Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?]
      using (scratch_revealLoopStore_i_get callargs len refund i)
  have hsecretEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L3 } evm
        (.index (.var "secrets") (.var "i")) =
          .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)) := by
    exact scratch_evalExpr_reveal_local_array_index_norm evm L3 "secrets" secrets i
      (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret))
      (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret))
      hsecretsL3 hiL3 hboundSecrets hsecretLookup (by simp [normalizeRawBoolWord?])
  refine ExecBlock.consNormal (ExecStmt.letDecl hsecretEval) ?_
  change ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
    [ .ite
        (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
          (.keccak256 (.abiEncodePacked
            [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
        [.continue] [],
      .assign .localVar { base := "refund" }
        (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
      .ite
        (.binary .and (.unary .not (.var "fake"))
          (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
        [ .internalCall "placeBid" [sender, .var "value"] "ok",
          .ite (.var "ok")
            [ .assign .localVar { base := "refund" }
                (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
      .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]
    (.continue { contract := blindAuctionContract, locals := L4 } evm)
  have hbidL4 :
      L4.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    dsimp [L4, scratch_revealSecretStore, scratch_revealFakeStore, scratch_revealValueStore]
    change
      ((((scratch_revealBidToCheckStore callargs evm len refund i).insert "value"
              (.int (Int.ofNat value.toNat))).insert "fake" (.bool fake)).insert "secret"
          (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret))).get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy)
    rw [store_get_ne, store_get_ne, store_get_ne]
    · exact scratch_revealBidToCheckStore_bid_get callargs evm len refund i
    · decide
    · decide
    · decide
  have hguard :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
          (.keccak256 (.abiEncodePacked
            [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")]))) =
          .ok (.bool true) := by
    simpa [scratch_revealPackedHashExpr] using
      scratch_evalExpr_reveal_hash_guard_true evm L4 i blinded hashBytes hbidL4 hblinded
        (by simpa [L4] using hhash) hne
  refine ExecBlock.consContinue ?_
  refine ExecStmt.iteTrue hguard ?_
  exact ExecBlock.consContinue ExecStmt.continue

theorem scratch_revealLoopBody_prefix_exec (evm : EVM.State) (callargs : Store)
    (values fakes secrets : List Value) (len refund i value secret : UInt256)
    (fake : Bool) (fakeRaw : Value) {result : ExecResult}
    (hbids : callargs.get? "bids" = none)
    (hvalues : callargs.get? "values" = some (.array values))
    (hfakes : callargs.get? "fakes" = some (.array fakes))
    (hsecrets : callargs.get? "secrets" = some (.array secrets))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hboundBids : i.toNat < len.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool fake))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (htail :
      ExecBlock blindAuctionConfig
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStore callargs evm len refund i value secret fake }
        evm (List.drop 4 scratch_revealLoopBodyStmts) result) :
    ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_revealLoopStore callargs len refund i }
      evm scratch_revealLoopBodyStmts result := by
  unfold scratch_revealLoopBodyStmts
  refine ExecBlock.consNormal
    (scratch_letStorage_reveal_bidToCheck evm callargs len refund i hbids hlen hboundBids) ?_
  let L1 := scratch_revealBidToCheckStore callargs evm len refund i
  let L2 := scratch_revealValueStore callargs evm len refund i value
  let L3 := scratch_revealFakeStore callargs evm len refund i value fake
  let L4 := scratch_revealSecretStore callargs evm len refund i value secret fake
  have hvaluesL1 : L1.get? "values" = some (.array values) := by
    simpa [L1, scratch_revealBidToCheckStore, Std.HashMap.getElem?_insert,
      Std.HashMap.get?_eq_getElem?] using
      (scratch_revealLoopStore_values_get (len := len) (refund := refund) (i := i) hvalues)
  have hiL1 : L1.get? "i" = some (.int (Int.ofNat i.toNat)) := by
    simpa [L1, scratch_revealBidToCheckStore, Std.HashMap.getElem?_insert,
      Std.HashMap.get?_eq_getElem?] using
      (scratch_revealLoopStore_i_get callargs len refund i)
  have hvalueEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L1 } evm
        (.index (.var "values") (.var "i")) =
          .ok (.int (Int.ofNat value.toNat)) := by
    exact scratch_evalExpr_reveal_local_array_index_norm evm L1 "values" values i
      (.int (Int.ofNat value.toNat)) (.int (Int.ofNat value.toNat)) hvaluesL1 hiL1
      hboundValues hvalueLookup (by simp [normalizeRawBoolWord?])
  refine ExecBlock.consNormal (ExecStmt.letDecl hvalueEval) ?_
  have hfakesL2 : L2.get? "fakes" = some (.array fakes) := by
    simpa [L2, scratch_revealValueStore, L1, scratch_revealBidToCheckStore,
      Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using
      (scratch_revealLoopStore_fakes_get (len := len) (refund := refund) (i := i) hfakes)
  have hiL2 : L2.get? "i" = some (.int (Int.ofNat i.toNat)) := by
    simpa [L2, scratch_revealValueStore, L1, scratch_revealBidToCheckStore,
      Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using
      (scratch_revealLoopStore_i_get callargs len refund i)
  have hfakeEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L2 } evm
        (.index (.var "fakes") (.var "i")) = .ok (.bool fake) := by
    exact scratch_evalExpr_reveal_local_array_index_norm evm L2 "fakes" fakes i
      fakeRaw (.bool fake) hfakesL2 hiL2 hboundFakes hfakeLookup hfakeNorm
  refine ExecBlock.consNormal (ExecStmt.letDecl hfakeEval) ?_
  have hsecretsL3 : L3.get? "secrets" = some (.array secrets) := by
    simpa [L3, scratch_revealFakeStore, scratch_revealValueStore, L1,
      scratch_revealBidToCheckStore, Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?]
      using
        (scratch_revealLoopStore_secrets_get (len := len) (refund := refund) (i := i)
          hsecrets)
  have hiL3 : L3.get? "i" = some (.int (Int.ofNat i.toNat)) := by
    simpa [L3, scratch_revealFakeStore, scratch_revealValueStore, L1,
      scratch_revealBidToCheckStore, Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?]
      using (scratch_revealLoopStore_i_get callargs len refund i)
  have hsecretEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L3 } evm
        (.index (.var "secrets") (.var "i")) =
          .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)) := by
    exact scratch_evalExpr_reveal_local_array_index_norm evm L3 "secrets" secrets i
      (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret))
      (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret))
      hsecretsL3 hiL3 hboundSecrets hsecretLookup (by simp [normalizeRawBoolWord?])
  refine ExecBlock.consNormal (ExecStmt.letDecl hsecretEval) ?_
  simpa [L4, scratch_revealLoopBodyStmts] using htail

/-
theorem scratch_revealLoopBody_prefix (evm : EVM.State) (callargs : Store)
    (values fakes secrets : List Value) (len refund i value secret : UInt256)
    (fake : Bool) (fakeRaw : Value)
    (hbids : callargs.get? "bids" = none)
    (hvalues : callargs.get? "values" = some (.array values))
    (hfakes : callargs.get? "fakes" = some (.array fakes))
    (hsecrets : callargs.get? "secrets" = some (.array secrets))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hboundBids : i.toNat < len.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool fake))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret))) :
    ABlock blindAuctionConfig evm
      { contract := blindAuctionContract, locals := scratch_revealLoopStore callargs len refund i }
      scratch_revealLoopBodyStmts
      { contract := blindAuctionContract,
        locals := scratch_revealSecretStore callargs evm len refund i value secret fake }
      [ .ite
          (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
            (.keccak256 (.abiEncodePacked
              [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
          [.continue] [],
        .assign .localVar { base := "refund" }
          (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
        .ite
          (.binary .and (.unary .not (.var "fake"))
            (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
          [ .internalCall "placeBid" [sender, .var "value"] "ok",
            .ite (.var "ok")
              [ .assign .localVar { base := "refund" }
                  (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
        .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ] := by
  refine ⟨fun htail => ?_⟩
  unfold scratch_revealLoopBodyStmts
  refine ExecBlock.consNormal
    (scratch_letStorage_reveal_bidToCheck evm callargs len refund i hbids hlen hboundBids) ?_
  let L1 := scratch_revealBidToCheckStore callargs evm len refund i
  let L2 := scratch_revealValueStore callargs evm len refund i value
  let L3 := scratch_revealFakeStore callargs evm len refund i value fake
  let L4 := scratch_revealSecretStore callargs evm len refund i value secret fake
  change ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L1 } evm
    [ .letDecl "value" (some uint256) (.index (.var "values") (.var "i")),
      .letDecl "fake" (some boolTy) (.index (.var "fakes") (.var "i")),
      .letDecl "secret" (some bytes32) (.index (.var "secrets") (.var "i")),
      .ite
        (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
          (.keccak256 (.abiEncodePacked
            [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
        [.continue] [],
      .assign .localVar { base := "refund" }
        (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
      .ite
        (.binary .and (.unary .not (.var "fake"))
          (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
        [ .internalCall "placeBid" [sender, .var "value"] "ok",
          .ite (.var "ok")
            [ .assign .localVar { base := "refund" }
                (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
      .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]
    (.continue { contract := blindAuctionContract, locals := L4 } evm) at htail
  change ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L1 } evm
    [ .letDecl "value" (some uint256) (.index (.var "values") (.var "i")),
      .letDecl "fake" (some boolTy) (.index (.var "fakes") (.var "i")),
      .letDecl "secret" (some bytes32) (.index (.var "secrets") (.var "i")),
      .ite
        (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
          (.keccak256 (.abiEncodePacked
            [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
        [.continue] [],
      .assign .localVar { base := "refund" }
        (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
      .ite
        (.binary .and (.unary .not (.var "fake"))
          (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
        [ .internalCall "placeBid" [sender, .var "value"] "ok",
          .ite (.var "ok")
            [ .assign .localVar { base := "refund" }
                (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
      .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]
    (ExecResult.continue { contract := blindAuctionContract, locals := L4 } evm) at htail
  have hvaluesL1 : L1.get? "values" = some (.array values) := by
    simpa [L1, scratch_revealBidToCheckStore, Std.HashMap.getElem?_insert,
      Std.HashMap.get?_eq_getElem?] using
      (scratch_revealLoopStore_values_get (len := len) (refund := refund) (i := i) hvalues)
  have hiL1 : L1.get? "i" = some (.int (Int.ofNat i.toNat)) := by
    simpa [L1, scratch_revealBidToCheckStore, Std.HashMap.getElem?_insert,
      Std.HashMap.get?_eq_getElem?] using
      (scratch_revealLoopStore_i_get callargs len refund i)
  have hvalueEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L1 } evm
        (.index (.var "values") (.var "i")) =
          .ok (.int (Int.ofNat value.toNat)) := by
    exact scratch_evalExpr_reveal_local_array_index_norm evm L1 "values" values i
      (.int (Int.ofNat value.toNat)) (.int (Int.ofNat value.toNat)) hvaluesL1 hiL1
      hboundValues hvalueLookup (by simp [normalizeRawBoolWord?])
  refine ExecBlock.consNormal (ExecStmt.letDecl hvalueEval) ?_
  change ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L2 } evm
    [ .letDecl "fake" (some boolTy) (.index (.var "fakes") (.var "i")),
      .letDecl "secret" (some bytes32) (.index (.var "secrets") (.var "i")),
      .ite
        (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
          (.keccak256 (.abiEncodePacked
            [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
        [.continue] [],
      .assign .localVar { base := "refund" }
        (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
      .ite
        (.binary .and (.unary .not (.var "fake"))
          (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
        [ .internalCall "placeBid" [sender, .var "value"] "ok",
          .ite (.var "ok")
            [ .assign .localVar { base := "refund" }
                (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
      .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]
    (.continue { contract := blindAuctionContract, locals := L4 } evm)
  have hfakesL2 : L2.get? "fakes" = some (.array fakes) := by
    simpa [L2, scratch_revealValueStore, L1, scratch_revealBidToCheckStore,
      Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using
      (scratch_revealLoopStore_fakes_get (len := len) (refund := refund) (i := i) hfakes)
  have hiL2 : L2.get? "i" = some (.int (Int.ofNat i.toNat)) := by
    simpa [L2, scratch_revealValueStore, L1, scratch_revealBidToCheckStore,
      Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using
      (scratch_revealLoopStore_i_get callargs len refund i)
  have hfakeEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L2 } evm
        (.index (.var "fakes") (.var "i")) = .ok (.bool fake) := by
    exact scratch_evalExpr_reveal_local_array_index_norm evm L2 "fakes" fakes i
      fakeRaw (.bool fake) hfakesL2 hiL2 hboundFakes hfakeLookup hfakeNorm
  refine ExecBlock.consNormal (ExecStmt.letDecl hfakeEval) ?_
  change ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L3 } evm
    [ .letDecl "secret" (some bytes32) (.index (.var "secrets") (.var "i")),
      .ite
        (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
          (.keccak256 (.abiEncodePacked
            [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
        [.continue] [],
      .assign .localVar { base := "refund" }
        (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
      .ite
        (.binary .and (.unary .not (.var "fake"))
          (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
        [ .internalCall "placeBid" [sender, .var "value"] "ok",
          .ite (.var "ok")
            [ .assign .localVar { base := "refund" }
                (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
      .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]
    (.continue { contract := blindAuctionContract, locals := L4 } evm)
  have hsecretsL3 : L3.get? "secrets" = some (.array secrets) := by
    simpa [L3, scratch_revealFakeStore, scratch_revealValueStore, L1,
      scratch_revealBidToCheckStore, Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?]
      using
        (scratch_revealLoopStore_secrets_get (len := len) (refund := refund) (i := i)
          hsecrets)
  have hiL3 : L3.get? "i" = some (.int (Int.ofNat i.toNat)) := by
    simpa [L3, scratch_revealFakeStore, scratch_revealValueStore, L1,
      scratch_revealBidToCheckStore, Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?]
      using (scratch_revealLoopStore_i_get callargs len refund i)
  have hsecretEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L3 } evm
        (.index (.var "secrets") (.var "i")) =
          .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)) := by
    exact scratch_evalExpr_reveal_local_array_index_norm evm L3 "secrets" secrets i
      (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret))
      (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret))
      hsecretsL3 hiL3 hboundSecrets hsecretLookup (by simp [normalizeRawBoolWord?])
  refine ExecBlock.consNormal (ExecStmt.letDecl hsecretEval) ?_
  simpa [L4] using htail
-/

theorem scratch_evalExpr_reveal_bid_deposit (evm : EVM.State) (locals : Store)
    (i deposit : UInt256)
    (hbid :
      locals.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy))
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.storage (aliasF "bidToCheck" "deposit")) =
        .ok (.int (Int.ofNat deposit.toNat)) := by
  rw [evalExpr?]
  simp only [scratch_resolveStorageRef_reveal_bid_deposit_ok evm locals i hbid,
    EvalResult.bind, bind]
  unfold uint256St
  rw [readStorage?_elem (cfg := blindAuctionConfig)
    (evm := evm) (er := scratch_revealBidFieldRef evm i "deposit")
    (t := .int uint256Int)
    (loc := blindAuctionUint256Loc (scratch_revealBidDepositSlot evm i))
    (scratch_revealBid_deposit_layout evm i)]
  rw [blindAuctionBiddingEndStorageLocLoad_uint256, hdeposit]

theorem scratch_evalExpr_reveal_placeBid_cond_true (evm : EVM.State) (locals : Store)
    (i value deposit : UInt256)
    (hbid :
      locals.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy))
    (hfake : locals.get? "fake" = some (.bool false))
    (hvalue : locals.get? "value" = some (.int (Int.ofNat value.toNat)))
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit)
    (hle : value.toNat ≤ deposit.toNat) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .and (.unary .not (.var "fake"))
        (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value"))) =
        .ok (.bool true) := by
  rw [evalExpr?]
  simp only [evalExpr?, evalExpr_reveal_var_value evm locals "fake" (.bool false) hfake,
    EvalResult.bind, bind, evalUnaryOp?, EvalResult.ofOption, pure,
    scratch_evalExpr_reveal_bid_deposit evm locals i deposit hbid hdeposit,
    evalExpr_reveal_var_int evm locals "value" (Int.ofNat value.toNat) hvalue]
  simp [evalBinaryOp?]
  exact hle

theorem scratch_evalExpr_reveal_placeBid_cond_false_fake (evm : EVM.State) (locals : Store)
    (i value deposit : UInt256)
    (hbid :
      locals.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy))
    (hfake : locals.get? "fake" = some (.bool true))
    (hvalue : locals.get? "value" = some (.int (Int.ofNat value.toNat)))
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .and (.unary .not (.var "fake"))
        (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value"))) =
        .ok (.bool false) := by
  rw [evalExpr?]
  simp only [evalExpr?, evalExpr_reveal_var_value evm locals "fake" (.bool true) hfake,
    EvalResult.bind, bind, evalUnaryOp?, EvalResult.ofOption, pure,
    scratch_evalExpr_reveal_bid_deposit evm locals i deposit hbid hdeposit,
    evalExpr_reveal_var_int evm locals "value" (Int.ofNat value.toNat) hvalue]
  simp [evalBinaryOp?]

theorem scratch_evalExpr_reveal_placeBid_cond_false_deposit (evm : EVM.State) (locals : Store)
    (i value deposit : UInt256)
    (hbid :
      locals.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy))
    (hfake : locals.get? "fake" = some (.bool false))
    (hvalue : locals.get? "value" = some (.int (Int.ofNat value.toNat)))
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit)
    (hlt : deposit.toNat < value.toNat) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .and (.unary .not (.var "fake"))
        (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value"))) =
        .ok (.bool false) := by
  rw [evalExpr?]
  simp only [evalExpr?, evalExpr_reveal_var_value evm locals "fake" (.bool false) hfake,
    EvalResult.bind, bind, evalUnaryOp?, EvalResult.ofOption, pure,
    scratch_evalExpr_reveal_bid_deposit evm locals i deposit hbid hdeposit,
    evalExpr_reveal_var_int evm locals "value" (Int.ofNat value.toNat) hvalue]
  simp [evalBinaryOp?]
  omega

-- LIBRARY CANDIDATE / LOCAL COPY: full-slot bytes32 storage writes, same shape as the
-- non-importable `Bid.lean` helper; promote to `Storage.lean`/`Common.lean` once shared.
theorem scratch_blindAuctionStorageLocStore_bytes32 (evm : EVM.State)
    (slot word : UInt256) (v : Value)
    (hval : valueToWord v = some word) :
    storageLocStore evm (blindAuctionBytes32Loc slot) v =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot word) := by
  unfold storageLocStore storageLocWriteWord blindAuctionBytes32Loc
  simp only [hval, bind, Option.bind, pure]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof word).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (32 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (32 : Fin 33).val) _) = word.toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (32 : Fin 33).val = 32 from rfl,
    List.take_zero, List.nil_append, List.drop_eq_nil_of_le (by rw [hslen]),
    List.append_nil, List.take_of_length_le (by rw [hvlen]), fromBytes'_toBytesLEWithSizeProof]

def scratch_revealZeroBlindedState (evm : EVM.State) (i : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (scratch_revealBidBlindedSlot evm i) (EVM.Word.ofNat 0)

theorem scratch_revealBidEvaledRef_storageStore (evm : EVM.State)
    (a : EVM.Address) (slot word i : UInt256) :
    scratch_revealBidEvaledRef (Solm.EVM.storageStore evm a slot word) i =
      scratch_revealBidEvaledRef evm i := by
  unfold scratch_revealBidEvaledRef Solm.EVM.storageStore
  cases h : evm.lookupAccount a <;> simp [Option.option, h, Ethereum.State.setAccount]

theorem scratch_evalExpr_reveal_cast_zero_bytes32 (evm : EVM.State) (locals : Store) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.cast (.intLit 0) bytes32St) =
        .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (EVM.Word.ofNat 0))) := by
  rw [evalExpr?]
  simp only [evalExpr?, EvalResult.bind, bind, pure]
  unfold bytes32St castValue? EvalResult.ofOption
  simp [EVM.Word.ofNat]

theorem scratch_assign_reveal_blinded_zero (evm : EVM.State) (locals : Store)
    (i : UInt256)
    (hbid :
      locals.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy)) :
    assignStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      .storage (aliasF "bidToCheck" "blindedBid")
      (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (EVM.Word.ofNat 0))) =
        .ok ({ contract := blindAuctionContract, locals := locals },
          scratch_revealZeroBlindedState evm i) := by
  rw [assignStorageRef?]
  simp only [scratch_resolveStorageRef_reveal_bid_blinded_ok evm locals i hbid,
    EvalResult.bind, bind]
  have hloc := scratch_revealBid_blinded_layout evm i
  simp only [hloc, EvalResult.ofOption, Option.bind]
  rw [scratch_blindAuctionStorageLocStore_bytes32 (word := EVM.Word.ofNat 0)]
  · rfl
  · native_decide

theorem scratch_assign_local_value (evm : EVM.State) (locals : Store)
    (name : Ident) (old value : Value)
    (hget : locals.get? name = some old) :
    assignStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      .localVar { base := name } value =
        .ok ({ contract := blindAuctionContract, locals := locals.insert name value }, evm) := by
  have hget' : locals[name]? = some old := by
    simpa [← Std.HashMap.get?_eq_getElem?] using hget
  simp [assignStorageRef?, updateLocalPath?, hget', EvalResult.bind, bind, pure]

theorem scratch_evalExprs_reveal_placeBid_args (evm : EVM.State) (locals : Store)
    (value : UInt256)
    (hvalue : locals.get? "value" = some (.int (Int.ofNat value.toNat))) :
    evalExprs? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      [sender, .var "value"] =
        .ok [.address evm.executionEnv.source, .int (Int.ofNat value.toNat)] := by
  simp [evalExprs?, evalExpr_reveal_sender evm locals,
    evalExpr_reveal_var_int evm locals "value" (Int.ofNat value.toNat) hvalue,
    EvalResult.bind, bind, pure]

theorem scratch_evalExpr_reveal_refund_add_deposit (evm : EVM.State) (locals : Store)
    (i refund deposit : UInt256)
    (hbid :
      locals.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy))
    (hrefund : locals.get? "refund" = some (.int (Int.ofNat refund.toNat)))
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit)
    (hfit : refund.toNat + deposit.toNat < UInt256.size) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))) =
        .ok (.int (Int.ofNat (refund.toNat + deposit.toNat))) := by
  unfold u256
  rw [evalExpr?]
  rw [evalExpr?]
  simp only [evalExpr_reveal_var_int evm locals "refund" (Int.ofNat refund.toNat) hrefund,
    scratch_evalExpr_reveal_bid_deposit evm locals i deposit hbid hdeposit,
    EvalResult.bind, bind]
  simp [evalBinaryOp?]
  have hnonneg : ¬ (((refund.toNat : Int) + (deposit.toNat : Int)) < 0) := by
    exact not_lt_of_ge (Int.add_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))
  have hlt : ¬ ((2 : Int) ^ 256 ≤ (refund.toNat : Int) + (deposit.toNat : Int)) := by
    norm_num [UInt256.size] at hfit ⊢
    omega
  have hif :
      ¬ ((refund.toNat : Int) + (deposit.toNat : Int) < 0 ∨
        (2 : Int) ^ 256 ≤ (refund.toNat : Int) + (deposit.toNat : Int)) := by
    intro hcond
    rcases hcond with hneg | hge
    · exact hnonneg hneg
    · exact hlt hge
  simp only [uint256Int]
  rw [if_neg hif]
  rfl

theorem scratch_evalExpr_reveal_refund_add_deposit_revert (evm : EVM.State)
    (locals : Store) (i refund deposit : UInt256)
    (hbid :
      locals.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy))
    (hrefund : locals.get? "refund" = some (.int (Int.ofNat refund.toNat)))
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit)
    (hover : UInt256.size ≤ refund.toNat + deposit.toNat) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))) =
        .revert := by
  unfold u256
  rw [evalExpr?]
  rw [evalExpr?]
  simp only [evalExpr_reveal_var_int evm locals "refund" (Int.ofNat refund.toNat) hrefund,
    scratch_evalExpr_reveal_bid_deposit evm locals i deposit hbid hdeposit,
    EvalResult.bind, bind]
  simp [evalBinaryOp?]
  have hge : (2 : Int) ^ 256 ≤ (refund.toNat : Int) + (deposit.toNat : Int) := by
    norm_num [UInt256.size] at hover ⊢
    omega
  have hif :
      (refund.toNat : Int) + (deposit.toNat : Int) < 0 ∨
        (2 : Int) ^ 256 ≤ (refund.toNat : Int) + (deposit.toNat : Int) := by
    exact Or.inr hge
  simp only [uint256Int]
  rw [if_pos hif]

theorem scratch_evalExpr_reveal_refund_sub_value (evm : EVM.State) (locals : Store)
    (refund value : UInt256)
    (hrefund : locals.get? "refund" = some (.int (Int.ofNat refund.toNat)))
    (hvalue : locals.get? "value" = some (.int (Int.ofNat value.toNat)))
    (hle : value.toNat ≤ refund.toNat) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (u256 (.binary .sub (.var "refund") (.var "value"))) =
        .ok (.int (Int.ofNat (refund.toNat - value.toNat))) := by
  unfold u256
  rw [evalExpr?]
  rw [evalExpr?]
  simp only [evalExpr_reveal_var_int evm locals "refund" (Int.ofNat refund.toNat) hrefund,
    evalExpr_reveal_var_int evm locals "value" (Int.ofNat value.toNat) hvalue,
    EvalResult.bind, bind]
  simp [evalBinaryOp?]
  have hsub_nonneg :
      ¬ (((refund.toNat : Int) - (value.toNat : Int)) < 0) := by
    omega
  have hsub_lt : ¬ ((2 : Int) ^ 256 ≤ (refund.toNat : Int) - (value.toNat : Int)) := by
    have hrefund_lt : refund.toNat < UInt256.size := refund.val.isLt
    norm_num [UInt256.size] at hrefund_lt ⊢
    omega
  have hif :
      ¬ ((refund.toNat : Int) - (value.toNat : Int) < 0 ∨
        (2 : Int) ^ 256 ≤ (refund.toNat : Int) - (value.toNat : Int)) := by
    intro hcond
    rcases hcond with hneg | hge
    · exact hsub_nonneg hneg
    · exact hsub_lt hge
  simp only [uint256Int]
  rw [if_neg hif]
  change EvalResult.ok (Value.int ((refund.toNat : Int) - (value.toNat : Int))) =
    EvalResult.ok (Value.int (Int.ofNat (refund.toNat - value.toNat)))
  rw [← Int.ofNat_sub hle]
  rfl

theorem scratch_evalExpr_reveal_refund_sub_value_revert (evm : EVM.State) (locals : Store)
    (refund value : UInt256)
    (hrefund : locals.get? "refund" = some (.int (Int.ofNat refund.toNat)))
    (hvalue : locals.get? "value" = some (.int (Int.ofNat value.toNat)))
    (hlt : refund.toNat < value.toNat) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (u256 (.binary .sub (.var "refund") (.var "value"))) =
        .revert := by
  unfold u256
  rw [evalExpr?]
  rw [evalExpr?]
  simp only [evalExpr_reveal_var_int evm locals "refund" (Int.ofNat refund.toNat) hrefund,
    evalExpr_reveal_var_int evm locals "value" (Int.ofNat value.toNat) hvalue,
    EvalResult.bind, bind]
  simp [evalBinaryOp?]
  have hneg : (refund.toNat : Int) - (value.toNat : Int) < 0 := by
    omega
  have hif :
      (refund.toNat : Int) - (value.toNat : Int) < 0 ∨
        (2 : Int) ^ 256 ≤ (refund.toNat : Int) - (value.toNat : Int) := Or.inl hneg
  simp only [uint256Int]
  rw [if_pos hif]

theorem scratch_evalExpr_reveal_i_add_one (evm : EVM.State) (locals : Store)
    (i : UInt256)
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hfit : i.toNat + 1 < UInt256.size) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .add (.var "i") (.intLit 1)) =
        .ok (.int (Int.ofNat (i + ⟨1⟩).toNat)) := by
  rw [evalExpr?]
  simp only [evalExpr_reveal_var_int evm locals "i" (Int.ofNat i.toNat) hi,
    evalExpr?, EvalResult.bind, bind, pure]
  simp [evalBinaryOp?]
  have hadd : (i + ⟨1⟩).toNat = i.toNat + 1 := add1_toNat hfit
  rw [hadd]
  norm_num

theorem scratch_revealLoopPostStep (evm : EVM.State) (locals : Store) (i : UInt256)
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hfit : i.toNat + 1 < UInt256.size) :
    ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      [ .assign .localVar { base := "i" } (.binary .add (.var "i") (.intLit 1)) ]
      (.ok { contract := blindAuctionContract,
              locals := locals.insert "i" (.int (Int.ofNat (i + ⟨1⟩).toNat)) } evm) := by
  refine ExecBlock.consNormal ?_ ExecBlock.nil
  exact ExecStmt.assign
    (scratch_evalExpr_reveal_i_add_one evm locals i hi hfit)
    (scratch_assign_local_value evm locals "i" (.int (Int.ofNat i.toNat))
      (.int (Int.ofNat (i + ⟨1⟩).toNat)) hi)

def scratch_revealSourceLoopInv (len : UInt256)
    (Rest : ℕ → UInt256 → UInt256 → Store → EVM.State → Prop)
    (v : ℕ) (locals : Store) (evm : EVM.State) : Prop :=
  ∃ i refund,
    locals.get? "i" = some (.int (Int.ofNat i.toNat)) ∧
    locals.get? "length" = some (.int (Int.ofNat len.toNat)) ∧
    locals.get? "refund" = some (.int (Int.ofNat refund.toNat)) ∧
    i.toNat + v = len.toNat ∧
    i.toNat ≤ len.toNat ∧
    Rest v i refund locals evm

theorem scratch_revealForLoop_from_step (len : UInt256)
    (Rest : ℕ → UInt256 → UInt256 → Store → EVM.State → Prop)
    (hstep : ∀ (v : ℕ) (L : Store) (evm : EVM.State) (i refund : UInt256),
        scratch_revealSourceLoopInv len Rest (v + 1) L evm →
        L.get? "i" = some (.int (Int.ofNat i.toNat)) →
        L.get? "refund" = some (.int (Int.ofNat refund.toNat)) →
        ∃ L1 evm1,
          (ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
              scratch_revealLoopBodyStmts (.ok { contract := blindAuctionContract, locals := L1 }
                evm1) ∨
            ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
              scratch_revealLoopBodyStmts
                (.continue { contract := blindAuctionContract, locals := L1 } evm1)) ∧
          ∃ L2 evm2,
            ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L1 } evm1
              scratch_revealLoopPostStmts (.ok { contract := blindAuctionContract, locals := L2 }
                evm2) ∧
            scratch_revealSourceLoopInv len Rest v L2 evm2) :
    ∀ v L evm, scratch_revealSourceLoopInv len Rest v L evm →
      ∃ L' evm',
        ExecForLoop blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
          (.binary .lt (.var "i") (.var "length")) scratch_revealLoopPostStmts
          scratch_revealLoopBodyStmts
          (.ok { contract := blindAuctionContract, locals := L' } evm') ∧
        scratch_revealSourceLoopInv len Rest 0 L' evm' := by
  refine execFor_var_state_continue (cfg := blindAuctionConfig) (C := blindAuctionContract)
    (condExpr := .binary .lt (.var "i") (.var "length"))
    (post := scratch_revealLoopPostStmts) (body := scratch_revealLoopBodyStmts)
    (P := scratch_revealSourceLoopInv len Rest) ?_ ?_ ?_
  · intro L evm hP
    rcases hP with ⟨i, refund, hi, hlen, _hrefund, hvar, _hle, _hrest⟩
    exact scratch_evalExpr_reveal_loop_cond_false_of_get evm L len i hi hlen (by omega)
  · intro v L evm hP
    rcases hP with ⟨i, refund, hi, hlen, _hrefund, hvar, _hle, _hrest⟩
    exact scratch_evalExpr_reveal_loop_cond_true_of_get evm L len i hi hlen (by omega)
  · intro v L evm hP
    rcases hP with ⟨i, refund, hi, hlen, hrefund, hvar, hle, hrest⟩
    exact hstep v L evm i refund ⟨i, refund, hi, hlen, hrefund, hvar, hle, hrest⟩ hi
      hrefund

theorem scratch_blindAuctionRevealBodyReturns_callSuccess_fromLoop
    (evm evmLoop evm' : EVM.State) (callargs : Store)
    (values fakes secrets : List Value) (len refund i : UInt256) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hafter :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbefore :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)
    (hbidding : callargs.get? biddingEndRef.base = none)
    (hreveal : callargs.get? revealEndRef.base = none)
    (hbids : callargs.get? "bids" = none)
    (hvalues : callargs.get? "values" = some (.array values))
    (hfakes : callargs.get? "fakes" = some (.array fakes))
    (hsecrets : callargs.get? "secrets" = some (.array secrets))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hvaluesLen : values.length = len.toNat)
    (hfakesLen : fakes.length = len.toNat)
    (hsecretsLen : secrets.length = len.toNat)
    (hloop :
      ExecForLoop blindAuctionConfig
        ({ contract := blindAuctionContract, locals := scratch_revealLoopStore callargs len ⟨0⟩ ⟨0⟩ } :
          Frame) evm
        (.binary .lt (.var "i") (.var "length")) scratch_revealLoopPostStmts
        scratch_revealLoopBodyStmts
        (.ok
          ({ contract := blindAuctionContract,
             locals := scratch_revealLoopStore callargs len refund i } : Frame) evmLoop))
    (hcall :
      callViaEVM evmLoop (EVM.address evmLoop.executionEnv.source)
        (Int.ofNat refund.toNat) ByteArray.empty (true, evm', out)) :
      ExecTransitionBody blindAuctionConfig blindAuctionContract evm callargs revealTransition.body
        (.returned
          ({ contract := blindAuctionContract,
             locals := scratch_revealCallStore callargs len refund i true out } : Frame)
          evm' none) := by
    let lengthFrame : Frame :=
      { contract := blindAuctionContract, locals := scratch_revealLengthStore callargs len }
    let refundFrame : Frame :=
      { contract := blindAuctionContract,
        locals := scratch_revealRefundStore callargs len ⟨0⟩ }
    let initLoopFrame : Frame :=
      { contract := blindAuctionContract,
        locals := scratch_revealLoopStore callargs len ⟨0⟩ ⟨0⟩ }
    let loopFrame : Frame :=
      { contract := blindAuctionContract,
        locals := scratch_revealLoopStore callargs len refund i }
    let finalFrame : Frame :=
      { contract := blindAuctionContract,
        locals := scratch_revealCallStore callargs len refund i true out }
    refine ExecFuncBody.execBlockOK ?_
    unfold revealTransition
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalExpr_reveal_afterBiddingEnd_true evm callargs hbidding hafter)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalExpr_reveal_beforeRevealEnd_true evm callargs hreveal hbefore)) ?_
    have hlengthEval :
        evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := callargs }
          evm (.arrayLength .storage (bidsRef sender)) = .ok (.int (Int.ofNat len.toNat)) := by
      exact evalExpr_reveal_bids_length_any evm callargs len hbids hlen
    refine ExecBlock.consNormal (ExecStmt.letDecl hlengthEval) ?_
    change ExecBlock blindAuctionConfig lengthFrame evm
      (List.drop 4 revealTransition.body)
      (.ok finalFrame evm')
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue
        (evalExpr_reveal_local_array_length_eq_var_true evm
          (scratch_revealLengthStore callargs len) "values" values len ?_
          (by simp [scratch_revealLengthStore]) hvaluesLen)) ?_
    · unfold scratch_revealLengthStore
      rw [store_get_ne]
      · exact hvalues
      · decide
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue
        (evalExpr_reveal_local_array_length_eq_var_true evm
          (scratch_revealLengthStore callargs len) "fakes" fakes len ?_
          (by simp [scratch_revealLengthStore]) hfakesLen)) ?_
    · unfold scratch_revealLengthStore
      rw [store_get_ne]
      · exact hfakes
      · decide
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue
        (evalExpr_reveal_local_array_length_eq_var_true evm
          (scratch_revealLengthStore callargs len) "secrets" secrets len ?_
          (by simp [scratch_revealLengthStore]) hsecretsLen)) ?_
    · unfold scratch_revealLengthStore
      rw [store_get_ne]
      · exact hsecrets
      · decide
    refine ExecBlock.consNormal
      (ExecStmt.letDecl (value := .int 0) (by simp [evalExpr?, pure])) ?_
    change ExecBlock blindAuctionConfig refundFrame evm
      [ scratch_revealForStmt,
        .lowLevelCall sender (.var "refund") (.newBytes (.intLit 0)) "success" "_data",
        .require (.var "success") ]
      (.ok finalFrame evm')
    have hfor :
        ExecStmt blindAuctionConfig refundFrame evm
          scratch_revealForStmt
          (.ok loopFrame evmLoop) := by
      have hinit :
          ExecBlock blindAuctionConfig
            refundFrame evm
            [ .letDecl "i" (some uint256) (.intLit 0) ]
            (.ok initLoopFrame evm) := by
        refine ExecBlock.consNormal
          (ExecStmt.letDecl (value := .int 0) (by simp [evalExpr?, pure])) ?_
        exact ExecBlock.nil
      exact ExecStmt.for hinit hloop
    refine ExecBlock.consNormal hfor ?_
    refine ExecBlock.consNormal
      (ExecStmt.lowLevelCallSuccess
        (evalExpr_reveal_sender evmLoop (scratch_revealLoopStore callargs len refund i))
        (evalExpr_reveal_refund evmLoop (scratch_revealLoopStore callargs len refund i)
          refund (scratch_revealLoopStore_refund_get callargs len refund i))
        (evalExpr_reveal_emptyBytes evmLoop (scratch_revealLoopStore callargs len refund i))
        hcall) ?_
    exact ExecBlock.consNormal
      (ExecStmt.requireTrue (scratch_evalExpr_reveal_success evm' callargs len refund i true out))
      ExecBlock.nil

theorem scratch_blindAuctionRevealBodyReverts_callFailure_fromLoop
    (evm evmLoop evm' : EVM.State) (callargs : Store)
    (values fakes secrets : List Value) (len refund i : UInt256) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hafter :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbefore :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)
    (hbidding : callargs.get? biddingEndRef.base = none)
    (hreveal : callargs.get? revealEndRef.base = none)
    (hbids : callargs.get? "bids" = none)
    (hvalues : callargs.get? "values" = some (.array values))
    (hfakes : callargs.get? "fakes" = some (.array fakes))
    (hsecrets : callargs.get? "secrets" = some (.array secrets))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hvaluesLen : values.length = len.toNat)
    (hfakesLen : fakes.length = len.toNat)
    (hsecretsLen : secrets.length = len.toNat)
    (hloop :
      ExecForLoop blindAuctionConfig
        ({ contract := blindAuctionContract, locals := scratch_revealLoopStore callargs len ⟨0⟩ ⟨0⟩ } :
          Frame) evm
        (.binary .lt (.var "i") (.var "length")) scratch_revealLoopPostStmts
        scratch_revealLoopBodyStmts
        (.ok
          ({ contract := blindAuctionContract,
             locals := scratch_revealLoopStore callargs len refund i } : Frame) evmLoop))
    (hcall :
      callViaEVM evmLoop (EVM.address evmLoop.executionEnv.source)
        (Int.ofNat refund.toNat) ByteArray.empty (false, evm', out)) :
      ExecTransitionBody blindAuctionConfig blindAuctionContract evm callargs revealTransition.body
        .reverted := by
    let lengthFrame : Frame :=
      { contract := blindAuctionContract, locals := scratch_revealLengthStore callargs len }
    let refundFrame : Frame :=
      { contract := blindAuctionContract,
        locals := scratch_revealRefundStore callargs len ⟨0⟩ }
    let initLoopFrame : Frame :=
      { contract := blindAuctionContract,
        locals := scratch_revealLoopStore callargs len ⟨0⟩ ⟨0⟩ }
    let loopFrame : Frame :=
      { contract := blindAuctionContract,
        locals := scratch_revealLoopStore callargs len refund i }
    refine ExecFuncBody.execBlockRevert ?_
    unfold revealTransition
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalExpr_reveal_afterBiddingEnd_true evm callargs hbidding hafter)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalExpr_reveal_beforeRevealEnd_true evm callargs hreveal hbefore)) ?_
    have hlengthEval :
        evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := callargs }
          evm (.arrayLength .storage (bidsRef sender)) = .ok (.int (Int.ofNat len.toNat)) := by
      exact evalExpr_reveal_bids_length_any evm callargs len hbids hlen
    refine ExecBlock.consNormal (ExecStmt.letDecl hlengthEval) ?_
    change ExecBlock blindAuctionConfig lengthFrame evm
      (List.drop 4 revealTransition.body) .reverted
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue
        (evalExpr_reveal_local_array_length_eq_var_true evm
          (scratch_revealLengthStore callargs len) "values" values len ?_
          (by simp [scratch_revealLengthStore]) hvaluesLen)) ?_
    · unfold scratch_revealLengthStore
      rw [store_get_ne]
      · exact hvalues
      · decide
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue
        (evalExpr_reveal_local_array_length_eq_var_true evm
          (scratch_revealLengthStore callargs len) "fakes" fakes len ?_
          (by simp [scratch_revealLengthStore]) hfakesLen)) ?_
    · unfold scratch_revealLengthStore
      rw [store_get_ne]
      · exact hfakes
      · decide
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue
        (evalExpr_reveal_local_array_length_eq_var_true evm
          (scratch_revealLengthStore callargs len) "secrets" secrets len ?_
          (by simp [scratch_revealLengthStore]) hsecretsLen)) ?_
    · unfold scratch_revealLengthStore
      rw [store_get_ne]
      · exact hsecrets
      · decide
    refine ExecBlock.consNormal
      (ExecStmt.letDecl (value := .int 0) (by simp [evalExpr?, pure])) ?_
    change ExecBlock blindAuctionConfig refundFrame evm
      [ scratch_revealForStmt,
        .lowLevelCall sender (.var "refund") (.newBytes (.intLit 0)) "success" "_data",
        .require (.var "success") ]
      .reverted
    have hfor :
        ExecStmt blindAuctionConfig refundFrame evm
          scratch_revealForStmt
          (.ok loopFrame evmLoop) := by
      have hinit :
          ExecBlock blindAuctionConfig
            refundFrame evm
            [ .letDecl "i" (some uint256) (.intLit 0) ]
            (.ok initLoopFrame evm) := by
        refine ExecBlock.consNormal
          (ExecStmt.letDecl (value := .int 0) (by simp [evalExpr?, pure])) ?_
        exact ExecBlock.nil
      exact ExecStmt.for hinit hloop
    refine ExecBlock.consNormal hfor ?_
    refine ExecBlock.consNormal
      (ExecStmt.lowLevelCallFailure
        (evalExpr_reveal_sender evmLoop (scratch_revealLoopStore callargs len refund i))
        (evalExpr_reveal_refund evmLoop (scratch_revealLoopStore callargs len refund i)
          refund (scratch_revealLoopStore_refund_get callargs len refund i))
        (evalExpr_reveal_emptyBytes evmLoop (scratch_revealLoopStore callargs len refund i))
        hcall) ?_
    exact ExecBlock.consRevert
      (ExecStmt.requireFalse (scratch_evalExpr_reveal_success evm' callargs len refund i false out))

theorem scratch_blindAuctionRevealBodyReturns_callSuccess_fromLoopOfLocals
    (evm evmLoop evm' : EVM.State) (callargs loopLocals : Store)
    (values fakes secrets : List Value) (len refund : UInt256) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hafter :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbefore :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)
    (hbidding : callargs.get? biddingEndRef.base = none)
    (hreveal : callargs.get? revealEndRef.base = none)
    (hbids : callargs.get? "bids" = none)
    (hvalues : callargs.get? "values" = some (.array values))
    (hfakes : callargs.get? "fakes" = some (.array fakes))
    (hsecrets : callargs.get? "secrets" = some (.array secrets))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hvaluesLen : values.length = len.toNat)
    (hfakesLen : fakes.length = len.toNat)
    (hsecretsLen : secrets.length = len.toNat)
    (hrefund : loopLocals.get? "refund" = some (.int (Int.ofNat refund.toNat)))
    (hloop :
      ExecForLoop blindAuctionConfig
        ({ contract := blindAuctionContract, locals := scratch_revealLoopStore callargs len ⟨0⟩ ⟨0⟩ } :
          Frame) evm
        (.binary .lt (.var "i") (.var "length")) scratch_revealLoopPostStmts
        scratch_revealLoopBodyStmts
        (.ok ({ contract := blindAuctionContract, locals := loopLocals } : Frame) evmLoop))
    (hcall :
      callViaEVM evmLoop (EVM.address evmLoop.executionEnv.source)
        (Int.ofNat refund.toNat) ByteArray.empty (true, evm', out)) :
      ExecTransitionBody blindAuctionConfig blindAuctionContract evm callargs revealTransition.body
        (.returned
          ({ contract := blindAuctionContract,
             locals := scratch_revealCallStoreOf loopLocals true out } : Frame)
          evm' none) := by
  let lengthFrame : Frame :=
    { contract := blindAuctionContract, locals := scratch_revealLengthStore callargs len }
  let refundFrame : Frame :=
    { contract := blindAuctionContract,
      locals := scratch_revealRefundStore callargs len ⟨0⟩ }
  let initLoopFrame : Frame :=
    { contract := blindAuctionContract,
      locals := scratch_revealLoopStore callargs len ⟨0⟩ ⟨0⟩ }
  refine ExecFuncBody.execBlockOK ?_
  unfold revealTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_reveal_afterBiddingEnd_true evm callargs hbidding hafter)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_reveal_beforeRevealEnd_true evm callargs hreveal hbefore)) ?_
  have hlengthEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := callargs }
        evm (.arrayLength .storage (bidsRef sender)) = .ok (.int (Int.ofNat len.toNat)) := by
    exact evalExpr_reveal_bids_length_any evm callargs len hbids hlen
  refine ExecBlock.consNormal (ExecStmt.letDecl hlengthEval) ?_
  change ExecBlock blindAuctionConfig lengthFrame evm
    (List.drop 4 revealTransition.body)
    (.ok
      ({ contract := blindAuctionContract,
         locals := scratch_revealCallStoreOf loopLocals true out } : Frame) evm')
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_array_length_eq_var_true evm
        (scratch_revealLengthStore callargs len) "values" values len ?_
        (by simp [scratch_revealLengthStore]) hvaluesLen)) ?_
  · unfold scratch_revealLengthStore
    rw [store_get_ne]
    · exact hvalues
    · decide
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_array_length_eq_var_true evm
        (scratch_revealLengthStore callargs len) "fakes" fakes len ?_
        (by simp [scratch_revealLengthStore]) hfakesLen)) ?_
  · unfold scratch_revealLengthStore
    rw [store_get_ne]
    · exact hfakes
    · decide
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_array_length_eq_var_true evm
        (scratch_revealLengthStore callargs len) "secrets" secrets len ?_
        (by simp [scratch_revealLengthStore]) hsecretsLen)) ?_
  · unfold scratch_revealLengthStore
    rw [store_get_ne]
    · exact hsecrets
    · decide
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (value := .int 0) (by simp [evalExpr?, pure])) ?_
  change ExecBlock blindAuctionConfig refundFrame evm
    [ scratch_revealForStmt,
      .lowLevelCall sender (.var "refund") (.newBytes (.intLit 0)) "success" "_data",
      .require (.var "success") ]
    (.ok
      ({ contract := blindAuctionContract,
         locals := scratch_revealCallStoreOf loopLocals true out } : Frame) evm')
  have hfor :
      ExecStmt blindAuctionConfig refundFrame evm
        scratch_revealForStmt
        (.ok { contract := blindAuctionContract, locals := loopLocals } evmLoop) := by
    have hinit :
        ExecBlock blindAuctionConfig
          refundFrame evm
          [ .letDecl "i" (some uint256) (.intLit 0) ]
          (.ok initLoopFrame evm) := by
      refine ExecBlock.consNormal
        (ExecStmt.letDecl (value := .int 0) (by simp [evalExpr?, pure])) ?_
      exact ExecBlock.nil
    exact ExecStmt.for hinit hloop
  refine ExecBlock.consNormal hfor ?_
  refine ExecBlock.consNormal
    (ExecStmt.lowLevelCallSuccess
      (evalExpr_reveal_sender evmLoop loopLocals)
      (evalExpr_reveal_refund evmLoop loopLocals refund hrefund)
      (evalExpr_reveal_emptyBytes evmLoop loopLocals)
      hcall) ?_
  exact ExecBlock.consNormal
    (ExecStmt.requireTrue (scratch_evalExpr_reveal_success_of evm' loopLocals true out))
    ExecBlock.nil

theorem scratch_blindAuctionRevealBodyReverts_callFailure_fromLoopOfLocals
    (evm evmLoop evm' : EVM.State) (callargs loopLocals : Store)
    (values fakes secrets : List Value) (len refund : UInt256) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hafter :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbefore :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)
    (hbidding : callargs.get? biddingEndRef.base = none)
    (hreveal : callargs.get? revealEndRef.base = none)
    (hbids : callargs.get? "bids" = none)
    (hvalues : callargs.get? "values" = some (.array values))
    (hfakes : callargs.get? "fakes" = some (.array fakes))
    (hsecrets : callargs.get? "secrets" = some (.array secrets))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hvaluesLen : values.length = len.toNat)
    (hfakesLen : fakes.length = len.toNat)
    (hsecretsLen : secrets.length = len.toNat)
    (hrefund : loopLocals.get? "refund" = some (.int (Int.ofNat refund.toNat)))
    (hloop :
      ExecForLoop blindAuctionConfig
        ({ contract := blindAuctionContract, locals := scratch_revealLoopStore callargs len ⟨0⟩ ⟨0⟩ } :
          Frame) evm
        (.binary .lt (.var "i") (.var "length")) scratch_revealLoopPostStmts
        scratch_revealLoopBodyStmts
        (.ok ({ contract := blindAuctionContract, locals := loopLocals } : Frame) evmLoop))
    (hcall :
      callViaEVM evmLoop (EVM.address evmLoop.executionEnv.source)
        (Int.ofNat refund.toNat) ByteArray.empty (false, evm', out)) :
      ExecTransitionBody blindAuctionConfig blindAuctionContract evm callargs revealTransition.body
        .reverted := by
  let lengthFrame : Frame :=
    { contract := blindAuctionContract, locals := scratch_revealLengthStore callargs len }
  let refundFrame : Frame :=
    { contract := blindAuctionContract,
      locals := scratch_revealRefundStore callargs len ⟨0⟩ }
  let initLoopFrame : Frame :=
    { contract := blindAuctionContract,
      locals := scratch_revealLoopStore callargs len ⟨0⟩ ⟨0⟩ }
  refine ExecFuncBody.execBlockRevert ?_
  unfold revealTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_reveal_afterBiddingEnd_true evm callargs hbidding hafter)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_reveal_beforeRevealEnd_true evm callargs hreveal hbefore)) ?_
  have hlengthEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := callargs }
        evm (.arrayLength .storage (bidsRef sender)) = .ok (.int (Int.ofNat len.toNat)) := by
    exact evalExpr_reveal_bids_length_any evm callargs len hbids hlen
  refine ExecBlock.consNormal (ExecStmt.letDecl hlengthEval) ?_
  change ExecBlock blindAuctionConfig lengthFrame evm
    (List.drop 4 revealTransition.body) .reverted
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_array_length_eq_var_true evm
        (scratch_revealLengthStore callargs len) "values" values len ?_
        (by simp [scratch_revealLengthStore]) hvaluesLen)) ?_
  · unfold scratch_revealLengthStore
    rw [store_get_ne]
    · exact hvalues
    · decide
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_array_length_eq_var_true evm
        (scratch_revealLengthStore callargs len) "fakes" fakes len ?_
        (by simp [scratch_revealLengthStore]) hfakesLen)) ?_
  · unfold scratch_revealLengthStore
    rw [store_get_ne]
    · exact hfakes
    · decide
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_array_length_eq_var_true evm
        (scratch_revealLengthStore callargs len) "secrets" secrets len ?_
        (by simp [scratch_revealLengthStore]) hsecretsLen)) ?_
  · unfold scratch_revealLengthStore
    rw [store_get_ne]
    · exact hsecrets
    · decide
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (value := .int 0) (by simp [evalExpr?, pure])) ?_
  change ExecBlock blindAuctionConfig refundFrame evm
    [ scratch_revealForStmt,
      .lowLevelCall sender (.var "refund") (.newBytes (.intLit 0)) "success" "_data",
      .require (.var "success") ]
    .reverted
  have hfor :
      ExecStmt blindAuctionConfig refundFrame evm
        scratch_revealForStmt
        (.ok { contract := blindAuctionContract, locals := loopLocals } evmLoop) := by
    have hinit :
        ExecBlock blindAuctionConfig
          refundFrame evm
          [ .letDecl "i" (some uint256) (.intLit 0) ]
          (.ok initLoopFrame evm) := by
      refine ExecBlock.consNormal
        (ExecStmt.letDecl (value := .int 0) (by simp [evalExpr?, pure])) ?_
      exact ExecBlock.nil
    exact ExecStmt.for hinit hloop
  refine ExecBlock.consNormal hfor ?_
  refine ExecBlock.consNormal
    (ExecStmt.lowLevelCallFailure
      (evalExpr_reveal_sender evmLoop loopLocals)
      (evalExpr_reveal_refund evmLoop loopLocals refund hrefund)
      (evalExpr_reveal_emptyBytes evmLoop loopLocals)
      hcall) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (scratch_evalExpr_reveal_success_of evm' loopLocals false out))

theorem scratch_revealLoopBody_ok_noPlace (evm : EVM.State) (callargs : Store)
    (values fakes secrets : List Value) (len refund i value secret blinded deposit : UInt256)
    (fake : Bool) (fakeRaw : Value) (hashBytes : List UInt8)
    (hbids : callargs.get? "bids" = none)
    (hvalues : callargs.get? "values" = some (.array values))
    (hfakes : callargs.get? "fakes" = some (.array fakes))
    (hsecrets : callargs.get? "secrets" = some (.array secrets))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hboundBids : i.toNat < len.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool fake))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit)
    (hhash :
      evalExpr? blindAuctionConfig
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStore callargs evm len refund i value secret fake } evm
        scratch_revealPackedHashExpr =
        .ok (.fixedBytes ⟨31, by decide⟩ hashBytes))
    (heq : EVM.Word.toBytesBE blinded = hashBytes)
    (hfit : refund.toNat + deposit.toNat < UInt256.size)
    (hskipPlace : fake = true ∨ deposit.toNat < value.toNat) :
    ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_revealLoopStore callargs len refund i }
      evm scratch_revealLoopBodyStmts
      (.ok
        { contract := blindAuctionContract,
          locals := scratch_revealRefundAddedStore callargs evm len refund i value secret deposit fake }
        (scratch_revealZeroBlindedState evm i)) := by
  let L4 := scratch_revealSecretStore callargs evm len refund i value secret fake
  let L5 := scratch_revealRefundAddedStore callargs evm len refund i value secret deposit fake
  have hbidL4 :
      L4.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    simpa [L4] using
      scratch_revealSecretStore_bid_get callargs evm len refund i value secret fake
  have hguard :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
          (.keccak256 (.abiEncodePacked
            [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")]))) =
          .ok (.bool false) := by
    simpa [scratch_revealPackedHashExpr, L4] using
      scratch_evalExpr_reveal_hash_guard_false evm L4 i blinded hashBytes hbidL4 hblinded
        (by simpa [L4] using hhash) heq
  have hrefundL4 :
      L4.get? "refund" = some (.int (Int.ofNat refund.toNat)) := by
    simpa [L4] using
      scratch_revealSecretStore_refund_get callargs evm len refund i value secret fake
  have hadd :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))) =
          .ok (.int (Int.ofNat (refund.toNat + deposit.toNat))) :=
    scratch_evalExpr_reveal_refund_add_deposit evm L4 i refund deposit hbidL4 hrefundL4
      hdeposit hfit
  have hassignRefund :
      assignStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        .localVar { base := "refund" } (.int (Int.ofNat (refund.toNat + deposit.toNat))) =
          .ok ({ contract := blindAuctionContract, locals := L5 }, evm) := by
    simpa [L5, scratch_revealRefundAddedStore, L4] using
      scratch_assign_local_value evm L4 "refund" (.int (Int.ofNat refund.toNat))
        (.int (Int.ofNat (refund.toNat + deposit.toNat))) hrefundL4
  have hbidL5 :
      L5.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    simpa [L5] using
      scratch_revealRefundAddedStore_bid_get callargs evm len refund i value secret deposit fake
  have hvalueL5 :
      L5.get? "value" = some (.int (Int.ofNat value.toNat)) := by
    simpa [L5] using
      scratch_revealRefundAddedStore_value_get callargs evm len refund i value secret deposit fake
  have hcondFalse :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        (.binary .and (.unary .not (.var "fake"))
          (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value"))) =
          .ok (.bool false) := by
    cases fake with
    | false =>
        have hfakeL5 : L5.get? "fake" = some (.bool false) := by
          simpa [L5] using
            scratch_revealRefundAddedStore_fake_get callargs evm len refund i value secret deposit
              false
        rcases hskipPlace with hfakeTrue | hlt
        · cases hfakeTrue
        · exact scratch_evalExpr_reveal_placeBid_cond_false_deposit evm L5 i value deposit
            hbidL5 hfakeL5 hvalueL5 hdeposit hlt
    | true =>
        have hfakeL5 : L5.get? "fake" = some (.bool true) := by
          simpa [L5] using
            scratch_revealRefundAddedStore_fake_get callargs evm len refund i value secret deposit
              true
        exact scratch_evalExpr_reveal_placeBid_cond_false_fake evm L5 i value deposit
          hbidL5 hfakeL5 hvalueL5 hdeposit
  have hzero :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        (.cast (.intLit 0) bytes32St) =
          .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (EVM.Word.ofNat 0))) :=
    scratch_evalExpr_reveal_cast_zero_bytes32 evm L5
  have hassignZero :
      assignStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        .storage (aliasF "bidToCheck" "blindedBid")
        (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (EVM.Word.ofNat 0))) =
          .ok ({ contract := blindAuctionContract, locals := L5 },
            scratch_revealZeroBlindedState evm i) :=
    scratch_assign_reveal_blinded_zero evm L5 i hbidL5
  have htail :
      ExecBlock blindAuctionConfig
        { contract := blindAuctionContract, locals := L4 } evm
        (List.drop 4 scratch_revealLoopBodyStmts)
        (.ok { contract := blindAuctionContract, locals := L5 }
          (scratch_revealZeroBlindedState evm i)) := by
    change ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := L4 } evm
      [ .ite
          (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
            (.keccak256 (.abiEncodePacked
              [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
          [.continue] [],
        .assign .localVar { base := "refund" }
          (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
        .ite
          (.binary .and (.unary .not (.var "fake"))
            (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
          [ .internalCall "placeBid" [sender, .var "value"] "ok",
            .ite (.var "ok")
              [ .assign .localVar { base := "refund" }
                  (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
        .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]
      (.ok { contract := blindAuctionContract, locals := L5 }
        (scratch_revealZeroBlindedState evm i))
    refine ExecBlock.consNormal (ExecStmt.iteFalse hguard ExecBlock.nil) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hadd hassignRefund) ?_
    refine ExecBlock.consNormal (ExecStmt.iteFalse hcondFalse ExecBlock.nil) ?_
    exact ExecBlock.consNormal (ExecStmt.assign hzero hassignZero) ExecBlock.nil
  exact scratch_revealLoopBody_prefix_exec evm callargs values fakes secrets len refund i value
    secret fake fakeRaw hbids hvalues hfakes hsecrets hlen hboundBids hboundValues
    hboundFakes hboundSecrets hvalueLookup hfakeLookup hfakeNorm hsecretLookup htail

theorem scratch_revealLoopBody_ok_placeBid_false (evm : EVM.State) (callargs : Store)
    (values fakes secrets : List Value) (len refund i value secret blinded deposit high : UInt256)
    (fakeRaw : Value) (hashBytes : List UInt8)
    (hbids : callargs.get? "bids" = none)
    (hvalues : callargs.get? "values" = some (.array values))
    (hfakes : callargs.get? "fakes" = some (.array fakes))
    (hsecrets : callargs.get? "secrets" = some (.array secrets))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hboundBids : i.toNat < len.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool false))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit)
    (hhigh : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩ = high)
    (hhash :
      evalExpr? blindAuctionConfig
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStore callargs evm len refund i value secret false } evm
        scratch_revealPackedHashExpr =
        .ok (.fixedBytes ⟨31, by decide⟩ hashBytes))
    (heq : EVM.Word.toBytesBE blinded = hashBytes)
    (hfit : refund.toNat + deposit.toNat < UInt256.size)
    (hdepositGe : value.toNat ≤ deposit.toNat)
    (hplaceFalse : value.toNat ≤ high.toNat) :
    ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_revealLoopStore callargs len refund i }
      evm scratch_revealLoopBodyStmts
      (.ok
        { contract := blindAuctionContract,
          locals :=
            (scratch_revealRefundAddedStore callargs evm len refund i value secret deposit false)
              |>.insert "ok" (.bool false) }
        (scratch_revealZeroBlindedState evm i)) := by
  let L4 := scratch_revealSecretStore callargs evm len refund i value secret false
  let L5 := scratch_revealRefundAddedStore callargs evm len refund i value secret deposit false
  let L6 := L5.insert "ok" (.bool false)
  have hbidL4 :
      L4.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    simpa [L4] using
      scratch_revealSecretStore_bid_get callargs evm len refund i value secret false
  have hguard :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
          (.keccak256 (.abiEncodePacked
            [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")]))) =
          .ok (.bool false) := by
    simpa [scratch_revealPackedHashExpr, L4] using
      scratch_evalExpr_reveal_hash_guard_false evm L4 i blinded hashBytes hbidL4 hblinded
        (by simpa [L4] using hhash) heq
  have hrefundL4 :
      L4.get? "refund" = some (.int (Int.ofNat refund.toNat)) := by
    simpa [L4] using
      scratch_revealSecretStore_refund_get callargs evm len refund i value secret false
  have hadd :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))) =
          .ok (.int (Int.ofNat (refund.toNat + deposit.toNat))) :=
    scratch_evalExpr_reveal_refund_add_deposit evm L4 i refund deposit hbidL4 hrefundL4
      hdeposit hfit
  have hassignRefund :
      assignStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        .localVar { base := "refund" } (.int (Int.ofNat (refund.toNat + deposit.toNat))) =
          .ok ({ contract := blindAuctionContract, locals := L5 }, evm) := by
    simpa [L5, scratch_revealRefundAddedStore, L4] using
      scratch_assign_local_value evm L4 "refund" (.int (Int.ofNat refund.toNat))
        (.int (Int.ofNat (refund.toNat + deposit.toNat))) hrefundL4
  have hbidL5 :
      L5.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    simpa [L5] using
      scratch_revealRefundAddedStore_bid_get callargs evm len refund i value secret deposit false
  have hvalueL5 :
      L5.get? "value" = some (.int (Int.ofNat value.toNat)) := by
    simpa [L5] using
      scratch_revealRefundAddedStore_value_get callargs evm len refund i value secret deposit false
  have hfakeL5 : L5.get? "fake" = some (.bool false) := by
    simpa [L5] using
      scratch_revealRefundAddedStore_fake_get callargs evm len refund i value secret deposit false
  have hcondTrue :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        (.binary .and (.unary .not (.var "fake"))
          (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value"))) =
          .ok (.bool true) :=
    scratch_evalExpr_reveal_placeBid_cond_true evm L5 i value deposit hbidL5 hfakeL5
      hvalueL5 hdeposit hdepositGe
  have hcall :
      ExecStmt blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        (.internalCall "placeBid" [sender, .var "value"] "ok")
        (.ok { contract := blindAuctionContract, locals := L6 } evm) := by
    let calleeFrame : Frame :=
      { contract := blindAuctionContract,
        locals := scratch_placeBidStore evm.executionEnv.source value }
    simpa [L6] using
      ExecStmt.internalCallReturn
        (cfg := blindAuctionConfig)
        (solm := { contract := blindAuctionContract, locals := L5 })
        (evm := evm)
        (name := "placeBid") (retVar := "ok")
        (args := [sender, .var "value"])
        (argVals := [.address evm.executionEnv.source, .int (Int.ofNat value.toNat)])
        (callee := placeBidFn.toCallable)
        (locals := scratch_placeBidStore evm.executionEnv.source value)
        (calleeSolm := calleeFrame)
        (calleeEvm := evm)
        (value := some (.bool false))
        (scratch_evalExprs_reveal_placeBid_args evm L5 value hvalueL5)
        scratch_placeBid_lookup
        (by simpa [FunctionDecl.toCallable] using
          scratch_placeBid_bind evm.executionEnv.source value)
        (by
          simpa [ExecTransitionBody, FunctionDecl.toCallable, calleeFrame] using
            (scratch_blindAuctionPlaceBidBodyReturns_false evm evm.executionEnv.source value high
              hhigh hplaceFalse))
  have hokFalse :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L6 } evm
        (.var "ok") = .ok (.bool false) := by
    exact evalExpr_reveal_var_value evm L6 "ok" (.bool false) (by simp [L6])
  have hbidL6 :
      L6.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    simpa [L6, Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using hbidL5
  have hzero :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L6 } evm
        (.cast (.intLit 0) bytes32St) =
          .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (EVM.Word.ofNat 0))) :=
    scratch_evalExpr_reveal_cast_zero_bytes32 evm L6
  have hassignZero :
      assignStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := L6 } evm
        .storage (aliasF "bidToCheck" "blindedBid")
        (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (EVM.Word.ofNat 0))) =
          .ok ({ contract := blindAuctionContract, locals := L6 },
            scratch_revealZeroBlindedState evm i) :=
    scratch_assign_reveal_blinded_zero evm L6 i hbidL6
  have hplaceThen :
      ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        [ .internalCall "placeBid" [sender, .var "value"] "ok",
          .ite (.var "ok")
            [ .assign .localVar { base := "refund" }
                (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ]
        (.ok { contract := blindAuctionContract, locals := L6 } evm) := by
    refine ExecBlock.consNormal hcall ?_
    exact ExecBlock.consNormal (ExecStmt.iteFalse hokFalse ExecBlock.nil) ExecBlock.nil
  have hplaceIte :
      ExecStmt blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        (.ite
          (.binary .and (.unary .not (.var "fake"))
            (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
          [ .internalCall "placeBid" [sender, .var "value"] "ok",
            .ite (.var "ok")
              [ .assign .localVar { base := "refund" }
                  (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [])
        (.ok { contract := blindAuctionContract, locals := L6 } evm) :=
    ExecStmt.iteTrue hcondTrue hplaceThen
  have htail :
      ExecBlock blindAuctionConfig
        { contract := blindAuctionContract, locals := L4 } evm
        (List.drop 4 scratch_revealLoopBodyStmts)
        (.ok { contract := blindAuctionContract, locals := L6 }
          (scratch_revealZeroBlindedState evm i)) := by
    change ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := L4 } evm
      [ .ite
          (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
            (.keccak256 (.abiEncodePacked
              [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
          [.continue] [],
        .assign .localVar { base := "refund" }
          (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
        .ite
          (.binary .and (.unary .not (.var "fake"))
            (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
          [ .internalCall "placeBid" [sender, .var "value"] "ok",
            .ite (.var "ok")
              [ .assign .localVar { base := "refund" }
                  (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
        .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]
      (.ok { contract := blindAuctionContract, locals := L6 }
        (scratch_revealZeroBlindedState evm i))
    refine ExecBlock.consNormal (ExecStmt.iteFalse hguard ExecBlock.nil) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hadd hassignRefund) ?_
    refine ExecBlock.consNormal (solm' := { contract := blindAuctionContract, locals := L6 })
      (evm' := evm) hplaceIte ?_
    exact ExecBlock.consNormal (ExecStmt.assign hzero hassignZero) ExecBlock.nil
  simpa [L6] using
    scratch_revealLoopBody_prefix_exec evm callargs values fakes secrets len refund i value
      secret false fakeRaw hbids hvalues hfakes hsecrets hlen hboundBids hboundValues
      hboundFakes hboundSecrets hvalueLookup hfakeLookup hfakeNorm hsecretLookup htail

theorem scratch_revealLoopBody_ok_placeBid_true_core (evm evmPB : EVM.State) (callargs : Store)
    (values fakes secrets : List Value) (len refund i value secret blinded deposit : UInt256)
    (fakeRaw : Value) (hashBytes : List UInt8)
    (hbids : callargs.get? "bids" = none)
    (hvalues : callargs.get? "values" = some (.array values))
    (hfakes : callargs.get? "fakes" = some (.array fakes))
    (hsecrets : callargs.get? "secrets" = some (.array secrets))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hboundBids : i.toNat < len.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool false))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit)
    (hhash :
      evalExpr? blindAuctionConfig
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStore callargs evm len refund i value secret false } evm
        scratch_revealPackedHashExpr =
        .ok (.fixedBytes ⟨31, by decide⟩ hashBytes))
    (heq : EVM.Word.toBytesBE blinded = hashBytes)
    (hfit : refund.toNat + deposit.toNat < UInt256.size)
    (hdepositGe : value.toNat ≤ deposit.toNat)
    (hplaceBody :
      ExecTransitionBody blindAuctionConfig blindAuctionContract evm
        (scratch_placeBidStore evm.executionEnv.source value) placeBidFn.body
        (.returned
          { contract := blindAuctionContract,
            locals := scratch_placeBidStore evm.executionEnv.source value }
          evmPB (some (.bool true))))
    (href : scratch_revealBidEvaledRef evmPB i = scratch_revealBidEvaledRef evm i) :
    ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_revealLoopStore callargs len refund i }
      evm scratch_revealLoopBodyStmts
      (.ok
        { contract := blindAuctionContract,
          locals := scratch_revealRefundPlacedStore callargs evm len refund i value secret deposit }
        (scratch_revealZeroBlindedState evmPB i)) := by
  let L4 := scratch_revealSecretStore callargs evm len refund i value secret false
  let L5 := scratch_revealRefundAddedStore callargs evm len refund i value secret deposit false
  let L6 := L5.insert "ok" (.bool true)
  let refundAdded : UInt256 := UInt256.ofNat (refund.toNat + deposit.toNat)
  let L7 := L6.insert "refund" (.int (Int.ofNat (refundAdded.toNat - value.toNat)))
  have hrefundAddedToNat : refundAdded.toNat = refund.toNat + deposit.toNat := by
    simpa [refundAdded] using ulit_toNat' (refund.toNat + deposit.toNat) hfit
  have hbidL4 :
      L4.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    simpa [L4] using
      scratch_revealSecretStore_bid_get callargs evm len refund i value secret false
  have hguard :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
          (.keccak256 (.abiEncodePacked
            [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")]))) =
          .ok (.bool false) := by
    simpa [scratch_revealPackedHashExpr, L4] using
      scratch_evalExpr_reveal_hash_guard_false evm L4 i blinded hashBytes hbidL4 hblinded
        (by simpa [L4] using hhash) heq
  have hrefundL4 :
      L4.get? "refund" = some (.int (Int.ofNat refund.toNat)) := by
    simpa [L4] using
      scratch_revealSecretStore_refund_get callargs evm len refund i value secret false
  have hadd :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))) =
          .ok (.int (Int.ofNat (refund.toNat + deposit.toNat))) :=
    scratch_evalExpr_reveal_refund_add_deposit evm L4 i refund deposit hbidL4 hrefundL4
      hdeposit hfit
  have hassignRefund :
      assignStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        .localVar { base := "refund" } (.int (Int.ofNat (refund.toNat + deposit.toNat))) =
          .ok ({ contract := blindAuctionContract, locals := L5 }, evm) := by
    simpa [L5, scratch_revealRefundAddedStore, L4] using
      scratch_assign_local_value evm L4 "refund" (.int (Int.ofNat refund.toNat))
        (.int (Int.ofNat (refund.toNat + deposit.toNat))) hrefundL4
  have hbidL5 :
      L5.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    simpa [L5] using
      scratch_revealRefundAddedStore_bid_get callargs evm len refund i value secret deposit false
  have hvalueL5 :
      L5.get? "value" = some (.int (Int.ofNat value.toNat)) := by
    simpa [L5] using
      scratch_revealRefundAddedStore_value_get callargs evm len refund i value secret deposit false
  have hfakeL5 : L5.get? "fake" = some (.bool false) := by
    simpa [L5] using
      scratch_revealRefundAddedStore_fake_get callargs evm len refund i value secret deposit false
  have hcondTrue :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        (.binary .and (.unary .not (.var "fake"))
          (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value"))) =
          .ok (.bool true) :=
    scratch_evalExpr_reveal_placeBid_cond_true evm L5 i value deposit hbidL5 hfakeL5
      hvalueL5 hdeposit hdepositGe
  have hcall :
      ExecStmt blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        (.internalCall "placeBid" [sender, .var "value"] "ok")
        (.ok { contract := blindAuctionContract, locals := L6 } evmPB) := by
    let calleeFrame : Frame :=
      { contract := blindAuctionContract,
        locals := scratch_placeBidStore evm.executionEnv.source value }
    simpa [L6] using
      ExecStmt.internalCallReturn
        (cfg := blindAuctionConfig)
        (solm := { contract := blindAuctionContract, locals := L5 })
        (evm := evm)
        (name := "placeBid") (retVar := "ok")
        (args := [sender, .var "value"])
        (argVals := [.address evm.executionEnv.source, .int (Int.ofNat value.toNat)])
        (callee := placeBidFn.toCallable)
        (locals := scratch_placeBidStore evm.executionEnv.source value)
        (calleeSolm := calleeFrame)
        (calleeEvm := evmPB)
        (value := some (.bool true))
        (scratch_evalExprs_reveal_placeBid_args evm L5 value hvalueL5)
        scratch_placeBid_lookup
        (by simpa [FunctionDecl.toCallable] using
          scratch_placeBid_bind evm.executionEnv.source value)
        (by simpa [ExecTransitionBody, FunctionDecl.toCallable, calleeFrame] using hplaceBody)
  have hokTrue :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L6 } evmPB
        (.var "ok") = .ok (.bool true) := by
    exact evalExpr_reveal_var_value evmPB L6 "ok" (.bool true) (by simp [L6])
  have hrefundL6 :
      L6.get? "refund" = some (.int (Int.ofNat refundAdded.toNat)) := by
    simpa [L6, refundAdded, hrefundAddedToNat, Std.HashMap.getElem?_insert,
      Std.HashMap.get?_eq_getElem?] using
        scratch_revealRefundAddedStore_refund_get callargs evm len refund i value secret deposit false
  have hvalueL6 :
      L6.get? "value" = some (.int (Int.ofNat value.toNat)) := by
    simpa [L6, Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using hvalueL5
  have hsubLe : value.toNat ≤ refundAdded.toNat := by
    rw [hrefundAddedToNat]
    omega
  have hsub :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L6 } evmPB
        (u256 (.binary .sub (.var "refund") (.var "value"))) =
          .ok (.int (Int.ofNat (refundAdded.toNat - value.toNat))) :=
    scratch_evalExpr_reveal_refund_sub_value evmPB L6 refundAdded value hrefundL6 hvalueL6
      hsubLe
  have hassignSub :
      assignStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := L6 } evmPB
        .localVar { base := "refund" } (.int (Int.ofNat (refundAdded.toNat - value.toNat))) =
          .ok ({ contract := blindAuctionContract, locals := L7 }, evmPB) := by
    simpa [L7] using
      scratch_assign_local_value evmPB L6 "refund" (.int (Int.ofNat refundAdded.toNat))
        (.int (Int.ofNat (refundAdded.toNat - value.toNat))) hrefundL6
  have hbidL7 :
      L7.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evmPB i) bidStructTy) := by
    have hbidOrig :
        L7.get? "bidToCheck" =
          some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
      simpa [L7, L6, Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using hbidL5
    simpa [href] using hbidOrig
  have hzero :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L7 } evmPB
        (.cast (.intLit 0) bytes32St) =
          .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (EVM.Word.ofNat 0))) :=
    scratch_evalExpr_reveal_cast_zero_bytes32 evmPB L7
  have hassignZero :
      assignStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := L7 } evmPB
        .storage (aliasF "bidToCheck" "blindedBid")
        (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (EVM.Word.ofNat 0))) =
          .ok ({ contract := blindAuctionContract, locals := L7 },
            scratch_revealZeroBlindedState evmPB i) :=
    scratch_assign_reveal_blinded_zero evmPB L7 i hbidL7
  have hthenOk :
      ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L6 } evmPB
        [ .assign .localVar { base := "refund" }
            (u256 (.binary .sub (.var "refund") (.var "value"))) ]
        (.ok { contract := blindAuctionContract, locals := L7 } evmPB) := by
    exact ExecBlock.consNormal (ExecStmt.assign hsub hassignSub) ExecBlock.nil
  have hokIte :
      ExecStmt blindAuctionConfig { contract := blindAuctionContract, locals := L6 } evmPB
        (.ite (.var "ok")
          [ .assign .localVar { base := "refund" }
              (u256 (.binary .sub (.var "refund") (.var "value"))) ] [])
        (.ok { contract := blindAuctionContract, locals := L7 } evmPB) :=
    ExecStmt.iteTrue hokTrue hthenOk
  have hplaceThen :
      ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        [ .internalCall "placeBid" [sender, .var "value"] "ok",
          .ite (.var "ok")
            [ .assign .localVar { base := "refund" }
                (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ]
        (.ok { contract := blindAuctionContract, locals := L7 } evmPB) := by
    refine ExecBlock.consNormal (solm' := { contract := blindAuctionContract, locals := L6 })
      (evm' := evmPB) hcall ?_
    exact ExecBlock.consNormal hokIte ExecBlock.nil
  have hplaceIte :
      ExecStmt blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        (.ite
          (.binary .and (.unary .not (.var "fake"))
            (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
          [ .internalCall "placeBid" [sender, .var "value"] "ok",
            .ite (.var "ok")
              [ .assign .localVar { base := "refund" }
                  (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [])
        (.ok { contract := blindAuctionContract, locals := L7 } evmPB) :=
    ExecStmt.iteTrue hcondTrue hplaceThen
  have htail :
      ExecBlock blindAuctionConfig
        { contract := blindAuctionContract, locals := L4 } evm
        (List.drop 4 scratch_revealLoopBodyStmts)
        (.ok { contract := blindAuctionContract, locals := L7 }
          (scratch_revealZeroBlindedState evmPB i)) := by
    change ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := L4 } evm
      [ .ite
          (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
            (.keccak256 (.abiEncodePacked
              [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
          [.continue] [],
        .assign .localVar { base := "refund" }
          (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
        .ite
          (.binary .and (.unary .not (.var "fake"))
            (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
          [ .internalCall "placeBid" [sender, .var "value"] "ok",
            .ite (.var "ok")
              [ .assign .localVar { base := "refund" }
                  (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
        .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]
      (.ok { contract := blindAuctionContract, locals := L7 }
        (scratch_revealZeroBlindedState evmPB i))
    refine ExecBlock.consNormal (ExecStmt.iteFalse hguard ExecBlock.nil) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hadd hassignRefund) ?_
    refine ExecBlock.consNormal (solm' := { contract := blindAuctionContract, locals := L7 })
      (evm' := evmPB) hplaceIte ?_
    exact ExecBlock.consNormal (ExecStmt.assign hzero hassignZero) ExecBlock.nil
  simpa [scratch_revealRefundPlacedStore, L7, L6, L5, refundAdded, hrefundAddedToNat] using
    scratch_revealLoopBody_prefix_exec evm callargs values fakes secrets len refund i value
      secret false fakeRaw hbids hvalues hfakes hsecrets hlen hboundBids hboundValues
      hboundFakes hboundSecrets hvalueLookup hfakeLookup hfakeNorm hsecretLookup htail

theorem scratch_revealLoopBody_ok_placeBid_true_zero (evm : EVM.State) (callargs : Store)
    (values fakes secrets : List Value) (len refund i value secret blinded deposit high old : UInt256)
    (fakeRaw : Value) (hashBytes : List UInt8)
    (hbids : callargs.get? "bids" = none)
    (hvalues : callargs.get? "values" = some (.array values))
    (hfakes : callargs.get? "fakes" = some (.array fakes))
    (hsecrets : callargs.get? "secrets" = some (.array secrets))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hboundBids : i.toNat < len.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool false))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit)
    (hhigh : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩ = high)
    (hold : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = old)
    (hhash :
      evalExpr? blindAuctionConfig
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStore callargs evm len refund i value secret false } evm
        scratch_revealPackedHashExpr =
        .ok (.fixedBytes ⟨31, by decide⟩ hashBytes))
    (heq : EVM.Word.toBytesBE blinded = hashBytes)
    (hfit : refund.toNat + deposit.toNat < UInt256.size)
    (hdepositGe : value.toNat ≤ deposit.toNat)
    (hlt : high.toNat < value.toNat)
    (hzero : UInt256.land old solcAddrMask = ⟨0⟩) :
    ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_revealLoopStore callargs len refund i }
      evm scratch_revealLoopBodyStmts
      (.ok
        { contract := blindAuctionContract,
          locals := scratch_revealRefundPlacedStore callargs evm len refund i value secret deposit }
        (scratch_revealZeroBlindedState
          (scratch_placeBidAfterBidder (scratch_placeBidAfterHigh evm value)
            evm.executionEnv.source) i)) := by
  let evmPB :=
    scratch_placeBidAfterBidder (scratch_placeBidAfterHigh evm value) evm.executionEnv.source
  refine scratch_revealLoopBody_ok_placeBid_true_core evm evmPB callargs values fakes secrets
    len refund i value secret blinded deposit fakeRaw hashBytes hbids hvalues hfakes hsecrets
    hlen hboundBids hboundValues hboundFakes hboundSecrets hvalueLookup hfakeLookup hfakeNorm
    hsecretLookup hblinded hdeposit hhash heq hfit hdepositGe ?_ ?_
  · simpa [evmPB] using
      scratch_blindAuctionPlaceBidBodyReturns_true_zero evm evm.executionEnv.source value high old
        hhigh hold hlt hzero
  · simp [evmPB, scratch_placeBidAfterBidder, scratch_placeBidAfterHigh,
      scratch_revealBidEvaledRef_storageStore]

theorem scratch_revealLoopBody_ok_placeBid_true_nonzero (evm : EVM.State) (callargs : Store)
    (values fakes secrets : List Value)
    (len refund i value secret blinded deposit high old pending : UInt256)
    (oldAddr : AccountAddress) (fakeRaw : Value) (hashBytes : List UInt8)
    (hbids : callargs.get? "bids" = none)
    (hvalues : callargs.get? "values" = some (.array values))
    (hfakes : callargs.get? "fakes" = some (.array fakes))
    (hsecrets : callargs.get? "secrets" = some (.array secrets))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hboundBids : i.toNat < len.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool false))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit)
    (hhigh : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩ = high)
    (hold : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = old)
    (holdAddr : oldAddr = AccountAddress.ofNat (UInt256.land old solcAddrMask).toNat)
    (hpending : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (pendingReturnsSlot (.address oldAddr)) = pending)
    (hhash :
      evalExpr? blindAuctionConfig
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStore callargs evm len refund i value secret false } evm
        scratch_revealPackedHashExpr =
        .ok (.fixedBytes ⟨31, by decide⟩ hashBytes))
    (heq : EVM.Word.toBytesBE blinded = hashBytes)
    (hfit : refund.toNat + deposit.toNat < UInt256.size)
    (hdepositGe : value.toNat ≤ deposit.toNat)
    (hlt : high.toNat < value.toNat)
    (hnonzero : UInt256.land old solcAddrMask ≠ ⟨0⟩)
    (hsum : pending.toNat + high.toNat < UInt256.size) :
    ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_revealLoopStore callargs len refund i }
      evm scratch_revealLoopBodyStmts
      (.ok
        { contract := blindAuctionContract,
          locals := scratch_revealRefundPlacedStore callargs evm len refund i value secret deposit }
        (scratch_revealZeroBlindedState
          (scratch_placeBidAfterBidder
            (scratch_placeBidAfterHigh
              (scratch_placeBidAfterPending evm oldAddr
                (UInt256.ofNat (pending.toNat + high.toNat))) value)
            evm.executionEnv.source) i)) := by
  let evmPB :=
    scratch_placeBidAfterBidder
      (scratch_placeBidAfterHigh
        (scratch_placeBidAfterPending evm oldAddr
          (UInt256.ofNat (pending.toNat + high.toNat))) value)
      evm.executionEnv.source
  refine scratch_revealLoopBody_ok_placeBid_true_core evm evmPB callargs values fakes secrets
    len refund i value secret blinded deposit fakeRaw hashBytes hbids hvalues hfakes hsecrets
    hlen hboundBids hboundValues hboundFakes hboundSecrets hvalueLookup hfakeLookup hfakeNorm
    hsecretLookup hblinded hdeposit hhash heq hfit hdepositGe ?_ ?_
  · simpa [evmPB] using
      scratch_blindAuctionPlaceBidBodyReturns_true_nonzero evm evm.executionEnv.source oldAddr
        value high old pending hhigh hold holdAddr hpending hlt hnonzero hsum
  · simp [evmPB, scratch_placeBidAfterBidder, scratch_placeBidAfterHigh,
      scratch_placeBidAfterPending, scratch_revealBidEvaledRef_storageStore]

/-! ### Generic source loop body facts over arbitrary locals -/

def scratch_revealBidToCheckStoreOf (locals : Store) (evm : EVM.State)
    (i : UInt256) : Store :=
  locals.insert "bidToCheck" (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy)

def scratch_revealValueStoreOf (locals : Store) (evm : EVM.State)
    (i value : UInt256) : Store :=
  (scratch_revealBidToCheckStoreOf locals evm i).insert "value"
    (.int (Int.ofNat value.toNat))

def scratch_revealFakeStoreOf (locals : Store) (evm : EVM.State)
    (i value : UInt256) (fake : Bool) : Store :=
  (scratch_revealValueStoreOf locals evm i value).insert "fake" (.bool fake)

def scratch_revealSecretStoreOf (locals : Store) (evm : EVM.State)
    (i value secret : UInt256) (fake : Bool) : Store :=
  (scratch_revealFakeStoreOf locals evm i value fake).insert "secret"
    (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret))

def scratch_revealRefundAddedStoreOf (locals : Store) (evm : EVM.State)
    (i refund value secret deposit : UInt256) (fake : Bool) : Store :=
  (scratch_revealSecretStoreOf locals evm i value secret fake).insert "refund"
    (.int (Int.ofNat (refund.toNat + deposit.toNat)))

def scratch_revealRefundPlacedStoreOf (locals : Store) (evm : EVM.State)
    (i refund value secret deposit : UInt256) : Store :=
  ((scratch_revealRefundAddedStoreOf locals evm i refund value secret deposit false).insert
      "ok" (.bool true)).insert "refund"
    (.int (Int.ofNat (refund.toNat + deposit.toNat - value.toNat)))

theorem scratch_revealBidToCheckStoreOf_bid_get (locals : Store) (evm : EVM.State)
    (i : UInt256) :
    (scratch_revealBidToCheckStoreOf locals evm i).get? "bidToCheck" =
      some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
  unfold scratch_revealBidToCheckStoreOf
  rw [store_get_self]

theorem scratch_evalStorageRef_reveal_bid_ok_of_get (evm : EVM.State) (locals : Store)
    (i len : UInt256)
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hbound : i.toNat < len.toNat) :
    evalStorageRef blindAuctionConfig
      { contract := blindAuctionContract, locals := locals }
      evm (bidElemRef sender (.var "i")) =
        .ok (scratch_revealBidEvaledRef evm i) := by
  have hbounds := scratch_revealBid_arrayIndexInBounds_ok evm i len hlen hbound
  simp only [bidElemRef, sender, evalStorageRef, evalStorageRefSteps.eq_def,
    evalStorageRefStep.eq_def, evalExpr?, envValue, valueToKey?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, List.nil_append, scratch_revealBidEvaledRef, hi]
  rw [hbounds]

theorem scratch_resolveStorageRef_reveal_bid_ok_of_get (evm : EVM.State) (locals : Store)
    (i len : UInt256)
    (hbids : locals.get? "bids" = none)
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hbound : i.toNat < len.toNat) :
    resolveStorageRef? blindAuctionConfig
      { contract := blindAuctionContract, locals := locals }
      evm (bidElemRef sender (.var "i")) =
        .ok (scratch_revealBidEvaledRef evm i, bidStructTy) := by
  exact resolveStorageRef?_ok hbids
    (scratch_evalStorageRef_reveal_bid_ok_of_get evm locals i len hi hlen hbound)
    (scratch_revealBid_storageType evm i)

theorem scratch_letStorage_reveal_bidToCheck_of_get (evm : EVM.State) (locals : Store)
    (i len : UInt256)
    (hbids : locals.get? "bids" = none)
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hbound : i.toNat < len.toNat) :
    ExecStmt blindAuctionConfig
      { contract := blindAuctionContract, locals := locals }
      evm (.letStorage "bidToCheck" (bidElemRef sender (.var "i")))
      (.ok
        { contract := blindAuctionContract,
          locals := scratch_revealBidToCheckStoreOf locals evm i }
        evm) := by
  exact ExecStmt.letStorage
    (scratch_resolveStorageRef_reveal_bid_ok_of_get evm locals i len hbids hi hlen hbound)

theorem scratch_revealSecretStoreOf_bid_get (locals : Store) (evm : EVM.State)
    (i value secret : UInt256) (fake : Bool) :
    (scratch_revealSecretStoreOf locals evm i value secret fake).get? "bidToCheck" =
      some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
  unfold scratch_revealSecretStoreOf scratch_revealFakeStoreOf scratch_revealValueStoreOf
    scratch_revealBidToCheckStoreOf
  rw [store_get_ne, store_get_ne, store_get_ne, store_get_self]
  · decide
  · decide
  · decide

theorem scratch_revealSecretStoreOf_value_get (locals : Store) (evm : EVM.State)
    (i value secret : UInt256) (fake : Bool) :
    (scratch_revealSecretStoreOf locals evm i value secret fake).get? "value" =
      some (.int (Int.ofNat value.toNat)) := by
  unfold scratch_revealSecretStoreOf scratch_revealFakeStoreOf scratch_revealValueStoreOf
  rw [store_get_ne, store_get_ne, store_get_self]
  · decide
  · decide

theorem scratch_revealSecretStoreOf_fake_get (locals : Store) (evm : EVM.State)
    (i value secret : UInt256) (fake : Bool) :
    (scratch_revealSecretStoreOf locals evm i value secret fake).get? "fake" =
      some (.bool fake) := by
  unfold scratch_revealSecretStoreOf scratch_revealFakeStoreOf
  rw [store_get_ne, store_get_self]
  decide

theorem scratch_revealSecretStoreOf_refund_get (locals : Store) (evm : EVM.State)
    (i refund value secret : UInt256) (fake : Bool)
    (hrefund : locals.get? "refund" = some (.int (Int.ofNat refund.toNat))) :
    (scratch_revealSecretStoreOf locals evm i value secret fake).get? "refund" =
      some (.int (Int.ofNat refund.toNat)) := by
  unfold scratch_revealSecretStoreOf scratch_revealFakeStoreOf scratch_revealValueStoreOf
    scratch_revealBidToCheckStoreOf
  rw [store_get_ne, store_get_ne, store_get_ne, store_get_ne]
  · exact hrefund
  · decide
  · decide
  · decide
  · decide

theorem scratch_revealRefundAddedStoreOf_bid_get (locals : Store) (evm : EVM.State)
    (i refund value secret deposit : UInt256) (fake : Bool) :
    (scratch_revealRefundAddedStoreOf locals evm i refund value secret deposit fake).get?
      "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
  unfold scratch_revealRefundAddedStoreOf
  rw [store_get_ne]
  · exact scratch_revealSecretStoreOf_bid_get locals evm i value secret fake
  · decide

theorem scratch_revealRefundAddedStoreOf_value_get (locals : Store) (evm : EVM.State)
    (i refund value secret deposit : UInt256) (fake : Bool) :
    (scratch_revealRefundAddedStoreOf locals evm i refund value secret deposit fake).get?
      "value" = some (.int (Int.ofNat value.toNat)) := by
  unfold scratch_revealRefundAddedStoreOf
  rw [store_get_ne]
  · exact scratch_revealSecretStoreOf_value_get locals evm i value secret fake
  · decide

theorem scratch_revealRefundAddedStoreOf_fake_get (locals : Store) (evm : EVM.State)
    (i refund value secret deposit : UInt256) (fake : Bool) :
    (scratch_revealRefundAddedStoreOf locals evm i refund value secret deposit fake).get?
      "fake" = some (.bool fake) := by
  unfold scratch_revealRefundAddedStoreOf
  rw [store_get_ne]
  · exact scratch_revealSecretStoreOf_fake_get locals evm i value secret fake
  · decide

theorem scratch_revealRefundAddedStoreOf_refund_get (locals : Store) (evm : EVM.State)
    (i refund value secret deposit : UInt256) (fake : Bool) :
    (scratch_revealRefundAddedStoreOf locals evm i refund value secret deposit fake).get?
      "refund" = some (.int (Int.ofNat (refund.toNat + deposit.toNat))) := by
  unfold scratch_revealRefundAddedStoreOf
  rw [store_get_self]

theorem scratch_revealLoopBody_prefix_exec_of_get (evm : EVM.State) (locals : Store)
    (values fakes secrets : List Value) (len refund i value secret : UInt256)
    (fake : Bool) (fakeRaw : Value) {result : ExecResult}
    (hbids : locals.get? "bids" = none)
    (hvalues : locals.get? "values" = some (.array values))
    (hfakes : locals.get? "fakes" = some (.array fakes))
    (hsecrets : locals.get? "secrets" = some (.array secrets))
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hboundBids : i.toNat < len.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool fake))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (htail :
      ExecBlock blindAuctionConfig
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStoreOf locals evm i value secret fake }
        evm (List.drop 4 scratch_revealLoopBodyStmts) result) :
    ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := locals }
      evm scratch_revealLoopBodyStmts result := by
  unfold scratch_revealLoopBodyStmts
  refine ExecBlock.consNormal
    (scratch_letStorage_reveal_bidToCheck_of_get evm locals i len hbids hi hlen hboundBids) ?_
  let L1 := scratch_revealBidToCheckStoreOf locals evm i
  let L2 := scratch_revealValueStoreOf locals evm i value
  let L3 := scratch_revealFakeStoreOf locals evm i value fake
  let L4 := scratch_revealSecretStoreOf locals evm i value secret fake
  have hvaluesL1 : L1.get? "values" = some (.array values) := by
    simpa [L1, scratch_revealBidToCheckStoreOf, Std.HashMap.getElem?_insert,
      Std.HashMap.get?_eq_getElem?] using hvalues
  have hiL1 : L1.get? "i" = some (.int (Int.ofNat i.toNat)) := by
    simpa [L1, scratch_revealBidToCheckStoreOf, Std.HashMap.getElem?_insert,
      Std.HashMap.get?_eq_getElem?] using hi
  have hvalueEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L1 } evm
        (.index (.var "values") (.var "i")) =
          .ok (.int (Int.ofNat value.toNat)) := by
    exact scratch_evalExpr_reveal_local_array_index_norm evm L1 "values" values i
      (.int (Int.ofNat value.toNat)) (.int (Int.ofNat value.toNat)) hvaluesL1 hiL1
      hboundValues hvalueLookup (by simp [normalizeRawBoolWord?])
  refine ExecBlock.consNormal (ExecStmt.letDecl hvalueEval) ?_
  have hfakesL2 : L2.get? "fakes" = some (.array fakes) := by
    simpa [L2, scratch_revealValueStoreOf, L1, scratch_revealBidToCheckStoreOf,
      Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using hfakes
  have hiL2 : L2.get? "i" = some (.int (Int.ofNat i.toNat)) := by
    simpa [L2, scratch_revealValueStoreOf, L1, scratch_revealBidToCheckStoreOf,
      Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using hi
  have hfakeEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L2 } evm
        (.index (.var "fakes") (.var "i")) = .ok (.bool fake) := by
    exact scratch_evalExpr_reveal_local_array_index_norm evm L2 "fakes" fakes i
      fakeRaw (.bool fake) hfakesL2 hiL2 hboundFakes hfakeLookup hfakeNorm
  refine ExecBlock.consNormal (ExecStmt.letDecl hfakeEval) ?_
  have hsecretsL3 : L3.get? "secrets" = some (.array secrets) := by
    simpa [L3, scratch_revealFakeStoreOf, scratch_revealValueStoreOf, L1,
      scratch_revealBidToCheckStoreOf, Std.HashMap.getElem?_insert,
      Std.HashMap.get?_eq_getElem?] using hsecrets
  have hiL3 : L3.get? "i" = some (.int (Int.ofNat i.toNat)) := by
    simpa [L3, scratch_revealFakeStoreOf, scratch_revealValueStoreOf, L1,
      scratch_revealBidToCheckStoreOf, Std.HashMap.getElem?_insert,
      Std.HashMap.get?_eq_getElem?] using hi
  have hsecretEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L3 } evm
        (.index (.var "secrets") (.var "i")) =
          .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)) := by
    exact scratch_evalExpr_reveal_local_array_index_norm evm L3 "secrets" secrets i
      (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret))
      (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret))
      hsecretsL3 hiL3 hboundSecrets hsecretLookup (by simp [normalizeRawBoolWord?])
  refine ExecBlock.consNormal (ExecStmt.letDecl hsecretEval) ?_
  simpa [L4, scratch_revealLoopBodyStmts] using htail

theorem scratch_revealLoopBody_revert_fake_invalid_of_get (evm : EVM.State)
    (locals : Store) (values fakes secrets : List Value) (len i value : UInt256)
    (fakeRaw : Value)
    (hbids : locals.get? "bids" = none)
    (hvalues : locals.get? "values" = some (.array values))
    (hfakes : locals.get? "fakes" = some (.array fakes))
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hboundBids : i.toNat < len.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .revert) :
    ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := locals }
      evm scratch_revealLoopBodyStmts .reverted := by
  unfold scratch_revealLoopBodyStmts
  refine ExecBlock.consNormal
    (scratch_letStorage_reveal_bidToCheck_of_get evm locals i len hbids hi hlen hboundBids) ?_
  let L1 := scratch_revealBidToCheckStoreOf locals evm i
  let L2 := scratch_revealValueStoreOf locals evm i value
  have hvaluesL1 : L1.get? "values" = some (.array values) := by
    simpa [L1, scratch_revealBidToCheckStoreOf, Std.HashMap.getElem?_insert,
      Std.HashMap.get?_eq_getElem?] using hvalues
  have hiL1 : L1.get? "i" = some (.int (Int.ofNat i.toNat)) := by
    simpa [L1, scratch_revealBidToCheckStoreOf, Std.HashMap.getElem?_insert,
      Std.HashMap.get?_eq_getElem?] using hi
  have hvalueEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L1 } evm
        (.index (.var "values") (.var "i")) =
          .ok (.int (Int.ofNat value.toNat)) := by
    exact scratch_evalExpr_reveal_local_array_index_norm evm L1 "values" values i
      (.int (Int.ofNat value.toNat)) (.int (Int.ofNat value.toNat)) hvaluesL1 hiL1
      hboundValues hvalueLookup (by simp [normalizeRawBoolWord?])
  refine ExecBlock.consNormal (ExecStmt.letDecl hvalueEval) ?_
  have hfakesL2 : L2.get? "fakes" = some (.array fakes) := by
    simpa [L2, scratch_revealValueStoreOf, L1, scratch_revealBidToCheckStoreOf,
      Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using hfakes
  have hiL2 : L2.get? "i" = some (.int (Int.ofNat i.toNat)) := by
    simpa [L2, scratch_revealValueStoreOf, L1, scratch_revealBidToCheckStoreOf,
      Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using hi
  have hfakeEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L2 } evm
        (.index (.var "fakes") (.var "i")) = .revert := by
    exact scratch_evalExpr_reveal_local_array_index_revert evm L2 "fakes" fakes i fakeRaw
      hfakesL2 hiL2 hboundFakes hfakeLookup hfakeNorm
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert hfakeEval)

theorem scratch_revealLoopBody_ok_noPlace_of_get (evm : EVM.State) (locals : Store)
    (values fakes secrets : List Value) (len refund i value secret blinded deposit : UInt256)
    (fake : Bool) (fakeRaw : Value) (hashBytes : List UInt8)
    (hbids : locals.get? "bids" = none)
    (hvalues : locals.get? "values" = some (.array values))
    (hfakes : locals.get? "fakes" = some (.array fakes))
    (hsecrets : locals.get? "secrets" = some (.array secrets))
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hrefund : locals.get? "refund" = some (.int (Int.ofNat refund.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hboundBids : i.toNat < len.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool fake))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit)
    (hhash :
      evalExpr? blindAuctionConfig
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStoreOf locals evm i value secret fake } evm
        scratch_revealPackedHashExpr =
        .ok (.fixedBytes ⟨31, by decide⟩ hashBytes))
    (heq : EVM.Word.toBytesBE blinded = hashBytes)
    (hfit : refund.toNat + deposit.toNat < UInt256.size)
    (hskipPlace : fake = true ∨ deposit.toNat < value.toNat) :
    ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := locals }
      evm scratch_revealLoopBodyStmts
      (.ok
        { contract := blindAuctionContract,
          locals := scratch_revealRefundAddedStoreOf locals evm i refund value secret deposit fake }
        (scratch_revealZeroBlindedState evm i)) := by
  let L4 := scratch_revealSecretStoreOf locals evm i value secret fake
  let L5 := scratch_revealRefundAddedStoreOf locals evm i refund value secret deposit fake
  have hbidL4 :
      L4.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    simpa [L4] using scratch_revealSecretStoreOf_bid_get locals evm i value secret fake
  have hguard :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
          (.keccak256 (.abiEncodePacked
            [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")]))) =
          .ok (.bool false) := by
    simpa [scratch_revealPackedHashExpr, L4] using
      scratch_evalExpr_reveal_hash_guard_false evm L4 i blinded hashBytes hbidL4 hblinded
        (by simpa [L4] using hhash) heq
  have hrefundL4 :
      L4.get? "refund" = some (.int (Int.ofNat refund.toNat)) := by
    simpa [L4] using
      scratch_revealSecretStoreOf_refund_get locals evm i refund value secret fake hrefund
  have hadd :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))) =
          .ok (.int (Int.ofNat (refund.toNat + deposit.toNat))) :=
    scratch_evalExpr_reveal_refund_add_deposit evm L4 i refund deposit hbidL4 hrefundL4
      hdeposit hfit
  have hassignRefund :
      assignStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        .localVar { base := "refund" } (.int (Int.ofNat (refund.toNat + deposit.toNat))) =
          .ok ({ contract := blindAuctionContract, locals := L5 }, evm) := by
    simpa [L5, scratch_revealRefundAddedStoreOf, L4] using
      scratch_assign_local_value evm L4 "refund" (.int (Int.ofNat refund.toNat))
        (.int (Int.ofNat (refund.toNat + deposit.toNat))) hrefundL4
  have hbidL5 :
      L5.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    simpa [L5] using
      scratch_revealRefundAddedStoreOf_bid_get locals evm i refund value secret deposit fake
  have hvalueL5 :
      L5.get? "value" = some (.int (Int.ofNat value.toNat)) := by
    simpa [L5] using
      scratch_revealRefundAddedStoreOf_value_get locals evm i refund value secret deposit fake
  have hcondFalse :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        (.binary .and (.unary .not (.var "fake"))
          (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value"))) =
          .ok (.bool false) := by
    cases fake with
    | false =>
        have hfakeL5 : L5.get? "fake" = some (.bool false) := by
          simpa [L5] using
            scratch_revealRefundAddedStoreOf_fake_get locals evm i refund value secret deposit
              false
        rcases hskipPlace with hfakeTrue | hlt
        · cases hfakeTrue
        · exact scratch_evalExpr_reveal_placeBid_cond_false_deposit evm L5 i value deposit
            hbidL5 hfakeL5 hvalueL5 hdeposit hlt
    | true =>
        have hfakeL5 : L5.get? "fake" = some (.bool true) := by
          simpa [L5] using
            scratch_revealRefundAddedStoreOf_fake_get locals evm i refund value secret deposit true
        exact scratch_evalExpr_reveal_placeBid_cond_false_fake evm L5 i value deposit
          hbidL5 hfakeL5 hvalueL5 hdeposit
  have hzero :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        (.cast (.intLit 0) bytes32St) =
          .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (EVM.Word.ofNat 0))) :=
    scratch_evalExpr_reveal_cast_zero_bytes32 evm L5
  have hassignZero :
      assignStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        .storage (aliasF "bidToCheck" "blindedBid")
        (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (EVM.Word.ofNat 0))) =
          .ok ({ contract := blindAuctionContract, locals := L5 },
            scratch_revealZeroBlindedState evm i) :=
    scratch_assign_reveal_blinded_zero evm L5 i hbidL5
  have htail :
      ExecBlock blindAuctionConfig
        { contract := blindAuctionContract, locals := L4 } evm
        (List.drop 4 scratch_revealLoopBodyStmts)
        (.ok { contract := blindAuctionContract, locals := L5 }
          (scratch_revealZeroBlindedState evm i)) := by
    change ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := L4 } evm
      [ .ite
          (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
            (.keccak256 (.abiEncodePacked
              [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
          [.continue] [],
        .assign .localVar { base := "refund" }
          (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
        .ite
          (.binary .and (.unary .not (.var "fake"))
            (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
          [ .internalCall "placeBid" [sender, .var "value"] "ok",
            .ite (.var "ok")
              [ .assign .localVar { base := "refund" }
                  (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
        .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]
      (.ok { contract := blindAuctionContract, locals := L5 }
        (scratch_revealZeroBlindedState evm i))
    refine ExecBlock.consNormal (ExecStmt.iteFalse hguard ExecBlock.nil) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hadd hassignRefund) ?_
    refine ExecBlock.consNormal (ExecStmt.iteFalse hcondFalse ExecBlock.nil) ?_
    exact ExecBlock.consNormal (ExecStmt.assign hzero hassignZero) ExecBlock.nil
  exact scratch_revealLoopBody_prefix_exec_of_get evm locals values fakes secrets len refund i
    value secret fake fakeRaw hbids hvalues hfakes hsecrets hi hlen hboundBids hboundValues
    hboundFakes hboundSecrets hvalueLookup hfakeLookup hfakeNorm hsecretLookup htail

theorem scratch_revealLoopBody_continue_hash_mismatch_of_get (evm : EVM.State)
    (locals : Store)
    (values fakes secrets : List Value) (len refund i value secret blinded : UInt256)
    (fake : Bool) (fakeRaw : Value) (hashBytes : List UInt8)
    (hbids : locals.get? "bids" = none)
    (hvalues : locals.get? "values" = some (.array values))
    (hfakes : locals.get? "fakes" = some (.array fakes))
    (hsecrets : locals.get? "secrets" = some (.array secrets))
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hboundBids : i.toNat < len.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool fake))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hhash :
      evalExpr? blindAuctionConfig
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStoreOf locals evm i value secret fake } evm
        scratch_revealPackedHashExpr =
        .ok (.fixedBytes ⟨31, by decide⟩ hashBytes))
    (hne : EVM.Word.toBytesBE blinded ≠ hashBytes) :
    ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := locals }
      evm scratch_revealLoopBodyStmts
      (.continue
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStoreOf locals evm i value secret fake }
        evm) := by
  let L4 := scratch_revealSecretStoreOf locals evm i value secret fake
  have hbidL4 :
      L4.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    simpa [L4] using scratch_revealSecretStoreOf_bid_get locals evm i value secret fake
  have hguard :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
          (.keccak256 (.abiEncodePacked
            [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")]))) =
          .ok (.bool true) := by
    simpa [scratch_revealPackedHashExpr, L4] using
      scratch_evalExpr_reveal_hash_guard_true evm L4 i blinded hashBytes hbidL4 hblinded
        (by simpa [L4] using hhash) hne
  have htail :
      ExecBlock blindAuctionConfig
        { contract := blindAuctionContract, locals := L4 } evm
        (List.drop 4 scratch_revealLoopBodyStmts)
        (.continue { contract := blindAuctionContract, locals := L4 } evm) := by
    change ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := L4 } evm
      [ .ite
          (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
            (.keccak256 (.abiEncodePacked
              [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
          [.continue] [],
        .assign .localVar { base := "refund" }
          (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
        .ite
          (.binary .and (.unary .not (.var "fake"))
            (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
          [ .internalCall "placeBid" [sender, .var "value"] "ok",
            .ite (.var "ok")
              [ .assign .localVar { base := "refund" }
                  (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
        .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]
      (.continue { contract := blindAuctionContract, locals := L4 } evm)
    refine ExecBlock.consContinue ?_
    refine ExecStmt.iteTrue hguard ?_
    exact ExecBlock.consContinue ExecStmt.continue
  exact scratch_revealLoopBody_prefix_exec_of_get evm locals values fakes secrets len refund i
    value secret fake fakeRaw hbids hvalues hfakes hsecrets hi hlen hboundBids hboundValues
    hboundFakes hboundSecrets hvalueLookup hfakeLookup hfakeNorm hsecretLookup htail

theorem scratch_revealLoopBody_ok_placeBid_false_of_get (evm : EVM.State) (locals : Store)
    (values fakes secrets : List Value) (len refund i value secret blinded deposit high : UInt256)
    (fakeRaw : Value) (hashBytes : List UInt8)
    (hbids : locals.get? "bids" = none)
    (hvalues : locals.get? "values" = some (.array values))
    (hfakes : locals.get? "fakes" = some (.array fakes))
    (hsecrets : locals.get? "secrets" = some (.array secrets))
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hrefund : locals.get? "refund" = some (.int (Int.ofNat refund.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hboundBids : i.toNat < len.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool false))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit)
    (hhigh : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩ = high)
    (hhash :
      evalExpr? blindAuctionConfig
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStoreOf locals evm i value secret false } evm
        scratch_revealPackedHashExpr =
        .ok (.fixedBytes ⟨31, by decide⟩ hashBytes))
    (heq : EVM.Word.toBytesBE blinded = hashBytes)
    (hfit : refund.toNat + deposit.toNat < UInt256.size)
    (hdepositGe : value.toNat ≤ deposit.toNat)
    (hplaceFalse : value.toNat ≤ high.toNat) :
    ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := locals }
      evm scratch_revealLoopBodyStmts
      (.ok
        { contract := blindAuctionContract,
          locals :=
            (scratch_revealRefundAddedStoreOf locals evm i refund value secret deposit false)
              |>.insert "ok" (.bool false) }
        (scratch_revealZeroBlindedState evm i)) := by
  let L4 := scratch_revealSecretStoreOf locals evm i value secret false
  let L5 := scratch_revealRefundAddedStoreOf locals evm i refund value secret deposit false
  let L6 := L5.insert "ok" (.bool false)
  have hbidL4 :
      L4.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    simpa [L4] using scratch_revealSecretStoreOf_bid_get locals evm i value secret false
  have hguard :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
          (.keccak256 (.abiEncodePacked
            [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")]))) =
          .ok (.bool false) := by
    simpa [scratch_revealPackedHashExpr, L4] using
      scratch_evalExpr_reveal_hash_guard_false evm L4 i blinded hashBytes hbidL4 hblinded
        (by simpa [L4] using hhash) heq
  have hrefundL4 :
      L4.get? "refund" = some (.int (Int.ofNat refund.toNat)) := by
    simpa [L4] using
      scratch_revealSecretStoreOf_refund_get locals evm i refund value secret false hrefund
  have hadd :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))) =
          .ok (.int (Int.ofNat (refund.toNat + deposit.toNat))) :=
    scratch_evalExpr_reveal_refund_add_deposit evm L4 i refund deposit hbidL4 hrefundL4
      hdeposit hfit
  have hassignRefund :
      assignStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        .localVar { base := "refund" } (.int (Int.ofNat (refund.toNat + deposit.toNat))) =
          .ok ({ contract := blindAuctionContract, locals := L5 }, evm) := by
    simpa [L5, scratch_revealRefundAddedStoreOf, L4] using
      scratch_assign_local_value evm L4 "refund" (.int (Int.ofNat refund.toNat))
        (.int (Int.ofNat (refund.toNat + deposit.toNat))) hrefundL4
  have hbidL5 :
      L5.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    simpa [L5] using
      scratch_revealRefundAddedStoreOf_bid_get locals evm i refund value secret deposit false
  have hvalueL5 :
      L5.get? "value" = some (.int (Int.ofNat value.toNat)) := by
    simpa [L5] using
      scratch_revealRefundAddedStoreOf_value_get locals evm i refund value secret deposit false
  have hfakeL5 : L5.get? "fake" = some (.bool false) := by
    simpa [L5] using
      scratch_revealRefundAddedStoreOf_fake_get locals evm i refund value secret deposit false
  have hcondTrue :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        (.binary .and (.unary .not (.var "fake"))
          (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value"))) =
          .ok (.bool true) :=
    scratch_evalExpr_reveal_placeBid_cond_true evm L5 i value deposit hbidL5 hfakeL5
      hvalueL5 hdeposit hdepositGe
  have hcall :
      ExecStmt blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        (.internalCall "placeBid" [sender, .var "value"] "ok")
        (.ok { contract := blindAuctionContract, locals := L6 } evm) := by
    let calleeFrame : Frame :=
      { contract := blindAuctionContract,
        locals := scratch_placeBidStore evm.executionEnv.source value }
    simpa [L6] using
      ExecStmt.internalCallReturn
        (cfg := blindAuctionConfig)
        (solm := { contract := blindAuctionContract, locals := L5 })
        (evm := evm)
        (name := "placeBid") (retVar := "ok")
        (args := [sender, .var "value"])
        (argVals := [.address evm.executionEnv.source, .int (Int.ofNat value.toNat)])
        (callee := placeBidFn.toCallable)
        (locals := scratch_placeBidStore evm.executionEnv.source value)
        (calleeSolm := calleeFrame)
        (calleeEvm := evm)
        (value := some (.bool false))
        (scratch_evalExprs_reveal_placeBid_args evm L5 value hvalueL5)
        scratch_placeBid_lookup
        (by simpa [FunctionDecl.toCallable] using
          scratch_placeBid_bind evm.executionEnv.source value)
        (by
          simpa [ExecTransitionBody, FunctionDecl.toCallable, calleeFrame] using
            (scratch_blindAuctionPlaceBidBodyReturns_false evm evm.executionEnv.source value high
              hhigh hplaceFalse))
  have hokFalse :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L6 } evm
        (.var "ok") = .ok (.bool false) := by
    exact evalExpr_reveal_var_value evm L6 "ok" (.bool false) (by simp [L6])
  have hbidL6 :
      L6.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    simpa [L6, Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using hbidL5
  have hzero :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L6 } evm
        (.cast (.intLit 0) bytes32St) =
          .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (EVM.Word.ofNat 0))) :=
    scratch_evalExpr_reveal_cast_zero_bytes32 evm L6
  have hassignZero :
      assignStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := L6 } evm
        .storage (aliasF "bidToCheck" "blindedBid")
        (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (EVM.Word.ofNat 0))) =
          .ok ({ contract := blindAuctionContract, locals := L6 },
            scratch_revealZeroBlindedState evm i) :=
    scratch_assign_reveal_blinded_zero evm L6 i hbidL6
  have hplaceThen :
      ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        [ .internalCall "placeBid" [sender, .var "value"] "ok",
          .ite (.var "ok")
            [ .assign .localVar { base := "refund" }
                (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ]
        (.ok { contract := blindAuctionContract, locals := L6 } evm) := by
    refine ExecBlock.consNormal hcall ?_
    exact ExecBlock.consNormal (ExecStmt.iteFalse hokFalse ExecBlock.nil) ExecBlock.nil
  have hplaceIte :
      ExecStmt blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        (.ite
          (.binary .and (.unary .not (.var "fake"))
            (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
          [ .internalCall "placeBid" [sender, .var "value"] "ok",
            .ite (.var "ok")
              [ .assign .localVar { base := "refund" }
                  (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [])
        (.ok { contract := blindAuctionContract, locals := L6 } evm) :=
    ExecStmt.iteTrue hcondTrue hplaceThen
  have htail :
      ExecBlock blindAuctionConfig
        { contract := blindAuctionContract, locals := L4 } evm
        (List.drop 4 scratch_revealLoopBodyStmts)
        (.ok { contract := blindAuctionContract, locals := L6 }
          (scratch_revealZeroBlindedState evm i)) := by
    change ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := L4 } evm
      [ .ite
          (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
            (.keccak256 (.abiEncodePacked
              [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
          [.continue] [],
        .assign .localVar { base := "refund" }
          (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
        .ite
          (.binary .and (.unary .not (.var "fake"))
            (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
          [ .internalCall "placeBid" [sender, .var "value"] "ok",
            .ite (.var "ok")
              [ .assign .localVar { base := "refund" }
                  (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
        .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]
      (.ok { contract := blindAuctionContract, locals := L6 }
        (scratch_revealZeroBlindedState evm i))
    refine ExecBlock.consNormal (ExecStmt.iteFalse hguard ExecBlock.nil) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hadd hassignRefund) ?_
    refine ExecBlock.consNormal (solm' := { contract := blindAuctionContract, locals := L6 })
      (evm' := evm) hplaceIte ?_
    exact ExecBlock.consNormal (ExecStmt.assign hzero hassignZero) ExecBlock.nil
  simpa [L6] using
    scratch_revealLoopBody_prefix_exec_of_get evm locals values fakes secrets len refund i value
      secret false fakeRaw hbids hvalues hfakes hsecrets hi hlen hboundBids hboundValues
      hboundFakes hboundSecrets hvalueLookup hfakeLookup hfakeNorm hsecretLookup htail

theorem scratch_revealLoopBody_ok_placeBid_true_core_of_get (evm evmPB : EVM.State)
    (locals : Store)
    (values fakes secrets : List Value) (len refund i value secret blinded deposit : UInt256)
    (fakeRaw : Value) (hashBytes : List UInt8)
    (hbids : locals.get? "bids" = none)
    (hvalues : locals.get? "values" = some (.array values))
    (hfakes : locals.get? "fakes" = some (.array fakes))
    (hsecrets : locals.get? "secrets" = some (.array secrets))
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hrefund : locals.get? "refund" = some (.int (Int.ofNat refund.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hboundBids : i.toNat < len.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool false))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit)
    (hhash :
      evalExpr? blindAuctionConfig
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStoreOf locals evm i value secret false } evm
        scratch_revealPackedHashExpr =
        .ok (.fixedBytes ⟨31, by decide⟩ hashBytes))
    (heq : EVM.Word.toBytesBE blinded = hashBytes)
    (hfit : refund.toNat + deposit.toNat < UInt256.size)
    (hdepositGe : value.toNat ≤ deposit.toNat)
    (hplaceBody :
      ExecTransitionBody blindAuctionConfig blindAuctionContract evm
        (scratch_placeBidStore evm.executionEnv.source value) placeBidFn.body
        (.returned
          { contract := blindAuctionContract,
            locals := scratch_placeBidStore evm.executionEnv.source value }
          evmPB (some (.bool true))))
    (href : scratch_revealBidEvaledRef evmPB i = scratch_revealBidEvaledRef evm i) :
    ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := locals }
      evm scratch_revealLoopBodyStmts
      (.ok
        { contract := blindAuctionContract,
          locals := scratch_revealRefundPlacedStoreOf locals evm i refund value secret deposit }
        (scratch_revealZeroBlindedState evmPB i)) := by
  let L4 := scratch_revealSecretStoreOf locals evm i value secret false
  let L5 := scratch_revealRefundAddedStoreOf locals evm i refund value secret deposit false
  let L6 := L5.insert "ok" (.bool true)
  let refundAdded : UInt256 := UInt256.ofNat (refund.toNat + deposit.toNat)
  let L7 := L6.insert "refund" (.int (Int.ofNat (refundAdded.toNat - value.toNat)))
  have hrefundAddedToNat : refundAdded.toNat = refund.toNat + deposit.toNat := by
    simpa [refundAdded] using ulit_toNat' (refund.toNat + deposit.toNat) hfit
  have hbidL4 :
      L4.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    simpa [L4] using scratch_revealSecretStoreOf_bid_get locals evm i value secret false
  have hguard :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
          (.keccak256 (.abiEncodePacked
            [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")]))) =
          .ok (.bool false) := by
    simpa [scratch_revealPackedHashExpr, L4] using
      scratch_evalExpr_reveal_hash_guard_false evm L4 i blinded hashBytes hbidL4 hblinded
        (by simpa [L4] using hhash) heq
  have hrefundL4 :
      L4.get? "refund" = some (.int (Int.ofNat refund.toNat)) := by
    simpa [L4] using
      scratch_revealSecretStoreOf_refund_get locals evm i refund value secret false hrefund
  have hadd :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))) =
          .ok (.int (Int.ofNat (refund.toNat + deposit.toNat))) :=
    scratch_evalExpr_reveal_refund_add_deposit evm L4 i refund deposit hbidL4 hrefundL4
      hdeposit hfit
  have hassignRefund :
      assignStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        .localVar { base := "refund" } (.int (Int.ofNat (refund.toNat + deposit.toNat))) =
          .ok ({ contract := blindAuctionContract, locals := L5 }, evm) := by
    simpa [L5, scratch_revealRefundAddedStoreOf, L4] using
      scratch_assign_local_value evm L4 "refund" (.int (Int.ofNat refund.toNat))
        (.int (Int.ofNat (refund.toNat + deposit.toNat))) hrefundL4
  have hbidL5 :
      L5.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    simpa [L5] using
      scratch_revealRefundAddedStoreOf_bid_get locals evm i refund value secret deposit false
  have hvalueL5 :
      L5.get? "value" = some (.int (Int.ofNat value.toNat)) := by
    simpa [L5] using
      scratch_revealRefundAddedStoreOf_value_get locals evm i refund value secret deposit false
  have hfakeL5 : L5.get? "fake" = some (.bool false) := by
    simpa [L5] using
      scratch_revealRefundAddedStoreOf_fake_get locals evm i refund value secret deposit false
  have hcondTrue :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        (.binary .and (.unary .not (.var "fake"))
          (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value"))) =
          .ok (.bool true) :=
    scratch_evalExpr_reveal_placeBid_cond_true evm L5 i value deposit hbidL5 hfakeL5
      hvalueL5 hdeposit hdepositGe
  have hcall :
      ExecStmt blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        (.internalCall "placeBid" [sender, .var "value"] "ok")
        (.ok { contract := blindAuctionContract, locals := L6 } evmPB) := by
    let calleeFrame : Frame :=
      { contract := blindAuctionContract,
        locals := scratch_placeBidStore evm.executionEnv.source value }
    simpa [L6] using
      ExecStmt.internalCallReturn
        (cfg := blindAuctionConfig)
        (solm := { contract := blindAuctionContract, locals := L5 })
        (evm := evm)
        (name := "placeBid") (retVar := "ok")
        (args := [sender, .var "value"])
        (argVals := [.address evm.executionEnv.source, .int (Int.ofNat value.toNat)])
        (callee := placeBidFn.toCallable)
        (locals := scratch_placeBidStore evm.executionEnv.source value)
        (calleeSolm := calleeFrame)
        (calleeEvm := evmPB)
        (value := some (.bool true))
        (scratch_evalExprs_reveal_placeBid_args evm L5 value hvalueL5)
        scratch_placeBid_lookup
        (by simpa [FunctionDecl.toCallable] using
          scratch_placeBid_bind evm.executionEnv.source value)
        (by simpa [ExecTransitionBody, FunctionDecl.toCallable, calleeFrame] using hplaceBody)
  have hokTrue :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L6 } evmPB
        (.var "ok") = .ok (.bool true) := by
    exact evalExpr_reveal_var_value evmPB L6 "ok" (.bool true) (by simp [L6])
  have hrefundL6 :
      L6.get? "refund" = some (.int (Int.ofNat refundAdded.toNat)) := by
    simpa [L6, refundAdded, hrefundAddedToNat, Std.HashMap.getElem?_insert,
      Std.HashMap.get?_eq_getElem?] using
        scratch_revealRefundAddedStoreOf_refund_get locals evm i refund value secret deposit false
  have hvalueL6 :
      L6.get? "value" = some (.int (Int.ofNat value.toNat)) := by
    simpa [L6, Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using hvalueL5
  have hsubLe : value.toNat ≤ refundAdded.toNat := by
    rw [hrefundAddedToNat]
    omega
  have hsub :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L6 } evmPB
        (u256 (.binary .sub (.var "refund") (.var "value"))) =
          .ok (.int (Int.ofNat (refundAdded.toNat - value.toNat))) :=
    scratch_evalExpr_reveal_refund_sub_value evmPB L6 refundAdded value hrefundL6 hvalueL6
      hsubLe
  have hassignSub :
      assignStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := L6 } evmPB
        .localVar { base := "refund" } (.int (Int.ofNat (refundAdded.toNat - value.toNat))) =
          .ok ({ contract := blindAuctionContract, locals := L7 }, evmPB) := by
    simpa [L7] using
      scratch_assign_local_value evmPB L6 "refund" (.int (Int.ofNat refundAdded.toNat))
        (.int (Int.ofNat (refundAdded.toNat - value.toNat))) hrefundL6
  have hbidL7 :
      L7.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evmPB i) bidStructTy) := by
    have hbidOrig :
        L7.get? "bidToCheck" =
          some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
      simpa [L7, L6, Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using hbidL5
    simpa [href] using hbidOrig
  have hzero :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L7 } evmPB
        (.cast (.intLit 0) bytes32St) =
          .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (EVM.Word.ofNat 0))) :=
    scratch_evalExpr_reveal_cast_zero_bytes32 evmPB L7
  have hassignZero :
      assignStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := L7 } evmPB
        .storage (aliasF "bidToCheck" "blindedBid")
        (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (EVM.Word.ofNat 0))) =
          .ok ({ contract := blindAuctionContract, locals := L7 },
            scratch_revealZeroBlindedState evmPB i) :=
    scratch_assign_reveal_blinded_zero evmPB L7 i hbidL7
  have hthenOk :
      ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L6 } evmPB
        [ .assign .localVar { base := "refund" }
            (u256 (.binary .sub (.var "refund") (.var "value"))) ]
        (.ok { contract := blindAuctionContract, locals := L7 } evmPB) := by
    exact ExecBlock.consNormal (ExecStmt.assign hsub hassignSub) ExecBlock.nil
  have hokIte :
      ExecStmt blindAuctionConfig { contract := blindAuctionContract, locals := L6 } evmPB
        (.ite (.var "ok")
          [ .assign .localVar { base := "refund" }
              (u256 (.binary .sub (.var "refund") (.var "value"))) ] [])
        (.ok { contract := blindAuctionContract, locals := L7 } evmPB) :=
    ExecStmt.iteTrue hokTrue hthenOk
  have hplaceThen :
      ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        [ .internalCall "placeBid" [sender, .var "value"] "ok",
          .ite (.var "ok")
            [ .assign .localVar { base := "refund" }
                (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ]
        (.ok { contract := blindAuctionContract, locals := L7 } evmPB) := by
    refine ExecBlock.consNormal (solm' := { contract := blindAuctionContract, locals := L6 })
      (evm' := evmPB) hcall ?_
    exact ExecBlock.consNormal hokIte ExecBlock.nil
  have hplaceIte :
      ExecStmt blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        (.ite
          (.binary .and (.unary .not (.var "fake"))
            (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
          [ .internalCall "placeBid" [sender, .var "value"] "ok",
            .ite (.var "ok")
              [ .assign .localVar { base := "refund" }
                  (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [])
        (.ok { contract := blindAuctionContract, locals := L7 } evmPB) :=
    ExecStmt.iteTrue hcondTrue hplaceThen
  have htail :
      ExecBlock blindAuctionConfig
        { contract := blindAuctionContract, locals := L4 } evm
        (List.drop 4 scratch_revealLoopBodyStmts)
        (.ok { contract := blindAuctionContract, locals := L7 }
          (scratch_revealZeroBlindedState evmPB i)) := by
    change ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := L4 } evm
      [ .ite
          (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
            (.keccak256 (.abiEncodePacked
              [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
          [.continue] [],
        .assign .localVar { base := "refund" }
          (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
        .ite
          (.binary .and (.unary .not (.var "fake"))
            (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
          [ .internalCall "placeBid" [sender, .var "value"] "ok",
            .ite (.var "ok")
              [ .assign .localVar { base := "refund" }
                  (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
        .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]
      (.ok { contract := blindAuctionContract, locals := L7 }
        (scratch_revealZeroBlindedState evmPB i))
    refine ExecBlock.consNormal (ExecStmt.iteFalse hguard ExecBlock.nil) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hadd hassignRefund) ?_
    refine ExecBlock.consNormal (solm' := { contract := blindAuctionContract, locals := L7 })
      (evm' := evmPB) hplaceIte ?_
    exact ExecBlock.consNormal (ExecStmt.assign hzero hassignZero) ExecBlock.nil
  simpa [scratch_revealRefundPlacedStoreOf, L7, L6, L5, refundAdded, hrefundAddedToNat] using
    scratch_revealLoopBody_prefix_exec_of_get evm locals values fakes secrets len refund i value
      secret false fakeRaw hbids hvalues hfakes hsecrets hi hlen hboundBids hboundValues
      hboundFakes hboundSecrets hvalueLookup hfakeLookup hfakeNorm hsecretLookup htail

theorem scratch_revealLoopBody_ok_placeBid_true_zero_of_get (evm : EVM.State) (locals : Store)
    (values fakes secrets : List Value) (len refund i value secret blinded deposit high old : UInt256)
    (fakeRaw : Value) (hashBytes : List UInt8)
    (hbids : locals.get? "bids" = none)
    (hvalues : locals.get? "values" = some (.array values))
    (hfakes : locals.get? "fakes" = some (.array fakes))
    (hsecrets : locals.get? "secrets" = some (.array secrets))
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hrefund : locals.get? "refund" = some (.int (Int.ofNat refund.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hboundBids : i.toNat < len.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool false))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit)
    (hhigh : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩ = high)
    (hold : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = old)
    (hhash :
      evalExpr? blindAuctionConfig
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStoreOf locals evm i value secret false } evm
        scratch_revealPackedHashExpr =
        .ok (.fixedBytes ⟨31, by decide⟩ hashBytes))
    (heq : EVM.Word.toBytesBE blinded = hashBytes)
    (hfit : refund.toNat + deposit.toNat < UInt256.size)
    (hdepositGe : value.toNat ≤ deposit.toNat)
    (hlt : high.toNat < value.toNat)
    (hzero : UInt256.land old solcAddrMask = ⟨0⟩) :
    ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := locals }
      evm scratch_revealLoopBodyStmts
      (.ok
        { contract := blindAuctionContract,
          locals := scratch_revealRefundPlacedStoreOf locals evm i refund value secret deposit }
        (scratch_revealZeroBlindedState
          (scratch_placeBidAfterBidder (scratch_placeBidAfterHigh evm value)
            evm.executionEnv.source) i)) := by
  let evmPB :=
    scratch_placeBidAfterBidder (scratch_placeBidAfterHigh evm value) evm.executionEnv.source
  refine scratch_revealLoopBody_ok_placeBid_true_core_of_get evm evmPB locals values fakes
    secrets len refund i value secret blinded deposit fakeRaw hashBytes hbids hvalues hfakes
    hsecrets hi hrefund hlen hboundBids hboundValues hboundFakes hboundSecrets hvalueLookup
    hfakeLookup hfakeNorm hsecretLookup hblinded hdeposit hhash heq hfit hdepositGe ?_ ?_
  · simpa [evmPB] using
      scratch_blindAuctionPlaceBidBodyReturns_true_zero evm evm.executionEnv.source value high old
        hhigh hold hlt hzero
  · simp [evmPB, scratch_placeBidAfterBidder, scratch_placeBidAfterHigh,
      scratch_revealBidEvaledRef_storageStore]

theorem scratch_revealLoopBody_ok_placeBid_true_nonzero_of_get (evm : EVM.State)
    (locals : Store) (values fakes secrets : List Value)
    (len refund i value secret blinded deposit high old pending : UInt256)
    (oldAddr : AccountAddress) (fakeRaw : Value) (hashBytes : List UInt8)
    (hbids : locals.get? "bids" = none)
    (hvalues : locals.get? "values" = some (.array values))
    (hfakes : locals.get? "fakes" = some (.array fakes))
    (hsecrets : locals.get? "secrets" = some (.array secrets))
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hrefund : locals.get? "refund" = some (.int (Int.ofNat refund.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hboundBids : i.toNat < len.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool false))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit)
    (hhigh : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩ = high)
    (hold : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = old)
    (holdAddr : oldAddr = AccountAddress.ofNat (UInt256.land old solcAddrMask).toNat)
    (hpending : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (pendingReturnsSlot (.address oldAddr)) = pending)
    (hhash :
      evalExpr? blindAuctionConfig
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStoreOf locals evm i value secret false } evm
        scratch_revealPackedHashExpr =
        .ok (.fixedBytes ⟨31, by decide⟩ hashBytes))
    (heq : EVM.Word.toBytesBE blinded = hashBytes)
    (hfit : refund.toNat + deposit.toNat < UInt256.size)
    (hdepositGe : value.toNat ≤ deposit.toNat)
    (hlt : high.toNat < value.toNat)
    (hnonzero : UInt256.land old solcAddrMask ≠ ⟨0⟩)
    (hsum : pending.toNat + high.toNat < UInt256.size) :
    ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := locals }
      evm scratch_revealLoopBodyStmts
      (.ok
        { contract := blindAuctionContract,
          locals := scratch_revealRefundPlacedStoreOf locals evm i refund value secret deposit }
        (scratch_revealZeroBlindedState
          (scratch_placeBidAfterBidder
            (scratch_placeBidAfterHigh
              (scratch_placeBidAfterPending evm oldAddr
                (UInt256.ofNat (pending.toNat + high.toNat))) value)
            evm.executionEnv.source) i)) := by
  let evmPB :=
    scratch_placeBidAfterBidder
      (scratch_placeBidAfterHigh
        (scratch_placeBidAfterPending evm oldAddr
          (UInt256.ofNat (pending.toNat + high.toNat))) value)
      evm.executionEnv.source
  refine scratch_revealLoopBody_ok_placeBid_true_core_of_get evm evmPB locals values fakes
    secrets len refund i value secret blinded deposit fakeRaw hashBytes hbids hvalues hfakes
    hsecrets hi hrefund hlen hboundBids hboundValues hboundFakes hboundSecrets hvalueLookup
    hfakeLookup hfakeNorm hsecretLookup hblinded hdeposit hhash heq hfit hdepositGe ?_ ?_
  · simpa [evmPB] using
      scratch_blindAuctionPlaceBidBodyReturns_true_nonzero evm evm.executionEnv.source oldAddr
        value high old pending hhigh hold holdAddr hpending hlt hnonzero hsum
  · simp [evmPB, scratch_placeBidAfterBidder, scratch_placeBidAfterHigh,
      scratch_placeBidAfterPending, scratch_revealBidEvaledRef_storageStore]

-- LIBRARY CANDIDATE: dynamic-array decoder nth/read bridge for fixed-width ABI elements.
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

namespace BlindAuction

/-- `reveal(uint256[],bool[],bytes32[])` body (pc 387) refines its transition. -/
theorem blindAuctionRevealBodyCore {cA gh bl σ_evm σ₀_evm σ_solm σ₀_solm A I} {g : UInt256}
    (hcode : I.code = blindAuctionBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hsel : selIs I ⟨#[0x90, 0x0f, 0x08, 0x0a]⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀_evm (Sat256.ofUInt256 g) A I) ⟨387⟩
      [blindAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm)
      k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hOriginalAccounts : accountMapEquiv σ₀_evm σ₀_solm) :
    runtimeEquivalenceFor blindAuctionConfig blindAuctionContract cA gh bl
      σ_evm σ₀_evm σ_solm σ₀_solm g A I := by
  have _hsize : I.calldata.size < UInt256.size := hsize
  have _hperm : I.perm = true := hperm
  have _hOriginalAccounts : accountMapEquiv σ₀_evm σ₀_solm := hOriginalAccounts
  have hsz := blindAuctionRevealSelector_size hsel
  have hd := blindAuctionDispatch_reveal (cd := I.calldata) hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have _hdecodeEntry :=
      blindAuctionX_reveal_decodeEntry (g := Sat256.ofUInt256 g) hwv hreach
    by_cases hshortHead : I.calldata.size < 100
    · have hdecNone := blindAuctionDecode_reveal_none_short (I := I) hsz hshortHead
      have hslt :
          UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ =
            ⟨1⟩ := by
        have h :=
          solcCalldataStaticLenCheckShort (sz := I.calldata.size) (words := 3)
            hsz hshortHead hsize (by omega)
        simpa using h
      have hrev := blindAuctionRevealX_decode_head_revert
        (g := Sat256.ofUInt256 g) hslt _hdecodeEntry
      exact hrev.reEquivDecodingFailed hcode hd hdecNone
    · by_cases hhuge : 2 ^ 255 + 4 ≤ I.calldata.size
      · have hdecNone := blindAuctionDecode_reveal_none_huge (I := I) hhuge
        have hslt :
            UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ =
              ⟨1⟩ := by
          have h :=
            solcCalldataStaticLenCheckHuge (sz := I.calldata.size) (words := 3)
              hhuge hsize (by omega)
          simpa using h
        have hrev := blindAuctionRevealX_decode_head_revert
          (g := Sat256.ofUInt256 g) hslt _hdecodeEntry
        exact hrev.reEquivDecodingFailed hcode hd hdecNone
      · have hslt :
            UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ =
              ⟨0⟩ := by
          have h :=
            solcCalldataStaticLenCheckOk (sz := I.calldata.size) (words := 3)
              (by omega) (by omega) hsize
          simpa using h
        obtain ⟨k1806, C1806, rd1806⟩ :=
          blindAuctionRevealX_decode_head_ok (g := Sat256.ofUInt256 g) hslt _hdecodeEntry
        by_cases hcalldataSign : I.calldata.size < 2 ^ 255
        · by_cases hdecNone :
              decodeCalldata (revealTransition.params.map Param.name)
                (transitionSignature revealTransition).paramTypes I.calldata = none
          · have hrev :=
              scratch_blindAuctionRevealDecode1806_none_reverts
                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀_evm)
                (A := A) (I := I) (g := Sat256.ofUInt256 g) rd1806 (by omega)
                hcalldataSign hdecNone
            exact hrev.reEquivDecodingFailed hcode hd hdecNone
          · obtain ⟨callargs, hdec⟩ := Option.ne_none_iff_exists'.mp hdecNone
            obtain ⟨values, fakes, secrets, hstore, hguards⟩ :=
              blindAuctionDecode_reveal_guard_facts hcalldataSign hdec
            rcases hguards with ⟨hvaluesGuards, hfakesGuards, hsecretsGuards⟩
            rcases hvaluesGuards with
              ⟨valuesLenWord, hvaluesListLen, hvaluesGt, hvaluesStart, hvaluesLenLoad,
                hvaluesLenMax, hvaluesEnd⟩
            rcases hfakesGuards with
              ⟨fakesLenWord, hfakesListLen, hfakesGt, hfakesStart, hfakesLenLoad,
                hfakesLenMax, hfakesEnd⟩
            rcases hsecretsGuards with
              ⟨secretsLenWord, hsecretsListLen, hsecretsGt, hsecretsStart,
                hsecretsLenLoad, hsecretsLenMax, hsecretsEnd⟩
            have hvaluesGet : callargs.get? "values" = some (.array values) := by
              rw [hstore, store_get_ne, store_get_ne, store_get_self]
              · decide
              · decide
            have hfakesGet : callargs.get? "fakes" = some (.array fakes) := by
              rw [hstore, store_get_ne, store_get_self]
              decide
            have hsecretsGet : callargs.get? "secrets" = some (.array secrets) := by
              rw [hstore, store_get_self]
            obtain ⟨_, _, rd887⟩ :=
              blindAuctionRevealDecodeArrays1806_to_887
                (ee := I) (g := Sat256.ofUInt256 g)
                rd1806 hvaluesGt hvaluesStart hvaluesLenLoad hvaluesLenMax hvaluesEnd
                hfakesGt hfakesStart hfakesLenLoad hfakesLenMax hfakesEnd
                hsecretsGt hsecretsStart hsecretsLenLoad hsecretsLenMax hsecretsEnd
            let evmSolm : EVM.State :=
              initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I
            have hwvSolm : evmSolm.executionEnv.weiValue = ⟨0⟩ := by
              simpa [evmSolm, initState] using hwv
            have hbiddingAbsent : callargs.get? biddingEndRef.base = none :=
              blindAuctionDecode_reveal_callargs_absent hdec (by decide) (by decide) (by decide)
            have hrevealAbsent : callargs.get? revealEndRef.base = none :=
              blindAuctionDecode_reveal_callargs_absent hdec (by decide) (by decide) (by decide)
            have hbidsEq := revealScratchBidsLengthWord_accountMapEquiv hAccounts I
            have hbiddingEq := revealScratchBiddingEndWord_accountMapEquiv hAccounts I
            have hrevealEq := revealScratchRevealEndWord_accountMapEquiv hAccounts I
            have hbidsHash := revealScratchBidsMappingBaseKeccak I
            by_cases hafter :
                (revealScratchBiddingEndWord σ_evm I).toNat <
                  (revealScratchTimestampWord I).toNat
            · by_cases hbefore :
                  (revealScratchTimestampWord I).toNat <
                    (revealScratchRevealEndWord σ_evm I).toNat
              · have hafterBody :
                    (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨1⟩).toNat <
                      (UInt256.ofNat evmSolm.executionEnv.header.timestamp).toNat := by
                  change (revealScratchBiddingEndWord σ_solm I).toNat <
                    (revealScratchTimestampWord I).toNat
                  rw [← hbiddingEq]
                  exact hafter
                have hbeforeBody :
                    (UInt256.ofNat evmSolm.executionEnv.header.timestamp).toNat <
                      (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩).toNat := by
                  change (revealScratchTimestampWord I).toNat <
                    (revealScratchRevealEndWord σ_solm I).toNat
                  rw [← hrevealEq]
                  exact hbefore
                have hlenBody :
                    Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
                      (bidsBase (.address evmSolm.executionEnv.source)) =
                        revealScratchBidsLengthWord σ_solm I := by
                  rfl
                by_cases hvaluesEq :
                    revealScratchBidsLengthWord σ_evm I = valuesLenWord
                · by_cases hfakesEq :
                      revealScratchBidsLengthWord σ_evm I = fakesLenWord
                  · by_cases hsecretsEq :
                        revealScratchBidsLengthWord σ_evm I = secretsLenWord
                    · have h963 :=
                        blindAuctionRevealX_from887_afterTimeGuards
                          (cA := cA) (σ := σ_evm) (I := I) (g := Sat256.ofUInt256 g)
                          (s0 := initState cA gh bl σ_evm σ₀_evm
                            (Sat256.ofUInt256 g) A I)
                          rd887 hafter hbefore
                      rcases h963 with ⟨_, _, rd963⟩
                      by_cases hbidsZero :
                          revealScratchBidsLengthWord σ_evm I = ⟨0⟩
                      · have hvaluesWordZero : valuesLenWord = ⟨0⟩ := by
                          rw [← hvaluesEq, hbidsZero]
                        have hfakesWordZero : fakesLenWord = ⟨0⟩ := by
                          rw [← hfakesEq, hbidsZero]
                        have hsecretsWordZero : secretsLenWord = ⟨0⟩ := by
                          rw [← hsecretsEq, hbidsZero]
                        have hvaluesLenZero : values.length = 0 := by
                          rw [hvaluesListLen, hvaluesWordZero]
                          rfl
                        have hfakesLenZero : fakes.length = 0 := by
                          rw [hfakesListLen, hfakesWordZero]
                          rfl
                        have hsecretsLenZero : secrets.length = 0 := by
                          rw [hsecretsListLen, hsecretsWordZero]
                          rfl
                        have hvaluesNil : values = [] :=
                          List.eq_nil_of_length_eq_zero hvaluesLenZero
                        have hfakesNil : fakes = [] :=
                          List.eq_nil_of_length_eq_zero hfakesLenZero
                        have hsecretsNil : secrets = [] :=
                          List.eq_nil_of_length_eq_zero hsecretsLenZero
                        have hvaluesGetEmpty :
                            callargs.get? "values" = some (.array []) := by
                          simpa [hvaluesNil] using hvaluesGet
                        have hfakesGetEmpty :
                            callargs.get? "fakes" = some (.array []) := by
                          simpa [hfakesNil] using hfakesGet
                        have hsecretsGetEmpty :
                            callargs.get? "secrets" = some (.array []) := by
                          simpa [hsecretsNil] using hsecretsGet
                        have hcallargsEmpty : callargs = revealEmptyStore :=
                          blindAuctionDecode_reveal_callargs_empty_eq hdec hvaluesGetEmpty
                            hfakesGetEmpty hsecretsGetEmpty
                        have hlenZeroBody :
                            Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
                              (bidsBase (.address evmSolm.executionEnv.source)) = ⟨0⟩ := by
                          rw [hlenBody, ← hbidsEq, hbidsZero]
                        by_cases hdepthEq : I.depth = 1024
                        · obtain ⟨_, _, rd1350⟩ :=
                            blindAuctionRevealX_from963_empty_callDepth
                              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                              (σ₀ := σ₀_evm) (A := A) (I := I)
                              (g := Sat256.ofUInt256 g)
                                hdepthEq
                                (by
                                  simpa [hvaluesWordZero, hfakesWordZero, hsecretsWordZero]
                                    using rd963)
                                hbidsZero hbidsHash
                          let evmSFail : EVM.State :=
                            { evmSolm with
                              substate := (evmSolm.addAccessedAccount
                                (EVM.address evmSolm.executionEnv.source)).substate }
                          have hcallS :
                              callViaEVM evmSolm (EVM.address evmSolm.executionEnv.source)
                                0 ByteArray.empty (false, evmSFail, ByteArray.empty) := by
                            apply callViaEVM.callNotMade
                            · rfl
                            · rfl
                            · rintro ⟨_, hdepthNe⟩
                              exact hdepthNe (by
                                simpa [evmSolm, initState] using hdepthEq)
                          have hbody :
                              ExecTransitionBody blindAuctionConfig blindAuctionContract evmSolm
                                callargs revealTransition.body .reverted := by
                            have hbodyEmpty :
                                ExecTransitionBody blindAuctionConfig blindAuctionContract evmSolm
                                  revealEmptyStore revealTransition.body .reverted :=
                              blindAuctionRevealBodyReverts_empty_callFailure evmSolm evmSFail
                                ByteArray.empty hwvSolm hafterBody hbeforeBody hlenZeroBody
                                hcallS
                            simpa [hcallargsEmpty] using hbodyEmpty
                          have hrev : RDrev blindAuctionBytecode (Sat256.ofUInt256 g)
                              (initState cA gh bl σ_evm σ₀_evm
                                (Sat256.ofUInt256 g) A I) :=
                            blindAuctionRevealX_postCallEmpty_failure_revert
                              (by simpa using rd1350)
                          exact hrev.reEquivExecutionRevert hcode hd hdec hbody
                        · have hdepthLt : I.depth.val < 1024 := by
                            have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
                            have hneVal : I.depth.val ≠ 1024 := by
                              intro hv
                              exact hdepthEq (Fin.ext hv)
                            omega
                          obtain ⟨cA', σ', z, out, A_in, callGas, _, _, hTheta,
                              hout255, rd1350⟩ :=
                            blindAuctionRevealX_from963_empty_callMade
                              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                              (σ₀ := σ₀_evm) (A := A) (I := I)
                                (g := Sat256.ofUInt256 g)
                                hdepthLt
                                (by
                                  simpa [hvaluesWordZero, hfakesWordZero, hsecretsWordZero]
                                    using rd963)
                                hbidsZero hbidsHash
                          rcases hTheta with ⟨g'', A', hThetaEq⟩
                          let evmECall : EVM.State :=
                            { initState cA gh bl σ_evm σ₀_evm
                                (Sat256.ofUInt256 g) A I with
                              accountMap := σ',
                              substate := A',
                              createdAccounts := cA' }
                          have hAddressId (a : AccountAddress) : EVM.address a = a := by
                            apply Fin.ext
                            simp [EVM.address, EVM.uintN]
                            exact Nat.mod_eq_of_lt a.isLt
                          have hcallE :
                              callViaEVM
                                (initState cA gh bl σ_evm σ₀_evm
                                  (Sat256.ofUInt256 g) A I)
                                (EVM.address I.source) 0 ByteArray.empty
                                (z, evmECall, out) := by
                            refine callViaEVM.callMade
                              (valueWord := (⟨0⟩ : UInt256))
                              (cA' := cA') (σ' := σ') (g' := g'') (A' := A')
                              wordOfInt_zero.symm ?_ ?_ ?_ ?_
                            · refine ⟨callGas, A_in, ?_⟩
                              simpa [evmECall, initState, hperm, revealScratchSenderWord,
                                hAddressId, accountAddress_roundtrip] using hThetaEq
                            · rfl
                            · show (⟨0⟩ : UInt256) ≤ _
                              exact Fin.zero_le _
                            · intro hd'
                              apply hdepthEq
                              simpa [initState] using hd'
                          obtain ⟨σ'_solm, A'_solm, hcallSRaw, hPostAccounts⟩ :=
                            callViaEVM_initState_accountMapEquiv
                              (storage := blindAuctionConfig.storage) hcallE hAccounts
                              hOriginalAccounts
                          let evmSCall : EVM.State :=
                            { evmSolm with
                              accountMap := σ'_solm,
                              substate := A'_solm,
                              createdAccounts := evmECall.createdAccounts }
                          have hcallS :
                              callViaEVM evmSolm (EVM.address evmSolm.executionEnv.source)
                                0 ByteArray.empty (z, evmSCall, out) := by
                            simpa [evmSolm, evmSCall, evmECall, initState] using hcallSRaw
                          cases z
                          · have hbody :
                                ExecTransitionBody blindAuctionConfig blindAuctionContract
                                  evmSolm callargs revealTransition.body .reverted := by
                              have hbodyEmpty :
                                  ExecTransitionBody blindAuctionConfig blindAuctionContract
                                    evmSolm revealEmptyStore revealTransition.body .reverted :=
                                blindAuctionRevealBodyReverts_empty_callFailure evmSolm evmSCall
                                  out hwvSolm hafterBody hbeforeBody hlenZeroBody hcallS
                              simpa [hcallargsEmpty] using hbodyEmpty
                            by_cases hout0 : out.size = 0
                            · have houtEmpty : out = ByteArray.empty := by
                                apply ByteArray.ext
                                change out.data = #[]
                                exact Array.eq_empty_of_size_eq_zero (by
                                  change out.size = 0
                                  exact hout0)
                              have hrev : RDrev blindAuctionBytecode (Sat256.ofUInt256 g)
                                  (initState cA gh bl σ_evm σ₀_evm
                                    (Sat256.ofUInt256 g) A I) :=
                                blindAuctionRevealX_postCallEmpty_failure_revert
                                  (by simpa [houtEmpty] using rd1350)
                              exact hrev.reEquivExecutionRevert hcode hd hdec hbody
                            · obtain ⟨_, _, _, _, rd1405⟩ :=
                                blindAuctionRevealX_postCallNonempty_toRequire
                                  (by simpa using rd1350) hout0
                                  (lt_size_of_lt_sign hout255)
                              have hrev : RDrev blindAuctionBytecode (Sat256.ofUInt256 g)
                                  (initState cA gh bl σ_evm σ₀_evm
                                    (Sat256.ofUInt256 g) A I) :=
                                blindAuctionRevealX_postCallRequire_failure_revert
                                  (by simpa using rd1405)
                              exact hrev.reEquivExecutionRevert hcode hd hdec hbody
                          · have hbody :
                                ExecTransitionBody blindAuctionConfig blindAuctionContract
                                  evmSolm callargs revealTransition.body
                                (.returned
                                  { contract := blindAuctionContract,
                                    locals := revealCallStore ⟨0⟩ ⟨0⟩ true out }
                                  evmSCall none) := by
                              have hbodyEmpty :
                                  ExecTransitionBody blindAuctionConfig blindAuctionContract
                                    evmSolm revealEmptyStore revealTransition.body
                                    (.returned
                                      { contract := blindAuctionContract,
                                        locals := revealCallStore ⟨0⟩ ⟨0⟩ true out }
                                      evmSCall none) :=
                                blindAuctionRevealBodyReturns_empty_callSuccess evmSolm
                                  evmSCall out hwvSolm hafterBody hbeforeBody hlenZeroBody
                                  hcallS
                              simpa [hcallargsEmpty] using hbodyEmpty
                            by_cases hout0 : out.size = 0
                            · have houtEmpty : out = ByteArray.empty := by
                                apply ByteArray.ext
                                change out.data = #[]
                                exact Array.eq_empty_of_size_eq_zero (by
                                  change out.size = 0
                                  exact hout0)
                              have hret : RDret blindAuctionBytecode (Sat256.ofUInt256 g)
                                  (initState cA gh bl σ_evm σ₀_evm
                                    (Sat256.ofUInt256 g) A I)
                                  (cA', σ') ByteArray.empty :=
                                blindAuctionRevealX_postCallEmpty_success_stop
                                  (by simpa [houtEmpty] using rd1350)
                              exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec
                                hbody
                                (by rfl)
                                (by
                                  change accountMapEquiv σ' σ'_solm
                                  simpa [evmECall] using hPostAccounts)
                                (returnEquiv.void rfl rfl rfl)
                            · obtain ⟨_, _, _, _, rd1405⟩ :=
                                blindAuctionRevealX_postCallNonempty_toRequire
                                  (by simpa using rd1350) hout0
                                  (lt_size_of_lt_sign hout255)
                              have hret : RDret blindAuctionBytecode (Sat256.ofUInt256 g)
                                  (initState cA gh bl σ_evm σ₀_evm
                                    (Sat256.ofUInt256 g) A I)
                                  (cA', σ') ByteArray.empty :=
                                blindAuctionRevealX_postCallRequire_success_stop
                                  (by simpa using rd1405)
                              exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec
                                hbody
                                (by rfl)
                                (by
                                  change accountMapEquiv σ' σ'_solm
                                  simpa [evmECall] using hPostAccounts)
                                (returnEquiv.void rfl rfl rfl)
                      · sorry
                    · have hrev :=
                        blindAuctionRevealDecodeArrays1806_secretsLengthMismatch_reverts
                          (cA := cA) (σ := σ_evm) (I := I) (g := Sat256.ofUInt256 g)
                        rd1806 hvaluesGt hvaluesStart hvaluesLenLoad hvaluesLenMax
                        hvaluesEnd hfakesGt hfakesStart hfakesLenLoad hfakesLenMax
                        hfakesEnd hsecretsGt hsecretsStart hsecretsLenLoad hsecretsLenMax
                        hsecretsEnd hafter hbefore hvaluesEq hfakesEq hsecretsEq hbidsHash
                      have hsecretsNeNat :
                          secrets.length ≠ (revealScratchBidsLengthWord σ_solm I).toNat := by
                        intro hnat
                        apply hsecretsEq
                        apply u256_inj
                        rw [hbidsEq]
                        omega
                      have hbody :
                          ExecTransitionBody blindAuctionConfig blindAuctionContract evmSolm
                            callargs revealTransition.body .reverted := by
                        exact blindAuctionRevealBodyReverts_decoded_lengthMismatch
                          evmSolm hdec hvaluesGet hfakesGet hsecretsGet hwvSolm hafterBody
                          hbeforeBody hlenBody (Or.inr (Or.inr hsecretsNeNat))
                      exact hrev.reEquivExecutionRevert hcode hd hdec hbody
                  · have hrev :=
                      blindAuctionRevealDecodeArrays1806_fakesLengthMismatch_reverts
                        (cA := cA) (σ := σ_evm) (I := I) (g := Sat256.ofUInt256 g)
                        rd1806 hvaluesGt hvaluesStart hvaluesLenLoad hvaluesLenMax
                        hvaluesEnd hfakesGt hfakesStart hfakesLenLoad hfakesLenMax
                        hfakesEnd hsecretsGt hsecretsStart hsecretsLenLoad hsecretsLenMax
                        hsecretsEnd hafter hbefore hvaluesEq hfakesEq hbidsHash
                    have hfakesNeNat :
                        fakes.length ≠ (revealScratchBidsLengthWord σ_solm I).toNat := by
                      intro hnat
                      apply hfakesEq
                      apply u256_inj
                      rw [hbidsEq]
                      omega
                    have hbody :
                        ExecTransitionBody blindAuctionConfig blindAuctionContract evmSolm
                          callargs revealTransition.body .reverted := by
                      exact blindAuctionRevealBodyReverts_decoded_lengthMismatch
                        evmSolm hdec hvaluesGet hfakesGet hsecretsGet hwvSolm hafterBody
                        hbeforeBody hlenBody (Or.inr (Or.inl hfakesNeNat))
                    exact hrev.reEquivExecutionRevert hcode hd hdec hbody
                · have hrev :=
                    blindAuctionRevealDecodeArrays1806_valuesLengthMismatch_reverts
                      (cA := cA) (σ := σ_evm) (I := I) (g := Sat256.ofUInt256 g)
                      rd1806 hvaluesGt hvaluesStart hvaluesLenLoad hvaluesLenMax hvaluesEnd
                      hfakesGt hfakesStart hfakesLenLoad hfakesLenMax hfakesEnd
                      hsecretsGt hsecretsStart hsecretsLenLoad hsecretsLenMax hsecretsEnd
                      hafter hbefore hvaluesEq hbidsHash
                  have hvaluesNeNat :
                      values.length ≠ (revealScratchBidsLengthWord σ_solm I).toNat := by
                    intro hnat
                    apply hvaluesEq
                    apply u256_inj
                    rw [hbidsEq]
                    omega
                  have hbody :
                      ExecTransitionBody blindAuctionConfig blindAuctionContract evmSolm
                        callargs revealTransition.body .reverted := by
                    exact blindAuctionRevealBodyReverts_decoded_lengthMismatch
                      evmSolm hdec hvaluesGet hfakesGet hsecretsGet hwvSolm hafterBody
                      hbeforeBody hlenBody (Or.inl hvaluesNeNat)
                  exact hrev.reEquivExecutionRevert hcode hd hdec hbody
              · have hrev := blindAuctionRevealX_from887_tooLate
                    (cA := cA) (σ := σ_evm) (I := I) (g := Sat256.ofUInt256 g)
                    (s0 := initState cA gh bl σ_evm σ₀_evm (Sat256.ofUInt256 g) A I)
                    rd887 hafter (Nat.le_of_not_gt hbefore)
                have hafterBody :
                    (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨1⟩).toNat <
                      (UInt256.ofNat evmSolm.executionEnv.header.timestamp).toNat := by
                  change (revealScratchBiddingEndWord σ_solm I).toNat <
                    (revealScratchTimestampWord I).toNat
                  rw [← hbiddingEq]
                  exact hafter
                have hlateBody :
                    (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩).toNat ≤
                      (UInt256.ofNat evmSolm.executionEnv.header.timestamp).toNat := by
                  change (revealScratchRevealEndWord σ_solm I).toNat ≤
                    (revealScratchTimestampWord I).toNat
                  rw [← hrevealEq]
                  exact Nat.le_of_not_gt hbefore
                have hbody :
                    ExecTransitionBody blindAuctionConfig blindAuctionContract evmSolm
                      callargs revealTransition.body .reverted := by
                  exact blindAuctionRevealBodyReverts_tooLate hwvSolm hbiddingAbsent
                    hrevealAbsent hafterBody hlateBody
                exact hrev.reEquivExecutionRevert hcode hd hdec hbody
            · have hrev := blindAuctionRevealX_from887_tooEarly
                  (cA := cA) (σ := σ_evm) (I := I) (g := Sat256.ofUInt256 g)
                  (s0 := initState cA gh bl σ_evm σ₀_evm (Sat256.ofUInt256 g) A I)
                  rd887 (Nat.le_of_not_gt hafter)
              have htimeBody :
                  (UInt256.ofNat evmSolm.executionEnv.header.timestamp).toNat ≤
                    (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨1⟩).toNat := by
                change (revealScratchTimestampWord I).toNat ≤
                  (revealScratchBiddingEndWord σ_solm I).toNat
                rw [← hbiddingEq]
                exact Nat.le_of_not_gt hafter
              have hbody :
                  ExecTransitionBody blindAuctionConfig blindAuctionContract evmSolm
                    callargs revealTransition.body .reverted := by
                exact blindAuctionRevealBodyReverts_tooEarly hwvSolm hbiddingAbsent htimeBody
              exact hrev.reEquivExecutionRevert hcode hd hdec hbody
        · have hcalldataGe : 2 ^ 255 ≤ I.calldata.size := by omega
          have hdecNone := blindAuctionDecode_reveal_none_huge_dynamic (I := I) hcalldataGe
          have hrev :=
            blindAuctionRevealDecode1806_hugeDynamic_reverts
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀_evm)
              (A := A) (I := I) (g := Sat256.ofUInt256 g) rd1806 hcalldataGe hsize
          exact hrev.reEquivDecodingFailed hcode hd hdecNone
  · have hrev := blindAuctionX_reveal_nonpayable (g := Sat256.ofUInt256 g) hwv hreach
    by_cases hdecNone :
        decodeCalldata (revealTransition.params.map Param.name)
          (transitionSignature revealTransition).paramTypes I.calldata = none
    · exact hrev.reEquivDecodingFailed hcode hd hdecNone
    · obtain ⟨callargs, hdec⟩ := Option.ne_none_iff_exists'.mp hdecNone
      have hbody :
          ExecTransitionBody blindAuctionConfig blindAuctionContract
            (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I) callargs
            revealTransition.body .reverted := by
        exact blindAuctionRevealBodyReverts_nonpayable
          (by simp only [initState]; exact hwv)
      exact hrev.reEquivExecutionRevert hcode hd hdec hbody

end BlindAuction
