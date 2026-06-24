import Examples.SimpleAuction.Storage
import Reasoning.Refinement
import Reasoning.SolmBody
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace SimpleAuction

/-! ## `auctionEnd()` local bridge facts -/

def auctionEndTimestampWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.header.timestamp

def auctionEndAuctionEndWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)

def auctionEndBeneficiaryRawWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)

def auctionEndBeneficiaryWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (auctionEndBeneficiaryRawWord σ I) solcAddrMask

def auctionEndHighestBidderRawWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)

def auctionEndWinnerWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (auctionEndHighestBidderRawWord σ I) solcAddrMask

def auctionEndHighestBidWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨3⟩ ⟨0⟩)

def auctionEndEndedRawWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨5⟩ ⟨0⟩)

def auctionEndEndedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (auctionEndEndedRawWord σ I) ⟨255⟩

def auctionEndSetEndedWord (old : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land old (UInt256.lnot ⟨255⟩)) ⟨1⟩

def auctionEndAfterEndedMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨5⟩ (auctionEndSetEndedWord (auctionEndEndedRawWord σ I))

def auctionEndedTopic : UInt256 :=
  ⟨0xdaec4582d5d9595688c8c98545fdd1c696d41c6aeaeb636737e84ed2f5c00eda⟩

noncomputable def auctionEndEventMemWinner (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (auctionEndWinnerWord σ I)).write 0 solcFreePtrMem 128 32

noncomputable def auctionEndEventMem (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (auctionEndHighestBidWord σ I)).write 0
    (auctionEndEventMemWinner σ I) 160 32

theorem auctionEndEventMemWinner_size (σ : AccountMap) (I : ExecutionEnv) :
    (auctionEndEventMemWinner σ I).size = 160 := by
  simpa [auctionEndEventMemWinner, solcReturnMem] using
    solcReturnMem_size (auctionEndWinnerWord σ I)

theorem auctionEndEventMem_size (σ : AccountMap) (I : ExecutionEnv) :
    (auctionEndEventMem σ I).size = 192 := by
  unfold auctionEndEventMem
  rw [toByteArray_write_eq _ _ 160 (by rw [auctionEndEventMemWinner_size])
      (by rw [auctionEndEventMemWinner_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, auctionEndEventMemWinner_size,
    zeroes_ofNat_size _ (by norm_num), toByteArray_size]

theorem auctionEndEventMem_read64 (σ : AccountMap) (I : ExecutionEnv) :
    (auctionEndEventMem σ I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold auctionEndEventMem
  rw [write32_read_below _ _ 160 64 (by rw [toByteArray_size])
    (by rw [auctionEndEventMemWinner_size]) (by omega)]
  simpa [auctionEndEventMemWinner, solcReturnMem] using
    solcReturnMem_read64 (auctionEndWinnerWord σ I)

theorem auctionEndEventMem_mload64 (σ : AccountMap) (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (auctionEndEventMem σ I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((auctionEndEventMem σ I).readWithPadding
         (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
  mloadFreePtrValue (by rw [auctionEndEventMem_size]; decide) (by decide)
    (auctionEndEventMem_read64 σ I)

theorem auctionEnd_write_len_zero (src base : ByteArray) (sa da : ℕ) :
    src.write sa base da 0 = base := by
  unfold ByteArray.write
  simp

theorem auctionEnd_readWithPadding_zero (mem : ByteArray) (addr : ℕ) :
    mem.readWithPadding addr 0 = ByteArray.empty := by
  unfold ByteArray.readWithPadding ByteArray.readWithoutPadding
  by_cases h : addr ≥ mem.size
  · simp [h]
    exact zeroes_zero (n := (OfNat.ofNat 0 : USize)) (by rfl)
  · simp [h]
    exact zeroes_zero (n := (OfNat.ofNat 0 : USize)) (by rfl)

-- PROMOTE -> Reasoning.EVMWord.
theorem auctionEndNat_lor_comm (a b : ℕ) : Nat.lor a b = Nat.lor b a := by
  apply Nat.eq_of_testBit_eq
  intro i
  show (a ||| b).testBit i = (b ||| a).testBit i
  rw [Nat.testBit_or, Nat.testBit_or, Bool.or_comm]

-- PROMOTE -> Reasoning.EVMWord.
theorem auctionEndU256_lor_comm (a b : UInt256) : UInt256.lor a b = UInt256.lor b a := by
  apply u256_inj
  show Nat.lor a.toNat b.toNat % UInt256.size =
    Nat.lor b.toNat a.toNat % UInt256.size
  rw [auctionEndNat_lor_comm]

-- PROMOTE -> Reasoning.Stepping / Reasoning.Reach: generic OR combinator.
theorem auctionEndOr_xstep {s : State} {code : ByteArray} {pcv a b : UInt256}
    {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.OR, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stBinop s (UInt256.lor a b) t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.OR, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_or s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 1 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stBinop]

-- PROMOTE -> Reasoning.Stepping / Reasoning.Reach: generic OR combinator.
theorem auctionEndRDOr {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.OR, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.lor a b :: t) mem aw rdata acc (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => auctionEndOr_xstep hc hp hdec hs hov)

-- PROMOTE -> Reasoning.Reach: one-step RETURNDATACOPY with caller-provided memory shape.
theorem auctionEndRDReturndatacopy {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c : UInt256} {t : List UInt256} (mcost : ℕ)
    (memout : ByteArray) (awout : UInt256)
    (h : RD code ee g s0 pc (a :: b :: c :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.RETURNDATACOPY, .none))
    (hguard : b.toNat + c.toNat ≤ rdata.size)
    (hmc : ∀ s : State, s.machineState.activeWords = aw → s.machineState.stack = a :: b :: c :: t →
        memoryExpansionCost s .RETURNDATACOPY = mcost)
    (hmemout : rdata.write b.toNat mem a.toNat c.toNat = memout)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat c.toNat) = awout)
    (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t memout awout rdata acc
      (k + 1) (C + (mcost + (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)))) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have hmcS : memoryExpansionCost s .RETURNDATACOPY = mcost := hmc s haw hstk
    have hmemok : ¬ b.toNat + c.toNat > s.machineState.returnData.size := by
      rw [hrdata]
      omega
    have st := returndatacopy_xstep hcode hpc hdec hstk hmemok hov
    rw [hmcS] at st
    rw [collapse_two_stage] at st
    by_cases gg : g.toNat < C + (mcost + (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)))
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · have hcost_pos :
          0 < mcost + (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)) := by
        simp [GasConstants.Gverylow]
      refine Or.inr ⟨stReturndatacopy s a b c t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega,
          by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stReturndatacopy]; exact hcode
      · simp only [stReturndatacopy]; rw [hpc]
      · rfl
      · simp only [stReturndatacopy, hmcS]
        rw [hgas, Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stReturndatacopy]; rw [hmem, hrdata, hmemout]
      · simp only [stReturndatacopy]; rw [haw, hawout]
      · simp only [stReturndatacopy]; exact hrdata
      · simp only [stReturndatacopy]; exact hacc
      · exact hee
      · exact hworld

-- PROMOTE -> Reasoning.Stepping / Reasoning.Reach: generic TIMESTAMP combinator.
def auctionEndStTimestamp (s : State) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩,
      stack := UInt256.ofNat s.executionEnv.header.timestamp :: s.machineState.stack,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable.subNat 2 } }

theorem auctionEndTimestamp_xstep {s : State} {code : ByteArray} {pcv : UInt256}
    {rest : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.TIMESTAMP, .none))
    (hstk : s.machineState.stack = rest) (hov : rest.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 2 then .error .OutOfGass
         else .ok (auctionEndStTimestamp s, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.TIMESTAMP, .none) := by
    rw [hcode, hpc]
    exact hdec
  have hov' : ¬ (s.machineState.stack.length - 0 + 1 > 1024) := by
    rw [hstk]
    omega
  rw [← hcode, step_timestamp s hd, if_neg hov']
  simp only [GasConstants.Gbase, auctionEndStTimestamp]

theorem auctionEndRDTimestamp {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C)
    (hdec : decode code pc = some (.TIMESTAMP, .none)) (hov : stk.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.ofNat ee.header.timestamp :: stk) mem aw rdata acc
      (k + 1) (C + 2) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have st := auctionEndTimestamp_xstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 2
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨auctionEndStTimestamp s,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega,
          by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [auctionEndStTimestamp]; exact hcode
      · simp only [auctionEndStTimestamp]; rw [hpc]
      · simp only [auctionEndStTimestamp]; rw [hee, hstk]
      · simp only [auctionEndStTimestamp]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [auctionEndStTimestamp]; exact hmem
      · simp only [auctionEndStTimestamp]; exact haw
      · simp only [auctionEndStTimestamp]; exact hrdata
      · simp only [auctionEndStTimestamp]; exact hacc
      · exact hee
      · exact hworld

theorem simpleAuctionAuctionEndSelector_size {I : ExecutionEnv}
    (hsel : ((⟨#[0x2a, 0x24, 0xf4, 0x6c]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x2a, 0x24, 0xf4, 0x6c]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem simpleAuctionDispatch_auctionEnd {cd : ByteArray}
    (hsel : ((⟨#[0x2a, 0x24, 0xf4, 0x6c]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg simpleAuctionContract cd = some auctionEndTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x2a, 0x24, 0xf4, 0x6c]⟩ : ByteArray) :=
    (simpleAuctionByteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [bidTransition, withdrawTransition])
    (post := [beneficiaryGetter, auctionEndTimeGetter, highestBidderGetter, highestBidGetter])
    rfl ?_ (by rw [selectorOf, simpleAuctionAuctionEndSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · rw [selectorOf, simpleAuctionBidSelectorBytes, hcd]; decide
  · rw [selectorOf, simpleAuctionWithdrawSelectorBytes, hcd]; decide

theorem simpleAuctionDecode_auctionEnd {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (auctionEndTransition.params.map Param.name)
      (transitionSignature auctionEndTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem simpleAuctionAuctionEndBodyReverts_nonpayable {evm : EVM.State} {locals : Store}
    (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody simpleAuctionConfig simpleAuctionContract evm locals
      auctionEndTransition.body .reverted := by
  exact bodyReverts_nonPayable h

theorem simpleAuctionX_auctionEnd_nonpayable {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue ≠ ⟨0⟩)
    (hreach : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨124⟩ [simpleAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev simpleAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd124⟩ := hreach
  have rd132 := evm_run rd124 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨135⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv)]
  exact rd132.revertStub (by decide) (by decide) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem simpleAuctionX_auctionEndToBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨124⟩ [simpleAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨555⟩
      [⟨122⟩, simpleAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd124⟩ := hreach
  exact ⟨_, _, evm_run rd124 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨135⟩,
    jumpiT (by rw [hwv]; decide) (by jump_dest),
    jumpdest, pop, push2 ⟨122⟩, push2 ⟨555⟩, jump (by jump_dest)]⟩

theorem simpleAuctionX_auctionEnd_timeRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨124⟩ [simpleAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (htime : (auctionEndTimestampWord I).toNat < (auctionEndAuctionEndWord σ I).toNat) :
    RDrev simpleAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd555⟩ := simpleAuctionX_auctionEndToBody (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hreach
  have rd558 := evm_run rd555 with [jumpdest, push1 ⟨1⟩]
  obtain ⟨_, _, rd559₀⟩ := rd558.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd559⟩ : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨559⟩
      [auctionEndAuctionEndWord σ I, ⟨122⟩, simpleAuctionSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionEndAuctionEndWord, initState] using rd559₀⟩
  have hlt : UInt256.lt (auctionEndTimestampWord I) (auctionEndAuctionEndWord σ I) = ⟨1⟩ :=
    ult_one htime
  have rd560 := auctionEndRDTimestamp rd559 (by decide) (by evm_ov)
  have rd562₀ := evm_run rd560 with [lt, iszero]
  have rd562 := rd562₀
  rw [show UInt256.lt (UInt256.ofNat I.header.timestamp) (auctionEndAuctionEndWord σ I) =
      ⟨1⟩ from by simpa [auctionEndTimestampWord] using hlt,
    show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd562
  have rd566 := evm_run rd562 with [push2 ⟨590⟩, jumpiNT (by decide)]
  let errSel : UInt256 := UInt256.shiftLeft (⟨0x044cee29⟩ : UInt256) ⟨228⟩
  have rd579 := evm_run rd566 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push4 ⟨0x044cee29⟩, push1 ⟨228⟩, shl, dup2,
    raw mstore 6 (solcReturnMem errSel) (UInt256.ofNat 5) (by decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov)]
  have rd589 := evm_run rd579 with [
    push1 ⟨4⟩, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost (solcReturnMem_mload64 errSel) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  exact rd589.rev 0 (by decide) mem_cost (by evm_ov)

theorem simpleAuctionX_auctionEnd_afterTime {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨124⟩ [simpleAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (htime : (auctionEndAuctionEndWord σ I).toNat ≤ (auctionEndTimestampWord I).toNat) :
    ∃ k C, RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨590⟩
      [⟨122⟩, simpleAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd555⟩ := simpleAuctionX_auctionEndToBody (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hreach
  have rd558 := evm_run rd555 with [jumpdest, push1 ⟨1⟩]
  obtain ⟨_, _, rd559₀⟩ := rd558.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd559⟩ : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨559⟩
      [auctionEndAuctionEndWord σ I, ⟨122⟩, simpleAuctionSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionEndAuctionEndWord, initState] using rd559₀⟩
  have hlt : UInt256.lt (auctionEndTimestampWord I) (auctionEndAuctionEndWord σ I) = ⟨0⟩ :=
    ult_zero htime
  have rd560 := auctionEndRDTimestamp rd559 (by decide) (by evm_ov)
  have rd562₀ := evm_run rd560 with [lt, iszero]
  have rd562 := rd562₀
  rw [show UInt256.lt (UInt256.ofNat I.header.timestamp) (auctionEndAuctionEndWord σ I) =
      ⟨0⟩ from by simpa [auctionEndTimestampWord] using hlt,
    show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd562
  exact ⟨_, _, evm_run rd562 with [push2 ⟨590⟩, jumpiT one_ne_zero_uint (by jump_dest)]⟩

theorem simpleAuctionX_auctionEnd_endedRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨124⟩ [simpleAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (htime : (auctionEndAuctionEndWord σ I).toNat ≤ (auctionEndTimestampWord I).toNat)
    (hended : auctionEndEndedWord σ I ≠ ⟨0⟩) :
    RDrev simpleAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd590⟩ := simpleAuctionX_auctionEnd_afterTime (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hreach htime
  have rd593 := evm_run rd590 with [jumpdest, push1 ⟨5⟩]
  obtain ⟨_, _, rd594₀⟩ := rd593.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd594⟩ : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨594⟩
      [auctionEndEndedRawWord σ I, ⟨122⟩, simpleAuctionSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionEndEndedRawWord, initState] using rd594₀⟩
  have rd598₀ := evm_run rd594 with [push1 ⟨255⟩, and, iszero]
  have rd598 := rd598₀
  have hmask : UInt256.land ⟨255⟩ (auctionEndEndedRawWord σ I) =
      auctionEndEndedWord σ I := by
    rw [simpleAuctionU256_land_comm ⟨255⟩ (auctionEndEndedRawWord σ I)]
    rfl
  rw [hmask, isZero_eq_zero_of_ne hended] at rd598
  have rd602 := evm_run rd598 with [push2 ⟨626⟩, jumpiNT (by decide)]
  let errSel : UInt256 := UInt256.shiftLeft (⟨0x0c39fb9f⟩ : UInt256) ⟨227⟩
  have rd615 := evm_run rd602 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push4 ⟨0x0c39fb9f⟩, push1 ⟨227⟩, shl, dup2,
    raw mstore 6 (solcReturnMem errSel) (UInt256.ofNat 5) (by decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov)]
  have rd625 := evm_run rd615 with [
    push1 ⟨4⟩, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost (solcReturnMem_mload64 errSel) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  exact rd625.rev 0 (by decide) mem_cost (by evm_ov)

theorem simpleAuctionX_auctionEnd_afterNotEnded {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨124⟩ [simpleAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (htime : (auctionEndAuctionEndWord σ I).toNat ≤ (auctionEndTimestampWord I).toNat)
    (hended : auctionEndEndedWord σ I = ⟨0⟩) :
    ∃ k C, RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨626⟩
      [⟨122⟩, simpleAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd590⟩ := simpleAuctionX_auctionEnd_afterTime (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hreach htime
  have rd593 := evm_run rd590 with [jumpdest, push1 ⟨5⟩]
  obtain ⟨_, _, rd594₀⟩ := rd593.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd594⟩ : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨594⟩
      [auctionEndEndedRawWord σ I, ⟨122⟩, simpleAuctionSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionEndEndedRawWord, initState] using rd594₀⟩
  have rd598₀ := evm_run rd594 with [push1 ⟨255⟩, and, iszero]
  have rd598 := rd598₀
  have hmask : UInt256.land ⟨255⟩ (auctionEndEndedRawWord σ I) =
      auctionEndEndedWord σ I := by
    rw [simpleAuctionU256_land_comm ⟨255⟩ (auctionEndEndedRawWord σ I)]
    rfl
  rw [hmask, hended, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd598
  exact ⟨_, _, evm_run rd598 with [push2 ⟨626⟩, jumpiT one_ne_zero_uint (by jump_dest)]⟩

theorem simpleAuctionX_auctionEnd_afterStoreAndLog {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨124⟩ [simpleAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (htime : (auctionEndAuctionEndWord σ I).toNat ≤ (auctionEndTimestampWord I).toNat)
    (hended : auctionEndEndedWord σ I = ⟨0⟩) :
    ∃ k C, RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨714⟩
      [⟨122⟩, simpleAuctionSelWord I]
      (auctionEndEventMem (auctionEndAfterEndedMap σ I) I) (UInt256.ofNat 6)
      ByteArray.empty (cA, auctionEndAfterEndedMap σ I) k C := by
  obtain ⟨_, _, rd626⟩ := simpleAuctionX_auctionEnd_afterNotEnded (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hreach htime hended
  have rd630 := evm_run rd626 with [jumpdest, push1 ⟨5⟩, dup1]
  obtain ⟨_, _, rd631₀⟩ := rd630.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd631⟩ : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨631⟩
      [auctionEndEndedRawWord σ I, ⟨5⟩, ⟨122⟩, simpleAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionEndEndedRawWord, initState] using rd631₀⟩
  have rd635₀ := evm_run rd631 with [push1 ⟨255⟩, not, and, push1 ⟨1⟩]
  have rd635 := rd635₀
  have hland : UInt256.land (UInt256.lnot ⟨255⟩) (auctionEndEndedRawWord σ I) =
      UInt256.land (auctionEndEndedRawWord σ I) (UInt256.lnot ⟨255⟩) := by
    exact simpleAuctionU256_land_comm (UInt256.lnot ⟨255⟩) (auctionEndEndedRawWord σ I)
  rw [hland] at rd635
  have rd638₀ := auctionEndRDOr rd635 (by decide) (by evm_ov)
  have rd638 := rd638₀
  have hlor : UInt256.lor ⟨1⟩
        (UInt256.land (auctionEndEndedRawWord σ I) (UInt256.lnot ⟨255⟩)) =
      auctionEndSetEndedWord (auctionEndEndedRawWord σ I) := by
    unfold auctionEndSetEndedWord
    exact auctionEndU256_lor_comm ⟨1⟩
      (UInt256.land (auctionEndEndedRawWord σ I) (UInt256.lnot ⟨255⟩))
  rw [hlor] at rd638
  have rd639 := evm_run rd638 with [swap1]
  obtain ⟨_, _, rd640₀⟩ := rd639.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd640⟩ : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨640⟩
      [⟨122⟩, simpleAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, auctionEndAfterEndedMap σ I) k C := by
    exact ⟨_, _, by simpa [auctionEndAfterEndedMap] using rd640₀⟩
  let σa := auctionEndAfterEndedMap σ I
  have rd642 := evm_run rd640 with [push1 ⟨2⟩]
  obtain ⟨_, _, rd643₀⟩ := rd642.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd643⟩ : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨643⟩
      [auctionEndHighestBidderRawWord σa I, ⟨122⟩, simpleAuctionSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σa) k C := by
    exact ⟨_, _, by simpa [σa, auctionEndHighestBidderRawWord] using rd643₀⟩
  have rd645 := evm_run rd643 with [push1 ⟨3⟩]
  obtain ⟨_, _, rd646₀⟩ := rd645.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd646⟩ : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨646⟩
      [auctionEndHighestBidWord σa I, auctionEndHighestBidderRawWord σa I,
        ⟨122⟩, simpleAuctionSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σa) k C := by
    exact ⟨_, _, by simpa [σa, auctionEndHighestBidWord] using rd646₀⟩
  have rd649 := evm_run rd646 with [
    push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov)]
  have rd660₀ := evm_run rd649 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap1, swap4, and]
  have rd660 := rd660₀
  have haddrMask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask := by
    decide
  rw [haddrMask] at rd660
  have rd662 := evm_run rd660 with [
    dup4,
    raw mstore 6 (auctionEndEventMemWinner σa I) (UInt256.ofNat 5) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd670 := evm_run rd662 with [
    push1 ⟨32⟩, dup4, add, swap2, swap1, swap2,
    raw mstore 3 (auctionEndEventMem σa I) (UInt256.ofNat 6) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd704 := rd670.pushConst auctionEndedTopic (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd713 := evm_run rd704 with [
    swap2, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (auctionEndEventMem_mload64 σa I) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have hlen64 : ((⟨128⟩ : UInt256) + ⟨64⟩).sub ⟨128⟩ = ⟨64⟩ := by
    decide
  have rd713' := rd713
  rw [hlen64] at rd713'
  have rd714 := RD.log1 0 (UInt256.ofNat 6) rd713' (by decide) hperm
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      native_decide)
    (by decide) (by evm_ov)
  exact ⟨_, _, by simpa [σa] using rd714⟩

theorem simpleAuctionX_auctionEnd_toCall {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨124⟩ [simpleAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (htime : (auctionEndAuctionEndWord σ I).toNat ≤ (auctionEndTimestampWord I).toNat)
    (hended : auctionEndEndedWord σ I = ⟨0⟩) :
    ∃ gasArg k C, RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨742⟩
      [gasArg, auctionEndBeneficiaryWord (auctionEndAfterEndedMap σ I) I,
        auctionEndHighestBidWord (auctionEndAfterEndedMap σ I) I,
        ⟨128⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨128⟩,
        auctionEndHighestBidWord (auctionEndAfterEndedMap σ I) I,
        auctionEndBeneficiaryWord (auctionEndAfterEndedMap σ I) I,
        ⟨0⟩, ⟨122⟩, simpleAuctionSelWord I]
      (auctionEndEventMem (auctionEndAfterEndedMap σ I) I) (UInt256.ofNat 6)
      ByteArray.empty (cA, auctionEndAfterEndedMap σ I) k C := by
  obtain ⟨_, _, rd714⟩ := simpleAuctionX_auctionEnd_afterStoreAndLog (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hperm hwv hreach htime hended
  let σa := auctionEndAfterEndedMap σ I
  have rd716 := evm_run rd714 with [push0, dup1]
  obtain ⟨_, _, rd717₀⟩ := rd716.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd717⟩ : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨717⟩
      [auctionEndBeneficiaryRawWord σa I, ⟨0⟩, ⟨122⟩, simpleAuctionSelWord I]
      (auctionEndEventMem σa I) (UInt256.ofNat 6) ByteArray.empty (cA, σa) k C := by
    exact ⟨_, _, by simpa [σa, auctionEndBeneficiaryRawWord] using rd717₀⟩
  have rd719 := evm_run rd717 with [push1 ⟨3⟩]
  obtain ⟨_, _, rd720₀⟩ := rd719.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd720⟩ : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨720⟩
      [auctionEndHighestBidWord σa I, auctionEndBeneficiaryRawWord σa I,
        ⟨0⟩, ⟨122⟩, simpleAuctionSelWord I]
      (auctionEndEventMem σa I) (UInt256.ofNat 6) ByteArray.empty (cA, σa) k C := by
    exact ⟨_, _, by simpa [σa, auctionEndHighestBidWord] using rd720₀⟩
  have rd723 := evm_run rd720 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (auctionEndEventMem_mload64 σa I) (by decide) (by evm_ov)]
  have rd734₀ := evm_run rd723 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap1, swap3, and]
  have rd734 := rd734₀
  have haddrMask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask := by
    decide
  rw [haddrMask] at rd734
  have rd741 := evm_run rd734 with [swap2, dup4, dup2, dup2, dup2, dup6, dup8]
  obtain ⟨gasArg, rd742⟩ := rd741.gas (by decide) (by evm_ov)
  exact ⟨gasArg, _, _, by simpa [σa] using rd742⟩

theorem simpleAuctionX_auctionEnd_postCallEmpty_toRequire {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {aw : UInt256} {k C : ℕ} {z high benef : UInt256}
    (rd : RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨743⟩
      [z, ⟨128⟩, high, benef, ⟨0⟩, ⟨122⟩, simpleAuctionSelWord I]
      mem aw ByteArray.empty acc k C) :
    ∃ k' C', RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨798⟩
      [z, ⟨122⟩, simpleAuctionSelWord I] mem aw ByteArray.empty acc k' C' := by
  refine ⟨_, _, evm_run rd with [
    swap3, pop, pop, pop,
    returndatasize, dup1, push0, dup2, eq, push2 ⟨788⟩,
    jumpiT (by decide) (by jump_dest),
    jumpdest, push1 ⟨96⟩, swap2, pop,
    jumpdest, pop, pop, swap1, pop]⟩

theorem simpleAuctionX_auctionEnd_postCallNonempty_toRequire {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {k C : ℕ} {z high benef : UInt256} {o : ByteArray}
    (rd : RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨743⟩
      [z, ⟨128⟩, high, benef, ⟨0⟩, ⟨122⟩, simpleAuctionSelWord I]
      mem (UInt256.ofNat 6) o acc k C)
    (hfp : (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (ho0 : o.size ≠ 0) (hosz : o.size < UInt256.size) :
    ∃ mem' aw' k' C', RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨798⟩
      [z, ⟨122⟩, simpleAuctionSelWord I] mem' aw' o acc k' C' := by
  let rdsz : UInt256 := UInt256.ofNat o.size
  have hrdsz_toNat : rdsz.toNat = o.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt hosz
  have hrdsz_ne : rdsz ≠ ⟨0⟩ := by
    intro h
    have hnat : rdsz.toNat = 0 := by rw [h]; rfl
    exact ho0 (by rwa [hrdsz_toNat] at hnat)
  have heq0 : UInt256.eq rdsz (⟨0⟩ : UInt256) = ⟨0⟩ := u256_eq_of_ne hrdsz_ne
  have rd752₀ := evm_run rd with [swap3, pop, pop, pop, returndatasize, dup1, push0, dup2, eq]
  have rd752 := rd752₀
  change UInt256.eq rdsz (⟨0⟩ : UInt256) = ⟨0⟩ at heq0
  rw [show UInt256.ofNat o.size = rdsz from rfl, heq0] at rd752
  have rd756 := evm_run rd752 with [push2 ⟨788⟩, jumpiNT (by decide)]
  let rounded : UInt256 := UInt256.land (UInt256.add rdsz ⟨63⟩) (UInt256.lnot ⟨31⟩)
  let mem2 : ByteArray := (UInt256.toByteArray (UInt256.add ⟨128⟩ rounded)).write 0 mem 64 32
  have rd774 := evm_run rd756 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost hfp (by decide) (by evm_ov),
    swap2, pop, push1 ⟨31⟩, not, push1 ⟨63⟩, returndatasize, add, and, dup3, add,
    push1 ⟨64⟩,
    raw mstore 0 mem2 (UInt256.ofNat 6) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  let mem3 : ByteArray := (UInt256.toByteArray rdsz).write 0 mem2 128 32
  have rd777 := evm_run rd774 with [
    returndatasize, dup3,
    raw mstore 0 mem3 (UInt256.ofNat 6) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd783 := evm_run rd777 with [returndatasize, push0, push1 ⟨32⟩, dup5, add]
  let copyDest : UInt256 := (⟨128⟩ : UInt256) + ⟨32⟩
  let copyLen : UInt256 := UInt256.ofNat o.size
  have hcopyLen_toNat : copyLen.toNat = o.size := by
    simpa [copyLen] using UInt256.toNat_ofNat_of_lt hosz
  let mem4 : ByteArray := o.write 0 mem3 copyDest.toNat copyLen.toNat
  have rd784 := auctionEndRDReturndatacopy
    (Cₘ (UInt256.ofNat (MachineState.M (UInt256.ofNat 6).toNat
      copyDest.toNat copyLen.toNat)) - Cₘ (UInt256.ofNat 6))
    mem4
    (UInt256.ofNat (MachineState.M (UInt256.ofNat 6).toNat copyDest.toNat copyLen.toNat))
    rd783 (by decide)
    (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, hcopyLen_toNat]; omega)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, copyDest, copyLen])
    (by rfl)
    (by rfl)
    (by evm_ov)
  have rd793 := evm_run rd784 with [push2 ⟨793⟩, jump (by jump_dest), jumpdest]
  exact ⟨_, _, _, _, evm_run rd793 with [pop, pop, swap1, pop]⟩

theorem simpleAuctionX_auctionEnd_requireSuccess_return {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : ℕ}
    (rd : RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨798⟩
      [⟨1⟩, ⟨122⟩, simpleAuctionSelWord I] mem aw rdata acc k C) :
    RDret simpleAuctionBytecode g (initState cA gh bl σ σ₀ g A I) acc ByteArray.empty := by
  have rd122 := evm_run rd with [
    dup1, push2 ⟨806⟩, jumpiT (by decide) (by jump_dest),
    jumpdest, pop, jump (by jump_dest), jumpdest]
  exact rd122.stop (by decide) (by evm_ov)

theorem simpleAuctionX_auctionEnd_requireSuccess_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : ℕ}
    (rd : RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨798⟩
      [⟨0⟩, ⟨122⟩, simpleAuctionSelWord I] mem aw rdata acc k C) :
    RDrev simpleAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd803 := evm_run rd with [dup1, push2 ⟨806⟩, jumpiNT (by decide), push0, push0]
  exact RD.rev _ rd803 (by decide)
    (fun s haws hstks => by rw [memExpRevertZeroOff s hstks, haws])
    (by evm_ov)

theorem simpleAuctionX_auctionEnd_callMade {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨124⟩ [simpleAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (htime : (auctionEndAuctionEndWord σ I).toNat ≤ (auctionEndTimestampWord I).toNat)
    (hended : auctionEndEndedWord σ I = ⟨0⟩)
    (hbalance : auctionEndHighestBidWord (auctionEndAfterEndedMap σ I) I ≤
      (auctionEndAfterEndedMap σ I |>.find? I.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k C : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA
          (initState cA gh bl σ σ₀ g A I).genesisBlockHeader
          (initState cA gh bl σ σ₀ g A I).blocks
          (auctionEndAfterEndedMap σ I) (initState cA gh bl σ σ₀ g A I).σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (auctionEndBeneficiaryWord (auctionEndAfterEndedMap σ I) I))
          (toExecute (auctionEndAfterEndedMap σ I)
            (AccountAddress.ofUInt256 (auctionEndBeneficiaryWord (auctionEndAfterEndedMap σ I) I)))
          callGas (UInt256.ofNat I.gasPrice)
          (auctionEndHighestBidWord (auctionEndAfterEndedMap σ I) I)
          (auctionEndHighestBidWord (auctionEndAfterEndedMap σ I) I)
          ByteArray.empty (I.depth + 1) I.header I.perm)
      ∧ RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨743⟩
          [(if z then ⟨1⟩ else ⟨0⟩), ⟨128⟩,
            auctionEndHighestBidWord (auctionEndAfterEndedMap σ I) I,
            auctionEndBeneficiaryWord (auctionEndAfterEndedMap σ I) I,
            ⟨0⟩, ⟨122⟩, simpleAuctionSelWord I]
          (auctionEndEventMem (auctionEndAfterEndedMap σ I) I) (UInt256.ofNat 6) o
          (cA', σ') k C := by
  obtain ⟨gasArg, _, _, rd742⟩ := simpleAuctionX_auctionEnd_toCall (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hperm hwv hreach htime hended
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ, rd743₀, _hosz⟩ :=
    rd742.callValueMade (by decide) hperm hbalance hdepth (by evm_ov)
  have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat o.size := by
      show (0 : Nat) ≤ (UInt256.ofNat o.size).val.val
      exact Nat.zero_le _
    simp [min, hle]
  have hcd : (auctionEndEventMem (auctionEndAfterEndedMap σ I) I).readWithPadding
      (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat = ByteArray.empty := by
    exact auctionEnd_readWithPadding_zero _ _
  have hΘ' : ∃ (g'' : UInt256) (A' : Substate),
      (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA
        (initState cA gh bl σ σ₀ g A I).genesisBlockHeader
        (initState cA gh bl σ σ₀ g A I).blocks
        (auctionEndAfterEndedMap σ I) (initState cA gh bl σ σ₀ g A I).σ₀ A_in
        (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
        (AccountAddress.ofUInt256 (auctionEndBeneficiaryWord (auctionEndAfterEndedMap σ I) I))
        (toExecute (auctionEndAfterEndedMap σ I)
          (AccountAddress.ofUInt256 (auctionEndBeneficiaryWord (auctionEndAfterEndedMap σ I) I)))
        callGas (UInt256.ofNat I.gasPrice)
        (auctionEndHighestBidWord (auctionEndAfterEndedMap σ I) I)
        (auctionEndHighestBidWord (auctionEndAfterEndedMap σ I) I)
        ByteArray.empty (I.depth + 1) I.header I.perm := by
    rcases hΘ with ⟨g'', A', hΘeq⟩
    refine ⟨g'', A', ?_⟩
    rw [hcd] at hΘeq
    exact hΘeq
  have haw : UInt256.ofNat
      (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat (⟨128⟩ : UInt256).toNat
        (⟨0⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) =
      (UInt256.ofNat 6) := by
    decide
  refine ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ', ?_⟩
  rw [hmin, auctionEnd_write_len_zero, haw] at rd743₀
  simpa [initState] using rd743₀

theorem simpleAuctionX_auctionEnd_callDepthRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨124⟩ [simpleAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (htime : (auctionEndAuctionEndWord σ I).toNat ≤ (auctionEndTimestampWord I).toNat)
    (hended : auctionEndEndedWord σ I = ⟨0⟩)
    (hdepth : I.depth = 1024) :
    RDrev simpleAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨gasArg, _, _, rd742⟩ := simpleAuctionX_auctionEnd_toCall (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hperm hwv hreach htime hended
  obtain ⟨_, _, rd743⟩ := rd742.callValueDepthLimit hperm (by decide) hdepth (by evm_ov)
  obtain ⟨_, _, rd798⟩ :=
    simpleAuctionX_auctionEnd_postCallEmpty_toRequire (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) rd743
  exact simpleAuctionX_auctionEnd_requireSuccess_revert rd798

-- PROMOTE -> Reasoning.Reach: value-parametric no-call-made branch for insufficient balance.
set_option maxHeartbeats 1000000 in
theorem auctionEndRDCallValueInsufficientBalance {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {k C : ℕ} {gasArg target value inOffset inSize outOffset outSize : UInt256}
    {t : List UInt256}
    (h : RD code ee g s0 pc
          (gasArg :: target :: value :: inOffset :: inSize :: outOffset :: outSize :: t)
          mem aw rdata (cA, σ) k C)
    (hperm : ee.perm = true)
    (hdec : decode code pc = some (.CALL, .none))
    (hbalance : ¬ value ≤ (σ.find? ee.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hdepth : ee.depth.val < 1024)
    (hov : t.length + 1 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (pc + ⟨1⟩) (⟨0⟩ :: t)
        (ByteArray.empty.write 0 mem outOffset.toNat
          (min outSize (UInt256.ofNat ByteArray.empty.size)).toNat)
        (UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat inSize.toNat)
          outOffset.toNat outSize.toNat))
        ByteArray.empty (cA, σ) k' C' := by
  unfold RD at h
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact ⟨k, C, by unfold RD; exact Or.inl hoog⟩
  · have hd : decode s.executionEnv.code s.machineState.pc = some (.CALL, .none) := by
      rw [hcode, hpc]; exact hdec
    have hperm' : s.executionEnv.perm = true := by rw [hee]; exact hperm
    have hdepth' : s.executionEnv.depth.val < 1024 := by rw [hee]; exact hdepth
    have st := step_call s hd
    rw [hstk] at st
    have hovF : (t.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 7 + 1 > 1024) = False :=
      eq_false (by omega)
    have hstaticF : (¬ s.executionEnv.perm = true ∧ value ≠ ({ val := 0 } : UInt256)) = False :=
      eq_false (by rintro ⟨hp, _⟩; exact hp hperm')
    have hdepthLt : s.executionEnv.depth < 1024 := by
      rw [Fin.lt_def]; exact hdepth'
    have hcA : s.createdAccounts = cA := congrArg Prod.fst hacc
    have hσ : s.accountMap = σ := congrArg Prod.snd hacc
    have hbalOpt :
        (value ≤ Option.option ⟨0⟩ (fun x => x.balance)
            (Batteries.RBMap.find? s.accountMap s.executionEnv.codeOwner)) = False := by
      rw [hee, hσ]
      rw [show Option.option ⟨0⟩ (fun x => x.balance)
          (Batteries.RBMap.find? σ ee.codeOwner) =
          (σ.find? ee.codeOwner |>.elim ⟨0⟩ (·.balance)) by
        cases Batteries.RBMap.find? σ ee.codeOwner <;> rfl]
      exact eq_false hbalance
    have hgtT :
        (value > (s.accountMap.find? s.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance))) =
          True := by
      rw [hee, hσ]
      exact eq_true (by
        show ((σ.find? ee.codeOwner).elim ⟨0⟩ fun x => x.balance).val.val < value.val.val
        exact Nat.lt_of_not_ge hbalance)
    have hdeqF : (s.executionEnv.depth == 1024) = false := by
      rw [beq_eq_false_iff_ne]
      intro hh
      rw [hh] at hdepth'
      exact absurd hdepth' (by decide)
    simp only [List.length_cons, hovF, hstaticF, if_false, hdepthLt, hbalOpt, hgtT,
      hdeqF] at st
    rw [collapse_two_stage, hcode] at st
    have hfuel : g.toNat + 1 - k = (g.toNat - k) + 1 := by omega
    have hXP := hX.trans (hfuel.symm ▸ X_peel (f := g.toNat - k) st)
    set mc := memoryExpansionCost s Operation.CALL with hmc
    set gc := Ccall (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target) value
      gasArg s.accountMap
      { pc := s.machineState.pc, stack := s.machineState.stack, execLength := s.machineState.execLength,
        gasAvailable := s.machineState.gasAvailable.subNat mc,
        activeWords := s.machineState.activeWords, memory := s.machineState.memory,
        returnData := s.machineState.returnData, H_return := s.machineState.H_return } s.substate with hgc
    set G := Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target) value
      gasArg s.accountMap
      { pc := s.machineState.pc, stack := s.machineState.stack, execLength := s.machineState.execLength + 1,
        gasAvailable := s.machineState.gasAvailable.subNat mc,
        activeWords := s.machineState.activeWords, memory := s.machineState.memory,
        returnData := s.machineState.returnData, H_return := s.machineState.H_return } s.substate with hG
    set gv := (s.machineState.gasAvailable.subNat mc).subNat (gc - (UInt256.ofNat G).toNat) with hgv
    split at hXP
    · exact ⟨k, C, by unfold RD; exact Or.inl hXP⟩
    · rename_i hP
      have hPle : mc + gc ≤ s.machineState.gasAvailable.toNat := Nat.le_of_not_lt hP
      have hcgle : (UInt256.ofNat G).toNat ≤ G := by
        show G % UInt256.size ≤ G
        exact Nat.mod_le _ _
      have hGltgc : G < gc := by
        rw [hG, hgc]
        exact Ccallgas_lt_Ccall (AccountAddress.ofUInt256 target)
          (AccountAddress.ofUInt256 target) value gasArg s.accountMap
          { pc := s.machineState.pc, stack := s.machineState.stack,
            execLength := s.machineState.execLength + 1,
            gasAvailable := s.machineState.gasAvailable.subNat mc,
            activeWords := s.machineState.activeWords, memory := s.machineState.memory,
            returnData := s.machineState.returnData, H_return := s.machineState.H_return }
          s.substate
      have hgasN : s.machineState.gasAvailable.toNat = g.toNat - C := by
        rw [hgas, Sat256.subNat_toNat]
      set callCharge := mc + (gc - (UInt256.ofNat G).toNat) with hcallCharge
      have hcallChargeLeGas : callCharge ≤ s.machineState.gasAvailable.toNat := by
        rw [hcallCharge]
        have hdeltaLe : gc - (UInt256.ofNat G).toNat ≤ gc := Nat.sub_le _ _
        omega
      have hCcallCharge : C + callCharge ≤ g.toNat := by
        rw [hgasN] at hcallChargeLeGas
        omega
      have hgvGas : gv = g.subNat (C + callCharge) := by
        rw [hgv, hgas, hcallCharge]
        rw [Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      rw [show g.toNat - k = g.toNat + 1 - (k + 1) from by omega] at hXP
      refine ⟨k + 1, C + callCharge, ?_⟩
      unfold RD
      refine Or.inr ⟨_, hXP, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hcode
      · rw [hpc]
      · rfl
      · show gv = g.subNat (C + callCharge)
        exact hgvGas
      · show k + 1 ≤ C + callCharge
        rw [hcallCharge]
        omega
      · exact hCcallCharge
      · simp [hmem]
      · rw [haw]
      · rfl
      · simp [hcA, hσ]
      · exact hee
      · exact hworld

theorem simpleAuctionX_auctionEnd_callInsufficientRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨124⟩ [simpleAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (htime : (auctionEndAuctionEndWord σ I).toNat ≤ (auctionEndTimestampWord I).toNat)
    (hended : auctionEndEndedWord σ I = ⟨0⟩)
    (hbalance : ¬ auctionEndHighestBidWord (auctionEndAfterEndedMap σ I) I ≤
      (auctionEndAfterEndedMap σ I |>.find? I.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hdepth : I.depth.val < 1024) :
    RDrev simpleAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨gasArg, _, _, rd742⟩ := simpleAuctionX_auctionEnd_toCall (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hperm hwv hreach htime hended
  obtain ⟨_, _, rd743⟩ :=
    auctionEndRDCallValueInsufficientBalance rd742 hperm (by decide) hbalance hdepth (by evm_ov)
  obtain ⟨_, _, rd798⟩ :=
    simpleAuctionX_auctionEnd_postCallEmpty_toRequire (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) rd743
  exact simpleAuctionX_auctionEnd_requireSuccess_revert rd798

/-! ## `auctionEnd()` Solm-side source execution helpers -/

def auctionEndAfterEndedState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩
    (auctionEndSetEndedWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩))

def auctionEndBeneficiaryRawWordState (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩

def auctionEndBeneficiaryWordState (evm : EVM.State) : UInt256 :=
  UInt256.land (auctionEndBeneficiaryRawWordState evm) solcAddrMask

def auctionEndHighestBidWordState (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩

def auctionEndEndedRawWordState (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩

def auctionEndEndedWordState (evm : EVM.State) : UInt256 :=
  UInt256.land (auctionEndEndedRawWordState evm) ⟨255⟩

def auctionEndCallStore (success : Bool) (out : ByteArray) : Store :=
  ((∅ : Store).insert "success" (.bool success)).insert "_data" (.bytes out)

theorem auctionEndAddress_ofNat_toNat (w : UInt256) :
    AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat =
      AccountAddress.ofUInt256 (UInt256.land w solcAddrMask) := by
  apply Fin.ext
  unfold AccountAddress.ofNat AccountAddress.ofUInt256
  simp [UInt256.toNat]

theorem auctionEndAddress_from_toNat (a : AccountAddress) :
    EVM.address a.toNat = a := by
  apply Fin.ext
  simp [EVM.address, EVM.uintN]
  exact Nat.mod_eq_of_lt a.isLt

theorem auctionEndAccountMapEquiv_balance {σ τ : AccountMap}
    (hστ : accountMapEquiv σ τ) (addr : AccountAddress) :
    (σ.find? addr |>.elim ⟨0⟩ (·.balance)) =
      (τ.find? addr |>.elim ⟨0⟩ (·.balance)) := by
  specialize hστ addr
  cases hσ : σ.find? addr <;> cases hτ : τ.find? addr <;>
    simp [hσ, hτ, accountEquiv] at hστ ⊢
  exact hστ.2.1

theorem auctionEndCallStore_success_get (success : Bool) (out : ByteArray) :
    (auctionEndCallStore success out)["success"]? = some (.bool success) := by
  change (auctionEndCallStore success out).get? "success" = some (.bool success)
  unfold auctionEndCallStore
  rw [store_get_ne]
  · exact store_get_self _ _ _
  · decide

theorem evalExpr_auctionEnd_auctionEndTime (evm : EVM.State) :
    evalExpr? simpleAuctionConfig { contract := simpleAuctionContract, locals := ∅ } evm
      (.storage auctionEndTimeRef) =
        .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat)) := by
  have her : evalStorageRef simpleAuctionConfig
      { contract := simpleAuctionContract, locals := ∅ } evm auctionEndTimeRef =
      .ok { base := "auctionEndTime", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, auctionEndTimeRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? simpleAuctionContract.storage
      ({ base := "auctionEndTime", steps := [] } : EvaledStorageRef) =
      some (.elem (.int uint256Int)) := by
    decide
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := by simp) (her := her)
    (hty := hty) (hloc := simpleAuctionConfig_storage_auctionEndTime)]
  rw [simpleAuctionStorageLocLoad_uint256]

theorem evalExpr_auctionEnd_beneficiary (evm : EVM.State) :
    evalExpr? simpleAuctionConfig { contract := simpleAuctionContract, locals := ∅ } evm
      (.storage beneficiaryRef) =
        .ok (.address (AccountAddress.ofNat (auctionEndBeneficiaryWordState evm).toNat)) := by
  have her : evalStorageRef simpleAuctionConfig
      { contract := simpleAuctionContract, locals := ∅ } evm beneficiaryRef =
      .ok { base := "beneficiary", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, beneficiaryRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? simpleAuctionContract.storage
      ({ base := "beneficiary", steps := [] } : EvaledStorageRef) = some (.elem .address) := by
    decide
  rw [evalExpr_storage_scalar (t := .address) (hbase := by simp) (her := her)
    (hty := hty) (hloc := simpleAuctionConfig_storage_beneficiary)]
  rw [simpleAuctionStorageLocLoad_address_offset0]
  rfl

theorem evalExpr_auctionEnd_highestBid (evm : EVM.State) :
    evalExpr? simpleAuctionConfig { contract := simpleAuctionContract, locals := ∅ } evm
      (.storage highestBidRef) =
        .ok (.int (Int.ofNat (auctionEndHighestBidWordState evm).toNat)) := by
  have her : evalStorageRef simpleAuctionConfig
      { contract := simpleAuctionContract, locals := ∅ } evm highestBidRef =
      .ok { base := "highestBid", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, highestBidRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? simpleAuctionContract.storage
      ({ base := "highestBid", steps := [] } : EvaledStorageRef) =
      some (.elem (.int uint256Int)) := by
    decide
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := by simp) (her := her)
    (hty := hty) (hloc := simpleAuctionConfig_storage_highestBid)]
  rw [simpleAuctionStorageLocLoad_uint256]
  rfl

theorem evalExpr_auctionEnd_ended_false (evm : EVM.State)
    (hzero : auctionEndEndedWordState evm = ⟨0⟩) :
    evalExpr? simpleAuctionConfig { contract := simpleAuctionContract, locals := ∅ } evm
      (.storage endedRef) = .ok (.bool false) := by
  have her : evalStorageRef simpleAuctionConfig
      { contract := simpleAuctionContract, locals := ∅ } evm endedRef =
      .ok { base := "ended", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, endedRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? simpleAuctionContract.storage
      ({ base := "ended", steps := [] } : EvaledStorageRef) = some (.elem .bool) := by
    decide
  rw [evalExpr_storage_scalar (t := .bool) (hbase := by simp) (her := her)
    (hty := hty) (hloc := simpleAuctionConfig_storage_ended)]
  simpa [auctionEndEndedWordState, auctionEndEndedRawWordState] using
    simpleAuctionStorageLocLoad_bool_offset0_false evm ⟨5⟩ hzero

theorem evalExpr_auctionEnd_ended_true (evm : EVM.State)
    (hnz : auctionEndEndedWordState evm ≠ ⟨0⟩) :
    evalExpr? simpleAuctionConfig { contract := simpleAuctionContract, locals := ∅ } evm
      (.storage endedRef) = .ok (.bool true) := by
  have her : evalStorageRef simpleAuctionConfig
      { contract := simpleAuctionContract, locals := ∅ } evm endedRef =
      .ok { base := "ended", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, endedRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? simpleAuctionContract.storage
      ({ base := "ended", steps := [] } : EvaledStorageRef) = some (.elem .bool) := by
    decide
  rw [evalExpr_storage_scalar (t := .bool) (hbase := by simp) (her := her)
    (hty := hty) (hloc := simpleAuctionConfig_storage_ended)]
  simpa [auctionEndEndedWordState, auctionEndEndedRawWordState] using
    simpleAuctionStorageLocLoad_bool_offset0_true evm ⟨5⟩ hnz

theorem evalExpr_auctionEnd_time_true (evm : EVM.State)
    (htime :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat ≤
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) :
    evalExpr? simpleAuctionConfig { contract := simpleAuctionContract, locals := ∅ } evm
      (.binary .ge now (.storage auctionEndTimeRef)) = .ok (.bool true) := by
  simp only [evalExpr?, now, envValue, evalExpr_auctionEnd_auctionEndTime, bind,
    EvalResult.bind, pure]
  simpa [evalBinaryOp?, UInt256.toNat] using htime

theorem evalExpr_auctionEnd_time_false (evm : EVM.State)
    (htime :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat) :
    evalExpr? simpleAuctionConfig { contract := simpleAuctionContract, locals := ∅ } evm
      (.binary .ge now (.storage auctionEndTimeRef)) = .ok (.bool false) := by
  simp only [evalExpr?, now, envValue, evalExpr_auctionEnd_auctionEndTime, bind,
    EvalResult.bind, pure]
  simpa [evalBinaryOp?, UInt256.toNat] using htime

theorem evalExpr_auctionEnd_not_ended_true (evm : EVM.State)
    (hzero : auctionEndEndedWordState evm = ⟨0⟩) :
    evalExpr? simpleAuctionConfig { contract := simpleAuctionContract, locals := ∅ } evm
      (.unary .not (.storage endedRef)) = .ok (.bool true) := by
  rw [evalExpr?]
  rw [evalExpr_auctionEnd_ended_false evm hzero]
  rfl

theorem evalExpr_auctionEnd_not_ended_false (evm : EVM.State)
    (hnz : auctionEndEndedWordState evm ≠ ⟨0⟩) :
    evalExpr? simpleAuctionConfig { contract := simpleAuctionContract, locals := ∅ } evm
      (.unary .not (.storage endedRef)) = .ok (.bool false) := by
  rw [evalExpr?]
  rw [evalExpr_auctionEnd_ended_true evm hnz]
  rfl

theorem evalExpr_auctionEnd_emptyBytes (evm : EVM.State) :
    evalExpr? simpleAuctionConfig { contract := simpleAuctionContract, locals := ∅ } evm
      (.newBytes (.intLit 0)) = .ok (.bytes ByteArray.empty) := by
  simp [evalExpr?, pure, bind, EvalResult.bind]
  rfl

theorem evalExpr_auctionEnd_success (evm : EVM.State) (success : Bool) (out : ByteArray) :
    evalExpr? simpleAuctionConfig
      { contract := simpleAuctionContract, locals := auctionEndCallStore success out } evm
      (.var "success") = .ok (.bool success) := by
  rw [evalExpr?]
  simp [EvalResult.ofOption, auctionEndCallStore_success_get]

theorem auctionEndAssignEnded (evm : EVM.State) :
    assignStorageRef? simpleAuctionConfig { contract := simpleAuctionContract, locals := ∅ } evm
      .storage endedRef (.bool true) =
        .ok ({ contract := simpleAuctionContract, locals := ∅ }, auctionEndAfterEndedState evm) := by
  apply assignStorageRef_storage_scalar_value (ty := boolSt)
      (hbase := by simp)
      (her := by
        simp [evalStorageRef, evalStorageRefSteps, endedRef, EvalResult.bind, pure, bind])
      (hty := by decide)
      (hloc := simpleAuctionConfig_storage_ended)
      (hscalar := by trivial)
  rw [simpleAuctionStorageLocStore_bool_true_offset0]
  rfl

theorem simpleAuctionAuctionEndBodyReverts_time (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (htime :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat) :
    ExecTransitionBody simpleAuctionConfig simpleAuctionContract evm ∅
      auctionEndTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  unfold auctionEndTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse (evalExpr_auctionEnd_time_false evm htime))

theorem simpleAuctionAuctionEndBodyReverts_ended (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (htime :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat ≤
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hnz : auctionEndEndedWordState evm ≠ ⟨0⟩) :
    ExecTransitionBody simpleAuctionConfig simpleAuctionContract evm ∅
      auctionEndTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  unfold auctionEndTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_auctionEnd_time_true evm htime)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_auctionEnd_not_ended_false evm hnz))

theorem simpleAuctionAuctionEndBodyReverts_callFailure
    (evm evm' : EVM.State) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (htime :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat ≤
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hended : auctionEndEndedWordState evm = ⟨0⟩)
    (hcall :
      callViaEVM (auctionEndAfterEndedState evm)
        (EVM.address
          (AccountAddress.ofNat
            (auctionEndBeneficiaryWordState (auctionEndAfterEndedState evm)).toNat))
        (Int.ofNat (auctionEndHighestBidWordState (auctionEndAfterEndedState evm)).toNat)
        ByteArray.empty (false, evm', out)) :
    ExecTransitionBody simpleAuctionConfig simpleAuctionContract evm ∅
      auctionEndTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  unfold auctionEndTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_auctionEnd_time_true evm htime)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_auctionEnd_not_ended_true evm hended)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure]) (auctionEndAssignEnded evm)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.lowLevelCallFailure
      (evalExpr_auctionEnd_beneficiary (auctionEndAfterEndedState evm))
      (evalExpr_auctionEnd_highestBid (auctionEndAfterEndedState evm))
      (evalExpr_auctionEnd_emptyBytes (auctionEndAfterEndedState evm)) hcall) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse (evalExpr_auctionEnd_success evm' false out))

theorem simpleAuctionAuctionEndBodyReturns_callSuccess
    (evm evm' : EVM.State) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (htime :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat ≤
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hended : auctionEndEndedWordState evm = ⟨0⟩)
    (hcall :
      callViaEVM (auctionEndAfterEndedState evm)
        (EVM.address
          (AccountAddress.ofNat
            (auctionEndBeneficiaryWordState (auctionEndAfterEndedState evm)).toNat))
        (Int.ofNat (auctionEndHighestBidWordState (auctionEndAfterEndedState evm)).toNat)
        ByteArray.empty (true, evm', out)) :
    ExecTransitionBody simpleAuctionConfig simpleAuctionContract evm ∅ auctionEndTransition.body
      (.returned { contract := simpleAuctionContract, locals := auctionEndCallStore true out }
        evm' none) := by
  refine ExecFuncBody.execBlockOK ?_
  unfold auctionEndTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_auctionEnd_time_true evm htime)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_auctionEnd_not_ended_true evm hended)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure]) (auctionEndAssignEnded evm)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.lowLevelCallSuccess
      (evalExpr_auctionEnd_beneficiary (auctionEndAfterEndedState evm))
      (evalExpr_auctionEnd_highestBid (auctionEndAfterEndedState evm))
      (evalExpr_auctionEnd_emptyBytes (auctionEndAfterEndedState evm)) hcall) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_auctionEnd_success evm' true out)) ?_
  exact ExecBlock.nil

theorem auctionEndAfterEndedState_accountMap (evm : EVM.State) :
    (auctionEndAfterEndedState evm).accountMap =
      sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap ⟨5⟩
        (auctionEndSetEndedWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩)) := by
  simp [auctionEndAfterEndedState, simpleAuctionStorageStore_accountMap]

theorem auctionEndAfterEndedState_createdAccounts (evm : EVM.State) :
    (auctionEndAfterEndedState evm).createdAccounts = evm.createdAccounts := by
  simp [auctionEndAfterEndedState, simpleAuctionStorageStore_createdAccounts]

theorem auctionEndAfterEndedState_executionEnv (evm : EVM.State) :
    (auctionEndAfterEndedState evm).executionEnv = evm.executionEnv := by
  simp [auctionEndAfterEndedState, storageStore_executionEnv]

theorem auctionEndAfterEndedState_originalMap (evm : EVM.State) :
    (auctionEndAfterEndedState evm).σ₀ = evm.σ₀ := by
  unfold auctionEndAfterEndedState Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.find? evm.executionEnv.codeOwner <;> simp [Option.option, State.setAccount]

theorem auctionEndAfterEndedState_substate (evm : EVM.State) :
    (auctionEndAfterEndedState evm).substate = evm.substate := by
  unfold auctionEndAfterEndedState Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.find? evm.executionEnv.codeOwner <;> simp [Option.option, State.setAccount]

theorem auctionEndAfterEndedState_genesisBlockHeader (evm : EVM.State) :
    (auctionEndAfterEndedState evm).genesisBlockHeader = evm.genesisBlockHeader := by
  unfold auctionEndAfterEndedState Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.find? evm.executionEnv.codeOwner <;> simp [Option.option, State.setAccount]

theorem auctionEndAfterEndedState_blocks (evm : EVM.State) :
    (auctionEndAfterEndedState evm).blocks = evm.blocks := by
  unfold auctionEndAfterEndedState Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.find? evm.executionEnv.codeOwner <;> simp [Option.option, State.setAccount]

theorem auctionEndAfterEndedState_accountMap_init {cA gh bl σ σ₀ A I} {g : Sat256} :
    (auctionEndAfterEndedState (initState cA gh bl σ σ₀ g A I)).accountMap =
      auctionEndAfterEndedMap σ I := by
  simp [auctionEndAfterEndedState_accountMap, auctionEndAfterEndedMap,
    auctionEndEndedRawWord, initState, Solm.EVM.storageLoad, State.lookupAccount,
    Account.lookupStorage]

theorem auctionEndBeneficiaryWordState_afterEnded_init {cA gh bl σ σ₀ A I} {g : Sat256} :
    auctionEndBeneficiaryWordState
      (auctionEndAfterEndedState (initState cA gh bl σ σ₀ g A I)) =
      auctionEndBeneficiaryWord (auctionEndAfterEndedMap σ I) I := by
  unfold auctionEndBeneficiaryWordState auctionEndBeneficiaryRawWordState
    auctionEndBeneficiaryWord auctionEndBeneficiaryRawWord
  unfold Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
  rw [auctionEndAfterEndedState_executionEnv, auctionEndAfterEndedState_accountMap_init]
  simp [initState]

theorem auctionEndHighestBidWordState_afterEnded_init {cA gh bl σ σ₀ A I} {g : Sat256} :
    auctionEndHighestBidWordState
      (auctionEndAfterEndedState (initState cA gh bl σ σ₀ g A I)) =
      auctionEndHighestBidWord (auctionEndAfterEndedMap σ I) I := by
  unfold auctionEndHighestBidWordState auctionEndHighestBidWord
  unfold Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
  rw [auctionEndAfterEndedState_executionEnv, auctionEndAfterEndedState_accountMap_init]
  simp [initState]

theorem auctionEndAfterEndedState_balance_init {cA gh bl σ σ₀ A I} {g : Sat256} :
    (auctionEndAfterEndedMap σ I |>.find? I.codeOwner |>.elim ⟨0⟩ (·.balance)) =
      ((auctionEndAfterEndedState (initState cA gh bl σ σ₀ g A I)).accountMap.find?
        (auctionEndAfterEndedState (initState cA gh bl σ σ₀ g A I)).executionEnv.codeOwner
          |>.elim ⟨0⟩ (·.balance)) := by
  rw [auctionEndAfterEndedState_executionEnv, auctionEndAfterEndedState_accountMap_init]
  rfl

theorem auctionEndAfterEndedState_EVMStateEquiv {evmE evmS : EVM.State}
    (hσ : EVMStateEquiv evmE evmS) :
    EVMStateEquiv (auctionEndAfterEndedState evmE) (auctionEndAfterEndedState evmS) := by
  unfold auctionEndAfterEndedState
  have hval :
      auctionEndSetEndedWord (Solm.EVM.storageLoad evmE evmE.executionEnv.codeOwner ⟨5⟩) =
        auctionEndSetEndedWord (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨5⟩) := by
    rw [hσ.storageLoad_codeOwner ⟨5⟩]
  exact hσ.storageStore_codeOwner ⟨5⟩ hval

theorem auctionEndEVMStateEquiv_balance_codeOwner {evmE evmS : EVM.State}
    (hσ : EVMStateEquiv evmE evmS) :
    (evmE.accountMap.find? evmE.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance)) =
      (evmS.accountMap.find? evmS.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance)) := by
  rw [hσ.executionEnv]
  exact auctionEndAccountMapEquiv_balance hσ.accountMap evmS.executionEnv.codeOwner

theorem auctionEndByteArray_eq_empty_of_size_zero (b : ByteArray) (h : b.size = 0) :
    b = ByteArray.empty := by
  apply ByteArray.ext
  exact Array.eq_empty_of_size_eq_zero (by simpa using h)

theorem simpleAuctionX_auctionEnd_afterCall_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {o : ByteArray} {k C : ℕ}
    (rd : RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨743⟩
      [⟨0⟩, ⟨128⟩,
        auctionEndHighestBidWord (auctionEndAfterEndedMap σ I) I,
        auctionEndBeneficiaryWord (auctionEndAfterEndedMap σ I) I,
        ⟨0⟩, ⟨122⟩, simpleAuctionSelWord I]
      (auctionEndEventMem (auctionEndAfterEndedMap σ I) I) (UInt256.ofNat 6) o
      acc k C)
    (hosz : o.size < UInt256.size) :
    RDrev simpleAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  by_cases ho : o.size = 0
  · have hoempty : o = ByteArray.empty := auctionEndByteArray_eq_empty_of_size_zero o ho
    subst o
    obtain ⟨_, _, rd798⟩ :=
      simpleAuctionX_auctionEnd_postCallEmpty_toRequire (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) rd
    exact simpleAuctionX_auctionEnd_requireSuccess_revert rd798
  · obtain ⟨_, _, _, _, rd798⟩ :=
      simpleAuctionX_auctionEnd_postCallNonempty_toRequire (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) rd
        (auctionEndEventMem_mload64 (auctionEndAfterEndedMap σ I) I) ho hosz
    exact simpleAuctionX_auctionEnd_requireSuccess_revert rd798

theorem simpleAuctionX_auctionEnd_afterCall_return {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {o : ByteArray} {k C : ℕ}
    (rd : RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨743⟩
      [⟨1⟩, ⟨128⟩,
        auctionEndHighestBidWord (auctionEndAfterEndedMap σ I) I,
        auctionEndBeneficiaryWord (auctionEndAfterEndedMap σ I) I,
        ⟨0⟩, ⟨122⟩, simpleAuctionSelWord I]
      (auctionEndEventMem (auctionEndAfterEndedMap σ I) I) (UInt256.ofNat 6) o
      acc k C)
    (hosz : o.size < UInt256.size) :
    RDret simpleAuctionBytecode g (initState cA gh bl σ σ₀ g A I) acc ByteArray.empty := by
  by_cases ho : o.size = 0
  · have hoempty : o = ByteArray.empty := auctionEndByteArray_eq_empty_of_size_zero o ho
    subst o
    obtain ⟨_, _, rd798⟩ :=
      simpleAuctionX_auctionEnd_postCallEmpty_toRequire (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) rd
    exact simpleAuctionX_auctionEnd_requireSuccess_return rd798
  · obtain ⟨_, _, _, _, rd798⟩ :=
      simpleAuctionX_auctionEnd_postCallNonempty_toRequire (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) rd
        (auctionEndEventMem_mload64 (auctionEndAfterEndedMap σ I) I) ho hosz
    exact simpleAuctionX_auctionEnd_requireSuccess_return rd798

theorem simpleAuctionAuctionEndBody {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = simpleAuctionBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hsel : selIs I ⟨#[0x2a, 0x24, 0xf4, 0x6c]⟩)
    (hreach : ∃ k C, RD simpleAuctionBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨124⟩
      [simpleAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
 :
    runtimeEquivalenceFor simpleAuctionConfig simpleAuctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0x2a, 0x24, 0xf4, 0x6c]⟩ : ByteArray) ==
      I.calldata.extract 0 4) = true := by
    simpa [selIs] using hsel
  have hsz := simpleAuctionAuctionEndSelector_size hsel'
  have hd := simpleAuctionDispatch_auctionEnd (cd := I.calldata) hsel'
  have hdec := simpleAuctionDecode_auctionEnd (I := I) hsz
  let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hσ : EVMStateEquiv evmE evmS := by
    simpa [evmE, evmS] using EVMStateEquiv.initState
      (g := Sat256.ofUInt256 g) hAccounts
  have hAuctionEnd : auctionEndAuctionEndWord σ_evm I = auctionEndAuctionEndWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
  have hEndedRaw : auctionEndEndedRawWord σ_evm I = auctionEndEndedRawWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨5⟩ ⟨0⟩
  have hEnded : auctionEndEndedWord σ_evm I = auctionEndEndedWord σ_solm I := by
    simp [auctionEndEndedWord, hEndedRaw]
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases htimeBad :
        (auctionEndTimestampWord I).toNat < (auctionEndAuctionEndWord σ_evm I).toNat
    · have htimeS :
          (auctionEndTimestampWord I).toNat < (auctionEndAuctionEndWord σ_solm I).toNat := by
        simpa [hAuctionEnd] using htimeBad
      have hbody :
          ExecTransitionBody simpleAuctionConfig simpleAuctionContract evmS ∅
            auctionEndTransition.body .reverted :=
        simpleAuctionAuctionEndBodyReverts_time evmS
          (by simpa [evmS, initState] using hwv)
          (by
            simpa [evmS, initState, auctionEndAuctionEndWord, auctionEndTimestampWord,
              Solm.EVM.storageLoad, State.lookupAccount] using htimeS)
      exact (simpleAuctionX_auctionEnd_timeRevert (g := Sat256.ofUInt256 g) hwv hreach
          htimeBad)
        |>.reEquivExecutionRevert hcode hd hdec hbody
    · have htimeLe :
          (auctionEndAuctionEndWord σ_evm I).toNat ≤ (auctionEndTimestampWord I).toNat := by
        omega
      have htimeS :
          (auctionEndAuctionEndWord σ_solm I).toNat ≤ (auctionEndTimestampWord I).toNat := by
        simpa [← hAuctionEnd] using htimeLe
      by_cases hendedZero : auctionEndEndedWord σ_evm I = ⟨0⟩
      · have hendedSZero : auctionEndEndedWord σ_solm I = ⟨0⟩ := by
          simpa [hEnded] using hendedZero
        have hendedSState : auctionEndEndedWordState evmS = ⟨0⟩ := by
          simpa [evmS, initState, auctionEndEndedWordState, auctionEndEndedRawWordState,
            auctionEndEndedWord, Solm.EVM.storageLoad, State.lookupAccount] using hendedSZero
        let evmEAfter := auctionEndAfterEndedState evmE
        let evmSAfter := auctionEndAfterEndedState evmS
        have hσAfter : EVMStateEquiv evmEAfter evmSAfter := by
          simpa [evmEAfter, evmSAfter] using auctionEndAfterEndedState_EVMStateEquiv hσ
        by_cases hdepthEq : I.depth = 1024
        · let evmSFail : EVM.State :=
            { evmSAfter with
              substate := (evmSAfter.addAccessedAccount
                (EVM.address
                  (AccountAddress.ofNat (auctionEndBeneficiaryWordState evmSAfter).toNat))).substate }
          have hcall :
              callViaEVM evmSAfter
                (EVM.address
                  (AccountAddress.ofNat (auctionEndBeneficiaryWordState evmSAfter).toNat))
                (Int.ofNat (auctionEndHighestBidWordState evmSAfter).toNat)
                ByteArray.empty (false, evmSFail, ByteArray.empty) := by
            apply callViaEVM.callNotMade
            · rfl
            · rfl
            · rintro ⟨_, hdepthNe⟩
              exact hdepthNe (by
                simpa [evmSAfter, evmS, initState, auctionEndAfterEndedState_executionEnv]
                  using hdepthEq)
          have hbody :
              ExecTransitionBody simpleAuctionConfig simpleAuctionContract evmS ∅
                auctionEndTransition.body .reverted :=
            simpleAuctionAuctionEndBodyReverts_callFailure evmS evmSFail ByteArray.empty
              (by simpa [evmS, initState] using hwv)
              (by
                simpa [evmS, initState, auctionEndAuctionEndWord, auctionEndTimestampWord,
                  Solm.EVM.storageLoad, State.lookupAccount] using htimeS)
              hendedSState
              (by simpa [evmSAfter] using hcall)
          exact (simpleAuctionX_auctionEnd_callDepthRevert (g := Sat256.ofUInt256 g) hperm
              hwv hreach htimeLe hendedZero hdepthEq)
            |>.reEquivExecutionRevert hcode hd hdec hbody
        · have hdepthLt : I.depth.val < 1024 := by
            have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
            have hneVal : I.depth.val ≠ 1024 := by
              intro hv
              apply hdepthEq
              exact Fin.ext hv
            omega
          by_cases hbalance : (
                auctionEndHighestBidWord (auctionEndAfterEndedMap σ_evm I) I ≤
                  ((auctionEndAfterEndedMap σ_evm I).find? I.codeOwner).elim ⟨0⟩
                    (fun x => x.balance))
          · obtain ⟨cA', σ', z, out, A_in, callGas, kCall, CCall, hTheta, rd743⟩ :=
              simpleAuctionX_auctionEnd_callMade (g := Sat256.ofUInt256 g) hperm hwv
                hreach htimeLe hendedZero hbalance hdepthLt
            obtain ⟨g'', A', hThetaEq⟩ := hTheta
            let targetE : EVM.Address :=
              AccountAddress.ofUInt256 (auctionEndBeneficiaryWord
                evmEAfter.accountMap evmEAfter.executionEnv)
            let valueE : ℤ :=
              Int.ofNat (auctionEndHighestBidWord evmEAfter.accountMap evmEAfter.executionEnv).toNat
            let evmECall : EVM.State :=
              { evmEAfter with accountMap := σ', substate := A', createdAccounts := cA' }
            have hBenefE :
                auctionEndBeneficiaryWordState evmEAfter =
                  auctionEndBeneficiaryWord (auctionEndAfterEndedMap σ_evm I) I := by
              simpa [evmEAfter, evmE] using
                (auctionEndBeneficiaryWordState_afterEnded_init (cA := cA) (gh := gh)
                  (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
                  (I := I) (g := Sat256.ofUInt256 g))
            have hBenefES :
                auctionEndBeneficiaryWordState evmEAfter =
                  auctionEndBeneficiaryWordState evmSAfter := by
              unfold auctionEndBeneficiaryWordState auctionEndBeneficiaryRawWordState
              rw [hσAfter.storageLoad_codeOwner ⟨0⟩]
            have hHighE :
                auctionEndHighestBidWordState evmEAfter =
                  auctionEndHighestBidWord (auctionEndAfterEndedMap σ_evm I) I := by
              simpa [evmEAfter, evmE] using
                (auctionEndHighestBidWordState_afterEnded_init (cA := cA) (gh := gh)
                  (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
                  (I := I) (g := Sat256.ofUInt256 g))
            have hHighES :
                auctionEndHighestBidWordState evmEAfter =
                  auctionEndHighestBidWordState evmSAfter := by
              unfold auctionEndHighestBidWordState
              exact hσAfter.storageLoad_codeOwner ⟨3⟩
            have hAfterMapE :
                evmEAfter.accountMap = auctionEndAfterEndedMap σ_evm I := by
              simpa [evmEAfter, evmE] using
                (auctionEndAfterEndedState_accountMap_init (cA := cA) (gh := gh)
                  (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
                  (I := I) (g := Sat256.ofUInt256 g))
            have hAfterEnvE : evmEAfter.executionEnv = I := by
              simpa [evmEAfter, evmE] using
                (auctionEndAfterEndedState_executionEnv
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
            have hCreatedE : evmEAfter.createdAccounts = cA := by
              simpa [evmEAfter, evmE, initState] using
                (auctionEndAfterEndedState_createdAccounts
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
            have hOrigE : evmEAfter.σ₀ = σ₀ := by
              simpa [evmEAfter, evmE, initState] using
                (auctionEndAfterEndedState_originalMap
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
            have hGenesisE : evmEAfter.genesisBlockHeader = gh := by
              simpa [evmEAfter, evmE, initState] using
                (auctionEndAfterEndedState_genesisBlockHeader
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
            have hBlocksE : evmEAfter.blocks = bl := by
              simpa [evmEAfter, evmE, initState] using
                (auctionEndAfterEndedState_blocks
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
            have hBalE :
                (auctionEndAfterEndedMap σ_evm I |>.find? I.codeOwner |>.elim ⟨0⟩
                    (·.balance)) =
                  (evmEAfter.accountMap.find? evmEAfter.executionEnv.codeOwner |>.elim
                    ⟨0⟩ (·.balance)) := by
              simpa [evmEAfter, evmE] using
                (auctionEndAfterEndedState_balance_init (cA := cA) (gh := gh) (bl := bl)
                  (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
                  (g := Sat256.ofUInt256 g))
            have hcallE :
                callViaEVM evmEAfter targetE valueE ByteArray.empty (z, evmECall, out) := by
              refine callViaEVM.callMade
                (valueWord := auctionEndHighestBidWord evmEAfter.accountMap evmEAfter.executionEnv)
                (cA' := cA') (σ' := σ') (g' := g'') (A' := A')
                ?_ ?_ ?_ ?_ ?_
              · exact (simpleAuctionWordOfInt_ofNat_toNat
                  (auctionEndHighestBidWord evmEAfter.accountMap evmEAfter.executionEnv)).symm
              · refine ⟨callGas, A_in, ?_⟩
                rw [hAfterEnvE, hCreatedE, hGenesisE, hBlocksE, hAfterMapE, hOrigE]
                simpa [targetE, hperm, accountAddress_roundtrip, hAfterMapE, hAfterEnvE,
                  initState] using hThetaEq
              · simp [evmECall]
              · simpa [hAfterMapE, hAfterEnvE, hBalE] using hbalance
              · intro hd
                exact hdepthEq (by
                  simpa [evmEAfter, evmE, initState, auctionEndAfterEndedState_executionEnv] using hd)
            have houtsz : out.size < UInt256.size := by
              have hsizeΘ := Theta_returnData_size_lt I.blobVersionedHashes cA
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).genesisBlockHeader
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).blocks
                (auctionEndAfterEndedMap σ_evm I)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).σ₀ A_in
                (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
                (AccountAddress.ofUInt256 (auctionEndBeneficiaryWord
                  (auctionEndAfterEndedMap σ_evm I) I))
                (toExecute (auctionEndAfterEndedMap σ_evm I)
                  (AccountAddress.ofUInt256 (auctionEndBeneficiaryWord
                    (auctionEndAfterEndedMap σ_evm I) I)))
                callGas (UInt256.ofNat I.gasPrice)
                (auctionEndHighestBidWord (auctionEndAfterEndedMap σ_evm I) I)
                (auctionEndHighestBidWord (auctionEndAfterEndedMap σ_evm I) I)
                ByteArray.empty (I.depth + 1) I.header I.perm
                (by simp [UInt256.size])
              rw [← hThetaEq] at hsizeΘ
              exact hsizeΘ
            have hOrigAfter : evmEAfter.σ₀ = evmSAfter.σ₀ := by
              simpa [evmEAfter, evmSAfter, evmE, evmS, initState,
                auctionEndAfterEndedState_originalMap]
            obtain ⟨σ'_solm, A'_solm, hcallSRaw, hPostAccounts⟩ :=
              callViaEVM_accountMapEquiv (storage := simpleAuctionConfig.storage)
                (evm_solm := evmSAfter) hcallE hσAfter.accountMap hOrigAfter
                hσAfter.createdAccounts.symm
                (by
                  simpa [evmEAfter, evmSAfter, evmE, evmS, initState,
                    auctionEndAfterEndedState_genesisBlockHeader])
                (by
                  simpa [evmEAfter, evmSAfter, evmE, evmS, initState,
                    auctionEndAfterEndedState_blocks])
                (by
                  simpa [evmEAfter, evmSAfter, evmE, evmS, initState,
                    auctionEndAfterEndedState_substate])
                hσAfter.executionEnv.symm
            let evmSCall : EVM.State :=
              { evmSAfter with
                accountMap := σ'_solm
                substate := A'_solm
                createdAccounts := evmECall.createdAccounts }
            have hBenefTarget :
                auctionEndBeneficiaryWord evmEAfter.accountMap evmEAfter.executionEnv =
                  auctionEndBeneficiaryWordState evmSAfter := by
              rw [hAfterMapE, hAfterEnvE, ← hBenefE, hBenefES]
            have hTargetEq :
                targetE =
                  EVM.address
                    (AccountAddress.ofNat (auctionEndBeneficiaryWordState evmSAfter).toNat) := by
              calc
                targetE =
                    AccountAddress.ofUInt256 (auctionEndBeneficiaryWordState evmSAfter) := by
                  simp [targetE, hBenefTarget]
                _ = AccountAddress.ofNat (auctionEndBeneficiaryWordState evmSAfter).toNat := by
                  simpa [auctionEndBeneficiaryWordState] using
                    (auctionEndAddress_ofNat_toNat
                      (auctionEndBeneficiaryRawWordState evmSAfter)).symm
                _ = EVM.address
                    (AccountAddress.ofNat (auctionEndBeneficiaryWordState evmSAfter).toNat) := by
                  exact (auctionEndAddress_from_toNat
                    (AccountAddress.ofNat (auctionEndBeneficiaryWordState evmSAfter).toNat)).symm
            have hValueTarget :
                auctionEndHighestBidWord evmEAfter.accountMap evmEAfter.executionEnv =
                  auctionEndHighestBidWordState evmSAfter := by
              rw [hAfterMapE, hAfterEnvE, ← hHighE, hHighES]
            have hValueEq :
                valueE = Int.ofNat (auctionEndHighestBidWordState evmSAfter).toNat := by
              simpa [valueE, hValueTarget]
            have hcallS :
                callViaEVM evmSAfter
                  (EVM.address
                    (AccountAddress.ofNat (auctionEndBeneficiaryWordState evmSAfter).toNat))
                  (Int.ofNat (auctionEndHighestBidWordState evmSAfter).toNat)
                  ByteArray.empty (z, evmSCall, out) := by
              simpa [evmSCall, hTargetEq, hValueEq] using hcallSRaw
            cases z
            · have hbody :
                  ExecTransitionBody simpleAuctionConfig simpleAuctionContract evmS ∅
                    auctionEndTransition.body .reverted :=
                simpleAuctionAuctionEndBodyReverts_callFailure evmS evmSCall out
                  (by simpa [evmS, initState] using hwv)
                  (by
                    simpa [evmS, initState, auctionEndAuctionEndWord, auctionEndTimestampWord,
                      Solm.EVM.storageLoad, State.lookupAccount] using htimeS)
                  hendedSState
                  (by simpa [evmSAfter] using hcallS)
              have hrev : RDrev simpleAuctionBytecode (Sat256.ofUInt256 g)
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
                simpleAuctionX_auctionEnd_afterCall_revert (cA := cA) (gh := gh) (bl := bl)
                  (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
                  (g := Sat256.ofUInt256 g)
                  (rd := by simpa using rd743) houtsz
              exact hrev.reEquivExecutionRevert hcode hd hdec hbody
            · have hbody :
                  ExecTransitionBody simpleAuctionConfig simpleAuctionContract evmS ∅
                    auctionEndTransition.body
                    (.returned { contract := simpleAuctionContract, locals := auctionEndCallStore true out }
                      evmSCall none) :=
                simpleAuctionAuctionEndBodyReturns_callSuccess evmS evmSCall out
                  (by simpa [evmS, initState] using hwv)
                  (by
                    simpa [evmS, initState, auctionEndAuctionEndWord, auctionEndTimestampWord,
                      Solm.EVM.storageLoad, State.lookupAccount] using htimeS)
                  hendedSState
                  (by simpa [evmSAfter] using hcallS)
              have hret : RDret simpleAuctionBytecode (Sat256.ofUInt256 g)
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                  (cA', σ') ByteArray.empty :=
                simpleAuctionX_auctionEnd_afterCall_return (cA := cA) (gh := gh) (bl := bl)
                  (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
                  (g := Sat256.ofUInt256 g)
                  (rd := by simpa using rd743) houtsz
              exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
                (by simp [evmSCall, evmECall])
                (by simpa [evmSCall, evmECall] using hPostAccounts)
                (returnEquiv.void rfl rfl rfl)
          · let evmSFail : EVM.State :=
              { evmSAfter with
                substate := (evmSAfter.addAccessedAccount
                  (EVM.address
                    (AccountAddress.ofNat (auctionEndBeneficiaryWordState evmSAfter).toNat))).substate }
            have hHighE :
                auctionEndHighestBidWordState evmEAfter =
                  auctionEndHighestBidWord (auctionEndAfterEndedMap σ_evm I) I := by
              simpa [evmEAfter, evmE] using
                (auctionEndHighestBidWordState_afterEnded_init (cA := cA) (gh := gh)
                  (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
                  (I := I) (g := Sat256.ofUInt256 g))
            have hHighES :
                auctionEndHighestBidWordState evmEAfter =
                  auctionEndHighestBidWordState evmSAfter := by
              unfold auctionEndHighestBidWordState
              exact hσAfter.storageLoad_codeOwner ⟨3⟩
            have hBalE :
                ((auctionEndAfterEndedMap σ_evm I).find? I.codeOwner).elim ⟨0⟩
                    (fun x => x.balance) =
                  (evmEAfter.accountMap.find? evmEAfter.executionEnv.codeOwner |>.elim
                    ⟨0⟩ (·.balance)) := by
              simpa [evmEAfter, evmE] using
                (auctionEndAfterEndedState_balance_init (cA := cA) (gh := gh) (bl := bl)
                  (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
                  (g := Sat256.ofUInt256 g))
            have hBalES :
                (evmEAfter.accountMap.find? evmEAfter.executionEnv.codeOwner |>.elim
                    ⟨0⟩ (·.balance)) =
                  (evmSAfter.accountMap.find? evmSAfter.executionEnv.codeOwner |>.elim
                    ⟨0⟩ (·.balance)) :=
              auctionEndEVMStateEquiv_balance_codeOwner hσAfter
            have hcall :
                callViaEVM evmSAfter
                  (EVM.address
                    (AccountAddress.ofNat (auctionEndBeneficiaryWordState evmSAfter).toNat))
                  (Int.ofNat (auctionEndHighestBidWordState evmSAfter).toNat)
                  ByteArray.empty (false, evmSFail, ByteArray.empty) := by
              apply callViaEVM.callNotMade
              · rfl
              · rfl
              · rintro ⟨hvalueBal, _⟩
                have hvalueBal' :
                    auctionEndHighestBidWordState evmSAfter ≤
                      (evmSAfter.accountMap.find? evmSAfter.executionEnv.codeOwner |>.elim
                        ⟨0⟩ (·.balance)) := by
                  rw [simpleAuctionWordOfInt_ofNat_toNat] at hvalueBal
                  exact hvalueBal
                have hvalueBalE :
                    auctionEndHighestBidWord (auctionEndAfterEndedMap σ_evm I) I ≤
                      (evmEAfter.accountMap.find? evmEAfter.executionEnv.codeOwner |>.elim
                        ⟨0⟩ (·.balance)) := by
                  simpa [← hHighES, hHighE, ← hBalES] using hvalueBal'
                exact hbalance (by simpa [hBalE] using hvalueBalE)
            have hbody :
                ExecTransitionBody simpleAuctionConfig simpleAuctionContract evmS ∅
                  auctionEndTransition.body .reverted :=
              simpleAuctionAuctionEndBodyReverts_callFailure evmS evmSFail ByteArray.empty
                (by simpa [evmS, initState] using hwv)
                (by
                  simpa [evmS, initState, auctionEndAuctionEndWord, auctionEndTimestampWord,
                    Solm.EVM.storageLoad, State.lookupAccount] using htimeS)
                hendedSState
                (by simpa [evmSAfter] using hcall)
            exact (simpleAuctionX_auctionEnd_callInsufficientRevert (g := Sat256.ofUInt256 g)
                hperm hwv hreach htimeLe hendedZero hbalance hdepthLt)
              |>.reEquivExecutionRevert hcode hd hdec hbody
      · have hendedBad : auctionEndEndedWord σ_evm I ≠ ⟨0⟩ := hendedZero
        have hendedS : auctionEndEndedWord σ_solm I ≠ ⟨0⟩ := by
          intro hz
          exact hendedBad (by simpa [hEnded] using hz)
        have hbody :
            ExecTransitionBody simpleAuctionConfig simpleAuctionContract evmS ∅
              auctionEndTransition.body .reverted :=
          simpleAuctionAuctionEndBodyReverts_ended evmS
            (by simpa [evmS, initState] using hwv)
            (by
              simpa [evmS, initState, auctionEndAuctionEndWord, auctionEndTimestampWord,
                Solm.EVM.storageLoad, State.lookupAccount] using htimeS)
            (by
              simpa [evmS, initState, auctionEndEndedWordState, auctionEndEndedRawWordState,
                auctionEndEndedWord, Solm.EVM.storageLoad, State.lookupAccount] using hendedS)
        exact (simpleAuctionX_auctionEnd_endedRevert (g := Sat256.ofUInt256 g) hwv hreach
            htimeLe hendedBad)
          |>.reEquivExecutionRevert hcode hd hdec hbody
  · have hbody :
        ExecTransitionBody simpleAuctionConfig simpleAuctionContract evmS ∅
          auctionEndTransition.body .reverted :=
      simpleAuctionAuctionEndBodyReverts_nonpayable
        (by simpa [evmS, initState] using hwv)
    exact (simpleAuctionX_auctionEnd_nonpayable (g := Sat256.ofUInt256 g) hwv hreach)
      |>.reEquivExecutionRevert hcode hd hdec hbody

end SimpleAuction
