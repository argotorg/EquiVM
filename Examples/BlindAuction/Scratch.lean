import Examples.BlindAuction.Reveal
import Examples.BlindAuction.Bids
import Examples.BlindAuction.HighestBidder

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 10000000
set_option maxHeartbeats 800000

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
  have rd1391 := RD.returndatacopy
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
    exact byteArray_readWithPadding_zero _ _
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
  rw [hmin, byteArray_write_len_zero, hawCall] at rd1350₀
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
  rw [Reasoning.Theory.u256_land_comm (UInt256.lnot solcAddrMask) old]
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
    rw [Reasoning.Theory.u256_land_comm solcAddrMask (scratch_placeBidHighestBidderWord σ I)]
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
  have rd1650 := RD.lor rd1649 (by decide) (by evm_ov)
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
  rw [byteArray_extract_two_chunks_0]
  · have hM0 : M.extract 0 32 = UInt256.toByteArray key := by
      dsimp [M]
      rw [← readWithPadding_eq_extract (scratch_placeBidPendingKeyMem mem key) 0
        (by rw [scratch_placeBidPendingKeyMem_size mem key hmem]; omega)]
      exact scratch_placeBidPendingKeyMem_read0 mem key hmem
    have hSself : S.extract 0 32 = S := by
      dsimp [S]
      rw [show 32 = (UInt256.toByteArray (⟨7⟩ : UInt256)).size by rw [toByteArray_size]]
      exact byteArray_extract_self _
    rw [hM0, hSself]
  · rw [ByteArray.size_extract]
    dsimp [M]
    rw [scratch_placeBidPendingKeyMem_size mem key hmem]
    norm_num
  · rw [ByteArray.size_extract]
    dsimp [S]
    rw [toByteArray_size]
    norm_num

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
    rw [Reasoning.Theory.u256_land_comm solcAddrMask (scratch_placeBidHighestBidderWord σ I)]
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
    exact Reasoning.Theory.u256_land_comm solcAddrMask (scratch_placeBidHighestBidderWord σ I)
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
  have rd1650 := RD.lor rd1649 (by decide) (by evm_ov)
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
    {s0 : State} {k C : ℕ} {mem : ByteArray} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {secret value slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen
      fakesEnd valuesLen valuesEnd sel deposit : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1265⟩
      [secret, ⟨0⟩, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmem : mem.size = 96)
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
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1014⟩
      (scratch_revealEvmLoopStack (i + ⟨1⟩) (UInt256.sub refund value) len revealEnd
        biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
      (scratch_placeBidPendingHashMem mem
        (UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask))
      (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap I.codeOwner
        (scratch_placeBidStoreBidderMap
          (scratch_placeBidStoreHighMap
            (scratch_placeBidStorePendingMap σ I
              (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I)) I value)
          I (UInt256.ofNat I.source.val)) slot ⟨0⟩) k' C' := by
  obtain ⟨_, _, rd1534⟩ :=
    scratch_blindAuctionRevealX_placeCond_place_toRoutine rd hdeposit hdepositGe
  obtain ⟨_, _, rd1297⟩ :=
    scratch_RD_placeBid_true_nonzero
      (value := value) (bidder := UInt256.ofNat I.source.val) (ret := ⟨1297⟩)
      (R := [secret, ⟨0⟩, value, slot, i, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel])
      rd1534 hperm hmem hplaceTrue hhighestBidderNonzero
      (scratch_revealSourceWord_canonical I) hsum (by jump_dest) (by simp)
  exact scratch_blindAuctionRevealX_placeBidTrue_toNext rd1297 hrefund hperm

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

end BlindAuction
