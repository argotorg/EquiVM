import Benchmarks.Midnight.TakeGatePrepare
import Benchmarks.Midnight.TakeGateSource
import Benchmarks.Midnight.StaticCallBridgeGas
import Benchmarks.Midnight.WordReplyMemory

variable {fork : Ethereum.Fork}

/-! Entry-gate STATICCALLs agree with their opaque source calls. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeGateCall {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {offer : OfferData} {mem rdata : ByteArray}
    {aw root flag : UInt256} {user : AccountAddress} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (kind : TakeGateKind)
    (hstack : R.length + 10 ≤ 1024) (hroot : root.toNat + 36 < 2^64)
    (hlower : 608 ≤ root.toNat) (hm : 608 ≤ mem.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (huser : memLoad kind.userOffset mem = UInt256.ofNat user.val)
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hu : frame.locals.get? kind.userName = some (.address user))
    (hs : SourceState s0 I σ evm) (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 kind.preparePC
      (UInt256.ofNat offer.market.enterGate.val :: flag :: R) mem aw rdata σ k C) :
    (ExecStmt fork config frame evm (takeGateCall kind) .reverted ∧
      RDrev fork midnightBytecode g s0) ∨
    ∃ (evm' : State) (σ' : AccountMap) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      ExecStmt fork config frame evm (takeGateCall kind)
        (.ok (takeGateAllowedFrame frame (calldataWord out 0)) evm') ∧
      typedCallViaEVM fork config evm offer.market.enterGate kind.name 0 [.address user]
        (true, evm', out) false ∧
      SourceState s0 I σ' evm' ∧ 32 ≤ out.size ∧
      (calldataWord out 0 = ⟨0⟩ ∨ calldataWord out 0 = ⟨1⟩) ∧
      MemoryPrefix mem (takeGateResultMemory kind mem root user out) root.toNat ∧
      memLoad (UInt256.ofNat 64) (takeGateResultMemory kind mem root user out) =
        root + UInt256.ofNat 32 ∧
      MemoryFunding credit (takeGateResultMemory kind mem root user out) aw' C' ∧
      RD fork midnightBytecode I g s0 kind.decodedPC (calldataWord out 0 :: R)
        (takeGateResultMemory kind mem root user out) aw' out σ' k' C' := by
  have hargs : evalExprs? config frame evm [.var kind.userName] = .ok [.address user] := by
    simp only [evalExprs?, evalExpr?, hu, EvalResult.ofOption, bind, pure, EvalResult.bind]
  obtain ⟨gas, aw1, k1, C1, ha1, rd1⟩ :=
    midnightTakeGatePrepare kind hstack hroot hlower hm hfree huser ha rd
  obtain ⟨evm', σ', success, out, k2, C2, hcall, hs', hc2, rd2, hout⟩ :=
    typedStaticCallBridgeMono (cfg := config) (name := kind.name) (args := [.address user])
      (R := root :: R) rd1 hs (by cases kind <;> native_decide)
      (by change _ = some ((takeGateCallMemory kind mem root user).readWithPadding root.toNat 36)
          rw [takeGateCallMemory_read]; exact encodeTakeGate kind user)
      (by decide) (by simp only [List.length_cons]; omega)
  have ha2 := memoryFundingAt (credit := credit) rd2 (by
    refine staticCallMemoryFunding ha1 hc2 ?_ ?_
    all_goals
      have hcov := ha1.covered
      simp only [MemoryCovered, takeGateCallMemory_size] at hcov
      change root.toNat + _ ≤ _
      simp only [show (UInt256.ofNat 36).toNat = 36 from rfl,
        show (UInt256.ofNat 32).toNat = 32 from rfl]
      omega)
  have hout' : out.size < UInt256.size := by change out.size < 2^256; omega
  rw [wordReplyMemory_eq _ _ _ hout'] at rd2 ha2
  have hpc : kind.callPC + ⟨1⟩ = kind.resumePC := by cases kind <;> rfl
  rw [hpc] at rd2
  have hcovered : root.toNat + 32 ≤ (takeGateCallMemory kind mem root user).size := by
    rw [takeGateCallMemory_size]
    omega
  have hword : 32 ≤ out.size → memLoad root
      (writeWord (wordReplyMemory (takeGateCallMemory kind mem root user) out root)
        64 (root + UInt256.ofNat 32)) = calldataWord out 0 := by
    intro h32
    rw [memLoad_writeWord_preserved _ _ _ _ (by
      rw [wordReplyMemory_size _ _ _ hcovered]; exact hcovered) (Or.inr (by omega)),
      wordReplyMemory_load _ _ _ hcovered h32]
  simp only [accountAddress_roundtrip] at hcall
  have hsourceCall : typedCallViaEVM fork config evm (EVM.address offer.market.enterGate.val)
      kind.name 0 [.address user] (success, evm', out) false := by
    simpa only [address_of_val] using hcall
  rcases midnightTakeGateReturn kind success hstack hout' (by omega) hword ha2 rd2 with
    ⟨hbad, hrev⟩ | ⟨htrue, h32, hbool, aw3, k3, C3, ha3, rd3⟩
  · refine Or.inl ⟨?_, hrev⟩
    rcases hbad with hfalse | hdecode
    · subst success
      exact ExecStmt.externalCallFailure (Or.inl wordOfInt_zero) (evalTakeGateReceiver ho)
        (by simp only [evalExpr?, pure]) hargs hsourceCall
    · cases success with
      | false =>
        exact ExecStmt.externalCallFailure (Or.inl wordOfInt_zero) (evalTakeGateReceiver ho)
          (by simp only [evalExpr?, pure]) hargs hsourceCall
      | true =>
        exact ExecStmt.externalCallReturnDecodeRevert (Or.inl wordOfInt_zero)
          (evalTakeGateReceiver ho) (by simp only [evalExpr?, pure]) hargs hsourceCall
          (by rw [decodeTakeGate, if_neg hdecode])
  · subst success
    simp only [wordReplyMemory, Nat.min_eq_left h32] at rd3 ha3
    have hp := takeGateResultMemory_properties kind mem root user h32 (by omega)
    refine Or.inr ⟨evm', σ', out, aw3, k3, C3, ?_, hcall, hs', h32, hbool,
      hp.2.2.2, hp.2.1, ha3, rd3⟩
    exact ExecStmt.externalCallSuccess (value := [wordToElem .bool (calldataWord out 0)])
      (Or.inl wordOfInt_zero) (evalTakeGateReceiver ho)
      (by simp only [evalExpr?, pure]) hargs hsourceCall
      (by rw [decodeTakeGate, if_pos ⟨h32, hbool⟩])

end Benchmarks.Midnight
