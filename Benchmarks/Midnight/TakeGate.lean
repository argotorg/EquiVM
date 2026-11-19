import Benchmarks.Midnight.TakeGateControl
import Benchmarks.Midnight.TakeGateCall

/-! A complete entry gate, including the condition, static call, and require. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeGate {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {offer : OfferData} {mem rdata : ByteArray}
    {aw root marketPtr arrayPtr callbackPtr offerRoot buyerSlot debt buyerDebt sellerSlot
      marketSlot decrease ratifierPtr increase saved : UInt256}
    {user : AccountAddress} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (kind : TakeGateKind) (hstack : R.length + 19 ≤ 1024)
    (hroot : root.toNat + 36 < 2^64) (hlower : 608 ≤ root.toNat) (hm : 608 ≤ mem.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (huser : memLoad kind.userOffset mem = UInt256.ofNat user.val)
    (hof : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hu : frame.locals.get? kind.userName = some (.address user))
    (hd : frame.locals.get? kind.deltaName = some (.int (kind.delta increase debt).toNat))
    (hs : SourceState s0 I σ evm)
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr offerRoot offer)
    (hoffer : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 kind.startPC
      ([buyerSlot, debt, buyerDebt, sellerSlot, marketSlot, decrease, ratifierPtr, increase,
        saved] ++ R) mem aw rdata σ k C) :
    (ExecStmt config frame evm (takeGateStmt kind) .reverted ∧
      RDrev midnightBytecode g s0) ∨
    ∃ (frame' : Frame) (evm' : State) (σ' : AccountMap) (mem' rdata' : ByteArray)
      (root' aw' : UInt256) (k' C' : Nat),
      ExecStmt config frame evm (takeGateStmt kind) (.ok frame' evm') ∧
      (frame' = frame ∨ frame' = takeGateAllowedFrame frame ⟨1⟩) ∧
      SourceState s0 I σ' evm' ∧ accountStorageStateEq evm.accountMap evm'.accountMap ∧
      MemoryPrefix mem mem' root.toNat ∧
      root.toNat ≤ root'.toNat ∧ root'.toNat ≤ root.toNat + 32 ∧
      root'.toNat % 32 = root.toNat % 32 ∧
      memLoad (UInt256.ofNat 64) mem' = root' ∧ MemoryFunding credit mem' aw' C' ∧
      RD midnightBytecode I g s0 kind.finishPC
        ([buyerSlot, debt, buyerDebt, sellerSlot, marketSlot, decrease, ratifierPtr, increase,
          saved] ++ R) mem' aw' rdata' σ' k' C' := by
  simp only [List.cons_append, List.nil_append] at rd
  rcases midnightTakeGateHead kind (by simp only [List.length_cons]; omega) ho hoffer ha rd with
    ⟨hn, aw1, k1, C1, ha1, rd1⟩ | ⟨hn, aw1, k1, C1, ha1, rd1⟩
  · exact Or.inr ⟨frame, evm, σ, mem, rdata, root, aw1, k1, C1,
      takeGateSkipped kind hof hd hn, Or.inl rfl, hs, accountStorageStateEq_refl _,
      MemoryPrefix.refl _ _, le_rfl, by omega, rfl, hfree, ha1, rd1⟩
  · rcases midnightTakeGateCall
        (R := [buyerSlot, debt, buyerDebt, sellerSlot, marketSlot, decrease, ratifierPtr,
          increase, saved] ++ R) kind
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
        hroot hlower hm hfree huser hof hu hs ha1 rd1 with
      ⟨hcall, hrev⟩ | ⟨evm', σ', out, aw2, k2, C2, hcall, htyped, hs', h32, hbool,
        hp, hfree2, ha2, rd2⟩
    · exact Or.inl ⟨takeGateFailed kind hof hd hn hcall, hrev⟩
    · rcases midnightTakeGateTail kind (by omega) hbool ha2 rd2 with
        ⟨hz, hr⟩ | ⟨hone, k3, C3, ha3, rd3⟩
      · exact Or.inl ⟨takeGateDenied kind hof hd hn (by simpa only [hz] using hcall), hr⟩
      · have hr : (root + UInt256.ofNat 32).toNat = root.toNat + 32 :=
          uadd_word_ofNat_toNat _ 32 (by change _ < 2^256; omega)
        exact Or.inr ⟨takeGateAllowedFrame frame ⟨1⟩, evm', σ',
          takeGateResultMemory kind mem root user out, out, root + UInt256.ofNat 32,
          aw2, k3, C3, takeGateAllowed kind hof hd hn (by simpa only [hone] using hcall),
          Or.inr rfl, hs', typedCallViaEVM_static_accountStorageStateEq htyped,
          hp, by rw [hr]; omega, by rw [hr], by rw [hr]; omega, hfree2, ha3, rd3⟩

end Benchmarks.Midnight
