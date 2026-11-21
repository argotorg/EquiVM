import Benchmarks.Midnight.BuyCallback

/-! The optional buyer callback rejoins the two token transfers. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def takeBuyDataFrame (frame : Frame) (offer : OfferData) (data : ByteArray) : Frame :=
  { frame with locals := frame.locals.insert "buyerCallbackData" (.bytes (takeBuyerData offer data)) }

theorem takeBuyCondition_eval {frame : Frame} {evm : State} {callback : AccountAddress}
    (hc : frame.locals.get? "buyerCallback" = some (.address callback)) :
    evalExpr? config frame evm takeBuyCondition = .ok (.bool (decide (callback ≠ 0))) := by
  have hcast : castValue? (.int 0) (.elem .address) = some (.address 0) := rfl
  simp only [takeBuyCondition, evalExpr?, hc, EvalResult.ofOption,
    EvalResult.bind, bind, pure, hcast, evalBinaryOp?]
  by_cases hz : callback = 0 <;> simp [hz]

theorem takeBuyStmt_shape : takeTransition.body[67]! =
    .ite takeBuyCondition
      [.letDecl "buyerCallbackData" (some .bytes) takeBuyerDataExpr,
        buyCallbackStmt, .require buyMagicGuard] [] := by decide +kernel

theorem midnightTakeBuyCallback {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {frame : Frame} {mem rdata data : ByteArray}
    {aw root market arrayPtr offerRoot callbackPtr takerPtr id assets units fee user
      sellerCallback payer wasLocked saved : UInt256} {offer : OfferData}
    {callback : AccountAddress} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 30 ≤ 1024)
    (ho : OfferStored mem ⟨832⟩ market arrayPtr callbackPtr offerRoot offer)
    (hlimit : offerRoot.toNat ≤ root.toNat)
    (hused : root.toNat ≤ mem.size)
    (hroot : root.toNat + 32 < 2^64) (hlo : 832 ≤ root.toNat) (hmem : 608 ≤ mem.size)
    (hd : MemoryByteString mem takerPtr data)
    (hbelow : takerPtr.toNat + 32 + paddedSize data.size ≤ root.toNat)
    (hoffer : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (htaker : memLoad (UInt256.ofNat 320) mem = takerPtr)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hid : memLoad (UInt256.ofNat 512) mem = id)
    (haRead : memLoad (UInt256.ofNat 256) mem = assets)
    (huRead : calldataWord I.calldata 68 = units)
    (hfRead : memLoad (UInt256.ofNat 224) mem = fee)
    (hbRead : memLoad (UInt256.ofNat 576) mem = user)
    (hf128 : fee.toNat < 2^128) (huser : user.toNat < EVM.addressModulus)
    (hfOffer : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hfData : frame.locals.get? "takerCallbackData" = some (.bytes data))
    (hfId : frame.locals.get? "id" = some (wordBytes32Value id))
    (hfAssets : frame.locals.get? "buyerAssets" = some (.int assets.toNat))
    (hfUnits : frame.locals.get? "units" = some (.int units.toNat))
    (hfFee : frame.locals.get? "buyerPendingFeeIncrease" = some (.int fee.toNat))
    (hfUser : frame.locals.get? "buyer" = some (.address (AccountAddress.ofNat user.toNat)))
    (ht : frame.locals.get? "buyerCallback" = some (.address callback))
    (ha : MemoryFunding credit mem aw C) (hs : SourceState s0 I σ evm)
    (rd : RD midnightBytecode I g s0
      (if UInt256.ofNat callback.val = ⟨0⟩ then ⟨13252⟩ else ⟨13774⟩)
      ([UInt256.ofNat callback.val, sellerCallback, payer, wasLocked, saved] ++ R)
      mem aw rdata σ k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecStmt config frame evm takeTransition.body[67]! .reverted ∧
      RDrev midnightBytecode g s0) ∨
    ∃ (frame' : Frame) (evm' : State) (σ' : AccountMap) (mem' out : ByteArray)
      (root' aw' ignored : UInt256) (k' C' : Nat),
      ExecStmt config frame evm takeTransition.body[67]! (.ok frame' evm') ∧
      frame'.contract = frame.contract ∧
      (∀ name, name ≠ "buyerCallbackData" → name ≠ "__c27" →
        frame'.locals.get? name = frame.locals.get? name) ∧
      SourceState s0 I σ' evm' ∧ MemoryPrefix mem mem' root.toNat ∧
      (root' = root ∨ root' = root + UInt256.ofNat 32) ∧
      root'.toNat ≤ mem'.size ∧
      memLoad (UInt256.ofNat 64) mem' = root' ∧ MemoryFunding credit mem' aw' C' ∧
      RD midnightBytecode I g s0 ⟨13252⟩
        ([ignored, sellerCallback, payer, wasLocked, saved] ++ R) mem' aw' out σ' k' C' := by
  rw [takeBuyStmt_shape]
  have hc := takeBuyCondition_eval (evm := evm) ht
  have hz : UInt256.ofNat callback.val = ⟨0⟩ ↔ callback = 0 := by
    rw [← accountAddress_roundtrip callback]
    constructor
    · intro h
      have hh := congrArg AccountAddress.ofUInt256 h
      simpa only [accountAddress_roundtrip] using hh
    · intro h
      rw [h]
      rfl
  by_cases hcb : callback = 0
  · rw [if_pos (hz.mpr hcb)] at rd
    refine Or.inr (Or.inr ⟨frame, evm, σ, mem, rdata, root, aw,
      UInt256.ofNat callback.val, k, C, ?_, rfl, ?_, hs, MemoryPrefix.refl _ _,
      Or.inl rfl, hused, hfree, ha, rd⟩)
    · exact ExecStmt.iteFalse (by simpa only [hcb, ne_eq, not_true_eq_false, decide_false] using hc)
        ExecBlock.nil
    · intros; rfl
  · rw [if_neg (fun h ↦ hcb (hz.mp h))] at rd
    obtain ⟨aw1, k1, C1, ha1, rd1⟩ := midnightTakeBuyerData
      (by change R.length + 9 ≤ 1024; omega) ho hoffer htaker ha rd
    have hdata := takeBuyerData_stored ho.callback hd
    have hdataBelow : (takeBuyerDataPtr offer callbackPtr takerPtr).toNat + 32 +
        paddedSize (takeBuyerData offer data).size ≤ root.toNat := by
      have hh := ho.extent
      by_cases hb : offer.buy = ⟨0⟩
      · simpa only [takeBuyerDataPtr, takeBuyerData, if_pos hb] using hbelow
      · simp only [takeBuyerDataPtr, takeBuyerData, if_neg hb]
        omega
    have hmarket : memLoad (memLoad (UInt256.ofNat 384) mem) mem = market := by
      rw [hoffer]
      exact ho.words.load_offset ⟨0, by change 0 < 15; decide⟩ rfl
    let frame1 := takeBuyDataFrame frame offer data
    have hget (name : Ident) (hn : name ≠ "buyerCallbackData") :
        frame1.locals.get? name = frame.locals.get? name :=
      store_get_ne _ _ (by simpa using hn.symm)
    have hargs := buyCallbackArgs (frame := frame1) (evm := evm)
      ((hget _ (by decide)).trans hfOffer) ((hget _ (by decide)).trans hfId)
      ((hget _ (by decide)).trans hfAssets) ((hget _ (by decide)).trans hfUnits)
      ((hget _ (by decide)).trans hfFee) ((hget _ (by decide)).trans hfUser)
      (by exact store_get_self _ _ _)
    have hdecl : ExecStmt config frame evm
        (.letDecl "buyerCallbackData" (some .bytes) takeBuyerDataExpr) (.ok frame1 evm) :=
      ExecStmt.letDecl (evalTakeBuyerData hfOffer hfData)
    have hcond : evalExpr? config frame evm takeBuyCondition = .ok (.bool true) := by
      simpa only [decide_eq_true hcb] using hc
    rcases midnightBuyCallback offer.market (by change R.length + 30 ≤ 1024; exact hstack)
        ho.market (by have hh := ho.extent; omega) hroot hlo hmem hdata hdataBelow hmarket hfree hid haRead huRead
        hfRead hbRead hf128 huser ((hget _ (by decide)).trans ht) hargs ha1 hs rd1 with
      hoog | ⟨hx, hr⟩ | ⟨evm', σ', out, mem', aw2, k2, C2, hx, hs', hp, hfree', hm', ha2, rd2⟩
    · exact Or.inl hoog
    · exact Or.inr (Or.inl ⟨ExecStmt.iteTrue hcond (ExecBlock.consNormal hdecl hx), hr⟩)
    · have rd3 := midnightBlocks.midnight_block_13971
        (by change R.length + 6 ≤ 1024; omega) (by jump_dest) rd2
      have ha3 := memoryFundingAt (credit := credit) rd3
        ((ha2.weaken (by omega)).mono (by omega))
      refine Or.inr (Or.inr ⟨buyCallbackFrame frame1 (calldataWord out 0), evm', σ', mem', out, root + UInt256.ofNat 32, _, saved,
        _, _, ExecStmt.iteTrue hcond (ExecBlock.consNormal hdecl hx), rfl, ?_, hs', hp,
        Or.inr rfl, ?_, hfree', ha3, rd3⟩)
      · intro name hn hn'
        exact (store_get_ne _ _ (by simpa using hn'.symm)).trans (hget name hn)
      · rw [uadd_word_ofNat_toNat root 32 (by change _ < 2^256; omega)]
        exact hm'

end Benchmarks.Midnight
