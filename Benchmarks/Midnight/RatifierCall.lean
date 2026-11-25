import Benchmarks.Midnight.RatifierInputMemory
import Benchmarks.Midnight.RatifierSource
import Benchmarks.Midnight.RatifierReturn
import Benchmarks.Midnight.StaticCallBridgeGas

variable {fork : Ethereum.Fork}

/-! The full ratifier call: calldata construction, static call, decoding, and acknowledgement. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

set_option maxHeartbeats 800000 in
theorem midnightRatifierCall {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {frame : Frame} {mem rdata data : ByteArray}
    {aw ptr marketPtr arrayPtr callbackPtr offerRoot root ratifierPtr : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (offer : OfferData) (taker : AccountAddress)
    (hstack : R.length + 30 ≤ 1024) (hmem : 576 ≤ mem.size) (hlower : 576 ≤ root.toNat)
    (ho : OfferStored mem ptr marketPtr arrayPtr callbackPtr offerRoot offer)
    (hc : OfferCanonical offer) (hb : MemoryByteString mem ratifierPtr data)
    (hbelow : offerRoot.toNat ≤ root.toNat)
    (hrat : ratifierPtr.toNat + 32 + paddedSize data.size ≤ root.toNat)
    (hroot : root.toNat + 32 < 2^64) (hlen : ratifierCalldataSize offer data < 2^64)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hptr : memLoad (UInt256.ofNat 384) mem = ptr)
    (htaker : memLoad (UInt256.ofNat 544) mem = UInt256.ofNat taker.val)
    (hof : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hdf : frame.locals.get? "ratifierData" = some (.bytes data))
    (htf : frame.locals.get? "taker" = some (.address taker))
    (hs : SourceState s0 I σ evm) (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨11276⟩ (ratifierPtr :: R) mem aw rdata σ k C) :
    (ExecBlock fork config frame evm [ratifierCallStmt, .require ratifierMagicGuard] .reverted ∧
      RDrev fork midnightBytecode g s0) ∨
    ∃ (evm' : State) (σ' : AccountMap) (mem' out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      ExecBlock fork config frame evm [ratifierCallStmt, .require ratifierMagicGuard]
        (.ok (ratifierCallFrame frame flashLoanMagic) evm') ∧ SourceState s0 I σ' evm' ∧
      MemoryPrefix mem mem' root.toNat ∧ memLoad (UInt256.ofNat 64) mem' = root + UInt256.ofNat 32 ∧
      root.toNat + 32 ≤ mem'.size ∧
      MemoryFunding (credit + 128 * offer.market.collaterals.length +
        3 * ((offer.callbackData.size + 31) / 32) + 3 * ((data.size + 31) / 32)) mem' aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨11413⟩ (ratifierPtr :: R) mem' aw' out σ' k' C' := by
  have hout : root.toNat + ratifierCalldataSize offer data + 64 < UInt256.size := by
    change _ < 2^256
    omega
  have hcpad : paddedSize offer.callbackData.size < 2^64 := by
    have he := ho.extent
    have hb := ho.bound
    omega
  have hbpad : paddedSize data.size < 2^64 := by omega
  have hcbelow : callbackPtr.toNat + 32 + paddedSize offer.callbackData.size ≤ root.toNat :=
    ho.extent.trans hbelow
  obtain ⟨gasArg, aw1, k1, C1, ha1, rd1⟩ := midnightRatifierPrepare offer taker hstack hmem hlower
    ho hc hb hbelow hrat hout hfree hptr htaker ha rd
  let input := ratifierInputMemory mem root callbackPtr ratifierPtr offer data taker
  have hn : (UInt256.ofNat (ratifierCalldataSize offer data)).toNat =
      ratifierCalldataSize offer data := UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)
  obtain ⟨hsize, hread, hp⟩ := ratifierInputMemory_read offer taker ho.callback hb hcpad hbpad
    hcbelow hrat hout
  change root.toNat + ratifierCalldataSize offer data ≤ input.size at hsize
  have h32 : root.toNat + 32 ≤ input.size := by
    unfold ratifierCalldataSize at hsize
    omega
  have hcover := ha1.covered
  change input.size ≤ 32 * aw1.toNat at hcover
  have hin : root.toNat + (UInt256.ofNat (ratifierCalldataSize offer data)).toNat ≤
      32 * aw1.toNat := by rw [hn]; omega
  have houtput : root.toNat + (UInt256.ofNat 32).toNat ≤ 32 * aw1.toNat := by
    change root.toNat + 32 ≤ _
    omega
  have hcd : config.externalABI.encode? "isRatified" (ratifierArguments offer data taker) =
      some (input.readWithPadding root.toNat
        (UInt256.ofNat (ratifierCalldataSize offer data)).toNat) := by
    rw [hn, show input = _ from rfl, hread]
    exact encodeRatifierCall offer data taker hc
  obtain ⟨evm', σ', success, out, k2, C2, hcall, hs', hC, rd2, hout2⟩ :=
    typedStaticCallBridgeMono rd1 hs (by native_decide) hcd (by rw [hn]; omega)
      (by change R.length + 3 ≤ 1024; omega)
  have ha2 := staticCallMemoryFunding (out := out) ha1 hC hin houtput
  have hout' : out.size < UInt256.size := by change _ < 2^256; omega
  have hreply := wordReplyMemory_eq input out root hout'
  change out.write 0 input root.toNat (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat =
    wordReplyMemory input out root at hreply
  dsimp only [input] at hreply
  rw [hreply] at rd2
  rw [wordReplyMemory_eq _ out root hout'] at ha2
  have hcall' : typedCallViaEVM fork config evm offer.ratifier "isRatified" 0
      (ratifierArguments offer data taker) (success, evm', out) false := by
    simpa only [accountAddress_roundtrip] using hcall
  rcases midnightRatifierReturn success (by change R.length + 12 ≤ 1024; omega)
      hout' hroot (by omega) h32 ha2 rd2 with
    ⟨hbad, hrev⟩ | ⟨htrue, hlong, he, aw3, k3, C3, ha3, rd3⟩
  · refine Or.inl ⟨?_, hrev⟩
    cases success with
    | false => exact .consRevert (ratifierCallFailure hof hdf htf hcall')
    | true =>
      by_cases hshort : out.size < 32
      · exact .consRevert (ratifierCallShort hof hdf htf hcall' hshort)
      · have hne : calldataWord out 0 ≠ flashLoanMagic := by simpa [hshort] using hbad
        refine .consNormal (ratifierCallSuccess hof hdf htf hcall' (by omega))
          (.consRevert (.requireFalse ?_))
        rw [ratifierMagicGuard_eval, decide_eq_false hne]
  · subst success
    let final := flashLoanCallbackResultMemory (wordReplyMemory input out root) root
    have hreplysize : (wordReplyMemory input out root).size = input.size :=
      wordReplyMemory_size _ _ _ h32
    have hfinalsize : final.size = input.size := by
      rw [show final = _ from rfl, callbackResultMemory_size _ _ (by rw [hreplysize]; omega),
        hreplysize]
    refine Or.inr ⟨evm', σ', final, out, aw3, k3, C3, ?_, hs', ?_, ?_, ?_, ha3, rd3⟩
    · refine .consNormal (by simpa only [he] using ratifierCallSuccess hof hdf htf hcall' hlong)
        (.consNormal (.requireTrue ?_) .nil)
      rw [ratifierMagicGuard_eval, decide_eq_true rfl]
    · exact hp.trans ((wordReplyMemory_prefix input out root root.toNat h32 le_rfl).trans
        (callbackResultMemory_prefix _ _ _))
    · exact callbackResultMemory_free _ _ (by rw [hreplysize]; omega)
    · rw [hfinalsize]
      exact h32

end Benchmarks.Midnight
