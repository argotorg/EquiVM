import Benchmarks.CompoundIII.Comet.ConstructorRemainingImmsEvm
import Benchmarks.CompoundIII.Comet.ConstructorRemainingImmsSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def constructorFactoryPayload : ByteArray := ByteArray.mk #[112, 66, 226, 216]

theorem constructorFactoryPayload_encode : config.externalABI.encode? "assetListFactory" [] =
    some constructorFactoryPayload := by
  change encodeCallWithSelector? (selectorBytes 112 66 226 216) [] [] = _
  simp only [encodeCallWithSelector?, encodeABIValues?, abiTupleHeadSize?,
    encodeABIValuesFrom?, bind, Option.bind]
  decide +kernel

def ConstructorFactoryReturnValid (out : ByteArray) : Prop :=
  32 ≤ out.size ∧ (calldataWord out 0).toNat < 2^160

instance (out : ByteArray) : Decidable (ConstructorFactoryReturnValid out) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem constructorFactory_decode {out : ByteArray} (hhi : out.size < 2^255) :
    config.externalABI.decode? "assetListFactory" out =
      if ConstructorFactoryReturnValid out then
        some [.address (AccountAddress.ofUInt256 (calldataWord out 0))] else none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  change (decodeReturnValue? (.elem .address) out).map (fun v ↦ [v]) = _
  unfold decodeReturnValue?
  rw [decodeReturnValues_scalarWords_eq (by decide),
    if_neg (by simp only [List.isEmpty_cons, hlen]; omega)]
  by_cases hlo : 32 ≤ out.size
  · have ht : ((out.toList.drop 0).take 32).length = 32 := by
      simp only [List.drop_zero, List.length_take, hlen]; omega
    simp only [decodeScalarWords?, decodeScalarWord_address_result ht,
      decode_word_at_eq_any out 0 (by omega)]
    by_cases hc : (calldataWord out 0).toNat < 2^160 <;>
      simp only [ConstructorFactoryReturnValid, hlo, true_and, EVM.addressModulus, EVM.twoPow,
        hc, if_true, if_false, bind, Option.bind, Option.map]
    rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  · have ht : ¬ ((out.toList.drop 0).take 32).length = 32 := by
      simp only [List.drop_zero, List.length_take, hlen]; omega
    simp only [decodeScalarWords?, decodeScalarWord?, readWord?, readBytes?, if_neg ht,
      bind, Option.bind, Option.map, ConstructorFactoryReturnValid, hlo, false_and, if_false]

theorem constructorFactory_typed {evm evm' : EVM.State} {delegate : AccountAddress}
    {z : Bool} {out : ByteArray}
    (hc : callViaEVM evm delegate 0 constructorFactoryPayload (z, evm', out) false) :
    typedCallViaEVM config evm delegate "assetListFactory" 0 [] (z, evm', out) false :=
  ⟨_, constructorFactoryPayload_encode, hc⟩

theorem constructorFactory_source_ok {frame : Frame} {evm evm' : EVM.State}
    {delegate : AccountAddress} {expr : Expr} {ret : Ident} {out : ByteArray}
    (he : evalExpr? config frame evm expr = .ok (.address delegate))
    (hc : callViaEVM evm delegate 0 constructorFactoryPayload (true, evm', out) false)
    (hhi : out.size < 2^255) (hv : ConstructorFactoryReturnValid out) :
    ExecStmt config frame evm
      (.externalCall expr "assetListFactory" (.intLit 0) [] ret (perm := false))
      (.ok { frame with locals := (frame.locals.insert ret
        (.address (AccountAddress.ofUInt256 (calldataWord out 0)))) } evm') := by
  rw [← addressOfAddress delegate] at hc
  exact ExecStmt.externalCallSuccess (eth := .intLit 0) (args := []) he
    (by simp only [evalExpr?, pure]) (by rfl) (constructorFactory_typed hc)
    (by rw [constructorFactory_decode hhi, if_pos hv])

theorem constructorFactory_source_revert {frame : Frame} {evm evm' : EVM.State}
    {delegate : AccountAddress} {expr : Expr} {ret : Ident} {z : Bool} {out : ByteArray}
    (he : evalExpr? config frame evm expr = .ok (.address delegate))
    (hc : callViaEVM evm delegate 0 constructorFactoryPayload (z, evm', out) false)
    (hhi : out.size < 2^255) (hv : ¬ (z = true ∧ ConstructorFactoryReturnValid out)) :
    ExecStmt config frame evm
      (.externalCall expr "assetListFactory" (.intLit 0) [] ret (perm := false)) .reverted := by
  rw [← addressOfAddress delegate] at hc
  cases z with
  | false =>
    exact ExecStmt.externalCallFailure he
      (by simp only [evalExpr?, pure]) (by rfl) (constructorFactory_typed hc)
  | true =>
    exact ExecStmt.externalCallReturnDecodeRevert he
      (by simp only [evalExpr?, pure]) (by rfl) (constructorFactory_typed hc)
      (by rw [constructorFactory_decode hhi, if_neg (fun h ↦ hv ⟨rfl, h⟩)])

theorem cometConstructorFactoryCall {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {σ : AccountMap} {c : ConstructorConfig} {mem rdata : ByteArray}
    {aw ptr base : UInt256} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hp : mem.readWithPadding ptr.toNat 4 = constructorFactoryPayload)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨1291⟩
      ((g.subNat C).toUInt256 :: constructorRecordWord c 4 :: ptr :: ⟨4⟩ :: ptr :: ⟨32⟩ ::
        base :: ptr :: R) mem aw rdata σ k C) :
    ∃ evm' σ' z out aw' k' C',
      callViaEVM evm c.extensionDelegate 0 constructorFactoryPayload (z, evm', out) false ∧
      SourceState s0 ee σ' evm' ∧ out.size < 2^138 ∧
      RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨1292⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: base :: ptr :: R)
        (callOutputMem mem out ptr ⟨32⟩) aw' out σ' k' C' := by
  have hdec : decode (cometWithExtendedAssetListCreationBytecode ++ tail) ⟨1291⟩ =
      some (.STATICCALL, .none) :=
    decode_append_left_of_decode _ _ _ _ _ (by native_decide)
      (by rw [cometCreationBytecode_size]; decide) (by decide)
  obtain ⟨evm', σ', z, out, k', C', hc, hs', hr, ho⟩ := staticCallBridge h hs hdec hp
    (by change 4 ≤ _; decide) (by change R.length + 2 + 1 ≤ 1024; omega)
  have ha : AccountAddress.ofUInt256 (constructorRecordWord c 4) = c.extensionDelegate :=
    accountAddress_roundtrip c.extensionDelegate
  rw [ha] at hc
  exact ⟨evm', σ', z, out, _, k', C', hc, hs', ho, hr⟩

def constructorSourceFactory (c : ConstructorConfig) (w feed factory : UInt256) : Frame :=
  let frame := constructorSourceDelegate c w feed
  { frame with locals := frame.locals.insert "__c2" (.address (AccountAddress.ofUInt256 factory)) }

theorem constructorSourceDelegate_eval {c : ConstructorConfig} {w feed : UInt256}
    {evm : EVM.State} :
    evalExpr? config (constructorSourceDelegate c w feed) evm (.var "delegate") =
      .ok (.address c.extensionDelegate) := by
  simp only [evalExpr?, constructorSourceDelegate, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert, EvalResult.ofOption]
  rfl

theorem constructorSourceFactory_exec {c : ConstructorConfig} {w feed : UInt256}
    {evm evm' evm'' : EVM.State} {out : ByteArray}
    (hp : ExecBlock config (constructorSourceEntry c) evm (contract.ctor.body.take 35)
      (.ok (constructorSourceDelegate c w feed) evm'))
    (hc : callViaEVM evm' c.extensionDelegate 0 constructorFactoryPayload (true, evm'', out) false)
    (hhi : out.size < 2^255) (hv : ConstructorFactoryReturnValid out) :
    ExecBlock config (constructorSourceEntry c) evm (contract.ctor.body.take 36)
      (.ok (constructorSourceFactory c w feed (calldataWord out 0)) evm'') := by
  change ExecBlock config _ _ (contract.ctor.body.take 35 ++
    [.externalCall (.var "delegate") "assetListFactory" (.intLit 0) [] "__c2" (perm := false)]) _
  apply execBlockAppendOk hp
  exact .consNormal (constructorFactory_source_ok constructorSourceDelegate_eval hc hhi hv) .nil

theorem constructorSourceFactory_revert {c : ConstructorConfig} {w feed : UInt256}
    {evm evm' evm'' : EVM.State} {z : Bool} {out : ByteArray}
    (hp : ExecBlock config (constructorSourceEntry c) evm (contract.ctor.body.take 35)
      (.ok (constructorSourceDelegate c w feed) evm'))
    (hc : callViaEVM evm' c.extensionDelegate 0 constructorFactoryPayload (z, evm'', out) false)
    (hhi : out.size < 2^255) (hv : ¬ (z = true ∧ ConstructorFactoryReturnValid out)) :
    ExecBlock config (constructorSourceEntry c) evm contract.ctor.body .reverted := by
  rw [← List.take_append_drop 35 contract.ctor.body]
  apply execBlockAppendOk hp
  exact .consRevert (constructorFactory_source_revert constructorSourceDelegate_eval hc hhi hv)

end Benchmarks.CompoundIII.Comet
