import Benchmarks.CompoundIII.Comet.TokenBalanceTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def decimalsPayload : ByteArray := ByteArray.mk #[49, 60, 229, 103]

theorem decimalsPayload_encode : config.externalABI.encode? "decimals" [] =
    some decimalsPayload := by
  change encodeCallWithSelector? (selectorBytes 49 60 229 103) [] [] = _
  simp only [encodeCallWithSelector?, encodeABIValues?, abiTupleHeadSize?,
    encodeABIValuesFrom?, bind, Option.bind]
  decide +kernel

def DecimalsReturnValid (out : ByteArray) : Prop :=
  32 ≤ out.size ∧ (calldataWord out 0).toNat < 2^8

instance (out : ByteArray) : Decidable (DecimalsReturnValid out) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem decimals_decode {out : ByteArray} (hhi : out.size < 2^255) :
    config.externalABI.decode? "decimals" out =
      if DecimalsReturnValid out then some [.int (Int.ofNat (calldataWord out 0).toNat)]
      else none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  change (decodeReturnValue? (.elem (.int (.uint ⟨8, by decide⟩))) out).map (fun v ↦ [v]) = _
  unfold decodeReturnValue?
  rw [decodeReturnValues_scalarWords_eq (by decide),
    if_neg (by simp only [List.isEmpty_cons, hlen]; omega)]
  by_cases hlo : 32 ≤ out.size
  · have ht : ((out.toList.drop 0).take 32).length = 32 := by
      simp only [List.drop_zero, List.length_take, hlen]; omega
    simp only [decodeScalarWords?, decodeScalarWord_uint_result ⟨8, by decide⟩ ht,
      decode_word_at_eq_any out 0 (by omega)]
    by_cases hc : (calldataWord out 0).toNat < 2^8 <;>
      simp only [DecimalsReturnValid, hlo, true_and, EVM.twoPow, hc, if_true, if_false,
        bind, Option.bind, Option.map]
  · have ht : ¬ ((out.toList.drop 0).take 32).length = 32 := by
      simp only [List.drop_zero, List.length_take, hlen]; omega
    simp only [decodeScalarWords?, decodeScalarWord?, readWord?, readBytes?, if_neg ht,
      bind, Option.bind, Option.map, DecimalsReturnValid, hlo, false_and, if_false]

theorem decimals_typed {evm evm' : EVM.State} {asset : AccountAddress}
    {z : Bool} {out : ByteArray}
    (hc : callViaEVM evm asset 0 decimalsPayload (z, evm', out) false) :
    typedCallViaEVM config evm asset "decimals" 0 [] (z, evm', out) false :=
  ⟨_, decimalsPayload_encode, hc⟩

theorem decimals_source_ok {frame : Frame} {evm evm' : EVM.State}
    {asset : AccountAddress} {expr : Expr} {ret : Ident} {out : ByteArray}
    (he : evalExpr? config frame evm expr = .ok (.address asset))
    (hc : callViaEVM evm asset 0 decimalsPayload (true, evm', out) false)
    (hhi : out.size < 2^255) (hv : DecimalsReturnValid out) :
    ExecStmt config frame evm (.externalCall expr "decimals" (.intLit 0) [] ret (perm := false))
      (.ok { frame with locals :=
        frame.locals.insert ret (.int (Int.ofNat (calldataWord out 0).toNat)) } evm') := by
  rw [← addressOfAddress asset] at hc
  exact ExecStmt.externalCallSuccess (eth := .intLit 0) (args := []) he
    (by simp only [evalExpr?, pure]) (by rfl) (decimals_typed hc)
    (by rw [decimals_decode hhi, if_pos hv])

theorem decimals_source_revert {frame : Frame} {evm evm' : EVM.State}
    {asset : AccountAddress} {expr : Expr} {ret : Ident} {z : Bool} {out : ByteArray}
    (he : evalExpr? config frame evm expr = .ok (.address asset))
    (hc : callViaEVM evm asset 0 decimalsPayload (z, evm', out) false)
    (hhi : out.size < 2^255) (hv : ¬ (z = true ∧ DecimalsReturnValid out)) :
    ExecStmt config frame evm (.externalCall expr "decimals" (.intLit 0) [] ret (perm := false))
      .reverted := by
  rw [← addressOfAddress asset] at hc
  cases z with
  | false =>
    exact ExecStmt.externalCallFailure he
      (by simp only [evalExpr?, pure]) (by rfl) (decimals_typed hc)
  | true =>
    exact ExecStmt.externalCallReturnDecodeRevert he
      (by simp only [evalExpr?, pure]) (by rfl) (decimals_typed hc)
      (by rw [decimals_decode hhi, if_neg (fun h ↦ hv ⟨rfl, h⟩)])

inductive DecimalsTrace (asset : AccountAddress) (evm : EVM.State) :
    Option (EVM.State × UInt256) → Prop where
  | response {evm' : EVM.State} {z : Bool} {out : ByteArray}
      (hc : callViaEVM evm asset 0 decimalsPayload (z, evm', out) false)
      (hh : out.size < 2^255) :
      DecimalsTrace asset evm
        (if z = true ∧ DecimalsReturnValid out then some (evm', calldataWord out 0) else none)

theorem decimalsTrace_source {asset : AccountAddress} {evm : EVM.State}
    {result : Option (EVM.State × UInt256)} (ht : DecimalsTrace asset evm result)
    (frame : Frame) (expr : Expr) (ret : Ident)
    (he : evalExpr? config frame evm expr = .ok (.address asset)) :
    ExecStmt config frame evm (.externalCall expr "decimals" (.intLit 0) [] ret (perm := false))
      (wordCallResult frame ret result) := by
  cases ht with
  | @response evm' z out hc hh =>
    by_cases hv : z = true ∧ DecimalsReturnValid out
    · rw [if_pos hv]
      rcases hv with ⟨rfl, hv⟩
      exact decimals_source_ok he hc hh hv
    · rw [if_neg hv]
      exact decimals_source_revert he hc hh hv

end Benchmarks.CompoundIII.Comet
