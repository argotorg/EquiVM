import Benchmarks.UniswapV3.Pool.Routines
import Reasoning.HeapMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables

namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: Reasoning.SolmBody, return several evaluated expressions.
theorem ABlock.returnsMany {cfg evm solm₀ stmts₀ solm rest} {exprs values}
    (prev : ABlock cfg evm solm₀ stmts₀ solm (.return exprs :: rest))
    (heval : evalExprs? cfg solm evm exprs = .ok values) :
    ExecBlock cfg solm₀ evm stmts₀ (.returned solm evm (some values)) :=
  prev.run (ExecBlock.consReturn (ExecStmt.return heval))

-- GENERALIZES Reasoning.ABI.encodeABIValue_uint256 to any unsigned ABI width.
theorem encodeABIValue_uint (width : ABI.BitWidth) (w : UInt256)
    (hlt : w.toNat < EVM.twoPow width.val) :
    encodeABIValue? (.elem (.int (.uint width))) (.int (Int.ofNat w.toNat)) =
      some (EVM.Word.toBytesBE w) := by
  have hword : EVM.word w.toNat = w := u256_ofNat_toNat w
  simp [encodeABIValue?, encodeABIWord?, hword, hlt, Nat.ne_of_gt width.property.1]

-- LIBRARY CANDIDATE: Reasoning.ABI, concatenate statically encoded return values.
theorem encodeStaticValuesFrom (items : List (ABIType × Value × EVM.Word))
    (headSize : Nat) (head tail : List UInt8)
    (hdyn : ∀ x ∈ items, isDynamicABIType x.1 = false)
    (henc : ∀ x ∈ items, encodeABIValue? x.1 x.2.1 = some (EVM.Word.toBytesBE x.2.2)) :
    encodeABIValuesFrom? (items.map (·.1)) (items.map (·.2.1)) headSize head tail =
      some (head ++ items.flatMap (fun x => EVM.Word.toBytesBE x.2.2) ++ tail) := by
  induction items generalizing head with
  | nil => simp only [List.map_nil, encodeABIValuesFrom?, List.flatMap_nil, List.append_nil]
  | cons x xs ih =>
    simp only [List.map_cons, encodeABIValuesFrom?, henc x (by simp), bind, Option.bind,
      hdyn x (by simp), Bool.false_eq_true, if_false]
    rw [ih _ (fun y hy => hdyn y (by simp [hy])) (fun y hy => henc y (by simp [hy]))]
    simp only [List.flatMap_cons, List.append_assoc]

-- LIBRARY CANDIDATE: Reasoning.ABI, return any tuple of statically encoded words.
theorem staticWordsReturnEncoding (items : List (ABIType × Value × EVM.Word))
    (headSize : Nat)
    (hhead : abiTupleHeadSize? (items.map (·.1)) = some headSize)
    (hdyn : ∀ x ∈ items, isDynamicABIType x.1 = false)
    (henc : ∀ x ∈ items, encodeABIValue? x.1 x.2.1 = some (EVM.Word.toBytesBE x.2.2)) :
    encodeReturnValues? (items.map (·.1)) (items.map (·.2.1)) =
      some (items.flatMap (fun x => EVM.Word.toBytesBE x.2.2)).toByteArray := by
  simp only [encodeReturnValues?, encodeABIValues?, hhead, bind, Option.bind,
    encodeStaticValuesFrom items headSize [] [] hdyn henc, List.nil_append, List.append_nil,
    mk_toArray_eq]

-- GENERALIZES Reasoning.ABIViews.uint256PairReturnEncoding to arbitrary unsigned widths.
theorem uintPairReturnEncoding (width0 width1 : ABI.BitWidth) (a b : UInt256)
    (ha : a.toNat < EVM.twoPow width0.val) (hb : b.toNat < EVM.twoPow width1.val) :
    encodeReturnValues? [.elem (.int (.uint width0)), .elem (.int (.uint width1))]
      [.int (Int.ofNat a.toNat), .int (Int.ofNat b.toNat)] = some (a.toByteArray ++ b.toByteArray) := by
  have h := staticWordsReturnEncoding
    [(.elem (.int (.uint width0)), .int (Int.ofNat a.toNat), a),
     (.elem (.int (.uint width1)), .int (Int.ofNat b.toNat), b)] 64
    (by simp only [List.map_cons, List.map_nil, abiTupleHeadSize?, staticABIEncodedSize?,
          isDynamicABIType, bind, Option.bind]
        cases width0; cases width1; rfl)
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> rfl)
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact encodeABIValue_uint width0 a ha
        · exact encodeABIValue_uint width1 b hb)
  simpa only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.toByteArray_append, word_toBytesBE_toByteArray_eq_toByteArray] using h

-- LIBRARY CANDIDATE: Reasoning.HeapMemory, tuple returns preserve the free pointer.
theorem returnMem_mload64 (ws : List UInt256) :
    memLoad (UInt256.ofNat 64) (returnMem ws) = ⟨128⟩ :=
  mloadWordValue_of_readWithPadding (by change 64 < _; rw [returnMem_size]; omega) (returnMem_read64 ws)

theorem RD.poolReturnUint128Pair {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : Nat} {v : UniswapV3PoolImmutables} {a b aw : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : AccountMap}
    (h : RD (deployedRuntime v) ee g s0 ⟨690⟩ (b :: a :: R)
      solcFreePtrMem aw rdata acc k C)
    (hov : R.length + 8 ≤ 1024) :
    RDret (deployedRuntime v) g s0 acc
      ((UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) a).toByteArray ++
        (UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) b).toByteArray) := by
  have hret := uniswapV3PoolBlocks.uniswapV3Pool_block_690
    (immWords := wordsOf (immStore v)) hov h
  have hload : memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ := solcFreePtrMem_mload64
  simp only [solcMask128, hload] at hret
  let a' := UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) a
  let b' := UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) b
  have hm : Reasoning.Theory.writeWord (solcReturnMem a') 160 b' = returnMem [a', b'] := by
    unfold Reasoning.Theory.writeWord
    rw [returnMem_single]
    exact returnMem_write [a'] b'
  change RDret (deployedRuntime v) g s0 acc
    ((Reasoning.Theory.writeWord (solcReturnMem a') 160 b').readWithPadding
      (memLoad (UInt256.ofNat 64) (Reasoning.Theory.writeWord (solcReturnMem a') 160 b')).toNat
      (UInt256.sub (UInt256.ofNat 192)
        (memLoad (UInt256.ofNat 64) (Reasoning.Theory.writeWord (solcReturnMem a') 160 b'))).toNat) at hret
  rw [hm, returnMem_mload64] at hret
  simp only [show (⟨128⟩ : UInt256).toNat = 128 from rfl,
    show (UInt256.sub (UInt256.ofNat 192) ⟨128⟩).toNat = 64 from by native_decide] at hret
  have hread : (returnMem [a', b']).readWithPadding 128 64 = wordBytes [a', b'] := by
    simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] using
      returnMem_read128 [a', b'] (by change 0 < 2; decide) (by change 64 < 2 ^ 64; decide)
  rw [hread] at hret
  simpa only [wordBytes, ByteArray.append_empty] using hret

-- LIBRARY CANDIDATE: Reasoning.ABI, encode a scalar boolean loaded from any word.
theorem encodeABIValue_boolWord (w : UInt256) :
    encodeABIValue? (.elem .bool) (wordToElem .bool w) =
      some (EVM.Word.toBytesBE (UInt256.isZero (UInt256.isZero w))) := by
  rw [wordToElemBool]
  by_cases hw : w = ⟨0⟩
  · subst w
    simp only [encodeABIValue?, encodeABIWord?, bind, Option.bind]
    rfl
  · rw [isZero_eq_zero_of_ne hw]
    simp only [hw, decide_false, Bool.not_false]
    simp only [encodeABIValue?, encodeABIWord?, bind, Option.bind]
    rfl

-- LIBRARY CANDIDATE: Reasoning.HeapMemory, expose a concrete tuple write offset to rewriting.
theorem returnMem_write_at (ws : List UInt256) (w : UInt256) (off : Nat)
    (hoff : off = 128 + 32 * ws.length) :
    w.toByteArray.write 0 (returnMem ws) off 32 = returnMem (ws ++ [w]) := by
  rw [hoff]
  exact returnMem_write ws w

-- LIBRARY CANDIDATE: prefix an already encoded ABI tuple with a selector.
theorem encodeCall_of_encodeReturn {types : List ABIType} {values : List Value}
    {payload : ByteArray} (selector : ByteArray)
    (h : encodeReturnValues? types values = some payload) :
    encodeCallWithSelector? selector types values = some (selector ++ payload) := by
  unfold encodeReturnValues? at h
  unfold encodeCallWithSelector?
  cases he : encodeABIValues? types values with
  | none => simp [he] at h
  | some bytes =>
      simp only [he, bind, Option.bind, Option.some.injEq] at h
      simp only [bind, Option.bind]
      simp only [← h, mk_toArray_eq]

end Benchmarks.UniswapV3.Pool
