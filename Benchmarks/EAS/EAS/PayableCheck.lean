import Benchmarks.EAS.EAS.PayableEVM

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- A successful ABI bool call followed by require(result).
def callBoolAccepted (heap : Nat) (success : Bool) (out : ByteArray) : Prop :=
  resolverCallValid heap success out ∧ calldataWord out 0 ≠ ⟨0⟩
instance (heap : Nat) (success : Bool) (out : ByteArray) : Decidable (callBoolAccepted heap success out) :=
  inferInstanceAs (Decidable (_ ∧ _))

def payableCheckBlock : Body := payableProbeBlock ++ [.require (.var "payableResult")]

theorem payableCheckSource {locals imms : Store} {evm evm' : EVM.State} {target : AccountAddress}
    {heap : Nat} {success : Bool} {out : ByteArray}
    (hr : locals.get? "resolver" = some (.address target))
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hc : callViaEVM fork evm target 0 payablePayload (success,evm',out) false) (hout : out.size < 2^255) :
    if callBoolAccepted heap success out then
      ExecBlock fork config {contract := contract, locals := locals, immutables := imms} evm payableCheckBlock
        (.ok {contract := contract, locals := payableProbeLocals locals out heap, immutables := imms} evm')
    else ExecBlock fork config {contract := contract, locals := locals, immutables := imms} evm payableCheckBlock .reverted := by
  have hp := payableProbeSource (imms := imms) hr hh hc hout
  have he : evalExpr? config {contract := contract, locals := payableProbeLocals locals out heap, immutables := imms}
      evm' (.var "payableResult") = .ok (.bool (decide (calldataWord out 0 ≠ ⟨0⟩))) := by
    simp only [evalExpr?, payableProbeLocals_result, EvalResult.ofOption]
  by_cases hv : resolverCallValid heap success out
  · rw [if_pos hv] at hp
    by_cases hn : calldataWord out 0 ≠ ⟨0⟩
    · rw [if_pos (show callBoolAccepted heap success out from ⟨hv,hn⟩)]
      exact execBlock_append hp (ExecBlock.consNormal (ExecStmt.requireTrue (by
        simpa only [decide_eq_true hn] using he)) ExecBlock.nil)
    · rw [if_neg (show ¬ callBoolAccepted heap success out from fun h => hn h.2)]
      exact execBlock_append hp (ExecBlock.consRevert (ExecStmt.requireFalse (by
        simpa only [decide_eq_false hn] using he)))
  · rw [if_neg hv] at hp
    rw [if_neg (show ¬ callBoolAccepted heap success out from fun h => hv h.1)]
    exact execBlock_append_term hp (by intros; exact nofun)

def payableGatePC : PayableSite → UInt256
  | .single => ⟨15772⟩ | .multiAttest => ⟨14728⟩ | .multiRevoke => ⟨15339⟩
def payableCheckedPC : PayableSite → UInt256
  | .single => ⟨15777⟩ | .multiAttest => ⟨14733⟩ | .multiRevoke => ⟨15344⟩

theorem payableGate {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap} {k C : Nat}
    {junk word a b c d e target : UInt256} {R : List UInt256} (v : EASImmutables) (site : PayableSite)
    (hstack : R.length+10 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 (payableDonePC site)
      (junk::word::payableSavedTail site a b c d e target R) mem aw out σ k C) :
    if word ≠ ⟨0⟩ then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (payableCheckedPC site)
        (payableSavedTail site a b c d e target R) mem aw' out σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  have hr : ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (payableGatePC site)
      (UInt256.isZero word::payableSavedTail site a b c d e target R) mem aw' out σ k' C' := by
    cases site with
    | single =>
      exact easBlocks.eas_block_16263_packed (immWords := wordsOf (immStore v))
        (by simp only [payableSavedTail, List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    | multiAttest =>
      exact easBlocks.eas_block_14897_packed (immWords := wordsOf (immStore v))
        (by simp only [payableSavedTail, List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    | multiRevoke =>
      exact easBlocks.eas_block_15512_packed (immWords := wordsOf (immStore v))
        (by simp only [payableSavedTail, List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨aw1,k1,C1,rd1⟩ := hr
  by_cases hn : word ≠ ⟨0⟩
  · rw [if_pos hn]
    have hz := isZero_eq_zero_of_ne hn
    cases site with
    | single =>
      exact easBlocks.eas_block_15772_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [payableSavedTail, List.length_cons]; omega) hz rd1
    | multiAttest =>
      exact easBlocks.eas_block_14728_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [payableSavedTail, List.length_cons]; omega) hz rd1
    | multiRevoke =>
      exact easBlocks.eas_block_15339_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [payableSavedTail, List.length_cons]; omega) hz rd1
  · rw [if_neg hn]
    have hw : word = ⟨0⟩ := not_ne_iff.mp hn
    have hz : UInt256.isZero word ≠ ⟨0⟩ := by rw [hw]; decide
    cases site with
    | single =>
      obtain ⟨aw2,k2,C2,rd2⟩ := easBlocks.eas_block_15772_taken_packed (immWords := wordsOf (immStore v))
        (by simp only [payableSavedTail, List.length_cons]; omega) hz (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
      exact easBlocks.eas_block_15407 (immWords := wordsOf (immStore v))
        (by simp only [easBlocks.eas_block_15772_taken_stack, payableSavedTail, List.length_cons]; omega) rd2
    | multiAttest =>
      obtain ⟨aw2,k2,C2,rd2⟩ := easBlocks.eas_block_14728_taken_packed (immWords := wordsOf (immStore v))
        (by simp only [payableSavedTail, List.length_cons]; omega) hz (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
      exact easBlocks.eas_block_14795 (immWords := wordsOf (immStore v)) (R := e::target::R)
        (by simp only [List.length_cons]; omega) rd2
    | multiRevoke =>
      obtain ⟨aw2,k2,C2,rd2⟩ := easBlocks.eas_block_15339_taken_packed (immWords := wordsOf (immStore v))
        (by simp only [payableSavedTail, List.length_cons]; omega) hz (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
      exact easBlocks.eas_block_15407 (immWords := wordsOf (immStore v))
        (by simp only [easBlocks.eas_block_15339_taken_stack, payableSavedTail, List.length_cons]; omega) rd2

theorem payableCheckEVM {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ptr junk a b c d e target : UInt256} {R : List UInt256} (v : EASImmutables) (site : PayableSite)
    (hstack : R.length+16 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hheap : ptr.toNat ≤ 2^64-1) (hlo : 96 ≤ ptr.toNat) (hh : memLoad (UInt256.ofNat 64) mem = ptr)
    (rd : RD fork (deployedRuntime v) ee g s0 (payableEntryPC site)
      (junk::payableSavedTail site a b c d e target R) mem aw rdata σ k C) :
    ∃ (evm' : EVM.State) (σ' : AccountMap) (success : Bool) (out : ByteArray),
      callViaEVM fork evm (AccountAddress.ofUInt256 target) 0 payablePayload (success,evm',out) false ∧
      SourceState s0 ee σ' evm' ∧ out.size < 2^138 ∧
      (if callBoolAccepted ptr.toNat success out then
        ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (payableCheckedPC site)
          (payableSavedTail site a b c d e target R) (payableOutputMemory mem ptr out) aw' out σ' k' C'
       else RDrev fork (deployedRuntime v) g s0) := by
  obtain ⟨evm',σ',success,out,hc,hs',hout,hr⟩ := payableEVM v site hstack hs hheap hlo hh rd
  refine ⟨evm',σ',success,out,hc,hs',hout,?_⟩
  by_cases hv : resolverCallValid ptr.toNat success out
  · rw [if_pos hv] at hr
    obtain ⟨aw1,k1,C1,rd1⟩ := hr
    have hg := payableGate v site (by omega) rd1
    by_cases hn : calldataWord out 0 ≠ ⟨0⟩
    · rw [if_pos (show callBoolAccepted ptr.toNat success out from ⟨hv,hn⟩)]
      simpa only [if_pos hn] using hg
    · rw [if_neg (show ¬ callBoolAccepted ptr.toNat success out from fun h => hn h.2)]
      simpa only [if_neg hn] using hg
  · rw [if_neg hv] at hr
    rw [if_neg (show ¬ callBoolAccepted ptr.toNat success out from fun h => hv h.1)]
    exact hr

end Benchmarks.EAS.EAS
