import Examples.Precompiles.Ripemd160.HashBridge
import Reasoning.ReachExact

/-!
# RIPEMD-160 recombination and return trace

The optimized runtime keeps the parallel line states in scratch memory.  This module rejoins
those states into the five chaining words and traces the final little-endian digest return.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Ripemd160

def runtimeRecombineChain (h : RuntimeChain) (left right : RuntimeLineState) : RuntimeChain :=
  { h0 := UInt256.land mask32Word (h.h1 + left.c + right.d)
    h1 := UInt256.land mask32Word (h.h2 + left.d + right.e)
    h2 := UInt256.land mask32Word (h.h3 + left.e + right.a)
    h3 := UInt256.land mask32Word (h.h4 + left.a + right.b)
    h4 := UInt256.land mask32Word (h.h0 + left.b + right.c) }

def runtimeCompressChain (X : Fin 16 → UInt256) (h : RuntimeChain) : RuntimeChain :=
  runtimeRecombineChain h
    (runtimePureLeftLine X 5 (runtimeLineOfChain h))
    (runtimePureRightLine X 5 (runtimeLineOfChain h))

structure RuntimeHashState where
  cursor : RuntimeMemCursor
  chain : RuntimeChain

def ripemd160RecombineGas : Nat := 251

def runtimeHashStep (I : ExecutionEnv) (block : Nat)
    (s : RuntimeHashState) : RuntimeHashState :=
  let blk := UInt256.ofNat block
  let X := runtimeParsedWords I blk s.cursor
  let parsed := hashParseCursor I blk s.cursor 16
  let leftCursor := runtimeLeftLineCursor
    (hashLeftInitCursor I s.chain parsed) (hashScratchPtr I) 5
  let finalCursor := runtimeRightLineCursor
    (hashRightInitCursor I s.chain leftCursor) (hashScratchPtr I) 5
  { cursor := finalCursor
    chain := runtimeCompressChain X s.chain }

/-- Exact gas of one complete compression-block iteration from one outer-loop header to the next. -/
def ripemd160CompressBlockGas (I : ExecutionEnv) (block : Nat)
    (s : RuntimeHashState) : Nat :=
  let blk := UInt256.ofNat block
  let parsed := hashParseCursor I blk s.cursor 16
  let leftInitial := hashLeftInitCursor I s.chain parsed
  let leftFinal := runtimeLeftLineCursor leftInitial (hashScratchPtr I) 5
  let rightInitial := hashRightInitCursor I s.chain leftFinal
  59
    + ripemd160ParseGas I blk s.cursor 16 0
    + ripemd160InitLineGas parsed (hashScratchPtr I + ⟨512⟩)
    + ripemd160LeftLineGas leftInitial (hashScratchPtr I) 5 0
    + ripemd160InitLineGas leftFinal (hashScratchPtr I + ⟨672⟩)
    + ripemd160RightLineGas rightInitial (hashScratchPtr I) 5 0
    + ripemd160RecombineGas

def runtimeHashRun (I : ExecutionEnv) : Nat → RuntimeHashState → RuntimeHashState
  | 0, s => s
  | block + 1, s => runtimeHashStep I block (runtimeHashRun I block s)

def runtimeSwap32 (x : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.lor
      (UInt256.land (UInt256.shiftRight x ⟨24⟩) ⟨0xff⟩)
      (UInt256.land (UInt256.shiftRight x ⟨8⟩) ⟨0xff00⟩))
    (UInt256.lor
      (UInt256.land (UInt256.shiftLeft x ⟨8⟩) ⟨0xff0000⟩)
      (UInt256.land (UInt256.shiftLeft x ⟨24⟩) ⟨0xff000000⟩))

def runtimeDigestPacked (h : RuntimeChain) : UInt256 :=
  UInt256.lor
    (UInt256.shiftLeft (runtimeSwap32 h.h0) ⟨128⟩)
    (UInt256.lor
      (UInt256.shiftLeft (runtimeSwap32 h.h1) ⟨96⟩)
      (UInt256.lor
        (UInt256.shiftLeft (runtimeSwap32 h.h2) ⟨64⟩)
        (UInt256.lor
          (UInt256.shiftLeft (runtimeSwap32 h.h3) ⟨32⟩)
          (runtimeSwap32 h.h4))))

def runtimeDigestValue (h : RuntimeChain) : UInt256 :=
  UInt256.shiftRight (UInt256.shiftLeft (runtimeDigestPacked h) ⟨96⟩) ⟨96⟩

theorem ripemd160X_recombineGas {cA σ I} {g : Sat256} {s0 : State}
    {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    {h : RuntimeChain} {left right : RuntimeLineState} {blk : UInt256}
    {X : Fin 16 → UInt256}
    (hinv : RuntimeRightInvariant c (hashScratchPtr I) X left right)
    (hbase : (hashScratchPtr I).toNat + 863 < 2 ^ 64)
    (rd1406 : RDx ripemd160RuntimeBytecode I g s0 ⟨1406⟩
      [h.h1, hashPadPtr I, calldataSizeWord I + ⟨72⟩,
        hashScratchPtr I, blk, h.h2, h.h0, h.h4, h.h3, ⟨122⟩]
      c.mem c.aw rdata (cA, σ) k C) :
    ∃ k', RDx ripemd160RuntimeBytecode I g s0 ⟨1028⟩
      (hashBlockLoopStack I (blk + ⟨1⟩) (runtimeRecombineChain h left right))
      c.mem c.aw rdata (cA, σ) k' (C + ripemd160RecombineGas) := by
  rcases hinv with ⟨hc, _, hleft, hright, hcover⟩
  have addrNat (n : UInt256) (hn : n.toNat ≤ 832) :
      (hashScratchPtr I + n).toNat = (hashScratchPtr I).toNat + n.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt]
    rw [show UInt256.size = 2 ^ 256 from by decide]
    omega
  have awEq (n : UInt256) (hn : n.toNat ≤ 800) :
      runtimeMloadAw c.aw (hashScratchPtr I + n) = c.aw :=
    runtimeMloadAw_eq_of_covers hc.1 (by rw [addrNat n (by omega)]; omega)
      (by rw [addrNat n (by omega)]; omega)
  have costEq (n : UInt256) (hn : n.toNat ≤ 800) :
      runtimeMloadCost c.aw (hashScratchPtr I + n) = 0 := by
    simp only [runtimeMloadCost, awEq n hn, Nat.sub_self]
  have lv512 : runtimeMloadValue c.mem c.aw (hashScratchPtr I + ⟨512⟩) = left.a :=
    hleft.1.load
  have lv544 : runtimeMloadValue c.mem c.aw (hashScratchPtr I + ⟨544⟩) = left.b := by
    rw [← show (⟨512⟩ : UInt256) + ⟨32⟩ = ⟨544⟩ by native_decide,
      ← u256_add_assoc]
    exact hleft.2.1.load
  have lv576 : runtimeMloadValue c.mem c.aw (hashScratchPtr I + ⟨576⟩) = left.c := by
    rw [← show (⟨512⟩ : UInt256) + ⟨64⟩ = ⟨576⟩ by native_decide,
      ← u256_add_assoc]
    exact hleft.2.2.1.load
  have lv608 : runtimeMloadValue c.mem c.aw (hashScratchPtr I + ⟨608⟩) = left.d := by
    rw [← show (⟨512⟩ : UInt256) + ⟨96⟩ = ⟨608⟩ by native_decide,
      ← u256_add_assoc]
    exact hleft.2.2.2.1.load
  have lv640 : runtimeMloadValue c.mem c.aw (hashScratchPtr I + ⟨640⟩) = left.e := by
    rw [← show (⟨512⟩ : UInt256) + ⟨128⟩ = ⟨640⟩ by native_decide,
      ← u256_add_assoc]
    exact hleft.2.2.2.2.load
  have rv672 : runtimeMloadValue c.mem c.aw (hashScratchPtr I + ⟨672⟩) = right.a :=
    hright.1.load
  have rv704 : runtimeMloadValue c.mem c.aw (hashScratchPtr I + ⟨704⟩) = right.b := by
    rw [← show (⟨672⟩ : UInt256) + ⟨32⟩ = ⟨704⟩ by native_decide,
      ← u256_add_assoc]
    exact hright.2.1.load
  have rv736 : runtimeMloadValue c.mem c.aw (hashScratchPtr I + ⟨736⟩) = right.c := by
    rw [← show (⟨672⟩ : UInt256) + ⟨64⟩ = ⟨736⟩ by native_decide,
      ← u256_add_assoc]
    exact hright.2.2.1.load
  have rv768 : runtimeMloadValue c.mem c.aw (hashScratchPtr I + ⟨768⟩) = right.d := by
    rw [← show (⟨672⟩ : UInt256) + ⟨96⟩ = ⟨768⟩ by native_decide,
      ← u256_add_assoc]
    exact hright.2.2.2.1.load
  have rv800 : runtimeMloadValue c.mem c.aw (hashScratchPtr I + ⟨800⟩) = right.e := by
    rw [← show (⟨672⟩ : UInt256) + ⟨128⟩ = ⟨800⟩ by native_decide,
      ← u256_add_assoc]
    exact hright.2.2.2.2.load
  have rd1p := evm_run rd1406 with [push2 ⟨512⟩, dup5, add]
  have rd1 := RDx.runtimeMload rd1p (by native_decide) (by simp)
  rw [awEq ⟨512⟩ (by decide), lv512] at rd1
  have rd2p := evm_run rd1 with [swap1, push2 ⟨544⟩, dup6, add]
  have rd2 := RDx.runtimeMload rd2p (by native_decide) (by simp)
  rw [awEq ⟨544⟩ (by decide), lv544] at rd2
  have rd3p := evm_run rd2 with [swap1, push2 ⟨576⟩, dup7, add]
  have rd3 := RDx.runtimeMload rd3p (by native_decide) (by simp)
  rw [awEq ⟨576⟩ (by decide), lv576] at rd3
  have rd4p := evm_run rd3 with [swap3, push2 ⟨608⟩, dup8, add]
  have rd4 := RDx.runtimeMload rd4p (by native_decide) (by simp)
  rw [awEq ⟨608⟩ (by decide), lv608] at rd4
  have rd5p := evm_run rd4 with [swap2, push2 ⟨640⟩, dup9, add]
  have rd5 := RDx.runtimeMload rd5p (by native_decide) (by simp)
  rw [awEq ⟨640⟩ (by decide), lv640] at rd5
  have rd6p := evm_run rd5 with [push2 ⟨672⟩, dup10, add]
  have rd6 := RDx.runtimeMload rd6p (by native_decide) (by simp)
  rw [awEq ⟨672⟩ (by decide), rv672] at rd6
  have rd7p := evm_run rd6 with [swap2, push2 ⟨704⟩, dup11, add]
  have rd7 := RDx.runtimeMload rd7p (by native_decide) (by simp)
  rw [awEq ⟨704⟩ (by decide), rv704] at rd7
  have rd8p := evm_run rd7 with [swap5, push2 ⟨736⟩, dup12, add]
  have rd8 := RDx.runtimeMload rd8p (by native_decide) (by simp)
  rw [awEq ⟨736⟩ (by decide), rv736] at rd8
  have rd9p := evm_run rd8 with [swap8, push2 ⟨768⟩, dup13, add]
  have rd9 := RDx.runtimeMload rd9p (by native_decide) (by simp)
  rw [awEq ⟨768⟩ (by decide), rv768] at rd9
  have rd10p := evm_run rd9 with [swap1, push2 ⟨800⟩, dup14, add]
  have rd10 := RDx.runtimeMload rd10p (by native_decide) (by simp)
  rw [awEq ⟨800⟩ (by decide), rv800] at rd10
  have rd1028 := evm_run rd10 with [
    swap4, add, add, push4 ⟨4294967295⟩, and, swap13,
    add, add, push4 ⟨4294967295⟩, and, swap14,
    add, add, push4 ⟨4294967295⟩, and, swap11,
    add, add, push4 ⟨4294967295⟩, and, swap8,
    add, add, push4 ⟨4294967295⟩, and, swap5,
    swap4, push1 ⟨1⟩, add, swap3, swap2, swap1,
    push2 ⟨1028⟩, jump (by jump_dest) ]
  rw [costEq ⟨512⟩ (by decide), costEq ⟨544⟩ (by decide),
    costEq ⟨576⟩ (by decide), costEq ⟨608⟩ (by decide),
    costEq ⟨640⟩ (by decide), costEq ⟨672⟩ (by decide),
    costEq ⟨704⟩ (by decide), costEq ⟨736⟩ (by decide),
    costEq ⟨768⟩ (by decide), costEq ⟨800⟩ (by decide)] at rd1028
  have rdExact := RDx.withIndices rd1028
    (C' := C + ripemd160RecombineGas) (by rfl) (by
      norm_num [ripemd160RecombineGas])
  exact ⟨_, by
    simpa [hashBlockLoopStack, runtimeRecombineChain, mask32Word,
      u256_add_comm, u256_add_assoc] using rdExact⟩

theorem ripemd160X_recombine {cA σ I} {g : Sat256} {s0 : State}
    {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}
    {h : RuntimeChain} {left right : RuntimeLineState} {blk : UInt256}
    {X : Fin 16 → UInt256}
    (hinv : RuntimeRightInvariant c (hashScratchPtr I) X left right)
    (hbase : (hashScratchPtr I).toNat + 863 < 2 ^ 64)
    (rd1406 : RDx ripemd160RuntimeBytecode I g s0 ⟨1406⟩
      [h.h1, hashPadPtr I, calldataSizeWord I + ⟨72⟩,
        hashScratchPtr I, blk, h.h2, h.h0, h.h4, h.h3, ⟨122⟩]
      c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RDx ripemd160RuntimeBytecode I g s0 ⟨1028⟩
      (hashBlockLoopStack I (blk + ⟨1⟩) (runtimeRecombineChain h left right))
      c.mem c.aw rdata (cA, σ) k' C' := by
  obtain ⟨k', h'⟩ := ripemd160X_recombineGas hinv hbase rd1406
  exact ⟨k', _, h'⟩

/-- Execute one complete 64-byte compression block, retaining the final scratch invariant. -/
theorem ripemd160X_compressBlock {cA gh bl σ σ₀ A I} {g : Sat256}
    {blk : UInt256} {h : RuntimeChain} {initial : RuntimeMemCursor} {k C : Nat}
    (hblk : UInt256.lt blk (hashBlockCountWord I) = ⟨1⟩)
    (hc : RuntimeCursorSmall initial)
    (hbase : (hashScratchPtr I).toNat + 863 < 2 ^ 64)
    (hread : ∀ i, i < 16 →
      (hashParseAddress I blk (UInt256.ofNat i)).toNat + 66 < 2 ^ 64)
    (rd1028 : RDx ripemd160RuntimeBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1028⟩
      (hashBlockLoopStack I blk h) initial.mem initial.aw
      ByteArray.empty (cA, σ) k C) :
    let parsed := hashParseCursor I blk initial 16
    let X := runtimeParsedWords I blk initial
    let left := runtimePureLeftLine X 5 (runtimeLineOfChain h)
    let leftCursor := runtimeLeftLineCursor (hashLeftInitCursor I h parsed)
      (hashScratchPtr I) 5
    let right := runtimePureRightLine X 5 (runtimeLineOfChain h)
    let finalCursor := runtimeRightLineCursor (hashRightInitCursor I h leftCursor)
      (hashScratchPtr I) 5
    ∃ k' C',
      RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1028⟩
        (hashBlockLoopStack I (blk + ⟨1⟩) (runtimeCompressChain X h))
        finalCursor.mem finalCursor.aw ByteArray.empty (cA, σ) k' C' ∧
      RuntimeRightInvariant finalCursor (hashScratchPtr I) X left right := by
  dsimp only
  obtain ⟨_, _, rd1304⟩ := ripemd160X_enterParseLoop hblk rd1028
  obtain ⟨_, _, rd1314⟩ := ripemd160X_parseBlock rd1304
  have hmessage := hashParseCursor_message hc (by omega) hread
  obtain ⟨_, _, rd1350⟩ := ripemd160X_reachLeftGroups rd1314
  have hleft0 : RuntimeLeftInvariant
      (hashLeftInitCursor I h (hashParseCursor I blk initial 16))
      (hashScratchPtr I) (runtimeParsedWords I blk initial) (runtimeLineOfChain h) := by
    rw [hashLeftInitCursor_eq]
    exact hmessage.2.initLeft hmessage.1 hbase
  obtain ⟨_, _, rd1360⟩ := ripemd160X_leftLine (by
    simpa [hashLeftGroupStack] using rd1350)
  have hleft := runtimeLeftLineCursor_invariant (groups := 5) hleft0 hbase
  obtain ⟨_, _, rd1396⟩ := ripemd160X_reachRightGroups rd1360
  have hright0 : RuntimeRightInvariant
      (hashRightInitCursor I h
        (runtimeLeftLineCursor
          (hashLeftInitCursor I h (hashParseCursor I blk initial 16))
          (hashScratchPtr I) 5))
      (hashScratchPtr I) (runtimeParsedWords I blk initial)
      (runtimePureLeftLine (runtimeParsedWords I blk initial) 5 (runtimeLineOfChain h))
      (runtimeLineOfChain h) := by
    rw [hashRightInitCursor_eq]
    exact hleft.initRight hbase
  obtain ⟨_, _, rd1406⟩ := ripemd160X_rightLine (by
    simpa [hashRightGroupStack] using rd1396)
  have hright := runtimeRightLineCursor_invariant (groups := 5) hright0 hbase
  obtain ⟨k', C', rdNext⟩ := ripemd160X_recombine hright hbase rd1406
  exact ⟨k', C', by simpa [runtimeCompressChain] using rdNext, hright⟩

/-- Iterate the complete compression trace over a natural-number prefix of the block loop. -/
theorem ripemd160X_blocks {cA gh bl σ σ₀ A I} {g : Sat256}
    {initial : RuntimeHashState} {blocks k C : Nat}
    (hblocks : blocks ≤ (hashBlockCountWord I).toNat)
    (hc : RuntimeCursorSmall initial.cursor)
    (hbase : (hashScratchPtr I).toNat + 863 < 2 ^ 64)
    (hread : ∀ block, block < blocks → ∀ i, i < 16 →
      (hashParseAddress I (UInt256.ofNat block) (UInt256.ofNat i)).toNat + 66 < 2 ^ 64)
    (rd1028 : RDx ripemd160RuntimeBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1028⟩
      (hashBlockLoopStack I ⟨0⟩ initial.chain)
      initial.cursor.mem initial.cursor.aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RDx ripemd160RuntimeBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1028⟩
      (hashBlockLoopStack I (UInt256.ofNat blocks) (runtimeHashRun I blocks initial).chain)
      (runtimeHashRun I blocks initial).cursor.mem
      (runtimeHashRun I blocks initial).cursor.aw ByteArray.empty (cA, σ) k' C' ∧
      RuntimeCursorSmall (runtimeHashRun I blocks initial).cursor := by
  induction blocks with
  | zero =>
      exact ⟨k, C, by simpa [runtimeHashRun] using rd1028,
        by simpa [runtimeHashRun] using hc⟩
  | succ block ih =>
      have hprev : block ≤ (hashBlockCountWord I).toNat := by omega
      obtain ⟨kprev, Cprev, rdprev, hcprev⟩ :=
        ih hprev (fun b hb i hi => hread b (by omega) i hi)
      have hblockLt : block < (hashBlockCountWord I).toNat := by omega
      have hblockWord :
          UInt256.lt (UInt256.ofNat block) (hashBlockCountWord I) = ⟨1⟩ := by
        apply ult_one
        rw [ulit_toNat' block (lt_of_lt_of_le hblockLt
          (hashBlockCountWord I).val.isLt.le)]
        exact hblockLt
      obtain ⟨knext, Cnext, rdnext, hinv⟩ :=
        ripemd160X_compressBlock hblockWord hcprev hbase
          (hread block (by omega)) rdprev
      have hnext : UInt256.ofNat block + ⟨1⟩ = UInt256.ofNat (block + 1) := by
        rw [u256_add_comm, u256_one_add_ofNat]
      refine ⟨knext, Cnext, ?_, ?_⟩
      · simpa [runtimeHashRun, runtimeHashStep, hnext] using rdnext
      · simpa [runtimeHashRun, runtimeHashStep] using hinv.small

def ripemd160FinishGas (aw : UInt256) : Nat :=
  569 + runtimeMstoreCost aw ⟨0⟩

/-- Leave the block loop, serialize the five little-endian words, and return one raw word while
    retaining the exact cumulative gas index. -/
theorem ripemd160X_finishGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {blk : UInt256} {h : RuntimeChain} {mem : ByteArray} {aw : UInt256} {k C : Nat}
    (hdone : UInt256.lt blk (hashBlockCountWord I) = ⟨0⟩)
    (rd1028 : RDx ripemd160RuntimeBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1028⟩
      (hashBlockLoopStack I blk h) mem aw ByteArray.empty (cA, σ) k C) :
    RDxRet ripemd160RuntimeBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ) (runtimeDigestValue h).toByteArray (C + ripemd160FinishGas aw) := by
  have rd1028' : RDx ripemd160RuntimeBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1028⟩
      [hashPadPtr I, calldataSizeWord I + ⟨72⟩, hashScratchPtr I, blk,
        h.h0, h.h4, h.h3, h.h2, h.h1, ⟨122⟩]
      mem aw ByteArray.empty (cA, σ) k C := by
    simpa [hashBlockLoopStack] using rd1028
  have rd1059 := evm_run rd1028' with [
    jumpdest, dup2, push1 ⟨6⟩, shr, dup5, lt, push2 ⟨1293⟩,
    jumpiNT (by simpa [hashBlockCountWord] using hdone), pop, pop, pop, pop,
    push2 ⟨1225⟩, push2 ⟨1183⟩, push2 ⟨1141⟩, push2 ⟨1099⟩,
    push2 ⟨1267⟩, swap5 ]
  have rd1099 := evm_run rd1059 with [
    push1 ⟨0xff⟩, dup2, push1 ⟨24⟩, shr, and,
    push2 ⟨0xff00⟩, dup3, push1 ⟨8⟩, shr, and, or, swap1,
    push4 ⟨0xff000000⟩, push3 ⟨0xff0000⟩, dup3, push1 ⟨8⟩, shl, and,
    swap2, push1 ⟨24⟩, shl, and, or, or, swap1, jump (by jump_dest) ]
  have rd1141 := evm_run rd1099 with [
    jumpdest, swap8,
    push1 ⟨0xff⟩, dup2, push1 ⟨24⟩, shr, and,
    push2 ⟨0xff00⟩, dup3, push1 ⟨8⟩, shr, and, or, swap1,
    push4 ⟨0xff000000⟩, push3 ⟨0xff0000⟩, dup3, push1 ⟨8⟩, shl, and,
    swap2, push1 ⟨24⟩, shl, and, or, or, swap1, jump (by jump_dest) ]
  have rd1183 := evm_run rd1141 with [
    jumpdest, swap6,
    push1 ⟨0xff⟩, dup2, push1 ⟨24⟩, shr, and,
    push2 ⟨0xff00⟩, dup3, push1 ⟨8⟩, shr, and, or, swap1,
    push4 ⟨0xff000000⟩, push3 ⟨0xff0000⟩, dup3, push1 ⟨8⟩, shl, and,
    swap2, push1 ⟨24⟩, shl, and, or, or, swap1, jump (by jump_dest) ]
  have rd1225 := evm_run rd1183 with [
    jumpdest, swap4,
    push1 ⟨0xff⟩, dup2, push1 ⟨24⟩, shr, and,
    push2 ⟨0xff00⟩, dup3, push1 ⟨8⟩, shr, and, or, swap1,
    push4 ⟨0xff000000⟩, push3 ⟨0xff0000⟩, dup3, push1 ⟨8⟩, shl, and,
    swap2, push1 ⟨24⟩, shl, and, or, or, swap1, jump (by jump_dest) ]
  have rd1267 := evm_run rd1225 with [
    jumpdest, swap2,
    push1 ⟨0xff⟩, dup2, push1 ⟨24⟩, shr, and,
    push2 ⟨0xff00⟩, dup3, push1 ⟨8⟩, shr, and, or, swap1,
    push4 ⟨0xff000000⟩, push3 ⟨0xff0000⟩, dup3, push1 ⟨8⟩, shl, and,
    swap2, push1 ⟨24⟩, shl, and, or, or, swap1, jump (by jump_dest) ]
  have rd122 := evm_run rd1267 with [
    jumpdest, swap1, push1 ⟨32⟩, shl, or,
    swap1, push1 ⟨64⟩, shl, or,
    swap1, push1 ⟨96⟩, shl, or,
    swap1, push1 ⟨128⟩, shl, or,
    push1 ⟨96⟩, shl, swap1, jump (by jump_dest) ]
  have rd127p := evm_run rd122 with [jumpdest, push1 ⟨96⟩, shr, push0]
  have rd128 := RDx.runtimeMstore rd127p (by native_decide) (by simp)
  have rd131 := evm_run rd128 with [push1 ⟨32⟩, push0]
  have rdExact := RDx.withIndices rd131 (C' := C + ripemd160FinishGas aw)
    (by rfl) (by simp only [ripemd160FinishGas]; omega)
  simpa only [Nat.add_zero] using rdExact.ret 0 (runtimeDigestValue h).toByteArray
    (by native_decide) (by
      intro s haw hstk
      have hmax : max aw.toNat 1 < UInt256.size := by
        exact max_lt aw.val.isLt (by native_decide)
      have hto : (UInt256.ofNat (max aw.toNat 1)).toNat = max aw.toNat 1 :=
        ulit_toNat' _ hmax
      norm_num [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        runtimeMstoreAw, MachineState.M, hto]
      change Cₘ (UInt256.ofNat (max aw.toNat 1)) -
        Cₘ (UInt256.ofNat (max aw.toNat 1)) = 0
      exact Nat.sub_self _)
    (by
      simpa [runtimeMstoreMem, runtimeDigestValue, runtimeDigestPacked, runtimeSwap32,
        u256_lor_comm, u256_lor_assoc] using
        toByteArray_write_read_back_of_gap (runtimeDigestValue h) mem 0 (by simp))
    (by simp)
/-- Functional projection of `ripemd160X_finishGas` for callers that do not inspect gas. -/
theorem ripemd160X_finish {cA gh bl σ σ₀ A I} {g : Sat256}
    {blk : UInt256} {h : RuntimeChain} {mem : ByteArray} {aw : UInt256} {k C : Nat}
    (hdone : UInt256.lt blk (hashBlockCountWord I) = ⟨0⟩)
    (rd1028 : RDx ripemd160RuntimeBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1028⟩
      (hashBlockLoopStack I blk h) mem aw ByteArray.empty (cA, σ) k C) :
    RDret ripemd160RuntimeBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ) (runtimeDigestValue h).toByteArray := by
  exact (ripemd160X_finishGas hdone rd1028).toRDret

end Ripemd160
