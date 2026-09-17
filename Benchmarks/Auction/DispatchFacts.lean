import Benchmarks.Auction.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option synthInstance.maxSize 1024

namespace Auction

def entryGroup (i : Entry) : Fin 4 := ⟨i.val / 5, by omega⟩

def groupFirstPc (group : Fin 4) : UInt256 :=
  match group.val with
  | 0 => ⟨228⟩
  | 1 => ⟨169⟩
  | 2 => ⟨99⟩
  | _ => ⟨40⟩

def selectedGroup (word : UInt256) : Fin 4 :=
  if UInt256.gt (armSelNat auctionBytecode ⟨18⟩) word = ⟨0⟩ then
    if UInt256.gt (armSelNat auctionBytecode ⟨29⟩) word = ⟨0⟩ then 3 else 2
  else
    if UInt256.gt (armSelNat auctionBytecode ⟨158⟩) word = ⟨0⟩ then 1 else 0

def groupEndPc (group : Fin 4) : UInt256 :=
  match group.val with
  | 0 => ⟨283⟩
  | 1 => ⟨224⟩
  | 2 => ⟨154⟩
  | _ => ⟨95⟩

theorem groupEnd : ∀ group : Fin 4,
    nthArmPc auctionBytecode (groupFirstPc group) 5 = groupEndPc group := by
  native_decide

theorem selectedGroup_entry : ∀ i : Entry, selectedGroup (entryWord i) = entryGroup i := by
  native_decide

theorem groupArmsWellFormed :
    ∀ (group : Fin 4) (j : Fin 5),
      armWellFormed auctionBytecode (nthArmPc auctionBytecode (groupFirstPc group) j.val) := by
  unfold armWellFormed
  native_decide

theorem entryArmsMiss :
    ∀ (i : Entry) (j : Fin 5), j.val < i.val % 5 →
      UInt256.eq
        (armSelNat auctionBytecode
          (nthArmPc auctionBytecode (groupFirstPc (entryGroup i)) j.val))
        (entryWord i) = ⟨0⟩ := by
  native_decide

theorem entryArmHit :
    ∀ i : Entry,
      UInt256.eq
        (armSelNat auctionBytecode
          (nthArmPc auctionBytecode (groupFirstPc (entryGroup i)) (i.val % 5)))
        (entryWord i) ≠ ⟨0⟩ := by
  native_decide

theorem entryArmTarget :
    ∀ i : Entry,
      armTgt auctionBytecode
        (nthArmPc auctionBytecode (groupFirstPc (entryGroup i)) (i.val % 5)) = entryPc i := by
  native_decide

theorem entryJumpdest :
    ∀ i : Entry, (D_J auctionBytecode 0).contains (entryPc i) = true := by
  native_decide

def groupEntry (group : Fin 4) (j : Fin 5) : Entry := ⟨group.val * 5 + j.val, by omega⟩

theorem groupArmWord :
    ∀ (group : Fin 4) (j : Fin 5),
      armSelNat auctionBytecode (nthArmPc auctionBytecode (groupFirstPc group) j.val) =
        entryWord (groupEntry group j) := by
  native_decide

theorem groupArmEq {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size)
    (group : Fin 4) (j : Fin 5) :
    UInt256.eq
        (armSelNat auctionBytecode (nthArmPc auctionBytecode (groupFirstPc group) j.val))
        (solcSelectorWord I) =
      if (entryBytes (groupEntry group j) == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  rw [groupArmWord]
  rcases group with ⟨group, hg⟩
  rcases j with ⟨j, hj⟩
  interval_cases group <;> interval_cases j <;>
    exact evmSelectorDecode hsz _ _ _ _ _
      (by simp only [entryWord, groupEntry]; decide)

theorem groupNextPc :
    ∀ (group : Fin 4) (j : Fin 5),
      selArmNextPc (nthArmPc auctionBytecode (groupFirstPc group) j.val)
        (armTgtWidth auctionBytecode (nthArmPc auctionBytecode (groupFirstPc group) j.val)) =
      nthArmPc auctionBytecode (groupFirstPc group) (j.val + 1) := by
  native_decide

end Auction
