import Examples.Ripemd160Old.HashLeftRounds01
import Examples.Ripemd160Old.HashLeftRounds02
import Examples.Ripemd160Old.HashLeftRounds03
import Examples.Ripemd160Old.HashLeftRounds04
import Examples.Ripemd160Old.HashLeftRounds05
import Examples.Ripemd160Old.HashLeftRounds06
import Examples.Ripemd160Old.HashLeftRounds07
import Examples.Ripemd160Old.HashLeftRounds08
import Examples.Ripemd160Old.HashRightRounds01
import Examples.Ripemd160Old.HashRightRounds02
import Examples.Ripemd160Old.HashRightRounds03
import Examples.Ripemd160Old.HashRightRounds04
import Examples.Ripemd160Old.HashRightRounds05
import Examples.Ripemd160Old.HashRightRounds06
import Examples.Ripemd160Old.HashRightRounds07
import Examples.Ripemd160Old.HashRightRounds08
import Examples.Precompiles.Ripemd160.HashWideInvariant

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

namespace Ripemd160Old

open Ripemd160

private theorem runtime_leftRoundHelper_0_9 {cA σ I} {g : Sat256} {s0 : State}
    {round : Nat} {t : List UInt256} {c : RuntimeMemCursor}
    {rdata : ByteArray} {k C : Nat}
    (hlo : 0 ≤ round) (hhi : round < 10) (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I round t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).mem
      (oldLeftRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).aw
      rdata (cA, σ) k' C' := by
  have cases : round = 0 ∨ round = 1 ∨ round = 2 ∨ round = 3 ∨ round = 4 ∨ round = 5 ∨ round = 6 ∨ round = 7 ∨ round = 8 ∨ round = 9 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact runtime_leftRoundHelper_0 hov rd
  · exact runtime_leftRoundHelper_1 hov rd
  · exact runtime_leftRoundHelper_2 hov rd
  · exact runtime_leftRoundHelper_3 hov rd
  · exact runtime_leftRoundHelper_4 hov rd
  · exact runtime_leftRoundHelper_5 hov rd
  · exact runtime_leftRoundHelper_6 hov rd
  · exact runtime_leftRoundHelper_7 hov rd
  · exact runtime_leftRoundHelper_8 hov rd
  · exact runtime_leftRoundHelper_9 hov rd

private theorem runtime_leftRoundHelper_10_19 {cA σ I} {g : Sat256} {s0 : State}
    {round : Nat} {t : List UInt256} {c : RuntimeMemCursor}
    {rdata : ByteArray} {k C : Nat}
    (hlo : 10 ≤ round) (hhi : round < 20) (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I round t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).mem
      (oldLeftRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).aw
      rdata (cA, σ) k' C' := by
  have cases : round = 10 ∨ round = 11 ∨ round = 12 ∨ round = 13 ∨ round = 14 ∨ round = 15 ∨ round = 16 ∨ round = 17 ∨ round = 18 ∨ round = 19 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact runtime_leftRoundHelper_10 hov rd
  · exact runtime_leftRoundHelper_11 hov rd
  · exact runtime_leftRoundHelper_12 hov rd
  · exact runtime_leftRoundHelper_13 hov rd
  · exact runtime_leftRoundHelper_14 hov rd
  · exact runtime_leftRoundHelper_15 hov rd
  · exact runtime_leftRoundHelper_16 hov rd
  · exact runtime_leftRoundHelper_17 hov rd
  · exact runtime_leftRoundHelper_18 hov rd
  · exact runtime_leftRoundHelper_19 hov rd

private theorem runtime_leftRoundHelper_20_29 {cA σ I} {g : Sat256} {s0 : State}
    {round : Nat} {t : List UInt256} {c : RuntimeMemCursor}
    {rdata : ByteArray} {k C : Nat}
    (hlo : 20 ≤ round) (hhi : round < 30) (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I round t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).mem
      (oldLeftRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).aw
      rdata (cA, σ) k' C' := by
  have cases : round = 20 ∨ round = 21 ∨ round = 22 ∨ round = 23 ∨ round = 24 ∨ round = 25 ∨ round = 26 ∨ round = 27 ∨ round = 28 ∨ round = 29 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact runtime_leftRoundHelper_20 hov rd
  · exact runtime_leftRoundHelper_21 hov rd
  · exact runtime_leftRoundHelper_22 hov rd
  · exact runtime_leftRoundHelper_23 hov rd
  · exact runtime_leftRoundHelper_24 hov rd
  · exact runtime_leftRoundHelper_25 hov rd
  · exact runtime_leftRoundHelper_26 hov rd
  · exact runtime_leftRoundHelper_27 hov rd
  · exact runtime_leftRoundHelper_28 hov rd
  · exact runtime_leftRoundHelper_29 hov rd

private theorem runtime_leftRoundHelper_30_39 {cA σ I} {g : Sat256} {s0 : State}
    {round : Nat} {t : List UInt256} {c : RuntimeMemCursor}
    {rdata : ByteArray} {k C : Nat}
    (hlo : 30 ≤ round) (hhi : round < 40) (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I round t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).mem
      (oldLeftRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).aw
      rdata (cA, σ) k' C' := by
  have cases : round = 30 ∨ round = 31 ∨ round = 32 ∨ round = 33 ∨ round = 34 ∨ round = 35 ∨ round = 36 ∨ round = 37 ∨ round = 38 ∨ round = 39 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact runtime_leftRoundHelper_30 hov rd
  · exact runtime_leftRoundHelper_31 hov rd
  · exact runtime_leftRoundHelper_32 hov rd
  · exact runtime_leftRoundHelper_33 hov rd
  · exact runtime_leftRoundHelper_34 hov rd
  · exact runtime_leftRoundHelper_35 hov rd
  · exact runtime_leftRoundHelper_36 hov rd
  · exact runtime_leftRoundHelper_37 hov rd
  · exact runtime_leftRoundHelper_38 hov rd
  · exact runtime_leftRoundHelper_39 hov rd

private theorem runtime_leftRoundHelper_40_49 {cA σ I} {g : Sat256} {s0 : State}
    {round : Nat} {t : List UInt256} {c : RuntimeMemCursor}
    {rdata : ByteArray} {k C : Nat}
    (hlo : 40 ≤ round) (hhi : round < 50) (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I round t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).mem
      (oldLeftRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).aw
      rdata (cA, σ) k' C' := by
  have cases : round = 40 ∨ round = 41 ∨ round = 42 ∨ round = 43 ∨ round = 44 ∨ round = 45 ∨ round = 46 ∨ round = 47 ∨ round = 48 ∨ round = 49 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact runtime_leftRoundHelper_40 hov rd
  · exact runtime_leftRoundHelper_41 hov rd
  · exact runtime_leftRoundHelper_42 hov rd
  · exact runtime_leftRoundHelper_43 hov rd
  · exact runtime_leftRoundHelper_44 hov rd
  · exact runtime_leftRoundHelper_45 hov rd
  · exact runtime_leftRoundHelper_46 hov rd
  · exact runtime_leftRoundHelper_47 hov rd
  · exact runtime_leftRoundHelper_48 hov rd
  · exact runtime_leftRoundHelper_49 hov rd

private theorem runtime_leftRoundHelper_50_59 {cA σ I} {g : Sat256} {s0 : State}
    {round : Nat} {t : List UInt256} {c : RuntimeMemCursor}
    {rdata : ByteArray} {k C : Nat}
    (hlo : 50 ≤ round) (hhi : round < 60) (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I round t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).mem
      (oldLeftRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).aw
      rdata (cA, σ) k' C' := by
  have cases : round = 50 ∨ round = 51 ∨ round = 52 ∨ round = 53 ∨ round = 54 ∨ round = 55 ∨ round = 56 ∨ round = 57 ∨ round = 58 ∨ round = 59 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact runtime_leftRoundHelper_50 hov rd
  · exact runtime_leftRoundHelper_51 hov rd
  · exact runtime_leftRoundHelper_52 hov rd
  · exact runtime_leftRoundHelper_53 hov rd
  · exact runtime_leftRoundHelper_54 hov rd
  · exact runtime_leftRoundHelper_55 hov rd
  · exact runtime_leftRoundHelper_56 hov rd
  · exact runtime_leftRoundHelper_57 hov rd
  · exact runtime_leftRoundHelper_58 hov rd
  · exact runtime_leftRoundHelper_59 hov rd

private theorem runtime_leftRoundHelper_60_69 {cA σ I} {g : Sat256} {s0 : State}
    {round : Nat} {t : List UInt256} {c : RuntimeMemCursor}
    {rdata : ByteArray} {k C : Nat}
    (hlo : 60 ≤ round) (hhi : round < 70) (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I round t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).mem
      (oldLeftRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).aw
      rdata (cA, σ) k' C' := by
  have cases : round = 60 ∨ round = 61 ∨ round = 62 ∨ round = 63 ∨ round = 64 ∨ round = 65 ∨ round = 66 ∨ round = 67 ∨ round = 68 ∨ round = 69 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact runtime_leftRoundHelper_60 hov rd
  · exact runtime_leftRoundHelper_61 hov rd
  · exact runtime_leftRoundHelper_62 hov rd
  · exact runtime_leftRoundHelper_63 hov rd
  · exact runtime_leftRoundHelper_64 hov rd
  · exact runtime_leftRoundHelper_65 hov rd
  · exact runtime_leftRoundHelper_66 hov rd
  · exact runtime_leftRoundHelper_67 hov rd
  · exact runtime_leftRoundHelper_68 hov rd
  · exact runtime_leftRoundHelper_69 hov rd

private theorem runtime_leftRoundHelper_70_79 {cA σ I} {g : Sat256} {s0 : State}
    {round : Nat} {t : List UInt256} {c : RuntimeMemCursor}
    {rdata : ByteArray} {k C : Nat}
    (hlo : 70 ≤ round) (hhi : round < 80) (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I round t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).mem
      (oldLeftRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).aw
      rdata (cA, σ) k' C' := by
  have cases : round = 70 ∨ round = 71 ∨ round = 72 ∨ round = 73 ∨ round = 74 ∨ round = 75 ∨ round = 76 ∨ round = 77 ∨ round = 78 ∨ round = 79 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact runtime_leftRoundHelper_70 hov rd
  · exact runtime_leftRoundHelper_71 hov rd
  · exact runtime_leftRoundHelper_72 hov rd
  · exact runtime_leftRoundHelper_73 hov rd
  · exact runtime_leftRoundHelper_74 hov rd
  · exact runtime_leftRoundHelper_75 hov rd
  · exact runtime_leftRoundHelper_76 hov rd
  · exact runtime_leftRoundHelper_77 hov rd
  · exact runtime_leftRoundHelper_78 hov rd
  · exact runtime_leftRoundHelper_79 hov rd

theorem runtime_leftRoundHelper {cA σ I} {g : Sat256} {s0 : State}
    {round : Nat} {t : List UInt256} {c : RuntimeMemCursor}
    {rdata : ByteArray} {k C : Nat}
    (hround : round < 80) (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨288⟩
      (oldLeftHelperStack I round t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8991⟩ t
      (oldLeftRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).mem
      (oldLeftRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).aw
      rdata (cA, σ) k' C' := by
  by_cases h10 : round < 10
  · exact runtime_leftRoundHelper_0_9 (by omega) h10 hov rd
  by_cases h20 : round < 20
  · exact runtime_leftRoundHelper_10_19 (by omega) h20 hov rd
  by_cases h30 : round < 30
  · exact runtime_leftRoundHelper_20_29 (by omega) h30 hov rd
  by_cases h40 : round < 40
  · exact runtime_leftRoundHelper_30_39 (by omega) h40 hov rd
  by_cases h50 : round < 50
  · exact runtime_leftRoundHelper_40_49 (by omega) h50 hov rd
  by_cases h60 : round < 60
  · exact runtime_leftRoundHelper_50_59 (by omega) h60 hov rd
  by_cases h70 : round < 70
  · exact runtime_leftRoundHelper_60_69 (by omega) h70 hov rd
  exact runtime_leftRoundHelper_70_79 (by omega) hround hov rd

private theorem runtime_rightRoundHelper_0_9 {cA σ I} {g : Sat256} {s0 : State}
    {round : Nat} {t : List UInt256} {c : RuntimeMemCursor}
    {rdata : ByteArray} {k C : Nat}
    (hlo : 0 ≤ round) (hhi : round < 10) (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I round t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).mem
      (oldRightRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).aw
      rdata (cA, σ) k' C' := by
  have cases : round = 0 ∨ round = 1 ∨ round = 2 ∨ round = 3 ∨ round = 4 ∨ round = 5 ∨ round = 6 ∨ round = 7 ∨ round = 8 ∨ round = 9 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact runtime_rightRoundHelper_0 hov rd
  · exact runtime_rightRoundHelper_1 hov rd
  · exact runtime_rightRoundHelper_2 hov rd
  · exact runtime_rightRoundHelper_3 hov rd
  · exact runtime_rightRoundHelper_4 hov rd
  · exact runtime_rightRoundHelper_5 hov rd
  · exact runtime_rightRoundHelper_6 hov rd
  · exact runtime_rightRoundHelper_7 hov rd
  · exact runtime_rightRoundHelper_8 hov rd
  · exact runtime_rightRoundHelper_9 hov rd

private theorem runtime_rightRoundHelper_10_19 {cA σ I} {g : Sat256} {s0 : State}
    {round : Nat} {t : List UInt256} {c : RuntimeMemCursor}
    {rdata : ByteArray} {k C : Nat}
    (hlo : 10 ≤ round) (hhi : round < 20) (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I round t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).mem
      (oldRightRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).aw
      rdata (cA, σ) k' C' := by
  have cases : round = 10 ∨ round = 11 ∨ round = 12 ∨ round = 13 ∨ round = 14 ∨ round = 15 ∨ round = 16 ∨ round = 17 ∨ round = 18 ∨ round = 19 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact runtime_rightRoundHelper_10 hov rd
  · exact runtime_rightRoundHelper_11 hov rd
  · exact runtime_rightRoundHelper_12 hov rd
  · exact runtime_rightRoundHelper_13 hov rd
  · exact runtime_rightRoundHelper_14 hov rd
  · exact runtime_rightRoundHelper_15 hov rd
  · exact runtime_rightRoundHelper_16 hov rd
  · exact runtime_rightRoundHelper_17 hov rd
  · exact runtime_rightRoundHelper_18 hov rd
  · exact runtime_rightRoundHelper_19 hov rd

private theorem runtime_rightRoundHelper_20_29 {cA σ I} {g : Sat256} {s0 : State}
    {round : Nat} {t : List UInt256} {c : RuntimeMemCursor}
    {rdata : ByteArray} {k C : Nat}
    (hlo : 20 ≤ round) (hhi : round < 30) (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I round t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).mem
      (oldRightRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).aw
      rdata (cA, σ) k' C' := by
  have cases : round = 20 ∨ round = 21 ∨ round = 22 ∨ round = 23 ∨ round = 24 ∨ round = 25 ∨ round = 26 ∨ round = 27 ∨ round = 28 ∨ round = 29 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact runtime_rightRoundHelper_20 hov rd
  · exact runtime_rightRoundHelper_21 hov rd
  · exact runtime_rightRoundHelper_22 hov rd
  · exact runtime_rightRoundHelper_23 hov rd
  · exact runtime_rightRoundHelper_24 hov rd
  · exact runtime_rightRoundHelper_25 hov rd
  · exact runtime_rightRoundHelper_26 hov rd
  · exact runtime_rightRoundHelper_27 hov rd
  · exact runtime_rightRoundHelper_28 hov rd
  · exact runtime_rightRoundHelper_29 hov rd

private theorem runtime_rightRoundHelper_30_39 {cA σ I} {g : Sat256} {s0 : State}
    {round : Nat} {t : List UInt256} {c : RuntimeMemCursor}
    {rdata : ByteArray} {k C : Nat}
    (hlo : 30 ≤ round) (hhi : round < 40) (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I round t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).mem
      (oldRightRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).aw
      rdata (cA, σ) k' C' := by
  have cases : round = 30 ∨ round = 31 ∨ round = 32 ∨ round = 33 ∨ round = 34 ∨ round = 35 ∨ round = 36 ∨ round = 37 ∨ round = 38 ∨ round = 39 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact runtime_rightRoundHelper_30 hov rd
  · exact runtime_rightRoundHelper_31 hov rd
  · exact runtime_rightRoundHelper_32 hov rd
  · exact runtime_rightRoundHelper_33 hov rd
  · exact runtime_rightRoundHelper_34 hov rd
  · exact runtime_rightRoundHelper_35 hov rd
  · exact runtime_rightRoundHelper_36 hov rd
  · exact runtime_rightRoundHelper_37 hov rd
  · exact runtime_rightRoundHelper_38 hov rd
  · exact runtime_rightRoundHelper_39 hov rd

private theorem runtime_rightRoundHelper_40_49 {cA σ I} {g : Sat256} {s0 : State}
    {round : Nat} {t : List UInt256} {c : RuntimeMemCursor}
    {rdata : ByteArray} {k C : Nat}
    (hlo : 40 ≤ round) (hhi : round < 50) (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I round t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).mem
      (oldRightRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).aw
      rdata (cA, σ) k' C' := by
  have cases : round = 40 ∨ round = 41 ∨ round = 42 ∨ round = 43 ∨ round = 44 ∨ round = 45 ∨ round = 46 ∨ round = 47 ∨ round = 48 ∨ round = 49 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact runtime_rightRoundHelper_40 hov rd
  · exact runtime_rightRoundHelper_41 hov rd
  · exact runtime_rightRoundHelper_42 hov rd
  · exact runtime_rightRoundHelper_43 hov rd
  · exact runtime_rightRoundHelper_44 hov rd
  · exact runtime_rightRoundHelper_45 hov rd
  · exact runtime_rightRoundHelper_46 hov rd
  · exact runtime_rightRoundHelper_47 hov rd
  · exact runtime_rightRoundHelper_48 hov rd
  · exact runtime_rightRoundHelper_49 hov rd

private theorem runtime_rightRoundHelper_50_59 {cA σ I} {g : Sat256} {s0 : State}
    {round : Nat} {t : List UInt256} {c : RuntimeMemCursor}
    {rdata : ByteArray} {k C : Nat}
    (hlo : 50 ≤ round) (hhi : round < 60) (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I round t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).mem
      (oldRightRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).aw
      rdata (cA, σ) k' C' := by
  have cases : round = 50 ∨ round = 51 ∨ round = 52 ∨ round = 53 ∨ round = 54 ∨ round = 55 ∨ round = 56 ∨ round = 57 ∨ round = 58 ∨ round = 59 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact runtime_rightRoundHelper_50 hov rd
  · exact runtime_rightRoundHelper_51 hov rd
  · exact runtime_rightRoundHelper_52 hov rd
  · exact runtime_rightRoundHelper_53 hov rd
  · exact runtime_rightRoundHelper_54 hov rd
  · exact runtime_rightRoundHelper_55 hov rd
  · exact runtime_rightRoundHelper_56 hov rd
  · exact runtime_rightRoundHelper_57 hov rd
  · exact runtime_rightRoundHelper_58 hov rd
  · exact runtime_rightRoundHelper_59 hov rd

private theorem runtime_rightRoundHelper_60_69 {cA σ I} {g : Sat256} {s0 : State}
    {round : Nat} {t : List UInt256} {c : RuntimeMemCursor}
    {rdata : ByteArray} {k C : Nat}
    (hlo : 60 ≤ round) (hhi : round < 70) (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I round t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).mem
      (oldRightRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).aw
      rdata (cA, σ) k' C' := by
  have cases : round = 60 ∨ round = 61 ∨ round = 62 ∨ round = 63 ∨ round = 64 ∨ round = 65 ∨ round = 66 ∨ round = 67 ∨ round = 68 ∨ round = 69 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact runtime_rightRoundHelper_60 hov rd
  · exact runtime_rightRoundHelper_61 hov rd
  · exact runtime_rightRoundHelper_62 hov rd
  · exact runtime_rightRoundHelper_63 hov rd
  · exact runtime_rightRoundHelper_64 hov rd
  · exact runtime_rightRoundHelper_65 hov rd
  · exact runtime_rightRoundHelper_66 hov rd
  · exact runtime_rightRoundHelper_67 hov rd
  · exact runtime_rightRoundHelper_68 hov rd
  · exact runtime_rightRoundHelper_69 hov rd

private theorem runtime_rightRoundHelper_70_79 {cA σ I} {g : Sat256} {s0 : State}
    {round : Nat} {t : List UInt256} {c : RuntimeMemCursor}
    {rdata : ByteArray} {k C : Nat}
    (hlo : 70 ≤ round) (hhi : round < 80) (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I round t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).mem
      (oldRightRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).aw
      rdata (cA, σ) k' C' := by
  have cases : round = 70 ∨ round = 71 ∨ round = 72 ∨ round = 73 ∨ round = 74 ∨ round = 75 ∨ round = 76 ∨ round = 77 ∨ round = 78 ∨ round = 79 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact runtime_rightRoundHelper_70 hov rd
  · exact runtime_rightRoundHelper_71 hov rd
  · exact runtime_rightRoundHelper_72 hov rd
  · exact runtime_rightRoundHelper_73 hov rd
  · exact runtime_rightRoundHelper_74 hov rd
  · exact runtime_rightRoundHelper_75 hov rd
  · exact runtime_rightRoundHelper_76 hov rd
  · exact runtime_rightRoundHelper_77 hov rd
  · exact runtime_rightRoundHelper_78 hov rd
  · exact runtime_rightRoundHelper_79 hov rd

theorem runtime_rightRoundHelper {cA σ I} {g : Sat256} {s0 : State}
    {round : Nat} {t : List UInt256} {c : RuntimeMemCursor}
    {rdata : ByteArray} {k C : Nat}
    (hround : round < 80) (hov : t.length + 64 ≤ 1024)
    (rd : RD runtimeBytecode I g s0 ⟨4126⟩
      (oldRightHelperStack I round t) c.mem c.aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ⟨8967⟩ t
      (oldRightRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).mem
      (oldRightRoundCursor c (hashScratchPtr I) (round / 16) (round % 16)).aw
      rdata (cA, σ) k' C' := by
  by_cases h10 : round < 10
  · exact runtime_rightRoundHelper_0_9 (by omega) h10 hov rd
  by_cases h20 : round < 20
  · exact runtime_rightRoundHelper_10_19 (by omega) h20 hov rd
  by_cases h30 : round < 30
  · exact runtime_rightRoundHelper_20_29 (by omega) h30 hov rd
  by_cases h40 : round < 40
  · exact runtime_rightRoundHelper_30_39 (by omega) h40 hov rd
  by_cases h50 : round < 50
  · exact runtime_rightRoundHelper_40_49 (by omega) h50 hov rd
  by_cases h60 : round < 60
  · exact runtime_rightRoundHelper_50_59 (by omega) h60 hov rd
  by_cases h70 : round < 70
  · exact runtime_rightRoundHelper_60_69 (by omega) h70 hov rd
  exact runtime_rightRoundHelper_70_79 (by omega) hround hov rd

def oldLeftLineCursor (initial : RuntimeMemCursor) (messageBase : UInt256) :
    Nat → RuntimeMemCursor
  | 0 => initial
  | round + 1 => oldLeftRoundCursor (oldLeftLineCursor initial messageBase round)
      messageBase (round / 16) (round % 16)

def oldRightLineCursor (initial : RuntimeMemCursor) (messageBase : UInt256) :
    Nat → RuntimeMemCursor
  | 0 => initial
  | round + 1 => oldRightRoundCursor (oldRightLineCursor initial messageBase round)
      messageBase (round / 16) (round % 16)

def oldPureLeftLine (X : Fin 16 → UInt256) : Nat → RuntimeLineState → RuntimeLineState
  | 0, s => s
  | round + 1, s => runtimePureLeftRound X (round / 16) (round % 16)
      (oldPureLeftLine X round s)

def oldPureRightLine (X : Fin 16 → UInt256) : Nat → RuntimeLineState → RuntimeLineState
  | 0, s => s
  | round + 1, s => runtimePureRightRound X (round / 16) (round % 16)
      (oldPureRightLine X round s)

theorem oldLeftRoundCursor_padded {I : ExecutionEnv}
    {c : RuntimeMemCursor} {n group round : Nat}
    (hc : RuntimePaddedCursor I c n)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RuntimePaddedCursor I (oldLeftRoundCursor c (hashScratchPtr I) group round) n := by
  unfold oldLeftRoundCursor
  exact runtimeRoundCursor_padded (lineOffset := 512) hc hsmall
    (hashScratchAdd_toNat I hsmall (by omega : 512 ≤ 895)) (by omega)

theorem oldRightRoundCursor_padded {I : ExecutionEnv}
    {c : RuntimeMemCursor} {n group round : Nat}
    (hc : RuntimePaddedCursor I c n)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RuntimePaddedCursor I (oldRightRoundCursor c (hashScratchPtr I) group round) n := by
  unfold oldRightRoundCursor
  exact runtimeRoundCursor_padded (lineOffset := 672) hc hsmall
    (hashScratchAdd_toNat I hsmall (by omega : 672 ≤ 895)) (by omega)

theorem oldLeftRoundCursor_line_padded {I : ExecutionEnv}
    {cursor : RuntimeMemCursor} {n group round : Nat}
    {X : Fin 16 → UInt256} {s : RuntimeLineState}
    (hpadded : RuntimePaddedCursor I cursor n)
    (hmessage : RuntimeMessageAt cursor (hashScratchPtr I) X)
    (hline : RuntimeLineAt cursor (hashScratchPtr I + ⟨512⟩) s)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RuntimeLineAt (oldLeftRoundCursor cursor (hashScratchPtr I) group round)
      (hashScratchPtr I + ⟨512⟩) (runtimePureLeftRound X group round s) := by
  rcases runtimeRoundValues_padded (lineOffset := 512) hpadded hmessage hline hsmall
      (hashScratchAdd_toNat I hsmall (by omega : 512 ≤ 895)) (by omega)
      (row := leftWordRowWord group) (round := UInt256.ofNat round) with
    ⟨ha, hb, hc, hd, he, hx⟩
  have hr := runtimeRoundCursor_line_padded (lineOffset := 512) hpadded hmessage hline
    hsmall (hashScratchAdd_toNat I hsmall (by omega : 512 ≤ 895)) (by omega)
    (round := UInt256.ofNat round) (row := leftWordRowWord group)
    (rotationRow := leftRotationRowWord group)
    (boolF := runtimeLeftF group (runtimeRoundB cursor (hashScratchPtr I + ⟨512⟩))
      (runtimeRoundC cursor (hashScratchPtr I + ⟨512⟩))
      (runtimeRoundD cursor (hashScratchPtr I + ⟨512⟩)))
    (constant := leftConstantWord group)
  simpa [oldLeftRoundCursor, runtimePureLeftRound, hb, hc, hd] using hr

theorem oldRightRoundCursor_line_padded {I : ExecutionEnv}
    {cursor : RuntimeMemCursor} {n group round : Nat}
    {X : Fin 16 → UInt256} {s : RuntimeLineState}
    (hpadded : RuntimePaddedCursor I cursor n)
    (hmessage : RuntimeMessageAt cursor (hashScratchPtr I) X)
    (hline : RuntimeLineAt cursor (hashScratchPtr I + ⟨672⟩) s)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RuntimeLineAt (oldRightRoundCursor cursor (hashScratchPtr I) group round)
      (hashScratchPtr I + ⟨672⟩) (runtimePureRightRound X group round s) := by
  rcases runtimeRoundValues_padded (lineOffset := 672) hpadded hmessage hline hsmall
      (hashScratchAdd_toNat I hsmall (by omega : 672 ≤ 895)) (by omega)
      (row := rightWordRowWord group) (round := UInt256.ofNat round) with
    ⟨ha, hb, hc, hd, he, hx⟩
  have hr := runtimeRoundCursor_line_padded (lineOffset := 672) hpadded hmessage hline
    hsmall (hashScratchAdd_toNat I hsmall (by omega : 672 ≤ 895)) (by omega)
    (round := UInt256.ofNat round) (row := rightWordRowWord group)
    (rotationRow := rightRotationRowWord group)
    (boolF := runtimeRightF group (runtimeRoundB cursor (hashScratchPtr I + ⟨672⟩))
      (runtimeRoundC cursor (hashScratchPtr I + ⟨672⟩))
      (runtimeRoundD cursor (hashScratchPtr I + ⟨672⟩)))
    (constant := rightConstantWord group)
  simpa [oldRightRoundCursor, runtimePureRightRound, hb, hc, hd] using hr

theorem RuntimeLeftWideInvariant.oldRound {I : ExecutionEnv}
    {cursor : RuntimeMemCursor} {n group round : Nat}
    {X : Fin 16 → UInt256} {s : RuntimeLineState}
    (hinv : RuntimeLeftWideInvariant I cursor n X s)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RuntimeLeftWideInvariant I
      (oldLeftRoundCursor cursor (hashScratchPtr I) group round) n X
      (runtimePureLeftRound X group round s) := by
  rcases hinv with ⟨hp, hm, hl⟩
  have hline := hashScratchAdd_toNat I hsmall (by omega : 512 ≤ 895)
  refine ⟨oldLeftRoundCursor_padded hp hsmall, ?_,
    oldLeftRoundCursor_line_padded hp hm hl hsmall⟩
  intro i
  unfold oldLeftRoundCursor
  apply (hm i).runtimeRoundCursor_below_padded (lineOffset := 512) hp hsmall hline
    (by omega)
  rw [runtimeMessageAddress_toNat i (lt_of_le_of_lt
    (Nat.add_le_add_left (by omega : 512 ≤ 895) _)
    (hashScratchPtr_add_uint I hsmall)), hline]
  omega

theorem RuntimeRightWideInvariant.oldRound {I : ExecutionEnv}
    {cursor : RuntimeMemCursor} {n group round : Nat}
    {X : Fin 16 → UInt256} {left right : RuntimeLineState}
    (hinv : RuntimeRightWideInvariant I cursor n X left right)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RuntimeRightWideInvariant I
      (oldRightRoundCursor cursor (hashScratchPtr I) group round) n X left
      (runtimePureRightRound X group round right) := by
  rcases hinv with ⟨hp, hm, hl, hr⟩
  have hline := hashScratchAdd_toNat I hsmall (by omega : 672 ≤ 895)
  have h672 : (hashScratchPtr I + ⟨672⟩).toNat =
      (hashScratchPtr I).toNat + 672 := by simpa using hline
  have h512 : (hashScratchPtr I + ⟨512⟩).toNat =
      (hashScratchPtr I).toNat + 512 := by
    simpa using hashScratchAdd_toNat I hsmall (by omega : 512 ≤ 895)
  have h544 : (hashScratchPtr I + ⟨512⟩ + ⟨32⟩).toNat =
      (hashScratchPtr I).toNat + 544 := by
    simpa [u256_add_assoc,
      show (⟨512⟩ : UInt256) + ⟨32⟩ = ⟨544⟩ by native_decide] using
      hashScratchAdd_toNat I hsmall (by omega : 544 ≤ 895)
  have h576 : (hashScratchPtr I + ⟨512⟩ + ⟨64⟩).toNat =
      (hashScratchPtr I).toNat + 576 := by
    simpa [u256_add_assoc,
      show (⟨512⟩ : UInt256) + ⟨64⟩ = ⟨576⟩ by native_decide] using
      hashScratchAdd_toNat I hsmall (by omega : 576 ≤ 895)
  have h608 : (hashScratchPtr I + ⟨512⟩ + ⟨96⟩).toNat =
      (hashScratchPtr I).toNat + 608 := by
    simpa [u256_add_assoc,
      show (⟨512⟩ : UInt256) + ⟨96⟩ = ⟨608⟩ by native_decide] using
      hashScratchAdd_toNat I hsmall (by omega : 608 ≤ 895)
  have h640 : (hashScratchPtr I + ⟨512⟩ + ⟨128⟩).toNat =
      (hashScratchPtr I).toNat + 640 := by
    simpa [u256_add_assoc,
      show (⟨512⟩ : UInt256) + ⟨128⟩ = ⟨640⟩ by native_decide] using
      hashScratchAdd_toNat I hsmall (by omega : 640 ≤ 895)
  have preserve {addr value : UInt256} (hw : RuntimeWordAt cursor addr value)
      (hbelow : addr.toNat + 32 ≤ (hashScratchPtr I + ⟨672⟩).toNat) :
      RuntimeWordAt (oldRightRoundCursor cursor (hashScratchPtr I) group round)
        addr value := by
    unfold oldRightRoundCursor
    exact hw.runtimeRoundCursor_below_padded (lineOffset := 672) hp hsmall hline
      (by omega) hbelow
  refine ⟨oldRightRoundCursor_padded hp hsmall, ?_, ?_,
    oldRightRoundCursor_line_padded hp hm hr hsmall⟩
  · intro i
    apply preserve (hm i)
    rw [runtimeMessageAddress_toNat i (lt_of_le_of_lt
      (Nat.add_le_add_left (by omega : 512 ≤ 895) _)
      (hashScratchPtr_add_uint I hsmall)), h672]
    omega
  · exact ⟨preserve hl.1 (by rw [h512, h672]; omega),
      preserve hl.2.1 (by rw [h544, h672]; omega),
      preserve hl.2.2.1 (by rw [h576, h672]; omega),
      preserve hl.2.2.2.1 (by rw [h608, h672]; omega),
      preserve hl.2.2.2.2 (by rw [h640, h672])⟩

theorem oldLeftLineCursor_wideInvariant {I : ExecutionEnv}
    {initial : RuntimeMemCursor} {n rounds : Nat}
    {X : Fin 16 → UInt256} {s : RuntimeLineState}
    (hinv : RuntimeLeftWideInvariant I initial n X s)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RuntimeLeftWideInvariant I
      (oldLeftLineCursor initial (hashScratchPtr I) rounds) n X
      (oldPureLeftLine X rounds s) := by
  induction rounds with
  | zero => simpa [oldLeftLineCursor, oldPureLeftLine] using hinv
  | succ round ih =>
      simpa [oldLeftLineCursor, oldPureLeftLine] using
        Ripemd160Old.RuntimeLeftWideInvariant.oldRound ih hsmall

theorem oldRightLineCursor_wideInvariant {I : ExecutionEnv}
    {initial : RuntimeMemCursor} {n rounds : Nat}
    {X : Fin 16 → UInt256} {left right : RuntimeLineState}
    (hinv : RuntimeRightWideInvariant I initial n X left right)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RuntimeRightWideInvariant I
      (oldRightLineCursor initial (hashScratchPtr I) rounds) n X left
      (oldPureRightLine X rounds right) := by
  induction rounds with
  | zero => simpa [oldRightLineCursor, oldPureRightLine] using hinv
  | succ round ih =>
      simpa [oldRightLineCursor, oldPureRightLine] using
        Ripemd160Old.RuntimeRightWideInvariant.oldRound ih hsmall

end Ripemd160Old
