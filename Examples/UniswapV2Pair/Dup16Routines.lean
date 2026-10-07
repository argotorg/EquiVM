import Reasoning.Reach
open Ethereum Ethereum.EVM Reasoning.Theory

-- LIBRARY CANDIDATE: missing DUP16 cooked step and reachability combinator.
namespace Reasoning.Reach
theorem dup16_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj kk ll mm nn oo pp : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP16, .none))
    (hstk : s.machineState.stack =
      a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn :: oo :: pp :: t)
    (hov : t.length + 17 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok
          (stSwap s
            (pp :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn :: oo :: pp :: t),
            .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP16, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_dup16 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn :: oo :: pp :: t).length -
          16 + 17 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

end Reasoning.Reach
