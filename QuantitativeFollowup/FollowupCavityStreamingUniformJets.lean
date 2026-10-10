module
public import QuantitativeFollowup.FollowupCavityStreamingPolynomialBudget
public import FourPapersCommon.FiniteStreamingPolynomialsIterated

@[expose] public section

/-! Uniform genuine closed-interval derivatives of the finite physical
cavity expectation, obtained by repeated actual streaming. Their constants
depend on the original number of leaves and the fixed test bound. -/
noncomputable section
open Set
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
open FourPapersCommon.FiniteStreamingPolynomials
variable {n k : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem streamingAtom_parent_identity
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (A : CavityStreamingAtom n k) (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (A.eval β ρ hβ hρ s a)
      (eval (fun B=>B.eval β ρ hβ hρ s a) (cavityStreamingAtomResponse β ρ s a A) u)
      (Icc (0:ℝ) 1) u := by
  exact hasDerivWithinAt_cavityStreamingAtom_eval hn β ρ hβ hρ s a ha has hq A u hu

theorem hasDerivWithinAt_cavityStreamingAtom_withinJet
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (A : CavityStreamingAtom n k) (r : ℕ) (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (withinJet (A.eval β ρ hβ hρ s a) (Icc (0:ℝ) 1) r)
      (withinJet (A.eval β ρ hβ hρ s a) (Icc (0:ℝ) 1) (r+1) u) (Icc (0:ℝ) 1) u := by
  let f:=fun B : CavityStreamingAtom n k=>B.eval β ρ hβ hρ s a
  let R : CavityStreamingAtom n k→Polynomial (CavityStreamingAtom n k):=
    cavityStreamingAtomResponse β ρ s a
  have he : (fun x=>eval f [(1,[A])] x)=f A := by
    funext x
    simp only [eval,monoEval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      List.prod_cons,List.prod_nil,mul_one,one_mul,add_zero]
  have hh:=hasDerivWithinAt_withinJet f R (Icc (0:ℝ) 1) uniqueDiffOn_Icc_zero_one
    (fun B v hv=>streamingAtom_parent_identity hn β ρ hβ hρ s a ha has hq B v hv)
    [(1,[A])] r u hu
  rw [he] at hh
  exact hh

theorem abs_cavityStreamingAtom_withinJet_le
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (A : CavityStreamingAtom n k) (r : ℕ) (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    |withinJet (A.eval β ρ hβ hρ s a) (Icc (0:ℝ) 1) r u|≤
      growth (7*β^2) A.complexity r*A.bound := by
  let f:=fun B : CavityStreamingAtom n k=>B.eval β ρ hβ hρ s a
  let R : CavityStreamingAtom n k→Polynomial (CavityStreamingAtom n k):=
    cavityStreamingAtomResponse β ρ s a
  have he : (fun x=>eval f [(1,[A])] x)=f A := by
    funext x
    simp only [eval,monoEval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      List.prod_cons,List.prod_nil,mul_one,one_mul,add_zero]
  have hP : costBound CavityStreamingAtom.complexity A.complexity [(1,[A])] := by
    intro t ht
    simp only [List.mem_singleton] at ht
    subst t
    simp only [monoCost,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,le_refl]
  have hh:=abs_withinJet_le f R (Icc (0:ℝ) 1) uniqueDiffOn_Icc_zero_one
    (fun B v hv=>streamingAtom_parent_identity hn β ρ hβ hρ s a ha has hq B v hv)
    CavityStreamingAtom.bound (fun B=>B.bound_nonneg)
    (fun B v hv=>B.eval_abs_le β ρ hβ hρ s a hq v hv)
    CavityStreamingAtom.complexity (7*β^2) (by positivity)
    (fun B=>cavityStreamingAtomResponse_costBound β ρ s a B)
    (fun B=>cavityStreamingAtomResponse_finiteStreaming_budget_le β ρ ⟨hρ.1.le,hρ.2⟩ s a ha has hq B)
    A.complexity [(1,[A])] hP r u hu
  rw [he] at hh
  simpa only [budget,monoWeight,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    List.prod_cons,List.prod_nil,abs_one,mul_one,one_mul,add_zero] using hh

end QuantitativeFollowup
