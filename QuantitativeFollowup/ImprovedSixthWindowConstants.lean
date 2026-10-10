module
public import QuantitativeFollowup.ImprovedSixthWindowProbability
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-! Uniform threshold and constants for sixth-window probability conversion.
No model tail conclusion is an input. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace QuantitativeFollowup
open QuantitativePaper
set_option maxHeartbeats 1000000

theorem improved_sixth_window_uniform_constants (a C A L : ℝ) (ha : 0<a) (hC : 0<C)
    (haC : a≤C) (hA : 0<A) (hL : 0<L) :
    ∃Nt : ℕ,∃Ax xstar cx Cx : ℝ,0<Ax ∧ 0<xstar ∧ 0<cx ∧ 0<Cx ∧
      ∀n : ℕ,Nt≤n→∀(Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : Ω→ℝ),Measurable X→
      (∀s : ℝ,0<s→s≤L→Integrable (fun ω=>Real.exp (s*X ω)) P)→
      (∀s : ℝ,0<s→s≤L→cgf X P s≤C*(n:ℝ)*s^6)→
      (∀s : ℝ,A*(n:ℝ)^(-(7/50:ℝ))≤s→s≤L→a*(n:ℝ)*s^6≤cgf X P s)→
      ∀x : ℝ,Ax*(n:ℝ)^(-(7/10:ℝ))≤x→x≤xstar→
        Real.exp (-Cx*(n:ℝ)*x^(6/5:ℝ))≤P.real {ω | (n:ℝ)*x≤X ω} ∧
        P.real {ω | (n:ℝ)*x≤X ω}≤Real.exp (-cx*(n:ℝ)*x^(6/5:ℝ)) := by
  let Ax:=a/2*A^5
  let xstar:=a/2*(L/2)^5
  let cx:=5/(6*(6*C)^(1/5:ℝ))
  let Cx:=(64*C+a)*(2/a)^(6/5:ℝ)
  have hp : Tendsto (fun n : ℕ=>a*A^6*(n:ℝ)^(4/25:ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop (by positivity : 0<a*A^6)
      ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<4/25)).comp tendsto_natCast_atTop_atTop)
  obtain ⟨Ns,hNs⟩:=eventually_atTop.1 (hp.eventually_ge_atTop (Real.log 4))
  let Nt:=max 1 Ns
  refine ⟨Nt,Ax,xstar,cx,Cx,by positivity,by positivity,by positivity,by positivity,?_⟩
  intro n hn Ω instΩ P instP X hXm hi hupper hlower x hxlo hxhi
  have hn1 : 1≤n := (le_max_left _ _).trans hn
  have hnR : 0<(n:ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hn1
  exact improved_sixth_window_probability_bounds X hXm (n:ℝ) a C A L x hnR ha hC haC hA hL
    hi hupper hlower (hNs n ((le_max_right _ _).trans hn)) hxlo hxhi

end QuantitativeFollowup
