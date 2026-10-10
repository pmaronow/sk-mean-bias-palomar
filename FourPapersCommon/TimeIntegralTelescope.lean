module
public import FourPapersCommon.ProgressiveTimeIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

/-! Actual finite telescoping of Bochner integrals across ordered time
cells, retaining repeated nodes. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators NNReal
namespace FourPapersCommon
set_option maxHeartbeats 400000
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem sum_setIntegral_Ioc_adjacent (f : ℝ≥0→E) (μ : Measure ℝ≥0)
    (a : ℕ→ℝ≥0) (N : ℕ) (ha : ∀i≤N,a 0≤a i)
    (hm : ∀i<N,a i≤a (i+1))
    (hi : ∀i≤N,IntegrableOn f (Ioc (a 0) (a i)) μ) :
    (∑i∈Finset.range N,∫r in Ioc (a i) (a (i+1)),f r ∂μ)=
      ∫r in Ioc (a 0) (a N),f r ∂μ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih (fun i h=>ha i (by omega))
      (fun i h=>hm i (by omega)) (fun i h=>hi i (by omega))]
    have hs : Ioc (a N) (a (N+1))⊆Ioc (a 0) (a (N+1)) := by
      intro r hr
      exact ⟨(ha N (by omega)).trans_lt hr.1,hr.2⟩
    rw [←setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      (hi N (by omega)) ((hi (N+1) le_rfl).mono_set hs),
      Ioc_union_Ioc_eq_Ioc (ha N (by omega)) (hm N (by omega))]

end FourPapersCommon
