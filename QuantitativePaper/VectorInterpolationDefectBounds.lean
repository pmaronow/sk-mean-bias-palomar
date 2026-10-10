module
public import QuantitativePaper.VectorInterpolationDefect

@[expose] public section

/-! Universal bounds on the literal conditional replica interpolation
error, including its actual free-measure mass. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace QuantitativePaper
open QuantitativeFollowup
variable {n : ℕ}

theorem vectorInterpolationDefect_le_free_mass (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hs : s≤1) (hβ : β≠0) (ht : t<1) :
    vectorInterpolationDefect (n:=n) μ s β t ht.le≤4*(1-s) := by
  have hi:=integrable_vectorInterpolationDefect hn μ s β t hβ ht
  have he:=integral_mono hi (integrable_const (4:ℝ))
    (fun q=>(vectorConditionalReplicaDefect_bounds hn μ β t s ht.le q).2)
  rw [integral_const,Measure.real,parisiFreeMeasure_univ,ENNReal.toReal_ofReal (sub_nonneg.mpr hs)] at he
  simpa only [vectorInterpolationDefect,smul_eq_mul,mul_comm] using he

theorem vectorInterpolationDefect_bounds (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hs : s≤1) (hβ : β≠0) (ht : t<1) :
    0≤vectorInterpolationDefect (n:=n) μ s β t ht.le ∧
      vectorInterpolationDefect (n:=n) μ s β t ht.le≤4*(1-s) :=
  ⟨vectorInterpolationDefect_nonneg hn μ s β t ht.le,
    vectorInterpolationDefect_le_free_mass hn μ s β t hs hβ ht⟩

end QuantitativePaper
