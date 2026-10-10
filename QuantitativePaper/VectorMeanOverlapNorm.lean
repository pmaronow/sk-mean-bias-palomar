module
public import QuantitativeFollowup.VectorSupportContact

@[expose] public section

/-! The normalized actual self-overlap is the literal expected squared
Euclidean magnetization norm. Contact therefore gives the paper's Nq
identity without changing the underlying law. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace QuantitativePaper
open QuantitativeFollowup
set_option maxHeartbeats 700000
variable {n : ℕ}

theorem integrable_vectorMeasureSpinMean_norm_sq (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (q : Paper.Overlap) :
    Integrable (fun sample=>‖vectorMeasureSpinMean (n:=n) μ β t ht q sample‖^2)
      (vectorMeasureDisorderTilt μ β t a) := by
  have hi (l : Fin n) : Integrable (fun sample=>(vectorMeasureSpinMean μ β t ht q sample l)^2)
      (vectorMeasureDisorderTilt μ β t a):=by
    simpa only [pow_two] using integrable_vectorMeanOverlap_mul μ β t a ht q q l
  simpa only [EuclideanSpace.real_norm_sq_eq] using integrable_finset_sum Finset.univ (fun l _=>hi l)

theorem integral_vectorMeasureSpinMean_norm_sq_eq_overlap (hn : 0<n)
    (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap) :
    (∫sample,‖vectorMeasureSpinMean (n:=n) μ β t ht q sample‖^2
      ∂vectorMeasureDisorderTilt μ β t a)=(n : ℝ)*vectorMeanOverlap (n:=n) μ β t a ht q := by
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finset_sum]
  · unfold vectorMeanOverlap
    have hn':(n : ℝ)≠0:=by positivity
    field_simp
  · intro l _
    simpa only [pow_two] using integrable_vectorMeanOverlap_mul μ β t a ht q q l

theorem vector_free_support_norm_contact (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s : ℝ) (hs : s∈Ico (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (ha : 0≤a)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t a≤vectorMeasureFunctional n ν β t a)
    (q : Paper.Overlap) (hq : q∈(parisiFreeMeasure μ s).support) :
    (∫sample,‖vectorMeasureSpinMean (n:=n) μ β t ht.le q sample‖^2
      ∂vectorMeasureDisorderTilt μ β t a)=(n : ℝ)*(q : ℝ) := by
  rw [integral_vectorMeasureSpinMean_norm_sq_eq_overlap hn μ β t a ht.le q,
    (vector_free_support_contact hn μ s hs hμ β t a hβ ht ha hmin q hq).2]

end QuantitativePaper
