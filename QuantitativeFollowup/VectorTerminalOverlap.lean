module
public import QuantitativeFollowup.VectorMeanOverlap
public import QuantitativePaper.VectorMeasureTerminalGradient

@[expose] public section

/-! Strict terminal self-overlap under the genuine fractional disorder
tilt, obtained from the actual finite-spin Gibbs law at the state endpoint. -/
noncomputable section
open MeasureTheory Set QuantitativePaper
open scoped Topology BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 800000
variable {n : ℕ}

theorem vectorMeanOverlap_one_lt_one (hn : 0<n) (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) : vectorMeanOverlap (n:=n) μ β t a ht 1<1 := by
  let P:=vectorMeasureDisorderTilt (n:=n) μ β t a
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  let g:=fun sample=>∑l : Fin n,(vectorMeasureSpinMean μ β t ht 1 sample l)^2
  have hi : Integrable g P := by
    apply integrable_finsetSum
    intro l _
    simpa only [pow_two] using integrable_vectorMeanOverlap_mul μ β t a ht 1 1 l
  have hstrict (sample : VectorDisorderBrownianSample n) : g sample<(n:ℝ) := by
    have hh:=vectorMeasureGradient_one_norm_sq_lt μ hn β t ht sample.1
      (vectorMeasureState μ β t ht 1 sample)
    have hone : ((1:Paper.Overlap):ℝ)=1 := rfl
    simpa only [g,EuclideanSpace.real_norm_sq_eq,vectorMeasureSpinMean,hone,
      Real.toNNReal_one] using hh
  have hz : 0<∫sample,(n:ℝ)-g sample∂P := by
    apply (integral_pos_iff_support_of_nonneg (fun sample=>(sub_pos.mpr (hstrict sample)).le)
      ((integrable_const (n:ℝ)).sub hi)).mpr
    have heq : Function.support (fun sample=>(n:ℝ)-g sample)=Set.univ := by
      ext sample
      simp only [Function.mem_support,mem_univ,iff_true]
      exact (sub_pos.mpr (hstrict sample)).ne'
    rw [heq]
    simp [P]
  simp only [integral_sub (integrable_const (n:ℝ)) hi,integral_const,probReal_univ,
    one_smul] at hz
  unfold vectorMeanOverlap
  rw [←integral_finsetSum _ (fun l _=>by
    simpa only [pow_two] using integrable_vectorMeanOverlap_mul μ β t a ht 1 1 l)]
  apply (div_lt_iff₀ (Nat.cast_pos.mpr hn)).mpr
  change (∫sample,g sample∂P)<1*(n:ℝ)
  linarith

end QuantitativeFollowup
