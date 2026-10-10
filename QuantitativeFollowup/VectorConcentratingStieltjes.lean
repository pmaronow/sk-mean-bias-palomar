module
public import QuantitativeFollowup.VectorConcentratingDelta
public import QuantitativeFollowup.StieltjesAbsolutelyContinuousDensity
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-! Literal Stieltjes representation of the actual concentrating curvature
mass. Global absolute continuity is derived from the true bounded continuous
Hessian-energy derivative and the actual closed-time evolution. -/
noncomputable section
open Set MeasureTheory Filter Paper QuantitativePaper
open scoped Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
variable {n : ℕ}

theorem exists_lipschitz_vectorMeanOverlapReal (μ : Paper.ParisiMeasure) (beta t outer : ℝ)
    (hbeta : beta ≠ 0) (ht : t < 1) :
    ∃K : NNReal, LipschitzWith K (vectorMeanOverlapReal (n:=n) μ beta t outer ht.le) := by
  obtain ⟨C,hC⟩ := (isCompact_univ : IsCompact (univ : Set Paper.Overlap)).exists_bound_of_continuousOn
    (continuous_vectorMeanOverlapDerivative (n:=n) μ beta t outer ht.le).continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (0 : Paper.Overlap) (mem_univ _))
  have hP : LipschitzWith (Real.toNNReal C) (vectorMeanOverlapPrimitive (n:=n) μ beta t outer ht.le) := by
    apply lipschitzWith_of_nnnorm_deriv_le
    · intro x
      exact (hasDerivAt_vectorMeanOverlapPrimitive μ beta t outer ht.le x).differentiableAt
    · intro x
      rw [(hasDerivAt_vectorMeanOverlapPrimitive μ beta t outer ht.le x).deriv]
      apply NNReal.coe_le_coe.mp
      simpa only [coe_nnnorm, Real.coe_toNNReal C hC0] using hC (projIcc 0 1 zero_le_one x) (mem_univ _)
  have hclamp : LipschitzWith 1 (fun x : ℝ => ((projIcc (0 : ℝ) 1 zero_le_one x : Paper.Overlap) : ℝ)) :=
    by
      simpa only [mul_one, Function.comp_def] using
        (LipschitzWith.subtype_val (Icc (0 : ℝ) 1)).comp (LipschitzWith.projIcc zero_le_one)
  refine ⟨Real.toNNReal C, ?_⟩
  have hp := hP.comp hclamp
  have he : (fun x : ℝ => vectorMeanOverlapPrimitive (n:=n) μ beta t outer ht.le
      ((projIcc (0 : ℝ) 1 zero_le_one x : Paper.Overlap) : ℝ)) =
      vectorMeanOverlapReal (n:=n) μ beta t outer ht.le := by
    funext x
    rw [vectorMeanOverlapPrimitive_eq μ beta t outer hbeta ht (projIcc 0 1 zero_le_one x).property]
    simp only [vectorMeanOverlapReal, projIcc_of_mem zero_le_one (projIcc 0 1 zero_le_one x).property]
  change LipschitzWith (Real.toNNReal C*1) _ at hp
  simpa only [mul_one, Function.comp_def, he] using hp

def vectorOverlapStieltjes (μ : Paper.ParisiMeasure) (beta t outer : ℝ)
    (hbeta : beta ≠ 0) (ht : t < 1) : StieltjesFunction ℝ where
  toFun := vectorMeanOverlapReal (n:=n) μ beta t outer ht.le
  mono' := (vectorMeanOverlap_monotone (n:=n) μ beta t outer hbeta ht).comp (monotone_projIcc zero_le_one)
  right_continuous' _x := (continuous_vectorMeanOverlapReal μ beta t outer ht.le).continuousAt.continuousWithinAt

@[simp] theorem vectorOverlapStieltjes_apply (μ : Paper.ParisiMeasure) (beta t outer : ℝ)
    (hbeta : beta ≠ 0) (ht : t < 1) (x : ℝ) :
    vectorOverlapStieltjes (n:=n) μ beta t outer hbeta ht x = vectorMeanOverlapReal (n:=n) μ beta t outer ht.le x := rfl

theorem vectorOverlapStieltjes_measure_density (μ : Paper.ParisiMeasure) (beta t outer : ℝ)
    (hbeta : beta ≠ 0) (ht : t < 1) :
    (vectorOverlapStieltjes (n:=n) μ beta t outer hbeta ht).measure =
      volume.withDensity (fun x => ENNReal.ofReal (deriv (vectorMeanOverlapReal (n:=n) μ beta t outer ht.le) x)) := by
  obtain ⟨K,hK⟩ := exists_lipschitz_vectorMeanOverlapReal (n:=n) μ beta t outer hbeta ht
  exact stieltjes_measure_eq_derivative_density _ (fun a b => hK.lipschitzOnWith.absolutelyContinuousOnInterval)

theorem vectorConcentratingDelta_eq_stieltjes (μ : Paper.ParisiMeasure) (beta t outer : ℝ)
    (hbeta : beta ≠ 0) (ht : t < 1) (a ell : ℝ) (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell) :
    vectorConcentratingDelta (n:=n) μ beta t outer ht.le a ell =
      ∫x, concentratingIntervalBump a ell x ∂(vectorOverlapStieltjes (n:=n) μ beta t outer hbeta ht).measure := by
  rw [vectorOverlapStieltjes_measure_density,
    integral_withDensity_eq_integral_toReal_smul (measurable_deriv _).ennreal_ofReal
      (Filter.Eventually.of_forall (fun _x => ENNReal.ofReal_lt_top))]
  have heq : (fun x => (ENNReal.ofReal (deriv (vectorMeanOverlapReal (n:=n) μ beta t outer ht.le) x)).toReal •
      concentratingIntervalBump a ell x) =
      (fun x => vectorMeanOverlapDerivative (n:=n) μ beta t outer ht.le (projIcc (0 : ℝ) 1 zero_le_one x)*
        concentratingIntervalBump a ell x) := by
    funext x
    have hnonneg : 0 ≤ deriv (vectorMeanOverlapReal (n:=n) μ beta t outer ht.le) x :=
      (vectorOverlapStieltjes (n:=n) μ beta t outer hbeta ht).mono.deriv_nonneg
    rw [ENNReal.toReal_ofReal hnonneg, smul_eq_mul]
    by_cases hx : x ∈ Ioo a (a+ell)
    · rw [(hasDerivAt_vectorMeanOverlapReal μ beta t outer hbeta ht
        ⟨ha.trans hx.1, hx.2.trans he⟩).deriv]
    · rw [concentratingIntervalBump_zero_outside a ell x hell hx, mul_zero, mul_zero]
  rw [heq]
  have hs : Function.support (fun x => vectorMeanOverlapDerivative (n:=n) μ beta t outer ht.le
      (projIcc (0 : ℝ) 1 zero_le_one x)*concentratingIntervalBump a ell x) ⊆ Ioc a (a+ell) := by
    intro x hx
    have hi : x ∈ Ioo a (a+ell) := by
      by_contra hn
      apply hx
      dsimp only
      rw [concentratingIntervalBump_zero_outside a ell x hell hn, mul_zero]
    exact ⟨hi.1,hi.2.le⟩
  exact intervalIntegral.integral_eq_integral_of_support_subset hs

end QuantitativeFollowup
