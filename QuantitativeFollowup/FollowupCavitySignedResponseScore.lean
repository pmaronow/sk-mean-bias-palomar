module
public import QuantitativeFollowup.FollowupCavitySignedResponseMeanResidual
public import FourPapersCommon.L2IntegralBounds

@[expose] public section

/-! The actual retained future residual and centered posterior score.
Its second-moment estimate comes from genuine conditional expectation
contraction and the finite mass of the future Stieltjes measure. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

def cavitySignedResponseFutureResidual (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (r l : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) : ℝ :=
  if r<l then cavitySignedResponseMeanResidual D μ r l sample else 0

def cavitySignedResponseIntegratedFutureResidual (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) : ℝ :=
  ∫l,cavitySignedResponseFutureResidual D μ r l sample ∂parisiFreeMeasure μ a

def cavitySignedResponseScore (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r : Paper.Overlap)
    (p : AnisotropicDisorderBrownianSample n×Configuration n) : ℝ :=
  cavitySignedResponseTerminalResidual D μ r p-
    cavitySignedResponseIntegratedFutureResidual D μ a r p.1

theorem measurable_uncurry_cavitySignedResponseFutureResidual (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (r : Paper.Overlap) :
    Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n =>
      cavitySignedResponseFutureResidual D μ r z.1 z.2) :=
  (measurable_uncurry_cavitySignedResponseMeanResidual D μ r).ite
    (measurableSet_lt measurable_const measurable_fst) measurable_const

theorem norm_cavitySignedResponseFutureResidual_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (r l : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) :
    ‖cavitySignedResponseFutureResidual D μ r l sample‖ ≤ 2 := by
  by_cases hrl : r<l
  · simpa only [cavitySignedResponseFutureResidual,if_pos hrl] using
      norm_cavitySignedResponseMeanResidual_le D μ r l sample
  · simp only [cavitySignedResponseFutureResidual,if_neg hrl,norm_zero]; norm_num

theorem measurable_cavitySignedResponseIntegratedFutureResidual (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r : Paper.Overlap) :
    Measurable (cavitySignedResponseIntegratedFutureResidual D μ a r) :=
  ((measurable_uncurry_cavitySignedResponseFutureResidual D μ r).stronglyMeasurable.integral_prod_left'
    (μ := parisiFreeMeasure μ a)).measurable

theorem norm_cavitySignedResponseIntegratedFutureResidual_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1) (r : Paper.Overlap)
    (sample : AnisotropicDisorderBrownianSample n) :
    ‖cavitySignedResponseIntegratedFutureResidual D μ a r sample‖ ≤ 2 :=
  anisotropic_freeIntegral_bound μ a ha _ 2 (by norm_num)
    (fun l => norm_cavitySignedResponseFutureResidual_le D μ r l sample)

private theorem future_residual_integrable (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r : Paper.Overlap) :
    Integrable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n =>
      cavitySignedResponseFutureResidual D μ r z.1 z.2)
      ((parisiFreeMeasure μ a).prod (anisotropicMeasureSampleLaw D μ a)) :=
  (integrable_const 2).mono'
    (measurable_uncurry_cavitySignedResponseFutureResidual D μ r).aestronglyMeasurable
    (.of_forall fun z => norm_cavitySignedResponseFutureResidual_le D μ r z.1 z.2)

private theorem future_residual_square_integrable (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r : Paper.Overlap) :
    Integrable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n =>
      (cavitySignedResponseFutureResidual D μ r z.1 z.2)^2)
      ((parisiFreeMeasure μ a).prod (anisotropicMeasureSampleLaw D μ a)) := by
  apply (integrable_const 4).mono'
    ((measurable_uncurry_cavitySignedResponseFutureResidual D μ r).pow_const 2).aestronglyMeasurable
  exact .of_forall fun z => by
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) (norm_cavitySignedResponseFutureResidual_le D μ r z.1 z.2) 2).trans_eq (by norm_num)

theorem cavitySignedResponseIntegratedFutureResidual_centered (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r : Paper.Overlap) :
    (∫sample,cavitySignedResponseIntegratedFutureResidual D μ a r sample
      ∂anisotropicMeasureSampleLaw D μ a)=0 := by
  have he (l : Paper.Overlap) : (∫sample,cavitySignedResponseFutureResidual D μ r l sample
      ∂anisotropicMeasureSampleLaw D μ a)=0 := by
    by_cases hrl : r<l
    · simpa only [cavitySignedResponseFutureResidual,if_pos hrl] using
        cavitySignedResponseMeanResidual_centered D μ a r l hrl.le
    · simp only [cavitySignedResponseFutureResidual,if_neg hrl,integral_zero]
  change (∫sample,∫l,cavitySignedResponseFutureResidual D μ r l sample
    ∂parisiFreeMeasure μ a ∂anisotropicMeasureSampleLaw D μ a)=0
  rw [←integral_integral_swap (future_residual_integrable D μ a r)]
  simp_rw [he]
  simp

theorem cavitySignedResponseIntegratedFutureResidual_second_moment_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1) (r : Paper.Overlap) :
    (∫sample,(cavitySignedResponseIntegratedFutureResidual D μ a r sample)^2
      ∂anisotropicMeasureSampleLaw D μ a) ≤ cavitySignedResponseCovarianceMoment D μ a Finset.univ r := by
  let P := anisotropicMeasureSampleLaw D μ a
  let ν := parisiFreeMeasure μ a
  let j := cavitySignedResponseCovarianceMoment D μ a Finset.univ r
  let Y := cavitySignedResponseIntegratedFutureResidual D μ a r
  have hν0 : 0 ≤ ν.real Set.univ := ENNReal.toReal_nonneg
  have hν1 : ν.real Set.univ ≤ 1 := by
    simp only [ν,Measure.real,parisiFreeMeasure_univ,ENNReal.toReal_ofReal (sub_nonneg.mpr ha.2)]
    linarith [ha.1]
  have hj0 : 0 ≤ j := cavitySignedResponseCovarianceMoment_nonneg D μ a _ r
  have hm := measurable_uncurry_cavitySignedResponseFutureResidual D μ r
  have hi2 := future_residual_square_integrable D μ a r
  have hYi : Integrable (fun sample => (Y sample)^2) P := by
    have hY : MemLp Y 2 P := MemLp.of_bound
      (measurable_cavitySignedResponseIntegratedFutureResidual D μ a r).aestronglyMeasurable 2
      (.of_forall (norm_cavitySignedResponseIntegratedFutureResidual_le D μ a ha r))
    exact hY.integrable_sq
  have hp (sample) : (Y sample)^2 ≤ ν.real Set.univ*
      (∫l,(cavitySignedResponseFutureResidual D μ r l sample)^2 ∂ν) := by
    have hF : MemLp (fun l => cavitySignedResponseFutureResidual D μ r l sample) 2 ν :=
      MemLp.of_bound (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable 2
        (.of_forall fun l => norm_cavitySignedResponseFutureResidual_le D μ r l sample)
    exact integral_sq_le_mass_mul_integral_sq _ hF
  have h := integral_mono hYi (hi2.integral_prod_right.const_mul (ν.real Set.univ)) hp
  change (∫sample,(Y sample)^2 ∂P) ≤
    ∫sample,ν.real Set.univ*(∫l,(cavitySignedResponseFutureResidual D μ r l sample)^2 ∂ν) ∂P at h
  rw [integral_const_mul,←integral_integral_swap hi2] at h
  have hlim (l : Paper.Overlap) : (∫sample,(cavitySignedResponseFutureResidual D μ r l sample)^2 ∂P) ≤ j := by
    by_cases hrl : r<l
    · simpa only [cavitySignedResponseFutureResidual,if_pos hrl] using
        cavitySignedResponseMeanResidual_second_moment_le D μ a r l hrl.le
    · simpa only [cavitySignedResponseFutureResidual,if_neg hrl,zero_pow (by decide : 2≠0),integral_zero] using hj0
  have hlimint := integral_mono hi2.integral_prod_left (integrable_const j) hlim
  rw [integral_const,smul_eq_mul] at hlimint
  have hmass : ν.real Set.univ*(ν.real Set.univ*j) ≤ j := by
    calc
      _ ≤ ν.real Set.univ*j := by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hν1 (mul_nonneg hν0 hj0)
      _ ≤ j := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hν1 hj0
  exact h.trans ((mul_le_mul_of_nonneg_left hlimint hν0).trans hmass)

theorem cavitySignedResponseScore_centered (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1) (r : Paper.Overlap) :
    (∫p,cavitySignedResponseScore D μ a r p ∂anisotropicMeasureSpinPathLaw D μ a)=0 := by
  have hx := (memLp_two_cavitySignedResponseTerminalResidual D μ a r).integrable (by norm_num)
  have hy : Integrable (fun p : AnisotropicDisorderBrownianSample n×Configuration n =>
      cavitySignedResponseIntegratedFutureResidual D μ a r p.1) (anisotropicMeasureSpinPathLaw D μ a) :=
    bounded_real_integrable _
      ((measurable_cavitySignedResponseIntegratedFutureResidual D μ a r).comp measurable_fst) 2
      (fun p => norm_cavitySignedResponseIntegratedFutureResidual_le D μ a ha r p.1)
  change (∫p,cavitySignedResponseTerminalResidual D μ r p-
    cavitySignedResponseIntegratedFutureResidual D μ a r p.1 ∂anisotropicMeasureSpinPathLaw D μ a)=0
  rw [integral_sub hx hy,cavitySignedResponseTerminalResidual_centered,
    integral_anisotropicMeasureSpinPathLaw_sample D μ a _
      (measurable_cavitySignedResponseIntegratedFutureResidual D μ a r),
    cavitySignedResponseIntegratedFutureResidual_centered,sub_self]

theorem cavitySignedResponseScore_second_moment_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1) (r : Paper.Overlap) :
    (∫p,(cavitySignedResponseScore D μ a r p)^2 ∂anisotropicMeasureSpinPathLaw D μ a) ≤
      4*cavitySignedResponseCovarianceMoment D μ a Finset.univ r := by
  let P := anisotropicMeasureSpinPathLaw D μ a
  let x := cavitySignedResponseTerminalResidual D μ r
  let y := fun p : AnisotropicDisorderBrownianSample n×Configuration n =>
    cavitySignedResponseIntegratedFutureResidual D μ a r p.1
  have hx : MemLp x 2 P := memLp_two_cavitySignedResponseTerminalResidual D μ a r
  have hy : MemLp y 2 P := MemLp.of_bound
    ((measurable_cavitySignedResponseIntegratedFutureResidual D μ a r).comp measurable_fst).aestronglyMeasurable 2
    (.of_forall fun p => norm_cavitySignedResponseIntegratedFutureResidual_le D μ a ha r p.1)
  have h := integral_mono (hx.sub hy).integrable_sq
    ((hx.integrable_sq.const_mul 2).add (hy.integrable_sq.const_mul 2)) (fun p => by
      change (x p-y p)^2 ≤ 2*(x p)^2+2*(y p)^2
      nlinarith [sq_nonneg (x p+y p)])
  change (∫p,(x p-y p)^2 ∂P) ≤ (∫p,2*(x p)^2+2*(y p)^2 ∂P) at h
  rw [integral_add (hx.integrable_sq.const_mul 2) (hy.integrable_sq.const_mul 2),integral_const_mul,
    integral_const_mul] at h
  have hx2 := cavitySignedResponseTerminalResidual_second_moment D μ a r
  have hy2 := cavitySignedResponseIntegratedFutureResidual_second_moment_le D μ a ha r
  have hym := (measurable_cavitySignedResponseIntegratedFutureResidual D μ a r).pow_const 2
  have he := integral_anisotropicMeasureSpinPathLaw_sample D μ a _ hym
  change (∫p,(y p)^2 ∂P) = _ at he
  change (∫p,(x p)^2 ∂P) = _ at hx2
  rw [he] at h
  rw [hx2] at h
  exact h.trans (by linarith)

end QuantitativeFollowup
