module
public import QuantitativeFollowup.SupportingPrintedScalarObservedPast
public import QuantitativeFollowup.ScalarReferenceMultiplier
public import FRSB.MStochasticL2

@[expose] public section

/-! The literal variance parameter d of the scalar diffusion.  The actual
native inverse temperature is sqrt(d), so its Brownian coefficient is
sqrt(d) and its curvature-square multiplier is exactly d.  All measures
are arbitrary genuine Parisi measures, with atoms retained. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FRSB QuantitativeFollowup
open scoped Topology NNReal
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def scalarVarianceGamma (d : ℝ) (μ : Paper.ParisiMeasure) : ℝ→ℝ :=
  FRSB.Gamma (Real.sqrt d) μ

def scalarVarianceK (d : ℝ) (μ : Paper.ParisiMeasure) (q : ℝ) : ℝ :=
  d*FRSB.curvatureMoment2 (Real.sqrt d) μ q

theorem scalarVarianceK_eq_GammaPrime (d : ℝ) (hd : 0<d)
    (μ : Paper.ParisiMeasure) (q : ℝ) :
    scalarVarianceK d μ q=FRSB.GammaPrime (Real.sqrt d) μ q := by
  simp only [scalarVarianceK,FRSB.GammaPrime,Real.sq_sqrt hd.le]

theorem scalar_variance_magnetization_observed_condExp (d : ℝ) (hd : 0<d)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) :
    (scalarMarkedSpinLaw (Real.sqrt d) (Real.sqrt_pos.mpr hd).ne' μ)[
      (fun z=>Paper.spinSign z.2) | scalarObservedPast (Real.sqrt d) μ q] =ᵐ[
        scalarMarkedSpinLaw (Real.sqrt d) (Real.sqrt_pos.mpr hd).ne' μ]
      fun z=>FRSB.M (Real.sqrt d) μ q z.1 :=
  scalarMarkedSpinLaw_sign_condExp_observed (Real.sqrt d) (Real.sqrt_pos.mpr hd).ne' μ q

theorem scalar_variance_magnetization_initial (d : ℝ) (hd : 0<d)
    (μ : Paper.ParisiMeasure) (ω : Paper.BrownianSample) :
    FRSB.M (Real.sqrt d) μ 0 ω=0 := by
  have he := stoppedMagnetization_eq_physical (Real.sqrt d) (Real.sqrt_pos.mpr hd).ne'
    μ (t:=0) (by norm_num) ω
  exact he.symm.trans (stoppedMagnetization_initial (Real.sqrt d)
    (Real.sqrt_pos.mpr hd).ne' μ ω)

theorem scalar_variance_brownian_coefficient (d : ℝ) (t : ℝ≥0)
    (ω : Paper.BrownianSample) :
    canonicalDiracShiftMartingale (Real.sqrt d) 0 t ω=
      Real.sqrt d*Paper.canonicalBrownian t ω := by
  simp only [canonicalDiracShiftMartingale,zero_add,canonicalBrownian_zero,sub_zero]

theorem scalar_variance_magnetization_stochastic_identity (d : ℝ) (hd : 0<d)
    (μ : Paper.ParisiMeasure) (T : ℝ≥0) (hT : T≤1) :
    TendstoInMeasure Paper.canonicalBrownianMeasure
      (FRSB.optimalMLeftSum (Real.sqrt d) (Real.sqrt_pos.mpr hd).ne' μ T) atTop
      (FRSB.M (Real.sqrt d) μ T) :=
  FRSB.optimalM_stochastic_identity (Real.sqrt d) (Real.sqrt_pos.mpr hd).ne' μ T hT

theorem scalar_variance_Gamma_hasDerivWithinAt (d : ℝ) (hd : 0<d)
    (μ : Paper.ParisiMeasure) (q : ℝ) (hq : q∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (scalarVarianceGamma d μ) (scalarVarianceK d μ q)
      (Icc (0:ℝ) 1) q := by
  rw [scalarVarianceK_eq_GammaPrime d hd μ q]
  exact FRSB.hasDerivWithinAt_Gamma_GammaPrime (Real.sqrt d) (Real.sqrt_pos.mpr hd).ne' μ hq

theorem scalar_variance_Gamma_hasDerivAt (d : ℝ) (hd : 0<d)
    (μ : Paper.ParisiMeasure) (q : ℝ) (hq : q∈Ioo (0:ℝ) 1) :
    HasDerivAt (scalarVarianceGamma d μ) (scalarVarianceK d μ q) q := by
  rw [scalarVarianceK_eq_GammaPrime d hd μ q]
  exact FRSB.hasDerivAt_Gamma_GammaPrime (Real.sqrt d) (Real.sqrt_pos.mpr hd).ne' μ hq

theorem scalar_variance_after_support_decay (d : ℝ) (hd : 0<d)
    (μ : Paper.ParisiMeasure) (q : ℝ) (hq : q∈Ioc (0:ℝ) 1)
    (hsupp : parisiSupport μ=Icc (0:ℝ) q) (t : ℝ) (ht : t∈Icc q 1) :
    scalarVarianceK d μ t≤Real.exp (-d*(t-q)/2)*scalarVarianceK d μ q := by
  simp_rw [scalarVarianceK_eq_GammaPrime d hd μ]
  simpa only [Real.sq_sqrt hd.le] using
    scalarGammaPrime_after_support_decay (Real.sqrt d) (Real.sqrt_pos.mpr hd) μ q hq hsupp t ht

theorem scalar_variance_minimizer_after_support_decay_exact (d : ℝ) (hd : 0<d)
    (μ : Paper.ParisiMeasure) (hmin : IsParisiMinimizer (Real.sqrt d) 0 μ)
    (q : ℝ) (hq : q∈Ioc (0:ℝ) 1) (hsupp : parisiSupport μ=Icc (0:ℝ) q)
    (t : ℝ) (ht : t∈Icc q 1) :
    scalarVarianceK d μ q=1 ∧
      scalarVarianceK d μ t≤Real.exp (-d*(t-q)/2)*scalarVarianceK d μ q ∧
      Real.exp (-d*(t-q)/2)*scalarVarianceK d μ q=Real.exp (-d*(t-q)/2) := by
  have hu : scalarVarianceK d μ q=1 := by
    rw [scalarVarianceK_eq_GammaPrime d hd μ q]
    exact GammaPrime_eq_one_on_support_interval (Real.sqrt d) (Real.sqrt_pos.mpr hd).ne'
      μ hmin q hq.1 hq.2 hsupp q ⟨hq.1.le,le_rfl⟩
  exact ⟨hu,scalar_variance_after_support_decay d hd μ q hq hsupp t ht,by rw [hu,mul_one]⟩

end HexagonPaper
