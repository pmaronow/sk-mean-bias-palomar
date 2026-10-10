module
public import QuantitativeFollowup.StandardSKAnisotropicLaw
public import QuantitativePaper.VectorMeasureSpatialSmooth
public import FourPapersCommon.AffineMixedLineDerivative

@[expose] public section

/-! Exact field-Hessian conjugation under the actual SK disorder compression. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open QuantitativePaper FourPapersCommon
set_option maxHeartbeats 1600000
variable {n : ℕ}

theorem standardSKAnisotropicFieldHessian (μ : Paper.ParisiMeasure) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) (ω : AnisotropicDisorder n)
    (x w : Field n) :
    fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential (standardSKAnisotropicModel n β t hβ ht) μ q))
      (anisotropicParameterPoint ω x) (anisotropicFieldInjection n w) (anisotropicFieldInjection n w)=
      inner ℝ (vectorMeasureHessian μ β t q (standardSKDisorderCompression ω) x w) w := by
  let D:=standardSKAnisotropicModel n β t hβ ht
  have hA : ContDiff ℝ 2 (anisotropicMeasureTailPotential D μ q) :=
    (anisotropicMeasureTailPotential_hessian_limit D μ q).2
  have h1:=hasDerivAt_fderiv_affine_line_direction (anisotropicMeasureTailPotential D μ q) hA
    (anisotropicParameterPoint ω x) (anisotropicFieldInjection n w) (anisotropicFieldInjection n w) 0
  have he (r : ℝ) : anisotropicParameterPoint ω x+r • anisotropicFieldInjection n w=
      anisotropicParameterPoint ω (x+r • w) := by
    ext e;cases e <;> simp [anisotropicParameterPoint,anisotropicFieldInjection]
  have hfun : (fun r : ℝ=>fderiv ℝ (anisotropicMeasureTailPotential D μ q)
      (anisotropicParameterPoint ω x+r • anisotropicFieldInjection n w) (anisotropicFieldInjection n w))=
      fun r : ℝ=>inner ℝ (vectorMeasureGradient μ β t q (standardSKDisorderCompression ω) (x+r • w)) w := by
    funext r
    rw [he,fderiv_anisotropicMeasureTailPotential_field,standardSKAnisotropicMeasureMagnetization]
  rw [hfun] at h1
  have hl : HasDerivAt (fun r : ℝ=>x+r • w) w 0 := by
    convert (hasDerivAt_const (0:ℝ) x).add ((hasDerivAt_id (0:ℝ)).smul_const w) using 1
    · rfl
    · simp only [one_smul,zero_add]
  have hG : HasFDerivAt (vectorMeasureGradient μ β t q (standardSKDisorderCompression ω))
      (vectorMeasureHessian μ β t q (standardSKDisorderCompression ω) x) (x+(0:ℝ) • w) := by
    simpa only [zero_smul,add_zero] using
      hasFDerivAt_vectorMeasureGradient μ β t ht.le q (standardSKDisorderCompression ω) x
  have h2 := (hG.comp_hasDerivAt (0:ℝ) hl).inner ℝ (hasDerivAt_const (0:ℝ) w)
  simpa only [zero_smul,add_zero,zero_add,D,inner_zero_right] using h1.unique h2

end QuantitativeFollowup
