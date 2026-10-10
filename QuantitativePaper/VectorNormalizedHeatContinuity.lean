module
public import QuantitativePaper.VectorHeatJointJets
public import QuantitativePaper.VectorNormalizedHeatPDE

@[expose] public section

/-! Actual joint continuity of the normalized heat gradient, diagonal
Hessian and backward drift, proved from the genuine input heat jets. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
open FourPapersCommon QuantitativeFollowup
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
variable {n : ℕ}

theorem continuous_vectorGaussianHeat {F : Field n → ℝ} (d : VectorHeatDatum F) :
    Continuous (fun p : ℝ×Field n=>vectorGaussianHeat F p.1 p.2) := by
  have hh := (show Continuous (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin 0=>Field n) ℝ=>
    L (fun _=>0)) from by fun_prop).comp (continuous_iteratedFDeriv_vectorGaussianHeat d 0 (by omega))
  simpa only [Function.comp_def,iteratedFDeriv_zero_apply] using hh

theorem fderiv_vectorNormalizedHeat {F H : Field n → ℝ}
    (dF : VectorHeatDatum F) (dH : VectorHeatDatum H) (hH : ∀ x,0 < H x)
    (v : ℝ) (x : Field n) :
    fderiv ℝ (vectorNormalizedHeat F H v) x=
      (vectorGaussianHeat H v x)⁻¹ • fderiv ℝ (vectorGaussianHeat F v) x-
        (vectorGaussianHeat F v x/(vectorGaussianHeat H v x)^2) •
          fderiv ℝ (vectorGaussianHeat H v) x := by
  ext w
  rw [show vectorNormalizedHeat F H v=(fun y=>vectorGaussianHeat F v y/vectorGaussianHeat H v y) from rfl,
    fderiv_vectorQuotient_apply (vectorGaussianHeat F v) (vectorGaussianHeat H v)
      (contDiff_vectorGaussianHeat_spatial dF v) (contDiff_vectorGaussianHeat_spatial dH v)
      (fun y=>(vectorGaussianHeat_pos dH hH v y).ne') x w]
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,vectorQuotientFirst]
  field_simp [(vectorGaussianHeat_pos dH hH v x).ne'] <;> ring

theorem continuous_fderiv_vectorNormalizedHeat {F H : Field n → ℝ}
    (dF : VectorHeatDatum F) (dH : VectorHeatDatum H) (hH : ∀ x,0 < H x) :
    Continuous (fun p : ℝ×Field n=>fderiv ℝ (vectorNormalizedHeat F H p.1) p.2) := by
  simp_rw [fderiv_vectorNormalizedHeat dF dH hH]
  have hn (p : ℝ×Field n) : vectorGaussianHeat H p.1 p.2≠0 := (vectorGaussianHeat_pos dH hH _ _).ne'
  exact (((continuous_vectorGaussianHeat dH).inv₀ hn).smul (continuous_fderiv_vectorGaussianHeat dF)).sub
    (((continuous_vectorGaussianHeat dF).div ((continuous_vectorGaussianHeat dH).pow 2)
      (fun p=>pow_ne_zero 2 (hn p))).smul (continuous_fderiv_vectorGaussianHeat dH))

theorem continuous_vectorNormalizedHeat_hessian_diagonal {F H : Field n → ℝ}
    (dF : VectorHeatDatum F) (dH : VectorHeatDatum H) (hH : ∀ x,0 < H x)
    (w : Field n) :
    Continuous (fun p : ℝ×Field n=>vectorHessian (vectorNormalizedHeat F H p.1) p.2 w w) := by
  have hn (p : ℝ×Field n) : vectorGaussianHeat H p.1 p.2≠0 := (vectorGaussianHeat_pos dH hH _ _).ne'
  have hF := continuous_vectorGaussianHeat dF
  have hG := continuous_vectorGaussianHeat dH
  have hDf := (continuous_fderiv_vectorGaussianHeat dF).clm_apply (continuous_const (y := w))
  have hDg := (continuous_fderiv_vectorGaussianHeat dH).clm_apply (continuous_const (y := w))
  have hHf := ((continuous_vectorHessian_vectorGaussianHeat dF).clm_apply
    (continuous_const (y := w))).clm_apply (continuous_const (y := w))
  have hHg := ((continuous_vectorHessian_vectorGaussianHeat dH).clm_apply
    (continuous_const (y := w))).clm_apply (continuous_const (y := w))
  have he : (fun p : ℝ×Field n=>vectorHessian (vectorNormalizedHeat F H p.1) p.2 w w)=
      (fun p=>vectorQuotientSecond (vectorGaussianHeat F p.1) (vectorGaussianHeat H p.1) p.2 w) := by
    funext p
    exact vectorHessian_vectorQuotient_apply _ _ (contDiff_vectorGaussianHeat_spatial dF _)
      (contDiff_vectorGaussianHeat_spatial dH _) (fun x=>(vectorGaussianHeat_pos dH hH _ x).ne') _ w
  rw [he]
  unfold vectorQuotientSecond
  exact (((hHf.div hG hn).sub (((continuous_const.mul hDf).mul hDg).div
    (hG.pow 2) (fun p=>pow_ne_zero 2 (hn p)))).sub ((hF.mul hHg).div
      (hG.pow 2) (fun p=>pow_ne_zero 2 (hn p)))).add
        (((continuous_const.mul hF).mul (hDg.pow 2)).div (hG.pow 3) (fun p=>pow_ne_zero 3 (hn p)))

theorem continuous_vectorNormalizedHeat_trace {F H : Field n → ℝ}
    (dF : VectorHeatDatum F) (dH : VectorHeatDatum H) (hH : ∀ x,0 < H x) :
    Continuous (fun p : ℝ×Field n=>vectorBilinearTrace (vectorHessian (vectorNormalizedHeat F H p.1) p.2)) := by
  exact continuous_finsetSum _ (fun i _=>continuous_vectorNormalizedHeat_hessian_diagonal dF dH hH
    (EuclideanSpace.single i 1))

theorem continuous_vectorHeatLogGradient {H : Field n → ℝ}
    (dH : VectorHeatDatum H) (hH : ∀ x,0 < H x) :
    Continuous (fun p : ℝ×Field n=>vectorHeatLogGradient H p.1 p.2) := by
  have hg := (InnerProductSpace.toDual ℝ (Field n)).symm.continuous.comp
    (continuous_fderiv_vectorGaussianHeat dH)
  exact ((continuous_vectorGaussianHeat dH).inv₀
    (fun p=>(vectorGaussianHeat_pos dH hH _ _).ne')).smul hg

end QuantitativePaper
