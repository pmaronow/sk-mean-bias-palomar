module
public import QuantitativePaper.VectorFiniteCellSampleTest
public import QuantitativePaper.VectorHeatSpatial
public import Mathlib

@[expose] public section

/-! Actual joint jets of compact smooth time/disorder/field tests. Global
bounds follow from compact support; spatial slices are restrictions to a
fixed linear isometric direction. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

abbrev VectorCompactTestParameter (n : ℕ) := ℝ × ((Couplings n × ℝ) × Field n)

def vectorCompactSmoothSpatialInclusion (n : ℕ) : Field n →L[ℝ] VectorCompactTestParameter n :=
  (ContinuousLinearMap.inr ℝ ℝ ((Couplings n × ℝ) × Field n)).comp
    (ContinuousLinearMap.inr ℝ (Couplings n × ℝ) (Field n))

theorem norm_vectorCompactSmoothSpatialInclusion_le (n : ℕ) :
    ‖vectorCompactSmoothSpatialInclusion n‖ ≤ 1 := by
  exact ((ContinuousLinearMap.inr ℝ ℝ ((Couplings n × ℝ) × Field n)).opNorm_comp_le
    (ContinuousLinearMap.inr ℝ (Couplings n × ℝ) (Field n))).trans
    (by grw [ContinuousLinearMap.norm_inr_le_one,ContinuousLinearMap.norm_inr_le_one]; norm_num)

def vectorCompactSmoothTimeField (f : VectorCompactTestParameter n → ℝ)
    (z : VectorCompactTestParameter n) : ℝ := fderiv ℝ f z (1,(0,0))

theorem contDiff_vectorCompactSmoothTimeField {f : VectorCompactTestParameter n → ℝ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (vectorCompactSmoothTimeField f) := by
  exact (contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const

theorem hasCompactSupport_vectorCompactSmoothTimeField {f : VectorCompactTestParameter n → ℝ}
    (hs : HasCompactSupport f) : HasCompactSupport (vectorCompactSmoothTimeField f) :=
  hs.fderiv_apply ℝ (1,(0,0))

theorem hasDerivAt_vectorCompactSmooth_time {f : VectorCompactTestParameter n → ℝ}
    (hf : ContDiff ℝ ∞ f) (r : ℝ) (p : Couplings n×ℝ) (x : Field n) :
    HasDerivAt (fun q => f (q,(p,x))) (vectorCompactSmoothTimeField f (r,(p,x))) r := by
  exact (hf.differentiable (by simp) (r,(p,x))).hasFDerivAt.comp_hasDerivAt r
    ((hasDerivAt_id r).prodMk (hasDerivAt_const r (p,x)))

theorem fderiv_vectorCompactSmooth_section {f : VectorCompactTestParameter n → ℝ}
    (hf : ContDiff ℝ ∞ f) (r : ℝ) (p : Couplings n×ℝ) (x : Field n) :
    fderiv ℝ (fun y => f (r,(p,y))) x =
      (fderiv ℝ f (r,(p,x))).comp (vectorCompactSmoothSpatialInclusion n) := by
  have hmap : HasFDerivAt (fun y : Field n => (r,(p,y)))
      (vectorCompactSmoothSpatialInclusion n) x := by
    convert (hasFDerivAt_const (r,(p,0)) x).add
      (vectorCompactSmoothSpatialInclusion n).hasFDerivAt using 1 <;>
      simp [vectorCompactSmoothSpatialInclusion]
    funext y
    simp
  exact ((hf.differentiable (by simp) _).hasFDerivAt.comp x hmap).fderiv

theorem iteratedFDeriv_vectorCompactSmooth_section {f : VectorCompactTestParameter n → ℝ}
    (hf : ContDiff ℝ ∞ f) (r : ℝ) (p : Couplings n×ℝ) (x : Field n) (j : ℕ) :
    iteratedFDeriv ℝ j (fun y => f (r,(p,y))) x =
      (iteratedFDeriv ℝ j f (r,(p,x))).compContinuousLinearMap
        (fun _ => vectorCompactSmoothSpatialInclusion n) := by
  let A : VectorCompactTestParameter n := (r,(p,0))
  have hshift : ContDiff ℝ ∞ (fun z : VectorCompactTestParameter n => f (A+z)) :=
    hf.comp (contDiff_const.add contDiff_id)
  have H := (vectorCompactSmoothSpatialInclusion n).iteratedFDeriv_comp_right
    hshift x (i := j) (by exact_mod_cast le_top)
  simpa [Function.comp_def,vectorCompactSmoothSpatialInclusion,A,
    iteratedFDeriv_comp_add_left] using H

theorem continuous_iteratedFDeriv_vectorCompactSmooth_section {f : VectorCompactTestParameter n → ℝ}
    (hf : ContDiff ℝ ∞ f) (j : ℕ) :
    Continuous (fun z : VectorCompactTestParameter n =>
      iteratedFDeriv ℝ j (fun y => f (z.1,(z.2.1,y))) z.2.2) := by
  have H := (ContinuousMultilinearMap.continuous_precomp
    (fun _ : Fin j => vectorCompactSmoothSpatialInclusion n)).comp
      (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top : (j : ℕ∞ω) ≤ ∞))
  exact H.congr (fun z => (iteratedFDeriv_vectorCompactSmooth_section hf z.1 z.2.1 z.2.2 j).symm)

theorem norm_iteratedFDeriv_vectorCompactSmooth_section_le {f : VectorCompactTestParameter n → ℝ}
    (hf : ContDiff ℝ ∞ f) (r : ℝ) (p : Couplings n×ℝ) (x : Field n) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y => f (r,(p,y))) x‖ ≤ ‖iteratedFDeriv ℝ j f (r,(p,x))‖ := by
  rw [iteratedFDeriv_vectorCompactSmooth_section hf]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hprod : (∏ _ : Fin j,‖vectorCompactSmoothSpatialInclusion n‖) ≤ 1 := by
    simpa only [Finset.prod_const_one] using
      (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun _ _ => norm_vectorCompactSmoothSpatialInclusion_le n))
  exact (mul_le_mul_of_nonneg_left hprod (norm_nonneg _)).trans_eq (mul_one _)

theorem continuous_fderiv_vectorCompactSmooth_section {f : VectorCompactTestParameter n → ℝ}
    (hf : ContDiff ℝ ∞ f) : Continuous (fun z : VectorCompactTestParameter n =>
      fderiv ℝ (fun y => f (z.1,(z.2.1,y))) z.2.2) := by
  have hd := hf.continuous_fderiv (by simp)
  have H : Continuous (fun z : VectorCompactTestParameter n =>
      (fderiv ℝ f z).comp (vectorCompactSmoothSpatialInclusion n)) := by fun_prop
  exact H.congr (fun z => (fderiv_vectorCompactSmooth_section hf z.1 z.2.1 z.2.2).symm)

theorem continuous_vectorHessian_vectorCompactSmooth_section {f : VectorCompactTestParameter n → ℝ}
    (hf : ContDiff ℝ ∞ f) : Continuous (fun z : VectorCompactTestParameter n =>
      vectorHessian (fun y => f (z.1,(z.2.1,y))) z.2.2) := by
  have H := (vectorBilinearOfTwoCLM n).continuous.comp
    (continuous_iteratedFDeriv_vectorCompactSmooth_section hf 2)
  exact H.congr (fun z => (vectorHessian_eq_bilinearOfTwo _ _).symm)


end QuantitativePaper
