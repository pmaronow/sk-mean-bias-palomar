module
public import QuantitativePaper.VectorQuotientCalculus
public import QuantitativePaper.GaussianWeightedRatioJets

@[expose] public section

/-! The backward generator of genuine normalized Gaussian heat averages.
The variance derivative is calculated from the actual heat equation and the
spatial quotient identities. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal BigOperators
namespace QuantitativePaper
open FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 1000000
variable {n : ℕ}

def vectorNormalizedHeat (F H : Field n → ℝ) (v : ℝ) (x : Field n) : ℝ :=
  vectorGaussianHeat F v x/vectorGaussianHeat H v x

def vectorHeatLogGradient (H : Field n → ℝ) (v : ℝ) (x : Field n) : Field n :=
  (vectorGaussianHeat H v x)⁻¹ • gradient (vectorGaussianHeat H v) x

theorem vectorGaussianHeat_pos {H : Field n → ℝ} (d : VectorHeatDatum H)
    (hH : ∀ x,0 < H x) (v : ℝ) (x : Field n) :
    0 < vectorGaussianHeat H v x := by
  apply (integral_pos_iff_support_of_nonneg (fun z=>(hH _).le)
    (d.integrable_shift v x)).mpr
  have he : Function.support (fun z=>H (fieldShift v x z))=univ := by
    ext z
    simp only [Function.mem_support,mem_univ,iff_true]
    exact (hH _).ne'
  rw [he]
  simp

theorem contDiff_vectorNormalizedHeat_spatial {F H : Field n → ℝ}
    (dF : VectorHeatDatum F) (dH : VectorHeatDatum H) (hH : ∀ x,0 < H x)
    (v : ℝ) : ContDiff ℝ 2 (vectorNormalizedHeat F H v) :=
  (contDiff_vectorGaussianHeat_spatial dF v).div
    (contDiff_vectorGaussianHeat_spatial dH v)
    (fun x=>(vectorGaussianHeat_pos dH hH v x).ne')

theorem hasDerivAt_vectorNormalizedHeat_variance {F H : Field n → ℝ}
    (dF : VectorHeatDatum F) (dH : VectorHeatDatum H) (hH : ∀ x,0 < H x)
    {v : ℝ} (hv : 0 < v) (x : Field n) :
    HasDerivAt (fun u=>vectorNormalizedHeat F H u x)
      (vectorBilinearTrace (vectorHessian (vectorNormalizedHeat F H v) x)/2+
        fderiv ℝ (vectorNormalizedHeat F H v) x (vectorHeatLogGradient H v x)) v := by
  have hd := (hasDerivAt_vectorGaussianHeat_variance dF hv x).div
    (hasDerivAt_vectorGaussianHeat_variance dH hv x)
    (vectorGaussianHeat_pos dH hH v x).ne'
  apply hd.congr_deriv
  change _ = vectorBilinearTrace (vectorHessian (fun y=>vectorGaussianHeat F v y/vectorGaussianHeat H v y) x)/2+
    fderiv ℝ (fun y=>vectorGaussianHeat F v y/vectorGaussianHeat H v y) x
      ((vectorGaussianHeat H v x)⁻¹ • gradient (vectorGaussianHeat H v) x)
  rw [vector_quotient_generator
    (vectorGaussianHeat F v) (vectorGaussianHeat H v)
    (contDiff_vectorGaussianHeat_spatial dF v) (contDiff_vectorGaussianHeat_spatial dH v)
    (fun y=>(vectorGaussianHeat_pos dH hH v y).ne') x]
  field_simp [(vectorGaussianHeat_pos dH hH v x).ne'] <;> ring

theorem vectorNormalizedHeat_exp_eq_weightedRatio (f g : Field n → ℝ)
    (v m : ℝ) :
    vectorNormalizedHeat (fun x=>Real.exp (m*f x)*g x)
      (fun x=>Real.exp (m*f x)) v=
      gaussianWeightedShiftRatio (Real.sqrt v • ContinuousLinearMap.id ℝ (Field n)) m f g := by
  funext x
  simp only [vectorNormalizedHeat,vectorGaussianHeat,gaussianWeightedShiftRatio,
    gaussianWeightedShiftMoment,gaussianShiftPartition,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply,fieldShift]

end QuantitativePaper
