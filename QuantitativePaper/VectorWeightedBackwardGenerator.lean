module
public import QuantitativePaper.VectorNormalizedHeatPDE
public import QuantitativePaper.VectorResponseContinuity

@[expose] public section

/-! The actual backward equation of a bounded weighted Gaussian response.
Its drift is the gradient of the same genuine Cole--Hopf potential, including
the zero-mass branch. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
open FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 1000000
variable {n : ℕ}

theorem vectorNormalizedHeat_exp_eq_stepResponse (f g : Field n → ℝ) (v m : ℝ) :
    vectorNormalizedHeat (fun x=>Real.exp (m*f x)*g x)
      (fun x=>Real.exp (m*f x)) v=vectorStepResponse v m f g := by
  funext x
  unfold vectorNormalizedHeat vectorGaussianHeat vectorStepResponse vectorStepWeight vectorStepPartition
  have he : (fun z=>Real.exp (m*f (fieldShift v x z)) /
      (∫ w,Real.exp (m*f (fieldShift v x w)) ∂fieldGaussian n)*g (fieldShift v x z))=
      (fun z=>(Real.exp (m*f (fieldShift v x z))*g (fieldShift v x z))/
        (∫ w,Real.exp (m*f (fieldShift v x w)) ∂fieldGaussian n)) := by
    funext z
    ring
  rw [he,integral_div]

theorem vectorHeatLogGradient_exp (f : Field n → ℝ) (m : ℝ)
    (dH : VectorHeatDatum (fun x=>Real.exp (m*f x))) (v : ℝ) (x : Field n) :
    vectorHeatLogGradient (fun y=>Real.exp (m*f y)) v x=
      m • gradient (vectorColeHopfStep v m f) x := by
  by_cases hm : m=0
  · subst m
    have he : vectorGaussianHeat (fun _ : Field n=>(1 : ℝ)) v=fun _=>1 := by
      funext y
      simp [vectorGaussianHeat]
    ext i
    simp [vectorHeatLogGradient,SYK.gradient_coord_eq,he]
  · let H : Field n → ℝ := vectorGaussianHeat (fun y=>Real.exp (m*f y)) v
    have hH : ContDiff ℝ 2 H := contDiff_vectorGaussianHeat_spatial dH v
    have hpos (y : Field n) : 0 < H y := vectorGaussianHeat_pos dH (fun z=>Real.exp_pos _) v y
    have he : vectorColeHopfStep v m f=fun y=>Real.log (H y)/m := by
      funext y
      simp only [vectorColeHopfStep,ite_eq_right hm,H,vectorGaussianHeat,vectorStepPartition]
    have hC : ContDiff ℝ 2 (vectorColeHopfStep v m f) := by
      rw [he]
      exact (hH.log (fun y=>(hpos y).ne')).div_const m
    ext i
    let e : Field n := EuclideanSpace.single i 1
    have hd := ((hasDerivAt_on_affine_line H hH x e 0).log
      (by simpa only [zero_smul,add_zero] using (hpos x).ne')).div_const m
    have hCH := hasDerivAt_on_affine_line (vectorColeHopfStep v m f) hC x e 0
    rw [he] at hCH
    have hh := hCH.unique hd
    simp only [zero_smul,add_zero] at hh
    change fderiv ℝ (fun y=>Real.log (H y)/m) x e=_ at hh
    simp only [vectorHeatLogGradient,PiLp.smul_apply,smul_eq_mul,SYK.gradient_coord_eq,he]
    change (H x)⁻¹*fderiv ℝ H x e=m*fderiv ℝ (fun y=>Real.log (H y)/m) x e
    rw [hh]
    field_simp [hm,(hpos x).ne']

theorem hasDerivAt_vectorStepResponse_variance (f g : Field n → ℝ) (m : ℝ)
    (dF : VectorHeatDatum (fun x=>Real.exp (m*f x)*g x))
    (dH : VectorHeatDatum (fun x=>Real.exp (m*f x)))
    {v : ℝ} (hv : 0 < v) (x : Field n) :
    HasDerivAt (fun u=>vectorStepResponse u m f g x)
      (vectorBilinearTrace (vectorHessian (vectorStepResponse v m f g) x)/2+
        fderiv ℝ (vectorStepResponse v m f g) x
          (m • gradient (vectorColeHopfStep v m f) x)) v := by
  have hd := hasDerivAt_vectorNormalizedHeat_variance dF dH (fun y=>Real.exp_pos _) hv x
  simp only [vectorNormalizedHeat_exp_eq_stepResponse f g,
    vectorHeatLogGradient_exp f m dH] at hd
  exact hd

end QuantitativePaper
