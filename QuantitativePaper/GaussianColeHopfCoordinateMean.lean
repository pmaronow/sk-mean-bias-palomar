module
public import QuantitativePaper.GaussianColeHopfCoordinateLog
public import QuantitativePaper.SmoothGaussianStep
public import Mathlib.Probability.Moments.MGFAnalytic

@[expose] public section

/-! The genuine zero-mass derivative of the Gaussian log partition is the
actual Gaussian average. Exponential integrability is derived from the input
shift bound and Gaussian Fernique integrability. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff
namespace QuantitativePaper
set_option maxHeartbeats 1400000
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem gaussianMassLog_eq_cgf {n : ℕ} (A : Field n →L[ℝ] E) (f : E → ℝ) (x : E) :
    (fun s => gaussianMassLog A f (s,x)) =
      cgf (fun z => f (x+A z)) (fieldGaussian n) := by
  funext s
  simp only [gaussianMassLog,gaussianShiftPartition,gaussianMassShift,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply,one_mul,cgf,mgf,
    Prod.fst_add,Prod.snd_add,add_zero]

 theorem gaussian_mass_integrableExpSet {n : ℕ} (A : Field n →L[ℝ] E)
    (f : E → ℝ) (U : Set E) (hf : ContinuousOn f U)
    (hshift : ∀ x∈U, ∀ z, x+A z∈U) (H : ℝ)
    (hlip : ∀ x∈U, ∀ z, |f (x+A z)-f x|  ≤  H*‖z‖)
    (x : E) (hx : x∈U) :
    integrableExpSet (fun z => f (x+A z)) (fieldGaussian n) = univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro s
  have hmap : Continuous (fun z => x+A z) := continuous_const.add A.continuous
  have hfx : Continuous (fun z => f (x+A z)) := continuousOn_univ.mp
    (hf.comp hmap.continuousOn (fun z _ => hshift x hx z))
  have he : Integrable (fun z : Field n => Real.exp (|s| * |f x|)*Real.exp ((|s| * |H|)*‖z‖))
      (fieldGaussian n) := (SYK.integrable_exp_mul_norm (ι:=Fin n) (|s| * |H|)).const_mul _
  apply he.mono' (hfx.const_mul s |>.rexp |>.aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hfs : |f (x+A z)|  ≤  |f x|+|H| * ‖z‖ := by
    have ht : |f (x+A z)|  ≤  |f x|+|f (x+A z)-f x| := by
      simpa only [add_sub_cancel] using abs_add_le (f x) (f (x+A z)-f x)
    exact ht.trans (add_le_add_right ((hlip x hx z).trans
      (mul_le_mul_of_nonneg_right (le_abs_self H) (norm_nonneg _))) _)
  have hb := mul_le_mul_of_nonneg_left hfs (abs_nonneg s)
  exact (le_abs_self (s*f (x+A z))).trans (by simpa only [abs_mul,mul_add,mul_assoc] using hb)

theorem hasDerivAt_gaussianMassLog_mass_zero {n : ℕ} (A : Field n →L[ℝ] E)
    (f : E → ℝ) (U : Set E) (hf : ContinuousOn f U)
    (hshift : ∀ x∈U, ∀ z, x+A z∈U) (H : ℝ)
    (hlip : ∀ x∈U, ∀ z, |f (x+A z)-f x|  ≤  H*‖z‖)
    (x : E) (hx : x∈U) :
    HasDerivAt (fun s => gaussianMassLog A f (s,x)) (gaussianShiftAverage A f x) 0 := by
  have hm : (0:ℝ)∈interior (integrableExpSet (fun z => f (x+A z)) (fieldGaussian n)) := by
    rw [gaussian_mass_integrableExpSet A f U hf hshift H hlip x hx,interior_univ]
    trivial
  rw [gaussianMassLog_eq_cgf]
  have ha := (analyticAt_cgf hm).differentiableAt.hasDerivAt
  have hp : (fieldGaussian n).real univ = 1 := by simp [Measure.real]
  simpa only [deriv_cgf_zero hm,hp,div_one,gaussianShiftAverage] using ha

theorem coordinateDerivative_gaussianMassLog_zero {n : ℕ} (A : Field n →L[ℝ] E)
    (f : E → ℝ) (U : Set E) (hf : ContinuousOn f U)
    (hshift : ∀ x∈U, ∀ z, x+A z∈U) (H : ℝ)
    (hlip : ∀ x∈U, ∀ z, |f (x+A z)-f x|  ≤  H*‖z‖)
    (x : E) (hx : x∈U) (hd : DifferentiableAt ℝ (gaussianMassLog A f) (0,x)) :
    coordinateDerivative (gaussianMassLog A f) (0,x) = gaussianShiftAverage A f x := by
  have hc := hd.hasFDerivAt.comp_hasDerivAt (0:ℝ)
    ((hasDerivAt_id (0:ℝ)).prodMk (hasDerivAt_const (0:ℝ) x))
  exact hc.unique (hasDerivAt_gaussianMassLog_mass_zero A f U hf hshift H hlip x hx)

end QuantitativePaper
