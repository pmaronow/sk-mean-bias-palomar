module
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeMeanSquare

@[expose] public section

/-! Global native field moduli inherited from actual finite posterior
values and their genuine locally uniform differential limits. The bounds
are independent of the profile and both observation nodes. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators NNReal Topology ContDiff
namespace QuantitativeFollowup
variable {n : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000

theorem anisotropicRestartSpinSquare_field_lipschitz (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q r : Paper.Overlap)
    (hqr : q ≤ r) (i : Fin n) :
    LipschitzWith (4*‖cavityCoordinateFeature i‖₊^2*‖anisotropicRestartFieldEnergyMap D‖₊)
      (fun x => anisotropicRestartSpinSquare D μ g q x i r) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply le_of_tendsto ((tendsto_anisotropicDyadicRestartPosteriorSquare D μ g q r hqr i x).dist
    (tendsto_anisotropicDyadicRestartPosteriorSquare D μ g q r hqr i y))
  exact .of_forall fun j => (anisotropicFiniteRestartPosteriorSquare_lipschitz D
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) g q (vectorDyadicTimeIndex r j) i).dist_le_mul x y

theorem anisotropicRestartSpinSquare_field_differential_lipschitz (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q r : Paper.Overlap)
    (hqr : q ≤ r) (i : Fin n) :
    LipschitzWith (31*‖cavityCoordinateFeature i‖₊^2*‖anisotropicRestartFieldEnergyMap D‖₊^2)
      (fderiv ℝ (fun x => anisotropicRestartSpinSquare D μ g q x i r)) := by
  have hu := (anisotropicRestartSpinSquare_field_derivative_limit D μ g q r hqr i).1
  have hp := tendstoLocallyUniformlyOn_univ.mpr hu
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply le_of_tendsto ((hp.tendsto_at (mem_univ x)).dist (hp.tendsto_at (mem_univ y)))
  exact .of_forall fun j => (anisotropicFiniteRestartPosteriorSquare_differential_lipschitz D
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) g q (vectorDyadicTimeIndex r j) i).dist_le_mul x y

private theorem nativeRestartLipschitz_sum {I E F : Type*} [Fintype I]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    (f : I → E → F) (K : I → ℝ≥0) (h : ∀ i, LipschitzWith (K i) (f i)) :
    LipschitzWith (∑ i, K i) (fun x => ∑ i, f i x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, ←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖f i x-f i y‖ := norm_sum_le _ _
    _ ≤ ∑ i, (K i : ℝ)*dist x y := Finset.sum_le_sum fun i _ => by
      simpa only [dist_eq_norm] using (h i).dist_le_mul x y
    _ = _ := by simp only [NNReal.coe_sum, Finset.sum_mul]

def anisotropicRestartMeanSquareFieldLipschitzBound (D : AnisotropicSpinModel n) : ℝ≥0 :=
  ‖(n : ℝ)⁻¹‖₊ * ∑ i : Fin n,
    4*‖cavityCoordinateFeature i‖₊^2*‖anisotropicRestartFieldEnergyMap D‖₊

def anisotropicRestartMeanSquareDifferentialLipschitzBound (D : AnisotropicSpinModel n) : ℝ≥0 :=
  ‖(n : ℝ)⁻¹‖₊ * ∑ i : Fin n,
    31*‖cavityCoordinateFeature i‖₊^2*‖anisotropicRestartFieldEnergyMap D‖₊^2

theorem anisotropicRestartMeanSquare_field_lipschitz (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q r : Paper.Overlap)
    (hqr : q ≤ r) :
    LipschitzWith (anisotropicRestartMeanSquareFieldLipschitzBound D)
      (fun x => anisotropicRestartMeanSquare D μ g q x r) := by
  have hs := nativeRestartLipschitz_sum
    (fun i x => anisotropicRestartSpinSquare D μ g q x i r)
    (fun i => 4*‖cavityCoordinateFeature i‖₊^2*‖anisotropicRestartFieldEnergyMap D‖₊)
    (anisotropicRestartSpinSquare_field_lipschitz D μ g q r hqr)
  have hh := (lipschitzWith_smul ((n : ℝ)⁻¹)).comp hs
  simpa only [anisotropicRestartMeanSquareFieldLipschitzBound, anisotropicRestartMeanSquare,
    Function.comp_def, smul_eq_mul, div_eq_mul_inv, mul_comm] using hh

theorem anisotropicRestartMeanSquare_field_differential_lipschitz (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q r : Paper.Overlap)
    (hqr : q ≤ r) :
    LipschitzWith (anisotropicRestartMeanSquareDifferentialLipschitzBound D)
      (fderiv ℝ (fun x => anisotropicRestartMeanSquare D μ g q x r)) := by
  let f := fun i : Fin n => fun x => anisotropicRestartSpinSquare D μ g q x i r
  have he : fderiv ℝ (fun x => anisotropicRestartMeanSquare D μ g q x r) =
      fun x => (n : ℝ)⁻¹ • ∑ i : Fin n, fderiv ℝ (f i) x := by
    funext x
    have hd := (HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      ((contDiff_anisotropicRestartSpinSquare_field D μ g q r hqr i).differentiable_one x).hasFDerivAt)).const_mul ((n : ℝ)⁻¹)
    simpa only [anisotropicRestartMeanSquare, f, div_eq_mul_inv,
      mul_comm, smul_eq_mul] using hd.fderiv
  rw [he]
  have hs := nativeRestartLipschitz_sum (fun i => fderiv ℝ (f i))
    (fun i => 31*‖cavityCoordinateFeature i‖₊^2*‖anisotropicRestartFieldEnergyMap D‖₊^2)
    (anisotropicRestartSpinSquare_field_differential_lipschitz D μ g q r hqr)
  exact (lipschitzWith_smul ((n : ℝ)⁻¹)).comp hs

end QuantitativeFollowup
