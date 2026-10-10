module
public import QuantitativeFollowup.AnisotropicTailDerivative
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

/-! Honest joint measurability and global spatial bounds for the limiting
anisotropic response. Difference quotients use the actual C1 potential. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter QuantitativePaper
open scoped NNReal Topology ContDiff
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 500000

theorem hasDerivAt_affine_line_of_differentiable {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E→ℝ) (hF : Differentiable ℝ F)
    (x v : E) (r : ℝ) :
    HasDerivAt (fun s => F (x+s • v)) (fderiv ℝ F (x+r • v) v) r := by
  apply (hF _).hasFDerivAt.comp_hasDerivAt r
  simpa only [id_eq,one_smul] using ((hasDerivAt_id r).smul_const v |>.const_add x)

theorem anisotropicMeasureTailDifferential_lipschitz (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) :
    LipschitzWith (‖anisotropicEnergyMap D‖₊^2) (fderiv ℝ (anisotropicMeasureTailPotential D μ q)) := by
  apply LipschitzWith.of_dist_le_mul
  intro P Q
  apply le_of_tendsto
    (((anisotropicMeasureTailPotential_derivative_limit D μ q).1.tendsto_at P).dist
      ((anisotropicMeasureTailPotential_derivative_limit D μ q).1.tendsto_at Q))
  exact Eventually.of_forall fun j => (anisotropicDyadicTailPotential_fderiv_lipschitz D μ q j).dist_le_mul P Q

theorem anisotropicMeasureTailMagnetization_lipschitz (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) :
    LipschitzWith (‖anisotropicResponseMap n‖₊*(‖anisotropicEnergyMap D‖₊^2))
      (anisotropicMeasureTailMagnetization D μ q) :=
  (anisotropicResponseMap n).lipschitz.comp (anisotropicMeasureTailDifferential_lipschitz D μ q)

theorem measurable_anisotropicMeasureTailMagnetization (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) :
    Measurable (fun z : Paper.Overlap×AnisotropicParameter n => anisotropicMeasureTailMagnetization D μ z.1 z.2) := by
  apply (WithLp.measurable_toLp 2 _).comp
  apply Measurable.of_eval
  intro i
  let h := fun j : ℕ => (1 : ℝ)/((j : ℝ)+1)
  have hpos (j : ℕ) : 0<h j := by dsimp only [h];positivity
  have hlim : Tendsto h atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,Eventually.of_forall hpos⟩
  let Q := fun j : ℕ => fun z : Paper.Overlap×AnisotropicParameter n =>
    (h j)⁻¹*(anisotropicMeasureTailPotential D μ z.1 (z.2+h j • anisotropicCoordinateDirection n i)-
      anisotropicMeasureTailPotential D μ z.1 z.2)
  have hQ (j : ℕ) : Measurable (Q j) := by
    have h₁ := (measurable_anisotropicMeasureTailPotential D μ).comp
      (show Measurable (fun z : Paper.Overlap×AnisotropicParameter n =>
        (z.1,z.2+h j • anisotropicCoordinateDirection n i)) from by fun_prop)
    exact measurable_const.mul (h₁.sub (measurable_anisotropicMeasureTailPotential D μ))
  apply measurable_of_tendsto_metrizable hQ
  apply tendsto_pi_nhds.mpr
  intro z
  let U := anisotropicMeasureTailPotential D μ z.1
  let v := anisotropicCoordinateDirection n i
  have hd : HasDerivAt (fun r : ℝ => U (z.2+r • v)) (fderiv ℝ U z.2 v) 0 := by
    simpa only [zero_smul,add_zero] using hasDerivAt_affine_line_of_differentiable U
      (anisotropicMeasureTailPotential_derivative_limit D μ z.1).2.differentiable_one z.2 v 0
  have hh := hd.tendsto_slope_zero_right.comp hlim
  change Tendsto (fun j => Q j z) atTop (𝓝 (fderiv ℝ U z.2 v))
  simpa only [Q,zero_smul,add_zero,zero_add,smul_eq_mul,Function.comp_def,U,v] using hh

end QuantitativeFollowup
