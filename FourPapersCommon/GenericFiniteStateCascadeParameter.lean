module
public import FourPapersCommon.GenericFiniteStateCascadeVariance

@[expose] public section

/-! Parameter differentiation of actual finite Gaussian log averages, including
zero mass. The input derivatives and growth concern the preceding potential;
the normalized output derivative is obtained by dominated differentiation. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ContDiff BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 1600000
variable {I : Type*} [Fintype I]

def finiteStateGaussianInputMean (a : ℝ)
    (F D : FiniteStateGaussianInput I → ℝ) : ℝ :=
  SpinGlass.Targets.pairedTiltMean a 1
    (fun y => F (finiteStateGaussianCoordinateField (ContinuousLinearMap.id ℝ _) y))
    (fun y => D (finiteStateGaussianCoordinateField (ContinuousLinearMap.id ℝ _) y)) 0

private theorem norm_input_coordinates_le (y : Fin (Fintype.card I) → ℝ) :
    ‖finiteStateGaussianCoordinateField (ContinuousLinearMap.id ℝ (FiniteStateGaussianInput I)) y‖ ≤
      SpinGlass.Targets.l1 y := by
  apply (norm_finiteStateGaussianCoordinateField_le _ y).trans
  simpa using mul_le_mul_of_nonneg_right ContinuousLinearMap.norm_id_le (SpinGlass.Targets.l1_nonneg y)

theorem hasDerivAt_finiteStateGaussianInputStep_parameter (a : ℝ)
    (F D : ℝ → FiniteStateGaussianInput I → ℝ) (t : ℝ) (J : Set ℝ)
    (hJ : J ∈ 𝓝 t) (M M' : ℝ) (C C' : ℝ≥0)
    (hF : ∀ u ∈ J, Measurable (F u)) (hD : ∀ u ∈ J, Measurable (D u))
    (hd : ∀ u ∈ J, ∀ z, HasDerivAt (fun w => F w z) (D u z) u)
    (hb : ∀ u ∈ J, ∀ z, |F u z| ≤ M+C*‖z‖)
    (hb' : ∀ u ∈ J, ∀ z, |D u z| ≤ M'+C'*‖z‖) :
    HasDerivAt (fun u => OverlapPaper.sourceLogAverage (stdGaussian (FiniteStateGaussianInput I)) a (F u))
      (finiteStateGaussianInputMean a (F t) (D t)) t := by
  let A := fun u (y : Fin (Fintype.card I) → ℝ) =>
    F u (finiteStateGaussianCoordinateField (ContinuousLinearMap.id ℝ (FiniteStateGaussianInput I)) y)
  let A' := fun u (y : Fin (Fintype.card I) → ℝ) =>
    D u (finiteStateGaussianCoordinateField (ContinuousLinearMap.id ℝ (FiniteStateGaussianInput I)) y)
  have hAc (u) (hu : u ∈ J) : Measurable (A u) :=
    (hF u hu).comp (finiteStateGaussianCoordinateField (ContinuousLinearMap.id ℝ (FiniteStateGaussianInput I))).measurable
  have hDc (u) (hu : u ∈ J) : Measurable (A' u) :=
    (hD u hu).comp (finiteStateGaussianCoordinateField (ContinuousLinearMap.id ℝ (FiniteStateGaussianInput I))).measurable
  have hh := SpinGlass.Targets.hasDerivAt_parisiStepPi_param
    (A := A) (A' := A') (m := a) (v := 1) (C := M) (D := (C : ℝ))
    (C' := M') (D' := (C' : ℝ)) 0 hJ C.2 C'.2
    (fun u hu y => hd u hu _) hAc hDc
    (fun u hu y => (hb u hu _).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left (norm_input_coordinates_le y) C.2)))
    (fun u hu y => (hb' u hu _).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left (norm_input_coordinates_le y) C'.2)))
  have hval : (∫ z, A' t (fun i => (0 : Fin (Fintype.card I) → ℝ) i+Real.sqrt 1*z i) *
      SpinGlass.Targets.tiltWeightPi (Fintype.card I) a 1 (A t) 0 z
        ∂SpinGlass.Targets.piGauss (Fintype.card I)) = finiteStateGaussianInputMean a (F t) (D t) := by
    simp only [finiteStateGaussianInputMean, SpinGlass.Targets.pairedTiltMean, A, A',
      Real.sqrt_one, one_mul, Pi.zero_apply, zero_add]
  rw [hval] at hh
  apply hh.congr_of_eventuallyEq
  filter_upwards [hJ] with u hu
  have he := finiteStateGaussianStep_eq_coordinateStep a 1
    (ContinuousLinearMap.id ℝ (FiniteStateGaussianInput I)) (F u) (hF u hu) 0
  simpa only [finiteStateGaussianStep, Real.sqrt_one, one_smul, zero_add, ContinuousLinearMap.id_apply] using he

end FourPapersCommon
