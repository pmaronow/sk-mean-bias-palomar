module
public import FourPapersCommon.GenericFiniteStateCascadeGeneratorField
public import FourPapersCommon.FiniteStateCascadeHessianExpectations

@[expose] public section

/-! The variance generator is the expectation of its bounded spatial source
under the actual normalized Gaussian transition. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ContDiff BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 600000
variable {S I : Type*} [Fintype S] [Fintype I]

theorem finiteStateGaussianInputMean_field_eq_stepLaw (a v : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F G : FiniteStateField S → ℝ) (hF : Measurable F) (hG : Measurable G)
    (H : FiniteStateField S) :
    finiteStateGaussianInputMean a
      (fun z => F (H+Real.sqrt v • L z)) (fun z => G (H+Real.sqrt v • L z)) =
        ∫ y, G y ∂finiteStateGaussianStepLaw a (Real.sqrt v • L) F H := by
  rw [finiteStateGaussianInputMean_eq_integral_tilted a _ _ (by fun_prop) (by fun_prop),
    finiteStateGaussianStepLaw_eq_map_tilted a _ F hF H,
    integral_map (by fun_prop : Measurable (fun z : FiniteStateGaussianInput I => H+(Real.sqrt v • L) z)).aemeasurable
      hG.aestronglyMeasurable]
  rfl

theorem finiteStateGaussianVarianceGenerator_eq_stepMean (a v : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (hF : ContDiff ℝ 2 F)
    (C B : ℝ≥0) (hC : ∀ H, ‖fderiv ℝ F H‖ ≤ C)
    (hB : ∀ H, ‖fderiv ℝ (fderiv ℝ F) H‖ ≤ B) (H : FiniteStateField S) :
    finiteStateGaussianVarianceGenerator a v L F H =
      ∫ y, finiteStateGaussianGeneratorField a L F y
        ∂finiteStateGaussianStepLaw a (Real.sqrt v • L) F H := by
  classical
  have hLip : LipschitzWith C F := lipschitzWith_of_nnnorm_fderiv_le
    (hF.differentiable (by norm_num)) (fun y => NNReal.coe_le_coe.mp (hC y))
  have := isProbabilityMeasure_finiteStateGaussianStepLaw a (Real.sqrt v • L) F
    hF.continuous.measurable H (integrable_exp_finiteStateGaussian_lipschitz F hLip _ H a)
  let G := fun i (y : FiniteStateField S) =>
    fderiv ℝ (fderiv ℝ F) y (L (finiteStateGaussianBasis I i)) (L (finiteStateGaussianBasis I i))+
      a*(fderiv ℝ F y (L (finiteStateGaussianBasis I i)))^2
  have hGc (i : Fin (Fintype.card I)) : Continuous (G i) := by
    have h1 := hF.continuous_fderiv (by norm_num)
    have h2 := (hF.fderiv_right (m := (1 : ℕ∞ω)) (by norm_num)).continuous_fderiv (by norm_num)
    exact ((h2.clm_apply continuous_const).clm_apply continuous_const).add
      ((h1.clm_apply continuous_const).pow 2 |>.const_mul a)
  have hGi (i : Fin (Fintype.card I)) : Integrable (G i)
      (finiteStateGaussianStepLaw a (Real.sqrt v • L) F H) :=
    Integrable.of_bound (hGc i).aestronglyMeasurable ((B+|a| *C^2)*‖L‖^2)
      (.of_forall fun y => by simpa only [Real.norm_eq_abs] using
        norm_finiteStateGaussian_generator_summand_le a L F C B hC hB y i)
  have he (i : Fin (Fintype.card I)) :
      SpinGlass.Targets.pairedTiltMean a v
        (fun y => F (H+finiteStateGaussianCoordinateField L y))
        (fun y => G i (H+finiteStateGaussianCoordinateField L y)) 0 =
          ∫ y, G i y ∂finiteStateGaussianStepLaw a (Real.sqrt v • L) F H :=
    pairedTiltMean_field_eq_stepLaw a v L F (G i) hF.continuous.measurable (hGc i).measurable H
  simp only [finiteStateGaussianVarianceGenerator]
  change (∑ i, SpinGlass.Targets.pairedTiltMean a v
    (fun y => F (H+finiteStateGaussianCoordinateField L y))
    (fun y => G i (H+finiteStateGaussianCoordinateField L y)) 0)/2 = _
  simp_rw [he]
  rw [← integral_finsetSum Finset.univ (fun i _ => hGi i), ← integral_div]
  rfl

theorem continuousOn_finiteStateGaussian_family_varianceGenerator
    {F : ℝ → FiniteStateField S → ℝ} {C B K : ℝ≥0}
    (d : FiniteStateGaussianTimeData F C B K)
    (a : ℝ) (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) :
    ContinuousOn (fun p : ℝ×FiniteStateField S => finiteStateGaussianVarianceGenerator a (1-p.1) L (F p.1) p.2)
      (finiteStateGaussianTimeDomain S) := by
  have hc := continuousOn_normalized_finiteStateGaussian_family d a L
    (fun t H => finiteStateGaussianGeneratorField a L (F t) H)
    (continuousOn_finiteStateGaussianGeneratorField d a L)
    (finiteStateGaussianGeneratorBound a L C B)
    (fun t ht H => by simpa only [Real.norm_eq_abs] using
      abs_finiteStateGaussianGeneratorField_le a L (F t) C B (d.first_bound t ht) (d.second_bound t ht) H)
  apply hc.congr
  intro p hp
  change finiteStateGaussianVarianceGenerator a (1-p.1) L (F p.1) p.2 = _
  rw [finiteStateGaussianVarianceGenerator_eq_stepMean a (1-p.1) L (F p.1)
    (d.spatial_C2 p.1 hp.1) C B (d.first_bound p.1 hp.1) (d.second_bound p.1 hp.1)]
  exact (integral_finiteStateGaussianStepLaw a _ (F p.1) (d.spatial_C2 p.1 hp.1).continuous.measurable
    (finiteStateGaussianGeneratorField a L (F p.1))
    ((continuousOn_finiteStateGaussianGeneratorField d a L).comp
      (continuous_const.prodMk continuous_id).continuousOn (fun y _ => ⟨hp.1,mem_univ y⟩)
      |> continuousOn_univ.mp |>.stronglyMeasurable) p.2)

end FourPapersCommon
