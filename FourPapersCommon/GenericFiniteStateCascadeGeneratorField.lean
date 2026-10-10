module
public import FourPapersCommon.GenericFiniteStateCascadeFamilySpatial
public import FourPapersCommon.GenericFiniteStateCascadeTimeFormula

@[expose] public section

/-! The bounded continuous spatial source in Gaussian covariance calculus. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ContDiff BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 600000
variable {S I : Type*} [Fintype S] [Fintype I]

def finiteStateGaussianGeneratorField (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (H : FiniteStateField S) : ℝ :=
  (∑ i, (fderiv ℝ (fderiv ℝ F) H (L (finiteStateGaussianBasis I i))
    (L (finiteStateGaussianBasis I i)) +
    a*(fderiv ℝ F H (L (finiteStateGaussianBasis I i)))^2))/2

def finiteStateGaussianGeneratorBound (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (C B : ℝ≥0) : ℝ≥0 :=
  Real.toNNReal ((Fintype.card I : ℝ)*(B+|a| *C^2)*‖L‖^2/2)

theorem finiteStateGaussianGeneratorBound_coe (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (C B : ℝ≥0) :
    (finiteStateGaussianGeneratorBound a L C B : ℝ) =
      (Fintype.card I : ℝ)*(B+|a| *C^2)*‖L‖^2/2 := Real.coe_toNNReal _ (by positivity)

theorem norm_finiteStateGaussian_generator_summand_le (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (C B : ℝ≥0)
    (hC : ∀ H, ‖fderiv ℝ F H‖ ≤ C)
    (hB : ∀ H, ‖fderiv ℝ (fderiv ℝ F) H‖ ≤ B)
    (H : FiniteStateField S) (i : Fin (Fintype.card I)) :
    |fderiv ℝ (fderiv ℝ F) H (L (finiteStateGaussianBasis I i))
      (L (finiteStateGaussianBasis I i)) +
      a*(fderiv ℝ F H (L (finiteStateGaussianBasis I i)))^2| ≤
        (B+|a| *C^2)*‖L‖^2 := by
  let v := L (finiteStateGaussianBasis I i)
  have hv : ‖v‖ ≤ ‖L‖ := by simpa [v] using L.le_opNorm (finiteStateGaussianBasis I i)
  have hg := (fderiv ℝ F H).le_opNorm v
  rw [Real.norm_eq_abs] at hg
  have hg' := hg.trans (mul_le_mul (hC H) hv (norm_nonneg _) C.2)
  have hh := (fderiv ℝ (fderiv ℝ F) H v).le_opNorm v
  rw [Real.norm_eq_abs] at hh
  have hh' := (fderiv ℝ (fderiv ℝ F) H).le_opNorm v
  have hb := mul_le_mul (hB H) hv (norm_nonneg _) B.2
  have hb' := mul_le_mul (hh'.trans hb) hv (norm_nonneg _) (mul_nonneg B.2 (norm_nonneg _))
  have hsq : |fderiv ℝ F H v|^2 ≤ (C*‖L‖)^2 :=
    (sq_le_sq₀ (abs_nonneg (fderiv ℝ F H v)) (by positivity)).2 hg'
  have ha := mul_le_mul_of_nonneg_left hsq (abs_nonneg a)
  calc
    _ ≤ |fderiv ℝ (fderiv ℝ F) H v v|+|a*(fderiv ℝ F H v)^2| := abs_add_le _ _
    _ ≤ (B+|a| *C^2)*‖L‖^2 := by
      rw [abs_mul, abs_sq]
      rw [sq_abs] at ha
      nlinarith [hh.trans hb']

theorem abs_finiteStateGaussianGeneratorField_le (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (C B : ℝ≥0)
    (hC : ∀ H, ‖fderiv ℝ F H‖ ≤ C)
    (hB : ∀ H, ‖fderiv ℝ (fderiv ℝ F) H‖ ≤ B) (H : FiniteStateField S) :
    |finiteStateGaussianGeneratorField a L F H| ≤ finiteStateGaussianGeneratorBound a L C B := by
  classical
  rw [finiteStateGaussianGeneratorField, abs_div, abs_of_pos (by norm_num : (0 : ℝ)<2),
    finiteStateGaussianGeneratorBound_coe]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hh := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    norm_finiteStateGaussian_generator_summand_le a L F C B hC hB H i
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc] using hh

theorem continuousOn_finiteStateGaussianGeneratorField
    {F : ℝ → FiniteStateField S → ℝ} {C B K : ℝ≥0}
    (d : FiniteStateGaussianTimeData F C B K)
    (a : ℝ) (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) :
    ContinuousOn (fun p : ℝ×FiniteStateField S => finiteStateGaussianGeneratorField a L (F p.1) p.2)
      (finiteStateGaussianTimeDomain S) := by
  classical
  apply ContinuousOn.div_const
  apply continuousOn_finsetSum
  intro i _
  exact ((d.second_cont.clm_apply continuousOn_const).clm_apply continuousOn_const).add
    ((d.first_cont.clm_apply continuousOn_const).pow 2 |>.const_mul a)

end FourPapersCommon
