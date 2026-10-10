module
public import FourPapersCommon.FiniteStateGaussianConvolution
public import FourPapersCommon.ScalarVectorColeHopf

@[expose] public section

/-! An independent scalar Gaussian terminal feature is exactly a new
Gaussian root coordinate. The Fubini input is an actual integrability
condition, allowing the exponential weights of physical cascade laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open QuantitativePaper
namespace FourPapersCommon
variable {S I : Type} [Fintype S] [Fintype I]
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem hasLaw_scalarRootCoordinate (c : ℝ) :
    HasLaw (fun z : Field 1 => c*z 0) (gaussianReal 0 (c^2).toNNReal)
      (stdGaussian (Field 1)) := by
  have h := gaussianReal_const_mul hasLaw_field_one_coordinate c
  have hg : fieldGaussian 1 = stdGaussian (Field 1) := map_pi_eq_stdGaussian
  simpa only [hg, mul_zero, mul_one, Real.toNNReal_of_nonneg (sq_nonneg c)] using h

theorem integral_finiteStateGaussianRawKernel_scalar_split
    (R : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (K H : FiniteStateField S) (c : ℝ) (f : FiniteStateField S → ℝ)
    (hf : Measurable f)
    (hi : Integrable f (finiteStateGaussianRawKernel
      (finiteStateGaussianSumMap R (scalarGaussianShift (c • K))) H)) :
    (∫Q,f Q ∂finiteStateGaussianRawKernel
      (finiteStateGaussianSumMap R (scalarGaussianShift (c • K))) H) =
      ∫θ,(∫Q,f (Q+θ • K) ∂finiteStateGaussianRawKernel R H)
        ∂gaussianReal 0 (c^2).toNNReal := by
  let g : FiniteStateGaussianInput I × Field 1 → ℝ :=
    fun z => f (H+R z.1+scalarGaussianShift (c • K) z.2)
  have hgm : Measurable g := hf.comp (by fun_prop)
  have hiS : Integrable (fun z => f (H+finiteStateGaussianSumMap R (scalarGaussianShift (c • K)) z))
      (stdGaussian (FiniteStateGaussianInput (I ⊕ Fin 1))) := by
    rw [finiteStateGaussianRawKernel_apply] at hi
    exact (integrable_map_measure hf.aestronglyMeasurable (by fun_prop)).mp hi
  have hiP : Integrable g ((stdGaussian (FiniteStateGaussianInput I)).prod (stdGaussian (Field 1))) := by
    rw [← stdGaussian_map_finiteGaussianSplit]
    apply (integrable_map_measure hgm.aestronglyMeasurable
      measurable_finiteGaussianSplit.aemeasurable).mpr
    simpa only [g, Function.comp_def, finiteGaussianSplit,
      finiteStateGaussianSumMap_apply, add_assoc] using hiS
  have he := (hasLaw_finiteGaussianSplit (I:=I) (J:=Fin 1)).integral_comp hgm.aestronglyMeasurable
  have ht : StronglyMeasurable (fun θ : ℝ =>
      ∫z : FiniteStateGaussianInput I,f (H+R z+θ • K) ∂stdGaussian (FiniteStateGaussianInput I)) := by
    have hm : Measurable (fun z : ℝ × FiniteStateGaussianInput I => f (H+R z.2+z.1 • K)) :=
      hf.comp (by fun_prop)
    exact hm.stronglyMeasurable.integral_prod_right'
  rw [finiteStateGaussianRawKernel_apply, integral_map (by fun_prop) hf.aestronglyMeasurable]
  calc
    _ = ∫z,g z ∂(stdGaussian (FiniteStateGaussianInput I)).prod (stdGaussian (Field 1)) := by
      simpa only [g, Function.comp_def, finiteGaussianSplit,
        finiteStateGaussianSumMap_apply, add_assoc] using he
    _ = ∫w : Field 1,∫z : FiniteStateGaussianInput I,
        f (H+R z+(c*w 0) • K) ∂stdGaussian (FiniteStateGaussianInput I) ∂stdGaussian (Field 1) := by
      rw [integral_prod_symm _ hiP]
      simp only [g, scalarGaussianShift_apply, smul_smul]
      apply integral_congr_ae
      exact .of_forall fun w => integral_congr_ae (.of_forall fun z => by
        dsimp only
        rw [mul_comm (w 0) c])
    _ = ∫θ,(∫z : FiniteStateGaussianInput I,f (H+R z+θ • K)
        ∂stdGaussian (FiniteStateGaussianInput I)) ∂gaussianReal 0 (c^2).toNNReal :=
      (hasLaw_scalarRootCoordinate c).integral_comp ht.aestronglyMeasurable
    _ = _ := by
      apply integral_congr_ae
      exact .of_forall fun θ => by
        dsimp only
        rw [finiteStateGaussianRawKernel_apply]
        exact (integral_map (by fun_prop)
          (hf.comp (by fun_prop : Measurable (fun Q : FiniteStateField S => Q+θ • K))).aestronglyMeasurable).symm

end FourPapersCommon
