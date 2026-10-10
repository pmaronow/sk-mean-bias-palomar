module
public import FourPapersCommon.FiniteGaussianSumLaw
public import FourPapersCommon.FiniteStateGaussianLaw
public import FourPapersCommon.FiniteStateCascadeKernels
public import OverlapPaper.ReplicaSourceGroupBaseline

@[expose] public section

/-! Genuine same-mass Gaussian convolution for independent, different
linear Gaussian input maps. Zero recursion mass and singular maps are included. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set OverlapPaper
open scoped BigOperators NNReal
namespace FourPapersCommon
variable {S I J : Type*} [Fintype S] [Fintype I] [Fintype J]
set_option maxHeartbeats 1500000

def finiteStateGaussianSumMap
    (L : FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (M : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) :
    FiniteStateGaussianInput (I⊕J)→L[ℝ]FiniteStateField S :=
  L.comp finiteGaussianLeft+M.comp finiteGaussianRight

@[simp] theorem finiteStateGaussianSumMap_apply
    (L : FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (M : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (z : FiniteStateGaussianInput (I⊕J)) :
    finiteStateGaussianSumMap L M z=L (finiteGaussianLeft z)+M (finiteGaussianRight z) := rfl

theorem integrable_finiteStateGaussian_product_lipschitz
    (L : FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (M : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (F : FiniteStateField S→ℝ) {C : NNReal} (hF : LipschitzWith C F) (H : FiniteStateField S) :
    Integrable (fun z : FiniteStateGaussianInput I×FiniteStateGaussianInput J=>F (H+L z.1+M z.2))
      ((stdGaussian (FiniteStateGaussianInput I)).prod (stdGaussian (FiniteStateGaussianInput J))) := by
  have hFc := hF.continuous
  rw [←stdGaussian_map_finiteGaussianSplit]
  apply (integrable_map_measure (by fun_prop : AEStronglyMeasurable
    (fun z : FiniteStateGaussianInput I×FiniteStateGaussianInput J=>F (H+L z.1+M z.2))
    ((stdGaussian (FiniteStateGaussianInput (I⊕J))).map finiteGaussianSplit))
    measurable_finiteGaussianSplit.aemeasurable).mpr
  simpa only [Function.comp_def,finiteGaussianSplit,finiteStateGaussianSumMap_apply,add_assoc] using
    integrable_finiteStateGaussian_lipschitz F hF (finiteStateGaussianSumMap L M) H

theorem integrable_exp_finiteStateGaussian_product_lipschitz
    (L : FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (M : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (F : FiniteStateField S→ℝ) {C : NNReal} (hF : LipschitzWith C F) (H : FiniteStateField S) (a : ℝ) :
    Integrable (fun z : FiniteStateGaussianInput I×FiniteStateGaussianInput J=>Real.exp (a*F (H+L z.1+M z.2)))
      ((stdGaussian (FiniteStateGaussianInput I)).prod (stdGaussian (FiniteStateGaussianInput J))) := by
  have hFc := hF.continuous
  rw [←stdGaussian_map_finiteGaussianSplit]
  apply (integrable_map_measure (by fun_prop : AEStronglyMeasurable
    (fun z : FiniteStateGaussianInput I×FiniteStateGaussianInput J=>Real.exp (a*F (H+L z.1+M z.2)))
    ((stdGaussian (FiniteStateGaussianInput (I⊕J))).map finiteGaussianSplit))
    measurable_finiteGaussianSplit.aemeasurable).mpr
  simpa only [Function.comp_def,finiteGaussianSplit,finiteStateGaussianSumMap_apply,add_assoc] using
    integrable_exp_finiteStateGaussian_lipschitz F hF (finiteStateGaussianSumMap L M) H a

theorem exp_mul_finiteStateGaussianStep (a : ℝ)
    (L : FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (F : FiniteStateField S→ℝ) {C : NNReal} (hF : LipschitzWith C F) (H : FiniteStateField S) :
    Real.exp (a*finiteStateGaussianStep a L F H)=
      ∫z,Real.exp (a*F (H+L z)) ∂stdGaussian (FiniteStateGaussianInput I) := by
  by_cases ha : a=0
  · simp [ha]
  · unfold finiteStateGaussianStep sourceLogAverage
    rw [if_neg ha,mul_div_cancel₀ _ ha,Real.exp_log]
    exact integral_exp_pos (integrable_exp_finiteStateGaussian_lipschitz F hF L H a)

theorem finiteStateGaussianStep_convolution (a : ℝ)
    (L : FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (M : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (F : FiniteStateField S→ℝ) {C : NNReal} (hF : LipschitzWith C F) (H : FiniteStateField S) :
    finiteStateGaussianStep a L (finiteStateGaussianStep a M F) H=
      finiteStateGaussianStep a (finiteStateGaussianSumMap L M) F H := by
  have hFc := hF.continuous
  have hmean := (hasLaw_finiteGaussianSplit (I:=I) (J:=J)).integral_comp
    (f:=fun z : FiniteStateGaussianInput I×FiniteStateGaussianInput J=>F (H+L z.1+M z.2))
    (by fun_prop)
  have hexp := (hasLaw_finiteGaussianSplit (I:=I) (J:=J)).integral_comp
    (f:=fun z : FiniteStateGaussianInput I×FiniteStateGaussianInput J=>Real.exp (a*F (H+L z.1+M z.2)))
    (by fun_prop)
  simp only [Function.comp_def,finiteGaussianSplit,←add_assoc] at hmean hexp
  by_cases ha : a=0
  · subst a
    simp only [finiteStateGaussianStep,sourceLogAverage,ite_true]
    rw [←integral_prod _ (integrable_finiteStateGaussian_product_lipschitz L M F hF H),
      ←hmean]
    simp only [finiteStateGaussianSumMap_apply,add_assoc]
  · have hI : (∫z,Real.exp (a*finiteStateGaussianStep a M F (H+L z))
        ∂stdGaussian (FiniteStateGaussianInput I))=
        ∫z,Real.exp (a*F (H+finiteStateGaussianSumMap L M z))
          ∂stdGaussian (FiniteStateGaussianInput (I⊕J)) := by
      simp_rw [exp_mul_finiteStateGaussianStep a M F hF]
      rw [←integral_prod _ (integrable_exp_finiteStateGaussian_product_lipschitz L M F hF H a),←hexp]
      simp only [finiteStateGaussianSumMap_apply,add_assoc]
    change sourceLogAverage (stdGaussian (FiniteStateGaussianInput I)) a
      (fun z=>finiteStateGaussianStep a M F (H+L z))=
      sourceLogAverage (stdGaussian (FiniteStateGaussianInput (I⊕J))) a
        (fun z=>F (H+finiteStateGaussianSumMap L M z))
    simp only [sourceLogAverage,ha,ite_false,hI]

end FourPapersCommon
