module
public import FourPapersCommon.FiniteStateCascadeGrowth

@[expose] public section

/-! Order preservation of genuine Gaussian logarithmic averages and finite
cascades. All Gaussian integrability follows from honest Lipschitz bounds. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal
namespace FourPapersCommon
open OverlapPaper
variable {S I : Type*} [Fintype S] [Fintype I]

 theorem finiteStateGaussianStep_mono (a : ℝ) (ha : 0 ≤ a)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F G : FiniteStateField S → ℝ) {C D : ℝ≥0}
    (hF : LipschitzWith C F) (hG : LipschitzWith D G) (hle : ∀ H, F H ≤ G H)
    (H : FiniteStateField S) : finiteStateGaussianStep a L F H ≤ finiteStateGaussianStep a L G H := by
  by_cases ha0 : a=0
  · simp only [finiteStateGaussianStep,sourceLogAverage,ha0,ite_true]
    exact integral_mono (integrable_finiteStateGaussian_lipschitz F hF L H)
      (integrable_finiteStateGaussian_lipschitz G hG L H) (fun z => hle (H+L z))
  · have hap : 0<a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hiF := integrable_exp_finiteStateGaussian_lipschitz F hF L H a
    have hiG := integrable_exp_finiteStateGaussian_lipschitz G hG L H a
    have hI := integral_mono hiF hiG (fun z => Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (hle (H+L z)) ha))
    have hlog := Real.log_le_log (integral_exp_pos hiF) hI
    simp only [finiteStateGaussianStep,sourceLogAverage,ha0,ite_false]
    exact div_le_div_of_nonneg_right hlog ha

 theorem finiteStateGaussianCascade_mono (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F G : FiniteStateField S → ℝ) {C D : ℝ≥0}
    (hF : LipschitzWith C F) (hG : LipschitzWith D G) (hle : ∀ H, F H ≤ G H)
    (J : ℕ) (H : FiniteStateField S) :
    finiteStateGaussianCascade a L F J H ≤ finiteStateGaussianCascade a L G J H := by
  induction J generalizing H with
  | zero => exact hle H
  | succ J ih =>
    exact finiteStateGaussianStep_mono (a J) (ha J) (L J) _ _
      (finiteStateGaussianCascade_lipschitz F hF a ha L J)
      (finiteStateGaussianCascade_lipschitz G hG a ha L J) ih H

end FourPapersCommon
