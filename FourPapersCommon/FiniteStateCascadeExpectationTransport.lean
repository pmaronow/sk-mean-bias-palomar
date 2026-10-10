module
public import FourPapersCommon.FiniteStateCascadeGibbsTransport

@[expose] public section

/-! Honest transport of every measurable cascade observable through a
continuous linear field map, including a cascade beginning at any depth. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Real OverlapPaper
namespace FourPapersCommon
variable {S R I : Type*} [Fintype S] [Fintype R] [Fintype I]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
set_option maxHeartbeats 1500000

theorem sourceKernelExpectation_finiteStateCascade_comp_linear
    (T : FiniteStateField R→L[ℝ]FiniteStateField S)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField R)
    (a : ℕ→ℝ) (ha : ∀j,0 ≤ a j)
    (F : FiniteStateField S→ℝ) {C : NNReal} (hF : LipschitzWith C F)
    (p j : ℕ) (G : FiniteStateField S→ℝ) (hG : Measurable G) (H : FiniteStateField R) :
    sourceKernelExpectation
      (fun r=>finiteStateGaussianCascadeKernel a (fun l=>T.comp (L l)) F (p+r)) j G (T H)=
      sourceKernelExpectation
        (fun r=>finiteStateGaussianCascadeKernel a L (fun y=>F (T y)) (p+r)) j (fun y=>G (T y)) H := by
  induction j generalizing H with
  | zero => rfl
  | succ j ih =>
    rw [sourceKernelExpectation,sourceKernelExpectation]
    dsimp only
    have hU := finiteStateGaussianCascade_lipschitz F hF a ha (fun l=>T.comp (L l)) (p+j)
    have hUm := hU.continuous.measurable
    have hCm := sourceKernelExpectation_measurable
      (fun r=>finiteStateGaussianCascadeKernel a (fun l=>T.comp (L l)) F (p+r)) G hG j
    rw [finiteStateGaussianCascadeKernel,finiteStateGaussianStepKernel_apply _ _ _ hUm,
      ←finiteStateGaussianStepLaw_comp_linear T (L (p+j)) (a (p+j)) _ hUm H,
      integral_map T.measurable.aemeasurable hCm.aestronglyMeasurable]
    simp_rw [ih]
    have hUF : (fun y=>finiteStateGaussianCascade a (fun l=>T.comp (L l)) F (p+j) (T y))=
        finiteStateGaussianCascade a L (fun y=>F (T y)) (p+j) :=
      funext (finiteStateGaussianCascade_comp_linear T L a F (p+j))
    rw [hUF]
    rw [finiteStateGaussianCascadeKernel,finiteStateGaussianStepKernel_apply]
    exact (finiteStateGaussianCascade_lipschitz _ (hF.comp T.lipschitz) a ha L (p+j)).continuous.measurable

end FourPapersCommon
