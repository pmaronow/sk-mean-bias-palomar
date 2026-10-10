module
public import FourPapersCommon.FiniteStateCascadeExpectations
public import FourPapersCommon.FiniteStateCascadeLinearTransport

@[expose] public section

/-! Actual normalized Gibbs expectations transport through any continuous
linear field embedding. The pushed law is proved from the Gaussian integrals,
including zero mass; no injectivity or law identification is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators
namespace FourPapersCommon
open OverlapPaper SpinGlass.AT
set_option maxHeartbeats 1600000
variable {S R I : Type*} [Fintype S] [Fintype R] [Fintype I]
 [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

 theorem finiteStateGaussianStepLaw_comp_linear
    (T : FiniteStateField R →L[ℝ] FiniteStateField S)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField R)
    (a : ℝ) (F : FiniteStateField S → ℝ) (hF : Measurable F)
    (H : FiniteStateField R) :
    (finiteStateGaussianStepLaw a L (fun y => F (T y)) H).map T=
      finiteStateGaussianStepLaw a (T.comp L) F (T H) := by
  have hm : Measurable (fun y => F (T y)) := by
    simpa only [Function.comp_def] using hF.comp T.continuous.measurable
  rw [finiteStateGaussianStepLaw_eq_map_tilted a L _ hm,
    Measure.map_map T.continuous.measurable (by fun_prop),
    finiteStateGaussianStepLaw_eq_map_tilted a (T.comp L) F hF]
  have he : (fun z => a*F (T (H+L z)))=(fun z => a*F (T H+(T.comp L) z)) := by
    funext z
    simp only [map_add,ContinuousLinearMap.comp_apply]
  rw [he]
  congr 1
  funext z
  simp only [Function.comp_def,map_add,ContinuousLinearMap.comp_apply]

 theorem integral_finiteStateCascadeGibbsKernel_comp_linear
    (V : S → ℝ) (P : S → ℝ) (a : ℕ → ℝ) (ha : ∀ j, 0≤a j)
    (T : FiniteStateField R →L[ℝ] FiniteStateField S)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField R)
    (j : ℕ) (H : FiniteStateField R) :
    (∫ σ, P σ ∂finiteStateCascadeGibbsKernel V a (fun i => T.comp (L i)) j (T H))=
      sourceKernelExpectation (finiteStateGaussianCascadeKernel a L (fun y => gtStateLogPartition V (T y))) j
        (fun y => ∫ σ, P σ ∂finiteStateGibbsKernel V (T y)) H := by
  classical
  let K : ℝ := ∑ σ : S, |P σ|
  have hPm : Measurable P := measurable_of_finite _
  have hPb (σ : S) : |P σ|≤K :=
    Finset.single_le_sum (fun σ _ => abs_nonneg (P σ)) (Finset.mem_univ σ)
  have hF := (finiteStateGaussianTerminal_lipschitz V).comp T.lipschitzWith
  induction j generalizing H with
  | zero =>
    simp only [finiteStateCascadeGibbsKernel,finiteStateCascadeFieldKernel,sourceKernelLaw,
      Kernel.comp_id,sourceKernelExpectation]
  | succ j ih =>
    haveI := isMarkovKernel_finiteStateCascadeGibbsKernel V a ha (fun i => T.comp (L i)) j
    haveI := isMarkovKernel_finiteStateGaussianTerminalCascadeKernel V a ha (fun i => T.comp (L i)) j
    have heK : finiteStateCascadeGibbsKernel V a (fun i => T.comp (L i)) (j+1)=
        finiteStateCascadeGibbsKernel V a (fun i => T.comp (L i)) j ∘ₖ
          finiteStateGaussianCascadeKernel a (fun i => T.comp (L i)) (gtStateLogPartition V) j := by
      simp only [finiteStateCascadeGibbsKernel,finiteStateCascadeFieldKernel,sourceKernelLaw,Kernel.comp_assoc]
    rw [heK,Kernel.integral_comp (source_bounded_integrable _ P hPm K hPb)]
    have hc := contDiff_one_finiteStateGaussianTerminalCascade V a ha (fun i => T.comp (L i)) j
    change (∫ y, (∫ σ, P σ ∂finiteStateCascadeGibbsKernel V a (fun i => T.comp (L i)) j y)
      ∂finiteStateGaussianStepKernel (a j) (T.comp (L j))
        (finiteStateGaussianTerminalCascade V a (fun i => T.comp (L i)) j) (T H))=_
    rw [finiteStateGaussianStepKernel_apply _ _ _ hc.continuous.measurable]
    have heF : (fun y => finiteStateGaussianTerminalCascade V a (fun i => T.comp (L i)) j (T y))=
        finiteStateGaussianCascade a L (fun y => gtStateLogPartition V (T y)) j := by
      funext y
      exact finiteStateGaussianCascade_comp_linear T L a (gtStateLogPartition V) j y
    rw [←finiteStateGaussianStepLaw_comp_linear T (L j) (a j) _ hc.continuous.measurable H]
    have hgm : Measurable (fun y => ∫ σ, P σ ∂finiteStateCascadeGibbsKernel V a (fun i => T.comp (L i)) j y) :=
      (hPm.stronglyMeasurable.integral_kernel).measurable
    rw [integral_map T.continuous.measurable.aemeasurable hgm.aestronglyMeasurable]
    simp_rw [ih]
    change (∫ y, sourceKernelExpectation _ j _ y
      ∂finiteStateGaussianStepLaw (a j) (L j)
        (fun y => finiteStateGaussianTerminalCascade V a (fun i => T.comp (L i)) j (T y)) H)=_
    rw [heF]
    rw [sourceKernelExpectation]
    congr 1
    exact (finiteStateGaussianStepKernel_apply _ _ _
      (finiteStateGaussianCascade_lipschitz _ hF a ha L j).continuous.measurable H).symm

end FourPapersCommon
