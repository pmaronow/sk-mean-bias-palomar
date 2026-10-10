module
public import FourPapersCommon.FiniteStateCascadeHessianTelescoping
public import FourPapersCommon.FiniteStateCascadeSmoothJets

@[expose] public section

/-! Actual first and second responses to a terminal feature taking values
in {-1,1}. Every future square is an integral under the genuine split law. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace FourPapersCommon
open SpinGlass.AT
variable {S I : Type} [Fintype S] [Fintype I]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem finiteStateCascadeBinaryFeature_second (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j : ℕ) (H K : FiniteStateField S) (hK : ∀ σ, K σ * K σ = 1) :
    fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L j)) H K K +
      a j * (fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) H K)^2 =
    1 - (1-a 0) * (∫ z, K z.1 * K z.2 ∂finiteStateCascadeSplitLaw V a L 0 j H) -
      ∑ p ∈ Finset.range j, (a p-a (p+1)) *
        (∫ z, K z.1 * K z.2 ∂finiteStateCascadeSplitLaw V a L (p+1) (j-(p+1)) H) := by
  classical
  haveI := isMarkovKernel_finiteStateCascadeGibbsKernel V a ha L j
  have hp : fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) H
      (finiteStatePointwiseProduct K K) = 1 := by
    rw [fderiv_finiteStateGaussianTerminalCascade_eq_gibbsMean V a ha L j]
    simp [finiteStatePointwiseProduct_apply, hK]
  have he := finiteStateCascadeHessian_pair_decomposition V a ha L j H K K
  rw [hp] at he
  simp_rw [finiteStateCascadePairMoment_eq_splitLaw V a ha L] at he
  have hs : (∑ p ∈ Finset.range j, (a (p+1)-a p) *
      (∫ z, K z.1 * K z.2 ∂finiteStateCascadeSplitLaw V a L (p+1) (j-(p+1)) H)) =
      -(∑ p ∈ Finset.range j, (a p-a (p+1)) *
        (∫ z, K z.1 * K z.2 ∂finiteStateCascadeSplitLaw V a L (p+1) (j-(p+1)) H)) := by
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hs] at he
  nlinarith only [he]

theorem hasDerivAt_finiteStateCascadeFeature_parameter (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j : ℕ) (H K : FiniteStateField S) (θ : ℝ) :
    HasDerivAt (fun u : ℝ => finiteStateGaussianTerminalCascade V a L j (H + u • K))
      (∫ σ, K σ ∂finiteStateCascadeGibbsKernel V a L j (H + θ • K)) θ := by
  have hd := ((contDiff_one_finiteStateGaussianTerminalCascade V a ha L j).differentiable_one
    (H + θ • K)).hasFDerivAt
  have hc := hd.comp_hasDerivAt θ ((hasDerivAt_id θ).smul_const K |>.const_add H)
  simpa only [Function.comp_def, id_eq, one_smul, fderiv_finiteStateGaussianTerminalCascade_eq_gibbsMean V a ha L j] using hc

end FourPapersCommon
