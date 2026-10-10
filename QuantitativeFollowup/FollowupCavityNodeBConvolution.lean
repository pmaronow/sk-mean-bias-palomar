module
public import QuantitativeFollowup.FollowupCavityNodeBSchedule
public import FourPapersCommon.FiniteStateGaussianConvolutionKernels
public import FourPapersCommon.KernelExpectationTripleGrouping

@[expose] public section

/-! The changing-coordinate covariance schedule is the actual anisotropic
finite model. Same-mass Gaussian convolution identifies both values and all
normalized future transition laws, including singular and repeated cells. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT FourPapersCommon QuantitativePaper
set_option maxHeartbeats 1800000
variable {n k : ℕ}

def cavityNodeBCascade (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : Fin n) (M t : ℝ) (j : ℕ) : FiniteStateField (Configuration n)→ℝ :=
  finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
    (cavityNodeBScheduleMass s) (cavityNodeBCurrentInput D s i M t) j

def cavityNodeBOriginalCascade (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : Fin n) (M t : ℝ) (j : ℕ) : FiniteStateField (Configuration n)→ℝ :=
  finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
    (anisotropicSchemeMass s) (cavityFiniteEnergyInput (anisotropicReplaceVariance D i (M*t)) s) j

private theorem rest_cov_reverse (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : Fin n) (M t : ℝ) (ht : t∈Ioo 0 1) (j : ℕ) (σ τ : Configuration n) :
    finiteStateSpectralCovariance (cavityRestEnergyInput D s i j) σ τ=
      finiteStateSpectralCovariance (cavityNodeBCurrentInput D s i M t (3*j+1)) σ τ+
        finiteStateSpectralCovariance (cavityNodeBCurrentInput D s i M t (3*j)) σ τ := by
  rw [add_comm]
  exact cavityNodeBCurrentInput_rest_covariance D s i M t ⟨ht.1.le,ht.2.le⟩ j σ τ

private theorem full_cov_reverse (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : Fin n) (M t : ℝ) (hM : 0<M) (ht : t∈Ioo 0 1) (j : ℕ) (σ τ : Configuration n) :
    finiteStateSpectralCovariance (cavityFiniteEnergyInput (anisotropicReplaceVariance D i (M*t)) s j) σ τ=
      finiteStateSpectralCovariance (cavityNodeBCurrentInput D s i M t (3*j+2)) σ τ+
        finiteStateSpectralCovariance (cavityRestEnergyInput D s i j) σ τ := by
  rw [add_comm]
  exact cavityNodeBCurrentInput_combined_covariance D s i M t hM ht j σ τ

theorem cavityNodeBCascade_three_eq_original (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : Fin n) (M t : ℝ) (hM : 0<M) (ht : t∈Ioo 0 1) (J : ℕ) :
    cavityNodeBCascade D s i M t (3*J)=cavityNodeBOriginalCascade D s i M t J := by
  induction J with
  | zero => rfl
  | succ J ih =>
    let F:=cavityNodeBOriginalCascade D s i M t J
    have hF : LipschitzWith 1 F := finiteStateGaussianTerminalCascade_lipschitz
      (fun _ : Configuration n=>0) (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s) _ J
    have hrest : finiteStateGaussianStep (anisotropicSchemeMass s J)
        (cavityNodeBCurrentInput D s i M t (3*J+1))
        (finiteStateGaussianStep (anisotropicSchemeMass s J)
          (cavityNodeBCurrentInput D s i M t (3*J)) F)=
        finiteStateGaussianStep (anisotropicSchemeMass s J) (cavityRestEnergyInput D s i J) F := by
      funext H
      exact finiteStateGaussianStep_convolution_of_covariance _ _ _ _
        (rest_cov_reverse D s i M t ht J) F hF H
    have hidx : 3*(J+1)=(3*J+2)+1 := by omega
    change cavityNodeBCascade D s i M t ((3*J+2)+1)=_
    change finiteStateGaussianStep (cavityNodeBScheduleMass s (3*J+2))
      (cavityNodeBCurrentInput D s i M t (3*J+2))
      (finiteStateGaussianStep (cavityNodeBScheduleMass s (3*J+1))
        (cavityNodeBCurrentInput D s i M t (3*J+1))
        (finiteStateGaussianStep (cavityNodeBScheduleMass s (3*J))
          (cavityNodeBCurrentInput D s i M t (3*J))
          (cavityNodeBCascade D s i M t (3*J))))=_
    rw [ih,cavityNodeBScheduleMass_three,cavityNodeBScheduleMass_three_one,
      cavityNodeBScheduleMass_three_two]
    change finiteStateGaussianStep _ _ (finiteStateGaussianStep _ _ (finiteStateGaussianStep _ _ F))=_
    rw [hrest]
    funext H
    exact finiteStateGaussianStep_convolution_of_covariance _ _ _ _
      (full_cov_reverse D s i M t hM ht J) F hF H

theorem cavityNodeBCascade_three_one (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : Fin n) (M t : ℝ) (hM : 0<M) (ht : t∈Ioo 0 1) (J : ℕ) :
    cavityNodeBCascade D s i M t (3*J+1)=
      finiteStateGaussianStep (anisotropicSchemeMass s J)
        (cavityNodeBCurrentInput D s i M t (3*J)) (cavityNodeBOriginalCascade D s i M t J) := by
  change finiteStateGaussianStep (cavityNodeBScheduleMass s (3*J))
    (cavityNodeBCurrentInput D s i M t (3*J)) (cavityNodeBCascade D s i M t (3*J))=_
  rw [cavityNodeBScheduleMass_three,cavityNodeBCascade_three_eq_original D s i M t hM ht J]

theorem cavityNodeBCascade_three_two (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : Fin n) (M t : ℝ) (hM : 0<M) (ht : t∈Ioo 0 1) (J : ℕ) :
    cavityNodeBCascade D s i M t (3*J+2)=
      finiteStateGaussianStep (anisotropicSchemeMass s J)
        (cavityRestEnergyInput D s i J) (cavityNodeBOriginalCascade D s i M t J) := by
  change finiteStateGaussianStep (cavityNodeBScheduleMass s (3*J+1))
    (cavityNodeBCurrentInput D s i M t (3*J+1)) (cavityNodeBCascade D s i M t (3*J+1))=_
  rw [cavityNodeBScheduleMass_three_one,cavityNodeBCascade_three_one D s i M t hM ht J]
  funext H
  exact finiteStateGaussianStep_convolution_of_covariance _ _ _ _
    (rest_cov_reverse D s i M t ht J) _
    (finiteStateGaussianTerminalCascade_lipschitz _ _ (anisotropicSchemeMass_nonneg s) _ J) H

def cavityNodeBRefinedKernel (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : Fin n) (M t : ℝ) (j : ℕ) :
    Kernel (FiniteStateField (Configuration n)) (FiniteStateField (Configuration n)) :=
  finiteStateGaussianStepKernel (cavityNodeBScheduleMass s j)
    (cavityNodeBCurrentInput D s i M t j) (cavityNodeBCascade D s i M t j)

def cavityNodeBOriginalKernel (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : Fin n) (M t : ℝ) (j : ℕ) :
    Kernel (FiniteStateField (Configuration n)) (FiniteStateField (Configuration n)) :=
  finiteStateGaussianStepKernel (anisotropicSchemeMass s j)
    (cavityFiniteEnergyInput (anisotropicReplaceVariance D i (M*t)) s j)
    (cavityNodeBOriginalCascade D s i M t j)

theorem cavityNodeBRefinedKernel_markov (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : Fin n) (M t : ℝ) (j : ℕ) : IsMarkovKernel (cavityNodeBRefinedKernel D s i M t j) :=
  isMarkovKernel_finiteStateGaussianTerminalCascadeKernel _ _ (cavityNodeBScheduleMass_nonneg s) _ j

theorem cavityNodeBRefinedKernel_triple (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : Fin n) (M t : ℝ) (hM : 0<M) (ht : t∈Ioo 0 1) (j : ℕ) :
    tripleGroupedKernel (cavityNodeBRefinedKernel D s i M t) j=cavityNodeBOriginalKernel D s i M t j := by
  unfold tripleGroupedKernel cavityNodeBRefinedKernel
  rw [cavityNodeBScheduleMass_three,cavityNodeBScheduleMass_three_one,cavityNodeBScheduleMass_three_two,
    cavityNodeBCascade_three_eq_original D s i M t hM ht j,
    cavityNodeBCascade_three_one D s i M t hM ht j,
    cavityNodeBCascade_three_two D s i M t hM ht j]
  rw [finiteStateGaussianStepKernel_convolution_of_covariance _ (anisotropicSchemeMass_nonneg s j)
    _ _ _ (rest_cov_reverse D s i M t ht j) _
    (show LipschitzWith 1 (cavityNodeBOriginalCascade D s i M t j) from
      finiteStateGaussianTerminalCascade_lipschitz _ _ (anisotropicSchemeMass_nonneg s) _ j)]
  exact finiteStateGaussianStepKernel_convolution_of_covariance _ (anisotropicSchemeMass_nonneg s j)
    _ _ _ (full_cov_reverse D s i M t hM ht j) _
    (finiteStateGaussianTerminalCascade_lipschitz _ _ (anisotropicSchemeMass_nonneg s) _ j)

theorem cavityNodeBRefinedFuture_eq_original (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : Fin n) (M t : ℝ) (hM : 0<M) (ht : t∈Ioo 0 1) (j l : ℕ)
    (F : FiniteStateField (Configuration n)→ℝ) (hF : Measurable F)
    (C : ℝ) (hC : ∀x,|F x|≤C) (H : FiniteStateField (Configuration n)) :
    OverlapPaper.sourceKernelExpectation (fun p=>cavityNodeBRefinedKernel D s i M t (3*j+p)) (3*l) F H=
      OverlapPaper.sourceKernelExpectation (fun p=>cavityNodeBOriginalKernel D s i M t (j+p)) l F H := by
  rw [sourceKernelExpectation_triple_group _
    (fun p=>cavityNodeBRefinedKernel_markov D s i M t (3*j+p)) F hF C hC l H]
  congr 2
  funext p
  change (cavityNodeBRefinedKernel D s i M t (3*j+3*p) ∘ₖ
      cavityNodeBRefinedKernel D s i M t (3*j+(3*p+1))) ∘ₖ
        cavityNodeBRefinedKernel D s i M t (3*j+(3*p+2))=_
  simp_rw [show 3*j+3*p=3*(j+p) by omega,show 3*j+(3*p+1)=3*(j+p)+1 by omega,
    show 3*j+(3*p+2)=3*(j+p)+2 by omega]
  exact cavityNodeBRefinedKernel_triple D s i M t hM ht (j+p)

end QuantitativeFollowup
