module
public import QuantitativeFollowup.FollowupCavityParameters
public import QuantitativeFollowup.AnisotropicFiniteLaw
public import FourPapersCommon.FiniteCascadePruning
public import Mathlib.Probability.Kernel.Composition.MeasureComp

@[expose] public section

/-! Actual marked descendants for the one-site cavity model. The couplings
are drawn once from the genuine tilted Gaussian law. Every branch uses the
normalized Gaussian Cole--Hopf transition and conditionally independent
terminal Gibbs sampling. Deleting descendants preserves the retained law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open FourPapersCommon FiniteCascadeGenealogy FiniteCascadePruning QuantitativePaper
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}

def anisotropicFiniteTreeKernel (D : AnisotropicSpinModel n) (s : RSBScheme k)
    {j : ℕ} (T : FiniteCascadeGenealogy j) :
    Kernel (AnisotropicParameter n) (Samples (Configuration n) T) :=
  (finiteCascadeGenealogyKernel (fun _ : Configuration n => 0)
    (anisotropicSchemeMass s) (fun l => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) T).comap
      (anisotropicEnergyMap D) (anisotropicEnergyMap D).continuous.measurable

instance anisotropicFiniteTreeKernel_markov (D : AnisotropicSpinModel n) (s : RSBScheme k)
    {j : ℕ} (T : FiniteCascadeGenealogy j) : IsMarkovKernel (anisotropicFiniteTreeKernel D s T) := by
  haveI := isMarkovKernel_finiteCascadeGenealogyKernel (fun _ : Configuration n => 0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
    (fun l => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) T
  unfold anisotropicFiniteTreeKernel
  infer_instance

theorem anisotropicFiniteTreeKernel_leaf (D : AnisotropicSpinModel n) (s : RSBScheme k)
    {j : ℕ} (T : FiniteCascadeGenealogy j) (i : Leaf T) :
    (anisotropicFiniteTreeKernel D s T).map (eval T i) = anisotropicFiniteSpinKernel D s j := by
  unfold anisotropicFiniteTreeKernel anisotropicFiniteSpinKernel
  rw [←Kernel.comap_map_comm _ (anisotropicEnergyMap D).continuous.measurable
    (measurable_eval T i),finiteCascadeGenealogyKernel_leaf_marginal _ _ (anisotropicSchemeMass_nonneg s)]

theorem anisotropicFiniteTreeKernel_pruning (D : AnisotropicSpinModel n) (s : RSBScheme k)
    {j : ℕ} {T U : FiniteCascadeGenealogy j} (P : FiniteCascadePruning T U) :
    (anisotropicFiniteTreeKernel D s T).map (project P) = anisotropicFiniteTreeKernel D s U := by
  unfold anisotropicFiniteTreeKernel
  rw [←Kernel.comap_map_comm _ (anisotropicEnergyMap D).continuous.measurable
    (measurable_project P),finiteCascadeGenealogyKernel_pruning _ _ (anisotropicSchemeMass_nonneg s)]

def anisotropicFiniteTreeLaw (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ)
    (T : FiniteCascadeGenealogy (k+2)) : Measure (Samples (Configuration n) T) :=
  (anisotropicFiniteTreeKernel D s T) ∘ₘ (anisotropicFiniteInitialLaw D s a)

instance anisotropicFiniteTreeLaw_probability (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (T : FiniteCascadeGenealogy (k+2)) :
    IsProbabilityMeasure (anisotropicFiniteTreeLaw D s a T) := by
  unfold anisotropicFiniteTreeLaw
  infer_instance

theorem anisotropicFiniteTreeLaw_leaf (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (T : FiniteCascadeGenealogy (k+2)) (i : Leaf T) :
    (anisotropicFiniteTreeLaw D s a T).map (eval T i) =
      (anisotropicFiniteSpinKernel D s (k+2)) ∘ₘ (anisotropicFiniteInitialLaw D s a) := by
  rw [anisotropicFiniteTreeLaw,Measure.map_comp _ _ (measurable_eval T i),
    anisotropicFiniteTreeKernel_leaf]

theorem anisotropicFiniteTreeLaw_pruning (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) {T U : FiniteCascadeGenealogy (k+2)} (P : FiniteCascadePruning T U) :
    (anisotropicFiniteTreeLaw D s a T).map (project P) = anisotropicFiniteTreeLaw D s a U := by
  rw [anisotropicFiniteTreeLaw,Measure.map_comp _ _ (measurable_project P),
    anisotropicFiniteTreeKernel_pruning]
  rfl

def followupCavityFiniteTreeLaw (n : ℕ) (β ρ : ℝ) (hβ : 0 < β)
    (hρ : ρ ∈ Ioc 0 1) (s : RSBScheme k) (a u : ℝ) (hu : u ∈ Icc 0 1)
    (T : FiniteCascadeGenealogy (k+2)) : Measure (Samples (Configuration (n+1)) T) :=
  anisotropicFiniteTreeLaw (followupCavitySpinModel n β ρ hβ hρ u hu) s a T

instance followupCavityFiniteTreeLaw_probability (n : ℕ) (β ρ : ℝ) (hβ : 0 < β)
    (hρ : ρ ∈ Ioc 0 1) (s : RSBScheme k) (a u : ℝ) (hu : u ∈ Icc 0 1)
    (T : FiniteCascadeGenealogy (k+2)) :
    IsProbabilityMeasure (followupCavityFiniteTreeLaw n β ρ hβ hρ s a u hu T) := by
  unfold followupCavityFiniteTreeLaw
  infer_instance

theorem followupCavityFiniteTreeLaw_pruning (n : ℕ) (β ρ : ℝ) (hβ : 0 < β)
    (hρ : ρ ∈ Ioc 0 1) (s : RSBScheme k) (a u : ℝ) (hu : u ∈ Icc 0 1)
    {T U : FiniteCascadeGenealogy (k+2)} (P : FiniteCascadePruning T U) :
    (followupCavityFiniteTreeLaw n β ρ hβ hρ s a u hu T).map (project P) =
      followupCavityFiniteTreeLaw n β ρ hβ hρ s a u hu U :=
  anisotropicFiniteTreeLaw_pruning _ _ _ P

end QuantitativeFollowup
