module
public import QuantitativeFollowup.FollowupCavityRootScaling
public import FourPapersCommon.FiniteCascadeTerminalSampleEquiv

@[expose] public section

/-! The physical incident-row and last-field interpolation on one fixed
Gaussian product. Its expectation is the ratio of actual positive marked
weights, with the true one-leaf normalizer. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

def cavityInterpolationGaussianScale (p : AnisotropicCouplingIndex n→Bool)
    (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (u b : ℝ) :
    CavityPathGaussianSpace T n→L[ℝ]CavityPathGaussianSpace T n :=
  (gaussianSelectedScale (cavityRootCouplingMask p T) u).comp
    (gaussianSelectedScale (cavitySelectedRootPathMask i T) b)

def cavityInterpolationSpinWeight (D : AnisotropicSpinModel n)
    (p : AnisotropicCouplingIndex n→Bool) (s : RSBScheme k) (a : ℝ) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (σ : TerminalSpins (Configuration n) T) (u b : ℝ) : ℝ :=
  ∫z : CavityPathGaussianSpace T n,cavityPathNumerator D s a i T σ
    (b,cavityInterpolationGaussianScale p i T u b z)∂stdGaussian (CavityPathGaussianSpace T n)

theorem cavityInterpolationSpinWeight_eq_actual (D : AnisotropicSpinModel n)
    (p : AnisotropicCouplingIndex n→Bool) (s : RSBScheme k) (a : ℝ) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (σ : TerminalSpins (Configuration n) T) (u b : ℝ) :
    cavityInterpolationSpinWeight D p s a i T σ u b=
      cavityPathSpinWeight (anisotropicScaleRootCouplings D p u) s a i T σ b := by
  unfold cavityInterpolationSpinWeight cavityPathSpinWeight
  simp_rw [cavityPathNumerator_scaleRootCouplings]
  rfl

def cavityInterpolationMarkedExpectation (D : AnisotropicSpinModel n)
    (p : AnisotropicCouplingIndex n→Bool) (s : RSBScheme k) (a : ℝ) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (F : TerminalSpins (Configuration n) T→ℝ)
    (u b : ℝ) : ℝ :=
  cavityPathMarkedExpectation (anisotropicScaleRootCouplings D p u) s a i T F b

theorem cavityInterpolationMarkedExpectation_eq_normalized_weights (D : AnisotropicSpinModel n)
    (p : AnisotropicCouplingIndex n→Bool) (s : RSBScheme k) (a : ℝ) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (F : TerminalSpins (Configuration n) T→ℝ) (u b : ℝ) (hb : 0<b) :
    cavityInterpolationMarkedExpectation D p s a i T F u b=
      (∑σ,F σ*cavityInterpolationSpinWeight D p s a i T σ u b)/
        (∑σ,cavityInterpolationSpinWeight D p s a i T σ u b) := by
  simp_rw [cavityInterpolationSpinWeight_eq_actual]
  rw [sum_cavityPathSpinWeight_eq_normalizer _ s a i T b hb]
  exact cavityPathMarkedExpectation_eq_weighted_sum _ s a i T F b hb

theorem cavityInterpolationSpinWeight_sum_pos (D : AnisotropicSpinModel n)
    (p : AnisotropicCouplingIndex n→Bool) (s : RSBScheme k) (a : ℝ) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (u b : ℝ) (hb : 0<b) : 0<∑σ,cavityInterpolationSpinWeight D p s a i T σ u b := by
  simp_rw [cavityInterpolationSpinWeight_eq_actual]
  rw [sum_cavityPathSpinWeight_eq_normalizer _ s a i T b hb]
  exact cavityPathNormalizer_pos _ s a i j b

theorem followupCavityTreeExpectation_eq_interpolation (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc 0 1) (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ)
    (u : ℝ) (hu : u∈Icc 0 1) :
    (∫σ,F σ∂anisotropicFiniteTreeLaw (followupCavitySpinModel n β ρ hβ hρ u hu) s a (asGenealogy T))=
      cavityInterpolationMarkedExpectation
        (followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩)
        (cavityIncidentRootMask n) s a (Fin.last n) (trimRoot T)
        (fun σ=>F (trimmedSpinEquiv (S:=Configuration (n+1)) T
          (terminalSampleEquiv (S:=Configuration (n+1)) (trimRoot T) σ)))
        u (followupCavityB n β ρ u) := by
  classical
  let e := (terminalSampleEquiv (S:=Configuration (n+1)) (trimRoot T)).trans
    (trimmedSpinEquiv (S:=Configuration (n+1)) T)
  have hF : Measurable F := by
    have h := (measurable_of_countable (F ∘ e)).comp e.symm.measurable
    simpa only [Function.comp_assoc, MeasurableEquiv.self_comp_symm, Function.comp_id] using h
  let D:=followupCavitySpinModel n β ρ hβ hρ u hu
  have hm:=anisotropicTrimmedRecordedTreeLaw_spin_marginal D s a hq T
  have hi:=integral_map (μ:=anisotropicTrimmedRecordedTreeLaw D s a T)
    ((trimmedSpinEquiv (S:=Configuration (n+1)) T).measurable.comp
      ((measurable_spins (trimRoot T)).comp measurable_snd)).aemeasurable
      hF.aestronglyMeasurable
  have hi' : (∫y,F y∂anisotropicFiniteTreeLaw D s a (asGenealogy T))=
      ∫p,F (trimmedSpinEquiv (S:=Configuration (n+1)) T (spins (trimRoot T) p.2))
        ∂anisotropicTrimmedRecordedTreeLaw D s a T := by
    calc
      _ = ∫y,F y∂Measure.map (fun z=>trimmedSpinEquiv (S:=Configuration (n+1)) T
          (spins (trimRoot T) z.2)) (anisotropicTrimmedRecordedTreeLaw D s a T) :=
        congrArg (fun P=>∫y,F y∂P) hm.symm
      _ = _ := hi
  change (∫y,F y∂anisotropicFiniteTreeLaw D s a (asGenealogy T))=_
  rw [hi']
  unfold cavityInterpolationMarkedExpectation cavityPathMarkedExpectation anisotropicTrimmedRecordedTreeLaw
  have hD:=followupCavitySpinModel_eq_scaled_root_and_path n β ρ hβ hρ u hu
  have hR:=anisotropicRootEnergyMap_replaceVariance
    (anisotropicScaleRootCouplings (followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩)
      (cavityIncidentRootMask n) u) (Fin.last n) (followupCavityB n β ρ u)
  dsimp only [D] at *
  rw [hD,hR]
  apply integral_congr_ae
  exact .of_forall fun p=>by
    dsimp only
    rw [terminalSampleEquiv_recordSpins]

end QuantitativeFollowup
