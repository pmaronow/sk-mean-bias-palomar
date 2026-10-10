module
public import QuantitativeFollowup.FollowupCavityMarkedFiveTerms
public import QuantitativeFollowup.FollowupCavityOriginalLeafPairs
public import QuantitativeFollowup.FollowupCavityDefectModel

@[expose] public section

/-! Genuine finite-profile physical streaming with all five retained-tree
terms represented by original leaves and fresh normalized continuation
marks. The centering term is kept explicit until the independent root
normalizer calculation identifies its sixth contribution. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

def cavityMarkedFiveExpectation (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) : ℝ :=
  (∫r,F r*cavityOriginalDistinctLeafDefect n s T r∂anisotropicTrimmedRecordedTreeLaw D s a T)-
    2*cavityOriginalFreshExpectation D s a T F+cavityFreshFreshExpectation D s a T F+
      cavityCurrentFreshExpectation D s a T F+cavityFutureFreshExpectation D s a T F

theorem integral_cavityRecordedStreamingDefect_eq_markedFive
    (D : AnisotropicSpinModel (n+1)) (hn : 0<n) (s : RSBScheme k) (a : ℝ)
    (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0) (T : FiniteTerminalGenealogy (k+2))
    (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) (hF : Measurable F)
    (C : ℝ) (hC : 0≤C) (hFb : ∀r,|F r|≤C) :
    (∫r,F r*cavityRecordedStreamingDefect n D s a T (D.variance (Fin.last n)) r
      ∂anisotropicTrimmedRecordedTreeLaw D s a T)=cavityMarkedFiveExpectation D s a T F := by
  rw [integral_cavityRecordedStreamingDefect_marked_five_terms D s a ha has hq T F hF C hC hFb]
  simp_rw [cavityRecordedOriginalOriginalDefect_eq_distinct_leaves D hn s T]
  rfl

theorem measurable_followupCavityPhysicalRecordObservable
    (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ) :
    Measurable (followupCavityPhysicalRecordObservable n T F) := by
  let e:=(terminalSampleEquiv (S:=Configuration (n+1)) (trimRoot T)).trans
    (trimmedSpinEquiv (S:=Configuration (n+1)) T)
  have hF : Measurable F := by
    have h:=(measurable_of_countable (F∘e)).comp e.symm.measurable
    simpa only [Function.comp_assoc,MeasurableEquiv.self_comp_symm,Function.comp_id] using h
  exact hF.comp ((trimmedSpinEquiv (S:=Configuration (n+1)) T).measurable.comp
    ((measurable_spins (trimRoot T)).comp measurable_snd))

theorem exists_followupCavityPhysicalRecordObservable_bound
    (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ) :
    ∃C,0≤C ∧ ∀r,|followupCavityPhysicalRecordObservable n T F r|≤C := by
  classical
  let G:=fun σ : TerminalSpins (Configuration (n+1)) (trimRoot T)=>
    F (trimmedSpinEquiv (S:=Configuration (n+1)) T
      (terminalSampleEquiv (S:=Configuration (n+1)) (trimRoot T) σ))
  refine ⟨∑σ,|G σ|,Finset.sum_nonneg (fun σ _=>abs_nonneg _),fun r=>?_⟩
  have he : followupCavityPhysicalRecordObservable n T F r=
      G (finiteCascadeRecordTerminalSpins (trimRoot T) r.2) := by
    dsimp only [followupCavityPhysicalRecordObservable,G]
    rw [terminalSampleEquiv_recordSpins]
  rw [he]
  exact Finset.single_le_sum (fun σ _=>abs_nonneg (G σ)) (Finset.mem_univ _)

theorem followupCavityPhysicalExpectation_eq_record_integral
    (n : ℕ) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc 0 1)
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0) (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ)
    (u : ℝ) (hu : u∈Icc 0 1) :
    followupCavityPhysicalExpectation n β ρ hβ hρ s a T F u=
      ∫r,followupCavityPhysicalRecordObservable n T F r
        ∂anisotropicTrimmedRecordedTreeLaw (followupCavitySpinModel n β ρ hβ hρ u hu) s a T := by
  let e:=(terminalSampleEquiv (S:=Configuration (n+1)) (trimRoot T)).trans
    (trimmedSpinEquiv (S:=Configuration (n+1)) T)
  have hF : Measurable F := by
    have h:=(measurable_of_countable (F∘e)).comp e.symm.measurable
    simpa only [Function.comp_assoc,MeasurableEquiv.self_comp_symm,Function.comp_id] using h
  rw [followupCavityPhysicalExpectation_eq_actual n β ρ hβ hρ s a hq T F u hu]
  rw [←anisotropicTrimmedRecordedTreeLaw_spin_marginal
    (followupCavitySpinModel n β ρ hβ hρ u hu) s a hq T]
  exact integral_map ((trimmedSpinEquiv (S:=Configuration (n+1)) T).measurable.comp
    ((measurable_spins (trimRoot T)).comp measurable_snd)).aemeasurable hF.aestronglyMeasurable

theorem integral_followupCavityPhysicalRecordScore_mul_eq_markedFive
    (n : ℕ) (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc 0 1)
    (s : RSBScheme k) (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (u : ℝ) (hu : u∈Icc 0 1)
    (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) (hF : Measurable F)
    (C : ℝ) (hC : 0≤C) (hFb : ∀r,|F r|≤C) :
    (∫r,F r*followupCavityPhysicalRecordScore n β ρ hβ hρ s a T u r
      ∂anisotropicTrimmedRecordedTreeLaw (followupCavitySpinModel n β ρ hβ hρ u hu) s a T)=
      (followupCavityAlpha n β ρ/2)*
        cavityMarkedFiveExpectation (followupCavitySpinModel n β ρ hβ hρ u hu) s a T F := by
  simp_rw [followupCavityPhysicalRecordScore_eq_actual_model_defect n hn β ρ hβ hρ s a ha has hq T u hu]
  have he (r) : F r*((followupCavityAlpha n β ρ/2)*cavityRecordedStreamingDefect n
      (followupCavitySpinModel n β ρ hβ hρ u hu) s a T
        ((followupCavitySpinModel n β ρ hβ hρ u hu).variance (Fin.last n)) r)=
      (followupCavityAlpha n β ρ/2)*(F r*cavityRecordedStreamingDefect n
        (followupCavitySpinModel n β ρ hβ hρ u hu) s a T
          ((followupCavitySpinModel n β ρ hβ hρ u hu).variance (Fin.last n)) r) := by ring
  simp_rw [he]
  rw [integral_const_mul,integral_cavityRecordedStreamingDefect_eq_markedFive
    (followupCavitySpinModel n β ρ hβ hρ u hu) hn s a ha has hq T F hF C hC hFb]

theorem hasDerivAt_followupCavityPhysicalExpectation_marked_covariance
    (n : ℕ) (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc 0 1)
    (s : RSBScheme k) (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ)
    (u : ℝ) (hu : u∈Ioc 0 1) :
    HasDerivAt (followupCavityPhysicalExpectation n β ρ hβ hρ s a T F)
      ((followupCavityAlpha n β ρ/2)*
        (cavityMarkedFiveExpectation (followupCavitySpinModel n β ρ hβ hρ u ⟨hu.1.le,hu.2⟩)
          s a T (followupCavityPhysicalRecordObservable n T F)-
          followupCavityPhysicalExpectation n β ρ hβ hρ s a T F u*
            cavityMarkedFiveExpectation (followupCavitySpinModel n β ρ hβ hρ u ⟨hu.1.le,hu.2⟩)
              s a T (fun _=>1))) u := by
  obtain ⟨C,hC,hFb⟩:=exists_followupCavityPhysicalRecordObservable_bound T F
  have h:=hasDerivAt_followupCavityPhysicalExpectation_recorded_covariance n β ρ hβ hρ s a T F u hu
  rw [integral_followupCavityPhysicalRecordScore_mul_eq_markedFive n hn β ρ hβ hρ s a ha has hq T u
    ⟨hu.1.le,hu.2⟩ (followupCavityPhysicalRecordObservable n T F)
      (measurable_followupCavityPhysicalRecordObservable T F) C hC hFb] at h
  have h1:=integral_followupCavityPhysicalRecordScore_mul_eq_markedFive n hn β ρ hβ hρ s a ha has hq T u
    ⟨hu.1.le,hu.2⟩ (fun _=>1) measurable_const 1 zero_le_one (fun _=>by simp)
  simp only [one_mul] at h1
  rw [h1] at h
  convert! h using 1
  ring

end QuantitativeFollowup
