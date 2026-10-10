module
public import QuantitativeFollowup.FollowupCavityDominatedPairIncrement
public import QuantitativeFollowup.FollowupCavityTerminalObservable
public import QuantitativeFollowup.FollowupCavityPairProductResponse
public import FourPapersCommon.FiniteObservationTrimLeafGeometry

@[expose] public section

/-! Deleting the zero root cell preserves the original terminal pair
test and its physical overlap clock. Thus the actual finite endpoint
increment applies directly to terminal observables of the full tree. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem observationLeafTerminalSpin_eq {S : Type} {j : ℕ}
    (T : FiniteTerminalGenealogy j) (i : ObservationLeaf T) (σ : TerminalSpins S T) :
    observationLeafTerminalSpin T i σ=observationTerminalSpin T i σ := by
  induction T with
  | leaf => rfl
  | advance T ih => exact ih i σ
  | fork T U ihT ihU => cases i with
    | inl i => exact ihT i σ.1
    | inr i => exact ihU i σ.2

theorem cavityProfileLevel_trim_clock (s : RSBScheme k) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (i l : ObservationLeaf T) :
    cavityProfileLevel s (observationCommonLevel (trimRoot T)
      (observationTrimLeaf T i) (observationTrimLeaf T l))=
      cavityProfileLevel s (observationCommonLevel T i l) := by
  apply Subtype.ext
  apply observationTrimLeaf_commonLevel_clock (fun d => (cavityProfileLevel s d : ℝ)) T
  simp only [cavityProfileLevel_coe_for_streaming]
  rw [show k+2-(k+2)=0 by omega,show k+2-(k+2-1)=1 by omega,s.q_zero,hq]

theorem cavityTerminalPairProduct_trim (s : RSBScheme k) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (i l : Fin 2 → ObservationLeaf T)
    (σ : TerminalSpins (Configuration (n+1)) (trimRoot T)) :
    cavityTerminalPairProduct s T i l
      ((terminalSampleEquiv (S:=Configuration (n+1)) T).symm
        (trimmedSpinEquiv (S:=Configuration (n+1)) T
          (terminalSampleEquiv (S:=Configuration (n+1)) (trimRoot T) σ)))=
      cavityTerminalPairProduct s (trimRoot T) (observationTrimLeaf T ∘ i)
        (observationTrimLeaf T ∘ l) σ := by
  have hs (j : ObservationLeaf T) := observationTrimLeaf_terminalSpin (S:=Configuration (n+1)) T j σ
  simp only [observationLeafTerminalSpin_eq] at hs
  simp only [cavityTerminalPairProduct,Function.comp_apply,hs,cavityProfileLevel_trim_clock s hq T]

theorem cavityTerminalSampleObservable_pair_domination (s : RSBScheme k) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (i l : Fin 2 → ObservationLeaf T)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (hdom : ∀σ, |F σ| ≤ |cavityTerminalPairProduct s T i l σ|)
    (z : CavityPathRecordSpace (trimRoot T) (n+1)) :
    |followupCavityPhysicalRecordObservable n T (cavityTerminalSampleObservable T F) z| ≤
      |cavityRecordedPairProduct s (trimRoot T) (observationTrimLeaf T ∘ i)
        (observationTrimLeaf T ∘ l) z| := by
  unfold followupCavityPhysicalRecordObservable cavityTerminalSampleObservable
  rw [←terminalSampleEquiv_recordSpins]
  have hh := hdom ((terminalSampleEquiv (S:=Configuration (n+1)) T).symm
    (trimmedSpinEquiv (S:=Configuration (n+1)) T
      (terminalSampleEquiv (S:=Configuration (n+1)) (trimRoot T)
        (finiteCascadeRecordTerminalSpins (trimRoot T) z.2))))
  rw [cavityTerminalPairProduct_trim s hq T i l] at hh
  simpa only [cavityTerminalPairProduct,cavityRecordedPairProduct,cavityRecordedLeafPairDefect,
    observationTerminalSpin_record,Function.comp_apply] using hh

theorem cavityFiniteRecorded_terminalPair_sub_le
    (hn : 0 < n) (β ρ : ℝ) (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (i l : Fin 2 → ObservationLeaf T)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (hdom : ∀σ, |F σ| ≤ |cavityTerminalPairProduct s T i l σ|)
    (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1)
    (x y : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    let D := followupCavitySpinModel n β ρ hβ hρ v hv
    |(∫z : CavityPathRecordSpace T (n+1),F (finiteCascadeRecordTerminalSpins T z.2)
        ∂anisotropicFiniteRecordedTreeLaw (followupCavitySpinModel n β ρ hβ hρ y hy) s a T)-
      (∫z : CavityPathRecordSpace T (n+1),F (finiteCascadeRecordTerminalSpins T z.2)
        ∂anisotropicFiniteRecordedTreeLaw (followupCavitySpinModel n β ρ hβ hρ x hx) s a T)| ≤
      (followupCavityAlpha n β ρ/2*(15*(FiniteCascadeGenealogy.leafCount (asGenealogy T) : ℝ)^2)*
        Real.exp (21*β^2)*(cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
          finiteCascadeUnweightedBranchSum (fun d => cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a
            (cavityProfileLevel s d)) T))*|y-x| := by
  dsimp only
  have hh := followupCavityPhysicalExpectation_dominatedPair_sub_le hn β ρ hβ hρ s a ha has hq T
    (observationTrimLeaf T ∘ i) (observationTrimLeaf T ∘ l) (cavityTerminalSampleObservable T F)
    (cavityTerminalSampleObservable_pair_domination s hq T i l F hdom) v hv x y hx hy
  rw [followupCavityPhysicalExpectation_terminal_integral β ρ hβ hρ s a hq T F y hy,
    followupCavityPhysicalExpectation_terminal_integral β ρ hβ hρ s a hq T F x hx] at hh
  dsimp only at hh
  have hc : cavityProfileLevel s (k+2)=cavityProfileLevel s (k+2-1) := by
    apply Subtype.ext
    simp only [cavityProfileLevel_coe_for_streaming]
    rw [show k+2-(k+2)=0 by omega,show k+2-(k+2-1)=1 by omega,s.q_zero,hq]
  rw [finiteCascadeUnweightedBranchSum_trimRoot _ T (congrArg
    (cavityCubicPairMoment (followupCavitySpinModel n β ρ hβ hρ v hv) (Paper.parisiSchemeMeasure s) a) hc)] at hh
  exact hh

end QuantitativeFollowup
