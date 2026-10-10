module
public import QuantitativeFollowup.FollowupCavityNormalizerGraftResponseGeometry

@[expose] public section

/-! The normalizer's actual fresh binary defect is the expectation of a
fixed terminal-spin test on the original mesh, with a genuine closed
six-term streaming derivative. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityNormalizerGraftTerminalTest (s : RSBScheme k)
    (i : vectorPosteriorFeatureIndex k)
    (σ : TerminalSpins (Configuration (n+1)) (cavityNormalizerGraftPairTree i).tree) : ℝ :=
  cavitySpinOverlapDefect n (vectorProfileAtom s i)
    (observationTerminalSpin (cavityNormalizerGraftPairTree i).tree
      (observationPairFirstLeaf (cavityNormalizerGraftPairTree i)) σ)
    (observationTerminalSpin (cavityNormalizerGraftPairTree i).tree
      (observationPairSecondLeaf (cavityNormalizerGraftPairTree i)) σ)

def followupCavityNormalizerGraftPairExpectation (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (s : RSBScheme k) (a : ℝ)
    (i : vectorPosteriorFeatureIndex k) : ℝ→ℝ :=
  followupCavityPhysicalExpectation n β ρ hβ hρ s a (cavityNormalizerGraftTree i)
    (cavityFutureResponseSampleObservable _ (cavityNormalizerGraftTerminalTest s i))

def cavityNormalizerGraftPairResponse (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (i : vectorPosteriorFeatureIndex k) : ℝ :=
  cavityMarkedSixExpectation D s a (cavityNormalizerGraftTree i)
    (fun r=>cavityNormalizerGraftTerminalTest s i
      (finiteCascadeRecordTerminalSpins (cavityNormalizerGraftPairTree i).tree r.2))

theorem followupCavityNormalizerGraftPairExpectation_eq_actual
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0)
    (i : vectorPosteriorFeatureIndex k) (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    followupCavityNormalizerGraftPairExpectation n β ρ hβ hρ s a i u=
      ∫z,cavitySpinOverlapDefect n (vectorProfileAtom s i) z.2.1 z.2.2
        ∂anisotropicFreshTerminalPairLaw (followupCavitySpinModel n β ρ hβ hρ u hu)
          (Paper.parisiSchemeMeasure s) a (vectorProfileAtom s i) := by
  let D:=followupCavitySpinModel n β ρ hβ hρ u hu
  let T:=cavityNormalizerGraftTree i
  let B:=fun z : Configuration (n+1)×Configuration (n+1)=>
    cavitySpinOverlapDefect n (vectorProfileAtom s i) z.1 z.2
  let pair:=fun z : CavityPathRecordSpace T (n+1)=>
    (observationLeafSpin T (observationPairFirstLeaf (cavityNormalizerGraftPairTree i)) z.2,
      observationLeafSpin T (observationPairSecondLeaf (cavityNormalizerGraftPairTree i)) z.2)
  have hp : Measurable pair:=
    ((measurable_observationLeafSpin T _).comp measurable_snd).prodMk
      ((measurable_observationLeafSpin T _).comp measurable_snd)
  have hi:=integral_map (μ:=anisotropicFiniteRecordedTreeLaw D s a T)
    hp.aemeasurable (measurable_of_finite B).aestronglyMeasurable
  rw [cavityNormalizerGraftPair_law D s a i] at hi
  have hs : (∫z,B z.2∂anisotropicFreshTerminalPairLaw D (Paper.parisiSchemeMeasure s) a
      (vectorProfileAtom s i))=(∫z,B z∂(anisotropicFreshTerminalPairLaw D
        (Paper.parisiSchemeMeasure s) a (vectorProfileAtom s i)).snd) :=
    (integral_map measurable_snd.aemeasurable (measurable_of_finite B).aestronglyMeasurable).symm
  rw [hs,hi]
  change followupCavityPhysicalExpectation n β ρ hβ hρ s a T
    (cavityTerminalSampleObservable T (cavityNormalizerGraftTerminalTest s i)) u=_
  rw [followupCavityPhysicalExpectation_terminal_integral β ρ hβ hρ s a hq T _ u hu]
  apply integral_congr_ae
  exact .of_forall fun z=>by
    change cavityNormalizerGraftTerminalTest s i
      (finiteCascadeRecordTerminalSpins (cavityNormalizerGraftPairTree i).tree z.2.2)=
      cavitySpinOverlapDefect n (vectorProfileAtom s i)
        (observationLeafSpin (cavityNormalizerGraftPairTree i).tree
          (observationPairFirstLeaf (cavityNormalizerGraftPairTree i)) z.2.2)
        (observationLeafSpin (cavityNormalizerGraftPairTree i).tree
          (observationPairSecondLeaf (cavityNormalizerGraftPairTree i)) z.2.2)
    unfold cavityNormalizerGraftTerminalTest
    rw [observationTerminalSpin_record,observationTerminalSpin_record]

theorem hasDerivWithinAt_followupCavityNormalizerGraftPairExpectation
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (i : vectorPosteriorFeatureIndex k) (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (followupCavityNormalizerGraftPairExpectation n β ρ hβ hρ s a i)
      (followupCavityAlpha n β ρ/2*cavityNormalizerGraftPairResponse
        (followupCavitySpinModel n β ρ hβ hρ u hu) s a i) (Icc (0:ℝ) 1) u := by
  have hh:=hasDerivWithinAt_followupCavityPhysicalExpectation_six_terms_closed hn β ρ hβ hρ
    s a ha has hq (cavityNormalizerGraftTree i)
    (cavityFutureResponseSampleObservable _ (cavityNormalizerGraftTerminalTest s i)) u hu
  rw [cavityFutureResponseSampleObservable_record] at hh
  exact hh

end QuantitativeFollowup
