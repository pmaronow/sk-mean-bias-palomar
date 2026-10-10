module
public import QuantitativeFollowup.FollowupCavityVertexGraftLaw
public import QuantitativeFollowup.FollowupCavitySixTermEndpoints

@[expose] public section

/-! A fixed terminal test with two actual fresh continuation marks is a
fixed spin test of the genuine enlarged genealogy. Its physical closed
six-term derivative therefore follows without a conditional response
assumption. Coincident graft sites are retained. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityCrossGraftSampleObservable (T : FiniteTerminalGenealogy (k+2))
    (v w : FiniteCascadeRecordVertex (trimRoot T)) (q : Paper.Overlap)
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T)) → ℝ)
    (σ : FiniteCascadeGenealogy.Samples (Configuration (n+1))
      (asGenealogy (.advance (finiteCascadeCrossVertexGraft v w)))) : ℝ :=
  let z := finiteCascadeCrossGraftSpinExtract v w σ
  F z.1*cavitySpinOverlapDefect n q z.2.1 z.2.2

theorem measurable_cavitySampleTest {j : ℕ} (T : FiniteTerminalGenealogy j)
    (F : FiniteCascadeGenealogy.Samples (Configuration n) (asGenealogy T) → ℝ) :
    Measurable F := by
  let e := terminalSampleEquiv (S:=Configuration n) T
  have hh := (measurable_of_finite (F ∘ e)).comp e.symm.measurable
  simpa only [Function.comp_assoc,MeasurableEquiv.self_comp_symm,Function.comp_id] using hh

theorem cavityCrossGraftSampleObservable_record
    (T : FiniteTerminalGenealogy (k+2)) (v w : FiniteCascadeRecordVertex (trimRoot T))
    (q : Paper.Overlap)
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T)) → ℝ)
    (r : CavityPathRecordSpace (finiteCascadeCrossVertexGraft v w) (n+1)) :
    followupCavityPhysicalRecordObservable n (.advance (finiteCascadeCrossVertexGraft v w))
      (cavityCrossGraftSampleObservable T v w q F) r=
      F (spins (trimRoot T) (finiteCascadeCrossGraftExtract v w r.2).1)*
        cavitySpinOverlapDefect n q (finiteCascadeCrossGraftExtract v w r.2).2.1
          (finiteCascadeCrossGraftExtract v w r.2).2.2 := by
  change F (finiteCascadeCrossGraftSpinExtract v w (spins (finiteCascadeCrossVertexGraft v w) r.2)).1*
    cavitySpinOverlapDefect n q
      (finiteCascadeCrossGraftSpinExtract v w (spins (finiteCascadeCrossVertexGraft v w) r.2)).2.1
      (finiteCascadeCrossGraftSpinExtract v w (spins (finiteCascadeCrossVertexGraft v w) r.2)).2.2=_
  rw [finiteCascadeCrossGraftRecordExtract_spins]

theorem followupCavityCrossGraftExpectation_eq_marked
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0) (T : FiniteTerminalGenealogy (k+2))
    (v w : FiniteCascadeRecordVertex (trimRoot T)) (q : Paper.Overlap)
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T)) → ℝ)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    followupCavityPhysicalExpectation n β ρ hβ hρ s a
      (.advance (finiteCascadeCrossVertexGraft v w)) (cavityCrossGraftSampleObservable T v w q F) u=
      ∫z,F (spins (trimRoot T) z.1.2)*cavitySpinOverlapDefect n q z.2.1 z.2.2
        ∂anisotropicCrossVertexMarkedLaw (followupCavitySpinModel n β ρ hβ hρ u hu) s a T v w := by
  rw [followupCavityPhysicalExpectation_eq_record_integral n β ρ hβ hρ s a hq
    (.advance (finiteCascadeCrossVertexGraft v w)) _ u hu,
    ←anisotropicCrossVertexMarkedLaw_eq_graft]
  have hF := measurable_cavitySampleTest (trimRoot T) F
  have hG : Measurable (fun z : CavityPathRecordSpace (trimRoot T) (n+1) ×
      (Configuration (n+1) × Configuration (n+1)) =>
      F (spins (trimRoot T) z.1.2)*cavitySpinOverlapDefect n q z.2.1 z.2.2) :=
    (hF.comp ((measurable_spins (trimRoot T)).comp (measurable_snd.comp measurable_fst))).mul
      ((measurable_of_finite (fun p : Configuration (n+1) × Configuration (n+1) =>
        cavitySpinOverlapDefect n q p.1 p.2)).comp measurable_snd)
  have hm : Measurable (fun z : CavityPathRecordSpace (finiteCascadeCrossVertexGraft v w) (n+1) =>
      ((z.1,(finiteCascadeCrossGraftExtract v w z.2).1),(finiteCascadeCrossGraftExtract v w z.2).2)) :=
    (measurable_fst.prodMk ((measurable_finiteCascadeCrossGraftExtract v w).fst.comp measurable_snd)).prodMk
      ((measurable_finiteCascadeCrossGraftExtract v w).snd.comp measurable_snd)
  rw [integral_map hm.aemeasurable hG.aestronglyMeasurable]
  apply integral_congr_ae
  exact .of_forall fun r => cavityCrossGraftSampleObservable_record T v w q F r

theorem hasDerivWithinAt_followupCavityCrossGraftExpectation
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (v w : FiniteCascadeRecordVertex (trimRoot T))
    (q : Paper.Overlap)
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T)) → ℝ)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (followupCavityPhysicalExpectation n β ρ hβ hρ s a
      (.advance (finiteCascadeCrossVertexGraft v w)) (cavityCrossGraftSampleObservable T v w q F))
      (followupCavityAlpha n β ρ/2*cavityMarkedSixExpectation
        (followupCavitySpinModel n β ρ hβ hρ u hu) s a (.advance (finiteCascadeCrossVertexGraft v w))
        (followupCavityPhysicalRecordObservable n (.advance (finiteCascadeCrossVertexGraft v w))
          (cavityCrossGraftSampleObservable T v w q F))) (Icc (0 : ℝ) 1) u :=
  hasDerivWithinAt_followupCavityPhysicalExpectation_six_terms_closed hn β ρ hβ hρ s a ha has hq
    (.advance (finiteCascadeCrossVertexGraft v w)) (cavityCrossGraftSampleObservable T v w q F) u hu

end QuantitativeFollowup
