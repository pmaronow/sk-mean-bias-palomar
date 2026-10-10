module
public import QuantitativeFollowup.FollowupCavityCrossGraftResponse

@[expose] public section

/-! One fresh continuation mark is a literal spin of the enlarged tree.
All fixed tests of the old terminal spins and the fresh mark retain the
closed physical streaming derivative, including its zero endpoint. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1700000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavitySingleGraftSampleObservable (T : FiniteTerminalGenealogy (k+2))
    (v : FiniteCascadeRecordVertex (trimRoot T))
    (H : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T)) ×
      Configuration (n+1) → ℝ)
    (σ : FiniteCascadeGenealogy.Samples (Configuration (n+1))
      (asGenealogy (.advance (finiteCascadeVertexGraft v)))) : ℝ :=
  H (finiteCascadeGraftSpinExtract v σ)

theorem measurable_cavitySamplePairTest {j : ℕ} (T : FiniteTerminalGenealogy j)
    (H : FiniteCascadeGenealogy.Samples (Configuration n) (asGenealogy T) × Configuration n → ℝ) :
    Measurable H := by
  let e := (terminalSampleEquiv (S:=Configuration n) T).prodCongr (MeasurableEquiv.refl (Configuration n))
  have hh := (measurable_of_finite (H ∘ e)).comp e.symm.measurable
  simpa only [Function.comp_assoc,MeasurableEquiv.self_comp_symm,Function.comp_id] using hh

theorem cavitySingleGraftSampleObservable_record
    (T : FiniteTerminalGenealogy (k+2)) (v : FiniteCascadeRecordVertex (trimRoot T))
    (H : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T)) ×
      Configuration (n+1) → ℝ)
    (r : CavityPathRecordSpace (finiteCascadeVertexGraft v) (n+1)) :
    followupCavityPhysicalRecordObservable n (.advance (finiteCascadeVertexGraft v))
      (cavitySingleGraftSampleObservable T v H) r=
      H (spins (trimRoot T) (finiteCascadeGraftRecordExtract v r.2).1,
        (finiteCascadeGraftRecordExtract v r.2).2) := by
  change H (finiteCascadeGraftSpinExtract v (spins (finiteCascadeVertexGraft v) r.2))=_
  rw [finiteCascadeGraftRecordExtract_spins]

theorem followupCavitySingleGraftExpectation_eq_marked
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0) (T : FiniteTerminalGenealogy (k+2))
    (v : FiniteCascadeRecordVertex (trimRoot T))
    (H : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T)) ×
      Configuration (n+1) → ℝ)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    followupCavityPhysicalExpectation n β ρ hβ hρ s a (.advance (finiteCascadeVertexGraft v))
      (cavitySingleGraftSampleObservable T v H) u=
      ∫z,H (spins (trimRoot T) z.1.2,z.2)
        ∂anisotropicSingleVertexMarkedLaw (followupCavitySpinModel n β ρ hβ hρ u hu) s a T v := by
  rw [followupCavityPhysicalExpectation_eq_record_integral n β ρ hβ hρ s a hq
    (.advance (finiteCascadeVertexGraft v)) _ u hu,←anisotropicSingleVertexMarkedLaw_eq_graft]
  have hH := measurable_cavitySamplePairTest (trimRoot T) H
  have hG : Measurable (fun z : CavityPathRecordSpace (trimRoot T) (n+1) × Configuration (n+1) =>
      H (spins (trimRoot T) z.1.2,z.2)) :=
    hH.comp (((measurable_spins (trimRoot T)).comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
  have hm : Measurable (fun z : CavityPathRecordSpace (finiteCascadeVertexGraft v) (n+1) =>
      ((z.1,(finiteCascadeGraftRecordExtract v z.2).1),(finiteCascadeGraftRecordExtract v z.2).2)) :=
    (measurable_fst.prodMk ((measurable_finiteCascadeGraftRecordExtract v).fst.comp measurable_snd)).prodMk
      ((measurable_finiteCascadeGraftRecordExtract v).snd.comp measurable_snd)
  rw [integral_map hm.aemeasurable hG.aestronglyMeasurable]
  apply integral_congr_ae
  exact .of_forall fun r => cavitySingleGraftSampleObservable_record T v H r

theorem hasDerivWithinAt_followupCavitySingleGraftExpectation
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (v : FiniteCascadeRecordVertex (trimRoot T))
    (H : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T)) ×
      Configuration (n+1) → ℝ)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (followupCavityPhysicalExpectation n β ρ hβ hρ s a
      (.advance (finiteCascadeVertexGraft v)) (cavitySingleGraftSampleObservable T v H))
      (followupCavityAlpha n β ρ/2*cavityMarkedSixExpectation
        (followupCavitySpinModel n β ρ hβ hρ u hu) s a (.advance (finiteCascadeVertexGraft v))
        (followupCavityPhysicalRecordObservable n (.advance (finiteCascadeVertexGraft v))
          (cavitySingleGraftSampleObservable T v H))) (Icc (0 : ℝ) 1) u :=
  hasDerivWithinAt_followupCavityPhysicalExpectation_six_terms_closed hn β ρ hβ hρ s a ha has hq
    (.advance (finiteCascadeVertexGraft v)) (cavitySingleGraftSampleObservable T v H) u hu

end QuantitativeFollowup
