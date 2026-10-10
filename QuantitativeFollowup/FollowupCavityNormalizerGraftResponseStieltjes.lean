module
public import QuantitativeFollowup.FollowupCavityNormalizerGraftResponse

@[expose] public section

/-! The actual normalizer fresh-defect term and the independent-copy sixth
streaming term have genuine second closed streaming derivatives. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def followupCavityNormalizerGraftExpectation (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (s : RSBScheme k) (a : ℝ) (u : ℝ) : ℝ :=
  ∑i,vectorPosteriorFeatureWeight s a i*
    followupCavityNormalizerGraftPairExpectation n β ρ hβ hρ s a i u

def cavityNormalizerGraftStreamingResponse (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) : ℝ :=
  ∑i,vectorPosteriorFeatureWeight s a i*cavityNormalizerGraftPairResponse D s a i

theorem followupCavityNormalizerGraftExpectation_eq_actual
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    followupCavityNormalizerGraftExpectation n β ρ hβ hρ s a u=
      cavityNormalizerFreshDefect (followupCavitySpinModel n β ρ hβ hρ u hu)
        (Paper.parisiSchemeMeasure s) a := by
  unfold cavityNormalizerFreshDefect
  rw [←vectorProfileFreeMeasure_eq_actual_free s a ha has hq,
    integral_vectorProfileFreeMeasure s a has]
  simp_rw [←followupCavityNormalizerGraftPairExpectation_eq_actual β ρ hβ hρ s a hq _ u hu]
  rfl

theorem hasDerivWithinAt_followupCavityNormalizerGraftExpectation
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (followupCavityNormalizerGraftExpectation n β ρ hβ hρ s a)
      (followupCavityAlpha n β ρ/2*cavityNormalizerGraftStreamingResponse
        (followupCavitySpinModel n β ρ hβ hρ u hu) s a) (Icc (0:ℝ) 1) u := by
  classical
  unfold followupCavityNormalizerGraftExpectation cavityNormalizerGraftStreamingResponse
  rw [Finset.mul_sum]
  have he (w x : ℝ) : followupCavityAlpha n β ρ/2*(w*x)=
      w*(followupCavityAlpha n β ρ/2*x):=by ring
  simp_rw [he]
  apply HasDerivWithinAt.fun_sum
  intro i _
  exact (hasDerivWithinAt_followupCavityNormalizerGraftPairExpectation hn β ρ hβ hρ
    s a ha has hq i u hu).const_mul _

def followupCavitySixthGraftExpectation (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (s : RSBScheme k) (a : ℝ)
    (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ) (u : ℝ) : ℝ :=
  a*followupCavityPhysicalExpectation n β ρ hβ hρ s a T F u*
    followupCavityNormalizerGraftExpectation n β ρ hβ hρ s a u

theorem followupCavitySixthGraftExpectation_eq_actual
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    followupCavitySixthGraftExpectation n β ρ hβ hρ s a T F u=
      a*(∫r,followupCavityPhysicalRecordObservable n T F r
        ∂anisotropicTrimmedRecordedTreeLaw (followupCavitySpinModel n β ρ hβ hρ u hu) s a T)*
        cavityNormalizerFreshDefect (followupCavitySpinModel n β ρ hβ hρ u hu)
          (Paper.parisiSchemeMeasure s) a := by
  rw [followupCavitySixthGraftExpectation,
    followupCavityPhysicalExpectation_eq_record_integral n β ρ hβ hρ s a hq T F u hu,
    followupCavityNormalizerGraftExpectation_eq_actual β ρ hβ hρ s a ha has hq u hu]

theorem hasDerivWithinAt_followupCavitySixthGraftExpectation
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    let D:=followupCavitySpinModel n β ρ hβ hρ u hu
    HasDerivWithinAt (followupCavitySixthGraftExpectation n β ρ hβ hρ s a T F)
      (a*(followupCavityAlpha n β ρ/2)*
        (cavityMarkedSixExpectation D s a T (followupCavityPhysicalRecordObservable n T F)*
          cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a+
          (∫r,followupCavityPhysicalRecordObservable n T F r
            ∂anisotropicTrimmedRecordedTreeLaw D s a T)*cavityNormalizerGraftStreamingResponse D s a))
      (Icc (0:ℝ) 1) u := by
  dsimp only
  have hF:=hasDerivWithinAt_followupCavityPhysicalExpectation_six_terms_closed hn β ρ hβ hρ
    s a ha has hq T F u hu
  have hN:=hasDerivWithinAt_followupCavityNormalizerGraftExpectation hn β ρ hβ hρ s a ha has hq u hu
  have hh:=(hF.const_mul a).fun_mul hN
  rw [followupCavityNormalizerGraftExpectation_eq_actual β ρ hβ hρ s a ha.1 has hq u hu,
    followupCavityPhysicalExpectation_eq_record_integral n β ρ hβ hρ s a hq T F u hu] at hh
  convert! hh using 1
  ring

end QuantitativeFollowup
