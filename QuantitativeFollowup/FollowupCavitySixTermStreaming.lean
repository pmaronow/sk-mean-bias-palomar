module
public import QuantitativeFollowup.FollowupCavityNormalizerRecordedScore

@[expose] public section

/-! Literal six-term streaming for the actual finite cavity model. The
sixth term uses two independent fresh terminal marks under the genuine
arbitrary-profile process law; its coefficient is identified by the true
one-leaf normalizer, not by a score-centering premise. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

def cavityNormalizerFreshDefect (D:AnisotropicSpinModel (n+1))(μ:Paper.ParisiMeasure)(a:ℝ):ℝ:=
  ∫q : Paper.Overlap,∫z,cavitySpinOverlapDefect n q z.2.1 z.2.2
    ∂anisotropicFreshTerminalPairLaw D μ a q∂parisiFreeMeasure μ a

def cavityMarkedSixExpectation (D:AnisotropicSpinModel (n+1))(s:RSBScheme k)
    (a:ℝ)(T:FiniteTerminalGenealogy (k+2))(F:CavityPathRecordSpace (trimRoot T) (n+1)→ℝ):ℝ:=
  cavityMarkedFiveExpectation D s a T F+
    a*(∫r,F r∂anisotropicTrimmedRecordedTreeLaw D s a T)*
      cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a

theorem integral_followupCavityPhysicalRecordScore_normalizer
    (hn:0<n)(β ρ:ℝ)(hβ:0<β)(hρ:ρ∈Ioc (0:ℝ) 1)
    (s:RSBScheme k)(a:ℝ)(ha:a∈Icc (0:ℝ) 1)(has:a ≤ s.m 1)(hq:s.q 1=0)
    (T:FiniteTerminalGenealogy (k+2))(u:ℝ)(hu:u∈Ioc (0:ℝ) 1):
    let D:=followupCavitySpinModel n β ρ hβ hρ u ⟨hu.1.le,hu.2⟩
    (∫r,followupCavityPhysicalRecordScore n β ρ hβ hρ s a T u r
      ∂anisotropicTrimmedRecordedTreeLaw D s a T)=
      -a*followupCavityAlpha n β ρ/2*cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a:=by
  dsimp only
  exact (integral_followupCavityPhysicalRecordScore_eq_log_normalizer_derivative hn β ρ hβ hρ s a hq T u hu).unique
    (hasDerivAt_log_followupCavityRootPartition hn β ρ hβ hρ (Paper.parisiSchemeMeasure s) a ha
      (parisiSchemeMeasure_mem_scalarFloor s a ha.1 has hq) u hu)

theorem hasDerivAt_followupCavityPhysicalExpectation_six_terms
    (hn:0<n)(β ρ:ℝ)(hβ:0<β)(hρ:ρ∈Ioc (0:ℝ) 1)
    (s:RSBScheme k)(a:ℝ)(ha:a∈Icc (0:ℝ) 1)(has:a ≤ s.m 1)(hq:s.q 1=0)
    (T:FiniteTerminalGenealogy (k+2))
    (F:FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ)
    (u:ℝ)(hu:u∈Ioc (0:ℝ) 1):
    HasDerivAt (followupCavityPhysicalExpectation n β ρ hβ hρ s a T F)
      (followupCavityAlpha n β ρ/2*
        cavityMarkedSixExpectation (followupCavitySpinModel n β ρ hβ hρ u ⟨hu.1.le,hu.2⟩)
          s a T (followupCavityPhysicalRecordObservable n T F)) u:=by
  let D:=followupCavitySpinModel n β ρ hβ hρ u ⟨hu.1.le,hu.2⟩
  have hd:=hasDerivAt_followupCavityPhysicalExpectation_marked_covariance n hn β ρ hβ hρ s a ha.1 has hq T F u hu
  have hN:=integral_followupCavityPhysicalRecordScore_normalizer hn β ρ hβ hρ s a ha has hq T u hu
  have hm:=integral_followupCavityPhysicalRecordScore_mul_eq_markedFive n hn β ρ hβ hρ s a ha.1 has hq T u
    ⟨hu.1.le,hu.2⟩ (fun _=>1) measurable_const 1 zero_le_one (fun _=>by simp)
  simp only [one_mul] at hm
  have he:(followupCavityAlpha n β ρ/2)*cavityMarkedFiveExpectation D s a T (fun _=>1)=
      -a*followupCavityAlpha n β ρ/2*cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a:=
    hm.symm.trans hN
  have hi:=followupCavityPhysicalExpectation_eq_record_integral n β ρ hβ hρ s a hq T F u ⟨hu.1.le,hu.2⟩
  unfold cavityMarkedSixExpectation
  rw [←hi]
  convert! hd using 1
  have hx:=congrArg (fun z:ℝ=>followupCavityPhysicalExpectation n β ρ hβ hρ s a T F u*z) he
  nlinarith only [hx]

end QuantitativeFollowup
