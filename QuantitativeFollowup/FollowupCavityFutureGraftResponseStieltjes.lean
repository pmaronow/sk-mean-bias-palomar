module
public import QuantitativeFollowup.FollowupCavityFutureGraftResponse

@[expose] public section

/-! The strict-future Stieltjes term is a finite sum of true physical
graft expectations. Its second streaming passage follows from their
actual closed derivatives, including the zero-coupling endpoint. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def followupCavityFutureGraftStieltjesExpectation (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (s : RSBScheme k) (a : ℝ)
    (T : FiniteTerminalGenealogy (k+2)) (v : FiniteCascadeRecordVertex (trimRoot T))
    (F : TerminalSpins (Configuration (n+1)) (trimRoot T)→ℝ) (u : ℝ) : ℝ :=
  ∑i,vectorPosteriorFeatureWeight s a i*
    (if anisotropicVertexOverlap s v<vectorProfileAtom s i then
      followupCavityFutureGraftResponseExpectation n β ρ hβ hρ s a T v
        (vectorProfileAtom s i) F u else 0)

def followupCavityFutureGraftStieltjesResponse (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (v : FiniteCascadeRecordVertex (trimRoot T))
    (F : TerminalSpins (Configuration (n+1)) (trimRoot T)→ℝ) : ℝ :=
  ∑i,vectorPosteriorFeatureWeight s a i*
    (if anisotropicVertexOverlap s v<vectorProfileAtom s i then
      cavityMarkedSixExpectation D s a
        (.advance (finiteCascadeFutureVertexGraft v
          (cavityFiniteFutureDepth s v.depth (vectorProfileAtom s i))))
        (fun r=>cavityFutureGraftResponseTerminalObservable T v
          (cavityFiniteFutureDepth s v.depth (vectorProfileAtom s i)) (vectorProfileAtom s i) F
          (finiteCascadeRecordTerminalSpins _ r.2)) else 0)

theorem followupCavityFutureGraftStieltjesExpectation_eq_actual
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (v : FiniteCascadeRecordVertex (trimRoot T))
    (F : TerminalSpins (Configuration (n+1)) (trimRoot T)→ℝ)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    followupCavityFutureGraftStieltjesExpectation n β ρ hβ hρ s a T v F u=
      ∫r,F (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)*
        (∫q : Paper.Overlap,if anisotropicVertexOverlap s v<q then
          cavityFutureVertexConditionalDefect (followupCavitySpinModel n β ρ hβ hρ u hu) s v q r
          else 0∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a)
        ∂anisotropicTrimmedRecordedTreeLaw (followupCavitySpinModel n β ρ hβ hρ u hu) s a T := by
  classical
  let D:=followupCavitySpinModel n β ρ hβ hρ u hu
  let R:=fun r : CavityPathRecordSpace (trimRoot T) (n+1)=>
    F (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)
  have hR:=measurable_followupCavityPhysicalRecordObservable T (cavityFutureResponseSampleObservable T F)
  rw [cavityFutureResponseSampleObservable_record] at hR
  obtain ⟨C,hC,hRb⟩:=exists_followupCavityPhysicalRecordObservable_bound T (cavityFutureResponseSampleObservable T F)
  rw [cavityFutureResponseSampleObservable_record] at hRb
  have he (q : Paper.Overlap) :
      (∫z,R z.1*cavitySpinOverlapDefect n q z.2.1 z.2.2
        ∂anisotropicFutureVertexMarkedLaw D s a T v q)=
      followupCavityFutureGraftResponseExpectation n β ρ hβ hρ s a T v q F u := by
    exact (integral_anisotropicFutureVertexMarkedLaw_overlapDefect D s a T v q R hR C hC hRb).trans
      (followupCavityFutureGraftResponseExpectation_eq_conditional_integral β ρ hβ hρ s a hq T v q F u hu).symm
  rw [integral_cavityRecorded_vertex_futureFresh D s a ha has hq T v R hR C hC hRb,
    ←vectorProfileFreeMeasure_eq_actual_free s a ha has hq,
    integral_vectorProfileFreeMeasure s a has]
  simp_rw [he]
  rfl

theorem hasDerivWithinAt_followupCavityFutureGraftStieltjesExpectation
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (v : FiniteCascadeRecordVertex (trimRoot T))
    (F : TerminalSpins (Configuration (n+1)) (trimRoot T)→ℝ)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (followupCavityFutureGraftStieltjesExpectation n β ρ hβ hρ s a T v F)
      (followupCavityAlpha n β ρ/2*followupCavityFutureGraftStieltjesResponse
        (followupCavitySpinModel n β ρ hβ hρ u hu) s a T v F) (Icc (0:ℝ) 1) u := by
  classical
  unfold followupCavityFutureGraftStieltjesExpectation followupCavityFutureGraftStieltjesResponse
  rw [Finset.mul_sum]
  have hx (w x : ℝ) : followupCavityAlpha n β ρ/2*(w*x)=
      w*(followupCavityAlpha n β ρ/2*x):=by ring
  simp_rw [hx]
  apply HasDerivWithinAt.fun_sum
  intro i _
  by_cases hi:anisotropicVertexOverlap s v<vectorProfileAtom s i
  · simp only [ite_eq_left hi]
    exact (hasDerivWithinAt_followupCavityFutureGraftResponseExpectation hn β ρ hβ hρ
      s a ha has hq T v (vectorProfileAtom s i) F u hu).const_mul _
  · simp only [ite_eq_right hi,mul_zero]
    exact hasDerivWithinAt_const u (Icc (0:ℝ) 1) 0

end QuantitativeFollowup
