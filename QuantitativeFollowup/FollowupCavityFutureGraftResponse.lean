module
public import QuantitativeFollowup.FollowupCavityFutureGraftResponseGeometry
public import QuantitativeFollowup.FollowupCavitySixTermEndpoints

@[expose] public section

/-! The literal conditional strict-future response is an expectation of
a fixed terminal-spin test on the actual enlarged finite tree. Its genuine
closed-interval six-term derivative is therefore available for iteration. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityFutureResponseSampleObservable (T : FiniteTerminalGenealogy (k+2))
    (F : TerminalSpins (Configuration (n+1)) (trimRoot T)→ℝ)
    (σ : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)) : ℝ :=
  F ((terminalSampleEquiv (S:=Configuration (n+1)) (trimRoot T)).symm
    ((trimmedSpinEquiv (S:=Configuration (n+1)) T).symm σ))

theorem cavityFutureResponseSampleObservable_record
    (T : FiniteTerminalGenealogy (k+2))
    (F : TerminalSpins (Configuration (n+1)) (trimRoot T)→ℝ) :
    followupCavityPhysicalRecordObservable n T (cavityFutureResponseSampleObservable T F)=
      fun r=>F (finiteCascadeRecordTerminalSpins (trimRoot T) r.2) := by
  funext r
  unfold followupCavityPhysicalRecordObservable cavityFutureResponseSampleObservable
  rw [(trimmedSpinEquiv (S:=Configuration (n+1)) T).symm_apply_apply,
    ←terminalSampleEquiv_recordSpins,
    (terminalSampleEquiv (S:=Configuration (n+1)) (trimRoot T)).symm_apply_apply]

def cavityFutureGraftResponseTerminalObservable
    (T : FiniteTerminalGenealogy (k+2)) (v : FiniteCascadeRecordVertex (trimRoot T))
    (p : ℕ) (q : Paper.Overlap)
    (F : TerminalSpins (Configuration (n+1)) (trimRoot T)→ℝ)
    (σ : TerminalSpins (Configuration (n+1)) (finiteCascadeFutureVertexGraft v p)) : ℝ :=
  let e:=cavityFutureGraftTerminalExtract v p σ
  F e.1*cavitySpinOverlapDefect n q e.2.1 e.2.2

def followupCavityFutureGraftResponseExpectation (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (s : RSBScheme k) (a : ℝ)
    (T : FiniteTerminalGenealogy (k+2)) (v : FiniteCascadeRecordVertex (trimRoot T))
    (q : Paper.Overlap) (F : TerminalSpins (Configuration (n+1)) (trimRoot T)→ℝ) : ℝ→ℝ :=
  followupCavityPhysicalExpectation n β ρ hβ hρ s a
    (.advance (finiteCascadeFutureVertexGraft v (cavityFiniteFutureDepth s v.depth q)))
    (cavityFutureResponseSampleObservable _
      (cavityFutureGraftResponseTerminalObservable T v (cavityFiniteFutureDepth s v.depth q) q F))

theorem followupCavityFutureGraftResponseExpectation_eq_conditional_integral
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (v : FiniteCascadeRecordVertex (trimRoot T))
    (q : Paper.Overlap) (F : TerminalSpins (Configuration (n+1)) (trimRoot T)→ℝ)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    followupCavityFutureGraftResponseExpectation n β ρ hβ hρ s a T v q F u=
      ∫r,F (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)*
        cavityFutureVertexConditionalDefect (followupCavitySpinModel n β ρ hβ hρ u hu) s v q r
        ∂anisotropicTrimmedRecordedTreeLaw (followupCavitySpinModel n β ρ hβ hρ u hu) s a T := by
  classical
  let D:=followupCavitySpinModel n β ρ hβ hρ u hu
  let p:=cavityFiniteFutureDepth s v.depth q
  let e:=finiteCascadeFutureGraftExtract (E:=FiniteStateField (Configuration (n+1)))
    (S:=Configuration (n+1)) v p
  let φ:=fun z : CavityPathRecordSpace (finiteCascadeFutureVertexGraft v p) (n+1)=>
    ((z.1,(e z.2).1),(e z.2).2)
  let R:=fun r : CavityPathRecordSpace (trimRoot T) (n+1)=>
    F (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)
  let H:=fun z : CavityPathRecordSpace (trimRoot T) (n+1)×(Configuration (n+1)×Configuration (n+1))=>
    R z.1*cavitySpinOverlapDefect n q z.2.1 z.2.2
  have hR : Measurable R := (measurable_of_finite F).comp
    ((measurable_finiteCascadeRecordTerminalSpins (trimRoot T)).comp measurable_snd)
  let C:=∑σ,|F σ|
  have hC : 0≤C:=Finset.sum_nonneg (fun _ _=>abs_nonneg _)
  have hRb (r) : |R r|≤C:=by
    change |F (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)|≤∑σ,|F σ|
    exact Finset.single_le_sum (f:=fun σ=>|F σ|) (fun _ _=>abs_nonneg _) (Finset.mem_univ _)
  have he:=measurable_finiteCascadeFutureGraftExtract
    (E:=FiniteStateField (Configuration (n+1))) (S:=Configuration (n+1)) v p
  have hφ : Measurable φ:=
    (measurable_fst.prodMk (he.fst.comp measurable_snd)).prodMk (he.snd.comp measurable_snd)
  have hH : Measurable H := (hR.comp measurable_fst).mul
    ((measurable_of_finite (fun z : Configuration (n+1)×Configuration (n+1)=>
      cavitySpinOverlapDefect n q z.1 z.2)).comp measurable_snd)
  have hm : (anisotropicTrimmedRecordedTreeLaw D s a
      (.advance (finiteCascadeFutureVertexGraft v p))).map φ=
      anisotropicFutureVertexMarkedLaw D s a T v q:=anisotropicFutureVertexMarkedLaw_eq_graft D s a T v q
  have hi:=integral_map (μ:=anisotropicTrimmedRecordedTreeLaw D s a
    (.advance (finiteCascadeFutureVertexGraft v p))) hφ.aemeasurable hH.aestronglyMeasurable
  rw [hm] at hi
  rw [followupCavityFutureGraftResponseExpectation,
    followupCavityPhysicalExpectation_eq_record_integral n β ρ hβ hρ s a hq _ _ u hu,
    cavityFutureResponseSampleObservable_record]
  rw [←integral_anisotropicFutureVertexMarkedLaw_overlapDefect D s a T v q R hR C hC hRb,hi]
  apply integral_congr_ae
  exact .of_forall fun z=>by
    dsimp only [H,φ,R,e,cavityFutureGraftResponseTerminalObservable]
    rw [cavityFutureGraftTerminalExtract_record]

theorem hasDerivWithinAt_followupCavityFutureGraftResponseExpectation
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (v : FiniteCascadeRecordVertex (trimRoot T))
    (q : Paper.Overlap) (F : TerminalSpins (Configuration (n+1)) (trimRoot T)→ℝ)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (followupCavityFutureGraftResponseExpectation n β ρ hβ hρ s a T v q F)
      (followupCavityAlpha n β ρ/2*cavityMarkedSixExpectation
        (followupCavitySpinModel n β ρ hβ hρ u hu) s a
        (.advance (finiteCascadeFutureVertexGraft v (cavityFiniteFutureDepth s v.depth q)))
        (fun r=>cavityFutureGraftResponseTerminalObservable T v
          (cavityFiniteFutureDepth s v.depth q) q F
          (finiteCascadeRecordTerminalSpins _ r.2))) (Icc (0:ℝ) 1) u := by
  have hh:=hasDerivWithinAt_followupCavityPhysicalExpectation_six_terms_closed hn β ρ hβ hρ
    s a ha has hq (.advance (finiteCascadeFutureVertexGraft v (cavityFiniteFutureDepth s v.depth q)))
    (cavityFutureResponseSampleObservable _
      (cavityFutureGraftResponseTerminalObservable T v (cavityFiniteFutureDepth s v.depth q) q F)) u hu
  rw [cavityFutureResponseSampleObservable_record] at hh
  exact hh

end QuantitativeFollowup
