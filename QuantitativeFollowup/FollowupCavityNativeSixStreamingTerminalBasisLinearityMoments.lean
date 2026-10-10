module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingTermwiseSecondBracket
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternMarkMeasurable
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternValueBounds
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingOriginFubini

@[expose] public section

/-! Finite terminal-basis recombination for actual marked moments. All
linearity comes from the probability integrals and fixed attachment weights. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private def deltaTest {S : Type*} (σ τ : S) : ℝ := by
  classical
  exact if τ=σ then 1 else 0

private theorem delta_expansion {S : Type*} [Fintype S] (F : S→ℝ) (τ : S) :
    F τ=∑σ : S,F σ*deltaTest σ τ := by
  classical
  simp [deltaTest,eq_comm]

private theorem old_test_integrable
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (G : TerminalSpins (Configuration (n+1)) T→ℝ) :
    Integrable (fun z=>G (finiteCascadeRecordTerminalSpins T z.2))
      (anisotropicRecordedProfileTreeLaw D μ a q T) := by
  classical
  apply (integrable_const (∑σ,|G σ|)).mono'
    ((measurable_of_finite G).comp
      ((measurable_finiteCascadeRecordTerminalSpins T).comp measurable_snd)).aestronglyMeasurable
  exact .of_forall fun z=>by
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (f:=fun σ=>|G σ|) (fun _ _=>abs_nonneg _) (Finset.mem_univ _)

private theorem old_test_basis
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F H : TerminalSpins (Configuration (n+1)) T→ℝ) :
    nativeStreamingOldTerminalExpectation D μ a q T (fun τ=>F τ*H τ)=
      ∑σ,F σ*nativeStreamingOldTerminalExpectation D μ a q T (fun τ=>deltaTest σ τ*H τ) := by
  classical
  unfold nativeStreamingOldTerminalExpectation
  calc
    _ = ∫z,∑σ,F σ*(deltaTest σ (finiteCascadeRecordTerminalSpins T z.2)*
        H (finiteCascadeRecordTerminalSpins T z.2))∂anisotropicRecordedProfileTreeLaw D μ a q T := by
      apply integral_congr_ae (.of_forall fun z=>?_)
      dsimp only
      rw [delta_expansion F,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro σ _
      ring
    _ = ∑σ,∫z,F σ*(deltaTest σ (finiteCascadeRecordTerminalSpins T z.2)*
        H (finiteCascadeRecordTerminalSpins T z.2))∂anisotropicRecordedProfileTreeLaw D μ a q T :=
      integral_finsetSum _ (fun σ _=>old_test_integrable D μ a q T (fun τ=>F σ*(deltaTest σ τ*H τ)))
    _ = _ := by simp_rw [integral_const_mul]

private theorem mark_test_basis {k : ℕ} {A : Type} [Fintype A]
    [MeasurableSpace A] [TopologicalSpace A] [DiscreteTopology A]
    [BorelSpace A] [SecondCountableTopology A]
    (T : FiniteTerminalGenealogy J)
    (P : ProbabilityMeasure ((AnisotropicObservationState k×
      Records (AnisotropicObservationState k) (Configuration k) T)×A))
    (F : TerminalSpins (Configuration k) T→ℝ)
    (H : TerminalSpins (Configuration k) T×A→ℝ) :
    nativeStreamingTerminalMarkMoment P (fun z=>F z.1*H z)=
      ∑σ,F σ*nativeStreamingTerminalMarkMoment P (fun z=>deltaTest σ z.1*H z) := by
  classical
  unfold nativeStreamingTerminalMarkMoment
  calc
    _ = ∫z,∑σ,F σ*(deltaTest σ (finiteCascadeRecordTerminalSpins T z.1.2)*
        H (finiteCascadeRecordTerminalSpins T z.1.2,z.2))∂(P:Measure ((AnisotropicObservationState k×Records (AnisotropicObservationState k) (Configuration k) T)×A)) := by
      apply integral_congr_ae (.of_forall fun z=>?_)
      dsimp only
      rw [delta_expansion F,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro σ _
      ring
    _ = ∑σ,∫z,F σ*(deltaTest σ (finiteCascadeRecordTerminalSpins T z.1.2)*
        H (finiteCascadeRecordTerminalSpins T z.1.2,z.2))∂(P:Measure ((AnisotropicObservationState k×Records (AnisotropicObservationState k) (Configuration k) T)×A)) :=
      integral_finsetSum _ (fun σ _=>integrable_nativeStreamingTerminalMarkTest P (fun z=>F σ*(deltaTest σ z.1*H z)))
    _ = _ := by simp_rw [integral_const_mul]

theorem nativeStreamingPatternMoment_terminal_basis
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (P : NativeStreamingAttachmentPattern T) :
    nativeStreamingPatternMoment D μ a q T F P=
      ∑σ,F σ*nativeStreamingPatternMoment D μ a q T
        (fun τ=>if τ=σ then 1 else 0) P := by
  classical
  cases P with
  | original i k =>
      by_cases hik : i=k
      · simp only [nativeStreamingPatternMoment,hik,ite_true,mul_zero,Finset.sum_const_zero]
      · simp only [nativeStreamingPatternMoment,if_neg hik]
        have hh := old_test_basis D μ a q T F (fun τ=>cavitySpinOverlapDefect n
          (q (observationCommonLevel T i k)) (observationTerminalSpin T i τ)
            (observationTerminalSpin T k τ))
        simpa only [nativeStreamingOldTerminalExpectation,observationTerminalSpin_record,deltaTest] using hh
  | originalFresh i o =>
      simpa only [nativeStreamingPatternMoment,nativeStreamingTerminalMarkMoment,nativeStreamingOriginalFreshSpinTest,deltaTest] using
        mark_test_basis T (nativeStreamingOriginSingleProbability D μ a q T o) F
          (fun z=>cavitySpinOverlapDefect n
            (nativeStreamingOriginCommonClock q T (.vertex (observationLeafVertex T i)) o)
            (observationTerminalSpin T i z.1) z.2)
  | cross o p =>
      simpa only [nativeStreamingPatternMoment,nativeStreamingTerminalMarkMoment,nativeStreamingDefectSpinTest,deltaTest] using
        mark_test_basis T (nativeStreamingOriginCrossProbability D μ a q T o p) F
          (fun z=>cavitySpinOverlapDefect n (nativeStreamingOriginCommonClock q T o p) z.2.1 z.2.2)
  | current o =>
      simpa only [nativeStreamingPatternMoment,nativeStreamingTerminalMarkMoment,nativeStreamingDefectSpinTest,deltaTest] using
        mark_test_basis T (nativeStreamingOriginCurrentProbability D μ a q T o) F
          (fun z=>cavitySpinOverlapDefect n (nativeStreamingOriginLevel q o) z.2.1 z.2.2)
  | future o j l =>
      simpa only [nativeStreamingPatternMoment,nativeStreamingTerminalMarkMoment,nativeStreamingDefectSpinTest,deltaTest] using
        mark_test_basis T (nativeStreamingOriginFutureProbability D μ a q T o j l) F
          (fun z=>cavitySpinOverlapDefect n l z.2.1 z.2.2)
  | normalizer l =>
      have hh := old_test_basis D μ a q T F (fun _=>1)
      simp only [mul_one] at hh
      simp only [nativeStreamingPatternMoment]
      rw [hh,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro σ _
      simp only [deltaTest]
      ring

theorem nativeStreamingOriginWeightIntegral_sum
    {I : Type*} [Fintype I]
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (incoming : ℝ)
    (Φ : I→NativeStreamingOrigin T→ℝ)
    (hi : ∀i e,Integrable (fun r=>Φ i (.edge e r))
      ((parisiFreeMeasure μ a).restrict (Ioc (q (e.depth+1)) (q e.depth)))) :
    nativeStreamingOriginWeightIntegral μ a q T incoming (fun o=>∑i,Φ i o)=
      ∑i,nativeStreamingOriginWeightIntegral μ a q T incoming (Φ i) := by
  classical
  induction T generalizing incoming with
  | leaf => simp only [nativeStreamingOriginWeightIntegral,Finset.mul_sum]
  | @advance j T ih =>
      change nativeStreamingOriginWeightIntegral μ a q T (Paper.parisiCDF μ (q j))
        (fun o=>∑i,Φ i (nativeStreamingOriginChild o))+
        (∫r in Ioc (q (j+1)) (q j),∑i,Φ i (.edge (.here T) r)∂parisiFreeMeasure μ a)+
        (Paper.parisiCDF μ (q (j+1))-incoming)*(∑i,Φ i (.vertex (.root T.advance)))=_
      rw [ih _ _ (fun i e=>hi i (.child e)),integral_finsetSum _ (fun i _=>hi i (.here T))]
      simp only [nativeStreamingOriginWeightIntegral,Finset.mul_sum,Finset.sum_add_distrib]
  | @fork j T U ihT ihU =>
      change nativeStreamingOriginWeightIntegral μ a q T (Paper.parisiCDF μ (q j))
        (fun o=>∑i,Φ i (nativeStreamingOriginLeft o))+
        nativeStreamingOriginWeightIntegral μ a q U (Paper.parisiCDF μ (q j))
        (fun o=>∑i,Φ i (nativeStreamingOriginRight o))+
        (2*Paper.parisiCDF μ (q j)-incoming)*(∑i,Φ i (.vertex (.root (.fork T U))))=_
      rw [ihT _ _ (fun i e=>hi i (.left e)),ihU _ _ (fun i e=>hi i (.right e))]
      simp only [nativeStreamingOriginWeightIntegral,Finset.mul_sum,Finset.sum_add_distrib]

theorem nativeStreamingOriginWeightIntegral_congr_ae_edges
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (incoming : ℝ)
    (Φ Ψ : NativeStreamingOrigin T→ℝ)
    (hV : ∀v,Φ (.vertex v)=Ψ (.vertex v))
    (hE : ∀e, (fun r=>Φ (.edge e r))=ᵐ[(parisiFreeMeasure μ a).restrict
      (Ioc (q (e.depth+1)) (q e.depth))](fun r=>Ψ (.edge e r))) :
    nativeStreamingOriginWeightIntegral μ a q T incoming Φ=
      nativeStreamingOriginWeightIntegral μ a q T incoming Ψ := by
  induction T generalizing incoming with
  | leaf => simp only [nativeStreamingOriginWeightIntegral,hV]
  | @advance j T ih =>
      change nativeStreamingOriginWeightIntegral μ a q T (Paper.parisiCDF μ (q j))
        (fun o=>Φ (nativeStreamingOriginChild o))+
        (∫r in Ioc (q (j+1)) (q j),Φ (.edge (.here T) r)∂parisiFreeMeasure μ a)+
        (Paper.parisiCDF μ (q (j+1))-incoming)*Φ (.vertex (.root T.advance))=_
      rw [ih (Paper.parisiCDF μ (q j)) (fun o=>Φ (nativeStreamingOriginChild o))
        (fun o=>Ψ (nativeStreamingOriginChild o)) (fun v=>hV (.child v)) (fun e=>hE (.child e)),
        integral_congr_ae (hE (.here T)),hV (.root T.advance)]
  | @fork j T U ihT ihU =>
      change nativeStreamingOriginWeightIntegral μ a q T (Paper.parisiCDF μ (q j))
        (fun o=>Φ (nativeStreamingOriginLeft o))+
        nativeStreamingOriginWeightIntegral μ a q U (Paper.parisiCDF μ (q j))
        (fun o=>Φ (nativeStreamingOriginRight o))+
        (2*Paper.parisiCDF μ (q j)-incoming)*Φ (.vertex (.root (.fork T U)))=_
      rw [ihT (Paper.parisiCDF μ (q j)) (fun o=>Φ (nativeStreamingOriginLeft o))
        (fun o=>Ψ (nativeStreamingOriginLeft o)) (fun v=>hV (.left v)) (fun e=>hE (.left e)),
        ihU (Paper.parisiCDF μ (q j)) (fun o=>Φ (nativeStreamingOriginRight o))
        (fun o=>Ψ (nativeStreamingOriginRight o)) (fun v=>hV (.right v)) (fun e=>hE (.right e)),hV (.root (.fork T U))]

end QuantitativeFollowup
