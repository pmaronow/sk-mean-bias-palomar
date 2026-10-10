module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternMoments
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingMovingTerminalMoments
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingCommonClockCoherence
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

@[expose] public section

/-! Actual finite-spin mark moments are coherent at fork roots. The proof
uses the unconditional continuation graft law, so it needs no monotonicity
or endpoint hypothesis on the observation schedule. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem nativeStreamingActualContinuationTerminalMoment_eq_integral
    {A : Type} [Fintype A] [MeasurableSpace A] [TopologicalSpace A]
    [DiscreteTopology A] [BorelSpace A] [SecondCountableTopology A]
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (U : (j : ℕ) → FiniteTerminalGenealogy j)
    (extract : (j : ℕ) → Records (AnisotropicObservationState n) (Configuration n) (U j) → A)
    (he : ∀ j, Measurable (extract j)) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex T) (G : TerminalSpins (Configuration n) T × A → ℝ) :
    nativeStreamingTerminalMarkMoment
      (nativeStreamingActualContinuationProbability D μ a q U extract T v) G =
      ∫ z, ∫ s, G (finiteCascadeRecordTerminalSpins T z.2, s)
        ∂((anisotropicRecordedProfileTreeKernel D μ q (U v.depth)).map (extract v.depth))
          (nativeStreamingVertexState v z.1 z.2)
        ∂anisotropicRecordedProfileTreeLaw D μ a q T := by
  let P := nativeStreamingActualContinuationProbability D μ a q U extract T v
  have hi := integrable_nativeStreamingTerminalMarkTest P G
  have hl : (P : Measure _) = nativeStreamingActualContinuationLaw D μ a q U extract T v := by
    change (anisotropicRecordedProfileTreeLaw D μ a q _).map _ = _
    exact nativeStreamingActualContinuationLaw_eq_graft D μ a q U extract he T v
  rw [hl] at hi
  haveI := nativeStreamingActualContinuationKernel_markov D μ q U extract he T v
  change (∫ z : ((AnisotropicObservationState n ×
    Records (AnisotropicObservationState n) (Configuration n) T) × A),
    G (finiteCascadeRecordTerminalSpins T z.1.2, z.2)
      ∂(P : Measure ((AnisotropicObservationState n ×
        Records (AnisotropicObservationState n) (Configuration n) T) × A))) = _
  rw [hl]
  unfold nativeStreamingActualContinuationLaw at hi ⊢
  rw [Measure.integral_compProd hi]
  rfl

private theorem nativeStreamingCommonPath_symm {j : ℕ} (T : FiniteTerminalGenealogy j)
    (v w : FiniteCascadeRecordVertex T) :
    finiteCascadeCommonPathDepth T v w = finiteCascadeCommonPathDepth T w v := by
  induction T with
  | leaf => cases v; cases w; rfl
  | advance T ih => cases v <;> cases w <;> simp only [finiteCascadeCommonPathDepth, ih]
  | fork T U ihT ihU =>
      cases v <;> cases w <;> simp only [finiteCascadeCommonPathDepth, ihT, ihU]

private theorem nativeStreamingRootCoherent_depth_mul {j : ℕ}
    (T : FiniteTerminalGenealogy j) (φ : FiniteCascadeRecordVertex T → ℝ)
    (hφ : nativeStreamingRootCoherent T φ) (c : ℕ → ℝ) :
    nativeStreamingRootCoherent T (fun v => c v.depth * φ v) := by
  induction T with
  | leaf => trivial
  | advance T ih => exact ih _ hφ
  | @fork j T U ihT ihU =>
      refine ⟨?_, ?_, ihT _ hφ.2.2.1, ihU _ hφ.2.2.2⟩
      · change c j * φ (.left (.root T)) = c j * φ (.root (.fork T U))
        rw [hφ.1]
      · change c j * φ (.right (.root U)) = c j * φ (.root (.fork T U))
        rw [hφ.2.1]

theorem nativeStreamingPatternMoment_originalFresh_vertex_root_coherent
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) (i : ObservationLeaf T) :
    nativeStreamingRootCoherent T (fun v =>
      nativeStreamingPatternMoment D μ a q T F (.originalFresh i (.vertex v))) := by
  have h := nativeStreamingConditionalMarkCommonPath_integral_root_coherent T
    (observationLeafVertex T i) (anisotropicRecordedProfileTreeLaw D μ a q T)
    (fun j x => ((anisotropicRecordedProfileTreeKernel D μ q (observationLinearTree j)).map
      (observationLinearSpin j)) x)
    (fun z c s => nativeStreamingOriginalFreshSpinTest T F i (q c)
      (finiteCascadeRecordTerminalSpins T z.2, s))
  convert h using 1
  funext v
  change nativeStreamingTerminalMarkMoment
    (nativeStreamingActualContinuationProbability D μ a q observationLinearTree
      observationLinearSpin T v)
    (nativeStreamingOriginalFreshSpinTest T F i
      (q (finiteCascadeCommonPathDepth T (observationLeafVertex T i) v))) = _
  rw [nativeStreamingActualContinuationTerminalMoment_eq_integral D μ a q
    observationLinearTree observationLinearSpin (fun j => measurable_observationLinearSpin j),
    nativeStreamingCommonPath_symm T (observationLeafVertex T i) v]

theorem nativeStreamingPatternMoment_current_vertex_root_coherent
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    nativeStreamingRootCoherent T (fun v => Paper.parisiCDF μ (q v.depth) *
      nativeStreamingPatternMoment D μ a q T F (.current (.vertex v))) := by
  refine nativeStreamingRootCoherent_depth_mul T
    (fun v => nativeStreamingPatternMoment D μ a q T F (.current (.vertex v))) ?_
    (fun j => Paper.parisiCDF μ (q j))
  have h := nativeStreamingVertexState_integral_root_coherent T
    (anisotropicRecordedProfileTreeLaw D μ a q T)
    (fun z j x => ∫ s, nativeStreamingDefectSpinTest T F (q j)
      (finiteCascadeRecordTerminalSpins T z.2, s)
      ∂((anisotropicRecordedProfileTreeKernel D μ q (nativeStreamingCurrentPairTree j)).map
        (nativeStreamingCurrentPairExtract j)) x)
  convert h using 1
  funext v
  change nativeStreamingTerminalMarkMoment
    (nativeStreamingActualContinuationProbability D μ a q nativeStreamingCurrentPairTree
      nativeStreamingCurrentPairExtract T v) (nativeStreamingDefectSpinTest T F (q v.depth)) = _
  exact nativeStreamingActualContinuationTerminalMoment_eq_integral D μ a q
    nativeStreamingCurrentPairTree nativeStreamingCurrentPairExtract
    nativeStreamingCurrentPairExtract_measurable T v _

end QuantitativeFollowup
