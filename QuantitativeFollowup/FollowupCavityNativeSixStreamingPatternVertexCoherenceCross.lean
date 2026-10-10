module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternVertexCoherence

@[expose] public section

/-! Both vertex arguments of the actual cross-mark moment are coherent
at fork roots, using the unconditional double-graft product law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem nativeStreamingCrossVertexProbability_eq_actual_continuations
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (v w : FiniteCascadeRecordVertex T) :
    (nativeStreamingCrossVertexProbability D μ a q T v w : Measure _) =
      anisotropicRecordedProfileTreeLaw D μ a q T ⊗ₘ
        (nativeStreamingActualContinuationKernel D μ q observationLinearTree
          observationLinearSpin T v ×ₖ
        nativeStreamingActualContinuationKernel D μ q observationLinearTree
          observationLinearSpin T w) := by
  let κ : ℕ → Kernel (AnisotropicObservationState n) (AnisotropicObservationState n) :=
    fun j => anisotropicObservationTransition D μ (q (j+1)) (q j)
  let θ : Kernel (AnisotropicObservationState n) (Configuration n) :=
    (anisotropicTerminalSpinKernel D).comap (anisotropicObservationParameter D)
      (measurable_anisotropicObservationParameter D)
  have hκ : ∀ j, IsMarkovKernel (κ j) := fun _ => inferInstance
  haveI : IsMarkovKernel θ := inferInstance
  have hg := nativeStreamingCrossObservationGraft_joint_law κ hκ θ observationLinearTree
    observationLinearSpin (fun j => measurable_observationLinearSpin j) v w
    (anisotropicObservationInitialLaw D μ a)
  unfold nativeStreamingCrossContinuationMarkedLaw nativeStreamingCrossContinuationKernel
    nativeStreamingContinuationVertexKernel nativeStreamingContinuationKernel at hg
  dsimp only [κ, θ] at hg
  simp_rw [← nativeStreamingRecordedProfileTreeKernel_eq_observation D μ q] at hg
  change (anisotropicRecordedProfileTreeLaw D μ a q _).map _ = _
  exact hg

theorem nativeStreamingCrossVertexTerminalMoment_eq_integral
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (v w : FiniteCascadeRecordVertex T)
    (G : TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ) :
    nativeStreamingTerminalMarkMoment (nativeStreamingCrossVertexProbability D μ a q T v w) G =
      ∫ z, ∫ s, G (finiteCascadeRecordTerminalSpins T z.2, s)
        ∂((((anisotropicRecordedProfileTreeKernel D μ q (observationLinearTree v.depth)).map
          (observationLinearSpin v.depth)) (nativeStreamingVertexState v z.1 z.2)).prod
          (((anisotropicRecordedProfileTreeKernel D μ q (observationLinearTree w.depth)).map
            (observationLinearSpin w.depth)) (nativeStreamingVertexState w z.1 z.2)))
        ∂anisotropicRecordedProfileTreeLaw D μ a q T := by
  let P := nativeStreamingCrossVertexProbability D μ a q T v w
  have hi := integrable_nativeStreamingTerminalMarkTest P G
  have hl := nativeStreamingCrossVertexProbability_eq_actual_continuations D μ a q T v w
  rw [hl] at hi
  haveI := nativeStreamingActualContinuationKernel_markov D μ q observationLinearTree
    observationLinearSpin (fun j => measurable_observationLinearSpin j) T v
  haveI := nativeStreamingActualContinuationKernel_markov D μ q observationLinearTree
    observationLinearSpin (fun j => measurable_observationLinearSpin j) T w
  unfold nativeStreamingTerminalMarkMoment
  rw [hl, Measure.integral_compProd hi]
  simp only [Kernel.prod_apply, nativeStreamingActualContinuationKernel, Kernel.comap_apply]
  rfl

private theorem nativeStreamingCrossCommonPath_symm {j : ℕ}
    (T : FiniteTerminalGenealogy j) (v w : FiniteCascadeRecordVertex T) :
    finiteCascadeCommonPathDepth T v w = finiteCascadeCommonPathDepth T w v := by
  induction T with
  | leaf => cases v; cases w; rfl
  | advance T ih => cases v <;> cases w <;> simp only [finiteCascadeCommonPathDepth, ih]
  | fork T U ihT ihU =>
      cases v <;> cases w <;> simp only [finiteCascadeCommonPathDepth, ihT, ihU]

theorem nativeStreamingPatternMoment_cross_left_vertex_root_coherent
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) (w : FiniteCascadeRecordVertex T) :
    nativeStreamingRootCoherent T (fun v =>
      nativeStreamingPatternMoment D μ a q T F (.cross (.vertex v) (.vertex w))) := by
  have h := nativeStreamingVertexStateCommonPath_integral_root_coherent T w
    (anisotropicRecordedProfileTreeLaw D μ a q T)
    (fun z j c x => ∫ s, nativeStreamingDefectSpinTest T F (q c)
      (finiteCascadeRecordTerminalSpins T z.2, s)
      ∂((((anisotropicRecordedProfileTreeKernel D μ q (observationLinearTree j)).map
        (observationLinearSpin j)) x).prod
        (((anisotropicRecordedProfileTreeKernel D μ q (observationLinearTree w.depth)).map
          (observationLinearSpin w.depth)) (nativeStreamingVertexState w z.1 z.2))))
  convert h using 1
  funext v
  change nativeStreamingTerminalMarkMoment (nativeStreamingCrossVertexProbability D μ a q T v w)
    (nativeStreamingDefectSpinTest T F (q (finiteCascadeCommonPathDepth T v w))) = _
  exact nativeStreamingCrossVertexTerminalMoment_eq_integral D μ a q T v w _

theorem nativeStreamingPatternMoment_cross_right_vertex_root_coherent
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) (v : FiniteCascadeRecordVertex T) :
    nativeStreamingRootCoherent T (fun w =>
      nativeStreamingPatternMoment D μ a q T F (.cross (.vertex v) (.vertex w))) := by
  have h := nativeStreamingVertexStateCommonPath_integral_root_coherent T v
    (anisotropicRecordedProfileTreeLaw D μ a q T)
    (fun z j c x => ∫ s, nativeStreamingDefectSpinTest T F (q c)
      (finiteCascadeRecordTerminalSpins T z.2, s)
      ∂((((anisotropicRecordedProfileTreeKernel D μ q (observationLinearTree v.depth)).map
        (observationLinearSpin v.depth)) (nativeStreamingVertexState v z.1 z.2)).prod
        (((anisotropicRecordedProfileTreeKernel D μ q (observationLinearTree j)).map
          (observationLinearSpin j)) x)))
  convert h using 1
  funext w
  change nativeStreamingTerminalMarkMoment (nativeStreamingCrossVertexProbability D μ a q T v w)
    (nativeStreamingDefectSpinTest T F (q (finiteCascadeCommonPathDepth T v w))) = _
  rw [nativeStreamingCrossVertexTerminalMoment_eq_integral,
    nativeStreamingCrossCommonPath_symm T v w]

end QuantitativeFollowup
