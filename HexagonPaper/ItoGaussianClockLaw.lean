module
public import HexagonPaper.ItoGaussianClockLawBasic
public import HexagonPaper.VariableScalarClockDriverContinuous
public import FourPapersCommon.ContinuousAEPathRepresentation

@[expose] public section

/-! A deterministic natural Itô integral with the true Brownian-clock
Gram matrix has exactly the law of the time-changed canonical Brownian
continuous path. Both random paths are genuine measurable maps into the
supremum-norm continuous-path space. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus FourPapersCommon
open scoped Topology NNReal ENNReal BigOperators
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

theorem deterministicIto_continuous_clock_law
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure)
    (τ : Paper.Overlap ≃o Paper.Overlap) (β : ℝ)
    (hGram : ∀ q r : Paper.Overlap,
      inner ℝ (deterministicTimeCut f (q : ℝ).toNNReal)
        (deterministicTimeCut f (r : ℝ).toNNReal) =
          β ^ 2 * min (τ q : ℝ) (τ r : ℝ))
    (L : Paper.BrownianSample → C(Paper.Overlap,ℝ)) (hL : Measurable L)
    (hIto : ∀ q : Paper.Overlap,
      (naturalItoProcess Paper.isBrownianReal_canonicalBrownian.toIsPreBrownianReal
        (fun t => (Paper.measurable_canonicalBrownian t).stronglyMeasurable) rfl
        (deterministicPredictableEmbedding (P:=Paper.canonicalBrownianMeasure)
          (Filtration.natural Paper.canonicalBrownian
            (fun t => (Paper.measurable_canonicalBrownian t).stronglyMeasurable)) f)
        (q : ℝ).toNNReal : Paper.BrownianSample → ℝ) =ᵐ[Paper.canonicalBrownianMeasure]
          (fun sample => L sample q)) :
    Paper.canonicalBrownianMeasure.map L =
      Paper.canonicalBrownianMeasure.map (scalarClockStoppedReferencePath τ β 1) := by
  apply continuous_path_law_eq_of_finite_evaluations
    Paper.canonicalBrownianMeasure L (scalarClockStoppedReferencePath τ β 1) hL
    (measurable_scalarClockStoppedReferencePath_one τ β)
  intro I
  have heval (q : Paper.Overlap) :
      (fun sample => L sample q) =ᵐ[Paper.canonicalBrownianMeasure]
      (wienerIntegral Paper.isBrownianReal_canonicalBrownian.toIsPreBrownianReal
        (deterministicTimeCut f (q : ℝ).toNNReal) : Paper.BrownianSample → ℝ) := by
    have hq := hIto q
    rw [naturalItoProcess_deterministic_eq_wiener] at hq
    exact hq.symm
  have hfinite :
      (fun sample => I.restrict (fun q => L sample q)) =ᵐ[Paper.canonicalBrownianMeasure]
      (fun sample => fun q : I =>
        (wienerIntegral Paper.isBrownianReal_canonicalBrownian.toIsPreBrownianReal
          (deterministicTimeCut f (q.val : ℝ).toNNReal) : Paper.BrownianSample → ℝ)
            sample) := by
    filter_upwards [ae_all_iff.mpr (fun q : I => heval q.val)] with sample hs
    exact funext hs
  rw [Measure.map_congr hfinite, deterministicWiener_clock_finite_law f τ β hGram I]
  congr 1
  funext sample q
  exact (scalarClockStoppedReferencePath_eval_one τ β sample q.val).symm

theorem exists_deterministicIto_continuous_clock_law
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure)
    (τ : Paper.Overlap ≃o Paper.Overlap) (β : ℝ)
    (hGram : ∀ q r : Paper.Overlap,
      inner ℝ (deterministicTimeCut f (q : ℝ).toNNReal)
        (deterministicTimeCut f (r : ℝ).toNNReal) =
          β ^ 2 * min (τ q : ℝ) (τ r : ℝ)) :
    ∃ L : Paper.BrownianSample → C(Paper.Overlap,ℝ), Measurable L ∧
      (∀ q : Paper.Overlap,
        (naturalItoProcess Paper.isBrownianReal_canonicalBrownian.toIsPreBrownianReal
          (fun t => (Paper.measurable_canonicalBrownian t).stronglyMeasurable) rfl
          (deterministicPredictableEmbedding (P:=Paper.canonicalBrownianMeasure)
            (Filtration.natural Paper.canonicalBrownian
              (fun t => (Paper.measurable_canonicalBrownian t).stronglyMeasurable)) f)
          (q : ℝ).toNNReal : Paper.BrownianSample → ℝ) =ᵐ[Paper.canonicalBrownianMeasure]
            (fun sample => L sample q)) ∧
      Paper.canonicalBrownianMeasure.map L =
        Paper.canonicalBrownianMeasure.map (scalarClockStoppedReferencePath τ β 1) := by
  obtain ⟨L,hL,hIto⟩ := exists_scalarItoContinuousPath
    (deterministicPredictableEmbedding (P:=Paper.canonicalBrownianMeasure)
      (Filtration.natural Paper.canonicalBrownian
        (fun t => (Paper.measurable_canonicalBrownian t).stronglyMeasurable)) f)
  exact ⟨L,hL,hIto,deterministicIto_continuous_clock_law f τ β hGram L hL hIto⟩

end HexagonPaper
