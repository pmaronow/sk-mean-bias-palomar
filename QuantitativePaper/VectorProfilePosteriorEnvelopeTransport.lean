module
public import QuantitativePaper.VectorProfilePosteriorMomentBound

@[expose] public section

/-! Exact pushforward of the actual posterior displacement envelope. It
permits arbitrary measurable envelope tests, while retaining the genuine
restarted field history and the independent Wiener reference measure. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 4000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem vectorClampedGridPosterior_fieldEnvelope_law (μ : Paper.ParisiMeasure)
    (j : ℕ) (β t : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap)
    (p : Couplings n×ℝ) (x : Field n) :
    (vectorTailGaussianPosterior
      (vectorClampedScheme (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q q.property)
        β t p x (vectorDyadicIndex j+3)).map
      (fun z=>vectorProfilePosteriorFieldEnvelope
        (vectorClampedScheme (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q q.property)
          β t p x (vectorDyadicIndex j+2) z.1)=
    (vectorDisorderBrownianMeasure n).map
      (fun sample=>vectorHistoryFieldDisplacement x
        (vectorRestartGridHistory μ j β t ht.le q p x (vectorDyadicIndex j+3) sample)) := by
  let d:=vectorDyadicIndex j
  let s:=vectorClampedScheme (Paper.parisiGridRSBScheme μ d) q q.property
  let F : FiniteHistory (VectorState n) (d+3)→ℝ:=vectorHistoryFieldDisplacement x
  let H:=vectorRestartGridHistory μ j β t ht.le q p x (d+3)
  let G : ((Fin (d+3)→Field n)×Configuration n)→FiniteHistory (VectorState n) (d+3):=
    fun z=>vectorHistoryFrom s β t 1 p x (d+3) z.1
  have hF : Measurable F:=(continuous_vectorHistoryFieldDisplacement x (d+3)).measurable
  have hH : Measurable H:=measurable_vectorRestartGridHistory_full μ j β t ht.le q p x
  have hG : Measurable G:=(measurable_vectorHistoryFrom s β t 1 p x (d+3)).comp measurable_fst
  have hm:=vectorClampedGridPosterior_field_history_law μ j β t hβ ht q p x
  change (vectorTailGaussianPosterior s β t p x (d+3)).map G=
    (vectorDisorderBrownianMeasure n).map H at hm
  have he:=congrArg (fun P : Measure (FiniteHistory (VectorState n) (d+3))=>P.map F) hm
  rw [Measure.map_map hF hG,Measure.map_map hF hH] at he
  have hE : (F ∘ G)=(fun z : ((Fin (d+3)→Field n)×Configuration n)=>
      vectorProfilePosteriorFieldEnvelope s β t p x (d+2) z.1) := by
    funext z
    exact (vectorClampedGridPosterior_fieldEnvelope_eq_displacement μ j β t q p x z.1).symm
  rw [hE] at he
  exact he

theorem measurable_vectorClampedGridPosterior_fieldEnvelope (μ : Paper.ParisiMeasure)
    (j : ℕ) (β t : ℝ) (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n) :
    Measurable (fun z : ((Fin (vectorDyadicIndex j+3)→Field n)×Configuration n)=>
      vectorProfilePosteriorFieldEnvelope
        (vectorClampedScheme (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q q.property)
          β t p x (vectorDyadicIndex j+2) z.1) := by
  have he : (fun z : ((Fin (vectorDyadicIndex j+3)→Field n)×Configuration n)=>
      vectorProfilePosteriorFieldEnvelope
        (vectorClampedScheme (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q q.property)
          β t p x (vectorDyadicIndex j+2) z.1)=
      (vectorHistoryFieldDisplacement x) ∘
        (fun z=>vectorHistoryFrom
          (vectorClampedScheme (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q q.property)
            β t 1 p x (vectorDyadicIndex j+3) z.1) := by
    funext z
    exact vectorClampedGridPosterior_fieldEnvelope_eq_displacement μ j β t q p x z.1
  rw [he]
  exact (continuous_vectorHistoryFieldDisplacement x _).measurable.comp
    ((measurable_vectorHistoryFrom _ β t 1 p x _).comp measurable_fst)

end QuantitativePaper
