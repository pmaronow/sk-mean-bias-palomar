module
public import QuantitativePaper.VectorProfilePosteriorMomentLaw

@[expose] public section

/-! A uniform first moment of the actual posterior field envelope. The
constant depends only on dimension and covariance, and includes dimension
zero. The genuine restarted Wiener history supplies both integrability and
the bound, independently of profile, restart, disorder, field, and depth. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 100000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 4000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def vectorProfilePosteriorMomentBound (n : ℕ) (β t : ℝ) : ℝ :=
  ∫sample,vectorRestartFieldPathEnvelope β t sample∂vectorDisorderBrownianMeasure n

theorem vectorProfilePosteriorMomentBound_nonneg (n : ℕ) (β t : ℝ) (ht : t≤1) :
    0≤vectorProfilePosteriorMomentBound n β t :=
  integral_nonneg (fun sample=>vectorRestartFieldPathEnvelope_nonneg β t ht sample)


theorem vectorClampedGridPosterior_fieldEnvelope_eq_displacement (μ : Paper.ParisiMeasure)
    (j : ℕ) (β t : ℝ) (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n)
    (z : Fin (vectorDyadicIndex j+3)→Field n) :
    vectorProfilePosteriorFieldEnvelope
      (vectorClampedScheme (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q q.property)
        β t p x (vectorDyadicIndex j+2) z=
    vectorHistoryFieldDisplacement x (vectorHistoryFrom
      (vectorClampedScheme (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q q.property)
        β t 1 p x (vectorDyadicIndex j+3) z) := by
  unfold vectorProfilePosteriorFieldEnvelope
  have hL : vectorDyadicIndex j+1+1+2-(vectorDyadicIndex j+2+1)=1 := by omega
  rw [hL]
  rfl

theorem integrable_vectorClampedGridPosterior_fieldEnvelope (μ : Paper.ParisiMeasure)
    (j : ℕ) (β t : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap)
    (p : Couplings n×ℝ) (x : Field n) :
    Integrable (fun z=>vectorProfilePosteriorFieldEnvelope
      (vectorClampedScheme (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q q.property)
        β t p x (vectorDyadicIndex j+2) z.1)
      (vectorTailGaussianPosterior
        (vectorClampedScheme (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q q.property)
          β t p x (vectorDyadicIndex j+3)) := by
  let d:=vectorDyadicIndex j
  let s:=vectorClampedScheme (Paper.parisiGridRSBScheme μ d) q q.property
  let F : FiniteHistory (VectorState n) (d+3)→ℝ:=vectorHistoryFieldDisplacement x
  let H:=vectorRestartGridHistory μ j β t ht.le q p x (d+3)
  let G : ((Fin (d+3)→Field n)×Configuration n)→FiniteHistory (VectorState n) (d+3):=
    fun z=>vectorHistoryFrom s β t 1 p x (d+3) z.1
  have hF : Measurable F:=(continuous_vectorHistoryFieldDisplacement x (d+3)).measurable
  have hH : Measurable H:=measurable_vectorRestartGridHistory_full μ j β t ht.le q p x
  have hG : Measurable G:=(measurable_vectorHistoryFrom s β t 1 p x (d+3)).comp measurable_fst
  have hi : Integrable (F ∘ H) (vectorDisorderBrownianMeasure n) := by
    apply (integrable_vectorRestartFieldPathEnvelope (n:=n) β t).mono'
      (hF.comp hH).aestronglyMeasurable
    exact .of_forall fun sample=>by
      change ‖vectorHistoryFieldDisplacement x (H sample)‖≤_
      have hn : 0≤vectorHistoryFieldDisplacement x (H sample) := norm_nonneg _
      rw [Real.norm_of_nonneg hn]
      exact vectorRestartGridHistory_displacement_le_envelope μ j β t ht.le q p x sample
  have hm := vectorClampedGridPosterior_field_history_law μ j β t hβ ht q p x
  change (vectorTailGaussianPosterior s β t p x (d+3)).map G=
    (vectorDisorderBrownianMeasure n).map H at hm
  have hiMap : Integrable F ((vectorTailGaussianPosterior s β t p x (d+3)).map G) := by
    rw [hm]
    exact (integrable_map_measure hF.aestronglyMeasurable hH.aemeasurable).mpr hi
  have hh := (integrable_map_measure hF.aestronglyMeasurable hG.aemeasurable).mp hiMap
  have hE : (fun z : ((Fin (d+3)→Field n)×Configuration n)=>
      vectorProfilePosteriorFieldEnvelope s β t p x (d+2) z.1)=F ∘ G := by
    funext z
    exact vectorClampedGridPosterior_fieldEnvelope_eq_displacement μ j β t q p x z.1
  rw [←hE] at hh
  exact hh

theorem integral_vectorClampedGridPosterior_fieldEnvelope_le (μ : Paper.ParisiMeasure)
    (j : ℕ) (β t : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap)
    (p : Couplings n×ℝ) (x : Field n) :
    (∫z,vectorProfilePosteriorFieldEnvelope
      (vectorClampedScheme (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q q.property)
        β t p x (vectorDyadicIndex j+2) z.1
      ∂vectorTailGaussianPosterior
        (vectorClampedScheme (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q q.property)
          β t p x (vectorDyadicIndex j+3))≤vectorProfilePosteriorMomentBound n β t := by
  let d:=vectorDyadicIndex j
  let s:=vectorClampedScheme (Paper.parisiGridRSBScheme μ d) q q.property
  let F : FiniteHistory (VectorState n) (d+3)→ℝ:=vectorHistoryFieldDisplacement x
  let H:=vectorRestartGridHistory μ j β t ht.le q p x (d+3)
  let G : ((Fin (d+3)→Field n)×Configuration n)→FiniteHistory (VectorState n) (d+3):=
    fun z=>vectorHistoryFrom s β t 1 p x (d+3) z.1
  have hF : Measurable F:=(continuous_vectorHistoryFieldDisplacement x (d+3)).measurable
  have hH : Measurable H:=measurable_vectorRestartGridHistory_full μ j β t ht.le q p x
  have hG : Measurable G:=(measurable_vectorHistoryFrom s β t 1 p x (d+3)).comp measurable_fst
  have hm := vectorClampedGridPosterior_field_history_law μ j β t hβ ht q p x
  change (vectorTailGaussianPosterior s β t p x (d+3)).map G=
    (vectorDisorderBrownianMeasure n).map H at hm
  have he:=congrArg (fun P : Measure (FiniteHistory (VectorState n) (d+3))=>∫h,F h∂P) hm
  rw [integral_map hG.aemeasurable hF.aestronglyMeasurable,
    integral_map hH.aemeasurable hF.aestronglyMeasurable] at he
  have hE : (fun z : ((Fin (d+3)→Field n)×Configuration n)=>
      vectorProfilePosteriorFieldEnvelope s β t p x (d+2) z.1)=(fun z=>F (G z)) := by
    funext z
    exact vectorClampedGridPosterior_fieldEnvelope_eq_displacement μ j β t q p x z.1
  have hleft : (∫z,vectorProfilePosteriorFieldEnvelope s β t p x (d+2) z.1
      ∂vectorTailGaussianPosterior s β t p x (d+3))=
      ∫z,F (G z)∂vectorTailGaussianPosterior s β t p x (d+3) := by
    rw [hE]
  change (∫z,vectorProfilePosteriorFieldEnvelope s β t p x (d+2) z.1
    ∂vectorTailGaussianPosterior s β t p x (d+3))≤_
  rw [hleft,he]
  apply integral_mono_of_nonneg
    (.of_forall fun sample=>show 0≤F (H sample) from norm_nonneg _)
    (integrable_vectorRestartFieldPathEnvelope (n:=n) β t)
    (.of_forall fun sample=>vectorRestartGridHistory_displacement_le_envelope μ j β t ht.le q p x sample)

end QuantitativePaper
