module
public import QuantitativePaper.VectorProfilePosteriorEnvelopeTransport

@[expose] public section

/-! Uniform exponential moments of the genuine posterior displacement.
All exponential integrability is proved from the actual independent
coordinate Wiener maxima. -/
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

theorem integrable_exp_vectorRestartFieldPathEnvelope (β t K : ℝ) :
    Integrable (fun sample : VectorDisorderBrownianSample n=>
      Real.exp (K*vectorRestartFieldPathEnvelope β t sample)) (vectorDisorderBrownianMeasure n) := by
  let c:=(1-t)*β^2
  have hi:=((integrable_exp_vectorBrownianPathEnvelope (n:=n) (K*Real.sqrt c)).comp_snd
    (completionLaw n)).const_mul (Real.exp (K*c*Real.sqrt (n:ℝ)))
  have he : (fun sample : VectorDisorderBrownianSample n=>
      Real.exp (K*vectorRestartFieldPathEnvelope β t sample))=
      (fun sample=>Real.exp (K*c*Real.sqrt (n:ℝ))*
        Real.exp ((K*Real.sqrt c)*vectorBrownianPathEnvelope sample.2)) := by
    funext sample
    rw [←Real.exp_add]
    congr 1
    unfold vectorRestartFieldPathEnvelope c
    ring
  rw [he]
  exact hi

def vectorProfilePosteriorExpMomentBound (n : ℕ) (β t K : ℝ) : ℝ :=
  ∫sample,Real.exp (K*vectorRestartFieldPathEnvelope β t sample)∂vectorDisorderBrownianMeasure n

theorem vectorProfilePosteriorExpMomentBound_nonneg (n : ℕ) (β t K : ℝ) :
    0≤vectorProfilePosteriorExpMomentBound n β t K :=
  integral_nonneg (fun _=>(Real.exp_pos _).le)

theorem vectorClampedGridPosterior_fieldEnvelope_exp_moment (μ : Paper.ParisiMeasure)
    (j : ℕ) (β t : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap)
    (p : Couplings n×ℝ) (x : Field n) (K : ℝ) (hK : 0≤K) :
    Integrable (fun z=>Real.exp (K*vectorProfilePosteriorFieldEnvelope
      (vectorClampedScheme (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q q.property)
        β t p x (vectorDyadicIndex j+2) z.1))
      (vectorTailGaussianPosterior
        (vectorClampedScheme (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q q.property)
          β t p x (vectorDyadicIndex j+3)) ∧
    (∫z,Real.exp (K*vectorProfilePosteriorFieldEnvelope
      (vectorClampedScheme (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q q.property)
        β t p x (vectorDyadicIndex j+2) z.1)
      ∂vectorTailGaussianPosterior
        (vectorClampedScheme (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q q.property)
          β t p x (vectorDyadicIndex j+3))≤vectorProfilePosteriorExpMomentBound n β t K := by
  let d:=vectorDyadicIndex j
  let s:=vectorClampedScheme (Paper.parisiGridRSBScheme μ d) q q.property
  let P:=vectorTailGaussianPosterior s β t p x (d+3)
  let E : ((Fin (d+3)→Field n)×Configuration n)→ℝ:=
    fun z=>vectorProfilePosteriorFieldEnvelope s β t p x (d+2) z.1
  let D : VectorDisorderBrownianSample n→ℝ:=fun sample=>vectorHistoryFieldDisplacement x
    (vectorRestartGridHistory μ j β t ht.le q p x (d+3) sample)
  let F : ℝ→ℝ:=fun v=>Real.exp (K*v)
  have hE : Measurable E:=measurable_vectorClampedGridPosterior_fieldEnvelope μ j β t q p x
  have hD : Measurable D:=(continuous_vectorHistoryFieldDisplacement x (d+3)).measurable.comp
    (measurable_vectorRestartGridHistory_full μ j β t ht.le q p x)
  have hF : Measurable F:=(measurable_id.const_mul K).exp
  have hbound (sample : VectorDisorderBrownianSample n) :
      F (D sample)≤Real.exp (K*vectorRestartFieldPathEnvelope β t sample) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (vectorRestartGridHistory_displacement_le_envelope μ j β t ht.le q p x sample) hK)
  have hiD : Integrable (F ∘ D) (vectorDisorderBrownianMeasure n) := by
    apply (integrable_exp_vectorRestartFieldPathEnvelope (n:=n) β t K).mono'
      (hF.comp hD).aestronglyMeasurable
    exact .of_forall fun sample=>by
      have hn : 0≤F (D sample):=(Real.exp_pos _).le
      change ‖F (D sample)‖≤_
      rw [Real.norm_of_nonneg hn]
      exact hbound sample
  have hm:=vectorClampedGridPosterior_fieldEnvelope_law μ j β t hβ ht q p x
  change P.map E=(vectorDisorderBrownianMeasure n).map D at hm
  have hiMap : Integrable F (P.map E) := by
    rw [hm]
    exact (integrable_map_measure hF.aestronglyMeasurable hD.aemeasurable).mpr hiD
  have hiE := (integrable_map_measure hF.aestronglyMeasurable hE.aemeasurable).mp hiMap
  have he:=congrArg (fun Q : Measure ℝ=>∫v,F v∂Q) hm
  rw [integral_map hE.aemeasurable hF.aestronglyMeasurable,
    integral_map hD.aemeasurable hF.aestronglyMeasurable] at he
  refine ⟨hiE,?_⟩
  rw [he]
  exact integral_mono hiD (integrable_exp_vectorRestartFieldPathEnvelope (n:=n) β t K) hbound

end QuantitativePaper
