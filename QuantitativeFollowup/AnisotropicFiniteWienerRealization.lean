module
public import QuantitativeFollowup.AnisotropicFiniteDiffusionHistoryLaw
public import QuantitativeFollowup.AnisotropicWhitenedIto

@[expose] public section

/-! Removing the auxiliary independent initial Gaussian from the actual
 Wiener realization. The finite diffusion uses precisely the original
 anisotropic disorder and coordinate Wiener paths, with the proved literal
 chronological history law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon QuantitativePaper
open scoped NNReal ENNReal
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

theorem anisotropicWhitenedFiniteState_same_wiener (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (sample other : VectorDisorderBrownianSample n)
    (hW : sample.2=other.2) (r : ℝ≥0) (hr : r ≤ 1) :
    anisotropicWhitenedFiniteState D s g r sample=anisotropicWhitenedFiniteState D s g r other := by
  rcases sample with ⟨p,w⟩
  rcases other with ⟨p',w'⟩
  dsimp only at hW
  subst w'
  rfl

def anisotropicFiniteWienerSampleLaw (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) :
    Measure (AnisotropicDisorderBrownianSample n) :=
  (anisotropicFiniteOuterLaw D s a).prod (vectorBrownianMeasure n)

instance anisotropicFiniteWienerSampleLaw_probability (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) : IsProbabilityMeasure (anisotropicFiniteWienerSampleLaw D s a) := by
  unfold anisotropicFiniteWienerSampleLaw
  infer_instance

def anisotropicFiniteWienerHistory (D : AnisotropicSpinModel n) (s : RSBScheme k) (j : ℕ)
    (sample : AnisotropicDisorderBrownianSample n) : FiniteHistory (AnisotropicParameter n) j :=
  anisotropicFinitePhysicalHistory D s sample.1 j ((0,0),sample.2)

theorem measurable_anisotropicFiniteWienerHistory (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) : Measurable (anisotropicFiniteWienerHistory D s j) := by
  unfold anisotropicFiniteWienerHistory
  simpa only [Function.comp_def,anisotropicFiniteDiffusionHistory,anisotropicFiniteWienerHistory] using
    (measurable_anisotropicFiniteDiffusionHistory D s j).comp
      (show Measurable (fun sample : AnisotropicDisorderBrownianSample n=>
        (sample.1,((0,0),sample.2))) from by fun_prop)

theorem anisotropicFiniteDiffusionHistory_eq_wiener (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (hj : j ≤ k+2) (sample : AnisotropicFiniteDiffusionSample n) :
    anisotropicFiniteDiffusionHistory D s j sample=
      anisotropicFiniteWienerHistory D s j (sample.1,sample.2.2) := by
  rfl

theorem anisotropicFiniteWiener_projection_law (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) :
    (anisotropicFiniteDiffusionSampleLaw D s a).map
      (fun sample : AnisotropicFiniteDiffusionSample n=>(sample.1,sample.2.2))=
      anisotropicFiniteWienerSampleLaw D s a := by
  change ((anisotropicFiniteOuterLaw D s a).prod (vectorDisorderBrownianMeasure n)).map
    (Prod.map id Prod.snd)=_
  rw [←Measure.map_prod_map _ _ measurable_id measurable_snd,Measure.map_id,
    vectorDisorderBrownianMeasure,Measure.map_snd_prod,measure_univ,one_smul]
  rfl

theorem anisotropicFiniteWiener_history_law (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (j : ℕ) (hj : j ≤ k+2) :
    (anisotropicFiniteWienerSampleLaw D s a).map (anisotropicFiniteWienerHistory D s j)=
      finiteHistoryLaw (anisotropicFiniteInitialLaw D s a) (anisotropicFiniteTransition D s) j := by
  rw [←anisotropicFiniteWiener_projection_law D s a,
    Measure.map_map (measurable_anisotropicFiniteWienerHistory D s j) (by fun_prop)]
  have he : (anisotropicFiniteWienerHistory D s j ∘
      fun sample : AnisotropicFiniteDiffusionSample n=>(sample.1,sample.2.2))=
      anisotropicFiniteDiffusionHistory D s j := by
    funext sample
    exact (anisotropicFiniteDiffusionHistory_eq_wiener D s j hj sample).symm
  rw [he,anisotropicFiniteDiffusion_history_law D s a j hj]

end QuantitativeFollowup
