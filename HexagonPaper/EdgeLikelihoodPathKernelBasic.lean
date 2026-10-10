module
public import HexagonPaper.EdgeLikelihood
public import QuantitativeFollowup.AnisotropicRecordedProfileTree

@[expose] public section

/-! Jointly measurable true stopped edge paths, with the initial disorder
and field retained as kernel input. Fresh canonical Wiener noise drives
the original native restarted Picard state. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open FourPapersCommon QuantitativePaper QuantitativeFollowup
open scoped Topology NNReal ENNReal
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def edgeNoiseStoppedPath (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q h : Paper.Overlap) (z : AnisotropicRestartNoiseData n) :
    C(Paper.Overlap,AnisotropicParameter n) :=
  ⟨fun r=>anisotropicDisorderInjection n z.1.1+anisotropicUnitInput D
      (anisotropicRestartNoiseStatePath D μ q z
        (((min (r:ℝ) (h:ℝ))-(q:ℝ)).toNNReal:ℝ)),
    continuous_const.add ((anisotropicUnitInput D).continuous.comp
      ((continuous_vectorNoiseStatePath
        (vectorTimeShiftDriftData (anisotropicWhitenedDriftData D μ z.1.1) (q:ℝ).toNNReal)
        1 (vectorRestartHorizon q) ((0,z.1.2),z.2)).comp
          (NNReal.continuous_coe.comp (continuous_real_toNNReal.comp
            ((continuous_subtype_val.min continuous_const).sub continuous_const)))))⟩

set_option backward.isDefEq.respectTransparency true in
theorem measurable_edgeNoiseStoppedPath (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q h : Paper.Overlap) : Measurable (edgeNoiseStoppedPath D μ q h) := by
  rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval]
  intro r
  change Measurable (fun z : AnisotropicRestartNoiseData n=>
    anisotropicDisorderInjection n z.1.1+anisotropicUnitInput D
      (anisotropicRestartNoiseStatePath D μ q z
        (((min (r:ℝ) (h:ℝ))-(q:ℝ)).toNNReal:ℝ)))
  have ht:Measurable (fun z : AnisotropicRestartNoiseData n=>
      ((((min (r:ℝ) (h:ℝ))-(q:ℝ)).toNNReal:ℝ),z)):=measurable_const.prodMk measurable_id
  convert
    ((anisotropicDisorderInjection n).measurable.comp measurable_fst.fst).add
    ((anisotropicUnitInput D).measurable.comp
      ((measurable_uncurry_anisotropicRestartNoiseStatePath D μ q).comp ht)) using 1 <;> rfl

theorem edgeNoiseStoppedPath_canonical (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q h : Paper.Overlap) (g : AnisotropicDisorder n) (x : Field n)
    (sample : VectorDisorderBrownianSample n) :
    edgeNoiseStoppedPath D μ q h ((g,x),vectorCanonicalBrownianPath sample.2)=
      edgeStoppedDiffusionPath D μ g q h x sample := by
  apply ContinuousMap.ext
  intro r
  change anisotropicDisorderInjection n g+anisotropicUnitInput D
      (anisotropicRestartNoiseStatePath D μ q ((g,x),vectorCanonicalBrownianPath sample.2)
        (((min (r:ℝ) (h:ℝ))-(q:ℝ)).toNNReal:ℝ))=
    anisotropicDisorderInjection n g+anisotropicUnitInput D
      (anisotropicRestartState D μ g q x ((min (r:ℝ) (h:ℝ)-(q:ℝ)).toNNReal) sample)
  rw [anisotropicRestartNoiseStatePath_canonical]
  apply Real.toNNReal_le_toNNReal
  exact sub_le_sub_right ((min_le_right (r:ℝ) (h:ℝ)).trans h.property.2) _

theorem measurable_edgeStoppedDiffusionPath_start (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q h : Paper.Overlap) :
    Measurable (fun z : AnisotropicObservationState n×VectorDisorderBrownianSample n=>
      edgeStoppedDiffusionPath D μ z.1.1 q h z.1.2 z.2) := by
  have hm:Measurable (fun z : AnisotropicObservationState n×VectorDisorderBrownianSample n=>
      (z.1,vectorCanonicalBrownianPath z.2.2)):=
    measurable_fst.prodMk ((measurable_vectorCanonicalBrownianPath (n:=n)).comp measurable_snd.snd)
  have he: (fun z : AnisotropicObservationState n×VectorDisorderBrownianSample n=>
      edgeStoppedDiffusionPath D μ z.1.1 q h z.1.2 z.2)=
    edgeNoiseStoppedPath D μ q h ∘ (fun z=>(z.1,vectorCanonicalBrownianPath z.2.2)) := by
    funext z
    exact (edgeNoiseStoppedPath_canonical D μ q h z.1.1 z.1.2 z.2).symm
  rw [he]
  exact (measurable_edgeNoiseStoppedPath D μ q h).comp hm

theorem measurable_edgeStoppedReferencePath_start (D : AnisotropicSpinModel n)
    (q h : Paper.Overlap) :
    Measurable (fun z : AnisotropicObservationState n×VectorDisorderBrownianSample n=>
      edgeStoppedReferencePath D z.1.1 q h z.1.2 z.2) := by
  rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval]
  intro r
  change Measurable (fun z : AnisotropicObservationState n×VectorDisorderBrownianSample n=>
    anisotropicDisorderInjection n z.1.1+anisotropicUnitInput D z.1.2+
      anisotropicUnitInput D
        (disorderVectorBrownian ((min (r:ℝ) (h:ℝ)-(q:ℝ)).toNNReal) z.2))
  exact (((anisotropicDisorderInjection n).measurable.comp measurable_fst.fst).add
    ((anisotropicUnitInput D).measurable.comp measurable_fst.snd)).add
      ((anisotropicUnitInput D).measurable.comp
        ((measurable_disorderVectorBrownian _).comp measurable_snd))

end HexagonPaper
