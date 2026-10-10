module
public import QuantitativePaper.VectorMeasureIto
public import QuantitativePaper.VectorBoundedTimeIntegral
public import FourPapersCommon.ProgressiveTimeIntegral

@[expose] public section

/-! Literal adapted vector controls and their actual integrated-drift Wiener
states. Adaptation of the drift integral is proved from progressive
measurability on the genuine enlarged past filtration. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

structure IsVectorParisiControl
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) : Prop where
  continuous : ∀sample,Continuous (fun r => A r sample)
  adapted : StronglyAdapted (vectorBrownianFiltration n) A
  norm_le : ∀r sample,‖A r sample‖≤Real.sqrt (n : ℝ)

theorem IsVectorParisiControl.measurable
    {A : ℝ≥0→VectorDisorderBrownianSample n→Field n} (hA : IsVectorParisiControl A) :
    Measurable (Function.uncurry A) := by
  apply measurable_uncurry_of_continuous_of_measurable hA.continuous
  intro r
  exact ((hA.adapted r).mono ((vectorBrownianFiltration n).le r)).measurable

def vectorControlDrift (c : ℝ) (μ : Paper.ParisiMeasure)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (r : ℝ≥0)
    (sample : VectorDisorderBrownianSample n) : Field n :=
  (c*Paper.parisiCDF μ r) • A r sample

theorem measurable_vectorControlDrift (c : ℝ) (μ : Paper.ParisiMeasure)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (hA : IsVectorParisiControl A) :
    Measurable (Function.uncurry (vectorControlDrift c μ A)) := by
  exact (measurable_const.mul ((Paper.parisiCDF_monotone μ).measurable.comp
    (NNReal.continuous_coe.measurable.comp measurable_fst))).smul hA.measurable

theorem norm_vectorControlDrift_le (c : ℝ) (μ : Paper.ParisiMeasure)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (hA : IsVectorParisiControl A)
    (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
    ‖vectorControlDrift c μ A r sample‖≤|c| * Real.sqrt (n : ℝ) := by
  rw [vectorControlDrift,norm_smul,Real.norm_eq_abs,abs_mul,
    abs_of_nonneg (Paper.parisiCDF_nonneg μ r)]
  calc
    _ ≤ |c| * 1*Real.sqrt (n : ℝ) := mul_le_mul
      (mul_le_mul_of_nonneg_left (Paper.parisiCDF_le_one μ r) (abs_nonneg c))
      (hA.norm_le r sample) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem stronglyProgressive_vectorControlDrift (c : ℝ) (μ : Paper.ParisiMeasure)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (hA : IsVectorParisiControl A) :
    IsStronglyProgressive (vectorBrownianFiltration n) (vectorControlDrift c μ A) := by
  have hp := hA.adapted.isStronglyProgressive_of_continuous hA.continuous
  intro r
  letI : MeasurableSpace (VectorDisorderBrownianSample n) := vectorBrownianFiltration n r
  have hcoef : Measurable (fun z : Iic r×VectorDisorderBrownianSample n =>
      c*Paper.parisiCDF μ (z.1 : ℝ≥0)) :=
    measurable_const.mul ((Paper.parisiCDF_monotone μ).measurable.comp
      measurable_fst.subtype_coe.coe_nnreal_real)
  exact (hcoef.smul (hp r).measurable).stronglyMeasurable

theorem stronglyAdapted_vectorIntegratedControlDrift (c : ℝ) (μ : Paper.ParisiMeasure)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (hA : IsVectorParisiControl A) :
    StronglyAdapted (vectorBrownianFiltration n)
      (fun r sample => vectorIntegratedDrift (fun s => vectorControlDrift c μ A s sample) r) := by
  exact stronglyAdapted_nnreal_integral (vectorBrownianFiltration n)
    (vectorControlDrift c μ A) (stronglyProgressive_vectorControlDrift c μ A hA)

theorem continuous_vectorIntegratedControlDrift (c : ℝ) (μ : Paper.ParisiMeasure)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (hA : IsVectorParisiControl A)
    (sample : VectorDisorderBrownianSample n) :
    Continuous (fun r => vectorIntegratedDrift (fun s => vectorControlDrift c μ A s sample) r) := by
  let D : ℝ≥0 := (|c| * Real.sqrt (n : ℝ)).toNNReal
  have hD : (D : ℝ)=|c| * Real.sqrt (n : ℝ) := Real.coe_toNNReal _ (by positivity)
  have hm := (measurable_vectorControlDrift c μ A hA).of_uncurry_right (y := sample)
  have hb (s : ℝ≥0) : ‖vectorControlDrift c μ A s sample‖≤D := by
    rw [hD]
    exact norm_vectorControlDrift_le c μ A hA s sample
  apply LipschitzWith.continuous (K := D)
  apply LipschitzWith.of_dist_le_mul
  intro r t
  rcases le_total r t with hrt|htr
  · rw [dist_eq_norm,norm_sub_rev,NNReal.dist_eq,abs_of_nonpos (by exact sub_nonpos.mpr hrt)]
    convert vectorIntegratedDrift_increment_bound _ hm D hb hrt using 1 <;> ring
  · rw [dist_eq_norm,NNReal.dist_eq,abs_of_nonneg (by exact sub_nonneg.mpr htr)]
    exact vectorIntegratedDrift_increment_bound _ hm D hb htr

def vectorControlledState (c : ℝ) (μ : Paper.ParisiMeasure)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (r : ℝ≥0)
    (sample : VectorDisorderBrownianSample n) : Field n :=
  Real.sqrt c • disorderVectorBrownian r sample+
    vectorIntegratedDrift (fun s => vectorControlDrift c μ A s sample) r

theorem stronglyAdapted_vectorControlledState (c : ℝ) (μ : Paper.ParisiMeasure)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (hA : IsVectorParisiControl A) :
    StronglyAdapted (vectorBrownianFiltration n) (vectorControlledState c μ A) := by
  intro r
  exact ((stronglyAdapted_disorderVectorBrownian n r).const_smul (Real.sqrt c)).add
    (stronglyAdapted_vectorIntegratedControlDrift c μ A hA r)

theorem continuous_vectorControlledState (c : ℝ) (μ : Paper.ParisiMeasure)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (hA : IsVectorParisiControl A)
    (sample : VectorDisorderBrownianSample n) : Continuous (fun r => vectorControlledState c μ A r sample) := by
  convert ((continuous_disorderVectorBrownian sample).const_smul (Real.sqrt c)).add
    (continuous_vectorIntegratedControlDrift c μ A hA sample) using 1
  funext r
  rfl

theorem measurable_vectorControlledState (c : ℝ) (μ : Paper.ParisiMeasure)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (hA : IsVectorParisiControl A) :
    Measurable (Function.uncurry (vectorControlledState c μ A)) := by
  apply measurable_uncurry_of_continuous_of_measurable (continuous_vectorControlledState c μ A hA)
  intro r
  exact ((stronglyAdapted_vectorControlledState c μ A hA r).mono ((vectorBrownianFiltration n).le r)).measurable

@[simp] theorem vectorControlledState_zero (c : ℝ) (μ : Paper.ParisiMeasure)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (sample : VectorDisorderBrownianSample n) :
    vectorControlledState c μ A 0 sample=0 := by
  simp [vectorControlledState,vectorIntegratedDrift,disorderVectorBrownian]

theorem vectorItoCharacteristics_vectorControlledState (c : ℝ) (μ : Paper.ParisiMeasure)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (hA : IsVectorParisiControl A) :
    VectorItoCharacteristics (vectorControlledState c μ A) (vectorControlDrift c μ A) (Real.sqrt c) where
  continuous_state := continuous_vectorControlledState c μ A hA
  measurable_state := measurable_vectorControlledState c μ A hA
  adapted_state := stronglyAdapted_vectorControlledState c μ A hA
  measurable_drift := measurable_vectorControlDrift c μ A hA
  bounded_drift := ⟨(|c| * Real.sqrt (n : ℝ)).toNNReal,fun r sample => by
    rw [Real.coe_toNNReal _ (by positivity)]
    exact norm_vectorControlDrift_le c μ A hA r sample⟩
  decomposition := by intro r sample;rw [vectorControlledState_zero];simp only [vectorControlledState,zero_add]

end QuantitativePaper
