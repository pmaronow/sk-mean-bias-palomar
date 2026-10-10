module
public import QuantitativePaper.VectorGaussianCoordinates
public import Paper.CanonicalBrownian
public import Paper.DiracShift
public import FRSB.BrownianMarkov
public import FourPapersCommon.FiniteProductTranspose

@[expose] public section

/-! Independent actual Wiener coordinates and independent initial SK disorder.
The process has continuous paths on every sample, starts at zero, and every
coordinate is a genuine Brownian motion under the constructed product law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace QuantitativePaper

abbrev VectorBrownianSample (n : ℕ) := Fin n → Paper.BrownianSample

def vectorBrownianMeasure (n : ℕ) : Measure (VectorBrownianSample n) :=
  Measure.pi (fun _ => Paper.canonicalBrownianMeasure)

instance vectorBrownianMeasure_probability (n : ℕ) :
    IsProbabilityMeasure (vectorBrownianMeasure n) := by
  unfold vectorBrownianMeasure
  infer_instance

def vectorBrownian {n : ℕ} (r : ℝ≥0) (sample : VectorBrownianSample n) : Field n :=
  WithLp.toLp 2 (fun i => Paper.canonicalBrownian r (sample i))

@[simp] theorem vectorBrownian_apply {n : ℕ} (r : ℝ≥0)
    (sample : VectorBrownianSample n) (i : Fin n) :
    vectorBrownian r sample i = Paper.canonicalBrownian r (sample i) := rfl

@[simp] theorem vectorBrownian_zero {n : ℕ} (sample : VectorBrownianSample n) :
    vectorBrownian 0 sample = 0 := by
  ext i
  simp

theorem measurable_vectorBrownian {n : ℕ} (r : ℝ≥0) :
    Measurable (vectorBrownian (n := n) r) := by
  unfold vectorBrownian
  have hh : Measurable (fun sample : VectorBrownianSample n =>
      fun i => Paper.canonicalBrownian r (sample i)) :=
    Measurable.of_eval fun i =>
      (Paper.measurable_canonicalBrownian r).comp (measurable_pi_apply i)
  exact (show Measurable (WithLp.toLp 2 : (Fin n → ℝ) → Field n) from by fun_prop).comp hh

theorem continuous_vectorBrownian {n : ℕ} (sample : VectorBrownianSample n) :
    Continuous (fun r => vectorBrownian r sample) := by
  unfold vectorBrownian
  exact (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp (continuous_pi fun i =>
    Paper.continuous_canonicalBrownian (sample i))

theorem measurable_uncurry_vectorBrownian (n : ℕ) :
    Measurable (Function.uncurry (vectorBrownian (n := n))) :=
  measurable_uncurry_of_continuous_of_measurable
    (fun sample => continuous_vectorBrownian sample) measurable_vectorBrownian

theorem hasLaw_vectorBrownian_coordinate_sample {n : ℕ} (i : Fin n) :
    HasLaw (fun sample : VectorBrownianSample n => sample i)
      Paper.canonicalBrownianMeasure (vectorBrownianMeasure n) := by
  exact (measurePreserving_eval
    (fun _ : Fin n => Paper.canonicalBrownianMeasure) i).hasLaw

theorem isBrownianReal_vectorBrownian_coordinate {n : ℕ} (i : Fin n) :
    IsBrownianReal (fun r sample => vectorBrownian r sample i)
      (vectorBrownianMeasure n) := by
  have h := Paper.isBrownianReal_canonicalBrownian.toIsPreBrownianReal.hasLaw_gaussianLimit
    (Measurable.of_eval Paper.measurable_canonicalBrownian).aemeasurable
  refine ⟨(h.comp (hasLaw_vectorBrownian_coordinate_sample i)).IsPreBrownianReal, ?_⟩
  exact Filter.Eventually.of_forall fun sample =>
    Paper.continuous_canonicalBrownian (sample i)

theorem iIndepFun_vectorBrownian_coordinate_samples (n : ℕ) :
    iIndepFun (fun (i : Fin n) (sample : VectorBrownianSample n) => sample i)
      (vectorBrownianMeasure n) :=
  iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

abbrev VectorDisorderBrownianSample (n : ℕ) := (Couplings n × ℝ) × VectorBrownianSample n

def vectorDisorderBrownianMeasure (n : ℕ) : Measure (VectorDisorderBrownianSample n) :=
  (completionLaw n).prod (vectorBrownianMeasure n)

instance vectorDisorderBrownianMeasure_probability (n : ℕ) :
    IsProbabilityMeasure (vectorDisorderBrownianMeasure n) := by
  unfold vectorDisorderBrownianMeasure
  infer_instance

def disorderVectorBrownian {n : ℕ} (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
    Field n := vectorBrownian r sample.2

theorem measurable_disorderVectorBrownian {n : ℕ} (r : ℝ≥0) :
    Measurable (disorderVectorBrownian (n := n) r) :=
  (measurable_vectorBrownian r).comp measurable_snd

theorem continuous_disorderVectorBrownian {n : ℕ}
    (sample : VectorDisorderBrownianSample n) :
    Continuous (fun r => disorderVectorBrownian r sample) :=
  continuous_vectorBrownian sample.2

theorem measurable_uncurry_disorderVectorBrownian (n : ℕ) :
    Measurable (Function.uncurry (disorderVectorBrownian (n := n))) :=
  measurable_uncurry_of_continuous_of_measurable
    continuous_disorderVectorBrownian measurable_disorderVectorBrownian

theorem hasLaw_initialVectorDisorder (n : ℕ) :
    HasLaw (Prod.fst : VectorDisorderBrownianSample n → Couplings n × ℝ)
      (completionLaw n) (vectorDisorderBrownianMeasure n) := by
  exact measurePreserving_fst.hasLaw

theorem hasLaw_vectorBrownian_samples_with_disorder (n : ℕ) :
    HasLaw (Prod.snd : VectorDisorderBrownianSample n → VectorBrownianSample n)
      (vectorBrownianMeasure n) (vectorDisorderBrownianMeasure n) := by
  exact measurePreserving_snd.hasLaw

theorem indep_initialVectorDisorder_vectorBrownian_samples (n : ℕ) :
    IndepFun (Prod.fst : VectorDisorderBrownianSample n → Couplings n × ℝ)
      Prod.snd (vectorDisorderBrownianMeasure n) := by
  exact indepFun_prod (X := id) (Y := id) measurable_id measurable_id

theorem isBrownianReal_disorderVectorBrownian_coordinate {n : ℕ} (i : Fin n) :
    IsBrownianReal (fun r sample => disorderVectorBrownian r sample i)
      (vectorDisorderBrownianMeasure n) := by
  have h := (isBrownianReal_vectorBrownian_coordinate i).toIsPreBrownianReal.hasLaw_gaussianLimit
    (Measurable.of_eval fun r =>
      (show Measurable (fun sample : VectorBrownianSample n =>
        Paper.canonicalBrownian r (sample i)) from
        (Paper.measurable_canonicalBrownian r).comp (measurable_pi_apply i))).aemeasurable
  refine ⟨(h.comp (hasLaw_vectorBrownian_samples_with_disorder n)).IsPreBrownianReal, ?_⟩
  exact Filter.Eventually.of_forall fun sample =>
    Paper.continuous_canonicalBrownian (sample.2 i)

def vectorBrownianRecord {n : ℕ} (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
    VectorState n := (sample.1,disorderVectorBrownian r sample)

theorem measurable_vectorBrownianRecord {n : ℕ} (r : ℝ≥0) :
    Measurable (vectorBrownianRecord (n := n) r) :=
  measurable_fst.prodMk (measurable_disorderVectorBrownian r)

def vectorBrownianFiltration (n : ℕ) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (VectorDisorderBrownianSample n)) :=
  Filtration.natural (vectorBrownianRecord (n := n))
    (fun r => (measurable_vectorBrownianRecord r).stronglyMeasurable)

theorem stronglyAdapted_vectorBrownianRecord (n : ℕ) :
    StronglyAdapted (vectorBrownianFiltration n) (vectorBrownianRecord (n := n)) :=
  Filtration.stronglyAdapted_natural _

theorem stronglyAdapted_disorderVectorBrownian (n : ℕ) :
    StronglyAdapted (vectorBrownianFiltration n) (disorderVectorBrownian (n := n)) :=
  fun r => (stronglyAdapted_vectorBrownianRecord n r).snd

theorem stronglyMeasurable_initialVectorDisorder (n : ℕ) (r : ℝ≥0) :
    StronglyMeasurable[vectorBrownianFiltration n r]
      (Prod.fst : VectorDisorderBrownianSample n → Couplings n × ℝ) :=
  (stronglyAdapted_vectorBrownianRecord n r).fst

end QuantitativePaper
