module
public import QuantitativePaper.VectorWeightedDriftExpectation
public import FourPapersCommon.VectorGaussianMoments
public import FourPapersCommon.VectorDriftTaylor
public import FourPapersCommon.NonnegativeTimeTranslation
public import QuantitativePaper.VectorItoCharacteristics

@[expose] public section

/-! Analytic characteristics for a bounded drift driven by the actual vector
Wiener process. Future increment laws and cancellations are supplied by the
constructed Wiener measure, rather than assumed in these characteristics.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ContDiff Topology
namespace QuantitativePaper
open FourPapersCommon

def vectorBrownianFiltrationAt (n : ℕ) (a : ℝ≥0) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (VectorDisorderBrownianSample n)) where
  seq := fun q=>vectorBrownianFiltration n (a+q)
  mono' := fun _ _ h=>(vectorBrownianFiltration n).mono (add_le_add (le_refl a) h)
  le' := fun q=>(vectorBrownianFiltration n).le (a+q)

structure VectorItoCharacteristicsAt (a : ℝ≥0) {n : ℕ}
    (X d : ℝ≥0 → VectorDisorderBrownianSample n → Field n) (σ : ℝ) : Prop where
  continuous_state : ∀ sample,Continuous (fun q=>X q sample)
  measurable_state : Measurable (Function.uncurry X)
  adapted_state : StronglyAdapted (vectorBrownianFiltrationAt n a) X
  measurable_drift : Measurable (Function.uncurry d)
  bounded_drift : ∃ D : ℝ≥0,∀ q sample,‖d q sample‖ ≤ D
  decomposition : ∀ q sample,X q sample = X 0 sample+σ • disorderVectorBrownianIncrement a (a+q) sample+
    vectorIntegratedDrift (fun s=>d s sample) q

structure VectorStaticItoTestAt (a : ℝ≥0) {n : ℕ}
    (f : VectorDisorderBrownianSample n → Field n → ℝ)
    (X : ℝ≥0 → VectorDisorderBrownianSample n → Field n) where
  firstBound : ℝ≥0
  secondBound : ℝ≥0
  thirdBound : ℝ≥0
  measurable : Measurable (Function.uncurry f)
  regularity : ∀ sample,ContDiff ℝ 3 (f sample)
  first_le : ∀ sample x,‖fderiv ℝ (f sample) x‖ ≤ firstBound
  second_le : ∀ sample x,‖iteratedFDeriv ℝ 2 (f sample) x‖ ≤ secondBound
  third_le : ∀ sample x,‖iteratedFDeriv ℝ 3 (f sample) x‖ ≤ thirdBound
  adapted_first : ∀ q,Measurable[vectorBrownianFiltration n (a+q)]
    (fun sample=>fderiv ℝ (f sample) (X q sample))
  adapted_second : ∀ q,Measurable[vectorBrownianFiltration n (a+q)]
    (fun sample=>vectorHessian (f sample) (X q sample))

theorem VectorItoCharacteristicsAt.increment {a : ℝ≥0} {n : ℕ}
    {X d : ℝ≥0 → VectorDisorderBrownianSample n → Field n} {σ : ℝ}
    (hc : VectorItoCharacteristicsAt a X d σ) (r t : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
    X t sample = X r sample+σ • disorderVectorBrownianIncrement (a+r) (a+t) sample+
      (vectorIntegratedDrift (fun s=>d s sample) t-vectorIntegratedDrift (fun s=>d s sample) r) := by
  rw [hc.decomposition t sample,hc.decomposition r sample]
  simp only [disorderVectorBrownianIncrement,smul_sub]
  abel

theorem VectorItoCharacteristics.timeShift {n : ℕ}
    {X d : ℝ≥0→VectorDisorderBrownianSample n→Field n} {σ : ℝ}
    (hc : VectorItoCharacteristics X d σ) (a : ℝ≥0) :
    VectorItoCharacteristicsAt a (fun q=>X (a+q)) (fun q=>d (a+q)) σ := by
  obtain ⟨D,hD⟩ := hc.bounded_drift
  refine {
    continuous_state := fun sample=>(hc.continuous_state sample).comp (continuous_const.add continuous_id)
    measurable_state := hc.measurable_state.comp
      (show Measurable (fun z : ℝ≥0×VectorDisorderBrownianSample n=>(a+z.1,z.2)) from by fun_prop)
    adapted_state := fun q=>hc.adapted_state (a+q)
    measurable_drift := hc.measurable_drift.comp
      (show Measurable (fun z : ℝ≥0×VectorDisorderBrownianSample n=>(a+z.1,z.2)) from by fun_prop)
    bounded_drift := ⟨D,fun q=>hD (a+q)⟩
    decomposition := ?_ }
  intro q sample
  have hh := hc.increment a (a+q) sample
  rw [←vectorIntegratedDrift_add (fun r=>d r sample)
    hc.measurable_drift.of_uncurry_right D (fun r=>hD r sample) a q] at hh
  simpa only [add_zero] using hh

theorem VectorStaticItoTestAt.continuous_first_path {a : ℝ≥0} {n : ℕ}
    {f : VectorDisorderBrownianSample n → Field n → ℝ}
    {X : ℝ≥0 → VectorDisorderBrownianSample n → Field n}
    (hf : VectorStaticItoTestAt a f X) (hX : ∀ sample,Continuous (fun q=>X q sample))
    (sample : VectorDisorderBrownianSample n) :
    Continuous (fun q=>fderiv ℝ (f sample) (X q sample)) := by
  exact ((hf.regularity sample).fderiv_right (m := 2) (by norm_num)).continuous.comp (hX sample)

theorem VectorStaticItoTestAt.continuous_second_path {a : ℝ≥0} {n : ℕ}
    {f : VectorDisorderBrownianSample n → Field n → ℝ}
    {X : ℝ≥0 → VectorDisorderBrownianSample n → Field n}
    (hf : VectorStaticItoTestAt a f X) (hX : ∀ sample,Continuous (fun q=>X q sample))
    (sample : VectorDisorderBrownianSample n) :
    Continuous (fun q=>vectorHessian (f sample) (X q sample)) := by
  exact (((hf.regularity sample).fderiv_right (m := 2) (by norm_num)).fderiv_right
    (m := 1) (by norm_num)).continuous.comp (hX sample)

end QuantitativePaper
