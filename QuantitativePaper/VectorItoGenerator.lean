module
public import QuantitativePaper.VectorItoTimeExpectation
public import FourPapersCommon.BoundedTimeIntegral

@[expose] public section

/-! Jointly measurable, bounded actual generators along the constructed
vector state. These bounds supply the integrability needed to subtract
prefix Itô identities on a physical profile interval. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
open FourPapersCommon
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
variable {n : ℕ} {T : ℝ≥0}

def vectorItoGenerator
    (test : TimeFTCData (VectorDisorderBrownianSample n) (Field n) T)
    (X d : ℝ≥0 → VectorDisorderBrownianSample n → Field n) (σ : ℝ)
    (s : ℝ≥0) (sample : VectorDisorderBrownianSample n) : ℝ :=
  fderiv ℝ (test.f s sample) (X s sample) (d s sample)+
    σ^2/2*vectorBilinearTrace (vectorHessian (test.f s sample) (X s sample))+
    test.ft s sample (X s sample)

theorem measurable_vectorItoGradientPath
    {X : ℝ≥0 → VectorDisorderBrownianSample n → Field n}
    {f : ℝ≥0 → VectorDisorderBrownianSample n → Field n → ℝ}
    (hf : VectorSpatialItoTest f X) :
    Measurable (fun p : ℝ≥0×VectorDisorderBrownianSample n=>fderiv ℝ (f p.1 p.2) (X p.1 p.2)) :=
  measurable_uncurry_of_continuous_of_measurable hf.continuous_first_path
    (fun s=>(hf.adapted_first s s).mono ((vectorBrownianFiltration n).le s) le_rfl)

theorem measurable_vectorItoTracePath
    {X : ℝ≥0 → VectorDisorderBrownianSample n → Field n}
    {f : ℝ≥0 → VectorDisorderBrownianSample n → Field n → ℝ}
    (hf : VectorSpatialItoTest f X) :
    Measurable (fun p : ℝ≥0×VectorDisorderBrownianSample n=>
      vectorBilinearTrace (vectorHessian (f p.1 p.2) (X p.1 p.2))) := by
  apply measurable_uncurry_of_continuous_of_measurable hf.continuous_trace_path
  intro s
  have hm := (hf.adapted_second s s).mono ((vectorBrownianFiltration n).le s) le_rfl
  exact Finset.measurable_sum Finset.univ (fun i _=>
    (show Measurable (fun H : Field n →L[ℝ] Field n →L[ℝ] ℝ=>
      H (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) from by fun_prop).comp hm)

theorem measurable_vectorItoTimePath
    {X d : ℝ≥0 → VectorDisorderBrownianSample n → Field n} {σ : ℝ}
    (hc : VectorItoCharacteristics X d σ)
    (test : TimeFTCData (VectorDisorderBrownianSample n) (Field n) T) :
    Measurable (fun p : ℝ≥0×VectorDisorderBrownianSample n=>test.ft p.1 p.2 (X p.1 p.2)) :=
  test.ft_measurable.comp ((NNReal.continuous_coe.measurable.comp measurable_fst).prodMk
    (measurable_snd.prodMk hc.measurable_state))

theorem measurable_vectorItoGenerator
    {X d : ℝ≥0 → VectorDisorderBrownianSample n → Field n} {σ : ℝ}
    (hc : VectorItoCharacteristics X d σ)
    (test : TimeFTCData (VectorDisorderBrownianSample n) (Field n) T)
    (hf : VectorSpatialItoTest (fun q=>test.f q) X) :
    Measurable (Function.uncurry (vectorItoGenerator test X d σ)) := by
  have ha := (show Measurable (fun p : (Field n →L[ℝ] ℝ)×Field n=>p.1 p.2) from by fun_prop).comp
    ((measurable_vectorItoGradientPath hf).prodMk hc.measurable_drift)
  exact (ha.add ((measurable_vectorItoTracePath hf).const_mul (σ^2/2))).add
    (measurable_vectorItoTimePath hc test)

theorem vectorItoGenerator_bound
    {X d : ℝ≥0 → VectorDisorderBrownianSample n → Field n} {σ : ℝ}
    (hc : VectorItoCharacteristics X d σ)
    (test : TimeFTCData (VectorDisorderBrownianSample n) (Field n) T)
    (hf : VectorSpatialItoTest (fun q=>test.f q) X)
    (D : ℝ≥0) (hD : ∀ s sample,‖d s sample‖ ≤ D)
    (s : ℝ≥0) (hs : s∈Icc 0 T) (sample : VectorDisorderBrownianSample n) :
    ‖vectorItoGenerator test X d σ s sample‖ ≤
      hf.firstBound*D+σ^2/2*((n : ℝ)*hf.secondBound)+test.bound := by
  have ha := ((fderiv ℝ (test.f s sample) (X s sample)).le_opNorm (d s sample)).trans
    (mul_le_mul (hf.first_le s sample _) (hD s sample) (norm_nonneg _) hf.firstBound.coe_nonneg)
  have hq : ‖σ^2/2*vectorBilinearTrace (vectorHessian (test.f s sample) (X s sample))‖ ≤
      σ^2/2*((n : ℝ)*hf.secondBound) := by
    rw [norm_mul,Real.norm_of_nonneg (by positivity),Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hf.trace_bound s sample) (by positivity)
  have ht := test.ft_bound s ⟨s.coe_nonneg,show (s : ℝ)≤T from hs.2⟩ sample (X s sample)
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add ha hq)) ht)

end QuantitativePaper
