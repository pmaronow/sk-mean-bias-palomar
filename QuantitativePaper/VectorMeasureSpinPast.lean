module
public import QuantitativePaper.VectorMeasureConditionalSpinMean
public import QuantitativePaper.VectorMeasureSpinIntegration
public import FourPapersCommon.PullbackIndicatorIntegral

@[expose] public section

/-! The terminal spin sampled from the actual arbitrary-profile diffusion
has the genuine spatial gradient as its conditional mean in the full past. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

def vectorSpinPast (n : ℕ) (q : ℝ≥0) :
    MeasurableSpace (VectorDisorderBrownianSample n×Configuration n) :=
  (vectorBrownianFiltration n q).comap Prod.fst

theorem vectorSpinPast_le (n : ℕ) (q : ℝ≥0) :
    vectorSpinPast n q≤ (inferInstance :
      MeasurableSpace (VectorDisorderBrownianSample n×Configuration n)) :=
  (MeasurableSpace.comap_mono ((vectorBrownianFiltration n).le q)).trans
    measurable_fst.comap_le

theorem adapted_vectorMeasureSpinMean_joint (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (l : Fin n) :
    Measurable[vectorSpinPast n (q : ℝ).toNNReal]
      (fun p : VectorDisorderBrownianSample n×Configuration n=>
        vectorMeasureSpinMean μ β t ht q p.1 l) :=
  (adapted_vectorMeasureSpinMean_component μ β t ht q l).comp
    (comap_measurable Prod.fst)

theorem integral_vectorMeasureSpinPathLaw_past_spin (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) (l : Fin n)
    (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n (q : ℝ).toNNReal] Z)
    (C : ℝ≥0) (hC : ∀ sample,‖Z sample‖≤C) :
    (∫p,Z p.1*Paper.spinSign (p.2 l) ∂vectorMeasureSpinPathLaw μ β t a ht.le)=
      ∫p,Z p.1*vectorMeasureSpinMean μ β t ht.le q p.1 l
        ∂vectorMeasureSpinPathLaw μ β t a ht.le := by
  have hZm : Measurable Z := hZ.mono ((vectorBrownianFiltration n).le _) le_rfl
  have hgm : Measurable (fun sample=>vectorMeasureSpinMean μ β t ht.le q sample l) :=
    (adapted_vectorMeasureSpinMean_component μ β t ht.le q l).mono
      ((vectorBrownianFiltration n).le _) le_rfl
  rw [integral_vectorMeasureSpinPathLaw_terminal_weight μ β t a ht.le Z hZm C hC
      (fun σ=>Paper.spinSign (σ l)),
    integral_vectorMeasureSpinPathLaw_sample μ β t a ht.le
      (fun sample=>Z sample*vectorMeasureSpinMean μ β t ht.le q sample l)
      (hZm.fun_mul hgm)]
  exact vectorMeasure_terminal_spin_pairing_past μ β t a hβ ht q l Z hZ C hC

theorem vectorMeasureSpinPathLaw_spin_condExp (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) (l : Fin n) :
    (vectorMeasureSpinPathLaw μ β t a ht.le)[
      (fun p : VectorDisorderBrownianSample n×Configuration n=>Paper.spinSign (p.2 l)) |
      vectorSpinPast n (q : ℝ).toNNReal]=ᵐ[vectorMeasureSpinPathLaw μ β t a ht.le]
      fun p=>vectorMeasureSpinMean μ β t ht.le q p.1 l := by
  haveI := vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht.le
  have hspin : Measurable (fun p : VectorDisorderBrownianSample n×Configuration n=>
      Paper.spinSign (p.2 l)) :=
    (measurable_of_finite (fun σ : Configuration n=>Paper.spinSign (σ l))).comp measurable_snd
  have hi : Integrable (fun p : VectorDisorderBrownianSample n×Configuration n=>
      Paper.spinSign (p.2 l)) (vectorMeasureSpinPathLaw μ β t a ht.le) :=
    (integrable_const (1 : ℝ)).mono' hspin.aestronglyMeasurable
      (.of_forall fun p=>by rw [Real.norm_eq_abs,Paper.abs_spinSign])
  have had := adapted_vectorMeasureSpinMean_joint μ β t ht.le q l
  have hci : Integrable (fun p : VectorDisorderBrownianSample n×Configuration n=>
      vectorMeasureSpinMean μ β t ht.le q p.1 l) (vectorMeasureSpinPathLaw μ β t a ht.le) :=
    (integrable_const (1 : ℝ)).mono'
      (had.mono (vectorSpinPast_le n _) le_rfl).aestronglyMeasurable
      (.of_forall fun p=>by simpa only [Real.norm_eq_abs] using
        vectorMeasureSpinMean_component_bound μ β t ht.le q p.1 l)
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (vectorSpinPast_le n _) hi
  · intro A hA hfinite
    exact hci.integrableOn
  · intro A hA hfinite
    obtain ⟨B,hB,rfl⟩ := MeasurableSpace.measurableSet_comap.mp hA
    have hBg : MeasurableSet B := ((vectorBrownianFiltration n).le _) B hB
    have he := integral_vectorMeasureSpinPathLaw_past_spin μ β t a hβ ht q l
      (B.indicator (fun _=>1)) (measurable_const.indicator hB) 1
      (fun sample=>by
        by_cases hs : sample∈B
        · simp only [indicator_of_mem hs,norm_one,NNReal.coe_one,le_refl]
        · simp only [indicator_of_notMem hs,norm_zero,NNReal.coe_one,zero_le_one])
    rw [integral_pullback_indicator_one_mul (vectorMeasureSpinPathLaw μ β t a ht.le)
        Prod.fst measurable_fst B hBg,
      integral_pullback_indicator_one_mul (vectorMeasureSpinPathLaw μ β t a ht.le)
        Prod.fst measurable_fst B hBg] at he
    exact he.symm
  · exact had.stronglyMeasurable.aestronglyMeasurable

end QuantitativePaper
