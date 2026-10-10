module
public import QuantitativeFollowup.VectorMeanOverlap
public import QuantitativePaper.VectorMeasureConditionalSpinMean
public import QuantitativePaper.VectorZeroOverlap
public import Mathlib.Probability.Martingale.Basic

@[expose] public section

/-! The actual arbitrary-profile spin-mean vector is a genuine martingale
in the full disorder/Wiener past under every real fractional disorder tilt.
The proof uses the actual terminal conditional law, not a martingale premise. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory QuantitativePaper
open scoped Topology NNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vectorMeasureGradient_zero_field (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (p : Couplings n×ℝ) :
    vectorMeasureGradient μ β t q p 0=0 := by
  have hfinite (j : ℕ) : vectorDyadicTailGradient μ β t q j p 0=0 := by
    unfold vectorDyadicTailGradient
    rw [vectorFiniteTailGradient_eq_magnetization,vectorMagnetization_zero_field]
  have hlim : Tendsto (fun j=>vectorDyadicTailGradient μ β t q j p 0)
      Filter.atTop (𝓝 (0:Field n)) := by
    simp only [hfinite]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique (tendsto_vectorDyadicTailGradient μ β t ht q p 0) hlim

theorem vectorMeasureSpinMean_zero (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (sample : VectorDisorderBrownianSample n) :
    vectorMeasureSpinMean μ β t ht 0 sample=0 := by
  have hzero : ((0:Paper.Overlap):ℝ)=0:=rfl
  simp only [vectorMeasureSpinMean,hzero,Real.toNNReal_zero,vectorMeasureState_zero]
  exact vectorMeasureGradient_zero_field μ β t ht 0 sample.1

theorem vectorMeanOverlap_zero (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) : vectorMeanOverlap (n:=n) μ β t a ht 0=0 := by
  simp only [vectorMeanOverlap,vectorMeasureSpinMean_zero,PiLp.zero_apply,
    zero_pow (by norm_num : (2:ℕ)≠0),integral_zero,Finset.sum_const_zero,zero_div]

def vectorOverlapFiltration (n : ℕ) :
    Filtration Paper.Overlap (inferInstance : MeasurableSpace (VectorDisorderBrownianSample n)) :=
  StochasticCalculus.monotoneReindexFiltration (vectorBrownianFiltration n)
    (fun q : Paper.Overlap=>(q:ℝ).toNNReal) (fun _ _ h=>Real.toNNReal_mono h)

theorem martingale_vectorMeasureSpinMean_component (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (l : Fin n) :
    Martingale (fun q : Paper.Overlap=>fun sample=>vectorMeasureSpinMean μ β t ht.le q sample l)
      (vectorOverlapFiltration n) (vectorMeasureDisorderTilt μ β t a) := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht.le
  apply (martingale_condExp (fun sample : VectorDisorderBrownianSample n=>terminalMean
      (vectorTerminalExponent n β t sample.1 (vectorMeasureState μ β t ht.le 1 sample))
      (fun σ=>Paper.spinSign (σ l))) (vectorOverlapFiltration n)
      (vectorMeasureDisorderTilt μ β t a)).congr
  · intro q
    exact (adapted_vectorMeasureSpinMean_component μ β t ht.le q l).stronglyMeasurable
  · intro q
    exact vectorMeasure_terminal_mean_condExp μ β t a hβ ht q l

theorem integrable_vectorMeasureSpinMean (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (q : Paper.Overlap) :
    Integrable (vectorMeasureSpinMean (n:=n) μ β t ht q) (vectorMeasureDisorderTilt μ β t a) := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  have hm:Measurable (vectorMeasureSpinMean (n:=n) μ β t ht q):=
    (adapted_vectorMeasureSpinMean μ β t ht q).mono ((vectorBrownianFiltration n).le _) le_rfl
  exact (integrable_const (Real.sqrt (n:ℝ))).mono' hm.aestronglyMeasurable
    (.of_forall fun sample=>norm_vectorMeasureGradient_le μ β t ht q sample.1
      (vectorMeasureState μ β t ht (q:ℝ).toNNReal sample))

theorem martingale_vectorMeasureSpinMean (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) :
    Martingale (vectorMeasureSpinMean (n:=n) μ β t ht.le)
      (vectorOverlapFiltration n) (vectorMeasureDisorderTilt μ β t a) := by
  let P:=vectorMeasureDisorderTilt (n:=n) μ β t a
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht.le
  refine ⟨fun q=>(adapted_vectorMeasureSpinMean μ β t ht.le q).stronglyMeasurable,?_⟩
  intro r q hrq
  have hcomponent (l : Fin n) :
      (fun sample=>(P[vectorMeasureSpinMean μ β t ht.le q | vectorOverlapFiltration n r]) sample l)
        =ᵐ[P] fun sample=>vectorMeasureSpinMean μ β t ht.le r sample l := by
    have hc:=(EuclideanSpace.proj l).comp_condExp_comm
      (m:=vectorOverlapFiltration n r) (integrable_vectorMeasureSpinMean μ β t a ht.le q)
    exact hc.trans ((martingale_vectorMeasureSpinMean_component μ β t a hβ ht l).condExp_ae_eq hrq)
  have hall : ∀ᵐ sample∂P,∀l : Fin n,
      (P[vectorMeasureSpinMean μ β t ht.le q | vectorOverlapFiltration n r]) sample l=
        vectorMeasureSpinMean μ β t ht.le r sample l := ae_all_iff.mpr hcomponent
  filter_upwards [hall] with sample hs
  ext l
  exact hs l

end QuantitativeFollowup
