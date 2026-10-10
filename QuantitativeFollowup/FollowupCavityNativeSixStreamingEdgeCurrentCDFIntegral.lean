module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeCurrentFamilyIntegral

@[expose] public section

/-! The current-pair streaming term uses the right CDF at the same actual
ancestral mark. Its moving CDF limit retains every diagonal atom. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1200000

def nativeStreamingEdgeCurrentCDFMaskedMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T)
    (S : Finset Paper.Overlap)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T ×
      (Configuration n × Configuration n) → ℝ) (r : Paper.Overlap) : ℝ :=
  Paper.parisiCDF μ r * nativeStreamingEdgeCurrentFamilyMaskedMoment D μ a q T e S G r

theorem measurable_nativeStreamingEdgeCurrentCDFMaskedMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap) (hq : Antitone q)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T)
    (S : Finset Paper.Overlap)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T ×
      (Configuration n × Configuration n) → ℝ)
    (hG : ∀σ, Continuous (fun r => G r σ)) :
    Measurable (nativeStreamingEdgeCurrentCDFMaskedMoment D μ a q T e S G) :=
  ((Paper.parisiCDF_measurable μ).comp measurable_subtype_coe).mul
    (measurable_nativeStreamingEdgeCurrentFamilyMaskedMoment D μ a q hq T e S G hG)

theorem nativeStreamingEdgeCurrentCDFMaskedMoment_abs_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T)
    (S : Finset Paper.Overlap)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T ×
      (Configuration n × Configuration n) → ℝ)
    (C : ℝ) (hC : 0≤C) (hG : ∀r σ, |G r σ|≤C) (r : Paper.Overlap) :
    |nativeStreamingEdgeCurrentCDFMaskedMoment D μ a q T e S G r|≤C := by
  rw [nativeStreamingEdgeCurrentCDFMaskedMoment,abs_mul,
    abs_of_nonneg (Paper.parisiCDF_nonneg μ r)]
  exact (mul_le_mul (Paper.parisiCDF_le_one μ r)
    (nativeStreamingEdgeCurrentFamilyMaskedMoment_abs_le D μ a q T e S G C hC hG r)
      (abs_nonneg _) zero_le_one).trans_eq (one_mul C)

theorem tendsto_nativeStreamingEdgeCurrentCDFIntegral (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (e : NativeStreamingEdge T) (S : Finset Paper.Overlap) (hzero : zeroOverlap∈S)
    (hlo : q (e.depth+1)∈S) (hhi : q e.depth∈S)
    (GN : ℕ → Paper.Overlap → TerminalSpins (Configuration n) T ×
      (Configuration n × Configuration n) → ℝ)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T ×
      (Configuration n × Configuration n) → ℝ)
    (hGN : ∀N σ, Continuous (fun r => GN N r σ))
    (hG : ∀r σ, Tendsto (fun N => GN N (FRSB.preservingRound S N r) σ) atTop (𝓝 (G r σ)))
    (C : ℝ) (hC : 0≤C) (hbound : ∀N r σ, |GN N r σ|≤C) :
    Tendsto (fun N => ∫r, nativeStreamingEdgeCurrentCDFMaskedMoment D
      (FRSB.preservingMeasure μ S N) a q T e S (GN N) r
        ∂parisiFreeMeasure (FRSB.preservingMeasure μ S N) a) atTop
      (𝓝 (∫r, nativeStreamingEdgeCurrentCDFMaskedMoment D μ a q T e S G r
        ∂parisiFreeMeasure μ a)) := by
  apply nativeStreaming_free_integral_tendsto μ S hzero a ha hμ _ _
    (fun N => measurable_nativeStreamingEdgeCurrentCDFMaskedMoment D _ a q hq T e S
      (GN N) (hGN N)) C hC
    (fun N r => nativeStreamingEdgeCurrentCDFMaskedMoment_abs_le D _ a q T e S
      (GN N) C hC (hbound N) r)
  intro r
  exact (nativeStreaming_preserving_cdf_at_round_tendsto μ S r).mul
    (nativeStreamingEdgeCurrentFamilyMaskedMoment_preserving_tendsto D μ a q hq T e S
      hlo hhi GN G hG r)

end QuantitativeFollowup
