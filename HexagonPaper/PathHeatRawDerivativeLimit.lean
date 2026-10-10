module
public import HexagonPaper.PathHeatRawNormalization
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

/-! Derivative-limit assembly from genuine raw finite Gaussian formulas.
This helper neither assumes nor supplies the finite Price formulas: the
actual clock-law and source-jet modules prove those separately. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace HexagonPaper
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem hasDerivAt_pathHeat_raw_normalizer_limit
    (Wn Fn Hn Jn : ℕ→ℝ→Ω→ℝ) (W F H J : ℝ→Ω→ℝ)
    (e : Ω→ℝ) (B C D a b x : ℝ) (hx : x∈Ioo a b)
    (hn : ∀n z,PathHeatDominatedData μ (Wn n z) (Fn n z) (Hn n z) (Jn n z) e B C D)
    (h : ∀z,PathHeatDominatedData μ (W z) (F z) (H z) (J z) e B C D)
    (hlim : ∀z : ℕ→ℝ,∀y,Tendsto z atTop (𝓝 y)→
      (∀ᵐω ∂μ,Tendsto (fun n=>Wn n (z n) ω) atTop (𝓝 (W y ω))) ∧
      (∀ᵐω ∂μ,Tendsto (fun n=>Fn n (z n) ω) atTop (𝓝 (F y ω))) ∧
      (∀ᵐω ∂μ,Tendsto (fun n=>Hn n (z n) ω) atTop (𝓝 (H y ω))) ∧
      (∀ᵐω ∂μ,Tendsto (fun n=>Jn n (z n) ω) atTop (𝓝 (J y ω))))
    (hfinite : ∀n z,z∈Ioo a b→HasDerivAt (fun u=>pathHeatNormalizer μ (Wn n u))
      (∫ω,Wn n z ω*Hn n z ω∂μ) z) :
    HasDerivAt (fun u=>pathHeatNormalizer μ (W u)) (∫ω,W x ω*H x ω∂μ) x := by
  apply hasDerivAt_pathHeat_limit
    (fun n u=>pathHeatNormalizer μ (Wn n u))
    (fun n u=>∫ω,Wn n u ω*Hn n u ω∂μ)
    (fun u=>pathHeatNormalizer μ (W u)) (fun u=>∫ω,W u ω*H u ω∂μ) a b x hx
  · exact hfinite
  · intro y hy
    obtain ⟨hw,hf,hh,hj⟩ := hlim (fun _=>y) y tendsto_const_nhds
    exact (pathHeat_normalized_limits (fun n=>hn n y) (h y) hw hf hh hj).2.1
  · intro z hz
    obtain ⟨hw,hf,hh,hj⟩ := hlim z x hz
    exact pathHeat_tendsto_weighted_integral (h x).integrable_envelope (h x).nonneg_C
      (fun n=>(hn n (z n)).weight_measurable)
      (fun n=>(hn n (z n)).density_generator_measurable)
      (fun n=>(hn n (z n)).weight_positive) (fun n=>(hn n (z n)).weight_bound)
      (fun n=>(hn n (z n)).density_generator_bound) hw hh

theorem hasDerivAt_pathHeat_expectation_log_normalizer_limits
    (Wn Fn Hn Jn : ℕ→ℝ→Ω→ℝ) (W F H J : ℝ→Ω→ℝ)
    (e : Ω→ℝ) (B C D a b x : ℝ) (hx : x∈Ioo a b)
    (hn : ∀n z,PathHeatDominatedData μ (Wn n z) (Fn n z) (Hn n z) (Jn n z) e B C D)
    (h : ∀z,PathHeatDominatedData μ (W z) (F z) (H z) (J z) e B C D)
    (hlim : ∀z : ℕ→ℝ,∀y,Tendsto z atTop (𝓝 y)→
      (∀ᵐω ∂μ,Tendsto (fun n=>Wn n (z n) ω) atTop (𝓝 (W y ω))) ∧
      (∀ᵐω ∂μ,Tendsto (fun n=>Fn n (z n) ω) atTop (𝓝 (F y ω))) ∧
      (∀ᵐω ∂μ,Tendsto (fun n=>Hn n (z n) ω) atTop (𝓝 (H y ω))) ∧
      (∀ᵐω ∂μ,Tendsto (fun n=>Jn n (z n) ω) atTop (𝓝 (J y ω))))
    (hfiniteZ : ∀n z,z∈Ioo a b→HasDerivAt (fun u=>pathHeatNormalizer μ (Wn n u))
      (∫ω,Wn n z ω*Hn n z ω∂μ) z)
    (hfiniteN : ∀n z,z∈Ioo a b→HasDerivAt (fun u=>∫ω,Wn n u ω*Fn n u ω∂μ)
      (∫ω,Wn n z ω*(Jn n z ω+Fn n z ω*Hn n z ω)∂μ) z) :
    (0<pathHeatNormalizer μ (W x)) ∧
    HasDerivAt (fun u=>pathHeatExpectation μ (W u) (F u))
      (pathHeatResponse μ (W x) (F x) (H x) (J x)) x ∧
    HasDerivAt (fun u=>Real.log (pathHeatNormalizer μ (W u)))
      (pathHeatExpectation μ (W x) (H x)) x := by
  have hp := pathHeat_normalizer_positive (h x)
  have hZ := hasDerivAt_pathHeat_raw_normalizer_limit Wn Fn Hn Jn W F H J e B C D a b x hx hn h hlim hfiniteZ
  refine ⟨hp,?_,?_⟩
  · apply hasDerivAt_pathHeat_normalized_limit Wn Fn Hn Jn W F H J e B C D a b x hx
      (fun n z _=>hn n z) (fun z _=>h z)
    · intro z y hnz hy hz
      exact hlim z y hz
    · intro n z hz
      exact hasDerivAt_pathHeat_expectation_of_raw (Wn n) (Fn n) (Hn n) (Jn n) e B C D z
        (hn n z) (hfiniteZ n z hz) (hfiniteN n z hz)
  · exact hZ.log hp.ne'

end HexagonPaper
