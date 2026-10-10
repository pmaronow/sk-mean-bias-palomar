module
public import QuantitativePaper.VectorMeasureSpinIntegration
public import Mathlib.Probability.Moments.Variance

@[expose] public section

/-! Bounded observables of the actual disorder/path/terminal-spin measure
survive the finite-profile approximation. Both the terminal Gibbs kernel
and the fractional disorder tilt are passed to the limit, rather than
assuming a joint-law convergence statement. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon
open scoped NNReal Topology BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

private theorem measurable_terminalMean_variable
    {Ω : Type*} [MeasurableSpace Ω] (E F : Ω → Configuration n → ℝ)
    (hE : ∀ σ,Measurable (fun sample=>E sample σ))
    (hF : ∀ σ,Measurable (fun sample=>F sample σ)) :
    Measurable (fun sample=>terminalMean (E sample) (F sample)) := by
  unfold terminalMean terminalWeight terminalPartition
  exact Finset.measurable_sum _ fun σ _=>
    ((hE σ).exp.div (Finset.measurable_sum _ fun τ _=>(hE τ).exp)).mul (hF σ)

theorem integral_vectorFiniteSpinPathLaw_bounded {k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (ht : t≤1)
    (F : VectorDisorderBrownianSample n × Configuration n → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : ∀p,‖F p‖≤C) :
    (∫p,F p ∂vectorFiniteSpinPathLaw s β t a ht)=
      ∫sample,terminalMean
        (vectorTerminalExponent n β t sample.1 (vectorFiniteState s β t ht 1 sample))
        (fun σ=>F (sample,σ)) ∂vectorFiniteDisorderTilt s β t a := by
  letI:=vectorFiniteSpinPathLaw_probability (n:=n) s β t a ht
  letI:=vectorFiniteDisorderTilt_probability (n:=n) s β t a
  have hi : Integrable F (vectorFiniteSpinPathLaw s β t a ht) :=
    (integrable_const C).mono' hF.aestronglyMeasurable (.of_forall hC)
  rw [vectorFiniteSpinPathLaw,Measure.integral_compProd hi]
  apply integral_congr_ae
  exact .of_forall fun sample=>by
    change (∫σ,F (sample,σ) ∂terminalLaw
      (vectorTerminalExponent n β t sample.1 (vectorFiniteState s β t ht 1 sample)))=_
    exact integral_terminalLaw _ _

theorem integral_vectorMeasureSpinPathLaw_bounded (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1)
    (F : VectorDisorderBrownianSample n × Configuration n → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : ∀p,‖F p‖≤C) :
    (∫p,F p ∂vectorMeasureSpinPathLaw μ β t a ht)=
      ∫sample,terminalMean
        (vectorTerminalExponent n β t sample.1 (vectorMeasureState μ β t ht 1 sample))
        (fun σ=>F (sample,σ)) ∂vectorMeasureDisorderTilt μ β t a := by
  letI:=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  have hi : Integrable F (vectorMeasureSpinPathLaw μ β t a ht) :=
    (integrable_const C).mono' hF.aestronglyMeasurable (.of_forall hC)
  rw [vectorMeasureSpinPathLaw,Measure.integral_compProd hi]
  apply integral_congr_ae
  exact .of_forall fun sample=>by
    change (∫σ,F (sample,σ) ∂terminalLaw
      (vectorTerminalExponent n β t sample.1 (vectorMeasureState μ β t ht 1 sample)))=_
    exact integral_terminalLaw _ _

theorem tendsto_integral_vectorDyadicSpinPathLaw_bounded (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1)
    (Fj : ℕ → VectorDisorderBrownianSample n × Configuration n → ℝ)
    (F : VectorDisorderBrownianSample n × Configuration n → ℝ)
    (C : ℝ) (hC : 0≤C) (hFj : ∀j,Measurable (Fj j))
    (hF : Measurable F) (hB : ∀j p,‖Fj j p‖≤C) (hBF : ∀p,‖F p‖≤C)
    (hlim : ∀sample σ,Tendsto (fun j=>Fj j (sample,σ)) atTop (𝓝 (F (sample,σ)))) :
    Tendsto (fun j=>∫p,Fj j p ∂vectorFiniteSpinPathLaw
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a ht) atTop
      (𝓝 (∫p,F p ∂vectorMeasureSpinPathLaw μ β t a ht)) := by
  let Gj := fun j sample=>terminalMean
    (vectorTerminalExponent n β t sample.1 (vectorDyadicState μ β t ht j 1 sample))
    (fun σ=>Fj j (sample,σ))
  let G := fun sample=>terminalMean
    (vectorTerminalExponent n β t sample.1 (vectorMeasureState μ β t ht 1 sample))
    (fun σ=>F (sample,σ))
  have hGj (j : ℕ) : Measurable (Gj j) := by
    dsimp only [Gj]
    apply measurable_terminalMean_variable
    · intro σ
      have hz : Measurable (fun sample : VectorDisorderBrownianSample n=>
          (sample.1,vectorDyadicState μ β t ht j 1 sample)) :=
        measurable_vectorFiniteJointState
          (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t ht 1
      simpa only [Function.comp_def] using
        (measurable_vectorTerminalExponent_state n β t σ).comp hz
    · intro σ
      exact (hFj j).comp (measurable_id.prodMk measurable_const)
  have hGB (j : ℕ) (sample) : ‖Gj j sample‖≤C := by
    rw [Real.norm_eq_abs]
    exact terminalMean_bound _ _ C (fun σ=>by
      simpa only [Real.norm_eq_abs] using hB j (sample,σ))
  have hGL (sample : VectorDisorderBrownianSample n) :
      Tendsto (fun j=>Gj j sample) atTop (𝓝 (G sample)) := by
    have hX:=tendsto_vectorDyadicState_at_moving_time μ β t ht 1
      (fun _=>1) (fun _=>le_rfl) tendsto_const_nhds sample
    have hE (σ : Configuration n) :
        Tendsto (fun j=>vectorTerminalExponent n β t sample.1
          (vectorDyadicState μ β t ht j 1 sample) σ) atTop
          (𝓝 (vectorTerminalExponent n β t sample.1
            (vectorMeasureState μ β t ht 1 sample) σ)) := by
      have hc : Continuous (fun x : Field n=>vectorTerminalExponent n β t sample.1 x σ) := by
        unfold vectorTerminalExponent fieldDot
        fun_prop
      exact (hc.tendsto _).comp hX
    have hExp (σ : Configuration n) :
        Tendsto (fun j=>Real.exp (vectorTerminalExponent n β t sample.1
          (vectorDyadicState μ β t ht j 1 sample) σ)) atTop
          (𝓝 (Real.exp (vectorTerminalExponent n β t sample.1
            (vectorMeasureState μ β t ht 1 sample) σ))) :=
      (Real.continuous_exp.tendsto _).comp (hE σ)
    have hP : Tendsto (fun j=>terminalPartition
        (vectorTerminalExponent n β t sample.1 (vectorDyadicState μ β t ht j 1 sample)))
        atTop (𝓝 (terminalPartition
          (vectorTerminalExponent n β t sample.1 (vectorMeasureState μ β t ht 1 sample)))) :=
      tendsto_finsetSum Finset.univ (fun σ _=>hExp σ)
    have hW (σ : Configuration n) :
        Tendsto (fun j=>terminalWeight
          (vectorTerminalExponent n β t sample.1 (vectorDyadicState μ β t ht j 1 sample)) σ)
          atTop (𝓝 (terminalWeight
            (vectorTerminalExponent n β t sample.1 (vectorMeasureState μ β t ht 1 sample)) σ)) :=
      (hExp σ).div hP (terminalPartition_pos _).ne'
    exact tendsto_finsetSum Finset.univ (fun σ _=>(hW σ).mul (hlim sample σ))
  have he:=tendsto_integral_vectorDyadicTilt_bounded μ β t a ht Gj G C hC hGj hGB
    (.of_forall hGL)
  simpa only [integral_vectorFiniteSpinPathLaw_bounded _ β t a ht _ (hFj _) C (hB _),
    integral_vectorMeasureSpinPathLaw_bounded μ β t a ht F hF C hBF,
    Gj,G,vectorDyadicState] using he

theorem tendsto_variance_vectorDyadicSpinPathLaw_bounded (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1)
    (Fj : ℕ → VectorDisorderBrownianSample n × Configuration n → ℝ)
    (F : VectorDisorderBrownianSample n × Configuration n → ℝ)
    (C : ℝ) (hC : 0≤C) (hFj : ∀j,Measurable (Fj j))
    (hF : Measurable F) (hB : ∀j p,‖Fj j p‖≤C) (hBF : ∀p,‖F p‖≤C)
    (hlim : ∀sample σ,Tendsto (fun j=>Fj j (sample,σ)) atTop (𝓝 (F (sample,σ)))) :
    Tendsto (fun j=>variance (Fj j) (vectorFiniteSpinPathLaw
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a ht)) atTop
      (𝓝 (variance F (vectorMeasureSpinPathLaw μ β t a ht))) := by
  have he:=tendsto_integral_vectorDyadicSpinPathLaw_bounded μ β t a ht Fj F C hC
    hFj hF hB hBF hlim
  have hs:=tendsto_integral_vectorDyadicSpinPathLaw_bounded μ β t a ht
    (fun j p=>(Fj j p)^2) (fun p=>(F p)^2) (C^2) (sq_nonneg _)
    (fun j=>(hFj j).pow_const 2) (hF.pow_const 2)
    (fun j p=>by simpa only [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) (hB j p) 2)
    (fun p=>by simpa only [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) (hBF p) 2)
    (fun sample σ=>(hlim sample σ).pow 2)
  have hMj (j : ℕ) : MemLp (Fj j) 2 (vectorFiniteSpinPathLaw
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a ht) := by
    letI:=vectorFiniteSpinPathLaw_probability (n:=n)
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a ht
    exact (memLp_const C).mono' (hFj j).aestronglyMeasurable (.of_forall (hB j))
  have hM : MemLp F 2 (vectorMeasureSpinPathLaw μ β t a ht) := by
    letI:=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht
    exact (memLp_const C).mono' hF.aestronglyMeasurable (.of_forall hBF)
  have hvj (j : ℕ) := by
    letI:=vectorFiniteSpinPathLaw_probability (n:=n)
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a ht
    exact variance_eq_sub (hMj j)
  letI:=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht
  simpa only [hvj,variance_eq_sub hM,Pi.pow_apply] using hs.sub (he.pow 2)

end QuantitativePaper
