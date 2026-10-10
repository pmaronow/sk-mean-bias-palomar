module
public import QuantitativePaper.VectorMeasureConditionalVariance
public import FourPapersCommon.PullbackIndicatorIntegral

@[expose] public section

/-! Conditional expectation of every actual terminal spin observable is
the pullback of its terminal-Gibbs conditional expectation on the Wiener
sample space. This identifies the genuine marked-spin conditional law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorMeasureTerminalObservable (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (d : Configuration n→ℝ) (sample : VectorDisorderBrownianSample n) : ℝ :=
  terminalMean (vectorTerminalExponent n β t sample.1 (vectorMeasureState μ β t ht 1 sample)) d

theorem measurable_vectorMeasureTerminalObservable (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (d : Configuration n→ℝ) : Measurable (vectorMeasureTerminalObservable μ β t ht d) := by
  have hφ : Measurable (fun p : VectorState n=>terminalMean (vectorTerminalExponent n β t p.1 p.2) d):=
    (continuous_vectorTerminalMean_joint β t d).measurable
  have hm:=hφ.comp (measurable_vectorMeasureJointState μ β t ht 1)
  dsimp only [Function.comp_def,vectorMeasureJointState] at hm
  exact hm

theorem integrable_vectorMeasureTerminalObservable (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (d : Configuration n→ℝ) :
    Integrable (vectorMeasureTerminalObservable μ β t ht d) (vectorMeasureDisorderTilt μ β t a) := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  let D:=∑σ : Configuration n,|d σ|
  have hd (σ : Configuration n) : |d σ|≤D:=
    Finset.single_le_sum (fun τ _=>abs_nonneg (d τ)) (Finset.mem_univ σ)
  apply (integrable_const D).mono'
    (measurable_vectorMeasureTerminalObservable μ β t ht d).aestronglyMeasurable
  filter_upwards with sample
  rw [Real.norm_eq_abs]
  exact terminalMean_bound _ d D hd

theorem measurePreserving_vectorMeasureSpinPathLaw_fst (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) :
    MeasurePreserving Prod.fst (vectorMeasureSpinPathLaw (n:=n) μ β t a ht)
      (vectorMeasureDisorderTilt μ β t a) := by
  refine ⟨measurable_fst,?_⟩
  exact vectorMeasureSpinPathLaw_fst μ β t a ht

theorem vectorMeasureSpinPathLaw_terminal_observable_condExp (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap) (d : Configuration n→ℝ) :
    (vectorMeasureSpinPathLaw μ β t a ht)[
      (fun p : VectorDisorderBrownianSample n×Configuration n=>d p.2)|vectorSpinPast n (q:ℝ).toNNReal]
      =ᵐ[vectorMeasureSpinPathLaw μ β t a ht]
      (fun p=>(vectorMeasureDisorderTilt μ β t a)[vectorMeasureTerminalObservable μ β t ht d|
        vectorBrownianFiltration n (q:ℝ).toNNReal] p.1) := by
  let P:=vectorMeasureDisorderTilt (n:=n) μ β t a
  let J:=vectorMeasureSpinPathLaw (n:=n) μ β t a ht
  let ambient : MeasurableSpace (VectorDisorderBrownianSample n) := inferInstance
  let V:=vectorBrownianFiltration n (q:ℝ).toNNReal
  letI : MeasurableSpace (VectorDisorderBrownianSample n) := ambient
  let F:=vectorMeasureTerminalObservable μ β t ht d
  let G:=P[F|V]
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  letI:=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht
  have hGi : Integrable G P:=integrable_condExp
  have hGm : StronglyMeasurable[V] G:=stronglyMeasurable_condExp
  have hGmg:Measurable G:=(hGm.mono ((vectorBrownianFiltration n).le _)).measurable
  have hci : Integrable (fun p : VectorDisorderBrownianSample n×Configuration n=>G p.1) J :=
    (measurePreserving_vectorMeasureSpinPathLaw_fst μ β t a ht).integrable_comp_of_integrable hGi
  have hspinm:Measurable (fun p : VectorDisorderBrownianSample n×Configuration n=>d p.2):=
    (measurable_of_finite d).comp measurable_snd
  let D:=∑σ : Configuration n,|d σ|
  have hspin : Integrable (fun p : VectorDisorderBrownianSample n×Configuration n=>d p.2) J :=
    (integrable_const D).mono' hspinm.aestronglyMeasurable (.of_forall fun p=>by
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (fun τ _=>abs_nonneg (d τ)) (Finset.mem_univ p.2))
  have had : StronglyMeasurable[vectorSpinPast n (q:ℝ).toNNReal]
      (fun p : VectorDisorderBrownianSample n×Configuration n=>G p.1) :=
    hGm.comp_measurable (comap_measurable Prod.fst)
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (vectorSpinPast_le n _) hspin
  · intro A _ _
    exact hci.integrableOn
  · intro A hA _
    obtain ⟨B,hB,rfl⟩:=MeasurableSpace.measurableSet_comap.mp hA
    have hBg:MeasurableSet B:=((vectorBrownianFiltration n).le _) B hB
    have he:=integral_vectorMeasureSpinPathLaw_terminal_weight μ β t a ht
      (B.indicator (fun _=>1)) (measurable_const.indicator hBg) 1
      (fun sample=>by by_cases hs:sample∈B <;> simp [hs]) d
    rw [integral_pullback_indicator_one_mul J Prod.fst measurable_fst B hBg,
      integral_indicator_one_mul_eq_setIntegral P B hBg] at he
    have hmB:Measurable (B.indicator G):=hGmg.indicator hBg
    have heG:=integral_vectorMeasureSpinPathLaw_sample μ β t a ht (B.indicator G) hmB
    have hleft : (∫p in Prod.fst⁻¹' B,G p.1∂J)=∫sample in B,G sample∂P := by
      rw [←integral_indicator (measurable_fst hBg),←integral_indicator hBg]
      convert heG using 1
      apply integral_congr_ae
      exact .of_forall fun p=>by by_cases hs:p.1∈B <;> simp [hs]
    rw [hleft,he]
    exact setIntegral_condExp ((vectorBrownianFiltration n).le _)
      (integrable_vectorMeasureTerminalObservable μ β t a ht d) hB
  · exact had.aestronglyMeasurable

end QuantitativePaper
