module
public import QuantitativePaper.VectorFinitePastSpinPairing
public import QuantitativePaper.VectorDyadicGridJetAgreement
public import QuantitativePaper.VectorDyadicGridLawAgreement
public import QuantitativePaper.VectorMeasureMarkedConditionalLaw
public import FourPapersCommon.BoundedConditionalPairing

@[expose] public section

/-! Every finite terminal observable has its genuine full-Wiener-past
conditional expectation, and agrees with the actual grid-measure version. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace QuantitativePaper
open FourPapersCommon OverlapPaper SpinGlass SpinGlass.Targets SpinGlass.AT
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem measurable_vectorFiniteTerminalObservable (s : RSBScheme k) (β t : ℝ)
    (ht : t≤1) (d : Configuration n→ℝ) :
    Measurable (fun sample : VectorDisorderBrownianSample n=>terminalMean
      (vectorTerminalExponent n β t sample.1 (vectorFiniteState s β t ht 1 sample)) d) := by
  have hm := (continuous_vectorTerminalMean_joint β t d).measurable.comp
    (measurable_vectorFiniteJointState (n:=n) s β t ht 1)
  dsimp only [Function.comp_def,vectorFiniteJointState] at hm
  exact hm

theorem adapted_vectorFiniteBackwardObservable (s : RSBScheme k) (β t : ℝ)
    (ht : t≤1) (d : Configuration n→ℝ) (i : ℕ) :
    Measurable[vectorBrownianFiltration n (s.q i).toNNReal]
      (fun sample : VectorDisorderBrownianSample n=>vectorBackwardMean s β t d i
        (vectorFiniteJointState s β t ht (s.q i).toNNReal sample)) :=
  (measurable_vectorBackwardMean s β t d i).comp
    (adapted_vectorFiniteJointState s β t ht _)

theorem vectorFinite_terminal_observable_condExp (s : RSBScheme k) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (d : Configuration n→ℝ) (i : ℕ) (hi : i≤k+2) :
    (vectorFiniteDisorderTilt s β t a)[(fun sample : VectorDisorderBrownianSample n=>
      terminalMean (vectorTerminalExponent n β t sample.1 (vectorFiniteState s β t ht.le 1 sample)) d)|
        vectorBrownianFiltration n (s.q i).toNNReal]=ᵐ[vectorFiniteDisorderTilt s β t a]
    (fun sample=>vectorBackwardMean s β t d i
        (vectorFiniteJointState s β t ht.le (s.q i).toNNReal sample)) := by
  haveI := vectorFiniteDisorderTilt_probability (n:=n) s β t a
  let D:=∑σ : Configuration n,|d σ|
  have hd σ : |d σ|≤D:=Finset.single_le_sum (fun τ _=>abs_nonneg (d τ)) (Finset.mem_univ σ)
  apply condExp_of_bounded_past_pairings (vectorBrownianFiltration n (s.q i).toNNReal)
    (vectorFiniteDisorderTilt s β t a) ((vectorBrownianFiltration n).le _)
    _ _ (measurable_vectorFiniteTerminalObservable s β t ht.le d)
    (adapted_vectorFiniteBackwardObservable s β t ht.le d i).stronglyMeasurable D
  · exact fun sample=>terminalMean_bound _ d D hd
  · exact fun sample=>abs_vectorBackwardMean_le s β t d D hd i _
  · intro Z hZ hC
    exact vectorFinite_terminal_mean_pairing_past s β t a hβ ht d i hi
      Z hZ 1 (fun sample=>by simpa using hC sample)

theorem vectorMeasureTerminalObservable_grid_eq_finite (μ : Paper.ParisiMeasure) (j : ℕ)
    (β t : ℝ) (ht : t≤1) (d : Configuration n→ℝ) (sample : VectorDisorderBrownianSample n) :
    vectorMeasureTerminalObservable (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t ht d sample=
      terminalMean (vectorTerminalExponent n β t sample.1
        (vectorFiniteState (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t ht 1 sample)) d := by
  unfold vectorMeasureTerminalObservable
  rw [vectorMeasureState_grid_eq_finite μ j β t ht 1 le_rfl]

theorem vectorMeasure_grid_terminal_observable_condExp (μ : Paper.ParisiMeasure) (j : ℕ)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (d : Configuration n→ℝ)
    (i : ℕ) (hi : i≤vectorDyadicIndex j+3) :
    (vectorMeasureDisorderTilt (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t a)[
      vectorMeasureTerminalObservable (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t ht.le d|
        vectorBrownianFiltration n ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q i).toNNReal]
      =ᵐ[vectorFiniteDisorderTilt (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a]
        (fun sample=>vectorBackwardMean (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t d i
          (vectorFiniteJointState (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t ht.le
            ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q i).toNNReal sample)) := by
  rw [vectorMeasureDisorderTilt_grid_eq_finite μ j β t a ht.le]
  have hf : vectorMeasureTerminalObservable (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t ht.le d=
      (fun sample : VectorDisorderBrownianSample n=>terminalMean
        (vectorTerminalExponent n β t sample.1 (vectorFiniteState
          (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t ht.le 1 sample)) d) :=
    funext (vectorMeasureTerminalObservable_grid_eq_finite μ j β t ht.le d)
  rw [hf]
  exact vectorFinite_terminal_observable_condExp _ β t a hβ ht d i hi

end QuantitativePaper
