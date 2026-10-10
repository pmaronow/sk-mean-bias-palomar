module
public import QuantitativePaper.VectorCascadeReplicaDefect
public import QuantitativePaper.VectorFiniteObservableConditionalExpectation
public import QuantitativePaper.VectorCovarianceTraceMeasurability

@[expose] public section

/-! The finite cascade split defect is the literal actual conditional two-spin
replica defect for the corresponding grid measure. Conditional second
moments are transported by the genuine full-past conditional expectation. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal BigOperators Topology
namespace QuantitativePaper
open FourPapersCommon SpinGlass SpinGlass.Targets SpinGlass.AT
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vectorMeasure_grid_first_moment_eq_backward (μ : Paper.ParisiMeasure) (j : ℕ)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (i : ℕ) (hi : i≤vectorDyadicIndex j+3)
    (q : Paper.Overlap) (hq : (q:ℝ)=(Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q i)
    (l : Fin n) :
    (fun sample : VectorDisorderBrownianSample n=>vectorMeasureSpinMean
      (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t ht.le q sample l)
      =ᵐ[vectorFiniteDisorderTilt (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a]
        (fun sample=>vectorBackwardMean (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t
          (fun σ=>Paper.spinSign (σ l)) i (vectorFiniteJointState
            (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t ht.le (q:ℝ).toNNReal sample)) := by
  have hb:=vectorMeasure_grid_terminal_observable_condExp μ j β t a hβ ht
    (fun σ=>Paper.spinSign (σ l)) i hi
  rw [←hq,vectorMeasureDisorderTilt_grid_eq_finite μ j β t a ht.le] at hb
  have hm:=vectorMeasure_terminal_mean_condExp (n:=n)
    (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t a hβ ht q l
  rw [vectorMeasureDisorderTilt_grid_eq_finite μ j β t a ht.le] at hm
  unfold vectorMeasureTerminalObservable at hb
  exact hm.symm.trans hb

theorem vectorMeasure_grid_second_moment_eq_backward (μ : Paper.ParisiMeasure) (j : ℕ)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (i : ℕ) (hi : i≤vectorDyadicIndex j+3)
    (q : Paper.Overlap) (hq : (q:ℝ)=(Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q i)
    (l r : Fin n) :
    (fun sample : VectorDisorderBrownianSample n=>
      vectorMeasureSpinCovariance (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t a ht.le q sample l r+
        vectorMeasureSpinMean (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t ht.le q sample l*
          vectorMeasureSpinMean (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t ht.le q sample r)
      =ᵐ[vectorFiniteDisorderTilt (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a]
        (fun sample=>vectorBackwardMean (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t
          (fun σ=>Paper.spinSign (σ l)*Paper.spinSign (σ r)) i (vectorFiniteJointState
            (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t ht.le (q:ℝ).toNNReal sample)) := by
  have hb:=vectorMeasure_grid_terminal_observable_condExp μ j β t a hβ ht
    (fun σ=>Paper.spinSign (σ l)*Paper.spinSign (σ r)) i hi
  rw [←hq,vectorMeasureDisorderTilt_grid_eq_finite μ j β t a ht.le] at hb
  filter_upwards [hb] with sample hs
  dsimp only [vectorMeasureSpinCovariance]
  rw [vectorMeasureDisorderTilt_grid_eq_finite μ j β t a ht.le,hs]
  ring

theorem vectorConditionalReplicaDefect_grid_eq_finite (hn : 0<n) (μ : Paper.ParisiMeasure) (j : ℕ)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (i : ℕ) (hi : i≤vectorDyadicIndex j+3)
    (q : Paper.Overlap) (hq : (q:ℝ)=(Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q i) :
    vectorConditionalReplicaDefect (n:=n) (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t a ht.le q=
      ∫sample : VectorDisorderBrownianSample n,vectorFiniteReplicaMatrixDefect (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t i q
        (vectorFiniteJointState (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t ht.le
          (q:ℝ).toNNReal sample)∂vectorFiniteDisorderTilt (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a := by
  let ν:=Paper.parisiGridMeasure μ (vectorDyadicIndex j)
  have hm : Measurable (vectorConditionalReplicaMatrixDefect (n:=n) ν β t a ht.le q):=by
    unfold vectorConditionalReplicaMatrixDefect
    apply Measurable.add
    · apply Measurable.sub
      · apply Measurable.const_mul
        exact Finset.measurable_sum _ fun l _=>Finset.measurable_sum _ fun r _=>
          ((measurable_vectorMeasureSpinCovariance_entry ν β t a ht.le q l r).add
            (((adapted_vectorMeasureSpinMean_component ν β t ht.le q l).mono
              ((vectorBrownianFiltration n).le _) le_rfl).mul
              ((adapted_vectorMeasureSpinMean_component ν β t ht.le q r).mono
                ((vectorBrownianFiltration n).le _) le_rfl))).pow_const 2
      · apply Measurable.const_mul
        apply Measurable.const_mul
        exact Finset.measurable_sum _ fun l _=>
          ((adapted_vectorMeasureSpinMean_component ν β t ht.le q l).mono
            ((vectorBrownianFiltration n).le _) le_rfl).pow_const 2
    · exact measurable_const
  rw [vectorConditionalReplicaDefect_eq_matrix_integral hn ν β t a hβ ht q,
    integral_vectorMeasureSpinPathLaw_sample ν β t a ht.le _ hm]
  dsimp only [ν]
  rw [vectorMeasureDisorderTilt_grid_eq_finite μ j β t a ht.le]
  apply integral_congr_ae
  have h1:=ae_all_iff.2 (fun l : Fin n=>vectorMeasure_grid_first_moment_eq_backward μ j β t a hβ ht i hi q hq l)
  have h2:=ae_all_iff.2 (fun l : Fin n=>ae_all_iff.2 (fun r : Fin n=>
    vectorMeasure_grid_second_moment_eq_backward μ j β t a hβ ht i hi q hq l r))
  filter_upwards [h1,h2] with sample hs1 hs2
  unfold vectorConditionalReplicaMatrixDefect vectorFiniteReplicaMatrixDefect
  simp_rw [hs2,hs1]

end QuantitativePaper
