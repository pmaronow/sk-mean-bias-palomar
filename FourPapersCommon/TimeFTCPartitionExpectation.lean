module
public import FourPapersCommon.TimeFTCPartition

@[expose] public section

/-! Quantitative expectation convergence of the literal right-endpoint
fundamental-theorem-of-calculus partition terms. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus
open scoped BigOperators NNReal Topology
namespace FourPapersCommon
set_option maxHeartbeats 1500000
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {T : ℝ≥0} (P : Measure Ω) [IsProbabilityMeasure P]

theorem integrable_timeFTCIntegral (d : TimeFTCData Ω E T)
    (X : ℝ≥0 → Ω → E) (hX : Measurable (Function.uncurry X))
    (Z : Ω → ℝ) (hZ : Measurable Z) (C : ℝ≥0) (hC : ∀ sample,‖Z sample‖ ≤ C) :
    Integrable (timeFTCIntegral d X Z) P := by
  haveI : IsFiniteMeasure (nonnegativeLebesgueMeasure.restrict (Ioc (0 : ℝ≥0) T)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using
      lt_top_iff_ne_top.mpr (nonnegativeLebesgueMeasure_Ioc_ne_top 0 T)⟩
  have hm : Measurable (fun p : ℝ≥0 × Ω => Z p.2*d.ft p.1 p.2 (X p.1 p.2)) :=
    (hZ.comp measurable_snd).mul (d.ft_measurable.comp
      ((NNReal.continuous_coe.measurable.comp measurable_fst).prodMk (measurable_snd.prodMk hX)))
  have hi : StronglyMeasurable (timeFTCIntegral d X Z) :=
    hm.stronglyMeasurable.integral_prod_left' (μ := nonnegativeLebesgueMeasure.restrict (Ioc 0 T))
  apply Integrable.of_bound hi.aestronglyMeasurable (C*d.bound*(T : ℝ))
  apply Eventually.of_forall
  intro sample
  have hh : ‖timeFTCIntegral d X Z sample‖ ≤
      (C*d.bound)*(nonnegativeLebesgueMeasure.restrict (Ioc (0 : ℝ≥0) T)).real univ := by
    apply norm_integral_le_of_norm_le_const
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hb := d.ft_bound s ⟨s.coe_nonneg,show (s : ℝ) ≤ T from hs.2⟩ sample (X s sample)
    rw [norm_mul]
    exact mul_le_mul (hC sample) hb (norm_nonneg _) C.coe_nonneg
  simpa only [Measure.real,Measure.restrict_apply_univ,nonnegativeLebesgueMeasure_Ioc,
    NNReal.coe_zero,sub_zero,ENNReal.toReal_ofReal T.coe_nonneg] using hh

theorem timeRightPartitionSum_expectation_error_bound (d : TimeFTCData Ω E T)
    (X : ℝ≥0 → Ω → E) (hX : Measurable (Function.uncurry X))
    (Z : Ω → ℝ) (hZ : Measurable Z) (C : ℝ≥0) (hC : ∀ sample,‖Z sample‖ ≤ C)
    (A D : ℝ≥0)
    (hi : ∀ r t : ℝ≥0,r ≤ t → t ≤ T →
      Integrable (fun sample => ‖X t sample-X r sample‖) P)
    (hinc : ∀ r t : ℝ≥0,r ≤ t → t ≤ T →
      (∫ sample,‖X t sample-X r sample‖ ∂P) ≤ A*Real.sqrt ((t : ℝ)-r)+D*((t : ℝ)-r))
    {N : ℕ} (hN : 0 < N) :
    Integrable (timeRightPartitionSum d X Z N) P ∧
    |(∫ sample,timeRightPartitionSum d X Z N sample ∂P)-
      ∫ sample,timeFTCIntegral d X Z sample ∂P| ≤
      C*d.spatialLip*(T : ℝ)*(A*Real.sqrt ((T : ℝ)/(N : ℝ))+D*((T : ℝ)/(N : ℝ))) := by
  let a : ℕ → ℝ≥0 := uniformPartitionTime T N
  let err : ℕ → Ω → ℝ := fun j=>timeFTCCellError d X Z (a j) (a (j+1))
  have hcell (j : ℕ) (hj : j ∈ Finset.range N) :=
    timeFTCCellError_expectation_bound P d X hX Z hZ C hC A D hi hinc
      (a j) (a (j+1)) (monotone_uniformPartitionTime T N (Nat.le_add_right _ _))
      (uniformPartitionTime_mem_Icc_of_le T hN (Nat.succ_le_iff.mpr (Finset.mem_range.mp hj))).2
  have hsum : Integrable (fun sample => ∑ j∈Finset.range N,err j sample) P :=
    integrable_finsetSum (Finset.range N) (fun j hj=>(hcell j hj).1)
  have hint := integrable_timeFTCIntegral P d X hX Z hZ C hC
  have heq : timeRightPartitionSum d X Z N =
      (fun sample => (∑ j∈Finset.range N,err j sample)+timeFTCIntegral d X Z sample) := by
    funext sample
    exact sub_eq_iff_eq_add.mp (timeRightPartitionSum_sub_integral d X hX Z hN sample)
  have hir : Integrable (timeRightPartitionSum d X Z N) P := by
    rw [heq]
    exact hsum.add hint
  refine ⟨hir,?_⟩
  have hdiff : (∫ sample,timeRightPartitionSum d X Z N sample ∂P)-
      ∫ sample,timeFTCIntegral d X Z sample ∂P =
      ∑ j∈Finset.range N,∫ sample,err j sample ∂P := by
    rw [← integral_sub hir hint]
    have he : (fun sample=>timeRightPartitionSum d X Z N sample-timeFTCIntegral d X Z sample) =
        (fun sample=>∑ j∈Finset.range N,err j sample) :=
      funext (timeRightPartitionSum_sub_integral d X hX Z hN)
    rw [he]
    exact integral_finsetSum (Finset.range N) (fun j hj=>(hcell j hj).1)
  rw [hdiff]
  have hdt (j : ℕ) : ((a (j+1) : ℝ≥0) : ℝ)-(a j : ℝ) = (T : ℝ)/(N : ℝ) := by
    have hh := dist_uniformPartitionTime_succ_eq T hN j
    rw [NNReal.dist_eq,abs_of_nonneg
      (sub_nonneg.mpr (show ((a j : ℝ≥0) : ℝ) ≤ a (j+1) from
        monotone_uniformPartitionTime T N (Nat.le_add_right _ _)))] at hh
    simpa only [NNReal.coe_div,NNReal.coe_natCast] using hh
  calc
    _ ≤ ∑ j∈Finset.range N,|∫ sample,err j sample ∂P| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j∈Finset.range N,C*d.spatialLip*((T : ℝ)/(N : ℝ))*
        (A*Real.sqrt ((T : ℝ)/(N : ℝ))+D*((T : ℝ)/(N : ℝ))) := by
      apply Finset.sum_le_sum
      intro j hj
      have hc := (hcell j hj).2
      rw [hdt j] at hc
      exact hc
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      have hne : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
      field_simp

end FourPapersCommon
