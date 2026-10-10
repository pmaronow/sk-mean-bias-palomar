module
public import QuantitativePaper.VectorFiniteCellGenerator
public import QuantitativePaper.VectorHeatState
public import QuantitativePaper.VectorBoundedTimeIntegral

@[expose] public section

/-! The actual finite-cell heat evolution, obtained from the proved vector
Itô formula with zero drift. All finite-cell analytic tests are instantiated. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal Topology ContDiff BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem vectorFiniteCell_heat_ito {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (p : Couplings n×ℝ) (i : ℕ) (hi : i≤k+1)
    (a : ℝ) (T : ℝ≥0) (hT : a+(T : ℝ) ≤ s.q (i+1)) (x : Field n) :
    Integrable (fun sample => vectorFiniteCellPotential s β t p i (a+T)
      (vectorHeatState (Real.sqrt ((1-t)*β^2)) x T sample)-
      vectorFiniteCellPotential s β t p i a x) (vectorDisorderBrownianMeasure n) ∧
    (∫ sample,vectorFiniteCellPotential s β t p i (a+T)
        (vectorHeatState (Real.sqrt ((1-t)*β^2)) x T sample)-
        vectorFiniteCellPotential s β t p i a x ∂vectorDisorderBrownianMeasure n)=
      -((1-t)*β^2)/2*(s.m i)*∫ r in Ioc 0 T,
        (∫ sample,‖gradient (vectorFiniteCellPotential s β t p i (a+r))
          (vectorHeatState (Real.sqrt ((1-t)*β^2)) x r sample)‖^2
          ∂vectorDisorderBrownianMeasure n) ∂nonnegativeLebesgueMeasure := by
  let c := (1-t)*β^2
  have hc : 0≤c := by dsimp only [c];positivity
  let X := vectorHeatState (Real.sqrt c) x
  let test := vectorFiniteCellTimeData s β t hβ ht p i hi a T hT
  let hf := vectorFiniteCellSpatialTest s β t p i a X
    (continuous_vectorHeatState _ x) (stronglyAdapted_vectorHeatState _ x)
  have hIto := vector_ito_time_expectation (vectorItoCharacteristics_vectorHeatState (Real.sqrt c) x)
    test hf (fun _ => 1) measurable_const 1 (by intro _;norm_num)
  have he : (fun sample => (1 : ℝ)*(test.f T sample (X T sample)-test.f 0 sample (X 0 sample)))=
      (fun sample => vectorFiniteCellPotential s β t p i (a+T) (X T sample)-
        vectorFiniteCellPotential s β t p i a x) := by
    funext sample
    simp only [test,vectorFiniteCellTimeData,one_mul,NNReal.coe_zero,add_zero,vectorHeatState_zero,X]
  rw [he] at hIto
  refine ⟨hIto.1,?_⟩
  let H : ℝ≥0→VectorDisorderBrownianSample n→ℝ := fun r sample =>
    vectorBilinearTrace (vectorHessian (vectorFiniteCellPotential s β t p i (a+r)) (X r sample))
  let F : ℝ≥0→VectorDisorderBrownianSample n→ℝ := fun r sample =>
    vectorFiniteCellTimeField s β t p i (a+r) (X r sample)
  have hHm : Measurable (Function.uncurry H) := by
    unfold H vectorBilinearTrace
    apply Finset.measurable_fun_sum
    intro l _
    change Measurable (fun z : ℝ≥0×VectorDisorderBrownianSample n =>
      directionalHessian (vectorFiniteCellPotential s β t p i (a+z.1)) (X z.1 z.2)
        (EuclideanSpace.single l (1 : ℝ)))
    simpa only [Function.comp_def] using
      (continuous_vectorFiniteCellPotential_hessian_diagonal s β t p i l).measurable.comp
        (show Measurable (fun z : ℝ≥0×VectorDisorderBrownianSample n =>
          (a+(z.1 : ℝ),X z.1 z.2)) from
          (measurable_const.add (NNReal.continuous_coe.measurable.comp measurable_fst)).prodMk
            (measurable_uncurry_vectorHeatState _ x))
  have hFm : Measurable (Function.uncurry F) := by
    simpa only [Function.comp_def,Function.uncurry_def,F] using
      (continuous_vectorFiniteCellTimeField s β t p i hi).measurable.comp
        (show Measurable (fun z : ℝ≥0×VectorDisorderBrownianSample n =>
          (a+(z.1 : ℝ),X z.1 z.2)) from
          (measurable_const.add (NNReal.continuous_coe.measurable.comp measurable_fst)).prodMk
            (measurable_uncurry_vectorHeatState _ x))
  have hHb (r : ℝ≥0) (_ : r≤T) (sample : VectorDisorderBrownianSample n) :
      ‖H r sample‖≤((n : ℝ≥0)*hf.secondBound : ℝ≥0) := by
    simpa only [H,Real.norm_eq_abs,NNReal.coe_mul,NNReal.coe_natCast] using hf.trace_bound r sample
  have hFb (r : ℝ≥0) (_ : r≤T) (sample : VectorDisorderBrownianSample n) :
      ‖F r sample‖≤test.bound := norm_vectorFiniteCellTimeField_le s β t ht.le p i hi _ _
  have hHF := vectorBoundedTimeIntegral_fubini H hHm T ((n : ℝ≥0)*hf.secondBound) hHb
  have hFF := vectorBoundedTimeIntegral_fubini F hFm T test.bound hFb
  have hTfin : IsFiniteMeasure (nonnegativeLebesgueMeasure.restrict (Ioc (0 : ℝ≥0) T)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using
      lt_top_iff_ne_top.mpr (nonnegativeLebesgueMeasure_Ioc_ne_top 0 T)⟩
  letI := hTfin
  have hHi : Integrable (fun r => ∫ sample,H r sample ∂vectorDisorderBrownianMeasure n)
      (nonnegativeLebesgueMeasure.restrict (Ioc 0 T)) := by
    simpa only [Function.uncurry_def] using hHF.1.integral_prod_left
  have hFi : Integrable (fun r => ∫ sample,F r sample ∂vectorDisorderBrownianMeasure n)
      (nonnegativeLebesgueMeasure.restrict (Ioc 0 T)) := by
    simpa only [Function.uncurry_def] using hFF.1.integral_prod_left
  calc
    _ = c/2*(∫ sample,(∫ r in Ioc 0 T,H r sample ∂nonnegativeLebesgueMeasure)
          ∂vectorDisorderBrownianMeasure n)+
        ∫ sample,(∫ r in Ioc 0 T,F r sample ∂nonnegativeLebesgueMeasure)
          ∂vectorDisorderBrownianMeasure n := by
      simpa only [test,vectorFiniteCellTimeData,timeFTCIntegral,H,F,one_mul,
        ContinuousLinearMap.map_zero,integral_zero,mul_zero,zero_add,
        Real.sq_sqrt hc] using hIto.2
    _ = c/2*(∫ r in Ioc 0 T,(∫ sample,H r sample ∂vectorDisorderBrownianMeasure n)
          ∂nonnegativeLebesgueMeasure)+
        ∫ r in Ioc 0 T,(∫ sample,F r sample ∂vectorDisorderBrownianMeasure n)
          ∂nonnegativeLebesgueMeasure := by rw [hHF.2,hFF.2]
    _ = ∫ r in Ioc 0 T,((c/2)*(∫ sample,H r sample ∂vectorDisorderBrownianMeasure n)+
        ∫ sample,F r sample ∂vectorDisorderBrownianMeasure n) ∂nonnegativeLebesgueMeasure := by
      rw [integral_add (hHi.const_mul _) hFi,integral_const_mul]
    _ = ∫ r in Ioc 0 T,(∫ sample,(c/2)*H r sample+F r sample
        ∂vectorDisorderBrownianMeasure n) ∂nonnegativeLebesgueMeasure := by
      apply integral_congr_ae
      filter_upwards [hHF.1.prod_right_ae,hFF.1.prod_right_ae] with r hHr hFr
      change Integrable (H r) (vectorDisorderBrownianMeasure n) at hHr
      change Integrable (F r) (vectorDisorderBrownianMeasure n) at hFr
      rw [integral_add (hHr.const_mul _) hFr,integral_const_mul]
    _ = _ := by
      simp_rw [show ∀r sample,(c/2)*H r sample+F r sample=
          -(c/2)*(s.m i)*‖gradient (vectorFiniteCellPotential s β t p i (a+r)) (X r sample)‖^2
        from fun r sample => by
          simpa only [H,F,c,add_comm,neg_div] using
            vectorFiniteCellTimeField_generator_cancel s β t p i (a+r) (X r sample)]
      simp only [integral_const_mul]
      simp only [c,X,neg_div]

end QuantitativePaper
