module
public import QuantitativePaper.VectorFiniteCellSampleTest
public import QuantitativePaper.VectorControlledState
public import QuantitativePaper.VectorItoIntervalExpectation

@[expose] public section

/-! Exact control verification on every genuine finite profile cell, with
the literal random initial disorder and constructed controlled Wiener state.
The square gap and coefficient mismatch are actual algebraic generator terms. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def vectorFiniteControlCellSource {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (μ : Paper.ParisiMeasure) (p : Couplings n×ℝ) (i : ℕ) (r : ℝ) (x A : Field n) : ℝ :=
  ((1-t)*β^2)/2*Paper.parisiCDF μ r*‖A‖^2-
    ((1-t)*β^2)/2*Paper.parisiCDF μ r*‖gradient (vectorFiniteCellPotential s β t p i r) x-A‖^2+
    ((1-t)*β^2)/2*(Paper.parisiCDF μ r-s.m i)*
      ‖gradient (vectorFiniteCellPotential s β t p i r) x‖^2

theorem vectorFiniteControlCell_generator {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (μ : Paper.ParisiMeasure) (p : Couplings n×ℝ) (i : ℕ) (r : ℝ) (x A : Field n) :
    fderiv ℝ (vectorFiniteCellPotential s β t p i r) x
        (((1-t)*β^2*Paper.parisiCDF μ r) • A)+
      ((1-t)*β^2)/2*vectorBilinearTrace
        (vectorHessian (vectorFiniteCellPotential s β t p i r) x)+
      vectorFiniteCellTimeField s β t p i r x=
      vectorFiniteControlCellSource s β t μ p i r x A := by
  have hh := vectorFiniteCellTimeField_generator_cancel s β t p i r x
  rw [ContinuousLinearMap.map_smul,smul_eq_mul,←inner_gradient_left]
  unfold vectorFiniteControlCellSource
  rw [norm_sub_sq_real]
  linarith

theorem vectorFiniteControlCell_ito {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (μ : Paper.ParisiMeasure)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (hA : IsVectorParisiControl A)
    (i : ℕ) (hi : i≤k+1) (a b : ℝ≥0) (hab : a≤b) (hb : (b : ℝ) ≤ s.q (i+1)) :
    Integrable (fun sample => vectorFiniteCellPotential s β t sample.1 i b
        (vectorControlledState ((1-t)*β^2) μ A b sample)-
      vectorFiniteCellPotential s β t sample.1 i a
        (vectorControlledState ((1-t)*β^2) μ A a sample)) (vectorDisorderBrownianMeasure n) ∧
    (∫ sample,vectorFiniteCellPotential s β t sample.1 i b
        (vectorControlledState ((1-t)*β^2) μ A b sample)-
      vectorFiniteCellPotential s β t sample.1 i a
        (vectorControlledState ((1-t)*β^2) μ A a sample) ∂vectorDisorderBrownianMeasure n)=
      ∫ sample,(∫ r in Ioc a b,vectorFiniteControlCellSource s β t μ sample.1 i r
        (vectorControlledState ((1-t)*β^2) μ A r sample) (A r sample)
        ∂nonnegativeLebesgueMeasure) ∂vectorDisorderBrownianMeasure n := by
  let c := (1-t)*β^2
  have hc : 0≤c := by dsimp only [c];positivity
  let X := vectorControlledState c μ A
  let T : ℝ≥0 := (s.q (i+1)).toNNReal
  have hT : (T : ℝ)=s.q (i+1) := Real.coe_toNNReal _ (s.q_nonneg (by omega))
  let test := vectorFiniteCellSampleTimeData (n := n) s β t hβ ht i hi 0 T (by rw [zero_add,hT])
  let hf := vectorFiniteCellSampleSpatialTest s β t i 0 X
    (continuous_vectorControlledState c μ A hA) (stronglyAdapted_vectorControlledState c μ A hA)
  have hh := vector_ito_interval_generator (vectorItoCharacteristics_vectorControlledState c μ A hA)
    test hf (fun _ => 1) measurable_const 1 (by intro _;norm_num) a b hab
    (by apply NNReal.coe_le_coe.mp;rw [hT];exact hb)
  have he : (fun sample => (1 : ℝ)*(test.f b sample (X b sample)-test.f a sample (X a sample)))=
      (fun sample => vectorFiniteCellPotential s β t sample.1 i b (X b sample)-
        vectorFiniteCellPotential s β t sample.1 i a (X a sample)) := by
    funext sample
    simp only [test,vectorFiniteCellSampleTimeData,one_mul,zero_add]
  rw [he] at hh
  refine ⟨hh.1,hh.2.trans ?_⟩
  apply integral_congr_ae
  exact Eventually.of_forall (fun sample => by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r _
    simp only [one_mul]
    change fderiv ℝ (vectorFiniteCellPotential s β t sample.1 i (0+r)) (X r sample)
      (vectorControlDrift c μ A r sample)+
      (Real.sqrt c)^2/2*vectorBilinearTrace
        (vectorHessian (vectorFiniteCellPotential s β t sample.1 i (0+r)) (X r sample))+
      vectorFiniteCellTimeField s β t sample.1 i (0+r) (X r sample)=_
    rw [zero_add,Real.sq_sqrt hc]
    exact vectorFiniteControlCell_generator s β t μ sample.1 i r (X r sample) (A r sample))

end QuantitativePaper
