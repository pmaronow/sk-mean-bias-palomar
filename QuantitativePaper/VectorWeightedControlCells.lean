module
public import QuantitativePaper.VectorFiniteControlCells

@[expose] public section

/-! Genuine bounded initial-past-weighted control verification in actual
finite Cole--Hopf cells. The weight is admitted by the proved vector Itô
expectation theorem, not by an assumed change-of-measure identity. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000

theorem vectorFiniteControlCell_weighted_ito {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (μ : Paper.ParisiMeasure)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (hA : IsVectorParisiControl A)
    (Z : VectorDisorderBrownianSample n→ℝ) (hZ : Measurable[vectorBrownianFiltration n 0] Z)
    (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C)
    (i : ℕ) (hi : i≤k+1) (a b : ℝ≥0) (hab : a≤b) (hb : (b : ℝ)≤ s.q (i+1)) :
    Integrable (fun sample => Z sample*(vectorFiniteCellPotential s β t sample.1 i b
        (vectorControlledState ((1-t)*β^2) μ A b sample)-
      vectorFiniteCellPotential s β t sample.1 i a
        (vectorControlledState ((1-t)*β^2) μ A a sample))) (vectorDisorderBrownianMeasure n) ∧
    (∫sample,Z sample*(vectorFiniteCellPotential s β t sample.1 i b
        (vectorControlledState ((1-t)*β^2) μ A b sample)-
      vectorFiniteCellPotential s β t sample.1 i a
        (vectorControlledState ((1-t)*β^2) μ A a sample)) ∂vectorDisorderBrownianMeasure n)=
      ∫sample,(∫r in Ioc a b,Z sample*vectorFiniteControlCellSource s β t μ sample.1 i r
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
    test hf Z hZ C hC a b hab (by apply NNReal.coe_le_coe.mp;rw [hT];exact hb)
  have he : (fun sample => Z sample*(test.f b sample (X b sample)-test.f a sample (X a sample)))=
      (fun sample => Z sample*(vectorFiniteCellPotential s β t sample.1 i b (X b sample)-
        vectorFiniteCellPotential s β t sample.1 i a (X a sample))) := by
    funext sample
    simp only [test,vectorFiniteCellSampleTimeData,zero_add]
  rw [he] at hh
  refine ⟨hh.1,hh.2.trans ?_⟩
  apply integral_congr_ae
  exact Eventually.of_forall (fun sample => by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r _
    change Z sample*vectorItoGenerator test X (vectorControlDrift c μ A) (Real.sqrt c) r sample=
      Z sample*vectorFiniteControlCellSource s β t μ sample.1 i r (X r sample) (A r sample)
    congr 1
    change fderiv ℝ (vectorFiniteCellPotential s β t sample.1 i (0+r)) (X r sample)
      (vectorControlDrift c μ A r sample)+
      (Real.sqrt c)^2/2*vectorBilinearTrace
        (vectorHessian (vectorFiniteCellPotential s β t sample.1 i (0+r)) (X r sample))+
      vectorFiniteCellTimeField s β t sample.1 i (0+r) (X r sample)=_
    rw [zero_add,Real.sq_sqrt hc]
    exact vectorFiniteControlCell_generator s β t μ sample.1 i r (X r sample) (A r sample))

end QuantitativePaper
