module
public import QuantitativePaper.VectorMeasureTerminalSpinPairing

@[expose] public section

/-! The true arbitrary-profile gradient evaluated along its diffusion is
measurable in the whole Wiener past, rather than only an initial record. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

theorem adapted_vectorMeasureSpinMean (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) :
    Measurable[vectorBrownianFiltration n (q : ℝ).toNNReal]
      (vectorMeasureSpinMean (n:=n) μ β t ht q) := by
  have hq : Measurable[vectorBrownianFiltration n (q : ℝ).toNNReal]
      (fun _ : VectorDisorderBrownianSample n=>q) := measurable_const
  have hm := (measurable_vectorMeasureGradient (n:=n) μ β t ht).comp
    (hq.prodMk (adapted_vectorMeasureJointState (n:=n) μ β t ht (q : ℝ).toNNReal))
  dsimp only [Function.comp_def,vectorMeasureJointState] at hm
  exact hm

theorem adapted_vectorMeasureSpinMean_component (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (l : Fin n) :
    Measurable[vectorBrownianFiltration n (q : ℝ).toNNReal]
      (fun sample=>vectorMeasureSpinMean μ β t ht q sample l) := by
  have hm := (EuclideanSpace.proj l).continuous.measurable.comp
    (adapted_vectorMeasureSpinMean μ β t ht q)
  dsimp only [Function.comp_def] at hm
  exact hm

end QuantitativePaper
