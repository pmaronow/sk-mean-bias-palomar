module
public import HexagonPaper.PathHeatSourceLemma

@[expose] public section

/-! The normalized Gaussian path heat lemma on the genuine reference law.
The source derivative measures retain their original index and atoms.
Auxiliary signed jets need only fixed-auxiliary TV continuity. Actual
Gaussian observations, finite Price differentiation, raw auxiliary/count
integration, Bernstein limits and common Fernique domination are proved
inside the imported chain. No density, response, normalizer positivity,
finite derivative or limiting derivative is an input hypothesis. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FourPapersCommon
open scoped Topology BigOperators unitInterval NNReal ENNReal BoundedContinuousFunction
namespace HexagonPaper
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E K : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [Fintype K] [Nonempty K] [TopologicalSpace K] [DiscreteTopology K]
  [MeasurableSpace K] [BorelSpace K] [MeasurableSingletonClass K]
variable {A J : ℕ} {a b : ℝ}

theorem lem_fnd_path_heat_finite_tree
    (μ : Measure E) [IsGaussian μ] (hab : a<b)
    (d : PathHeatSectionwiseSignedSource (Icc a b) E K (pathHeatFiniteTreeIndex A J))
    (C : ℝ≥0) (hs : PathHeatFiniteTreeSourceHypotheses a b hab.le d C)
    (c : Icc a b→Fin (A+J)→C(I,I)) (dc : Icc a b→Fin (A+J)→C(I,ℝ))
    (δ : Fin (A+J)→ℝ) (W : Fin (A+J)→Fin (A+J)→ℝ)
    (hc : ∀l,Continuous (fun z=>c z l)) (hdcc : ∀l,Continuous (fun z=>dc z l))
    (hstrict : ∀z : Icc a b,z.val∈Ioo a b→∀l,StrictMono (c z l))
    (hroot : ∀z l,c z l 0=0)
    (hdc : ∀z∈Ioo a b,∀l t,
      HasDerivAt (fun u=>(c (projIcc a b hab.le u) l t:ℝ))
        (dc (projIcc a b hab.le z) l t) z) :
    let ι := pathHeatFiniteTreeIndexEmbedding A J
    let f := fun u=>pathHeatSectionwiseNativeWienerExpectation μ d ι c δ W (projIcc a b hab.le u)
    let r := fun u=>pathHeatSourcePrintedResponse μ d ι c dc δ W (projIcc a b hab.le u)
    let g := fun u=>Real.log (pathHeatSectionwiseNativeWienerNormalizer μ d ι c δ W (projIcc a b hab.le u))
    let s := fun u=>pathHeatSourcePrintedLogNormalizerResponse μ d ι c dc δ W (projIcc a b hab.le u)
    (∀z,0<pathHeatSectionwiseNativeWienerNormalizer μ d ι c δ W z) ∧
    (∀x∈Ioo a b,HasDerivAt f (r x) x ∧ HasDerivAt g (s x) x) ∧
    ContDiffOn ℝ 1 f (Ioo a b) ∧ ContDiffOn ℝ 1 g (Ioo a b) ∧
    HasDerivWithinAt f (r a) (Ici a) a ∧ HasDerivWithinAt f (r b) (Iic b) b ∧
    HasDerivWithinAt g (s a) (Ici a) a ∧ HasDerivWithinAt g (s b) (Iic b) b := by
  exact lem_fnd_path_heat μ hab d (C*(1+A+J))
    (hs.analytic hab.le d C) (pathHeatFiniteTreeIndexEmbedding A J) c dc δ W
    hc hdcc hstrict hroot hdc

end HexagonPaper
