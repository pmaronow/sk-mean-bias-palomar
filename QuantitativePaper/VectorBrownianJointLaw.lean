module
public import QuantitativePaper.VectorBrownianScheme

@[expose] public section

/-! The literal normalized finite-profile density on a continuous Brownian
sample space. Its finite-grid projection is the already constructed exact
disorder/field/spin law. This is a law construction; the drift under this
tilt is a separate stochastic theorem. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon

def vectorBrownianJointMap {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : VectorDisorderBrownianSample n × Configuration n) :
    FiniteHistory (VectorState n) (k+2) × Configuration n :=
  (vectorSchemeBrownianHistory s β t p.1,p.2)

theorem measurable_vectorBrownianJointMap {n k : ℕ} (s : RSBScheme k) (β t : ℝ) :
    Measurable (vectorBrownianJointMap (n := n) s β t) :=
  (measurable_vectorSchemeBrownianHistory s β t).prodMap measurable_id

def vectorBrownianJointDensity {n k : ℕ} (s : RSBScheme k) (β t a : ℝ)
    (p : VectorDisorderBrownianSample n × Configuration n) : ℝ≥0∞ :=
  vectorNormalizedDensity s β t a (vectorBrownianJointMap s β t p)

theorem measurable_vectorBrownianJointDensity {n k : ℕ} (s : RSBScheme k) (β t a : ℝ) :
    Measurable (vectorBrownianJointDensity (n := n) s β t a) := by
  have hD : Measurable (vectorNormalizedDensity (n := n) s β t a) :=
    ((measurable_vectorFullHistoryDensity s β t a).comp measurable_fst).mul
      (measurable_vectorHistoryTerminalWeight s β t)
  exact hD.comp (measurable_vectorBrownianJointMap s β t)

def vectorBrownianJointLaw {n k : ℕ} (s : RSBScheme k) (β t a : ℝ) :
    Measure (VectorDisorderBrownianSample n × Configuration n) :=
  ((vectorDisorderBrownianMeasure n).prod (Measure.count : Measure (Configuration n))).withDensity
    (vectorBrownianJointDensity s β t a)

theorem vectorBrownianJointLaw_map {n k : ℕ} (s : RSBScheme k) (β t a : ℝ) (ht : t ≤ 1) :
    (vectorBrownianJointLaw (n := n) s β t a).map (vectorBrownianJointMap s β t) =
      vectorJointLaw s β t a := by
  have hD : Measurable (vectorNormalizedDensity (n := n) s β t a) :=
    ((measurable_vectorFullHistoryDensity s β t a).comp measurable_fst).mul
      (measurable_vectorHistoryTerminalWeight s β t)
  unfold vectorBrownianJointLaw vectorBrownianJointDensity
  rw [map_withDensity_pullback _ _ (measurable_vectorBrownianJointMap s β t) _ hD]
  change (((vectorDisorderBrownianMeasure n).prod Measure.count).map
    (Prod.map (vectorSchemeBrownianHistory s β t) id)).withDensity _ = _
  rw [← Measure.map_prod_map _ _ (measurable_vectorSchemeBrownianHistory s β t) measurable_id,
    vectorSchemeBrownianHistory_map s β t ht,Measure.map_id,
    vectorJointLaw_eq_normalizedDensity,Measure.compProd_const]

theorem vectorBrownianJointLaw_probability {n k : ℕ} (s : RSBScheme k) (β t a : ℝ) (ht : t ≤ 1) :
    IsProbabilityMeasure (vectorBrownianJointLaw (n := n) s β t a) := by
  constructor
  have h := congrArg (fun P : Measure (FiniteHistory (VectorState n) (k+2) × Configuration n) =>
    P univ) (vectorBrownianJointLaw_map (n := n) s β t a ht)
  rw [Measure.map_apply (measurable_vectorBrownianJointMap s β t) MeasurableSet.univ,
    preimage_univ] at h
  exact h.trans (vectorJointLaw_probability (n := n) s β t a).measure_univ

theorem hasLaw_vectorBrownianJointHistory {n k : ℕ} (s : RSBScheme k) (β t a : ℝ) (ht : t ≤ 1) :
    HasLaw (vectorBrownianJointMap (n := n) s β t) (vectorJointLaw s β t a)
      (vectorBrownianJointLaw s β t a) :=
  ⟨(measurable_vectorBrownianJointMap s β t).aemeasurable,
    vectorBrownianJointLaw_map s β t a ht⟩

end QuantitativePaper
