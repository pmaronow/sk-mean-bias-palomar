module
public import FourPapersCommon.FiniteCascadeConditionalMarks
public import FourPapersCommon.FiniteCascadeTreeFeatureScores

@[expose] public section

/-! The finite density charges are indexed by actual recorded-tree
vertices. This identifies the literal first and second feature scores with
weighted vertex derivatives, without introducing auxiliary score premises. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
variable {S I : Type} [Fintype S] [Fintype I]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

@[reducible] def finiteCascadeVertexInteriorCharges (a : ℕ → ℝ) :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) → List (ℝ × FiniteCascadeRecordVertex T)
  | _, .leaf => []
  | _, @FiniteTerminalGenealogy.advance j T =>
      (finiteCascadeTreeRootCoefficient a T-a j, .child (.root T)) ::
        (finiteCascadeVertexInteriorCharges a T).map (fun z => (z.1,.child z.2))
  | _, .fork T U =>
      (finiteCascadeVertexInteriorCharges a T).map (fun z => (z.1,.left z.2)) ++
        (finiteCascadeVertexInteriorCharges a U).map (fun z => (z.1,.right z.2))

def finiteCascadeVertexCharges (a : ℕ → ℝ) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) : List (ℝ × FiniteCascadeRecordVertex T) :=
  (finiteCascadeTreeRootCoefficient a T-s, .root T) :: finiteCascadeVertexInteriorCharges a T

theorem finiteCascadeTreeInteriorFieldSum_eq_vertex_sum
    (a : ℕ → ℝ) (F : ℕ → FiniteStateField S → ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (H : FiniteStateField S)
    (z : Records (FiniteStateField S) S T) :
    finiteCascadeTreeInteriorFieldSum a F T z =
      ((finiteCascadeVertexInteriorCharges a T).map
        (fun c => c.1*F c.2.depth (c.2.field H z))).sum := by
  induction T generalizing H with
  | leaf => rfl
  | @advance j T ih =>
      simp only [finiteCascadeTreeInteriorFieldSum, finiteCascadeVertexInteriorCharges,
        List.map_cons, List.sum_cons, List.map_map, Function.comp_def,
        FiniteCascadeRecordVertex.depth, FiniteCascadeRecordVertex.field]
      exact congrArg (fun r => _+r) (ih z.1 z.2)
  | fork T U ihT ihU =>
      simp only [finiteCascadeTreeInteriorFieldSum, finiteCascadeVertexInteriorCharges,
        List.map_append, List.sum_append, List.map_map, Function.comp_def,
        FiniteCascadeRecordVertex.depth, FiniteCascadeRecordVertex.field]
      exact congrArg₂ (·+·) (ihT H z.1) (ihU H z.2)

theorem finiteCascadeTreeFieldSum_eq_vertex_sum
    (a : ℕ → ℝ) (F : ℕ → FiniteStateField S → ℝ) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (H : FiniteStateField S)
    (z : Records (FiniteStateField S) S T) :
    finiteCascadeTreeFieldSum a F s T H z =
      ((finiteCascadeVertexCharges a s T).map
        (fun c => c.1*F c.2.depth (c.2.field H z))).sum := by
  simp only [finiteCascadeVertexCharges, List.map_cons, List.sum_cons,
    FiniteCascadeRecordVertex.depth, FiniteCascadeRecordVertex.field,
    finiteCascadeTreeFieldSum]
  exact congrArg (fun r => _+r) (finiteCascadeTreeInteriorFieldSum_eq_vertex_sum a F T H z)

theorem finiteCascadeTreeFeatureScore_eq_vertex_sum (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (H K : FiniteStateField S)
    (z : Records (FiniteStateField S) S T) (θ : ℝ) :
    finiteCascadeTreeFeatureScore V a L s T H K z θ =
      finiteCascadeTreeTerminalFeature K T z -
        ((finiteCascadeVertexCharges a s T).map (fun c => c.1 *
          fderiv ℝ (finiteStateGaussianTerminalCascade V a L c.2.depth)
            (c.2.field (H+θ • K) (finiteCascadeShiftRecords K θ T z)) K)).sum := by
  rw [finiteCascadeTreeFeatureScore, finiteCascadeTreeFieldSum_eq_vertex_sum]

theorem finiteCascadeTreeFeatureSecondCharge_eq_vertex_sum (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (H K : FiniteStateField S)
    (z : Records (FiniteStateField S) S T) (θ : ℝ) :
    finiteCascadeTreeFeatureSecondCharge V a L s T H K z θ =
      ((finiteCascadeVertexCharges a s T).map (fun c => c.1 *
        fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L c.2.depth))
          (c.2.field (H+θ • K) (finiteCascadeShiftRecords K θ T z)) K K)).sum := by
  rw [finiteCascadeTreeFeatureSecondCharge, finiteCascadeTreeFieldSum_eq_vertex_sum]

end FourPapersCommon
