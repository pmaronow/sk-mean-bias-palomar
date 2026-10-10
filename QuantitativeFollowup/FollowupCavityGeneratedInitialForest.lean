module
public import QuantitativeFollowup.FollowupCavityGeneratedForestConstruction

@[expose] public section

/-! Initial replicas all branch at the actual free mark p. Binary fork
shape is retained, and the two endpoint observations remain fixed even
when p equals zero or one. This constructs the starting forest rather
than assuming its pair clocks or a mark marginal bound. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

inductive CavityGeneratedSiblingShape
  | single
  | fork (left right : CavityGeneratedSiblingShape)

def CavityGeneratedSiblingShape.tree : CavityGeneratedSiblingShape → FiniteTerminalGenealogy 1
  | .single => .advance .leaf
  | .fork S T => .fork S.tree T.tree

theorem CavityGeneratedSiblingShape.constructs
    (S : CavityGeneratedSiblingShape) (labels : ℕ → CavityGeneratedClockLabel 1)
    (hmark : labels 1 = .mark 0) :
    CavityGeneratedGenealogyConstruction labels (.advance S.tree) := by
  apply CavityGeneratedGenealogyConstruction.advance
  induction S with
  | single => exact .advance (.linear 0)
  | fork S T ihS ihT => exact .fork 0 hmark ihS ihT

def cavityGeneratedInitialForestLabels (i : Fin 3) : CavityGeneratedClockLabel 1 :=
  if i.val = 0 then .terminal else if i.val = 1 then .mark 0 else .initial

def cavityGeneratedInitialForest (S : CavityGeneratedSiblingShape) :
    CavityGeneratedConstructedForest 1 where
  componentCount := 1
  depth := fun _ => 2
  tree := fun _ => .advance S.tree
  label := fun _ => cavityGeneratedInitialForestLabels
  terminal_label := fun _ => rfl
  initial_label := fun _ => rfl
  construction := by
    intro c
    apply S.constructs
    rfl

theorem cavityGeneratedInitialForest_orderSet_eq_univ
    (S : CavityGeneratedSiblingShape) :
    (cavityGeneratedInitialForest S).clockTemplate.orderSet = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro h c j
  fin_cases j
  · change h 0 ≤ (1:Paper.Overlap)
    exact (h 0).property.2
  · change (0:Paper.Overlap) ≤ h 0
    exact (h 0).property.1

theorem cavityGeneratedInitialForest_three_defects
    {n : ℕ} (hn : 0 < n) (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : 0 ≤ a)
    (S : CavityGeneratedSiblingShape)
    (c : Fin 3 → Fin (cavityGeneratedInitialForest S).componentCount)
    (b e : (r : Fin 3) → ObservationLeaf ((cavityGeneratedInitialForest S).tree (c r))) :
    (∫ h, cavityGeneratedForestThreeDefectMoment D μ a
      (cavityGeneratedInitialForest S).depth (cavityGeneratedInitialForest S).tree
      ((cavityGeneratedInitialForest S).clockTemplate.clock h) c b e
      ∂(CavityGeneratedMarkProgram.initial : CavityGeneratedMarkProgram Paper.Overlap 1).measure
        (parisiFreeMeasure μ a)) ≤
      cavityThirdMoment D μ a := by
  have h := cavityGeneratedConstructedForest_three_defects_count_bound hn D μ a ha
    (.initial : CavityGeneratedMarkProgram Paper.Overlap 1)
    (cavityGeneratedInitialForest S) c b e 0 (by exact Nat.le_refl 0)
  simpa only [cavityGeneratedThreeDefectCountConstant, CavityGeneratedMarkProgram.constructorCount,
    Nat.zero_add, pow_zero, Nat.one_mul, Nat.cast_one, one_mul,
    cavityGeneratedInitialForest_orderSet_eq_univ, CavityGeneratedMarkProgram.measure,
    Measure.restrict_univ] using h

end QuantitativeFollowup
