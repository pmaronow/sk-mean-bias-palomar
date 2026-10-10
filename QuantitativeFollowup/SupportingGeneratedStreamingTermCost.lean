module
public import QuantitativeFollowup.SupportingGeneratedStreamingCountConstants
public import QuantitativeFollowup.FollowupCavityGeneratedOriginForkLabels

@[expose] public section

/-! Costs of actual source choices are controlled by genuine forest
leaves and inherited fork labels. No fork-count or output-budget identity
is supplied by the caller. These are supporting induction estimates. -/
noncomputable section
open scoped ENNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 700000
variable {m : ℕ}

theorem cavityGenerated_component_leaf_bound_pos
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (K : ℕ) (hK : cavityGeneratedForestLeafCount W≤K) : 0<K :=
  lt_of_lt_of_le (cavityGeneratedComponentLeafCount_pos (W.component c))
    ((cavityGeneratedComponentLeafCount_le_total W c).trans hK)

theorem cavityGenerated_component_origin_cost_le
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (hm : 0 < m) (K : ℕ) (hK : cavityGeneratedForestLeafCount W≤K) :
    FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c))+
      (cavityGeneratedOriginForkMarks W c).length ≤ printedGeneratedOriginAppendCost K m := by
  have hk : FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c))≤K :=
    (cavityGeneratedComponentLeafCount_le_total W c).trans hK
  have hf := cavityGeneratedOriginForkMarks_count W c
  have hfl : (cavityGeneratedOriginForkMarks W c).length≤K-1 := by omega
  have hmul : K-1≤(K-1)*m := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (K-1) (Nat.succ_le_of_lt hm)
  exact Nat.add_le_add hk (hfl.trans hmul)

theorem cavityGenerated_component_origin_cost_le_ennreal
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (hm : 0 < m) (K : ℕ) (hK : cavityGeneratedForestLeafCount W≤K) :
    (FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) : ℝ≥0∞)+
      ((cavityGeneratedOriginForkMarks W c).length : ℝ≥0∞) ≤
        (printedGeneratedOriginAppendCost K m : ℝ≥0∞) := by
  exact_mod_cast cavityGenerated_component_origin_cost_le W c hm K hK

theorem cavityGenerated_component_origin_cost_le_uniform
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (hm : 0 < m) (K M : ℕ) (hK : cavityGeneratedForestLeafCount W≤K) (hmM : m≤M) :
    FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c))+
      (cavityGeneratedOriginForkMarks W c).length ≤ printedGeneratedOriginAppendCost K M :=
  (cavityGenerated_component_origin_cost_le W c hm K hK).trans
    (printedGeneratedOriginAppendCost_mono le_rfl hmM)

theorem cavityGenerated_component_origin_cost_le_uniform_ennreal
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (hm : 0 < m) (K M : ℕ) (hK : cavityGeneratedForestLeafCount W≤K) (hmM : m≤M) :
    (FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) : ℝ≥0∞)+
      ((cavityGeneratedOriginForkMarks W c).length : ℝ≥0∞) ≤
        (printedGeneratedOriginAppendCost K M : ℝ≥0∞) := by
  exact_mod_cast cavityGenerated_component_origin_cost_le_uniform W c hm K M hK hmM

theorem printedGeneratedStreamingTermCosts_le (K m : ℕ) (hK : 0<K) :
    1≤printedGeneratedStreamingStepCost K m ∧
    2*printedGeneratedOriginAppendCost K m≤printedGeneratedStreamingStepCost K m ∧
    (printedGeneratedOriginAppendCost K m)^2≤printedGeneratedStreamingStepCost K m ∧
    printedGeneratedOriginAppendCost K m≤printedGeneratedStreamingStepCost K m := by
  let A := printedGeneratedOriginAppendCost K m
  have hKA : 2*A≤4*K*A := Nat.mul_le_mul_right A (by omega)
  have hKA2 : A^2≤K*A^2 := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (A^2) (Nat.succ_le_of_lt hK)
  have h1 : 1≤printedGeneratedStreamingStepCost K m := by
    unfold printedGeneratedStreamingStepCost
    omega
  have h2 : 2*A≤printedGeneratedStreamingStepCost K m := by
    unfold printedGeneratedStreamingStepCost
    dsimp only [A] at hKA
    omega
  have h3 : A^2≤printedGeneratedStreamingStepCost K m := by
    unfold printedGeneratedStreamingStepCost
    dsimp only [A] at hKA2 ⊢
    omega
  have h4 : A≤printedGeneratedStreamingStepCost K m := (by omega : A≤2*A).trans h2
  exact ⟨h1,h2,h3,h4⟩

theorem printedGeneratedStreamingTermCosts_le_ennreal (K m : ℕ) (hK : 0<K) :
    (1 : ℝ≥0∞)≤(printedGeneratedStreamingStepCost K m : ℝ≥0∞) ∧
    2*(printedGeneratedOriginAppendCost K m : ℝ≥0∞)≤
      (printedGeneratedStreamingStepCost K m : ℝ≥0∞) ∧
    (printedGeneratedOriginAppendCost K m : ℝ≥0∞)^2≤
      (printedGeneratedStreamingStepCost K m : ℝ≥0∞) ∧
    (printedGeneratedOriginAppendCost K m : ℝ≥0∞)≤
      (printedGeneratedStreamingStepCost K m : ℝ≥0∞) := by
  have H := printedGeneratedStreamingTermCosts_le K m hK
  refine ⟨?_,?_,?_,?_⟩
  · exact_mod_cast H.1
  · exact_mod_cast H.2.1
  · exact_mod_cast H.2.2.1
  · exact_mod_cast H.2.2.2

end QuantitativeFollowup
