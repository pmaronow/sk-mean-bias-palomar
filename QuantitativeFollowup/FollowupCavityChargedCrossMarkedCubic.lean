module
public import QuantitativeFollowup.FollowupCavityCrossMarkedCubic
public import QuantitativeFollowup.FollowupCavityCurrentGraftCubicBudget

@[expose] public section

/-! Charged physical cross/current cubic budgets. The actual conditional
mark products, not a hypothetical marginal or moment bound, are summed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityChargedCrossMarkedTripleMoment (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (T : FiniteTerminalGenealogy (k+2)) (i l : Fin 2 → ObservationLeaf (trimRoot T)) : ℝ :=
  let cs := finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)
  (cs.map (fun c => c.1 * (cs.map (fun d => d.1 * (∫z,
    |cavityRecordedPairProduct s (trimRoot T) i l z.1 *
      cavitySpinOverlapDefect n (cavityPhysicalCommonOverlap s (trimRoot T) c.2 d.2) z.2.1 z.2.2|
        ∂anisotropicCrossVertexMarkedLaw D s a T c.2 d.2))).sum)).sum

theorem cavityChargedCrossMarkedTripleMoment_le (hn : 0<n)
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (i l : Fin 2 → ObservationLeaf (trimRoot T)) :
    cavityChargedCrossMarkedTripleMoment D s a T i l ≤
      (FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)^2 *
        (2*cavityThirdMoment D (Paper.parisiSchemeMeasure s) a +
          3*finiteCascadeUnweightedBranchSum
            (fun d => cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)) := by
  have hb : cavityChargedCrossMarkedTripleMoment D s a T i l ≤
      cavityChargedCrossGraftBranchBudget s a T (cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a) := by
    unfold cavityChargedCrossMarkedTripleMoment cavityChargedCrossGraftBranchBudget
    apply List.sum_le_sum
    intro c hc
    apply mul_le_mul_of_nonneg_left _ (anisotropicTrimmedVertexCharges_nonneg s a has T c hc)
    apply List.sum_le_sum
    intro d hd
    apply mul_le_mul_of_nonneg_left _ (anisotropicTrimmedVertexCharges_nonneg s a has T d hd)
    rw [finiteCascadeCrossVertexGraft_branchSum]
    exact cavityCrossVertex_leaf_triple_cubic hn D s a hq T c.2 d.2 i l
  exact hb.trans (cavityChargedCrossGraftBranchBudget_le s a ha has hq T
    (cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a)
    (fun q => (cavityCubicPairMoment_bounds D (Paper.parisiSchemeMeasure s) a q).1))

def cavityChargedCurrentMarkedTripleMoment (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (T : FiniteTerminalGenealogy (k+2)) (i l : Fin 2 → ObservationLeaf (trimRoot T)) : ℝ :=
  ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)).map
    (fun c => c.1 * (∫z, |cavityRecordedPairProduct s (trimRoot T) i l z.1 *
      cavitySpinOverlapDefect n (cavityPhysicalCommonOverlap s (trimRoot T) c.2 c.2) z.2.1 z.2.2|
        ∂anisotropicCrossVertexMarkedLaw D s a T c.2 c.2))).sum

theorem cavityChargedCurrentMarkedTripleMoment_le (hn : 0<n)
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (i l : Fin 2 → ObservationLeaf (trimRoot T)) :
    cavityChargedCurrentMarkedTripleMoment D s a T i l ≤
      (FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ) *
        (2*cavityThirdMoment D (Paper.parisiSchemeMeasure s) a +
          3*finiteCascadeUnweightedBranchSum
            (fun d => cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)) := by
  have hb : cavityChargedCurrentMarkedTripleMoment D s a T i l ≤
      cavityChargedCurrentGraftBranchBudget s a T (cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a) := by
    unfold cavityChargedCurrentMarkedTripleMoment cavityChargedCurrentGraftBranchBudget
    apply List.sum_le_sum
    intro c hc
    apply mul_le_mul_of_nonneg_left _ (anisotropicTrimmedVertexCharges_nonneg s a has T c hc)
    rw [finiteCascadeCrossVertexGraft_branchSum]
    exact cavityCrossVertex_leaf_triple_cubic hn D s a hq T c.2 c.2 i l
  exact hb.trans (cavityChargedCurrentGraftBranchBudget_le s a ha has hq T
    (cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a)
    (fun q => (cavityCubicPairMoment_bounds D (Paper.parisiSchemeMeasure s) a q).1))

end QuantitativeFollowup
