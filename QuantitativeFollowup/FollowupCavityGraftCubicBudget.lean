module
public import QuantitativeFollowup.FollowupCavityIntroducedLevels
public import QuantitativeFollowup.FollowupCavityVertexGraftLaw

@[expose] public section

/-! Cubic branch budgets for the literal single and double graft trees,
with actual nonnegative streaming vertex charges. Inherited branch
levels are retained and the new levels are the grafted vertices. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {k : ℕ}
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

def cavityChargedGraftBranchBudget (s : RSBScheme k) (a : ℝ)
    (T : FiniteTerminalGenealogy (k+2)) (f : Paper.Overlap→ℝ) : ℝ :=
  ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)).map
    (fun c=>c.1*finiteCascadeUnweightedBranchSum (fun j=>f (cavityProfileLevel s j))
      (finiteCascadeVertexGraft c.2))).sum

theorem cavityChargedGraftBranchBudget_le (s : RSBScheme k) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (f : Paper.Overlap→ℝ) (hf : ∀q,0≤f q) :
    cavityChargedGraftBranchBudget s a T f≤
      (FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)*
        ((∫q,f q∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a)+
          2*finiteCascadeUnweightedBranchSum (fun j=>f (cavityProfileLevel s j)) (trimRoot T)) := by
  let B:=finiteCascadeUnweightedBranchSum (fun j=>f (cavityProfileLevel s j)) (trimRoot T)
  let L:ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
  let cs:=finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)
  have hB : 0≤B:=finiteCascadeUnweightedBranchSum_nonneg _ (fun j=>hf _) _
  have hW : (cs.map Prod.fst).sum=L-a := by
    dsimp only [cs,L]
    rw [finiteCascadeVertexCharges_sum,leafCount_trimRoot]
  have hv:=cavityLevelCharges_le_free_and_branch_marks s a ha.1 has hq (trimRoot T) f hf
  rw [leafCount_trimRoot] at hv
  have he : cavityChargedGraftBranchBudget s a T f=
      (L-a)*B+(cs.map (fun c=>c.1*f (cavityProfileLevel s c.2.depth))).sum := by
    unfold cavityChargedGraftBranchBudget
    simp_rw [finiteCascadeVertexGraft_branchSum,mul_add]
    rw [List.sum_map_add]
    change (cs.map (fun c=>c.1*B)).sum+_= _
    rw [List.sum_map_mul_right,hW]
  rw [he]
  change _≤L*((∫q,f q∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a)+2*B)
  change (cs.map (fun c=>c.1*f (cavityProfileLevel s c.2.depth))).sum≤
    L*((∫q,f q∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a)+B) at hv
  nlinarith [mul_nonneg ha.1 hB]

end QuantitativeFollowup
