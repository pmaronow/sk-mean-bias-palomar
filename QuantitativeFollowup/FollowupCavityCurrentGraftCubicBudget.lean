module
public import QuantitativeFollowup.FollowupCavityCrossGraftCubicBudget
public import QuantitativeFollowup.FollowupCavityDegeneratePairCubic
public import QuantitativeFollowup.FollowupCavityGraftedCubicMoments

@[expose] public section

/-! The two marks in the current-CDF term are independently grafted at
the same vertex. Their weight is one actual vertex charge, rather than
its square. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

def cavityChargedCurrentGraftBranchBudget (s : RSBScheme k) (a : ℝ)
    (T : FiniteTerminalGenealogy (k+2)) (f : Paper.Overlap→ℝ) : ℝ :=
  ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)).map
    (fun c=>c.1*finiteCascadeUnweightedBranchSum (fun j=>f (cavityProfileLevel s j))
      (finiteCascadeCrossVertexGraft c.2 c.2))).sum

theorem cavityChargedCurrentGraftBranchBudget_le (s : RSBScheme k) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (f : Paper.Overlap→ℝ) (hf : ∀q,0≤f q) :
    cavityChargedCurrentGraftBranchBudget s a T f≤
      (FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)*
        (2*(∫q,f q∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a)+
          3*finiteCascadeUnweightedBranchSum (fun j=>f (cavityProfileLevel s j)) (trimRoot T)) := by
  let B:=finiteCascadeUnweightedBranchSum (fun j=>f (cavityProfileLevel s j)) (trimRoot T)
  let E:=∫q,f q∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a
  let L:ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
  let cs:=finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)
  have hB : 0≤B:=finiteCascadeUnweightedBranchSum_nonneg _ (fun j=>hf _) _
  have hW : (cs.map Prod.fst).sum=L-a := by
    dsimp only [cs,L]
    rw [finiteCascadeVertexCharges_sum,leafCount_trimRoot]
  have hv:=cavityLevelCharges_le_free_and_branch_marks s a ha.1 has hq (trimRoot T) f hf
  rw [leafCount_trimRoot] at hv
  have he : cavityChargedCurrentGraftBranchBudget s a T f=
      (L-a)*B+2*(cs.map (fun c=>c.1*f (cavityProfileLevel s c.2.depth))).sum := by
    unfold cavityChargedCurrentGraftBranchBudget
    simp_rw [finiteCascadeCrossVertexGraft_branchSum]
    rw [show (fun c : ℝ×FiniteCascadeRecordVertex (trimRoot T)=>
        c.1*(finiteCascadeUnweightedBranchSum (fun j=>f (cavityProfileLevel s j)) (trimRoot T)+
          f (cavityProfileLevel s c.2.depth)+f (cavityProfileLevel s c.2.depth)))=
        (fun c=>c.1*B+2*(c.1*f (cavityProfileLevel s c.2.depth))) from funext (fun c=>by dsimp [B];ring)]
    rw [List.sum_map_add,List.sum_map_mul_right,List.sum_map_mul_left,hW]
  rw [he]
  change (cs.map (fun c=>c.1*f (cavityProfileLevel s c.2.depth))).sum≤L*(E+B) at hv
  change _≤L*(2*E+3*B)
  nlinarith [mul_nonneg ha.1 hB]

def cavityChargedCurrentGraftTripleMoment (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (i l : (v : FiniteCascadeRecordVertex (trimRoot T))→
      Fin 3→ObservationLeaf (.advance (finiteCascadeCrossVertexGraft v v))) : ℝ :=
  ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)).map
    (fun c=>c.1*cavityRecordedTripleDefectMoment D (Paper.parisiSchemeMeasure s) a
      (cavityProfileLevel s) (.advance (finiteCascadeCrossVertexGraft c.2 c.2)) (i c.2) (l c.2))).sum

theorem cavityChargedCurrentGraftTripleMoment_le_free_cubic (hn : 0<n)
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (i l : (v : FiniteCascadeRecordVertex (trimRoot T))→
      Fin 3→ObservationLeaf (.advance (finiteCascadeCrossVertexGraft v v))) :
    cavityChargedCurrentGraftTripleMoment D s a T i l≤
      (FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)*
        (2*cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
          3*finiteCascadeUnweightedBranchSum
            (fun j=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s j)) (trimRoot T)) := by
  obtain ⟨hzero,hroot,hmono⟩:=cavityProfileLevel_clock s
  have hb : cavityChargedCurrentGraftTripleMoment D s a T i l≤
      cavityChargedCurrentGraftBranchBudget s a T (cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a) := by
    unfold cavityChargedCurrentGraftTripleMoment cavityChargedCurrentGraftBranchBudget
    apply List.sum_le_sum
    intro c hc
    have hh:=cavityRecorded_threeDefects_le_branch_cubic_all_pairs hn D (Paper.parisiSchemeMeasure s) a
      (cavityProfileLevel s) hzero (.advance (finiteCascadeCrossVertexGraft c.2 c.2)) hroot hmono
      (i c.2) (l c.2)
    exact mul_le_mul_of_nonneg_left hh (anisotropicTrimmedVertexCharges_nonneg s a has T c hc)
  exact hb.trans (cavityChargedCurrentGraftBranchBudget_le s a ha has hq T
    (cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a)
    (fun q=>(cavityCubicPairMoment_bounds D (Paper.parisiSchemeMeasure s) a q).1))

end QuantitativeFollowup
