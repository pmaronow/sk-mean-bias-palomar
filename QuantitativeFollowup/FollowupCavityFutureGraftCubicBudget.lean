module
public import QuantitativeFollowup.FollowupCavityFutureDepthLevels
public import QuantitativeFollowup.FollowupCavityFutureVertexGraftLaw
public import QuantitativeFollowup.FollowupCavityGraftCubicBudget

@[expose] public section

/-! The strict-future graft budget has the actual vertex charges and free
Stieltjes measure. Its two new branch levels are the recorded vertex and
its true future split; neither is supplied as a moment estimate. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {k : ℕ}
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def cavityChargedFutureGraftBranchBudget (s : RSBScheme k) (a : ℝ)
    (T : FiniteTerminalGenealogy (k+2)) (f : Paper.Overlap→ℝ) : ℝ :=
  ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)).map
    (fun c=>c.1*(∫q : Paper.Overlap,if cavityProfileLevel s c.2.depth<q then
      finiteCascadeUnweightedBranchSum (fun j=>f (cavityProfileLevel s j))
        (finiteCascadeFutureVertexGraft c.2 (cavityFiniteFutureDepth s c.2.depth q)) else 0
          ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a))).sum

theorem cavityChargedFutureGraftBranchBudget_le (s : RSBScheme k) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (f : Paper.Overlap→ℝ) (hf : ∀q,0≤f q) :
    cavityChargedFutureGraftBranchBudget s a T f≤
      2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)*
        ((∫q,f q∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a)+
          finiteCascadeUnweightedBranchSum (fun j=>f (cavityProfileLevel s j)) (trimRoot T)) := by
  let ν:=parisiFreeMeasure (Paper.parisiSchemeMeasure s) a
  let B:=finiteCascadeUnweightedBranchSum (fun j=>f (cavityProfileLevel s j)) (trimRoot T)
  let E:=∫q,f q∂ν
  let L:ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
  let cs:=finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)
  have hB : 0≤B:=finiteCascadeUnweightedBranchSum_nonneg _ (fun j=>hf _) _
  have hE : 0≤E:=integral_nonneg hf
  have hi (F : Paper.Overlap→ℝ) : Integrable F ν := by
    dsimp only [ν]
    rw [←vectorProfileFreeMeasure_eq_actual_free s a ha.1 has hq]
    exact integrable_vectorProfileFreeMeasure s a F
  have hm : ν.real univ=1-a := by
    change (parisiFreeMeasure (Paper.parisiSchemeMeasure s) a univ).toReal=1-a
    rw [parisiFreeMeasure_univ,ENNReal.toReal_ofReal (by linarith [ha.2])]
  have hb (v : FiniteCascadeRecordVertex (trimRoot T)) :
      (∫q : Paper.Overlap,if cavityProfileLevel s v.depth<q then
        finiteCascadeUnweightedBranchSum (fun j=>f (cavityProfileLevel s j))
          (finiteCascadeFutureVertexGraft v (cavityFiniteFutureDepth s v.depth q)) else 0∂ν)≤B+f (cavityProfileLevel s v.depth)+E := by
    have he : (∫q : Paper.Overlap,if cavityProfileLevel s v.depth<q then
        finiteCascadeUnweightedBranchSum (fun j=>f (cavityProfileLevel s j))
          (finiteCascadeFutureVertexGraft v (cavityFiniteFutureDepth s v.depth q)) else 0∂ν)=
        ∫q : Paper.Overlap,if cavityProfileLevel s v.depth<q then B+f (cavityProfileLevel s v.depth)+f q else 0∂ν := by
      apply integral_congr_ae
      filter_upwards [ae_cavityFiniteFutureDepth_level s a ha.1 has hq v.depth
        (v.depth_le.trans (by omega : k+1≤k+2))] with q hq'
      by_cases h:cavityProfileLevel s v.depth<q
      · rw [ite_eq_left h,ite_eq_left h,finiteCascadeFutureVertexGraft_branchSum _ v _
          (cavityFiniteFutureDepth_le s v.depth q),hq' h]
      · rw [ite_eq_right h,ite_eq_right h]
    rw [he]
    have hh : (∫q : Paper.Overlap,if cavityProfileLevel s v.depth<q then
        B+f (cavityProfileLevel s v.depth)+f q else 0∂ν)≤
        ∫q : Paper.Overlap,B+f (cavityProfileLevel s v.depth)+f q∂ν := by
      apply integral_mono (hi _) (hi _)
      intro q
      dsimp only
      split_ifs
      · exact le_rfl
      · exact add_nonneg (add_nonneg hB (hf (cavityProfileLevel s v.depth))) (hf q)
    have hev : (∫q : Paper.Overlap,B+f (cavityProfileLevel s v.depth)+f q∂ν)=
        (1-a)*(B+f (cavityProfileLevel s v.depth))+E := by
      rw [integral_add (hi _) (hi _),integral_const,hm]
      rfl
    rw [hev] at hh
    apply hh.trans
    calc
      (1-a)*(B+f (cavityProfileLevel s v.depth))+E≤
          1*(B+f (cavityProfileLevel s v.depth))+E :=
        by simpa only [add_comm] using add_le_add_right (mul_le_mul_of_nonneg_right
          (show 1-a≤1 by linarith [ha.1])
          (add_nonneg hB (hf (cavityProfileLevel s v.depth)))) E
      _ = B+f (cavityProfileLevel s v.depth)+E := by ring

  have hW : (cs.map Prod.fst).sum=L-a := by
    dsimp only [cs,L]
    rw [finiteCascadeVertexCharges_sum,leafCount_trimRoot]
  have hv:=cavityLevelCharges_le_free_and_branch_marks s a ha.1 has hq (trimRoot T) f hf
  rw [leafCount_trimRoot] at hv
  have hh : cavityChargedFutureGraftBranchBudget s a T f≤
      (cs.map (fun c=>c.1*(B+f (cavityProfileLevel s c.2.depth)+E))).sum := by
    unfold cavityChargedFutureGraftBranchBudget
    apply List.sum_le_sum
    intro c hc
    exact mul_le_mul_of_nonneg_left (hb c.2) (anisotropicTrimmedVertexCharges_nonneg s a has T c hc)
  have he : (cs.map (fun c=>c.1*(B+f (cavityProfileLevel s c.2.depth)+E))).sum=
      (L-a)*(B+E)+(cs.map (fun c=>c.1*f (cavityProfileLevel s c.2.depth))).sum := by
    rw [show (fun c : ℝ×FiniteCascadeRecordVertex (trimRoot T)=>c.1*(B+f (cavityProfileLevel s c.2.depth)+E))=
        (fun c=>c.1*(B+E)+c.1*f (cavityProfileLevel s c.2.depth)) from funext (fun c=>by ring)]
    rw [List.sum_map_add,List.sum_map_mul_right,hW]
  rw [he] at hh
  change (cs.map (fun c=>c.1*f (cavityProfileLevel s c.2.depth))).sum≤L*(E+B) at hv
  change _≤2*L*(E+B)
  nlinarith [mul_nonneg ha.1 (add_nonneg hB hE)]

end QuantitativeFollowup
