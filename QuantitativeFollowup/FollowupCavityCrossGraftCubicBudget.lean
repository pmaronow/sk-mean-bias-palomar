module
public import QuantitativeFollowup.FollowupCavityGraftCubicBudget

@[expose] public section

/-! The double-graft branch budget has its literal two vertex-charge
weights. Its new branch levels are precisely the two graft vertices,
including coincident vertices. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {k : ℕ}
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

private theorem weighted_affine_sum {A : Type*} (xs : List (ℝ×A)) (f : A→ℝ) (B : ℝ) :
    (xs.map (fun c=>c.1*(B+f c.2))).sum=
      (xs.map Prod.fst).sum*B+(xs.map (fun c=>c.1*f c.2)).sum := by
  simp_rw [mul_add]
  rw [List.sum_map_add,List.sum_map_mul_right]

private theorem weighted_affine_sum_left {A : Type*} (xs : List (ℝ×A)) (f : A→ℝ) (B W : ℝ) :
    (xs.map (fun c=>c.1*(W*(B+f c.2)+
      (xs.map (fun d=>d.1*f d.2)).sum))).sum=
      (xs.map Prod.fst).sum*W*B+
        (W+(xs.map Prod.fst).sum)*(xs.map (fun d=>d.1*f d.2)).sum := by
  rw [show (fun c : ℝ×A=>c.1*(W*(B+f c.2)+
      (xs.map (fun d=>d.1*f d.2)).sum))=
      (fun c=>c.1*(W*(B+f c.2))+c.1*(xs.map (fun d=>d.1*f d.2)).sum)
      from funext (fun c=>mul_add _ _ _)]
  rw [List.sum_map_add]
  have hfirst : (xs.map (fun c=>c.1*(W*(B+f c.2)))).sum=
      W*((xs.map Prod.fst).sum*B+(xs.map (fun c=>c.1*f c.2)).sum) := by
    have he : (fun c : ℝ×A=>c.1*(W*(B+f c.2)))=
        fun c=>W*(c.1*(B+f c.2)) := funext (fun _=>by ring)
    rw [he,List.sum_map_mul_left,weighted_affine_sum]
  rw [hfirst,List.sum_map_mul_right]
  ring

def cavityChargedCrossGraftBranchBudget (s : RSBScheme k) (a : ℝ)
    (T : FiniteTerminalGenealogy (k+2)) (f : Paper.Overlap→ℝ) : ℝ :=
  let cs:=finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)
  (cs.map (fun c=>c.1*(cs.map (fun d=>d.1*
    finiteCascadeUnweightedBranchSum (fun j=>f (cavityProfileLevel s j))
      (finiteCascadeCrossVertexGraft c.2 d.2))).sum)).sum

theorem cavityChargedCrossGraftBranchBudget_le (s : RSBScheme k) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (f : Paper.Overlap→ℝ) (hf : ∀q,0≤f q) :
    cavityChargedCrossGraftBranchBudget s a T f≤
      (FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)^2*
        (2*(∫q,f q∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a)+
          3*finiteCascadeUnweightedBranchSum (fun j=>f (cavityProfileLevel s j)) (trimRoot T)) := by
  let B:=finiteCascadeUnweightedBranchSum (fun j=>f (cavityProfileLevel s j)) (trimRoot T)
  let L:ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
  let cs:=finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)
  let W:ℝ:=(cs.map Prod.fst).sum
  let V:ℝ:=(cs.map (fun c=>c.1*f (cavityProfileLevel s c.2.depth))).sum
  let E:=∫q,f q∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a
  have hB : 0≤B:=finiteCascadeUnweightedBranchSum_nonneg _ (fun j=>hf _) _
  have hL : 0≤L:=Nat.cast_nonneg _
  have hW : W=L-a := by
    dsimp only [W,cs,L]
    rw [finiteCascadeVertexCharges_sum,leafCount_trimRoot]
  have hW0 : 0≤W:=List.sum_nonneg (by
    intro x hx
    obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hx
    exact anisotropicTrimmedVertexCharges_nonneg s a has T c hc)
  have hWL : W≤L:=by rw [hW];linarith [ha.1]
  have hV0 : 0≤V:=List.sum_nonneg (by
    intro x hx
    obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hx
    exact mul_nonneg (anisotropicTrimmedVertexCharges_nonneg s a has T c hc) (hf _))
  have hE : 0≤E:=integral_nonneg hf
  have hV : V≤L*(E+B) := by
    have hh:=cavityLevelCharges_le_free_and_branch_marks s a ha.1 has hq (trimRoot T) f hf
    rw [leafCount_trimRoot] at hh
    exact hh
  have he : cavityChargedCrossGraftBranchBudget s a T f=W^2*B+2*W*V := by
    unfold cavityChargedCrossGraftBranchBudget
    simp_rw [finiteCascadeCrossVertexGraft_branchSum]
    change (cs.map (fun c=>c.1*(cs.map (fun d=>d.1*(B+
      f (cavityProfileLevel s c.2.depth)+f (cavityProfileLevel s d.2.depth)))).sum)).sum=_
    have hi (c : ℝ×FiniteCascadeRecordVertex (trimRoot T)) :
        (cs.map (fun d=>d.1*(B+f (cavityProfileLevel s c.2.depth)+
          f (cavityProfileLevel s d.2.depth)))).sum=
        W*(B+f (cavityProfileLevel s c.2.depth))+V :=
      weighted_affine_sum cs (fun v=>f (cavityProfileLevel s v.depth))
        (B+f (cavityProfileLevel s c.2.depth))
    simp_rw [hi]
    have hh:=weighted_affine_sum_left cs (fun v=>f (cavityProfileLevel s v.depth)) B W
    change _=W^2*B+2*W*V
    rw [hh]
    dsimp only [W,V]
    ring
  rw [he]
  change _≤L^2*(2*E+3*B)
  have hWB : W^2*B≤L^2*B:=mul_le_mul_of_nonneg_right ((sq_le_sq₀ hW0 hL).mpr hWL) hB
  have hWV : W*V≤L*(L*(E+B)):=mul_le_mul hWL hV hV0 hL
  nlinarith

end QuantitativeFollowup
