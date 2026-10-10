module
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawProperties

@[expose] public section

/-! Unary observations contribute no extra leaves or forks. Component
choices and every replacement/append count use the actual observed trees. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
variable {m C : ℕ}

def CavityGeneratedObservedRawComponent.leafCount (U : CavityGeneratedObservedRawComponent m) : ℕ :=
  FiniteCascadeGenealogy.leafCount (asGenealogy U.tree)

theorem CavityGeneratedObservedRawComponent.leafCount_pos
    (U : CavityGeneratedObservedRawComponent m) : 0<U.leafCount :=
  FiniteCascadeGenealogy.leafCount_pos (asGenealogy U.tree)

theorem CavityGeneratedObservedRawComponent.forkCount_add_one
    (U : CavityGeneratedObservedRawComponent m) :
    (cavityGeneratedOriginForkVertices U.tree).length+1=U.leafCount :=
  cavityGeneratedOriginForkVertices_count U.tree

theorem cavityGeneratedObservedRawComponent_le_total
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount) :
    (W.component c).leafCount≤W.leafCount := by
  exact Finset.single_le_sum (fun j _=>Nat.zero_le ((W.component j).leafCount)) (Finset.mem_univ c)

theorem cavityGeneratedObservedRawComponentCount_le_leaves
    (W : CavityGeneratedObservedRawForest m) : W.componentCount≤W.leafCount := by
  calc
    W.componentCount=∑_c : Fin W.componentCount,1 := by simp
    _ ≤ W.leafCount := Finset.sum_le_sum fun c _=>
      Nat.succ_le_iff.mpr ((W.component c).leafCount_pos)

theorem cavityGeneratedObservedRawForestReplaceComponent_component_same
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (U : CavityGeneratedObservedRawComponent m) :
    (cavityGeneratedObservedRawForestReplaceComponent W c U).component c=U := by
  classical
  exact Function.update_self _ _ _

theorem cavityGeneratedObservedRawForestReplaceComponent_component_other
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (U : CavityGeneratedObservedRawComponent m) (s : Fin W.componentCount) (hs : s≠c) :
    (cavityGeneratedObservedRawForestReplaceComponent W c U).component s=W.component s := by
  classical
  exact Function.update_of_ne hs _ _

theorem cavityGeneratedObservedRawForestReplaceComponent_leafCount
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (U : CavityGeneratedObservedRawComponent m) :
    (cavityGeneratedObservedRawForestReplaceComponent W c U).leafCount+(W.component c).leafCount=
      W.leafCount+U.leafCount := by
  classical
  let f : Fin W.componentCount→ℕ := fun j=>(W.component j).leafCount
  have he : (fun j=>(Function.update W.component c U j).leafCount)=
      Function.update f c U.leafCount := by
    funext j
    by_cases hj : j=c
    · subst j; simp only [Function.update_self]
    · simp only [Function.update_of_ne hj,f]
  change (∑j : Fin W.componentCount,(Function.update W.component c U j).leafCount)+f c=
    (∑j : Fin W.componentCount,f j)+U.leafCount
  rw [he]
  change (∑j : Fin W.componentCount,Function.update f c U.leafCount j)+f c=
    (∑j : Fin W.componentCount,f j)+U.leafCount
  have hnew := Finset.sum_erase_add (s:=Finset.univ)
    (Function.update f c U.leafCount) (Finset.mem_univ c)
  have hold := Finset.sum_erase_add (s:=Finset.univ) f (Finset.mem_univ c)
  have herase : (∑j∈Finset.univ.erase c,Function.update f c U.leafCount j)=
      ∑j∈Finset.univ.erase c,f j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact Function.update_of_ne (Finset.mem_erase.mp hj).1 _ _
  simp only [Function.update_self] at hnew
  rw [herase] at hnew
  omega

theorem cavityGeneratedObservedRawForestAppendComponent_leafCount
    (W : CavityGeneratedObservedRawForest m) (U : CavityGeneratedObservedRawComponent m) :
    (cavityGeneratedObservedRawForestAppendComponent W U).leafCount=W.leafCount+U.leafCount := by
  change (∑c : Fin (W.componentCount+1),
    (Fin.snoc (α:=fun _=>CavityGeneratedObservedRawComponent m) W.component U c).leafCount)=
      (∑c : Fin W.componentCount,(W.component c).leafCount)+U.leafCount
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last]

theorem cavityGeneratedObservedRaw_component_bound_pos
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (K : ℕ) (hK : W.leafCount≤K) : 0<K :=
  (W.component c).leafCount_pos.trans_le ((cavityGeneratedObservedRawComponent_le_total W c).trans hK)

theorem cavityGeneratedObservedRaw_component_origin_cost_le
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (hm : 0 < m) (K : ℕ) (hK : W.leafCount≤K) :
    (W.component c).leafCount+(cavityGeneratedOriginForkVertices (W.tree c)).length≤
      printedGeneratedOriginAppendCost K m := by
  have hk := (cavityGeneratedObservedRawComponent_le_total W c).trans hK
  have hf := (W.component c).forkCount_add_one
  change (cavityGeneratedOriginForkVertices (W.tree c)).length+1=(W.component c).leafCount at hf
  have hfle : (cavityGeneratedOriginForkVertices (W.tree c)).length≤K-1 := by omega
  have hfm : (cavityGeneratedOriginForkVertices (W.tree c)).length≤(K-1)*m := by
    calc
      _ = (cavityGeneratedOriginForkVertices (W.tree c)).length*1 := by omega
      _ ≤ (K-1)*m := Nat.mul_le_mul hfle (Nat.succ_le_iff.mpr hm)
  exact Nat.add_le_add hk hfm

theorem cavityGeneratedObservedRaw_component_origin_cost_le_uniform
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (hm : 0 < m) (K L : ℕ) (hK : W.leafCount≤K) (hmL : m≤L) :
    (W.component c).leafCount+(cavityGeneratedOriginForkVertices (W.tree c)).length≤
      printedGeneratedOriginAppendCost K L :=
  (cavityGeneratedObservedRaw_component_origin_cost_le W c hm K hK).trans
    (printedGeneratedOriginAppendCost_mono le_rfl hmL)

theorem cavityGeneratedObservedRaw_component_origin_cost_le_uniform_ennreal
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (hm : 0 < m) (K L : ℕ) (hK : W.leafCount≤K) (hmL : m≤L) :
    ((W.component c).leafCount : ℝ≥0∞)+
        ((cavityGeneratedOriginForkVertices (W.tree c)).length : ℝ≥0∞)≤
      (printedGeneratedOriginAppendCost K L : ℝ≥0∞) := by
  exact_mod_cast cavityGeneratedObservedRaw_component_origin_cost_le_uniform W c hm K L hK hmL

end QuantitativeFollowup
