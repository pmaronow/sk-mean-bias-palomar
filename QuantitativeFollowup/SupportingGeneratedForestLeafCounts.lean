module
public import QuantitativeFollowup.SupportingGeneratedNormalizerForest

@[expose] public section

/-! Exact total leaf counts for actual constructed forests. Component
replacement and the independent binary normalizer retain their genuine
genealogies; neither grid depth nor a guessed growth parameter enters. -/
noncomputable section
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m M C : ℕ}

def cavityGeneratedComponentLeafCount (U : CavityGeneratedConstructedComponent m) : ℕ :=
  FiniteCascadeGenealogy.leafCount (asGenealogy U.tree)

def cavityGeneratedForestLeafCount (W : CavityGeneratedConstructedForest m) : ℕ :=
  ∑c : Fin W.componentCount,cavityGeneratedComponentLeafCount (W.component c)

theorem cavityGeneratedComponentLeafCount_pos (U : CavityGeneratedConstructedComponent m) :
    0<cavityGeneratedComponentLeafCount U :=
  FiniteCascadeGenealogy.leafCount_pos (asGenealogy U.tree)

theorem cavityGeneratedForestLeafCount_eq_tree_sum (W : CavityGeneratedConstructedForest m) :
    cavityGeneratedForestLeafCount W=
      ∑c : Fin W.componentCount,FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) := rfl

theorem cavityGeneratedForestLeafCount_ofComponents
    (U : Fin C→CavityGeneratedConstructedComponent m) :
    cavityGeneratedForestLeafCount (cavityGeneratedForestOfComponents U)=
      ∑c : Fin C,cavityGeneratedComponentLeafCount (U c) := rfl

theorem cavityGeneratedComponentLeafCount_le_total (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) :
    cavityGeneratedComponentLeafCount (W.component c)≤cavityGeneratedForestLeafCount W := by
  change cavityGeneratedComponentLeafCount (W.component c)≤
    ∑j : Fin W.componentCount,cavityGeneratedComponentLeafCount (W.component j)
  exact Finset.single_le_sum (fun j _=>Nat.zero_le (cavityGeneratedComponentLeafCount (W.component j)))
    (Finset.mem_univ c)

theorem cavityGeneratedForest_componentCount_le_leaves (W : CavityGeneratedConstructedForest m) :
    W.componentCount≤cavityGeneratedForestLeafCount W := by
  calc
    W.componentCount = ∑_c : Fin W.componentCount,1 := by simp
    _ ≤ cavityGeneratedForestLeafCount W :=
      Finset.sum_le_sum fun c _=>Nat.succ_le_iff.mpr (cavityGeneratedComponentLeafCount_pos (W.component c))

theorem cavityGeneratedForestLeafCount_reindex (W : CavityGeneratedConstructedForest m)
    (τ : Fin m→Fin M) : cavityGeneratedForestLeafCount (W.reindex τ)=cavityGeneratedForestLeafCount W := rfl

theorem cavityGeneratedForestLeafCount_replace_component
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (U : CavityGeneratedConstructedComponent m) :
    cavityGeneratedForestLeafCount (cavityGeneratedForestOfComponents (Function.update W.component c U))+
      cavityGeneratedComponentLeafCount (W.component c)=
      cavityGeneratedForestLeafCount W+cavityGeneratedComponentLeafCount U := by
  classical
  let f : Fin W.componentCount→ℕ := fun j=>cavityGeneratedComponentLeafCount (W.component j)
  have he : (fun j=>cavityGeneratedComponentLeafCount (Function.update W.component c U j))=
      Function.update f c (cavityGeneratedComponentLeafCount U) := by
    funext j
    by_cases hj : j=c
    · subst j
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hj,f]
  rw [cavityGeneratedForestLeafCount_ofComponents,he]
  change (∑j : Fin W.componentCount,Function.update f c (cavityGeneratedComponentLeafCount U) j)+f c=
    (∑j : Fin W.componentCount,f j)+cavityGeneratedComponentLeafCount U
  have hnew := Finset.sum_erase_add (s:=Finset.univ)
    (Function.update f c (cavityGeneratedComponentLeafCount U)) (Finset.mem_univ c)
  have hold := Finset.sum_erase_add (s:=Finset.univ) f (Finset.mem_univ c)
  have herase : (∑j∈Finset.univ.erase c,Function.update f c (cavityGeneratedComponentLeafCount U) j)=
      ∑j∈Finset.univ.erase c,f j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact Function.update_of_ne (Finset.mem_erase.mp hj).1 _ _
  simp only [Function.update_self] at hnew
  rw [herase] at hnew
  omega

theorem cavityGeneratedForestLeafCount_append_component
    (W : CavityGeneratedConstructedForest m) (U : CavityGeneratedConstructedComponent m) :
    cavityGeneratedForestLeafCount (W.appendComponent U)=
      cavityGeneratedForestLeafCount W+cavityGeneratedComponentLeafCount U := by
  change (∑c : Fin (W.componentCount+1),
    cavityGeneratedComponentLeafCount (m:=m)
      (Fin.snoc (α:=fun _=>CavityGeneratedConstructedComponent m) W.component U c))=
      (∑c : Fin W.componentCount,cavityGeneratedComponentLeafCount (W.component c))+
        cavityGeneratedComponentLeafCount U
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last]

theorem cavityGeneratedForestLeafCount_append_normalizer
    (W : CavityGeneratedConstructedForest m) :
    cavityGeneratedForestLeafCount (printedGeneratedNormalizerAppendedForest W)=
      cavityGeneratedForestLeafCount W+2 := by
  rw [printedGeneratedNormalizerAppendedForest,cavityGeneratedForestLeafCount_append_component,
    cavityGeneratedForestLeafCount_reindex]
  rfl

theorem cavityGeneratedForest_sum_component_squares_le
    (W : CavityGeneratedConstructedForest m) :
    (∑c : Fin W.componentCount,(cavityGeneratedComponentLeafCount (W.component c))^2)≤
      (cavityGeneratedForestLeafCount W)^2 :=
  Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _=>Nat.zero_le _)

theorem cavityGeneratedForest_sum_component_squares_real_le
    (W : CavityGeneratedConstructedForest m) :
    (∑c : Fin W.componentCount,((cavityGeneratedComponentLeafCount (W.component c) : ℝ))^2)≤
      (cavityGeneratedForestLeafCount W : ℝ)^2 := by
  have he : (∑c : Fin W.componentCount,(cavityGeneratedComponentLeafCount (W.component c) : ℝ))=
      (cavityGeneratedForestLeafCount W : ℝ) := by
    simp only [cavityGeneratedForestLeafCount,Nat.cast_sum]
  exact (Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _=>Nat.cast_nonneg _)).trans_eq
    (congrArg (fun x : ℝ=>x^2) he)

end QuantitativeFollowup
