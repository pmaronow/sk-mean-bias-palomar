module
public import FourPapersCommon.FiniteCascadeVertexCharges

@[expose] public section

/-! Actual recorded-tree vertex weights are nonnegative and sum exactly
to the number of leaves minus the genuine outer tilt. -/
noncomputable section
namespace FourPapersCommon
open FiniteTerminalGenealogy
set_option maxHeartbeats 1500000

theorem finiteCascadeVertexInteriorCharges_nonneg (a : ℕ → ℝ)
    (ha : ∀j,0 ≤ a j) (hanti : Antitone a) (h0 : a 0 ≤ 1)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    ∀c∈finiteCascadeVertexInteriorCharges a T,0 ≤ c.1 := by
  induction T with
  | leaf => simp [finiteCascadeVertexInteriorCharges]
  | @advance j T ih =>
      intro c hc
      rcases List.mem_cons.mp hc with hc | hc
      · subst c
        exact sub_nonneg.mpr (finiteCascadeTreeRootCoefficient_ge a ha hanti h0 T)
      · rcases List.mem_map.mp hc with ⟨d,hd,rfl⟩
        exact ih d hd
  | fork T U ihT ihU =>
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · rcases List.mem_map.mp hc with ⟨d,hd,rfl⟩
        exact ihT d hd
      · rcases List.mem_map.mp hc with ⟨d,hd,rfl⟩
        exact ihU d hd

theorem finiteCascadeVertexCharges_nonneg (a : ℕ → ℝ)
    (ha : ∀j,0 ≤ a j) (hanti : Antitone a) (h0 : a 0 ≤ 1)
    (s : ℝ) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (hs : s ≤ finiteCascadeTreeRootCoefficient a T) :
    ∀c∈finiteCascadeVertexCharges a s T,0 ≤ c.1 := by
  intro c hc
  rcases List.mem_cons.mp hc with hc | hc
  · subst c
    exact sub_nonneg.mpr hs
  · exact finiteCascadeVertexInteriorCharges_nonneg a ha hanti h0 T c hc

theorem finiteCascadeVertexInteriorCharges_sum (a : ℕ → ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    finiteCascadeTreeRootCoefficient a T +
      ((finiteCascadeVertexInteriorCharges a T).map Prod.fst).sum =
        (FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ) := by
  induction T with
  | leaf => simp [finiteCascadeTreeRootCoefficient,finiteCascadeVertexInteriorCharges,
      asGenealogy,FiniteCascadeGenealogy.leafCount]
  | @advance j T ih =>
      simp only [finiteCascadeTreeRootCoefficient,finiteCascadeVertexInteriorCharges,
        List.map_cons,List.sum_cons,List.map_map,Function.comp_def,asGenealogy,
        FiniteCascadeGenealogy.leafCount] at *
      linarith
  | fork T U ihT ihU =>
      simp only [finiteCascadeTreeRootCoefficient,finiteCascadeVertexInteriorCharges,
        List.map_append,List.sum_append,List.map_map,Function.comp_def,asGenealogy,
        FiniteCascadeGenealogy.leafCount,Nat.cast_add] at *
      linarith

theorem finiteCascadeVertexCharges_sum (a : ℕ → ℝ) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    ((finiteCascadeVertexCharges a s T).map Prod.fst).sum =
      (FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s := by
  simp only [finiteCascadeVertexCharges,List.map_cons,List.sum_cons]
  linarith [finiteCascadeVertexInteriorCharges_sum a T]

end FourPapersCommon
