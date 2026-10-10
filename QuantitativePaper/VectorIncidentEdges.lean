module
public import QuantitativePaper.VectorSiteGaussianCoordinates

@[expose] public section

/-! The actual triangular disorder has exactly N-1 independent coordinates
incident to a fixed site. No diagonal-completion coordinate is incident. -/
noncomputable section
open Set
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets

abbrev IncidentEdge {n : ℕ} (i : Fin n) := {e : Edge n // e.val.1=i ∨ e.val.2=i}

def incidentEdgeNeighborEquiv {n : ℕ} (i : Fin n) : IncidentEdge i ≃ {j : Fin n // j ≠ i} where
  toFun e := if h : e.val.val.1=i then
    ⟨e.val.val.2, by intro he; have hl := e.val.property; rw [h,he] at hl; exact hl.false⟩
    else ⟨e.val.val.1,h⟩
  invFun j := if h : i < j.val then
    ⟨⟨(i,j.val),h⟩,Or.inl rfl⟩
    else ⟨⟨(j.val,i),lt_of_le_of_ne (le_of_not_gt h) j.property⟩,Or.inr rfl⟩
  left_inv e := by
    rcases e.property with h | h
    · have hl : i < e.val.val.2 := by simpa [h] using e.val.property
      apply Subtype.ext
      apply Subtype.ext
      simp [h,hl]
      exact Prod.ext h.symm rfl
    · have hl : e.val.val.1 < i := by simpa [h] using e.val.property
      have hne : e.val.val.1 ≠ i := hl.ne
      have hnot : ¬i < e.val.val.1 := not_lt.mpr hl.le
      apply Subtype.ext
      apply Subtype.ext
      simp [hne,hnot,h]
      exact Prod.ext rfl h.symm
  right_inv j := by
    apply Subtype.ext
    by_cases hj : i < j.val
    · simp [hj]
    · simp [hj,j.property]

theorem card_incidentEdge {n : ℕ} (i : Fin n) : Fintype.card (IncidentEdge i) = n-1 := by
  rw [Fintype.card_congr (incidentEdgeNeighborEquiv i)]
  simp [Fintype.card_subtype_compl]

end QuantitativePaper
