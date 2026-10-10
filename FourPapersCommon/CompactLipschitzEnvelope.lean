module
public import FourPapersCommon.MinimumEnvelope
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-! Compact attainment and the genuine Lipschitz fundamental theorem for
uniformly bounded interior derivatives of a family of actual functions. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace FourPapersCommon
set_option maxHeartbeats 600000

def compactMinimumValue {ι : Type*} (S : Set ι) (F : ℝ→ι→ℝ) (t : ℝ) : ℝ:=
  sInf ((F t) '' S)

theorem compactMinimumValue_attained {ι : Type*} [TopologicalSpace ι]
    (S : Set ι) (hS : IsCompact S) (hne : S.Nonempty) (F : ℝ→ι→ℝ)
    (t : ℝ) (hc : ContinuousOn (F t) S) :
    ∃i∈S,F t i=compactMinimumValue S F t ∧ ∀j∈S,compactMinimumValue S F t≤F t j := by
  obtain ⟨i,hi,hmin⟩:=hS.exists_isMinOn hne hc
  have hb : BddBelow ((F t) '' S):=⟨F t i,by
    rintro y ⟨j,hj,rfl⟩
    exact hmin hj⟩
  have he : compactMinimumValue S F t=F t i:=by
    apply le_antisymm
    · exact csInf_le hb ⟨i,hi,rfl⟩
    · exact le_csInf (hne.image _) (by rintro y ⟨j,hj,rfl⟩;exact hmin hj)
  exact ⟨i,hi,he.symm,fun j hj=>he.symm ▸ hmin hj⟩

theorem lipschitzOnWith_of_bounded_interior_derivative (f g : ℝ→ℝ)
    (a b : ℝ) (K : NNReal) (hc : ContinuousOn f (Icc a b))
    (hd : ∀t∈Ioo a b,HasDerivAt f (g t) t)
    (hb : ∀t∈Ioo a b,|g t|≤(K : ℝ)) :
    LipschitzOnWith K f (Icc a b) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  have hordered (x : ℝ) (hx : x∈Icc a b) (y : ℝ) (hy : y∈Icc a b) (hxy : x<y) :
      dist (f x) (f y)≤(K : ℝ)*dist x y:=by
    obtain ⟨z,hz,he⟩:=exists_hasDerivAt_eq_slope f g hxy
      (hc.mono (Icc_subset_Icc hx.1 hy.2))
      (fun z hz=>hd z ⟨hx.1.trans_lt hz.1,hz.2.trans_le hy.2⟩)
    have hg:=hb z ⟨hx.1.trans_lt hz.1,hz.2.trans_le hy.2⟩
    rw [he,abs_div,abs_of_pos (sub_pos.mpr hxy)] at hg
    have hh:=(div_le_iff₀ (sub_pos.mpr hxy)).mp hg
    calc
      dist (f x) (f y)=|f y-f x|:=by rw [Real.dist_eq,abs_sub_comm]
      _≤(K : ℝ)*(y-x):=hh
      _=(K : ℝ)*dist x y:=by
        rw [Real.dist_eq,abs_of_neg (sub_neg.mpr hxy)]
        ring
  intro x hx y hy
  rcases lt_trichotomy x y with hxy|rfl|hyx
  · exact hordered x hx y hy hxy
  · simp
  · simpa only [dist_comm] using hordered y hy x hx hyx

theorem compactMinimumValue_lipschitz {ι : Type*} [TopologicalSpace ι]
    (S : Set ι) (hS : IsCompact S) (hne : S.Nonempty) (F G : ℝ→ι→ℝ)
    (a b : ℝ) (K : NNReal)
    (hcμ : ∀t∈Icc a b,ContinuousOn (F t) S)
    (hct : ∀i∈S,ContinuousOn (fun t=>F t i) (Icc a b))
    (hd : ∀i∈S,∀t∈Ioo a b,HasDerivAt (fun r=>F r i) (G t i) t)
    (hb : ∀i∈S,∀t∈Ioo a b,|G t i|≤(K : ℝ)) :
    LipschitzOnWith K (compactMinimumValue S F) (Icc a b) := by
  apply lipschitzOnWith_minimum_envelope F (compactMinimumValue S F) S (Icc a b) K
  · intro t ht i hi
    obtain ⟨j,hj,_,hle⟩:=compactMinimumValue_attained S hS hne F t (hcμ t ht)
    exact hle i hi
  · intro t ht
    obtain ⟨i,hi,he,_⟩:=compactMinimumValue_attained S hS hne F t (hcμ t ht)
    exact ⟨i,hi,he⟩
  · intro i hi
    exact lipschitzOnWith_of_bounded_interior_derivative (fun t=>F t i) (fun t=>G t i)
      a b K (hct i hi) (hd i hi) (hb i hi)

theorem compactMinimumValue_derivative_contact {ι : Type*} [TopologicalSpace ι]
    (S : Set ι) (hS : IsCompact S) (hne : S.Nonempty) (F : ℝ→ι→ℝ)
    (a b t : ℝ) (ht : t∈Ioo a b)
    (hcμ : ∀r∈Icc a b,ContinuousOn (F r) S)
    (i : ι) (hi : i∈S) (hmin : F t i=compactMinimumValue S F t)
    (hf : DifferentiableAt ℝ (compactMinimumValue S F) t) (d : ℝ)
    (hd : HasDerivAt (fun r=>F r i) d t) :
    deriv (compactMinimumValue S F) t=d := by
  apply hasDerivAt_minimum_envelope_contact (compactMinimumValue S F) (fun r=>F r i)
    (Icc a b) t _ d (Icc_mem_nhds ht.1 ht.2) _ hmin.symm hf.hasDerivAt hd
  intro r hr
  obtain ⟨j,hj,_,hle⟩:=compactMinimumValue_attained S hS hne F r (hcμ r hr)
  exact hle i hi

end FourPapersCommon
