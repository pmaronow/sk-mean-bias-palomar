module
public import OverlapPaper.ReplicaSourceGroupGeometry

@[expose] public section

/-! Literal two-family overlap matrix, its chronological group refinement,
and exact group sizes. -/
noncomputable section
open Set Real
open scoped BigOperators
namespace OverlapPaper
set_option maxHeartbeats 900000

def replicaHalfGroup {k : ℕ} (hk : 0 < k) (l : Fin (2*k)) : Fin (2*k) :=
  if l.val<k then ⟨0,by omega⟩ else ⟨1,by omega⟩

theorem replicaHalfGroup_eq_iff {k : ℕ} (hk : 0 < k) (l j : Fin (2*k)) :
    replicaHalfGroup hk l=replicaHalfGroup hk j ↔ (l.val<k ↔ j.val<k) := by
  by_cases hl : l.val<k <;> by_cases hj : j.val<k <;>
    simp [replicaHalfGroup,hl,hj,Fin.ext_iff]

private theorem half_filter_card (k : ℕ) :
    (Finset.univ.filter (fun j : Fin (2*k) => j.val<k)).card=k := by
  let e : {j : Fin (2*k) // j.val<k} ≃ Fin k :=
    { toFun := fun j => ⟨j.1.val,j.2⟩
      invFun := fun j => ⟨⟨j.val,by have := j.isLt; omega⟩,j.isLt⟩
      left_inv := fun j => by apply Subtype.ext; apply Fin.ext; rfl
      right_inv := fun j => by apply Fin.ext; rfl }
  have h := Fintype.card_congr e
  rw [Fintype.card_subtype] at h
  simpa using h

private theorem half_filter_not_card (k : ℕ) :
    (Finset.univ.filter (fun j : Fin (2*k) => ¬j.val<k)).card=k := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (2*k))))
    (fun j => j.val<k)
  rw [half_filter_card] at h
  simp only [Finset.card_univ,Fintype.card_fin] at h
  omega

theorem replicaHalfGroup_fiber_card {k : ℕ} (hk : 0 < k) (l : Fin (2*k)) :
    (Finset.univ.filter (fun j => replicaHalfGroup hk l=replicaHalfGroup hk j)).card=k := by
  simp_rw [replicaHalfGroup_eq_iff]
  by_cases hl : l.val<k
  · simpa only [hl,true_iff] using half_filter_card k
  · simpa only [hl,false_iff] using half_filter_not_card k

def replicaTwoGroupTarget (k : ℕ) (r S : ℝ) : Matrix (Fin (2*k)) (Fin (2*k)) ℝ :=
  fun l j => if l=j then 1 else if (l.val<k ↔ j.val<k) then S else r

def replicaTwoGroup {k : ℕ} (hk : 0 < k) (r S q : ℝ) (l : Fin (2*k)) : Fin (2*k) :=
  if q<r then ⟨0,by omega⟩ else if q<S then replicaHalfGroup hk l else l

theorem replicaTwoGroupTarget_mem (k : ℕ) (r S : ℝ) (hr : r ∈ Icc 0 1) (hS : S ∈ Icc 0 1)
    (l j : Fin (2*k)) : replicaTwoGroupTarget k r S l j ∈ Icc 0 1 := by
  unfold replicaTwoGroupTarget
  split_ifs
  · norm_num
  · exact hS
  · exact hr

theorem replicaTwoGroupTarget_symm (k : ℕ) (r S : ℝ) (l j : Fin (2*k)) :
    replicaTwoGroupTarget k r S l j=replicaTwoGroupTarget k r S j l := by
  simp [replicaTwoGroupTarget,eq_comm,Iff.comm]

@[simp] theorem replicaTwoGroupTarget_diag (k : ℕ) (r S : ℝ) (l : Fin (2*k)) :
    replicaTwoGroupTarget k r S l l=1 := by simp [replicaTwoGroupTarget]

theorem replicaTwoGroup_eq_iff {k : ℕ} (hk : 0 < k) (r S q : ℝ)
    (hrS : r ≤ S) (hq : q<1) (l j : Fin (2*k)) :
    replicaTwoGroup hk r S q l=replicaTwoGroup hk r S q j ↔
      q<replicaTwoGroupTarget k r S l j := by
  by_cases hr : q<r
  · have hs : q<S := hr.trans_le hrS
    by_cases he : l=j <;> by_cases hb : l.val<k ↔ j.val<k <;>
      simp [replicaTwoGroup,replicaTwoGroupTarget,hr,hs,he,hb,hq]
  · by_cases hs : q<S
    · simp only [replicaTwoGroup,hr,ite_false,hs,ite_true,replicaHalfGroup_eq_iff]
      by_cases he : l=j <;> by_cases hb : l.val<k ↔ j.val<k <;>
        simp [replicaTwoGroupTarget,he,hb,hq,hr,hs] at *
    · by_cases he : l=j <;> by_cases hb : l.val<k ↔ j.val<k <;>
        simp [replicaTwoGroup,replicaTwoGroupTarget,hr,hs,he,hb,hq]

theorem replicaTwoGroupTarget_cell {k : ℕ} (r S q₀ q₁ : ℝ) (hq₁ : q₁ ≤ 1)
    (hr : r ≤ q₀ ∨ q₁ ≤ r) (hS : S ≤ q₀ ∨ q₁ ≤ S) (l j : Fin (2*k)) :
    replicaTwoGroupTarget k r S l j ≤ q₀ ∨ q₁ ≤ replicaTwoGroupTarget k r S l j := by
  unfold replicaTwoGroupTarget
  split_ifs
  · exact Or.inr hq₁
  · exact hS
  · exact hr

theorem replicaTwoGroup_fiber_card {k : ℕ} (hk : 0 < k) (r S q : ℝ) (l : Fin (2*k)) :
    (Finset.univ.filter (fun j => replicaTwoGroup hk r S q l=replicaTwoGroup hk r S q j)).card =
      if q<r then 2*k else if q<S then k else 1 := by
  classical
  by_cases hr : q<r
  · simp [replicaTwoGroup,hr]
  · by_cases hs : q<S
    · simpa only [replicaTwoGroup,hr,ite_false,hs,ite_true] using replicaHalfGroup_fiber_card hk l
    · simp only [replicaTwoGroup,hr,hs,ite_false]
      have he : (Finset.univ.filter (fun j : Fin (2*k) => l=j)) = {l} := by
        ext j
        simp [eq_comm]
      rw [he]
      simp

theorem replicaTwoGroup_penalty_increment {k : ℕ} (hk : 0 < k)
    (ξ : FourPapersCommon.AdmissibleEvenMixture) (r S q₀ q₁ α : ℝ)
    (hrS : r ≤ S) (hq : q₀<q₁) (hq₁ : q₁ ≤ 1)
    (hr : r ≤ q₀ ∨ q₁ ≤ r) (hS : S ≤ q₀ ∨ q₁ ≤ S) :
    (1/2 : ℝ)*(α/(if q₀<r then (2*k : ℝ) else if q₀<S then k else 1))*
      (replicaTheta ξ (replicaOverlapPath (replicaTwoGroupTarget k r S) q₁)-
        replicaTheta ξ (replicaOverlapPath (replicaTwoGroupTarget k r S) q₀)) =
      (2*k : ℝ)/2*α*(ξ.correction q₁-ξ.correction q₀) := by
  have hpos : 0 < (if q₀<r then 2*k else if q₀<S then k else 1) := by split_ifs <;> omega
  have hg := fun l j => replicaTwoGroup_eq_iff hk r S q₀ hrS (hq.trans_le hq₁) l j
  have hc := fun (l j : Fin (2*k)) => replicaTwoGroupTarget_cell r S q₀ q₁ hq₁ hr hS l j
  have H := replicaOverlapPath_rescaled_penalty_increment hpos ξ (replicaTwoGroupTarget k r S)
    q₀ q₁ α hq (replicaTwoGroup hk r S q₀) hg hc
    (fun l => replicaTwoGroup_fiber_card hk r S q₀ l)
  simpa only [Nat.cast_ite,Nat.cast_one,Nat.cast_mul,Nat.cast_ofNat] using H

end OverlapPaper
