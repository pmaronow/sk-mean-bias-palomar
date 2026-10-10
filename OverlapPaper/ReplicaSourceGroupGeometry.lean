module
public import OverlapPaper.ReplicaSourcePathAlgebra

@[expose] public section

/-! Concrete one-group overlap targets and chronological refinement. Group
sizes and the absence of a crossing breakpoint are proved from the literal
matrix, rather than being supplied as normalized cascade identities. -/
noncomputable section
open Set Real
open scoped BigOperators
namespace OverlapPaper
variable {d : ℕ}

def replicaUniformTarget (d : ℕ) (S : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun l j => if l=j then 1 else S

def replicaUniformGroup (hd : 0 < d) (S q : ℝ) (l : Fin d) : Fin d :=
  if q<S then ⟨0,hd⟩ else l

theorem replicaUniformTarget_mem (S : ℝ) (hS : S ∈ Icc 0 1) (l j : Fin d) :
    replicaUniformTarget d S l j ∈ Icc 0 1 := by
  by_cases h : l=j <;> simp [replicaUniformTarget,h,hS]

theorem replicaUniformTarget_symm (S : ℝ) (l j : Fin d) :
    replicaUniformTarget d S l j = replicaUniformTarget d S j l := by
  simp [replicaUniformTarget,eq_comm]

@[simp] theorem replicaUniformTarget_diag (S : ℝ) (l : Fin d) :
    replicaUniformTarget d S l l=1 := by simp [replicaUniformTarget]

theorem replicaUniformGroup_eq_iff (hd : 0 < d) (S q : ℝ) (hq : q<1) (l j : Fin d) :
    replicaUniformGroup hd S q l=replicaUniformGroup hd S q j ↔ q<replicaUniformTarget d S l j := by
  by_cases hs : q<S
  · by_cases h : l=j <;> simp [replicaUniformGroup,replicaUniformTarget,hs,h,hq]
  · by_cases h : l=j <;> simp [replicaUniformGroup,replicaUniformTarget,hs,h,hq]

theorem replicaUniformTarget_cell (S q₀ q₁ : ℝ) (hq₁ : q₁ ≤ 1)
    (hS : S ≤ q₀ ∨ q₁ ≤ S) (l j : Fin d) :
    replicaUniformTarget d S l j ≤ q₀ ∨ q₁ ≤ replicaUniformTarget d S l j := by
  by_cases h : l=j
  · exact Or.inr (by simpa [replicaUniformTarget,h] using hq₁)
  · simpa [replicaUniformTarget,h] using hS

theorem replicaUniformGroup_fiber_card (hd : 0 < d) (S q : ℝ) (l : Fin d) :
    (Finset.univ.filter (fun j => replicaUniformGroup hd S q l=replicaUniformGroup hd S q j)).card =
      if q<S then d else 1 := by
  classical
  by_cases hs : q<S
  · simp [replicaUniformGroup,hs]
  · simp only [replicaUniformGroup, hs, ite_false]
    have he : (Finset.univ.filter (fun j : Fin d => l=j)) = {l} := by
      ext j
      simp [eq_comm]
    rw [he]
    simp

theorem replicaUniformGroup_penalty_increment (hd : 0 < d)
    (ξ : FourPapersCommon.AdmissibleEvenMixture) (S q₀ q₁ α : ℝ)
    (hq : q₀<q₁) (hq₁ : q₁ ≤ 1) (hS : S ≤ q₀ ∨ q₁ ≤ S) :
    (1/2 : ℝ)*(α/(if q₀<S then (d : ℝ) else 1))*
      (replicaTheta ξ (replicaOverlapPath (replicaUniformTarget d S) q₁)-
        replicaTheta ξ (replicaOverlapPath (replicaUniformTarget d S) q₀)) =
      (d : ℝ)/2*α*(ξ.correction q₁-ξ.correction q₀) := by
  have hpos : 0 < (if q₀<S then d else 1) := by split_ifs <;> omega
  have hg := fun l j => replicaUniformGroup_eq_iff hd S q₀ (hq.trans_le hq₁) l j
  have hc := fun (l j : Fin d) => replicaUniformTarget_cell S q₀ q₁ hq₁ hS l j
  have H := replicaOverlapPath_rescaled_penalty_increment hpos ξ (replicaUniformTarget d S)
    q₀ q₁ α hq (replicaUniformGroup hd S q₀) hg hc
    (fun l => replicaUniformGroup_fiber_card hd S q₀ l)
  simpa only [Nat.cast_ite, Nat.cast_one] using H

end OverlapPaper
