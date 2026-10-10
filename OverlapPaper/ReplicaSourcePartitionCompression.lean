module
public import OverlapPaper.ReplicaSourceChronologicalBaseline
public import OverlapPaper.ReplicaSourceTwoGroupGeometry

@[expose] public section

/-! Redundant Gaussian group labels are compressed using the actual finite
image. Empty fibers are removed and all nonempty fiber sizes are preserved. -/
noncomputable section
open Set Real MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace OverlapPaper
open FourPapersCommon SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000
variable {d : ℕ}

 theorem replica_partition_compression (groupOf : Fin d → Fin d) (c : ℕ)
    (hcard : ∀ l, (Finset.univ.filter (fun m => groupOf l=groupOf m)).card=c) :
    ∃ b : ℕ, ∃ group : Fin d → Fin b, ∃ rep : Fin b → Fin d,
      (∀ i, group (rep i)=i) ∧
      (∀ i, (Finset.univ.filter (fun l => group l=i)).card=c) ∧
      (∀ l m, groupOf l=groupOf m ↔ group l=group m) := by
  classical
  let A := {i : Fin d // ∃ l, groupOf l=i}
  let e : A ≃ Fin (Fintype.card A) := Fintype.equivFin A
  let group : Fin d → Fin (Fintype.card A) := fun l => e ⟨groupOf l,⟨l,rfl⟩⟩
  let rep : Fin (Fintype.card A) → Fin d := fun i => Classical.choose (e.symm i).property
  have hrepval (i : Fin (Fintype.card A)) : groupOf (rep i)=(e.symm i).val :=
    Classical.choose_spec (e.symm i).property
  have hrep (i : Fin (Fintype.card A)) : group (rep i)=i := by
    change e ⟨groupOf (rep i),_⟩=i
    rw [show (⟨groupOf (rep i),_⟩ : A)=e.symm i by apply Subtype.ext; exact hrepval i]
    exact e.apply_symm_apply i
  have hpart (l m : Fin d) : groupOf l=groupOf m ↔ group l=group m := by
    change _ ↔ e ⟨groupOf l,_⟩=e ⟨groupOf m,_⟩
    rw [e.injective.eq_iff,Subtype.ext_iff]
  refine ⟨Fintype.card A,group,rep,hrep,?_,hpart⟩
  intro i
  have hf : (Finset.univ.filter (fun l => group l=i))=
      Finset.univ.filter (fun l => groupOf (rep i)=groupOf l) := by
    ext l
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    rw [hpart,hrep,eq_comm]
  rw [hf,hcard]

 theorem replicaUniformGroup_refinement (hd : 0<d) (S q₀ q₁ : ℝ) (hq : q₁≤q₀)
    (l m : Fin d) (he : replicaUniformGroup hd S q₀ l=replicaUniformGroup hd S q₀ m) :
    replicaUniformGroup hd S q₁ l=replicaUniformGroup hd S q₁ m := by
  by_cases hs0 : q₀<S
  · have hs1 := hq.trans_lt hs0
    simp [replicaUniformGroup,hs1]
  · have hlm : l=m := by simpa only [replicaUniformGroup,hs0,ite_false] using he
    rw [hlm]

 theorem replicaTwoGroup_refinement {r : ℕ} (hr : 0<r) (R S q₀ q₁ : ℝ) (hq : q₁≤q₀)
    (l m : Fin (2*r)) (he : replicaTwoGroup hr R S q₀ l=replicaTwoGroup hr R S q₀ m) :
    replicaTwoGroup hr R S q₁ l=replicaTwoGroup hr R S q₁ m := by
  by_cases hR0 : q₀<R
  · have hR1 := hq.trans_lt hR0
    simp [replicaTwoGroup,hR1]
  · by_cases hR1 : q₁<R
    · simp [replicaTwoGroup,hR1]
    · by_cases hS0 : q₀<S
      · have hS1 := hq.trans_lt hS0
        simpa only [replicaTwoGroup,hR0,hR1,hS0,hS1,ite_false,ite_true] using he
      · have hlm : l=m := by simpa only [replicaTwoGroup,hR0,hS0,ite_false] using he
        rw [hlm]

 theorem replicaSourceUniformSiteCascade_baseline {k : ℕ}
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h S : ℝ) (hd : 0<d) (mark : Finset (Fin d)) :
    finiteStateGaussianCascade
      (fun i => s.m (k+1-i)/(if s.q (k+1-i)<S then (d : ℝ) else 1))
      (fun i => replicaSiteCopyGaussianCLM (ξ.first (s.q (k+2-i))-ξ.first (s.q (k+1-i)))
        (replicaUniformGroup hd S (s.q (k+1-i))))
      (replicaSourceSingleSite h 0 mark) (k+2) 0=
      (d : ℝ)*(Real.log 2+mixedPotential ξ (Paper.parisiSchemeMeasure s) (0,h)) := by
  let c := fun i => if s.q (k+1-i)<S then d else 1
  have hc (j : ℕ) (_ : j<k+2) : 0<c j := by dsimp [c]; split_ifs <;> omega
  have hcomp (j : ℕ) (_ : j<k+2) := replica_partition_compression
    (replicaUniformGroup hd S (s.q (k+1-j))) (c j)
    (fun l => replicaUniformGroup_fiber_card hd S (s.q (k+1-j)) l)
  have hrefine (j : ℕ) (hj : j<k+1) (l m : Fin d) := replicaUniformGroup_refinement hd S
    (s.q (k+1-j)) (s.q (k+1-(j+1)))
    (by simpa only [show k+1-(j+1)+1=k+1-j by omega] using s.q_mono (k+1-(j+1)) (by omega)) l m
  have he := replicaSourceSiteCascade_baseline_zero ξ s h mark _ c hc hcomp hrefine
  simpa only [c,Nat.cast_ite,Nat.cast_one] using he

 theorem replicaSourceTwoGroupSiteCascade_baseline {k r : ℕ}
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h R S : ℝ) (hr : 0<r) (mark : Finset (Fin (2*r))) :
    finiteStateGaussianCascade
      (fun i => s.m (k+1-i)/(if s.q (k+1-i)<R then (2*r : ℝ) else if s.q (k+1-i)<S then r else 1))
      (fun i => replicaSiteCopyGaussianCLM (ξ.first (s.q (k+2-i))-ξ.first (s.q (k+1-i)))
        (replicaTwoGroup hr R S (s.q (k+1-i))))
      (replicaSourceSingleSite h 0 mark) (k+2) 0=
      (2*r : ℝ)*(Real.log 2+mixedPotential ξ (Paper.parisiSchemeMeasure s) (0,h)) := by
  let c := fun i => if s.q (k+1-i)<R then 2*r else if s.q (k+1-i)<S then r else 1
  have hc (j : ℕ) (_ : j<k+2) : 0<c j := by dsimp [c]; split_ifs <;> omega
  have hcomp (j : ℕ) (_ : j<k+2) := replica_partition_compression
    (replicaTwoGroup hr R S (s.q (k+1-j))) (c j)
    (fun l => replicaTwoGroup_fiber_card hr R S (s.q (k+1-j)) l)
  have hrefine (j : ℕ) (hj : j<k+1) (l m : Fin (2*r)) := replicaTwoGroup_refinement hr R S
    (s.q (k+1-j)) (s.q (k+1-(j+1)))
    (by simpa only [show k+1-(j+1)+1=k+1-j by omega] using s.q_mono (k+1-(j+1)) (by omega)) l m
  have he := replicaSourceSiteCascade_baseline_zero ξ s h mark _ c hc hcomp hrefine
  simpa only [c,Nat.cast_ite,Nat.cast_one,Nat.cast_mul,Nat.cast_ofNat] using he

end OverlapPaper
