module
public import QuantitativeFollowup.FollowupCavityInterpolationCoordinates

@[expose] public section

/-! Exact contraction of the triangular disorder index to the n physical
incident sites. The extra selected diagonal coordinate has zero coupling
and contributes exactly zero. -/
noncomputable section
open Set
open scoped BigOperators
namespace QuantitativeFollowup
open QuantitativePaper FourPapersCommon
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

def cavityIncidentEdge {n : ℕ} (i : Fin n) : AnisotropicCouplingIndex (n+1):=
  ⟨(i.castSucc,Fin.last n),Fin.le_last _⟩

theorem sum_cavityIncidentEdges {n : ℕ} (f : AnisotropicCouplingIndex (n+1)→ℝ) :
    (∑e∈Finset.univ.filter (fun e : AnisotropicCouplingIndex (n+1)=>
      e.1.1≠Fin.last n ∧ e.1.2=Fin.last n),f e)=∑i : Fin n,f (cavityIncidentEdge i) := by
  classical
  symm
  apply Finset.sum_bij (fun i _=>cavityIncidentEdge i)
  · intro i _
    simp [cavityIncidentEdge,Fin.castSucc_ne_last]
  · intro i _ j _ hij
    have hv:=congrArg (fun e : AnisotropicCouplingIndex (n+1)=>e.1.1.val) hij
    exact Fin.ext hv
  · intro e he
    obtain ⟨hfirst,hlast⟩:= (Finset.mem_filter.mp he).2
    have hne : e.1.1.val≠n:=by
      intro h
      apply hfirst
      exact Fin.ext h
    have hlt : e.1.1.val<n:=by have :=e.1.1.isLt;omega
    let i : Fin n:=⟨e.1.1.val,hlt⟩
    refine ⟨i,Finset.mem_univ _,?_⟩
    apply Subtype.ext
    apply Prod.ext
    · exact Fin.ext rfl
    · exact hlast.symm
  · intro i _
    rfl

theorem followupCavity_incident_hessian_sum (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc 0 1) (f : AnisotropicCouplingIndex (n+1)→ℝ) :
    (∑e,if cavityIncidentRootMask n e then
      ((followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩).coupling e)^2*f e else 0)=
      (followupCavityAlpha n β ρ/(n:ℝ))*∑i : Fin n,f (cavityIncidentEdge i) := by
  classical
  have heq (e : AnisotropicCouplingIndex (n+1)) :
      (if cavityIncidentRootMask n e then
        ((followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩).coupling e)^2*f e else 0)=
      if e.1.1≠Fin.last n ∧ e.1.2=Fin.last n then
        (followupCavityAlpha n β ρ/(n:ℝ))*f e else 0 := by
    by_cases hl:e.1.2=Fin.last n
    · by_cases hi:e.1.1=Fin.last n
      · simp [cavityIncidentRootMask,followupCavitySpinModel,hl,hi]
      · have hd:e.1.1≠e.1.2:=by simpa only [hl] using hi
        simp only [cavityIncidentRootMask,hl,decide_true,ite_true,followupCavitySpinModel,hd,ite_false,
          hi,not_false_eq_true,true_and,and_true]
        rw [followupCavityRowCoupling_square n β ρ 1 hρ.2 zero_le_one,mul_one,ite_eq_left hi]
    · simp [cavityIncidentRootMask,hl]
  simp_rw [heq]
  rw [←Finset.sum_filter,sum_cavityIncidentEdges,Finset.mul_sum]

end QuantitativeFollowup
