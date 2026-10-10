module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseDensityAlgebra

@[expose] public section

/-! Exact finite grouping of the observable and mixed-observable terms
in the actual outer covariance Hessian. All weights are arbitrary real
numbers; probabilistic contraction and symmetry enter separately. -/
noncomputable section
open scoped BigOperators Classical
namespace QuantitativeFollowup
set_option autoImplicit false
set_option maxHeartbeats 1200000
variable {I R : Type*} [Fintype I] [Nonempty I] [Fintype R]

def cavityObservableAlgebraFirst (m h : ℝ) (M : I→ℝ) (i : I) : ℝ :=2*m*h*M i
def cavityObservableAlgebraSecond (m h : ℝ) (M E : I→ℝ) (i : I) : ℝ :=
  2*(M i*h)^2+2*m*E i
def cavityObservableAlgebraRestFirst (m : ℝ) (M : I→ℝ) (H : I→I→ℝ) (i : I) : ℝ :=
  2/(Fintype.card I:ℝ)*m*(∑l,M l*H l i)
def cavityObservableAlgebraRestSecond (m : ℝ) (M : I→ℝ) (H D : I→I→ℝ) (i : I) : ℝ :=
  2/(Fintype.card I:ℝ)*(m^2*(∑l,H l i^2)+∑l,M l*D i l)

private theorem observable_sum_weighted_swap {J K : Type*} [Fintype J] [Fintype K]
    (w : K→ℝ) (f : J→K→ℝ) :
    (∑j,∑k,w k*f j k)=∑k,w k*(∑j,f j k) := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _=>(Finset.mul_sum _ _ _).symm

theorem cavityObservableAlgebra_last_group
    (m h barA eps : ℝ) (M E tau : I→ℝ) (w mr : R→ℝ) (Mr : R→I→ℝ) :
    1/(2*(Fintype.card I:ℝ))*(∑i,(
      cavityObservableAlgebraSecond m h M E i*barA+
      2*cavityDensityAlgebraScore w mr Mr tau eps i*cavityObservableAlgebraFirst m h M i*barA))=
    barA*(h^2*(∑i,M i^2)/(Fintype.card I:ℝ)+
      m*(∑i,E i)/(Fintype.card I:ℝ)+
      2*m*h*eps*(∑i,tau i*M i)/(Fintype.card I:ℝ)-
      2*m*h*(∑r,w r*mr r*(∑i,M i*Mr r i))/(Fintype.card I:ℝ)) := by
  have hn : (Fintype.card I:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hcross (i : I) : (∑r,w r*Mr r i*mr r)*M i=
      ∑r,w r*mr r*(M i*Mr r i) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun r _=>by ring
  have hp (i : I) :
      cavityObservableAlgebraSecond m h M E i*barA+
        2*cavityDensityAlgebraScore w mr Mr tau eps i*cavityObservableAlgebraFirst m h M i*barA=
      2*barA*(h^2*M i^2+m*E i+2*m*h*eps*(tau i*M i)-
        2*m*h*(∑r,w r*mr r*(M i*Mr r i))) := by
    rw [←hcross i]
    dsimp only [cavityObservableAlgebraSecond,cavityObservableAlgebraFirst,cavityDensityAlgebraScore]
    ring
  have hsum := Finset.sum_congr (s₁:=Finset.univ) (s₂:=Finset.univ) rfl (fun i _=>hp i)
  rw [hsum]
  rw [←Finset.mul_sum]
  simp_rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum]
  rw [observable_sum_weighted_swap (fun r=>w r*mr r) (fun i r=>M i*Mr r i)]
  generalize (∑i,M i^2)=A
  generalize (∑i,E i)=B
  generalize (∑i,tau i*M i)=C
  generalize (∑r,w r*mr r*(∑i,M i*Mr r i))=D
  field_simp [hn]
  <;>ring

theorem cavityObservableAlgebra_rest_group
    (m h barf eps : ℝ) (M tau : I→ℝ) (H D : I→I→ℝ)
    (w mr : R→ℝ) (Mr : R→I→ℝ) :
    1/(2*(Fintype.card I:ℝ))*(∑i,(
      barf*cavityObservableAlgebraRestSecond m M H D i+
      2*cavityObservableAlgebraFirst m h M i*cavityObservableAlgebraRestFirst m M H i+
      2*cavityDensityAlgebraScore w mr Mr tau eps i*barf*cavityObservableAlgebraRestFirst m M H i))=
    barf*m^2*(∑i,∑l,H l i^2)/(Fintype.card I:ℝ)^2+
      barf*(∑l,M l*(∑i,D i l))/(Fintype.card I:ℝ)^2+
      4*m^2*h*(∑i,M i*(∑l,M l*H l i))/(Fintype.card I:ℝ)^2+
      2*barf*m*eps*(∑i,tau i*(∑l,M l*H l i))/(Fintype.card I:ℝ)^2-
      2*barf*m*(∑r,w r*mr r*(∑i,Mr r i*(∑l,M l*H l i)))/(Fintype.card I:ℝ)^2 := by
  have hn : (Fintype.card I:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  let S := fun i=>∑l,M l*H l i
  have hcross (i : I) : (∑r,w r*Mr r i*mr r)*S i=
      ∑r,w r*mr r*(Mr r i*S i) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun r _=>by ring
  have hp (i : I) :
      barf*cavityObservableAlgebraRestSecond m M H D i+
        2*cavityObservableAlgebraFirst m h M i*cavityObservableAlgebraRestFirst m M H i+
        2*cavityDensityAlgebraScore w mr Mr tau eps i*barf*cavityObservableAlgebraRestFirst m M H i=
      (2/(Fintype.card I:ℝ))*(barf*m^2*(∑l,H l i^2)+barf*(∑l,M l*D i l)+
        4*m^2*h*(M i*S i)+2*barf*m*eps*(tau i*S i)-
        2*barf*m*(∑r,w r*mr r*(Mr r i*S i))) := by
    rw [←hcross i]
    dsimp only [cavityObservableAlgebraRestSecond,cavityObservableAlgebraRestFirst,
      cavityObservableAlgebraFirst,cavityDensityAlgebraScore,S]
    ring
  have hsum := Finset.sum_congr (s₁:=Finset.univ) (s₂:=Finset.univ) rfl (fun i _=>hp i)
  rw [hsum]
  rw [←Finset.mul_sum]
  simp_rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum]
  rw [observable_sum_weighted_swap M D,
    observable_sum_weighted_swap (fun r=>w r*mr r) (fun i r=>Mr r i*S i)]
  dsimp only [S]
  generalize (∑i,∑l,H l i^2)=A
  generalize (∑l,M l*(∑i,D i l))=B
  generalize (∑i,M i*(∑l,M l*H l i))=C
  generalize (∑i,tau i*(∑l,M l*H l i))=E
  generalize (∑r,w r*mr r*(∑i,Mr r i*(∑l,M l*H l i)))=F
  field_simp [hn]
  <;>ring

end QuantitativeFollowup
