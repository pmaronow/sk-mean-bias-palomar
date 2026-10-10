module
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Fintype.Card
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Literal second-density algebra in the independent-endpoint response.
Only finite sums and the genuine binary-spin squares are used here.
The probabilistic score and its derivatives are supplied by separate model
theorems, not assumed to equal the desired response. -/
noncomputable section
open Finset
namespace QuantitativeFollowup
set_option maxHeartbeats 1200000

def cavityDensityAlgebraScore {I R : Type*} [Fintype R]
    (w m : R → ℝ) (M : R → I → ℝ) (tau : I → ℝ) (eps : ℝ) (i : I) : ℝ :=
  tau i*eps-∑r,w r*M r i*m r

def cavityDensityAlgebraSecond {I R : Type*}
    (c m : R → ℝ) (M future : R → I → ℝ) (r : R) (i : I) : ℝ :=
  1-c r*(M r i*m r)^2-future r i

private theorem cavityDensityAlgebra_pointwise {I R : Type*} [Fintype R]
    (w c m : R → ℝ) (M future : R → I → ℝ) (tau : I → ℝ) (eps : ℝ)
    (heps : eps^2=1) (i : I) (htau : (tau i)^2=1) :
    cavityDensityAlgebraScore w m M tau eps i ^2-
      ∑r,w r*cavityDensityAlgebraSecond c m M future r i =
      1-∑r,w r - 2*(∑r,w r*eps*m r*(tau i*M r i)) +
      (∑r,∑l,w r*w l*m r*m l*(M r i*M l i)) +
      (∑r,w r*c r*(m r)^2*(M r i)^2) + (∑r,w r*future r i) := by
  have hspin : (tau i*eps)^2=1 := by rw [mul_pow,htau,heps,mul_one]
  have hcross : (tau i*eps)*(∑r,w r*M r i*m r) =
      ∑r,w r*eps*m r*(tau i*M r i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  have hpair : (∑r,w r*M r i*m r)^2 =
      ∑r,∑l,w r*w l*m r*m l*(M r i*M l i) := by
    rw [pow_two,Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hsecond : (∑r,w r*cavityDensityAlgebraSecond c m M future r i) =
      (∑r,w r)-(∑r,w r*c r*(m r)^2*(M r i)^2)-(∑r,w r*future r i) := by
    rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r _
    dsimp only [cavityDensityAlgebraSecond]
    ring
  unfold cavityDensityAlgebraScore
  rw [sub_sq,hspin,hpair,hsecond]
  have H : 2*(tau i*eps)*(∑r,w r*M r i*m r) =
      2*(∑r,w r*eps*m r*(tau i*M r i)) := by rw [mul_assoc,hcross]
  rw [H]
  ring

theorem cavityDensityAlgebra_second_density_group
    {I R : Type*} [Fintype I] [Nonempty I] [Fintype R]
    (w c m : R → ℝ) (M future : R → I → ℝ) (tau : I → ℝ) (eps Fbar Abar : ℝ)
    (heps : eps^2=1) (htau : ∀i,(tau i)^2=1) :
    ((Fintype.card I : ℝ)⁻¹/2)*
      (∑i,Fbar*Abar*(cavityDensityAlgebraScore w m M tau eps i ^2-
        ∑r,w r*cavityDensityAlgebraSecond c m M future r i)) =
      Fbar*Abar/2*(1-∑r,w r) -
      Fbar*Abar*(∑r,w r*eps*m r*((Fintype.card I : ℝ)⁻¹*(∑i,tau i*M r i))) +
      Fbar*Abar/2*(∑r,∑l,w r*w l*m r*m l*
        ((Fintype.card I : ℝ)⁻¹*(∑i,M r i*M l i))) +
      Fbar*Abar/2*(∑r,w r*c r*(m r)^2*
        ((Fintype.card I : ℝ)⁻¹*(∑i,(M r i)^2))) +
      Fbar*Abar/2*(∑r,w r*((Fintype.card I : ℝ)⁻¹*(∑i,future r i))) := by
  have hn : (Fintype.card I : ℝ)≠0 :=
    (Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr inferInstance)).ne'
  have H (i : I) := cavityDensityAlgebra_pointwise w c m M future tau eps heps i (htau i)
  simp_rw [H]
  rw [← Finset.mul_sum]
  simp_rw [Finset.sum_add_distrib,Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have cross : (∑i,(2:ℝ)*(∑r,w r*eps*m r*(tau i*M r i))) =
      2*(∑r,w r*eps*m r*(∑i,tau i*M r i)) := by
    rw [← Finset.mul_sum,Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
  have pair : (∑i,∑r,∑l,w r*w l*m r*m l*(M r i*M l i)) =
      ∑r,∑l,w r*w l*m r*m l*(∑i,M r i*M l i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
  have diagonal : (∑i,∑r,w r*c r*(m r)^2*(M r i)^2) =
      ∑r,w r*c r*(m r)^2*(∑i,(M r i)^2) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
  have futureSum : (∑i,∑r,w r*future r i) = ∑r,w r*(∑i,future r i) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
  rw [cross,pair,diagonal,futureSum]
  have scaleCross : (∑r,w r*eps*m r*((Fintype.card I : ℝ)⁻¹*(∑i,tau i*M r i))) =
      (Fintype.card I : ℝ)⁻¹*(∑r,w r*eps*m r*(∑i,tau i*M r i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  have scalePair : (∑r,∑l,w r*w l*m r*m l*
      ((Fintype.card I : ℝ)⁻¹*(∑i,M r i*M l i))) =
      (Fintype.card I : ℝ)⁻¹*(∑r,∑l,w r*w l*m r*m l*(∑i,M r i*M l i)) := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro l _
    ring
  have scaleDiagonal : (∑r,w r*c r*(m r)^2*
      ((Fintype.card I : ℝ)⁻¹*(∑i,(M r i)^2))) =
      (Fintype.card I : ℝ)⁻¹*(∑r,w r*c r*(m r)^2*(∑i,(M r i)^2)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  have scaleFuture : (∑r,w r*((Fintype.card I : ℝ)⁻¹*(∑i,future r i))) =
      (Fintype.card I : ℝ)⁻¹*(∑r,w r*(∑i,future r i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [scaleCross,scalePair,scaleDiagonal,scaleFuture]
  generalize (∑r,w r)=W
  generalize (∑r,w r*eps*m r*(∑i,tau i*M r i))=C
  generalize (∑r,∑l,w r*w l*m r*m l*(∑i,M r i*M l i))=P
  generalize (∑r,w r*c r*(m r)^2*(∑i,(M r i)^2))=D
  generalize (∑r,w r*(∑i,future r i))=T
  field_simp [hn]
  <;> ring

end QuantitativeFollowup
