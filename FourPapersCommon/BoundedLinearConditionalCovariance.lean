module
public import FourPapersCommon.BoundedAffineConditionalVariance

@[expose] public section

/-! The conditional variance of a genuine bounded past-dependent linear
combination is the corresponding quadratic conditional covariance. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace FourPapersCommon
variable {Ω ι : Type*} [m₀ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] [Fintype ι] [DecidableEq ι]
set_option maxHeartbeats 1500000

theorem finite_linear_square (b X : ι→ℝ) :
    (∑i,b i*X i)^2=∑i,∑j,(b i*b j)*(X i*X j) := by
  rw [pow_two,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem condExp_bounded_random_linear_square (m : MeasurableSpace Ω) (hm : m≤m₀)
    (b X : ι→Ω→ℝ) (hb : ∀i,StronglyMeasurable[m] (b i))
    (hX : ∀i,Measurable[m₀] (X i)) (K : ℝ) (hK : 0≤K)
    (hB : ∀i ω, ‖b i ω‖≤K) (hXB : ∀i ω, ‖X i ω‖≤1) :
    P[(fun ω=>(∑i,b i ω*X i ω)^2)|m]=ᵐ[P]
      (fun ω=>∑i,∑j,(b i ω*b j ω)*P[(fun ω=>X i ω*X j ω)|m] ω) := by
  let B : ι×ι→Ω→ℝ := fun ij ω=>b ij.1 ω*b ij.2 ω
  let Y : ι×ι→Ω→ℝ := fun ij ω=>X ij.1 ω*X ij.2 ω
  have hBknown (ij : ι×ι) : StronglyMeasurable[m] (B ij) := (hb ij.1).mul (hb ij.2)
  have hYm (ij : ι×ι) : Measurable[m₀] (Y ij) := (hX ij.1).mul (hX ij.2)
  have hBB (ij : ι×ι) (ω : Ω) : ‖B ij ω‖≤K^2 := by
    change ‖b ij.1 ω*b ij.2 ω‖≤K^2
    rw [norm_mul,pow_two]
    exact mul_le_mul (hB ij.1 ω) (hB ij.2 ω) (norm_nonneg _) hK
  have hYB (ij : ι×ι) (ω : Ω) : ‖Y ij ω‖≤1 := by
    change ‖X ij.1 ω*X ij.2 ω‖≤1
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul (hXB ij.1 ω) (hXB ij.2 ω) (norm_nonneg _) zero_le_one
  have he : (fun ω=>(∑i,b i ω*X i ω)^2)=(fun ω=>∑ij : ι×ι,B ij ω*Y ij ω) := by
    funext ω
    rw [Fintype.sum_prod_type]
    exact finite_linear_square _ _
  rw [he]
  have hs:=condExp_bounded_random_linear (m₀:=m₀) (P:=P) m hm B Y hBknown hYm (K^2)
    (sq_nonneg K) hBB hYB
  simpa only [Fintype.sum_prod_type,B,Y] using hs

theorem condVar_bounded_random_linear (m : MeasurableSpace Ω) (hm : m≤m₀)
    (b X : ι→Ω→ℝ) (hb : ∀i,StronglyMeasurable[m] (b i))
    (hX : ∀i,Measurable[m₀] (X i)) (K : ℝ) (hK : 0≤K)
    (hB : ∀i ω, ‖b i ω‖≤K) (hXB : ∀i ω, ‖X i ω‖≤1) :
    condVar m (fun ω=>∑i,b i ω*X i ω) P=ᵐ[P]
      (fun ω=>∑i,∑j,(b i ω*b j ω)*
        (P[(fun ω=>X i ω*X j ω)|m] ω-P[X i|m] ω*P[X j|m] ω)) := by
  have hbm (i : ι) : Measurable[m₀] (b i) := (hb i).mono hm |>.measurable
  have hg : Measurable[m₀] (fun ω=>∑i,b i ω*X i ω) :=
    Finset.measurable_sum _ (fun i _=>(hbm i).mul (hX i))
  have hgb (ω : Ω) : ‖∑i,b i ω*X i ω‖≤(Fintype.card ι:ℝ)*K := by
    calc
      _≤∑i : ι,‖b i ω*X i ω‖ := norm_sum_le _ _
      _≤∑_i : ι,K := Finset.sum_le_sum fun i _=>by
        rw [norm_mul]
        simpa only [mul_one] using mul_le_mul (hB i ω) (hXB i ω) (norm_nonneg _) hK
      _=(Fintype.card ι:ℝ)*K := by simp
  have hgL : MemLp (fun ω=>∑i,b i ω*X i ω) 2 P :=
    MemLp.of_bound hg.aestronglyMeasurable _ (.of_forall hgb)
  have hv:=condVar_ae_eq_condExp_sq_sub_sq_condExp hm hgL
  have h1:=condExp_bounded_random_linear (m₀:=m₀) (P:=P) m hm b X hb hX K hK hB hXB
  have h2:=condExp_bounded_random_linear_square (m₀:=m₀) (P:=P) m hm b X hb hX K hK hB hXB
  filter_upwards [hv,h1,h2] with ω hω h1ω h2ω
  change condVar m (fun ω=>∑i,b i ω*X i ω) P ω=
    P[(fun ω=>(∑i,b i ω*X i ω)^2)|m] ω-
    (P[(fun ω=>∑i,b i ω*X i ω)|m] ω)^2 at hω
  rw [h1ω,h2ω] at hω
  rw [hω,finite_linear_square]
  simp_rw [mul_sub,Finset.sum_sub_distrib]

end FourPapersCommon
