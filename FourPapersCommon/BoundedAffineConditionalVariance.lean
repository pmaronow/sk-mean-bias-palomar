module
public import Mathlib.Probability.CondVar
public import FourPapersCommon.WeightedConditionalIntegral

@[expose] public section

/-! Finite random linear combinations of bounded terminal observables,
with coefficients known in the whole conditioning sigma algebra. These
are genuine conditional expectations and variances under a probability law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace FourPapersCommon
variable {Ω ι : Type*} [m₀ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] [Fintype ι] [DecidableEq ι]
set_option maxHeartbeats 1200000

theorem bounded_real_integrable (f : Ω→ℝ) (hf : Measurable f)
    (C : ℝ) (hC : ∀ω, ‖f ω‖≤C) : Integrable f P :=
  (integrable_const C).mono' hf.aestronglyMeasurable (.of_forall hC)

theorem condExp_bounded_random_linear (m : MeasurableSpace Ω) (hm : m≤m₀)
    (b X : ι→Ω→ℝ) (hb : ∀i,StronglyMeasurable[m] (b i))
    (hX : ∀i,Measurable[m₀] (X i)) (K : ℝ) (hK : 0≤K)
    (hB : ∀i ω, ‖b i ω‖≤K) (hXB : ∀i ω, ‖X i ω‖≤1) :
    P[(fun ω=>∑i,b i ω*X i ω)|m]=ᵐ[P]
      (fun ω=>∑i,b i ω*P[X i|m] ω) := by
  have hbi (i : ι) : Measurable[m₀] (b i) := (hb i).mono hm |>.measurable
  have hxi (i : ι) : Integrable (X i) P := bounded_real_integrable (m₀:=m₀) (P:=P) _ (hX i) 1 (hXB i)
  have hprod (i : ι) : Integrable (fun ω=>b i ω*X i ω) P := by
    apply bounded_real_integrable (m₀:=m₀) (P:=P) _ ((hbi i).mul (hX i)) K
    intro ω
    change ‖b i ω*X i ω‖≤K
    rw [norm_mul]
    simpa only [mul_one] using mul_le_mul (hB i ω) (hXB i ω) (norm_nonneg _) hK
  have hs:=condExp_finsetSum (μ:=P) (s:=Finset.univ) (fun i _=>hprod i) m
  have hp (i : ι) := condExp_mul_of_stronglyMeasurable_left (hb i) (hprod i) (hxi i) (m:=m)
  have he : (∑i : ι,fun ω=>b i ω*X i ω)=(fun ω=>∑i,b i ω*X i ω) := by
    funext ω
    simp only [Finset.sum_apply]
  rw [he] at hs
  filter_upwards [hs,ae_all_iff.2 hp] with ω hω hall
  simp only [Finset.sum_apply,Pi.mul_apply] at hω hall
  exact hω.trans (Finset.sum_congr rfl fun i _=>hall i)

theorem integral_condVar_le_variance (m : MeasurableSpace Ω) (hm : m≤m₀)
    (X : Ω→ℝ) (hX : MemLp X 2 P) :
    (∫ω,condVar m X P ω ∂P)≤variance X P := by
  have h:=integral_condVar_add_variance_condExp hm hX
  have hn:=variance_nonneg (P[X|m]) P
  linarith

theorem condVar_sub_known (m : MeasurableSpace Ω) (hm : m≤m₀)
    (X d : Ω→ℝ) (hX : Integrable X P) (hd : Integrable d P)
    (hknown : StronglyMeasurable[m] d) :
    condVar m (X-d) P=ᵐ[P] condVar m X P := by
  have he:=condExp_sub (m:=m) hX hd
  have hdce:=condExp_of_stronglyMeasurable hm hknown hd
  apply condExp_congr_ae
  filter_upwards [he] with ω hω
  simp only [Pi.sub_apply,hdce] at hω
  change (X ω-d ω-P[X-d|m] ω)^2=(X ω-P[X|m] ω)^2
  rw [hω]
  congr 1
  ring

end FourPapersCommon
