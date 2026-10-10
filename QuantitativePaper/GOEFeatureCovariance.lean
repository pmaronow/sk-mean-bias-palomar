module
public import QuantitativePaper.GOECompletionMatrix

@[expose] public section

/-! The paper's literal independent GOE coordinate features and their exact
spin-overlap covariance, including all N independent diagonal coordinates. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1000000

def goeFeature (n : ℕ) (β : ℝ) (σ : Configuration n) : Edge n⊕Fin n→ℝ
  | .inl e => β/Real.sqrt (n : ℝ)*Paper.spinSign (σ e.val.1)*Paper.spinSign (σ e.val.2)
  | .inr _ => β/Real.sqrt (2*(n : ℝ))

theorem goeFeature_diagonal_square_sum (n : ℕ) (hn : 0 < n) (β : ℝ)
    (σ τ : Configuration n) :
    (∑i : Fin n,goeFeature n β σ (.inr i)*goeFeature n β τ (.inr i))=β^2/2 := by
  have hN : (n : ℝ)≠0 := by exact_mod_cast hn.ne'
  simp only [goeFeature,←pow_two,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    div_pow,Real.sq_sqrt (show 0 ≤ 2*(n : ℝ) by positivity)]
  field_simp
  <;> ring

theorem goeFeature_covariance (n : ℕ) (hn : 0 < n) (β : ℝ)
    (σ τ : Configuration n) :
    (∑e : Edge n⊕Fin n,goeFeature n β σ e*goeFeature n β τ e)=
      β^2*(n : ℝ)/2*((∑i,Paper.spinSign (σ i)*Paper.spinSign (τ i))/(n : ℝ))^2 := by
  classical
  have hN : n≠0 := hn.ne'
  have he : (∑e : Edge n,goeFeature n β σ (.inl e)*goeFeature n β τ (.inl e))=
      ∑e : Edge n,Paper.physicalSKCoefficient n β σ (some e)*
        Paper.physicalSKCoefficient n β τ (some e) := by
    apply Finset.sum_congr rfl
    intro e _
    simp only [goeFeature,Paper.physicalSKCoefficient]
    ring
  rw [Fintype.sum_sum_type,goeFeature_diagonal_square_sum n hn β σ τ,he]
  have hc := Paper.physicalSKCoefficient_covariance n β σ τ
  rw [Fintype.sum_option] at hc
  simp only [Paper.physicalSKCoefficient,Paper.skCommonNoiseCoefficient,hN,ite_false,
    ←pow_two,div_pow,Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)] at hc
  simp only [Paper.physicalSKCoefficient]
  rw [add_comm]
  convert hc using 1 <;> ring

end QuantitativePaper
