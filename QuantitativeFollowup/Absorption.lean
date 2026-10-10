module
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Tactic

@[expose] public section

/-! The exact finite-term absorption estimate in Lemma 8.3. This is an
unconditional real inequality proved by weighted arithmetic-geometric
means; it will be applied to the actual finite-SK interpolation error. -/
noncomputable section
open scoped BigOperators
namespace QuantitativeFollowup

theorem scaled_young_rpow {A e h δ : ℝ} (hA : 0 ≤ A) (he : 0 ≤ e)
    (hh : 0 < h) (hh1 : h < 1) (hδ : 0 < δ) :
    A * e ^ h ≤ h * δ * e +
      (1-h) * A ^ (1/(1-h)) * δ ^ (-h/(1-h)) := by
  have hc : 0 < 1-h := sub_pos.mpr hh1
  have ha : 0 ≤ A * δ ^ (-h) := mul_nonneg hA (Real.rpow_nonneg hδ.le _)
  have hy := Real.geom_mean_le_arith_mean2_weighted hh.le hc.le
    (mul_nonneg hδ.le he)
    (Real.rpow_nonneg ha (1/(1-h))) (by ring : h+(1-h)=1)
  have hpow : ((A*δ^(-h))^(1/(1-h)))^(1-h) = A*δ^(-h) := by
    rw [← Real.rpow_mul ha]
    have hx : (1/(1-h))*(1-h)=1 := by field_simp
    rw [hx,Real.rpow_one]
  rw [hpow,Real.mul_rpow hδ.le he] at hy
  have hcancel : δ^h * δ^(-h)=1 := by
    rw [←Real.rpow_add hδ,add_neg_cancel,Real.rpow_zero]
  have hl : δ^h*e^h*(A*δ^(-h))=A*e^h := by
    calc
      _ = A*e^h*(δ^h*δ^(-h)) := by ring
      _ = _ := by rw [hcancel,mul_one]
  rw [hl,Real.mul_rpow hA (Real.rpow_nonneg hδ.le _),←Real.rpow_mul hδ.le] at hy
  have hx : -h*(1/(1-h))=-h/(1-h) := by ring
  rw [hx] at hy
  convert hy using 1 <;> ring

theorem absorption {n : ℕ} {e Λ B₀ : ℝ} (A h : Fin n → ℝ)
    (he : 0 ≤ e) (hΛ : 0 ≤ Λ) (hB₀ : 0 ≤ B₀)
    (hA : ∀ i, 0 ≤ A i) (hh : ∀ i, h i ∈ Set.Ioo (0 : ℝ) 1)
    (hbound : e ≤ B₀ + ∑ i, A i * (e+Λ) ^ h i) :
    e ≤ 2*B₀ + 2*∑ i, (A i*Λ^h i +
      (1-h i)*(2*(n:ℝ)*h i)^(h i/(1-h i))*A i^(1/(1-h i))) := by
  classical
  by_cases hn : n=0
  · subst n
    simp only [Fin.sum_univ_zero,add_zero,mul_zero] at hbound ⊢
    linarith
  have hnp : 0 < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hb (i : Fin n) : A i * (e+Λ)^h i ≤ A i*Λ^h i +
      e/(2*(n:ℝ)) +
        (1-h i)*(2*(n:ℝ)*h i)^(h i/(1-h i))*A i^(1/(1-h i)) := by
    have hp : 0 < 2*(n:ℝ)*h i := by positivity [ (hh i).1 ]
    have hy := scaled_young_rpow (hA i) he (hh i).1 (hh i).2 (inv_pos.mpr hp)
    have hg := mul_le_mul_of_nonneg_left
      (Real.rpow_add_le_add_rpow he hΛ (hh i).1.le (hh i).2.le) (hA i)
    have hinv : ((2*(n:ℝ)*h i)⁻¹)^(-h i/(1-h i)) =
        (2*(n:ℝ)*h i)^(h i/(1-h i)) := by
      rw [Real.inv_rpow hp.le,←Real.rpow_neg hp.le]
      congr 1
      ring
    rw [hinv] at hy
    have hc : h i * (2*(n:ℝ)*h i)⁻¹ * e=e/(2*(n:ℝ)) := by
      field_simp [hnp.ne', (hh i).1.ne']
    rw [hc] at hy
    nlinarith
  have hs := Finset.sum_le_sum (fun i (_hi : i∈Finset.univ) => hb i)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul] at hs
  have hc : (n:ℝ)*(e/(2*(n:ℝ)))=e/2 := by field_simp
  rw [hc] at hs
  rw [Finset.sum_add_distrib]
  linarith

end QuantitativeFollowup
