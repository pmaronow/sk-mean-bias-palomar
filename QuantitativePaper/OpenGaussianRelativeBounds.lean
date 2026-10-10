module
public import QuantitativePaper.OpenGaussianPartitionBounds

@[expose] public section

/-! Gaussian smoothing preserves exponential growth bounds on the actual
positive-order jets. The relative bounds cancel the linear-growth potential. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal
namespace QuantitativePaper
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 1400000

def gaussianRelativeJetCoefficient (n : ℕ) (K D H a : ℝ) (j : ℕ) : ℝ :=
  (j.factorial:ℝ)*K^j*gaussianNormExponentialMoment n (H+(j:ℝ)*D*a) /
    gaussianNormExponentialMoment n (-H)

theorem gaussianRelativeJetCoefficient_nonneg (n : ℕ) (K D H a : ℝ)
    (hK : 0 ≤ K) (j : ℕ) : 0 ≤ gaussianRelativeJetCoefficient n K D H a j := by
  unfold gaussianRelativeJetCoefficient
  have hp := (gaussianNormExponentialMoment_pos n (H+(j:ℝ)*D*a)).le
  exact div_nonneg (by positivity)
    (gaussianNormExponentialMoment_pos n (-H)).le

theorem norm_iteratedFDeriv_gaussianShiftPartition_relative_exp {n N j : ℕ}
    (g : E → ℝ) (U : Set E) (hU : IsOpen U) (hg : ContDiffOn ℝ N g U)
    (A : Field n →L[ℝ] E) (hshift : ∀ x ∈ U, ∀ z, x+A z ∈ U)
    (B L K D H : ℝ) (hL : 0 ≤ L) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hvalue : ∀ x ∈ U, g x ≤ B+L*‖x‖)
    (hjets : ∀ i, 1 ≤ i → i ≤ N → ∀ x ∈ U,
      ‖iteratedFDeriv ℝ i g x‖ ≤ (K*Real.exp (D*‖x‖))^i)
    (hlip : ∀ x ∈ U, ∀ z, |g (x+A z)-g x| ≤ H*‖z‖)
    (hj : j ≤ N) (x : E) (hx : x ∈ U) :
    ‖iteratedFDeriv ℝ j (gaussianShiftPartition A 1 g) x‖ ≤
      gaussianRelativeJetCoefficient n K D H ‖A‖ j *
        Real.exp ((j:ℝ)*D*‖x‖)*gaussianShiftPartition A 1 g x := by
  have hjn := (gaussianNormExponentialMoment_pos n (-H)).ne'
  have hn := norm_iteratedFDeriv_gaussianShiftPartition_exp_bound g U hU hg A hshift
    B L K D H hL hK hD hvalue hjets hlip hj x hx
  have hl := gaussianShiftPartition_lower_on_open N g U hU hg A hshift
    B L K D H hL hK hD hvalue hjets hlip x hx
  calc
    _ ≤ (j.factorial:ℝ)*K^j*Real.exp (g x+(j:ℝ)*D*‖x‖)*
        gaussianNormExponentialMoment n (H+(j:ℝ)*D*‖A‖) := hn
    _ = gaussianRelativeJetCoefficient n K D H ‖A‖ j *
        Real.exp ((j:ℝ)*D*‖x‖)*(Real.exp (g x)*gaussianNormExponentialMoment n (-H)) := by
      unfold gaussianRelativeJetCoefficient
      rw [Real.exp_add]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hl
      (mul_nonneg (gaussianRelativeJetCoefficient_nonneg n K D H ‖A‖ hK j) (Real.exp_pos _).le)

theorem gaussianShiftPartition_smooth_relative_exp_jets {n : ℕ} (N : ℕ)
    (g : E → ℝ) (U : Set E) (hU : IsOpen U) (hg : ContDiffOn ℝ N g U)
    (A : Field n →L[ℝ] E) (hshift : ∀ x ∈ U, ∀ z, x+A z ∈ U)
    (B L K D H : ℝ) (hL : 0 ≤ L) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hvalue : ∀ x ∈ U, g x ≤ B+L*‖x‖)
    (hjets : ∀ i, 1 ≤ i → i ≤ N → ∀ x ∈ U,
      ‖iteratedFDeriv ℝ i g x‖ ≤ (K*Real.exp (D*‖x‖))^i)
    (hlip : ∀ x ∈ U, ∀ z, |g (x+A z)-g x| ≤ H*‖z‖) :
    ContDiffOn ℝ N (gaussianShiftPartition A 1 g) U ∧
      (∀ x ∈ U, 0 < gaussianShiftPartition A 1 g x) ∧
      ∃ C : ℝ, 1 ≤ C ∧ ∀ j, 1 ≤ j → j ≤ N → ∀ x ∈ U,
        ‖iteratedFDeriv ℝ j (gaussianShiftPartition A 1 g) x‖ ≤
          (C*Real.exp (D*‖x‖))^j*gaussianShiftPartition A 1 g x := by
  have hZ := contDiffOn_gaussianShiftPartition_of_exp_jets N g U hU hg A hshift
    B L K D hL hK hD hvalue hjets
  have hp := gaussianShiftPartition_pos_on_open N g U hU hg A hshift
    B L K D H hL hK hD hvalue hjets hlip
  let C := finiteJetPowerBound (gaussianRelativeJetCoefficient n K D H ‖A‖) N
  refine ⟨hZ, hp, C, finiteJetPowerBound_ge_one _ _, ?_⟩
  intro j hj0 hj x hx
  have hn := norm_iteratedFDeriv_gaussianShiftPartition_relative_exp g U hU hg A hshift
    B L K D H hL hK hD hvalue hjets hlip hj x hx
  apply hn.trans
  have hc := finite_jet_bound_le_power (gaussianRelativeJetCoefficient n K D H ‖A‖) N j hj0 hj
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (Real.exp_pos ((j:ℝ)*D*‖x‖)).le) (hp x hx).le
  convert hh using 1
  rw [mul_pow, ← Real.exp_nat_mul]
  congr 2
  ring

theorem log_gaussianShiftPartition_smooth_exp_jets {n : ℕ} (N : ℕ)
    (g : E → ℝ) (U : Set E) (hU : IsOpen U) (hg : ContDiffOn ℝ N g U)
    (A : Field n →L[ℝ] E) (hshift : ∀ x ∈ U, ∀ z, x+A z ∈ U)
    (B L K D H : ℝ) (hL : 0 ≤ L) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hvalue : ∀ x ∈ U, g x ≤ B+L*‖x‖)
    (hjets : ∀ i, 1 ≤ i → i ≤ N → ∀ x ∈ U,
      ‖iteratedFDeriv ℝ i g x‖ ≤ (K*Real.exp (D*‖x‖))^i)
    (hlip : ∀ x ∈ U, ∀ z, |g (x+A z)-g x| ≤ H*‖z‖) :
    ContDiffOn ℝ N (fun x => Real.log (gaussianShiftPartition A 1 g x)) U ∧
      ∃ C : ℝ, 1 ≤ C ∧ ∀ j, 1 ≤ j → j ≤ N → ∀ x ∈ U,
        ‖iteratedFDeriv ℝ j (fun x => Real.log (gaussianShiftPartition A 1 g x)) x‖ ≤
          (C*Real.exp (D*‖x‖))^j := by
  obtain ⟨hZ, hp, C, hC, hrelative⟩ := gaussianShiftPartition_smooth_relative_exp_jets N g U hU
    hg A hshift B L K D H hL hK hD hvalue hjets hlip
  let J : ℕ → ℝ := fun j => (j.factorial:ℝ)*logJetCoefficient j
  let R := finiteJetPowerBound J N
  refine ⟨hZ.log (fun x hx => (hp x hx).ne'), R*C, ?_, ?_⟩
  · exact one_le_mul_of_one_le_of_one_le (finiteJetPowerBound_ge_one J N) hC
  · intro j hj0 hj x hx
    have hn := norm_iteratedFDeriv_log_le_of_relative_on_open _ U hU hZ hp hj0 hj
      (C*Real.exp (D*‖x‖)) x hx (fun i hi hij => hrelative i hi (hij.trans hj) x hx)
    apply hn.trans
    have hJ := finite_jet_bound_le_power J N j hj0 hj
    have hh := mul_le_mul_of_nonneg_right hJ (by positivity : 0 ≤ (C*Real.exp (D*‖x‖))^j)
    convert hh using 1
    rw [← mul_pow]
    congr 1
    ring

end QuantitativePaper
