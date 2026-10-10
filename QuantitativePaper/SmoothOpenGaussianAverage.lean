module
public import QuantitativePaper.OpenGaussianPartitionBounds
public import QuantitativePaper.SmoothGaussianAverage

@[expose] public section

/-! Actual zero-mass smoothing on an open parameter domain with exponential
jet envelopes. Every domination and derivative identity uses the Gaussian
integral itself. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal
namespace QuantitativePaper
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 1400000

theorem gaussianShiftAverage_smooth_exp_inputs_on_open {n : ℕ} (N : ℕ)
    (f : E → ℝ) (U : Set E) (hU : IsOpen U) (hf : ContDiffOn ℝ N f U)
    (A : Field n →L[ℝ] E) (hshift : ∀ x ∈ U, ∀ z, x+A z ∈ U)
    (K D : ℝ) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hjets : ∀ j, j ≤ N → ∀ x ∈ U,
      ‖iteratedFDeriv ℝ j f x‖ ≤ (K*Real.exp (D*‖x‖))^(j+1)) :
    (∀ z, ContDiffOn ℝ N (fun x => f (x+A z)) U) ∧
    (∀ j, j ≤ N → ∀ x ∈ U, AEStronglyMeasurable
      (fun z => iteratedFDeriv ℝ j (fun y => f (y+A z)) x) (fieldGaussian n)) ∧
    (∀ x ∈ U, ∃ s ∈ 𝓝 x, s ⊆ U ∧ ∃ J : ℕ → Field n → ℝ,
      (∀ j, j ≤ N → Integrable (J j) (fieldGaussian n)) ∧
      ∀ j, j ≤ N → ∀ y ∈ s, ∀ z,
        ‖iteratedFDeriv ℝ j (fun u => f (u+A z)) y‖ ≤ J j z) := by
  refine ⟨fun z => hf.comp (contDiffOn_id.add contDiffOn_const) (fun x hx => hshift x hx z), ?_, ?_⟩
  · intro j hj x hx
    simp_rw [iteratedFDeriv_comp_add_right]
    exact (continuous_iteratedFDeriv_shift_on_open f U hU hf A hshift hj x hx).aestronglyMeasurable
  · intro x hx
    let R := ‖x‖+1
    let J : ℕ → Field n → ℝ := fun j z => K^(j+1)*Real.exp ((j+1:ℕ)*D*R)*
      Real.exp ((j+1:ℕ)*D*‖A‖*‖z‖)
    refine ⟨Metric.ball x 1 ∩ U, inter_mem (Metric.ball_mem_nhds x (by norm_num))
      (hU.mem_nhds hx), inter_subset_right, J, ?_, ?_⟩
    · intro j _
      exact (SYK.integrable_exp_mul_norm (ι:=Fin n) ((j+1:ℕ)*D*‖A‖)).const_mul _
    · intro j hj y hy z
      rw [iteratedFDeriv_comp_add_right]
      apply (hjets j hj (y+A z) (hshift y hy.2 z)).trans
      dsimp only [J]
      rw [mul_pow, ← Real.exp_nat_mul, mul_assoc (K^(j+1)), ← Real.exp_add]
      apply mul_le_mul_of_nonneg_left ?_ (pow_nonneg hK _)
      apply Real.exp_le_exp.mpr
      have hy' : ‖y‖ ≤ R := norm_le_norm_add_const_of_dist_le hy.1.le
      have hn := (norm_add_le y (A z)).trans (add_le_add hy' (A.le_opNorm z))
      have hh := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ ((j+1:ℕ):ℝ)*D)
      nlinarith

theorem gaussianShiftAverage_smooth_exp_jets_on_open {n : ℕ} (N : ℕ)
    (f : E → ℝ) (U : Set E) (hU : IsOpen U) (hf : ContDiffOn ℝ N f U)
    (A : Field n →L[ℝ] E) (hshift : ∀ x ∈ U, ∀ z, x+A z ∈ U)
    (K D : ℝ) (hK : 1 ≤ K) (hD : 0 ≤ D)
    (hjets : ∀ j, j ≤ N → ∀ x ∈ U,
      ‖iteratedFDeriv ℝ j f x‖ ≤ (K*Real.exp (D*‖x‖))^(j+1)) :
    ContDiffOn ℝ N (gaussianShiftAverage A f) U ∧
      ∃ C : ℝ, 1 ≤ C ∧ ∀ j, 1 ≤ j → j ≤ N → ∀ x ∈ U,
        ‖iteratedFDeriv ℝ j (gaussianShiftAverage A f) x‖ ≤
          (C*Real.exp ((2*D)*‖x‖))^j := by
  have hK0 := zero_le_one.trans hK
  obtain ⟨h₁, h₂, h₃⟩ := gaussianShiftAverage_smooth_exp_inputs_on_open N f U hU hf A hshift K D hK0 hD hjets
  have hs : ContDiffOn ℝ N (gaussianShiftAverage A f) U :=
    contDiffOn_integral_of_dominated_derivatives N (fieldGaussian n) _ U hU h₁ h₂ h₃
  let J : ℕ → ℝ := fun j => gaussianNormExponentialMoment n ((j+1:ℕ)*D*‖A‖)
  let R := finiteJetPowerBound J N
  refine ⟨hs, R*K^2, ?_, ?_⟩
  · exact one_le_mul_of_one_le_of_one_le (finiteJetPowerBound_ge_one J N) (one_le_pow₀ hK)
  · intro j hj0 hj x hx
    have he := iteratedFDeriv_integral_of_locally_dominated_derivatives N (fieldGaussian n)
      (fun x z => f (x+A z)) U hU h₁ h₂ h₃ j hj x hx
    change ‖iteratedFDeriv ℝ j (fun x => ∫ z, f (x+A z) ∂fieldGaussian n) x‖ ≤ _
    rw [he]
    have hb := norm_integral_le_of_norm_le
      (f := fun z : Field n => iteratedFDeriv ℝ j (fun y => f (y+A z)) x)
      (g := fun z : Field n => K^(j+1)*Real.exp ((j+1:ℕ)*D*‖x‖)*
        Real.exp ((j+1:ℕ)*D*‖A‖*‖z‖))
      ((SYK.integrable_exp_mul_norm (ι:=Fin n) ((j+1:ℕ)*D*‖A‖)).const_mul _)
      (.of_forall fun z => by
        rw [iteratedFDeriv_comp_add_right]
        apply (hjets j hj (x+A z) (hshift x hx z)).trans
        rw [mul_pow, ← Real.exp_nat_mul, mul_assoc (K^(j+1)), ← Real.exp_add]
        apply mul_le_mul_of_nonneg_left ?_ (pow_nonneg hK0 _)
        apply Real.exp_le_exp.mpr
        have hn := (norm_add_le x (A z)).trans (add_le_add (le_refl ‖x‖) (A.le_opNorm z))
        have hh := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ ((j+1:ℕ):ℝ)*D)
        nlinarith)
    rw [integral_const_mul] at hb
    apply hb.trans
    have hp : 1 ≤ K*Real.exp (D*‖x‖) :=
      one_le_mul_of_one_le_of_one_le hK (Real.one_le_exp_iff.mpr (mul_nonneg hD (norm_nonneg _)))
    have hpower := pow_le_pow_right₀ hp (by omega : j+1 ≤ 2*j)
    have hJ := finite_jet_bound_le_power J N j hj0 hj
    have hJn := (gaussianNormExponentialMoment_pos n ((j+1:ℕ)*D*‖A‖)).le
    have hh := mul_le_mul hpower hJ hJn (pow_nonneg (zero_le_one.trans hp) _)
    calc
      _ = (K*Real.exp (D*‖x‖))^(j+1)*J j := by
        rw [mul_pow, ← Real.exp_nat_mul]
        simp only [J, gaussianNormExponentialMoment, fieldGaussian, mul_assoc]
      _ ≤ (K*Real.exp (D*‖x‖))^(2*j)*R^j := hh
      _ = (R*K^2*Real.exp ((2*D)*‖x‖))^j := by
        have heE : Real.exp ((2*D)*‖x‖)^j = Real.exp (D*‖x‖)^(2*j) := by
          rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
          congr 1
          push_cast
          ring
        rw [mul_pow, mul_pow, mul_pow, heE, pow_mul]
        ring


end QuantitativePaper
