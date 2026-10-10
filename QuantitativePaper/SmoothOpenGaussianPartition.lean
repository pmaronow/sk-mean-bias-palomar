module
public import QuantitativePaper.LocalJetBounds
public import QuantitativePaper.SmoothGaussianPartition

@[expose] public section

/-! Genuine Gaussian parameter integrals on shift-invariant open domains.
Positive-order jets may grow exponentially in the parameter norm; the value
itself has linear growth, which keeps every Gaussian majorant integrable. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal
namespace QuantitativePaper
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 1400000

theorem continuous_iteratedFDeriv_shift_on_open {n N j : ℕ}
    (f : E → ℝ) (U : Set E) (hU : IsOpen U) (hf : ContDiffOn ℝ N f U)
    (A : Field n →L[ℝ] E) (hshift : ∀ x ∈ U, ∀ z, x+A z ∈ U)
    (hj : j ≤ N) (x : E) (hx : x ∈ U) :
    Continuous (fun z => iteratedFDeriv ℝ j f (x+A z)) := by
  have hc := (hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast hj) hU.uniqueDiffOn).comp_continuous (continuous_const.add A.continuous) (hshift x hx)
  apply hc.congr
  intro z
  exact iteratedFDerivWithin_of_isOpen j hU (hshift x hx z)

theorem norm_iteratedFDeriv_exp_shift_le {n N j : ℕ}
    (g : E → ℝ) (U : Set E) (hU : IsOpen U) (hg : ContDiffOn ℝ N g U)
    (A : Field n →L[ℝ] E) (hshift : ∀ x ∈ U, ∀ z, x+A z ∈ U)
    (K D : ℝ) (hK : 0 ≤ K)
    (hjets : ∀ i, 1 ≤ i → i ≤ N → ∀ x ∈ U,
      ‖iteratedFDeriv ℝ i g x‖ ≤ (K*Real.exp (D*‖x‖))^i)
    (hj : j ≤ N) (x : E) (hx : x ∈ U) (z : Field n) :
    ‖iteratedFDeriv ℝ j (fun y => Real.exp (g (y+A z))) x‖ ≤
      (j.factorial:ℝ)*K^j*Real.exp (g (x+A z)+(j:ℝ)*D*‖x+A z‖) := by
  let F : E → ℝ := fun y => Real.exp (g y)
  change ‖iteratedFDeriv ℝ j (fun y => F (y+A z)) x‖ ≤ _
  rw [iteratedFDeriv_comp_add_right]
  have hh := norm_iteratedFDeriv_exp_le_on_open g U hU hg hj
    (K*Real.exp (D*‖x+A z‖)) (x+A z) (hshift x hx z)
    (fun i hi hij => hjets i hi (hij.trans hj) _ (hshift x hx z))
  apply hh.trans_eq
  rw [mul_pow, ← Real.exp_nat_mul]
  rw [show g (x+A z)+(j:ℝ)*D*‖x+A z‖ = g (x+A z)+(j:ℝ)*(D*‖x+A z‖) by ring,
    Real.exp_add]
  ring

theorem gaussianShiftPartition_smooth_inputs_on_open {n : ℕ} (N : ℕ)
    (g : E → ℝ) (U : Set E) (hU : IsOpen U) (hg : ContDiffOn ℝ N g U)
    (A : Field n →L[ℝ] E) (hshift : ∀ x ∈ U, ∀ z, x+A z ∈ U)
    (B L K D : ℝ) (hL : 0 ≤ L) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hvalue : ∀ x ∈ U, g x ≤ B+L*‖x‖)
    (hjets : ∀ i, 1 ≤ i → i ≤ N → ∀ x ∈ U,
      ‖iteratedFDeriv ℝ i g x‖ ≤ (K*Real.exp (D*‖x‖))^i) :
    (∀ z, ContDiffOn ℝ N (fun x => Real.exp (g (x+A z))) U) ∧
    (∀ j, j ≤ N → ∀ x ∈ U, AEStronglyMeasurable
      (fun z => iteratedFDeriv ℝ j (fun y => Real.exp (g (y+A z))) x) (fieldGaussian n)) ∧
    (∀ x ∈ U, ∃ s ∈ 𝓝 x, s ⊆ U ∧ ∃ J : ℕ → Field n → ℝ,
      (∀ j, j ≤ N → Integrable (J j) (fieldGaussian n)) ∧
      ∀ j, j ≤ N → ∀ y ∈ s, ∀ z,
        ‖iteratedFDeriv ℝ j (fun u => Real.exp (g (u+A z))) y‖ ≤ J j z) := by
  have hG : ContDiffOn ℝ N (fun x => Real.exp (g x)) U := hg.exp
  refine ⟨fun z => hG.comp (contDiffOn_id.add contDiffOn_const) (fun x hx => hshift x hx z), ?_, ?_⟩
  · intro j hj x hx
    let F : E → ℝ := fun y => Real.exp (g y)
    change AEStronglyMeasurable (fun z => iteratedFDeriv ℝ j (fun y => F (y+A z)) x) _
    simp_rw [iteratedFDeriv_comp_add_right]
    exact (continuous_iteratedFDeriv_shift_on_open _ U hU hG A hshift hj x hx).aestronglyMeasurable
  · intro x hx
    let R := ‖x‖+1
    let J : ℕ → Field n → ℝ := fun j z =>
      (j.factorial:ℝ)*K^j*Real.exp (B+(L+(j:ℝ)*D)*R)*
        Real.exp ((L+(j:ℝ)*D)*‖A‖*‖z‖)
    refine ⟨Metric.ball x 1 ∩ U, inter_mem (Metric.ball_mem_nhds x (by norm_num))
      (hU.mem_nhds hx), inter_subset_right, J, ?_, ?_⟩
    · intro j _
      exact (SYK.integrable_exp_mul_norm (ι:=Fin n) ((L+(j:ℝ)*D)*‖A‖)).const_mul
        ((j.factorial:ℝ)*K^j*Real.exp (B+(L+(j:ℝ)*D)*R))
    · intro j hj y hy z
      have hn : ‖y+A z‖ ≤ R+‖A‖*‖z‖ := by
        have hy' : ‖y‖ ≤ R := by
          exact norm_le_norm_add_const_of_dist_le hy.1.le
        exact (norm_add_le y (A z)).trans (add_le_add hy' (A.le_opNorm z))
      apply (norm_iteratedFDeriv_exp_shift_le g U hU hg A hshift K D hK hjets hj y hy.2 z).trans
      dsimp only [J]
      rw [mul_assoc ((j.factorial:ℝ)*K^j), ← Real.exp_add]
      apply mul_le_mul_of_nonneg_left ?_ (by positivity : 0 ≤ (j.factorial:ℝ)*K^j)
      apply Real.exp_le_exp.mpr
      have hl : 0 ≤ L+(j:ℝ)*D := by positivity
      have hv := hvalue (y+A z) (hshift y hy.2 z)
      have hh := mul_le_mul_of_nonneg_left hn hl
      nlinarith

theorem contDiffOn_gaussianShiftPartition_of_exp_jets {n : ℕ} (N : ℕ)
    (g : E → ℝ) (U : Set E) (hU : IsOpen U) (hg : ContDiffOn ℝ N g U)
    (A : Field n →L[ℝ] E) (hshift : ∀ x ∈ U, ∀ z, x+A z ∈ U)
    (B L K D : ℝ) (hL : 0 ≤ L) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hvalue : ∀ x ∈ U, g x ≤ B+L*‖x‖)
    (hjets : ∀ i, 1 ≤ i → i ≤ N → ∀ x ∈ U,
      ‖iteratedFDeriv ℝ i g x‖ ≤ (K*Real.exp (D*‖x‖))^i) :
    ContDiffOn ℝ N (gaussianShiftPartition A 1 g) U := by
  obtain ⟨h₁, h₂, h₃⟩ := gaussianShiftPartition_smooth_inputs_on_open N g U hU hg A hshift
    B L K D hL hK hD hvalue hjets
  change ContDiffOn ℝ N (fun x => ∫ z, Real.exp (1*g (x+A z)) ∂fieldGaussian n) U
  simp only [one_mul]
  exact contDiffOn_integral_of_dominated_derivatives N (fieldGaussian n) _ U hU h₁ h₂ h₃

end QuantitativePaper
