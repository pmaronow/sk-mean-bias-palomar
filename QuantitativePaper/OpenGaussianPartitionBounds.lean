module
public import QuantitativePaper.SmoothOpenGaussianPartition
public import QuantitativePaper.FiniteJetBounds

@[expose] public section

/-! Actual Gaussian partition lower bounds and relative derivative bounds.
The value at the base point cancels from every logarithmic derivative bound. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal
namespace QuantitativePaper
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 1400000

def gaussianNormExponentialMoment (n : ℕ) (c : ℝ) : ℝ :=
  ∫ z : Field n, Real.exp (c*‖z‖) ∂fieldGaussian n

theorem gaussianNormExponentialMoment_pos (n : ℕ) (c : ℝ) :
    0 < gaussianNormExponentialMoment n c := by
  apply (integral_pos_iff_support_of_nonneg (fun _ => (Real.exp_pos _).le)
    (SYK.integrable_exp_mul_norm (ι:=Fin n) c)).mpr
  have hs : Function.support (fun z : Field n => Real.exp (c*‖z‖)) = univ := by
    ext z
    simp [Function.mem_support, Real.exp_ne_zero]
  rw [hs]
  simp

theorem integrable_gaussianShiftPartition_on_open {n : ℕ} (N : ℕ)
    (g : E → ℝ) (U : Set E) (hU : IsOpen U) (hg : ContDiffOn ℝ N g U)
    (A : Field n →L[ℝ] E) (hshift : ∀ x ∈ U, ∀ z, x+A z ∈ U)
    (B L K D : ℝ) (hL : 0 ≤ L) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hvalue : ∀ x ∈ U, g x ≤ B+L*‖x‖)
    (hjets : ∀ i, 1 ≤ i → i ≤ N → ∀ x ∈ U,
      ‖iteratedFDeriv ℝ i g x‖ ≤ (K*Real.exp (D*‖x‖))^i)
    (x : E) (hx : x ∈ U) :
    Integrable (fun z => Real.exp (g (x+A z))) (fieldGaussian n) := by
  obtain ⟨_, hm, hb⟩ := gaussianShiftPartition_smooth_inputs_on_open N g U hU hg A hshift
    B L K D hL hK hD hvalue hjets
  obtain ⟨s, hs, _, J, hi, hJ⟩ := hb x hx
  have hmeas := (continuousMultilinearCurryFin0 ℝ E ℝ).continuous.comp_aestronglyMeasurable
    (hm 0 (Nat.zero_le _) x hx)
  apply (hi 0 (Nat.zero_le _)).mono'
  · simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply,
      LinearIsometryEquiv.apply_symm_apply] using hmeas
  · exact .of_forall fun z => by
      simpa only [norm_iteratedFDeriv_zero] using hJ 0 (Nat.zero_le _) x (mem_of_mem_nhds hs) z

theorem gaussianShiftPartition_lower_on_open {n : ℕ} (N : ℕ)
    (g : E → ℝ) (U : Set E) (hU : IsOpen U) (hg : ContDiffOn ℝ N g U)
    (A : Field n →L[ℝ] E) (hshift : ∀ x ∈ U, ∀ z, x+A z ∈ U)
    (B L K D H : ℝ) (hL : 0 ≤ L) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hvalue : ∀ x ∈ U, g x ≤ B+L*‖x‖)
    (hjets : ∀ i, 1 ≤ i → i ≤ N → ∀ x ∈ U,
      ‖iteratedFDeriv ℝ i g x‖ ≤ (K*Real.exp (D*‖x‖))^i)
    (hlip : ∀ x ∈ U, ∀ z, |g (x+A z)-g x| ≤ H*‖z‖)
    (x : E) (hx : x ∈ U) :
    Real.exp (g x)*gaussianNormExponentialMoment n (-H) ≤ gaussianShiftPartition A 1 g x := by
  have hi := integrable_gaussianShiftPartition_on_open N g U hU hg A hshift
    B L K D hL hK hD hvalue hjets x hx
  have hm := integral_mono
    ((SYK.integrable_exp_mul_norm (ι:=Fin n) (-H)).const_mul (Real.exp (g x))) hi
    (fun z => by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hh := (abs_le.mp (hlip x hx z)).1
      linarith)
  simpa only [integral_const_mul, gaussianNormExponentialMoment, gaussianShiftPartition, one_mul] using hm

theorem gaussianShiftPartition_pos_on_open {n : ℕ} (N : ℕ)
    (g : E → ℝ) (U : Set E) (hU : IsOpen U) (hg : ContDiffOn ℝ N g U)
    (A : Field n →L[ℝ] E) (hshift : ∀ x ∈ U, ∀ z, x+A z ∈ U)
    (B L K D H : ℝ) (hL : 0 ≤ L) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hvalue : ∀ x ∈ U, g x ≤ B+L*‖x‖)
    (hjets : ∀ i, 1 ≤ i → i ≤ N → ∀ x ∈ U,
      ‖iteratedFDeriv ℝ i g x‖ ≤ (K*Real.exp (D*‖x‖))^i)
    (hlip : ∀ x ∈ U, ∀ z, |g (x+A z)-g x| ≤ H*‖z‖)
    (x : E) (hx : x ∈ U) :
    0 < gaussianShiftPartition A 1 g x :=
  (mul_pos (Real.exp_pos _) (gaussianNormExponentialMoment_pos n (-H))).trans_le
    (gaussianShiftPartition_lower_on_open N g U hU hg A hshift B L K D H hL hK hD
      hvalue hjets hlip x hx)

theorem norm_iteratedFDeriv_gaussianShiftPartition_exp_bound {n N j : ℕ}
    (g : E → ℝ) (U : Set E) (hU : IsOpen U) (hg : ContDiffOn ℝ N g U)
    (A : Field n →L[ℝ] E) (hshift : ∀ x ∈ U, ∀ z, x+A z ∈ U)
    (B L K D H : ℝ) (hL : 0 ≤ L) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hvalue : ∀ x ∈ U, g x ≤ B+L*‖x‖)
    (hjets : ∀ i, 1 ≤ i → i ≤ N → ∀ x ∈ U,
      ‖iteratedFDeriv ℝ i g x‖ ≤ (K*Real.exp (D*‖x‖))^i)
    (hlip : ∀ x ∈ U, ∀ z, |g (x+A z)-g x| ≤ H*‖z‖)
    (hj : j ≤ N) (x : E) (hx : x ∈ U) :
    ‖iteratedFDeriv ℝ j (gaussianShiftPartition A 1 g) x‖ ≤
      (j.factorial:ℝ)*K^j*Real.exp (g x+(j:ℝ)*D*‖x‖)*
        gaussianNormExponentialMoment n (H+(j:ℝ)*D*‖A‖) := by
  obtain ⟨h₁, h₂, h₃⟩ := gaussianShiftPartition_smooth_inputs_on_open N g U hU hg A hshift
    B L K D hL hK hD hvalue hjets
  have he := iteratedFDeriv_integral_of_locally_dominated_derivatives N (fieldGaussian n)
    (fun x z => Real.exp (g (x+A z))) U hU h₁ h₂ h₃ j hj x hx
  change ‖iteratedFDeriv ℝ j (fun x => ∫ z, Real.exp (1*g (x+A z)) ∂fieldGaussian n) x‖ ≤ _
  simp only [one_mul]
  rw [he]
  have hb := norm_integral_le_of_norm_le
    (g := fun z : Field n => (j.factorial:ℝ)*K^j*Real.exp (g x+(j:ℝ)*D*‖x‖)*
      Real.exp ((H+(j:ℝ)*D*‖A‖)*‖z‖))
    ((SYK.integrable_exp_mul_norm (ι:=Fin n) (H+(j:ℝ)*D*‖A‖)).const_mul _)
    (.of_forall fun z => by
      apply (norm_iteratedFDeriv_exp_shift_le g U hU hg A hshift K D hK hjets hj x hx z).trans
      rw [mul_assoc ((j.factorial:ℝ)*K^j), ← Real.exp_add]
      apply mul_le_mul_of_nonneg_left ?_ (by positivity : 0 ≤ (j.factorial:ℝ)*K^j)
      apply Real.exp_le_exp.mpr
      have hl := (abs_le.mp (hlip x hx z)).2
      have hn := (norm_add_le x (A z)).trans (add_le_add (le_refl ‖x‖) (A.le_opNorm z))
      have hh := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ (j:ℝ)*D)
      nlinarith)
  simpa only [integral_const_mul, gaussianNormExponentialMoment] using hb

end QuantitativePaper
