module
public import QuantitativePaper.SmoothGaussianPartition
public import QuantitativePaper.BoundedJets

@[expose] public section

/-! Actual Gaussian smoothing of an exponentially weighted smooth
observable. Spatial derivatives of the numerator are bounded relative to
the genuine positive partition function, uniformly in the shift operator.
The terminal potential may have linear growth. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal BigOperators
namespace QuantitativePaper
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 1000000

def gaussianWeightedShiftMoment {n : ℕ} (A : Field n →L[ℝ] E)
    (m : ℝ) (f g : E → ℝ) (x : E) : ℝ :=
  ∫ z,Real.exp (m*f (x+A z))*g (x+A z) ∂fieldGaussian n

def gaussianWeightedJetCoefficient (m K : ℝ) (G : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ i∈Finset.range (j+1),(j.choose i : ℝ)*gaussianJetCoefficient m K i*G (j-i)

theorem gaussianWeightedJetCoefficient_nonneg (m K : ℝ) (hK : 0 ≤ K)
    (G : ℕ → ℝ) (hG : ∀ i,0 ≤ G i) (j : ℕ) :
    0 ≤ gaussianWeightedJetCoefficient m K G j := by
  exact Finset.sum_nonneg (fun i _=>mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (gaussianJetCoefficient_nonneg m K hK i)) (hG _))

theorem norm_iteratedFDeriv_exp_mul_observable_le {N j : ℕ}
    (f g : E → ℝ) (hf : ContDiff ℝ N f) (hg : ContDiff ℝ N g)
    (m K : ℝ) (hK : 0 ≤ K) (G : ℕ → ℝ) (hG : ∀ i,0 ≤ G i)
    (hjets : ∀ i,1 ≤ i → i ≤ N → ∀ x,‖iteratedFDeriv ℝ i f x‖ ≤ K^i)
    (hgJets : ∀ i,i ≤ N → ∀ x,‖iteratedFDeriv ℝ i g x‖ ≤ G i)
    (hj : j ≤ N) (x : E) :
    ‖iteratedFDeriv ℝ j (fun y=>Real.exp (m*f y)*g y) x‖ ≤
      gaussianWeightedJetCoefficient m K G j*Real.exp (m*f x) := by
  have he : ContDiff ℝ N (fun y=>Real.exp (m*f y)) := (contDiff_const.mul hf).exp
  apply (norm_iteratedFDeriv_mul_le he hg x (by exact_mod_cast hj)).trans
  rw [gaussianWeightedJetCoefficient,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hb := norm_iteratedFDeriv_exp_mul_le f hf (hi'.trans hj) m K x
    (fun l hl hli=>hjets l hl (hli.trans (hi'.trans hj)) x)
  have hb' : ‖iteratedFDeriv ℝ i (fun y=>Real.exp (m*f y)) x‖ ≤
      gaussianJetCoefficient m K i*Real.exp (m*f x) := by
    simpa only [gaussianJetCoefficient,mul_assoc,mul_left_comm,mul_comm] using hb
  have hc := mul_le_mul hb' (hgJets (j-i) ((Nat.sub_le j i).trans hj) x)
    (norm_nonneg _) (mul_nonneg (gaussianJetCoefficient_nonneg m K hK i) (Real.exp_pos _).le)
  have hh := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (j.choose i))
  simpa only [gaussianJetCoefficient,mul_assoc,mul_left_comm,mul_comm] using hh

theorem gaussianWeightedShiftMoment_smooth_inputs {n : ℕ} (N : ℕ)
    (f g : E → ℝ) (hf : ContDiff ℝ N f) (hg : ContDiff ℝ N g)
    (L : ℝ≥0) (hlip : LipschitzWith L f) (m K : ℝ) (hK : 0 ≤ K)
    (G : ℕ → ℝ) (hG : ∀ i,0 ≤ G i)
    (hjets : ∀ i,1 ≤ i → i ≤ N → ∀ x,‖iteratedFDeriv ℝ i f x‖ ≤ K^i)
    (hgJets : ∀ i,i ≤ N → ∀ x,‖iteratedFDeriv ℝ i g x‖ ≤ G i)
    (A : Field n →L[ℝ] E) :
    (∀ z,ContDiff ℝ N (fun x=>Real.exp (m*f (x+A z))*g (x+A z))) ∧
    (∀ j,j ≤ N → ∀ x,AEStronglyMeasurable
      (fun z=>iteratedFDeriv ℝ j (fun y=>Real.exp (m*f (y+A z))*g (y+A z)) x)
      (fieldGaussian n)) ∧
    (∀ x,∃ s∈𝓝 x,∃ B : ℕ → Field n → ℝ,
      (∀ j,j ≤ N → Integrable (B j) (fieldGaussian n)) ∧
      ∀ j,j ≤ N → ∀ y∈s,∀ z,
        ‖iteratedFDeriv ℝ j (fun u=>Real.exp (m*f (u+A z))*g (u+A z)) y‖ ≤ B j z) := by
  let F : E → ℝ := fun x=>Real.exp (m*f x)*g x
  have hF : ContDiff ℝ N F := ((contDiff_const.mul hf).exp).mul hg
  refine ⟨fun z=>hF.comp (contDiff_id.add contDiff_const),?_,?_⟩
  · intro j hj x
    change AEStronglyMeasurable (fun z=>iteratedFDeriv ℝ j (fun y=>F (y+A z)) x) _
    simp_rw [iteratedFDeriv_comp_add_right]
    exact ((hF.continuous_iteratedFDeriv (by exact_mod_cast hj)).comp
      (continuous_const.add A.continuous)).aestronglyMeasurable
  · intro x
    let B : ℕ → Field n → ℝ := fun j z=>gaussianWeightedJetCoefficient m K G j*
      Real.exp (|m| * (|f x|+(L : ℝ)))*Real.exp (|m| *(L : ℝ)*‖A‖*‖z‖)
    refine ⟨Metric.ball x 1,Metric.ball_mem_nhds x (by norm_num),B,?_,?_⟩
    · intro j _
      exact (SYK.integrable_exp_mul_norm (ι := Fin n) (|m| *(L : ℝ)*‖A‖)).const_mul
        (gaussianWeightedJetCoefficient m K G j*Real.exp (|m| * (|f x|+(L : ℝ))))
    · intro j hj y hy z
      change ‖iteratedFDeriv ℝ j (fun u=>F (u+A z)) y‖ ≤ _
      rw [iteratedFDeriv_comp_add_right]
      have hb := norm_iteratedFDeriv_exp_mul_observable_le f g hf hg m K hK G hG
        hjets hgJets hj (y+A z)
      have hdom : Real.exp (m*f (y+A z)) ≤
          Real.exp (|m| * (|f x|+(L : ℝ)))*Real.exp (|m| *(L : ℝ)*‖A‖*‖z‖) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        calc
          _ ≤ |m| * |f (y+A z)| := by rw [← abs_mul];exact le_abs_self _
          _ ≤ |m| * (|f x|+(L : ℝ)*(1+‖A‖*‖z‖)) :=
            mul_le_mul_of_nonneg_left (gaussian_shift_abs_le f L hlip A x y z hy) (abs_nonneg _)
          _ = _ := by ring
      exact hb.trans (by
        dsimp only [B]
        have hh := mul_le_mul_of_nonneg_left hdom (gaussianWeightedJetCoefficient_nonneg m K hK G hG j)
        simpa only [mul_assoc] using hh)

theorem contDiff_gaussianWeightedShiftMoment {n : ℕ} (N : ℕ)
    (f g : E → ℝ) (hf : ContDiff ℝ N f) (hg : ContDiff ℝ N g)
    (L : ℝ≥0) (hlip : LipschitzWith L f) (m K : ℝ) (hK : 0 ≤ K)
    (G : ℕ → ℝ) (hG : ∀ i,0 ≤ G i)
    (hjets : ∀ i,1 ≤ i → i ≤ N → ∀ x,‖iteratedFDeriv ℝ i f x‖ ≤ K^i)
    (hgJets : ∀ i,i ≤ N → ∀ x,‖iteratedFDeriv ℝ i g x‖ ≤ G i)
    (A : Field n →L[ℝ] E) : ContDiff ℝ N (gaussianWeightedShiftMoment A m f g) := by
  obtain ⟨h₁,h₂,h₃⟩ := gaussianWeightedShiftMoment_smooth_inputs N f g hf hg L hlip m K hK
    G hG hjets hgJets A
  exact contDiff_integral_of_dominated_derivatives N (fieldGaussian n) _ h₁ h₂ h₃

theorem norm_iteratedFDeriv_gaussianWeightedShiftMoment_le {n : ℕ} (N j : ℕ)
    (f g : E → ℝ) (hf : ContDiff ℝ N f) (hg : ContDiff ℝ N g)
    (L : ℝ≥0) (hlip : LipschitzWith L f) (m K : ℝ) (hK : 0 ≤ K)
    (G : ℕ → ℝ) (hG : ∀ i,0 ≤ G i)
    (hjets : ∀ i,1 ≤ i → i ≤ N → ∀ x,‖iteratedFDeriv ℝ i f x‖ ≤ K^i)
    (hgJets : ∀ i,i ≤ N → ∀ x,‖iteratedFDeriv ℝ i g x‖ ≤ G i)
    (A : Field n →L[ℝ] E) (hj : j ≤ N) (x : E) :
    ‖iteratedFDeriv ℝ j (gaussianWeightedShiftMoment A m f g) x‖ ≤
      gaussianWeightedJetCoefficient m K G j*gaussianShiftPartition A m f x := by
  obtain ⟨h₁,h₂,h₃⟩ := gaussianWeightedShiftMoment_smooth_inputs N f g hf hg L hlip m K hK
    G hG hjets hgJets A
  rw [show iteratedFDeriv ℝ j (gaussianWeightedShiftMoment A m f g) x=
      ∫ z,iteratedFDeriv ℝ j (fun y=>Real.exp (m*f (y+A z))*g (y+A z)) x ∂fieldGaussian n from
    iteratedFDeriv_integral_of_dominated_derivatives N (fieldGaussian n) _ h₁ h₂ h₃ j hj x]
  have hb := norm_integral_le_of_norm_le
    ((integrable_gaussianShiftPartition_input f L hlip A m x).const_mul
      (gaussianWeightedJetCoefficient m K G j))
    (f := fun z=>iteratedFDeriv ℝ j (fun y=>Real.exp (m*f (y+A z))*g (y+A z)) x)
    (Eventually.of_forall fun z=>by
      change ‖iteratedFDeriv ℝ j (fun y=>(fun u=>Real.exp (m*f u)*g u) (y+A z)) x‖ ≤ _
      rw [iteratedFDeriv_comp_add_right (f := fun u=>Real.exp (m*f u)*g u) j (A z) x]
      exact norm_iteratedFDeriv_exp_mul_observable_le f g hf hg m K hK G hG hjets hgJets hj _)
  rw [integral_const_mul] at hb
  exact hb

end QuantitativePaper
