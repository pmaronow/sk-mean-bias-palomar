module
public import QuantitativePaper.VectorVarianceContinuity

@[expose] public section

/-! Genuine joint variance/field continuity of normalized Gaussian responses.
Centering by f(x) provides an integrable bound uniform in the field point. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 400000

def vectorCenteredStepMoment {n : ℕ} (f g : Field n→ℝ) (m : ℝ)
    (v : ℝ) (x : Field n) : ℝ :=
  ∫z,Real.exp (m*(f (fieldShift v x z)-f x))*g (fieldShift v x z) ∂fieldGaussian n

theorem vectorCenteredStepMoment_eq {n : ℕ} (f g : Field n→ℝ) (m v : ℝ)
    (x : Field n) :
    vectorCenteredStepMoment f g m v x=
      Real.exp (-m*f x)*(∫z,Real.exp (m*f (fieldShift v x z))*g (fieldShift v x z) ∂fieldGaussian n) := by
  rw [vectorCenteredStepMoment,←integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only
    rw [mul_sub,Real.exp_sub,div_eq_mul_inv,←Real.exp_neg]
    simp only [neg_mul]
    ring

theorem continuous_vectorCenteredStepMoment {n : ℕ} (f g : Field n→ℝ)
    (K : ℝ≥0) (hf : LipschitzWith K f) (hg : Continuous g) (R : ℝ)
    (hb : ∀x,|g x| ≤ R) (m : ℝ) :
    Continuous (fun p : ℝ×Field n => vectorCenteredStepMoment f g m p.1 p.2) := by
  have hR : 0 ≤ R := (abs_nonneg (g 0)).trans (hb 0)
  apply continuous_iff_continuousAt.mpr
  intro p
  let D := |m| * (K : ℝ)*Real.sqrt (p.1+1)
  let B := fun z : Field n => R*Real.exp (D*‖z‖)
  have hshift (z : Field n) : Continuous (fun w : ℝ×Field n => fieldShift w.1 w.2 z) := by
    unfold fieldShift
    fun_prop
  apply continuousAt_of_dominated (bound := B)
  · exact Eventually.of_forall fun w =>
      (((Real.continuous_exp.comp (continuous_const.mul
        ((hf.continuous.comp (by unfold fieldShift;fun_prop)).sub continuous_const))).mul
          (hg.comp (by unfold fieldShift;fun_prop))).aestronglyMeasurable)
  · have hv : ∀ᶠ w : ℝ×Field n in 𝓝 p,w.1<p.1+1 :=
      continuous_fst.continuousAt.eventually (Iio_mem_nhds (by linarith))
    filter_upwards [hv] with w hw
    exact Eventually.of_forall fun z => by
      have hdiff := hf.dist_le_mul (fieldShift w.1 w.2 z) w.2
      simp only [fieldShift,dist_eq_norm,add_sub_cancel_left,norm_smul,
        Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hdiff
      have hroot := Real.sqrt_le_sqrt hw.le
      have hexp : Real.exp (m*(f (fieldShift w.1 w.2 z)-f w.2)) ≤ Real.exp (D*‖z‖) := by
        apply Real.exp_le_exp.mpr
        calc
          _ ≤ |m| * |f (fieldShift w.1 w.2 z)-f w.2| := by rw [←abs_mul];exact le_abs_self _
          _ ≤ |m| * ((K : ℝ)*(Real.sqrt w.1*‖z‖)) :=
            mul_le_mul_of_nonneg_left hdiff (abs_nonneg m)
          _ ≤ D*‖z‖ := by
            dsimp only [D]
            have hh := mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hroot (mul_nonneg (abs_nonneg m) K.coe_nonneg))
              (norm_nonneg z)
            simpa only [mul_assoc] using hh
      rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
      exact (mul_le_mul_of_nonneg_left (hb _) (Real.exp_pos _).le).trans
        (by dsimp only [B];simpa only [mul_comm] using mul_le_mul_of_nonneg_right hexp hR)
  · exact (SYK.integrable_exp_mul_norm (ι := Fin n) D).const_mul R
  · exact Eventually.of_forall fun z =>
      ((Real.continuous_exp.comp (continuous_const.mul
        ((hf.continuous.comp (hshift z)).sub (hf.continuous.comp continuous_snd)))).mul
          (hg.comp (hshift z))).continuousAt

theorem vectorStepResponse_eq_centered_ratio {n : ℕ} (f g : Field n→ℝ)
    (K : ℝ≥0) (hf : LipschitzWith K f) (m v : ℝ) (x : Field n) :
    vectorStepResponse v m f g x=
      vectorCenteredStepMoment f g m v x/vectorCenteredStepMoment f (fun _ => 1) m v x := by
  rw [vectorCenteredStepMoment_eq,vectorCenteredStepMoment_eq]
  simp only [mul_one]
  unfold vectorStepResponse vectorStepWeight
  have he : (fun z => Real.exp (m*f (fieldShift v x z))/vectorStepPartition v m f x*g (fieldShift v x z))=
      fun z => (Real.exp (m*f (fieldShift v x z))*g (fieldShift v x z))/vectorStepPartition v m f x := by
    funext z
    ring
  rw [he,integral_div]
  change _ = (Real.exp (-m*f x)*_)/(Real.exp (-m*f x)*vectorStepPartition v m f x)
  field_simp [Real.exp_ne_zero, (vectorStepPartition_pos f K hf v m x).ne']

theorem continuous_vectorStepResponse_variance_field {n : ℕ} (f g : Field n→ℝ)
    (K : ℝ≥0) (hf : LipschitzWith K f) (hg : Continuous g) (R : ℝ)
    (hb : ∀x,|g x| ≤ R) (m : ℝ) :
    Continuous (fun p : ℝ×Field n => vectorStepResponse p.1 m f g p.2) := by
  have hnum := continuous_vectorCenteredStepMoment f g K hf hg R hb m
  have hden := continuous_vectorCenteredStepMoment f (fun _ => 1) K hf continuous_const 1
    (fun _ => by norm_num) m
  have hn (p : ℝ×Field n) : vectorCenteredStepMoment f (fun _ => 1) m p.1 p.2≠0 := by
    rw [vectorCenteredStepMoment_eq]
    simp only [mul_one]
    exact mul_ne_zero (Real.exp_ne_zero _) (vectorStepPartition_pos f K hf p.1 m p.2).ne'
  have hh := hnum.div hden hn
  have he : (fun p : ℝ×Field n => vectorStepResponse p.1 m f g p.2)=
      fun p => vectorCenteredStepMoment f g m p.1 p.2/vectorCenteredStepMoment f (fun _ => 1) m p.1 p.2 :=
    funext fun p => vectorStepResponse_eq_centered_ratio f g K hf m p.1 p.2
  rw [he]
  exact hh

end QuantitativePaper
