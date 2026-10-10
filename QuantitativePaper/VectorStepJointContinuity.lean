module
public import QuantitativePaper.VectorResponseContinuity
public import QuantitativePaper.VectorFiniteCells

@[expose] public section

/-! Genuine joint variance/field continuity of Gaussian Cole--Hopf values,
including zero variance and zero mass. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 400000

theorem continuous_vectorColeHopfStep_variance_field {n : ℕ} (f : Field n→ℝ)
    (K : ℝ≥0) (hf : LipschitzWith K f) (m : ℝ) :
    Continuous (fun p : ℝ×Field n => vectorColeHopfStep p.1 m f p.2) := by
  by_cases hm : m=0
  · subst m
    simp only [vectorColeHopfStep,ite_true]
    apply continuous_iff_continuousAt.mpr
    intro p
    let B := fun z : Field n => |f p.2|+(K : ℝ)+((K : ℝ)*Real.sqrt (p.1+1))*‖z‖
    have hshift (z : Field n) : Continuous (fun w : ℝ×Field n => fieldShift w.1 w.2 z) := by
      unfold fieldShift
      fun_prop
    apply continuousAt_of_dominated (bound := B)
    · exact Eventually.of_forall fun w => (hf.continuous.comp (by unfold fieldShift;fun_prop)).aestronglyMeasurable
    · have hv : ∀ᶠ w : ℝ×Field n in 𝓝 p,w.1<p.1+1 :=
        continuous_fst.continuousAt.eventually (Iio_mem_nhds (by linarith))
      have hx : ∀ᶠ w : ℝ×Field n in 𝓝 p,dist w.2 p.2<1 :=
        continuous_snd.continuousAt.eventually (Metric.ball_mem_nhds p.2 (by norm_num))
      filter_upwards [hv,hx] with w hw hwx
      exact Eventually.of_forall fun z => by
        have h₀ := abs_fieldShift_lipschitz f K hf w.1 w.2 z
        have h₁ := hf.dist_le_mul w.2 p.2
        rw [Real.dist_eq] at h₁
        have hf₀ : |f w.2| ≤ |f p.2|+(K : ℝ) := by
          have ha := abs_add_le (f p.2) (f w.2-f p.2)
          rw [add_sub_cancel] at ha
          have hh := mul_le_mul_of_nonneg_left hwx.le K.coe_nonneg
          linarith
        have hroot := Real.sqrt_le_sqrt hw.le
        have h₂ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hroot K.coe_nonneg) (norm_nonneg z)
        rw [Real.norm_eq_abs]
        dsimp only [B]
        exact h₀.trans (add_le_add hf₀ h₂)
    · exact ((integrable_const |f p.2|).add (integrable_const (K : ℝ))).add
        ((integrable_fieldGaussian_norm n).const_mul ((K : ℝ)*Real.sqrt (p.1+1)))
    · exact Eventually.of_forall fun z => (hf.continuous.comp (hshift z)).continuousAt
  · have hM := continuous_vectorCenteredStepMoment f (fun _ => 1) K hf continuous_const 1
      (fun _ => by norm_num) m
    have hpos (p : ℝ×Field n) : 0 < vectorCenteredStepMoment f (fun _ => 1) m p.1 p.2 := by
      rw [vectorCenteredStepMoment_eq]
      simp only [mul_one]
      exact mul_pos (Real.exp_pos _) (vectorStepPartition_pos f K hf p.1 m p.2)
    have hh := (hf.continuous.comp continuous_snd).add ((hM.log (fun p => (hpos p).ne')).div_const m)
    have he : (fun p : ℝ×Field n => vectorColeHopfStep p.1 m f p.2)=
        fun p => f p.2+Real.log (vectorCenteredStepMoment f (fun _ => 1) m p.1 p.2)/m := by
      funext p
      rw [vectorCenteredStepMoment_eq]
      simp only [mul_one]
      change vectorColeHopfStep p.1 m f p.2=
        f p.2+Real.log (Real.exp (-m*f p.2)*vectorStepPartition p.1 m f p.2)/m
      rw [Real.log_mul (Real.exp_ne_zero _) (vectorStepPartition_pos f K hf p.1 m p.2).ne',Real.log_exp]
      simp only [vectorColeHopfStep,ite_eq_right hm]
      change _=f p.2+(-m*f p.2+Real.log (vectorStepPartition p.1 m f p.2))/m
      field_simp
      ring
    rw [he]
    exact hh

theorem continuous_vectorFiniteCellPotential_time_field {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n×ℝ) (i : ℕ) :
    Continuous (fun z : ℝ×Field n => vectorFiniteCellPotential s β t p i z.1 z.2) := by
  have hh := continuous_vectorColeHopfStep_variance_field (vectorRecursion s β t p (k+1-i)) _
    (vectorRecursion_lipschitz s β t p (k+1-i)) (s.m i)
  exact hh.comp (by fun_prop : Continuous (fun z : ℝ×Field n =>
    (((1-t)*β^2*(s.q (i+1)-z.1)),z.2)))

end QuantitativePaper
