module
public import QuantitativePaper.VectorColeHopfSignedMass
public import QuantitativePaper.VectorMassRegularity

@[expose] public section

/-! Order, additive constants, and compact-mass norm barriers for the literal
Gaussian transform. These estimates remain valid for negative masses. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal
namespace QuantitativePaper
set_option maxHeartbeats 1600000

theorem vectorColeHopfStep_add_const_all_mass {n : ℕ} (f : Field n→ℝ)
    (K : ℝ≥0) (hf : LipschitzWith K f) (c m C : ℝ) (x : Field n) :
    vectorColeHopfStep c m (fun y=>C+f y) x=C+vectorColeHopfStep c m f x := by
  by_cases hm : m=0
  · subst m
    simp only [vectorColeHopfStep,ite_true]
    rw [integral_add (integrable_const _) (integrable_vectorStep_input f K hf c x)]
    simp
  · have hZ : vectorStepPartition c m (fun y=>C+f y) x=
        Real.exp (m*C)*vectorStepPartition c m f x := by
      unfold vectorStepPartition
      simp_rw [mul_add,Real.exp_add]
      rw [integral_const_mul]
    simp only [vectorColeHopfStep,hm,ite_false,hZ]
    rw [Real.log_mul (Real.exp_ne_zero _) (vectorStepPartition_pos f K hf c m x).ne',Real.log_exp]
    field_simp

private theorem vectorColeHopfStep_mono_nonneg {n : ℕ} (f g : Field n→ℝ)
    (K L : ℝ≥0) (hf : LipschitzWith K f) (hg : LipschitzWith L g)
    (c m : ℝ) (hm : 0 ≤ m) (hfg : ∀x,f x≤g x) (x : Field n) :
    vectorColeHopfStep c m f x≤vectorColeHopfStep c m g x := by
  by_cases hm0 : m=0
  · subst m
    simp only [vectorColeHopfStep,ite_true]
    exact integral_mono (integrable_vectorStep_input f K hf c x)
      (integrable_vectorStep_input g L hg c x) (fun z=>hfg _)
  · have hp : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
    have hZ : vectorStepPartition c m f x≤vectorStepPartition c m g x :=
      integral_mono (integrable_exp_vectorStep f K hf c m x)
        (integrable_exp_vectorStep g L hg c m x)
        (fun z=>Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hfg _) hm))
    simp only [vectorColeHopfStep,hm0,ite_false]
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (vectorStepPartition_pos f K hf c m x) hZ) hm

theorem vectorColeHopfStep_mono_all_mass {n : ℕ} (f g : Field n→ℝ)
    (K L : ℝ≥0) (hf : LipschitzWith K f) (hg : LipschitzWith L g)
    (c m : ℝ) (hfg : ∀x,f x≤g x) (x : Field n) :
    vectorColeHopfStep c m f x≤vectorColeHopfStep c m g x := by
  by_cases hm : 0 ≤ m
  · exact vectorColeHopfStep_mono_nonneg f g K L hf hg c m hm hfg x
  · rw [vectorColeHopfStep_mass_reflection c m f,vectorColeHopfStep_mass_reflection c m g]
    exact neg_le_neg (vectorColeHopfStep_mono_nonneg (fun y=>-g y) (fun y=>-f y)
      L K hg.neg hf.neg c (-m) (by linarith) (fun y=>neg_le_neg (hfg y)) x)

theorem vectorColeHopfStep_norm_barrier {n : ℕ} (K : ℝ≥0) (c M : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀m∈Icc (-M) M, ∀f : Field n→ℝ, LipschitzWith K f →
      |vectorColeHopfStep c m f 0|≤|f 0|+C := by
  let g : Field n→ℝ := fun x=>(K:ℝ)*‖x‖
  have hg : LipschitzWith K g := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    have hh := (lipschitzWith_one_norm : LipschitzWith 1 (norm : Field n→ℝ)).dist_le_mul x y
    simp only [Real.dist_eq,NNReal.coe_one,one_mul] at hh
    rw [Real.dist_eq,show g x-g y=(K:ℝ)*(‖x‖-‖y‖) by dsimp only [g]; ring,
      abs_mul,abs_of_nonneg K.coe_nonneg]
    exact mul_le_mul_of_nonneg_left hh K.coe_nonneg
  have hc : Continuous (fun m=>vectorColeHopfStep c m g 0) :=
    continuous_iff_continuousAt.mpr fun m=>(analyticAt_vectorColeHopfStep_mass g K hg c 0 m).continuousAt
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro m hm f hf
  have hupper : ∀x,f x≤f 0+g x := by
    intro x
    have hh := hf.dist_le_mul x 0
    rw [Real.dist_eq,dist_zero_right] at hh
    dsimp only [g]
    linarith [(abs_le.mp hh).2]
  have hlower : ∀x,f 0-g x≤f x := by
    intro x
    have hh := hf.dist_le_mul x 0
    rw [Real.dist_eq,dist_zero_right] at hh
    dsimp only [g]
    linarith [(abs_le.mp hh).1]
  have hu := vectorColeHopfStep_mono_all_mass f (fun x=>f 0+g x) K K hf
    (by rw [lipschitzWith_iff_dist_le_mul]; intro x y
        simpa [dist_eq_norm] using hg.dist_le_mul x y) c m hupper 0
  have hl := vectorColeHopfStep_mono_all_mass (fun x=>f 0+ -g x) f K K
    (by rw [lipschitzWith_iff_dist_le_mul]; intro x y
        simpa [dist_eq_norm] using hg.neg.dist_le_mul x y) hf c m (fun x=>by simpa only [sub_eq_add_neg] using hlower x) 0
  rw [vectorColeHopfStep_add_const_all_mass g K hg] at hu
  rw [vectorColeHopfStep_add_const_all_mass (fun x=>-g x) K hg.neg] at hl
  have hgm := hC m hm
  have hgn := hC (-m) (by constructor <;> linarith [hm.1,hm.2])
  rw [vectorColeHopfStep_mass_reflection c m (fun x=>-g x)] at hl
  simp only [neg_neg] at hl
  rw [Real.norm_eq_abs] at hgm hgn
  apply abs_le.mpr
  constructor
  · linarith [(abs_le.mp hgn).2,neg_abs_le (f 0),le_max_left C 0]
  · linarith [(abs_le.mp hgm).2,le_abs_self (f 0),le_max_left C 0]

end QuantitativePaper
