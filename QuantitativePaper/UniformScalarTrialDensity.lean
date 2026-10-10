module
public import QuantitativeFollowup.ClippedTrialMeasureDensity
public import QuantitativeFollowup.StieltjesLocalCongruence
public import QuantitativeFollowup.StieltjesLipschitz
public import Mathlib.Topology.MetricSpace.Lipschitz

@[expose] public section

/-! Genuine local measure domination from the uniform root Lipschitz bound.
The clipped probability retains its prescribed root atom; this theorem
controls its actual energy measure on the open positive root interval. -/
noncomputable section
open Set MeasureTheory Paper QuantitativeFollowup
open scoped ENNReal NNReal
namespace QuantitativePaper
set_option maxHeartbeats 1200000

theorem stieltjes_measure_le_volume_of_lipschitz (f : StieltjesFunction ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hLip : ∀x y,‖f y-f x‖ ≤ C*‖y-x‖) :
    f.measure ≤ ENNReal.ofReal C • volume := by
  let c : ℝ≥0 := ⟨C,hC⟩
  have hfLip : LipschitzWith c f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (f x) (f y) ≤ C*dist x y
    simpa only [c,NNReal.coe_mk,Real.dist_eq,Real.norm_eq_abs,abs_sub_comm] using hLip x y
  let g : StieltjesFunction ℝ :=
    { toFun := fun x=>C*x-f x
      mono' := by
        intro x y hxy
        have hh := (le_abs_self (f y-f x)).trans (hLip x y)
        rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hxy)] at hh
        nlinarith
      right_continuous' := fun x=>
        ((continuous_const.mul continuous_id).sub hfLip.continuous).continuousWithinAt }
  have he : f+g=c • StieltjesFunction.id := by
    ext x
    change f x+(C*x-f x)=C*x
    ring
  have hm : f.measure+g.measure=ENNReal.ofReal C • volume := by
    rw [←StieltjesFunction.measure_add,he,StieltjesFunction.measure_smul,
      ←Real.volume_eq_stieltjes_id]
    ext S
    change (c:ℝ≥0∞)*volume S=ENNReal.ofReal C*volume S
    rw [←ENNReal.ofReal_coe_nnreal (p:=c)]
    rfl
  rw [←hm]
  exact Measure.le_add_right le_rfl

theorem stieltjes_local_measure_le_volume_of_lipschitz (f : StieltjesFunction ℝ)
    (a b C : ℝ) (hab : a ≤ b) (hC : 0 ≤ C)
    (hLip : ∀x∈Icc a b,∀y∈Icc a b,‖f y-f x‖ ≤ C*‖y-x‖) :
    f.measure.restrict (Ioo a b) ≤ ENNReal.ofReal C • volume.restrict (Ioo a b) := by
  let P := projIcc a b hab
  have hp : LipschitzWith 1 P := LipschitzWith.projIcc hab
  have hpl (x y : ℝ) : ‖(P y:ℝ)-(P x:ℝ)‖ ≤ ‖y-x‖ := by
    simpa only [Real.dist_eq,Subtype.dist_eq,NNReal.coe_one,one_mul,
      Real.norm_eq_abs] using hp.dist_le_mul y x
  have hfLip : LipschitzWith (⟨C,hC⟩:ℝ≥0) (fun x=>f (P x)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (f (P x)) (f (P y)) ≤ C*dist x y
    have hh := (hLip (P x) (P x).property (P y) (P y).property).trans
      (mul_le_mul_of_nonneg_left (hpl x y) hC)
    simpa only [NNReal.coe_mk,Real.dist_eq,Real.norm_eq_abs,abs_sub_comm] using hh
  let g : StieltjesFunction ℝ :=
    { toFun := fun x=>f (P x)
      mono' := fun x y hxy=>f.mono (monotone_projIcc hab hxy)
      right_continuous' := fun x=>hfLip.continuous.continuousWithinAt }
  have he : f.measure.restrict (Ioo a b)=g.measure.restrict (Ioo a b) := by
    apply stieltjes_restrict_Ioo_congr
    intro x hx
    change f x=f (projIcc a b hab x)
    rw [projIcc_of_mem hab hx]
  rw [he,←Measure.restrict_smul]
  apply Measure.restrict_mono_measure
  apply stieltjes_measure_le_volume_of_lipschitz g C hC
  intro x y
  have hh := hfLip.dist_le_mul y x
  change dist (f (P y)) (f (P x)) ≤ C*dist y x at hh
  simpa only [g,Real.dist_eq,Real.norm_eq_abs] using hh

theorem scalarClippedTrial_uniform_local_energy_density
    (β lam T C : ℝ) (hβ : 0<β) (hlam : lam∈Icc (0:ℝ) β)
    (hT : T∈Ioc (0:ℝ) 1) (hC : 0≤C) (μ : Paper.ParisiMeasure)
    (hLip : ∀x∈Icc (0:ℝ) T,∀y∈Icc (0:ℝ) T,
      ‖β*parisiCDF μ y-β*parisiCDF μ x‖ ≤ C*‖y-x‖) :
    (ENNReal.ofReal β •
      (parisiCDFPrimitive (scalarClippedTrialMeasure (lam/β)
        ⟨div_nonneg hlam.1 hβ.le,(div_le_one hβ).mpr hlam.2⟩ μ)).measure).restrict (Ioo (0:ℝ) T) ≤
      ENNReal.ofReal C • volume.restrict (Ioo (0:ℝ) T) := by
  rw [scalarClippedTrialMeasure_energy_density β lam hβ hlam μ (Ioo (0:ℝ) T)
    measurableSet_Ioo (fun x hx=>⟨hx.1.le,hx.2.le.trans hT.2⟩) (by simp)]
  apply stieltjes_local_measure_le_volume_of_lipschitz _ 0 T C hT.1.le hC
  intro x hx y hy
  change ‖max lam (β*parisiCDF μ y)-max lam (β*parisiCDF μ x)‖ ≤ _
  have hm : ‖max lam (β*parisiCDF μ y)-max lam (β*parisiCDF μ x)‖ ≤
      ‖β*parisiCDF μ y-β*parisiCDF μ x‖ := by
    simpa only [Real.norm_eq_abs,max_comm lam] using
      abs_max_sub_max_le_abs (β*parisiCDF μ y) (β*parisiCDF μ x) lam
  exact hm.trans (hLip x hx y hy)

end QuantitativePaper
