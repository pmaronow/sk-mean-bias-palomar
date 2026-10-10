module
public import QuantitativeFollowup.FiniteThirdDerivativeBarrier
public import FRSB.BackwardsLower
public import FRSB.ParisiGridTopology
public import FRSB.GridMeasureIdentification
public import FRSB.SupportDensityFormula
public import FRSB.ParisiMinimizerGeometry
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

/-! Actual strict fourth derivative at the origin, and hence strictly positive
root density for the actual zero-field minimizing Parisi measure. -/
noncomputable section
open Set Filter MeasureTheory Paper FRSB
open scoped Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 400000

theorem finiteScheme_thirdDerivativeBarrier_actual {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β≠0) (t x : ℝ) (ht : t∈Icc (0:ℝ) 1) (hx : 0≤x) :
    thirdDerivativeBarrier (β^2*(1-t),x)≤-backwardD β (parisiSchemeMeasure s) 3 (t,x) := by
  by_cases ht1 : t=1
  · subst t
    simpa only [sub_self,mul_zero,backwardD_three_terminal,neg_mul,neg_neg] using
      thirdDerivativeBarrier_terminal_le hx
  obtain ⟨p,hp,hcell,hq⟩:=exists_parisiFinite_right_cell s
    (t:=t) ⟨ht.1,lt_of_le_of_ne ht.2 ht1⟩
  have hh:=finiteScheme_thirdDerivativeBarrier_le s β hβ p hp
    (backwardClock β t) (backwardClock_cell_mem s β ⟨hcell.1,hcell.2.le⟩) x hx
  change thirdDerivativeBarrier (backwardClock β t,x)≤
    -backwardD β (parisiSchemeMeasure s) 3 (backwardTime β (backwardClock β t),x) at hh
  rw [backwardTime_clock β hβ t] at hh
  exact hh

theorem thirdDerivativeBarrier_actual (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (t x : ℝ) (ht : t∈Icc (0:ℝ) 1) (hx : 0≤x) :
    thirdDerivativeBarrier (β^2*(1-t),x)≤-backwardD β μ 3 (t,x) := by
  have hh:=(tendsto_backwardD_of_weak β 2 μ (parisiGridMeasure μ)
    (tendsto_parisiGridMeasure μ) (t,x)).neg
  apply ge_of_tendsto hh
  exact .of_forall fun j=>by
    simpa only [parisiSchemeMeasure_grid_eq] using
      finiteScheme_thirdDerivativeBarrier_actual (parisiGridRSBScheme μ j) β hβ t x ht hx

theorem parisi_fourth_origin_strict (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
    backwardD β μ 4 (t,0)≤-2*Real.exp (-4)*Real.exp (-4*(β^2*(1-t))) := by
  let τ:=β^2*(1-t)
  let f:ℝ→ℝ:=fun x=>-backwardD β μ 3 (t,x)-thirdDerivativeBarrier (τ,x)
  have hf0 : f 0=0 := by
    have ho:=backwardD_reflect β μ t ht 3 0
    simp only [neg_zero] at ho
    norm_num at ho
    dsimp only [f]
    rw [thirdDerivativeBarrier_zero]
    linarith
  have hder : HasDerivAt f
      (-backwardD β μ 4 (t,0)-2*Real.exp (-4)*Real.exp (-4*τ)) 0 := by
    have hh:=(hasDerivAt_backwardD β μ 3 t 0 ht).neg.sub
      (hasDerivAt_thirdDerivativeBarrier_space τ 0)
    convert! hh using 1 <;>
      simp only [f,thirdDerivativeBarrierX,pow_two,mul_zero,sub_zero,neg_zero,Real.exp_zero,mul_one]
  have hlim:=hder.tendsto_slope_zero_right
  have hnn : 0≤-backwardD β μ 4 (t,0)-2*Real.exp (-4)*Real.exp (-4*τ) := by
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin (s:=Ioi (0:ℝ)) (a:=0)] with x hx
    have hp : 0≤f x := sub_nonneg.mpr (thirdDerivativeBarrier_actual β hβ μ t x ht hx.le)
    simpa only [zero_add,hf0,sub_zero,smul_eq_mul] using mul_nonneg (inv_nonneg.mpr hx.le) hp
  dsimp only [τ] at hnn
  linarith

theorem parisi_fourth_origin_neg (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : backwardD β μ 4 (t,0)<0 := by
  have hh:=parisi_fourth_origin_strict β hβ μ t ht
  have hp : 0<2*Real.exp (-4)*Real.exp (-4*(β^2*(1-t))) := by positivity
  linarith

theorem scalar_minimizer_root_density_pos (β : ℝ) (hβ : 0<β)
    (μ : Paper.ParisiMeasure) (hmin : IsParisiMinimizer β 0 μ)
    (q : ℝ) (hq : q∈Ioo (0:ℝ) 1) (hsupp : parisiSupport μ=Icc (0:ℝ) q) :
    0<parisiSmoothDensity β μ q 0 := by
  rw [parisiSmoothDensity_initial_of_support_interval β hβ μ hmin q hq.1 hq.2.le hsupp]
  have hd : parisiSpatialJet β μ 4 0 0<0 := by
    simpa only [backwardD_eq_spatialJet] using parisi_fourth_origin_neg β hβ.ne' μ 0 ⟨le_rfl,by norm_num⟩
  exact div_pos (mul_pos (pow_pos hβ 5) (sq_pos_of_ne_zero (ne_of_lt hd))) (by norm_num)

end QuantitativeFollowup
