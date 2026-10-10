module
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-! Genuine dominated convergence for exponentially tilted bounded
observables, using a vanishing uniform error in their actual potentials. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace FourPapersCommon
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem tendsto_integral_exp_mul_of_uniform_error
    (X : Ω→ℝ) (Xj Yj : ℕ→Ω→ℝ) (Y : Ω→ℝ) (a C : ℝ)
    (hC : 0≤C) (ε : ℕ→ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hXj : ∀ j,Measurable (Xj j)) (hYj : ∀ j,Measurable (Yj j))
    (hX : Integrable (fun ω=>Real.exp (a*X ω)) P)
    (hbound : ∀ j ω,|Xj j ω-X ω|≤ε j)
    (hYbound : ∀ j ω,‖Yj j ω‖≤C)
    (hY : ∀ᵐω ∂P,Tendsto (fun j=>Yj j ω) atTop (𝓝 (Y ω))) :
    Tendsto (fun j=>∫ω,Real.exp (a*Xj j ω)*Yj j ω ∂P) atTop
      (𝓝 (∫ω,Real.exp (a*X ω)*Y ω ∂P)) := by
  have hpot (ω : Ω) : Tendsto (fun j=>Xj j ω) atTop (𝓝 (X ω)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _=>dist_nonneg)
      (fun j=>by simpa only [Real.dist_eq] using hbound j ω) hε
  let B : Ω→ℝ := fun ω=>(Real.exp |a| * C)*Real.exp (a*X ω)
  apply tendsto_integral_filter_of_dominated_convergence B
    (.of_forall (fun j=>( (Real.measurable_exp.comp (measurable_const.mul (hXj j))).mul
      (hYj j)).aestronglyMeasurable))
    ?_ (hX.const_mul _) ?_
  · filter_upwards [hε.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1))] with j hj
    exact .of_forall (fun ω=>by
      have hp : a*Xj j ω≤|a|+a*X ω := by
        have h : a*(Xj j ω-X ω)≤|a| * ε j := by
          calc
            _≤|a*(Xj j ω-X ω)| := le_abs_self _
            _=|a| * |Xj j ω-X ω| := abs_mul _ _
            _≤|a| * ε j := mul_le_mul_of_nonneg_left (hbound j ω) (abs_nonneg a)
        have h' := mul_le_mul_of_nonneg_left hj.le (abs_nonneg a)
        linarith
      simp only [Pi.mul_apply,Function.comp_apply]
      rw [norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]
      calc
        _≤Real.exp (a*Xj j ω)*C := mul_le_mul_of_nonneg_left (hYbound j ω) (Real.exp_pos _).le
        _≤Real.exp (|a|+a*X ω)*C := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hp) hC
        _=B ω := by rw [Real.exp_add];dsimp only [B];ring)
  · filter_upwards [hY] with ω hω
    have hp : Tendsto (fun j=>Real.exp (a*Xj j ω)) atTop (𝓝 (Real.exp (a*X ω))) := by
      simpa only [Function.comp_def] using
        (Real.continuous_exp.tendsto (a*X ω)).comp ((hpot ω).const_mul a)
    simpa only [Pi.mul_apply,Function.comp_apply] using hp.mul hω

end FourPapersCommon
