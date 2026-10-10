module
public import QuantitativePaper.UniformQuantitativeParisi
public import QuantitativeFollowup.RootProbabilityQuantile

@[expose] public section

/-! The small-interval moving estimate is the genuine score-cutoff bound
in native energy units. The optimized defect is used only at honest
minimum differentiability points, hence almost everywhere. -/
noncomputable section
open Set Filter MeasureTheory Paper QuantitativePaper FourPapersCommon
namespace QuantitativeFollowup
set_option maxHeartbeats 2000000
variable {n : ℕ}

def smallIntervalDefect (n : ℕ) (β lam rho : ℝ) : ℝ :=
  β*optimizedVectorInterpolationDefect n β (lam/β) (1-rho)

theorem smallInterval_half_normalization (x β : ℝ) (hx : 0<x) (hβ : 0<β) :
    β*(x*β^2)^(-(1/2:ℝ))=x^(-(1/2:ℝ)) := by
  rw [Real.mul_rpow hx.le (sq_nonneg β)]
  have hp : (β^2)^(-(1/2:ℝ))=β⁻¹ := by
    rw [←Real.rpow_two,←Real.rpow_mul hβ.le]
    norm_num
    rw [Real.rpow_neg_one]
  rw [hp]
  field_simp

theorem smallInterval_profile_moving (hn : 0<n) (μ : Paper.ParisiMeasure)
    (β lam rho : ℝ) (hβ : 0<β) (hrho : rho∈Ioc (0:ℝ) 1)
    (hs : lam/β∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor (lam/β))
    (hmin : ∀ν∈scalarFloor (lam/β),vectorMeasureFunctional n μ β (1-rho) (lam/β) ≤ 
      vectorMeasureFunctional n ν β (1-rho) (lam/β)) :
    β*vectorInterpolationDefect (n:=n) μ (lam/β) β (1-rho) (by linarith [hrho.1])  ≤ 
      movingCutoffDefectConstant*((n:ℝ)*rho)^(-(1/2:ℝ)) := by
  have ht : 1-rho<1:=by linarith [hrho.1]
  have hb:=vector_moving_cutoff hn μ (lam/β) β (1-rho) hβ.ne' ht hs hμ hmin
  have hm : (n:ℝ)*((1-(1-rho))*β^2)=((n:ℝ)*rho)*β^2:=by ring
  rw [hm] at hb
  have hrate:=hb.trans (mul_le_mul_of_nonneg_left
    ((min_le_right _ _).trans (min_le_left _ _)) movingCutoffDefectConstant_pos.le)
  have hh:=mul_le_mul_of_nonneg_left hrate hβ.le
  calc
    _ ≤ β*(movingCutoffDefectConstant*((n:ℝ)*rho*β^2)^(-(1/2:ℝ))):=hh
    _=movingCutoffDefectConstant*((n:ℝ)*rho)^(-(1/2:ℝ)):=by
      rw [mul_left_comm β,smallInterval_half_normalization _ β
        (mul_pos (Nat.cast_pos.mpr hn) hrho.1) hβ]

theorem smallIntervalDefect_moving (hn : 0<n) (β lam rho : ℝ) (hβ : 0<β)
    (hrho : rho∈Ioo (0:ℝ) 1) (hs : lam/β∈Ioo (0:ℝ) 1)
    (hf : DifferentiableAt ℝ (vectorInterpolationMinimum n β (lam/β)) (1-rho)) :
    smallIntervalDefect n β lam rho  ≤ 
      movingCutoffDefectConstant*((n:ℝ)*rho)^(-(1/2:ℝ)) := by
  let μ:=vectorMeasureMinimizer n hn β (1-rho) (lam/β) (by linarith [hrho.1]) hs.2.le
  have hμ:=vectorMeasureMinimizer_mem n hn β (1-rho) (lam/β) (by linarith [hrho.1]) hs.2.le
  have hmin:=vectorMeasureMinimizer_minimal n hn β (1-rho) (lam/β) (by linarith [hrho.1]) hs.2.le
  unfold smallIntervalDefect
  rw [optimizedVectorInterpolationDefect_eq_of_minimizer hn μ β (lam/β) hs hμ hβ.ne'
    (1-rho) ⟨by linarith [hrho.2],by linarith [hrho.1]⟩ hmin hf]
  exact smallInterval_profile_moving hn μ β lam rho hβ ⟨hrho.1,hrho.2.le⟩ hs hμ hmin

end QuantitativeFollowup
