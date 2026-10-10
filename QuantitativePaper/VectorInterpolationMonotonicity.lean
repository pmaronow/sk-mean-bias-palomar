module
public import QuantitativePaper.VectorGridInterpolationIntegral
public import QuantitativePaper.VectorInterpolationMinimumIntegral

@[expose] public section

/-! Positivity of the actual replica defect makes both the physical
fixed-profile interpolation and its attained compact minimum decrease. -/
noncomputable section
open Set Filter MeasureTheory
open scoped NNReal Topology
namespace QuantitativePaper
open FourPapersCommon
variable {n : ℕ}
set_option maxHeartbeats 1600000

theorem vectorMeasureFunctional_interpolation_antitone (hn : 0<n)
    (μ : Paper.ParisiMeasure) (β s : ℝ) (hs : s∈Ioo (0:ℝ) 1)
    (hμ : μ∈scalarFloor s) (hβ : β≠0) :
    AntitoneOn (fun t=>vectorMeasureFunctional n μ β t s) (Icc (0:ℝ) 1) := by
  intro r hr u hu hru
  have hlim:=(tendsto_vectorMeasureFunctional_grid hn μ β u s hu.2).sub
    (tendsto_vectorMeasureFunctional_grid hn μ β r s hr.2)
  apply sub_nonpos.mp
  apply le_of_tendsto hlim
  exact .of_forall fun j=>by
    rw [(vectorMeasureFunctional_grid_interpolation_integral
      hn μ j β s hs hμ hβ r u hr hu hru).2]
    apply mul_nonpos_of_nonpos_of_nonneg
    · exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg β)) (by norm_num)
    · exact intervalIntegral.integral_nonneg_of_forall hru fun t=>
        (vectorInterpolationTimeDefect_bounds hn
          (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) s β t hs.2.le hβ).1

theorem vectorInterpolationMinimum_antitone (n : ℕ) (hn : 0<n)
    (β s : ℝ) (hs : s∈Ioo (0:ℝ) 1) (hβ : β≠0) :
    AntitoneOn (vectorInterpolationMinimum n β s) (Icc (0:ℝ) 1) := by
  intro r hr u hu hru
  obtain ⟨μ,hμ,he,_⟩:=compactMinimumValue_attained (scalarFloor s)
    (isCompact_scalarFloor s) (scalarFloor_nonempty s hs.2.le)
    (fun t μ=>vectorMeasureFunctional n μ β t s) r
    (continuous_vectorMeasureFunctional n hn β r s hr.2).continuousOn
  obtain ⟨ν,hν,_,hle⟩:=compactMinimumValue_attained (scalarFloor s)
    (isCompact_scalarFloor s) (scalarFloor_nonempty s hs.2.le)
    (fun t μ=>vectorMeasureFunctional n μ β t s) u
    (continuous_vectorMeasureFunctional n hn β u s hu.2).continuousOn
  calc
    vectorInterpolationMinimum n β s u≤vectorMeasureFunctional n μ β u s:=hle μ hμ
    _≤vectorMeasureFunctional n μ β r s:=
      vectorMeasureFunctional_interpolation_antitone hn μ β s hs hμ hβ hr hu hru
    _=vectorInterpolationMinimum n β s r:=he

theorem optimizedVectorInterpolationDefect_bounds (n : ℕ) (hn : 0<n)
    (β s : ℝ) (hs : s∈Ioo (0:ℝ) 1) (hβ : β≠0) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) :
    0≤optimizedVectorInterpolationDefect n β s t ∧
      optimizedVectorInterpolationDefect n β s t≤4*(1-s) := by
  have hnhds:=Icc_mem_nhds ht.1 ht.2
  have hd:= (vectorInterpolationMinimum_antitone n hn β s hs hβ).derivWithin_nonpos (x:=t)
  rw [derivWithin_of_mem_nhds hnhds] at hd
  have hb:=norm_deriv_le_of_lipschitzOn hnhds
    (vectorInterpolationMinimum_lipschitz n hn β s hs hβ)
  change ‖deriv (vectorInterpolationMinimum n β s) t‖≤β^2*(1-s) at hb
  rw [Real.norm_eq_abs] at hb
  have hb0:= (abs_le.mp hb).1
  have hbp : 0<β^2:=sq_pos_of_ne_zero hβ
  unfold optimizedVectorInterpolationDefect
  constructor
  · exact div_nonneg (mul_nonneg_of_nonpos_of_nonpos (by norm_num) hd) (sq_nonneg β)
  · apply (div_le_iff₀ hbp).mpr
    nlinarith

theorem constrainedParisiValue_sub_completedFractionalPressure_nonneg
    (n : ℕ) (hn : 0<n) (β s : ℝ) (hs : s∈Ioo (0:ℝ) 1) (hβ : β≠0) :
    0≤constrainedParisiValue β s-completedFractionalPressure n β s := by
  rw [←vectorInterpolationMinimum_endpoint_gap n hn β s hβ hs.2.le hs.1.ne']
  exact sub_nonneg.mpr (vectorInterpolationMinimum_antitone n hn β s hs hβ
    (by norm_num) (by norm_num) (by norm_num))

end QuantitativePaper
