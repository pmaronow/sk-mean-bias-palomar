module
public import HexagonPaper.VariableScalarClockState
public import HexagonPaper.VariableScalarClockPDE
public import HexagonPaper.VariableScalarClockPrimitiveSubstitution

@[expose] public section

/-! Actual drift substitution for the native Picard state, with every
arbitrary-profile atom retained in its CDF. -/
noncomputable section
open Set Filter MeasureTheory Paper FRSB
open scoped Topology
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

def scalarCoefficientStateFromNoise (c : ℝ→ℝ)
    (hint : IntervalIntegrable c volume 0 1)
    (hpos : ∀r∈Ioo (0:ℝ) 1,0<c r) (μ : Paper.ParisiMeasure) (Z : C(Paper.Overlap,ℝ)) :
    C(Paper.Overlap,ℝ) :=
  scalarClockStateFromNoise (scalarCoefficientClock c hint hpos)
    (Real.sqrt (scalarCoefficientPrimitive c 1)) μ Z

theorem scalarCoefficientStateFromNoise_integral_equation
    (c : ℝ→ℝ) (hint : IntervalIntegrable c volume 0 1)
    (hpos : ∀r∈Icc (0:ℝ) 1,0<c r) (μ : Paper.ParisiMeasure)
    (Z : C(Paper.Overlap,ℝ)) (q : Paper.Overlap) :
    scalarCoefficientStateFromNoise c hint (fun r hr=>hpos r ⟨hr.1.le,hr.2.le⟩) μ Z q=Z q+
      ∫r in (0:ℝ)..(q:ℝ),c r*parisiCDF μ r*
        scalarCoefficientSpatialField c hint (fun r hr=>hpos r ⟨hr.1.le,hr.2.le⟩) μ 1
          (r,scalarCoefficientStateFromNoise c hint (fun r hr=>hpos r ⟨hr.1.le,hr.2.le⟩)
            μ Z (projIcc 0 1 zero_le_one r)) := by
  let hp:∀r∈Ioo (0:ℝ) 1,0<c r:=fun r hr=>hpos r ⟨hr.1.le,hr.2.le⟩
  let τ:=scalarCoefficientClock c hint hp
  let ν:=scalarClockMeasure τ μ
  let β:=Real.sqrt (scalarCoefficientPrimitive c 1)
  let Y:=scalarClockStateFromNoise τ β μ Z
  let F:ℝ→ℝ:=fun s=>β^2*parisiCDF ν s*parisiGradient β ν
    (s,Y (τ.symm (projIcc 0 1 zero_le_one s)))
  have hβ:β≠0:=(scalarCoefficientClock_temperature c hint hp).1.ne'
  have hβsq:β^2=scalarCoefficientPrimitive c 1:=
    (scalarCoefficientClock_temperature c hint hp).2
  have hC:scalarCoefficientPrimitive c 1≠0:=(scalarCoefficient_total_pos c hint hp).ne'
  have hG:Continuous (fun s : ℝ=>parisiGradient β ν
      (s,Y (τ.symm (projIcc 0 1 zero_le_one s)))) :=
    (continuous_parisiGradient β ν).comp
      (continuous_id.prodMk (Y.continuous.comp (τ.symm.continuous.comp continuous_projIcc)))
  have hF:Measurable F:=(measurable_const.mul (parisiCDF_measurable ν)).mul hG.measurable
  have hsub:=scalarCoefficientClock_prefix_integral c hint hpos q F hF.aestronglyMeasurable
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (τ q).property.1,
    integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le q.property.1] at hsub
  have he:=scalarClockStateFromNoise_integral_equation τ β hβ μ Z q
  change Y q=Z q+∫s in (0:ℝ)..(τ q:ℝ),F s at he
  change Y q=Z q+_
  rw [he,hsub]
  congr 1
  apply intervalIntegral.integral_congr_uIoo
  rw [uIoo_of_le q.property.1]
  intro r hr
  have hri:r∈Icc (0:ℝ) 1:=⟨hr.1.le,hr.2.le.trans q.property.2⟩
  let z:Paper.Overlap:=⟨r,hri⟩
  have hclock:scalarCoefficientRealClock c hint hp r=(τ z:ℝ):=by
    unfold scalarCoefficientRealClock
    rw [projIcc_of_mem zero_le_one hri]
  have hproj:projIcc 0 1 zero_le_one (scalarCoefficientRealClock c hint hp r)=τ z:=by
    rw [hclock,projIcc_of_mem zero_le_one (τ z).property]
  have hCDF:parisiCDF ν (scalarCoefficientRealClock c hint hp r)=parisiCDF μ r:=by
    rw [hclock]
    exact scalarClockMeasure_cdf τ μ z
  change (c r/scalarCoefficientPrimitive c 1)*F (scalarCoefficientRealClock c hint hp r)=_
  dsimp only [F]
  rw [hCDF,hproj,τ.symm_apply_apply]
  change (c r/scalarCoefficientPrimitive c 1)*(β^2*parisiCDF μ r*
      parisiGradient β ν (scalarCoefficientRealClock c hint hp r,Y z))=
    c r*parisiCDF μ r*scalarCoefficientSpatialField c hint hp μ 1
      (r,Y (projIcc 0 1 zero_le_one r))
  unfold scalarCoefficientSpatialField
  rw [parisiSpatialField_one,projIcc_of_mem zero_le_one hri]
  change (c r/scalarCoefficientPrimitive c 1)*(β^2*parisiCDF μ r*
      parisiGradient β ν (scalarCoefficientRealClock c hint hp r,Y z))=
    c r*parisiCDF μ r*parisiGradient β ν (scalarCoefficientRealClock c hint hp r,Y z)
  rw [hβsq]
  field_simp

end HexagonPaper
