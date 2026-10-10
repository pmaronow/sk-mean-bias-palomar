module
public import FourPapersCommon.WienerRotation

@[expose] public section

/-! Genuine exponential supremum moments of the actual continuous Brownian
path. Fernique is applied to the proved path-product rotation identity. -/
noncomputable section
open MeasureTheory ProbabilityTheory Paper
namespace FourPapersCommon
set_option maxHeartbeats 800000

theorem exists_integrable_exp_sq_canonicalWienerMeasure :
    ∃ ε : ℝ, 0<ε ∧ Integrable (fun path : WienerPath => Real.exp (ε*‖path‖^2))
      canonicalWienerMeasure :=
  exists_integrable_exp_sq_of_map_rotation_eq_self
    (canonicalWienerMeasure_rotation (-(Real.pi/4)))

theorem integrable_exp_norm_canonicalWienerMeasure (c : ℝ) :
    Integrable (fun path : WienerPath => Real.exp (c*‖path‖)) canonicalWienerMeasure := by
  obtain ⟨ε,hε,hi⟩ := exists_integrable_exp_sq_canonicalWienerMeasure
  have hbound (path : WienerPath) : c*‖path‖ ≤ ε*‖path‖^2+c^2/ε := by
    have hh := sq_nonneg (ε*‖path‖-c)
    have he : ε*(c^2/ε)=c^2 := by field_simp
    nlinarith [norm_nonneg path,sq_nonneg c,mul_pos hε hε]
  apply (hi.const_mul (Real.exp (c^2/ε))).mono' (by fun_prop)
  exact .of_forall fun path => by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le,←Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [hbound path])

theorem integrable_exp_norm_canonicalBrownianPath (c : ℝ) :
    Integrable (fun sample => Real.exp (c*‖canonicalBrownianPath sample‖))
      canonicalBrownianMeasure := by
  have hP : HasLaw canonicalBrownianPath canonicalWienerMeasure canonicalBrownianMeasure :=
    ⟨measurable_canonicalBrownianPath.aemeasurable,rfl⟩
  exact hP.integrable_comp (integrable_exp_norm_canonicalWienerMeasure c)

end FourPapersCommon
