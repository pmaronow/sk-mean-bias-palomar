module
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-! Real Hilbert-space integrals of square-integrable vectors. -/
noncomputable section
open MeasureTheory
namespace FourPapersCommon
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {P : Measure Ω} {X Y : Ω→E}

theorem integrable_inner_of_memLp_two (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    Integrable (fun ω => inner ℝ (X ω) (Y ω)) P := by
  have hi := memLp_one_iff_integrable.mp (hX.norm.mul hY.norm)
  apply hi.mono' ((hX.aestronglyMeasurable.inner hY.aestronglyMeasurable))
  exact .of_forall fun ω => by
    change ‖inner ℝ (X ω) (Y ω)‖≤‖X ω‖*‖Y ω‖
    simpa only [Real.norm_eq_abs] using abs_real_inner_le_norm (X ω) (Y ω)

theorem integral_norm_sub_sq_of_memLp_two [IsFiniteMeasure P] (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    (∫ω,‖X ω-Y ω‖^2 ∂P)=(∫ω,‖X ω‖^2 ∂P)-2*(∫ω,inner ℝ (X ω) (Y ω)∂P)+
      (∫ω,‖Y ω‖^2 ∂P) := by
  simp_rw [norm_sub_sq_real]
  have ha := integral_add (hX.integrable_norm_pow'.sub
    ((integrable_inner_of_memLp_two hX hY).const_mul 2)) hY.integrable_norm_pow'
  have hs := integral_sub hX.integrable_norm_pow' ((integrable_inner_of_memLp_two hX hY).const_mul 2)
  simp only [Pi.add_apply,Pi.sub_apply] at ha hs
  rw [ha,hs,integral_const_mul]

end FourPapersCommon
