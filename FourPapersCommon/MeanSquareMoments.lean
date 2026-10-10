module
public import FourPapersCommon.HilbertL2Integrals
public import FourPapersCommon.IntegralHilbertReaction

@[expose] public section

/-! Genuine mean-square convergence implies convergence of second moments. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace FourPapersCommon
variable {Ω E ι : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {P : Measure Ω} [IsFiniteMeasure P]
    {X : ι→Ω→E} {U : Ω→E} {l : Filter ι}
set_option maxHeartbeats 600000

theorem tendsto_integral_norm_sq_of_meanSquare (hX : ∀i,MemLp (X i) 2 P) (hU : MemLp U 2 P)
    (hlim : Tendsto (fun i =>∫ω,‖X i ω-U ω‖^2∂P) l (𝓝 0)) :
    Tendsto (fun i =>∫ω,‖X i ω‖^2∂P) l (𝓝 (∫ω,‖U ω‖^2∂P)) := by
  let C := ∫ω,‖U ω‖^2∂P
  have hC : 0≤C := integral_nonneg fun _=>sq_nonneg _
  have hcross (i : ι) :
      ‖∫ω,inner ℝ (U ω) (X i ω-U ω)∂P‖≤Real.sqrt (C*(∫ω,‖X i ω-U ω‖^2∂P)) := by
    have hc := integral_inner_sq_le hU ((hX i).sub hU)
    rw [show X i-U=(fun ω=>X i ω-U ω) from rfl] at hc
    have he : 0≤∫ω,‖X i ω-U ω‖^2∂P := integral_nonneg fun _=>sq_nonneg _
    have hs := Real.sq_sqrt (mul_nonneg hC he)
    rw [Real.norm_eq_abs]
    have hca : |∫ω,inner ℝ (U ω) (X i ω-U ω)∂P|^2≤C*(∫ω,‖X i ω-U ω‖^2∂P) := by
      simpa only [sq_abs,C] using hc
    nlinarith [abs_nonneg (∫ω,inner ℝ (U ω) (X i ω-U ω)∂P),Real.sqrt_nonneg (C*(∫ω,‖X i ω-U ω‖^2∂P))]
  have hb : Tendsto (fun i =>Real.sqrt (C*(∫ω,‖X i ω-U ω‖^2∂P))) l (𝓝 0) := by
    simpa only [mul_zero,Real.sqrt_zero,Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp (hlim.const_mul C)
  have hc := squeeze_zero_norm hcross hb
  have he (i : ι) : (∫ω,‖X i ω‖^2∂P)=C+2*(∫ω,inner ℝ (U ω) (X i ω-U ω)∂P)+
      (∫ω,‖X i ω-U ω‖^2∂P) := by
    have hf : (∫ω,‖X i ω‖^2∂P)=
        (∫ω,‖U ω+(X i ω-U ω)‖^2∂P) := by
      apply integral_congr_ae
      exact .of_forall fun ω => by congr 2; abel
    rw [hf]
    have h := integral_norm_sub_sq_of_memLp_two hU (((hX i).sub hU).neg)
    rw [show X i-U=(fun ω=>X i ω-U ω) from rfl] at h
    simp only [Pi.neg_apply,sub_neg_eq_add,inner_neg_right,integral_neg,norm_neg] at h
    convert h using 1 <;> simp only [C] <;> ring
  simp_rw [he]
  simpa only [mul_zero,add_zero] using ((tendsto_const_nhds (x:=C)).add (hc.const_mul 2)).add hlim

end FourPapersCommon
