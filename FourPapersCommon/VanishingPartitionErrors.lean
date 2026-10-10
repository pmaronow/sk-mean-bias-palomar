module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-! Integrable cell errors of orders mesh^(3/2), mesh², and mesh³ have a
vanishing total expectation on a fixed interval. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace FourPapersCommon
variable {Ω : Type*} [MeasurableSpace Ω]

theorem tendsto_integral_partition_errors (P : Measure Ω)
    (e : ℕ → ℕ → Ω → ℝ) (T A B C : ℝ)
    (hi : ∀ N i,i∈Finset.range (N+1) → Integrable (e N i) P)
    (hb : ∀ N i,i∈Finset.range (N+1) →
      ‖∫ ω,e N i ω ∂P‖ ≤ A*(T/(N+1))*Real.sqrt (T/(N+1))+
        B*(T/(N+1))^2+C*(T/(N+1))^3) :
    Tendsto (fun N=>∫ ω,∑ i∈Finset.range (N+1),e N i ω ∂P) atTop (𝓝 0) := by
  have hbound (N : ℕ) :
      ‖∫ ω,∑ i∈Finset.range (N+1),e N i ω ∂P‖ ≤
        T*(A*Real.sqrt (T/(N+1))+B*(T/(N+1))+C*(T/(N+1))^2) := by
    rw [integral_finsetSum _ (fun i hi'=>hi N i hi')]
    calc
      _ ≤ ∑ i∈Finset.range (N+1),‖∫ ω,e N i ω ∂P‖ := norm_sum_le _ _
      _ ≤ ∑ i∈Finset.range (N+1),
          (A*(T/(N+1))*Real.sqrt (T/(N+1))+B*(T/(N+1))^2+C*(T/(N+1))^3) :=
        Finset.sum_le_sum (fun i hi'=>hb N i hi')
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
        have hne : (N : ℝ)+1≠0 := by positivity
        field_simp
  apply squeeze_zero_norm hbound
  have hmesh : Tendsto (fun N : ℕ=>T/((N : ℝ)+1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using
      (tendsto_const_div_atTop_nhds_zero_nat T).comp (tendsto_add_atTop_nat 1)
  have hroot : Tendsto (fun N : ℕ=>Real.sqrt (T/((N : ℝ)+1))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hmesh
  have H : Tendsto (fun N : ℕ=>T*(A*Real.sqrt (T/((N : ℝ)+1))+
      B*(T/((N : ℝ)+1))+C*(T/((N : ℝ)+1))^2)) atTop
      (𝓝 (T*(A*0+B*0+C*0^2))) :=
    (tendsto_const_nhds (x := T)).mul
      ((((tendsto_const_nhds (x := A)).mul hroot).add
        ((tendsto_const_nhds (x := B)).mul hmesh)).add
          ((tendsto_const_nhds (x := C)).mul (hmesh.pow 2)))
  simpa only [mul_zero,add_zero,zero_pow (by norm_num : (2 : ℕ)≠0)] using H

end FourPapersCommon
