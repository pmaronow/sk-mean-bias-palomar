module
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-! The finite orthogonal-sum identity follows from actual pairwise
expectations and square integrability. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace FourPapersCommon

theorem integral_finset_sum_square {Ω I : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (S : Finset I) (Y : I → Ω → ℝ)
    (hY : ∀ i ∈ S, MemLp (Y i) 2 P)
    (horth : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (∫ ω, Y i ω*Y j ω ∂P)=0) :
    (∫ ω, (∑ i ∈ S, Y i ω)^2 ∂P)=∑ i ∈ S, ∫ ω, (Y i ω)^2 ∂P := by
  classical
  have hip (i : I) (hi : i ∈ S) (j : I) (hj : j ∈ S) :
      Integrable (fun ω => Y i ω*Y j ω) P :=
    memLp_one_iff_integrable.mp ((hY i hi).mul (hY j hj))
  have he : (fun ω => (∑ i ∈ S, Y i ω)^2) =
      (fun ω => ∑ i ∈ S, ∑ j ∈ S, Y i ω*Y j ω) := by
    funext ω
    rw [pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  rw [he, integral_finsetSum S (fun i hi => integrable_finsetSum S (fun j hj => hip i hi j hj))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum S (fun j hj => hip i hi j hj)]
  have hc : ∀ j ∈ S, j ≠ i → (∫ ω, Y i ω*Y j ω ∂P)=0 :=
    fun j hj hji => horth i hi j hj hji.symm
  rw [Finset.sum_eq_single i (fun j hj hji => hc j hj hji)
    (fun hni => (hni hi).elim)]
  simp only [pow_two]

end FourPapersCommon
