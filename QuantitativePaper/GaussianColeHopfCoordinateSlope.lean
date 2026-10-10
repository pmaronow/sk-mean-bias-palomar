module
public import QuantitativePaper.GaussianColeHopfCoordinateJets

@[expose] public section

/-! The removable mass quotient follows from a local FTC, including the
actual zero-coordinate derivative. No extension of the input outside its open
parameter cylinder is used. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace QuantitativePaper
set_option maxHeartbeats 1600000
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

theorem smoothCoordinateSlope_eq_integral_on_open (f : ℝ×E → ℝ)
    (U : Set (ℝ×E)) (hU : IsOpen U) (N : ℕ)
    (hf : ContDiffOn ℝ (N+1) f U)
    (hcontract : ∀ x ∈ U, ∀ r ∈ Icc (0:ℝ) 1, coordinateContraction r x ∈ U)
    (hzero : ∀ x, (0,x) ∈ U → f (0,x)=0)
    (z : ℝ×E) (hzU : z ∈ U) :
    smoothCoordinateSlope f z = smoothCoordinateSlopeIntegral f z := by
  unfold smoothCoordinateSlope smoothCoordinateSlopeIntegral
  rw [integral_Icc_eq_integral_Ioc, ←intervalIntegral.integral_of_le (show (0:ℝ)≤1 by norm_num)]
  by_cases hz : z.1=0
  · simp only [hz, ite_true, mul_zero]
    simp only [intervalIntegral.integral_const, sub_zero, one_smul]
  · rw [if_neg hz]
    let D : ℝ → ℝ := fun r => fderiv ℝ f (r*z.1,z.2) (1,0)
    have hc : ContinuousOn D (Icc (0:ℝ) 1) := by
      have hfd := (hf.fderiv_of_isOpen hU (show (0:ℕ∞ω)+1 ≤ N+1 by norm_cast; omega)).continuousOn
      have hm : Continuous (fun r : ℝ => (r*z.1,z.2)) :=
        (continuous_id.mul continuous_const).prodMk continuous_const
      exact (hfd.comp hm.continuousOn
        (fun r hr => by simpa only [coordinateContraction_apply] using hcontract z hzU r hr)).clm_apply continuousOn_const
    have hd (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) :
        HasDerivAt (fun t => f (t*z.1,z.2)) (z.1*D r) r := by
      have hpoint : (r*z.1,z.2) ∈ U := by
        simpa only [coordinateContraction_apply] using hcontract z hzU r hr
      have hh := ((hf.contDiffAt (hU.mem_nhds hpoint)).differentiableAt
        (by simp)).hasFDerivAt.comp_hasDerivAt r
        (((hasDerivAt_id r).mul_const z.1).prodMk (hasDerivAt_const r z.2))
      apply hh.congr_deriv
      simp only [one_mul]
      change fderiv ℝ f (r*z.1,z.2) (z.1,0)=z.1*D r
      have he : (z.1,(0:E))=z.1 • ((1:ℝ),(0:E)) := by simp
      rw [he,map_smul]
      rfl
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r hr => hd r (by simpa only [uIcc_of_le (show (0:ℝ)≤1 by norm_num)] using hr))
      ((hc.const_mul z.1).intervalIntegrable_of_Icc (by norm_num))
    have h0 : f (0,z.2)=0 := hzero z.2 (by
      simpa only [coordinateContraction_apply, zero_mul] using hcontract z hzU 0 ⟨le_rfl,zero_le_one⟩)
    simp only [one_mul, zero_mul, h0, sub_zero, intervalIntegral.integral_const_mul] at hFTC
    change f z/z.1=∫r in (0:ℝ)..1,D r
    apply (div_eq_iff hz).mpr
    simpa only [mul_comm] using hFTC.symm

end QuantitativePaper
