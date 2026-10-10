module
public import QuantitativeFollowup.FollowupCavityStableDefectModel
public import QuantitativeFollowup.SmallIntervalOptimized
public import QuantitativeFollowup.StableIntervalInverseSquareIntegral

@[expose] public section

/-! Honest optimized-envelope and inverse-square integration of the native
stable defect reducer. The actual contraction inequalities remain explicit
inputs until the independent native cavity theorem is instantiated. -/
noncomputable section
open Set Filter MeasureTheory QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

def FollowupCavityStableContractionAt (n : ℕ) (β C : ℝ)
    (μ : Paper.ParisiMeasure) (s rho : ℝ) (hr : 0 < rho) : Prop :=
  (3*rho/4)*vectorIntegratedSelfOverlapVariance (n:=n) μ s β (1-rho)
      (by linarith) ≤
    C*((n:ℝ)⁻¹+vectorInterpolationTraceError (n:=n) μ s β (1-rho) (by linarith)+
      vectorMeanDirectionCovarianceIntegral (n:=n) μ s β (1-rho) s (by linarith)+
      vectorIntegratedSelfOverlapCubic (n:=n) μ s β (1-rho) (by linarith))

theorem followupCavityStableDefect_optimized_ae_of_contraction
    (n : ℕ) (hn : 2 ≤ n) (β C : ℝ) (hβ : 1 < β) (hC : 1 ≤ C)
    (lam rho0 : ℝ) (hlam : lam ∈ Ioc (0:ℝ) (β/2))
    (hrho0 : rho0 ∈ Ioc (0:ℝ) 1) (hNr : (n:ℝ)⁻¹ ≤ rho0)
    (hcontract : ∀rho,∀hrho : rho ∈ Icc rho0 1,∀μ : Paper.ParisiMeasure,
      μ ∈ scalarFloor (lam/β) →
      (∀ν∈scalarFloor (lam/β),vectorMeasureFunctional n μ β (1-rho) (lam/β) ≤
        vectorMeasureFunctional n ν β (1-rho) (lam/β)) →
      FollowupCavityStableContractionAt n β C μ (lam/β) rho (hrho0.1.trans_le hrho.1)) :
    ∀ᵐrho ∂volume,rho∈Ioo rho0 1 →
      smallIntervalDefect n β lam rho ≤
        followupCavityStableDefectConstant β C*(Real.log (2+(n:ℝ)))^2/
          ((n:ℝ)*lam*rho^2) := by
  have hn0 : 0<n := by omega
  have hβp : 0<β := zero_lt_one.trans hβ
  have hs : lam/β ∈ Ioo (0:ℝ) 1 :=
    ⟨div_pos hlam.1 hβp,(div_lt_one hβp).mpr (by linarith [hlam.2])⟩
  filter_upwards [smallInterval_ae_differentiable n hn0 β lam hβp hs] with rho hd
  intro hr
  have hrho : rho∈Ioo (0:ℝ) 1 := ⟨hrho0.1.trans hr.1,hr.2⟩
  let μ := vectorMeasureMinimizer n hn0 β (1-rho) (lam/β) (by linarith [hrho.1]) hs.2.le
  have hμ := vectorMeasureMinimizer_mem n hn0 β (1-rho) (lam/β) (by linarith [hrho.1]) hs.2.le
  have hmin := vectorMeasureMinimizer_minimal n hn0 β (1-rho) (lam/β)
    (by linarith [hrho.1]) hs.2.le
  have hc := hcontract rho ⟨hr.1.le,hr.2.le⟩ μ hμ hmin
  have hb := followupCavityStableDefect_of_contraction n hn β C hβ hC μ lam rho
    hlam ⟨hrho.1,hrho.2.le⟩ (hNr.trans hr.1.le) hμ hmin hc
  unfold smallIntervalDefect
  rw [optimizedVectorInterpolationDefect_eq_of_minimizer hn0 μ β (lam/β) hs hμ hβp.ne'
    (1-rho) ⟨by linarith [hrho.2],by linarith [hrho.1]⟩ hmin (hd hrho)]
  exact hb

theorem followupCavityStableDefect_integrated_of_contraction
    (n : ℕ) (hn : 2 ≤ n) (β C : ℝ) (hβ : 1 < β) (hC : 1 ≤ C)
    (lam rho0 : ℝ) (hlam : lam ∈ Ioc (0:ℝ) (β/2))
    (hrho0 : rho0 ∈ Ioc (0:ℝ) 1) (hNr : (n:ℝ)⁻¹ ≤ rho0)
    (hcontract : ∀rho,∀hrho : rho ∈ Icc rho0 1,∀μ : Paper.ParisiMeasure,
      μ ∈ scalarFloor (lam/β) →
      (∀ν∈scalarFloor (lam/β),vectorMeasureFunctional n μ β (1-rho) (lam/β) ≤
        vectorMeasureFunctional n ν β (1-rho) (lam/β)) →
      FollowupCavityStableContractionAt n β C μ (lam/β) rho (hrho0.1.trans_le hrho.1)) :
    IntervalIntegrable (smallIntervalDefect n β lam) volume rho0 1 ∧
      (∫rho in rho0..(1:ℝ),smallIntervalDefect n β lam rho) ≤
        followupCavityStableDefectConstant β C*(Real.log (2+(n:ℝ)))^2/
          ((n:ℝ)*lam*rho0) := by
  have hn0 : 0<n := by omega
  have hβp : 0<β := zero_lt_one.trans hβ
  have hlp : 0<lam := hlam.1
  have hs : lam/β ∈ Ioo (0:ℝ) 1 :=
    ⟨div_pos hlam.1 hβp,(div_lt_one hβp).mpr (by linarith [hlam.2])⟩
  have hi : IntervalIntegrable (smallIntervalDefect n β lam) volume rho0 1 :=
    (smallIntervalDefect_intervalIntegrable n hn0 β lam hβp hs).mono_set (by
      rw [uIcc_of_le zero_le_one,uIcc_of_le hrho0.2]
      exact Icc_subset_Icc hrho0.1.le le_rfl)
  have hb := followupCavityStableDefect_optimized_ae_of_contraction n hn β C hβ hC
    lam rho0 hlam hrho0 hNr hcontract
  let B := followupCavityStableDefectConstant β C*(Real.log (2+(n:ℝ)))^2/((n:ℝ)*lam)
  have hB : 0 ≤ B := by
    have hpos := followupCavityStableDefectConstant_pos β C hβ hC
    dsimp only [B]
    positivity
  refine ⟨hi,?_⟩
  have hh := stableInterval_integral_of_inverseSquare_bound (smallIntervalDefect n β lam)
    rho0 B hrho0.1 hrho0.2 hB hi (hb.mono (fun rho h hr=>by
      simpa only [B,div_div,mul_assoc] using h hr))
  simpa only [B,div_div,mul_assoc] using hh

end QuantitativeFollowup
