module
public import QuantitativeFollowup.FollowupCavityStableDefectActualSource

@[expose] public section

/-! The source's optimized-envelope clause needs only one stable minimizer
at the given differentiability point. No interval stability is required. -/
noncomputable section
open Set Filter MeasureTheory Paper FRSB QuantitativePaper FourPapersCommon
namespace QuantitativeFollowup
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem followup_cavity_stable_defect_actual_optimized_of_stable_minimizer
    (N : ℕ) (hN : 2≤N) (β : ℝ) (hβ : 1<β)
    (μ : Paper.ParisiMeasure) (lam rho : ℝ)
    (hlam : lam∈Ioc (0:ℝ) (β/2)) (hrho : rho∈Ioo (0:ℝ) 1)
    (hNr : (N:ℝ)⁻¹≤rho) (hμ : μ∈scalarFloor (lam/β))
    (hmin : ∀ν∈scalarFloor (lam/β),vectorMeasureFunctional N μ β (1-rho) (lam/β) ≤
      vectorMeasureFunctional N ν β (1-rho) (lam/β))
    (hstable : FollowupCavityPrintedScalarStability (N-1) β rho
      (zero_lt_one.trans hβ) ⟨hrho.1,hrho.2.le⟩ μ (lam/β)
      (followupCavitySourceLevel_mem_Icc β (zero_lt_one.trans hβ) lam hlam) hμ)
    (hd : DifferentiableAt ℝ (vectorInterpolationMinimum N β (lam/β)) (1-rho)) :
    smallIntervalDefect N β lam rho ≤
      followupCavityNativeStableDefectConstant β*(Real.log (2+(N:ℝ)))^2/
        ((N:ℝ)*lam*rho^2) := by
  have hn0 : 0<N := by omega
  have hb : 0<β := zero_lt_one.trans hβ
  have hs : lam/β∈Ioo (0:ℝ) 1 :=
    ⟨div_pos hlam.1 hb,(div_lt_one hb).mpr (by linarith [hlam.2])⟩
  have h := followup_cavity_stable_defect_actual_printed_stability N hN β hβ μ lam rho
    hlam ⟨hrho.1,hrho.2.le⟩ hNr hμ hmin hstable
  unfold smallIntervalDefect
  rw [optimizedVectorInterpolationDefect_eq_of_minimizer hn0 μ β (lam/β) hs hμ hb.ne'
    (1-rho) ⟨by linarith [hrho.2],by linarith [hrho.1]⟩ hmin hd]
  exact h

theorem followup_cavity_stable_defect_actual_optimized_some_minimizer_ae
    (N : ℕ) (hN : 2≤N) (β : ℝ) (hβ : 1<β) (lam : ℝ)
    (hlam : lam∈Ioc (0:ℝ) (β/2)) :
    ∀ᵐrho∂volume,∀hrho : rho∈Ioo (0:ℝ) 1,(N:ℝ)⁻¹≤rho →
      (∃μ : Paper.ParisiMeasure,∃hμ : μ∈scalarFloor (lam/β),
        (∀ν∈scalarFloor (lam/β),vectorMeasureFunctional N μ β (1-rho) (lam/β) ≤
          vectorMeasureFunctional N ν β (1-rho) (lam/β)) ∧
        FollowupCavityPrintedScalarStability (N-1) β rho (zero_lt_one.trans hβ)
          ⟨hrho.1,hrho.2.le⟩ μ (lam/β)
          (followupCavitySourceLevel_mem_Icc β (zero_lt_one.trans hβ) lam hlam) hμ) →
      smallIntervalDefect N β lam rho ≤
        followupCavityNativeStableDefectConstant β*(Real.log (2+(N:ℝ)))^2/
          ((N:ℝ)*lam*rho^2) := by
  have hn0 : 0<N := by omega
  have hb : 0<β := zero_lt_one.trans hβ
  have hs : lam/β∈Ioo (0:ℝ) 1 :=
    ⟨div_pos hlam.1 hb,(div_lt_one hb).mpr (by linarith [hlam.2])⟩
  filter_upwards [smallInterval_ae_differentiable N hn0 β lam hb hs] with rho hd
  intro hrho hNr hsome
  obtain ⟨μ,hμ,hmin,hstable⟩ := hsome
  exact followup_cavity_stable_defect_actual_optimized_of_stable_minimizer N hN β hβ
    μ lam rho hlam hrho hNr hμ hmin hstable (hd hrho)

end QuantitativeFollowup
