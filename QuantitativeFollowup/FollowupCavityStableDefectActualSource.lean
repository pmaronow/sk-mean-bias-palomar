module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseCheckpoint
public import QuantitativeFollowup.FollowupCavityFullVarianceTraceNativeProfile
public import QuantitativeFollowup.FollowupCavityStableDefectIntegrated

@[expose] public section

/-! The literal stable-defect conclusions under the printed scalar quadratic
order. The actual zero response supplies the physical contraction internally. -/
noncomputable section
open Set Filter MeasureTheory Paper FRSB QuantitativePaper FourPapersCommon
namespace QuantitativeFollowup
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- The printed scalar stability condition, with its freely chosen error. -/
def FollowupCavityPrintedScalarStability (n : ℕ) (β rho : ℝ)
    (hβ : 0 < β) (hrho : rho∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hμ : μ∈scalarFloor a) : Prop :=
  ∃ ε∈Icc (0:ℝ) (rho/4),∀f : endpointFixedL2 (parisiFreeMeasure μ a),
    inner ℝ f (scalarResponseL2Operator (followupCavityScalarBeta n β rho)
      (followupCavityScalarBeta_pos n β rho hβ hrho).ne' μ a ha hμ f)
      ≤ (1+ε)*‖f‖^2

theorem followupCavitySourceLevel_mem_Icc (β : ℝ) (hβ : 0 < β)
    (lam : ℝ) (hlam : lam∈Ioc (0:ℝ) (β/2)) :
    lam/β∈Icc (0:ℝ) 1 := by
  refine ⟨(div_pos hlam.1 hβ).le,?_⟩
  apply (div_le_iff₀ hβ).mpr
  linarith [hlam.2]

theorem followup_cavity_contraction_actual_printed_stability
    (n : ℕ) (hn : 0<n) (β rho : ℝ) (hβ : 0<β)
    (hrho : rho∈Ioc (0:ℝ) 1) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Ioc (0:ℝ) (1/2)) (hμ : μ∈scalarFloor a)
    (hmin : ∀ν∈scalarFloor a,vectorMeasureFunctional (n+1) μ β (1-rho) a ≤
      vectorMeasureFunctional (n+1) ν β (1-rho) a)
    (hstable : FollowupCavityPrintedScalarStability n β rho hβ hrho μ a
      ⟨ha.1.le,by linarith [ha.2]⟩ hμ) :
    FollowupCavityStableContractionAt (n+1) β (followupCavityNativeClosureConstant β)
      μ a rho hrho.1 := by
  obtain ⟨ε,hε,hJ⟩ := hstable
  have ha01 : a∈Icc (0:ℝ) 1 := ⟨ha.1.le,by linarith [ha.2]⟩
  have hresponse := followupCavityCpp_zero_response_ae n hn β rho hβ hrho μ a ha01 hμ
  have h := followup_cavity_contraction_of_zero_response n hn β rho hβ hrho μ a
    ha hμ hmin ε hε hJ hresponse
  simpa only [FollowupCavityStableContractionAt,one_div] using h

theorem followup_cavity_stable_defect_actual_printed_stability
    (N : ℕ) (hN : 2≤N) (β : ℝ) (hβ : 1<β)
    (μ : Paper.ParisiMeasure) (lam rho : ℝ)
    (hlam : lam∈Ioc (0:ℝ) (β/2)) (hrho : rho∈Ioc (0:ℝ) 1)
    (hNr : (N:ℝ)⁻¹≤rho) (hμ : μ∈scalarFloor (lam/β))
    (hmin : ∀ν∈scalarFloor (lam/β),vectorMeasureFunctional N μ β (1-rho) (lam/β) ≤
      vectorMeasureFunctional N ν β (1-rho) (lam/β))
    (hstable : FollowupCavityPrintedScalarStability (N-1) β rho
      (zero_lt_one.trans hβ) hrho μ (lam/β)
      (followupCavitySourceLevel_mem_Icc β (zero_lt_one.trans hβ) lam hlam) hμ) :
    β*vectorInterpolationDefect (n:=N) μ (lam/β) β (1-rho) (by linarith [hrho.1]) ≤
      followupCavityNativeStableDefectConstant β*(Real.log (2+(N:ℝ)))^2/
        ((N:ℝ)*lam*rho^2) := by
  have hb : 0<β := zero_lt_one.trans hβ
  have hn : 0<N-1 := by omega
  have hsucc : N-1+1=N := by omega
  have ha : lam/β∈Ioc (0:ℝ) (1/2) :=
    ⟨div_pos hlam.1 hb,(div_le_iff₀ hb).mpr (by linarith [hlam.2])⟩
  have hmin' : ∀ν∈scalarFloor (lam/β),
      vectorMeasureFunctional (N-1+1) μ β (1-rho) (lam/β) ≤
        vectorMeasureFunctional (N-1+1) ν β (1-rho) (lam/β) := by
    simpa only [hsucc] using hmin
  have hc := followup_cavity_contraction_actual_printed_stability (N-1) hn β rho hb
    hrho μ (lam/β) ha hμ hmin' hstable
  have hcN : FollowupCavityStableContractionAt N β (followupCavityNativeClosureConstant β)
      μ (lam/β) rho hrho.1 := by simpa only [hsucc] using hc
  exact followupCavityStableDefect_of_contraction N hN β
    (followupCavityNativeClosureConstant β) hβ (followupCavityNativeClosureConstant_one_le β)
    μ lam rho hlam hrho hNr hμ hmin hcN

theorem followup_cavity_stable_defect_actual_printed_optimized_ae
    (N : ℕ) (hN : 2≤N) (β : ℝ) (hβ : 1<β) (lam rho0 : ℝ)
    (hlam : lam∈Ioc (0:ℝ) (β/2)) (hrho0 : rho0∈Ioc (0:ℝ) 1)
    (hNr : (N:ℝ)⁻¹≤rho0)
    (hstable : ∀rho,∀hrho : rho∈Icc rho0 1,∀μ : Paper.ParisiMeasure,
      ∀hμ : μ∈scalarFloor (lam/β),
      (∀ν∈scalarFloor (lam/β),vectorMeasureFunctional N μ β (1-rho) (lam/β) ≤
        vectorMeasureFunctional N ν β (1-rho) (lam/β)) →
      FollowupCavityPrintedScalarStability (N-1) β rho (zero_lt_one.trans hβ)
        ⟨hrho0.1.trans_le hrho.1,hrho.2⟩ μ (lam/β)
        (followupCavitySourceLevel_mem_Icc β (zero_lt_one.trans hβ) lam hlam) hμ) :
    ∀ᵐrho∂volume,rho∈Ioo rho0 1 →
      smallIntervalDefect N β lam rho ≤
        followupCavityNativeStableDefectConstant β*(Real.log (2+(N:ℝ)))^2/
          ((N:ℝ)*lam*rho^2) := by
  have hb : 0<β := zero_lt_one.trans hβ
  have hn : 0<N-1 := by omega
  have hsucc : N-1+1=N := by omega
  have ha : lam/β∈Ioc (0:ℝ) (1/2) :=
    ⟨div_pos hlam.1 hb,(div_le_iff₀ hb).mpr (by linarith [hlam.2])⟩
  apply followupCavityStableDefect_optimized_ae_of_contraction N hN β
    (followupCavityNativeClosureConstant β) hβ (followupCavityNativeClosureConstant_one_le β)
    lam rho0 hlam hrho0 hNr
  intro rho hrho μ hμ hmin
  have hc := followup_cavity_contraction_actual_printed_stability (N-1) hn β rho hb
    ⟨hrho0.1.trans_le hrho.1,hrho.2⟩ μ (lam/β) ha hμ
    (by simpa only [hsucc] using hmin) (hstable rho hrho μ hμ hmin)
  simpa only [hsucc] using hc

theorem followup_cavity_stable_defect_actual_printed_integrated
    (N : ℕ) (hN : 2≤N) (β : ℝ) (hβ : 1<β) (lam rho0 : ℝ)
    (hlam : lam∈Ioc (0:ℝ) (β/2)) (hrho0 : rho0∈Ioc (0:ℝ) 1)
    (hNr : (N:ℝ)⁻¹≤rho0)
    (hstable : ∀rho,∀hrho : rho∈Icc rho0 1,∀μ : Paper.ParisiMeasure,
      ∀hμ : μ∈scalarFloor (lam/β),
      (∀ν∈scalarFloor (lam/β),vectorMeasureFunctional N μ β (1-rho) (lam/β) ≤
        vectorMeasureFunctional N ν β (1-rho) (lam/β)) →
      FollowupCavityPrintedScalarStability (N-1) β rho (zero_lt_one.trans hβ)
        ⟨hrho0.1.trans_le hrho.1,hrho.2⟩ μ (lam/β)
        (followupCavitySourceLevel_mem_Icc β (zero_lt_one.trans hβ) lam hlam) hμ) :
    IntervalIntegrable (smallIntervalDefect N β lam) volume rho0 1 ∧
      (∫rho in rho0..(1:ℝ),smallIntervalDefect N β lam rho) ≤
        followupCavityNativeStableDefectConstant β*(Real.log (2+(N:ℝ)))^2/
          ((N:ℝ)*lam*rho0) := by
  have hb : 0<β := zero_lt_one.trans hβ
  have hn : 0<N-1 := by omega
  have hsucc : N-1+1=N := by omega
  have ha : lam/β∈Ioc (0:ℝ) (1/2) :=
    ⟨div_pos hlam.1 hb,(div_le_iff₀ hb).mpr (by linarith [hlam.2])⟩
  apply followupCavityStableDefect_integrated_of_contraction N hN β
    (followupCavityNativeClosureConstant β) hβ (followupCavityNativeClosureConstant_one_le β)
    lam rho0 hlam hrho0 hNr
  intro rho hrho μ hμ hmin
  have hc := followup_cavity_contraction_actual_printed_stability (N-1) hn β rho hb
    ⟨hrho0.1.trans_le hrho.1,hrho.2⟩ μ (lam/β) ha hμ
    (by simpa only [hsucc] using hmin) (hstable rho hrho μ hμ hmin)
  simpa only [hsucc] using hc

end QuantitativeFollowup
