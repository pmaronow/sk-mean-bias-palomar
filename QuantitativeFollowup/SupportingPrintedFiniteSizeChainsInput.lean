module
public import QuantitativeFollowup.FollowupCavityActualStableProfile
public import QuantitativeFollowup.FollowupCavityStableIntervalActualSource
public import QuantitativeFollowup.FoundationMeanBias
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-! The Section 8 comparison input before Young absorption. The actual
trial and stable interval estimates are discharged internally. -/
noncomputable section
open Set Filter MeasureTheory Paper FRSB QuantitativePaper FourPapersCommon
open scoped Topology
namespace QuantitativeFollowup
set_option autoImplicit false
set_option maxHeartbeats 2400000

theorem supportingPrintedFiniteSize_same_error_input (β : ℝ) (hβ : 1 < β) :
    ∃ C L lambda0 : ℝ, 0 < C ∧ 1 ≤ L ∧ lambda0∈Ioc (0:ℝ) 1 ∧
      lambda0 ≤ β/4 ∧ ∀ N : ℕ, ∀ hN : 2 ≤ N,
      ∀ lam∈Icc ((N:ℝ)⁻¹) lambda0,
      energyComparisonError N β lam ≤
        C*(Real.log (2+(N:ℝ)))^3/((N:ℝ)*lam^(12/7:ℝ)) +
        (C*(N:ℝ)^(-(2/3:ℝ)))*
          (energyComparisonError N β lam+L*lam^5)^(1/21:ℝ) +
        (C*(N:ℝ)^(-(2/3:ℝ))*lam^(-(1/3:ℝ)))*
          (energyComparisonError N β lam+L*lam^5)^(1/7:ℝ) := by
  obtain ⟨Cst,Ct,hCst,hCt,hStable⟩ := followup_actual_stable_interval_integral β hβ
  obtain ⟨L,lambdaTrial,hL,hTrial0,hTrialβ,hTrial⟩ := fourTermBudget_actual_trial β hβ
  obtain ⟨Cs,hCs,hActual⟩ := fourTermBudget_actual_input β hβ
  let lambdaSt := min 1 (β/4)
  let lambda0 := min lambdaTrial lambdaSt
  let C := fourTermBudgetInputConstant Cs Ct (12*Cst)
  have hb : 0 < β := zero_lt_one.trans hβ
  have hSt : lambdaSt∈Ioc (0:ℝ) 1 :=
    ⟨lt_min zero_lt_one (div_pos hb (by norm_num)),min_le_left _ _⟩
  have h0 : lambda0∈Ioc (0:ℝ) 1 :=
    ⟨lt_min hTrial0.1 hSt.1,(min_le_left _ _).trans hTrial0.2⟩
  have h0β : lambda0 ≤ β/4 := (min_le_left _ _).trans hTrialβ
  have hC : 0 < C := fourTermBudgetInputConstant_pos Cs Ct (12*Cst)
    hCs.le hCt.le (by positivity)
  refine ⟨C,L,lambda0,hC,hL,h0,h0β,?_⟩
  intro N hN lam hlam
  have hn0 : 0 < N := by omega
  have hp : 0 < (N:ℝ) := Nat.cast_pos.mpr hn0
  have hlp : 0 < lam := (inv_pos.mpr hp).trans_le hlam.1
  have hlTrial : lam∈Ioc (0:ℝ) lambdaTrial :=
    ⟨hlp,hlam.2.trans (min_le_left _ _)⟩
  have hlSt : lam∈Icc ((N:ℝ)⁻¹) lambdaSt :=
    ⟨hlam.1,hlam.2.trans (min_le_right _ _)⟩
  have hlβ : lam∈Icc (0:ℝ) β := ⟨hlp.le,by linarith [hlam.2.trans h0β]⟩
  have hlSmall : lam∈Ioc (0:ℝ) (min 1 (β/4)) :=
    ⟨hlp,le_min (hlam.2.trans h0.2) (hlam.2.trans h0β)⟩
  have hs : lam/β∈Ioo (0:ℝ) 1 :=
    ⟨div_pos hlp hb,(div_lt_one hb).mpr (by linarith [hlam.2.trans h0β])⟩
  let eta := energyComparisonError N β lam+L*lam^5
  have he := energyComparisonError_nonneg N hn0 β hb lam hs
  have heta : lam^5 ≤ eta := by
    have hh := mul_le_mul_of_nonneg_right hL (pow_nonneg hlp.le 5)
    dsimp only [eta]
    linarith
  have hBudget : ∀rho : ℝ,∀hrho : rho∈Ioc (0:ℝ) 1,
      smallIntervalTrialGap N hn0 β lam rho hb hlβ hrho.1.le ≤ eta :=
    fun rho hrho => hTrial N hn0 lam hlTrial rho hrho
  exact hActual N hN lam L Cst Ct hlSmall hL hCst hCt.le hBudget
    (hStable N hN lam eta hlSt hlβ heta hBudget)

theorem supportingPrintedFiniteSize_stable_tail_chain (β : ℝ) (hβ : 1<β) :
    ∃ L lambda0 Cst Ct : ℝ,1≤L ∧ lambda0∈Ioc (0:ℝ) 1 ∧
      lambda0≤β/4 ∧ 1≤Cst ∧ 0<Ct ∧
      ∀N : ℕ,∀hN : 2≤N,∀lam : ℝ,lam∈Icc ((N:ℝ)⁻¹) lambda0 →
      let eta := stableIntervalTrialBudget N β lam L
      let rho0 := stableIntervalCutoff Cst eta
      lam^5≤eta ∧ 0<rho0 ∧ min 1 (12*Cst*lam^((5:ℝ)/7))≤rho0 ∧
      rho0≤12*Cst*eta^((1:ℝ)/7) ∧
      (rho0<1 →
        (∀rho∈Icc rho0 1,∀μ : Paper.ParisiMeasure,∀hμ : μ∈scalarFloor (lam/β),
          (∀ν∈scalarFloor (lam/β),vectorMeasureFunctional N μ β (1-rho) (lam/β) ≤
            vectorMeasureFunctional N ν β (1-rho) (lam/β)) →
          let ε := Cst*(rho^((-3:ℝ)/4)*eta^((1:ℝ)/4)+lam^2+(N:ℝ)⁻¹)
          0<rho ∧ (N:ℝ)⁻¹≤rho ∧ ε∈Icc (0:ℝ) (rho/4) ∧
          ∀hs : lam/β∈Icc (0:ℝ) 1,∀hd : 0<followupScalarCoefficient N β rho,
          ∀f : endpointFixedL2 (parisiFreeMeasure μ (lam/β)),
            inner ℝ f (scalarResponseL2Operator (Real.sqrt (followupScalarCoefficient N β rho))
              (Real.sqrt_pos.mpr hd).ne' μ (lam/β) hs hμ f)≤(1+ε)*‖f‖^2) ∧
        IntervalIntegrable (smallIntervalDefect N β lam) volume rho0 1 ∧
        (∫rho in rho0..(1:ℝ),smallIntervalDefect N β lam rho)≤
          Ct*(Real.log (2+(N:ℝ)))^2/((N:ℝ)*lam*rho0) ∧
        Ct*(Real.log (2+(N:ℝ)))^2/((N:ℝ)*lam*rho0)≤
          Ct*(Real.log (2+(N:ℝ)))^2/((N:ℝ)*lam^((12:ℝ)/7))) := by
  obtain ⟨L,lambda0,Cst,hL,h0,h0β,hCst,hPrinted⟩ :=
    stable_interval_actual_minimizers_printed_operator β hβ
  let Cp := followupCavityNativeStableDefectConstant β
  have hCp : 0<Cp := followupCavityNativeStableDefectConstant_pos β hβ
  refine ⟨L,lambda0,Cst,Cp,hL,h0,h0β,hCst,hCp,?_⟩
  intro N hN lam hlam
  have hb : 0<β := zero_lt_one.trans hβ
  have hn0 : 0<N := by omega
  have hn : 0<N-1 := by omega
  have hsucc : N-1+1=N := by omega
  have hNrpos : 0<(N:ℝ) := Nat.cast_pos.mpr hn0
  have hlp : 0<lam := (inv_pos.mpr hNrpos).trans_le hlam.1
  have hlunit : lam∈Ioc (0:ℝ) 1 := ⟨hlp,hlam.2.trans h0.2⟩
  have hlbeta : lam∈Ioc (0:ℝ) (β/2) := ⟨hlp,by linarith [hlam.2.trans h0β]⟩
  have hs : lam/β∈Ioo (0:ℝ) 1 :=
    ⟨div_pos hlp hb,(div_lt_one hb).mpr (by linarith [hlam.2.trans h0β])⟩
  let eta := stableIntervalTrialBudget N β lam L
  have he : 0≤energyComparisonError N β lam := energyComparisonError_nonneg N hn0 β hb lam hs
  have heta : lam^5≤eta := by
    have hh := mul_le_mul_of_nonneg_right hL (pow_nonneg hlp.le 5)
    dsimp only [eta,stableIntervalTrialBudget]
    linarith
  have hbounds := stableIntervalCutoff_bounds Cst eta lam hCst hlp heta
  let rho0 := stableIntervalCutoff Cst eta
  dsimp only
  refine ⟨heta,hbounds.1,hbounds.2.1,hbounds.2.2,?_⟩
  intro hcut
  have hPrinted' := hPrinted N hN lam hlam hcut
  have hR0 : rho0∈Ioc (0:ℝ) 1 := ⟨hbounds.1,hcut.le⟩
  have hNr : (N:ℝ)⁻¹≤rho0 :=
    (stableIntervalCutoff_stability Cst eta lam ((N:ℝ)⁻¹) rho0 hCst hlunit
      heta hlam.1 hcut le_rfl).2.1
  have hSource : ∀rho,∀hrho : rho∈Icc rho0 1,∀μ : Paper.ParisiMeasure,
      ∀hμ : μ∈scalarFloor (lam/β),
      (∀ν∈scalarFloor (lam/β),vectorMeasureFunctional N μ β (1-rho) (lam/β) ≤
        vectorMeasureFunctional N ν β (1-rho) (lam/β)) →
      FollowupCavityPrintedScalarStability (N-1) β rho hb
        ⟨hR0.1.trans_le hrho.1,hrho.2⟩ μ (lam/β)
        (followupCavitySourceLevel_mem_Icc β hb lam hlbeta) hμ := by
    intro rho hrho μ hμ hmin
    have hp := hPrinted' rho hrho μ hμ hmin
    refine ⟨_,⟨hp.2.2.1,hp.2.2.2.1⟩,?_⟩
    intro f
    have hd : 0<followupScalarCoefficient N β rho :=
      (half_pos (sq_pos_of_ne_zero hb.ne')).trans_le
        (followupScalarCoefficient_window N hN β rho ⟨hp.1,hrho.2⟩).1.1
    have hj := hp.2.2.2.2 (followupCavitySourceLevel_mem_Icc β hb lam hlbeta) hd f
    simpa only [followupCavityScalarBeta,followupCavityD_eq_completed_scalar_coefficient,hsucc]
      using hj
  obtain ⟨hi,hIntegral⟩ := followup_cavity_stable_defect_actual_printed_integrated
    N hN β hβ lam rho0 hlbeta hR0 hNr hSource
  refine ⟨?_,hi,hIntegral,?_⟩
  · intro rho hrho μ hμ hmin
    have hp := hPrinted' rho hrho μ hμ hmin
    exact ⟨hp.1,hp.2.1,⟨hp.2.2.1,hp.2.2.2.1⟩,hp.2.2.2.2⟩
  · have hlow : lam^((5:ℝ)/7)≤rho0 :=
      stableInterval_cutoff_lower_power Cst eta lam hCst hlunit heta
    have hprod : lam*lam^((5:ℝ)/7)=lam^((12:ℝ)/7) := by
      calc
        _=lam^(1:ℝ)*lam^((5:ℝ)/7) := by rw [Real.rpow_one]
        _=_ := by rw [←Real.rpow_add hlp];norm_num
    calc
      (Cp*(Real.log (2+(N:ℝ)))^2/((N:ℝ)*lam*rho0))=(Cp*(Real.log (2+(N:ℝ)))^2/((N:ℝ)*lam))/rho0 := by rw [div_div,mul_assoc]
      _≤(Cp*(Real.log (2+(N:ℝ)))^2/((N:ℝ)*lam))/lam^((5:ℝ)/7) :=
        div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hlp _) hlow
      _=Cp*(Real.log (2+(N:ℝ)))^2/((N:ℝ)*lam^((12:ℝ)/7)) := by
        rw [div_div,mul_assoc,hprod]

theorem supportingPrintedFiniteSize_chosen_mean_chain (β : ℝ) (hβ : 1 < β) :
    ∃ L lambda0 : ℝ,∃ N1 : ℕ,1 ≤ L ∧ lambda0∈Ioc (0:ℝ) 1 ∧
      2 ≤ N1 ∧ ∀ N : ℕ,N1 ≤ N →
      let lam := (N:ℝ)^(-(7/50:ℝ))
      lam∈Ioc (0:ℝ) lambda0 ∧
      0 ≤ (Paper.parisiPDEValue β 0-pressure N β)/β ∧
      (Paper.parisiPDEValue β 0-pressure N β)/β ≤
        32*L*lam^5+2*energyComparisonError N β lam := by
  obtain ⟨L,lambda0,hL,h0,h0β,hMean⟩ := foundation_mean_bias β hβ
  have hsmall : ∀ᶠ N : ℕ in atTop,(N:ℝ)^(-(7/50:ℝ)) ≤ lambda0 := by
    exact ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 7/50)).comp
      tendsto_natCast_atTop_atTop).eventually_le_const h0.1
  obtain ⟨Nt,hNt⟩ := eventually_atTop.1 hsmall
  refine ⟨L,lambda0,max 2 Nt,hL,h0,le_max_left _ _,?_⟩
  intro N hN
  have hn : 2 ≤ N := (le_max_left _ _).trans hN
  have hn0 : 0 < N := by omega
  have hp : 0 < (N:ℝ) := Nat.cast_pos.mpr hn0
  have hl : (N:ℝ)^(-(7/50:ℝ))∈Ioc (0:ℝ) lambda0 :=
    ⟨Real.rpow_pos_of_pos hp _,hNt N ((le_max_right _ _).trans hN)⟩
  have h := hMean N hn0 _ hl
  exact ⟨hl,by simpa only [energyMeanDeficit_eq_pressure_gap] using h.1,
    by simpa only [energyMeanDeficit_eq_pressure_gap] using h.2.1.trans h.2.2⟩

end QuantitativeFollowup
