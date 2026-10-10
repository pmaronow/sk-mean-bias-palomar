module
public import QuantitativeFollowup.StableIntervalBudgetModel
public import QuantitativeFollowup.StableIntervalInverseSquareIntegral
public import QuantitativeFollowup.FourTermBudgetReduction

@[expose] public section

/-! Integrating the actual minimizing model once its native cavity estimate
is supplied. The cavity estimate remains an explicit separate premise in
this reduction; it is not a proof of the cavity theorem itself. -/
noncomputable section
open Set Filter MeasureTheory Paper FRSB QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 2400000

def StableCavityProfileBound (β C : ℝ) : Prop :=
  ∀n : ℕ,∀hn : 2 ≤ n,∀μ : Paper.ParisiMeasure,∀lam rho : ℝ,
    lam∈Ioc (0:ℝ) (min 1 (β/4)) → ∀hrho : rho∈Ioc (0:ℝ) 1,
    μ∈scalarFloor (lam/β) →
    (∀ν∈scalarFloor (lam/β),vectorMeasureFunctional n μ β (1-rho) (lam/β) ≤
      vectorMeasureFunctional n ν β (1-rho) (lam/β)) →
    (n:ℝ)⁻¹ ≤ rho →
    scalarOperatorStabilityError β μ (followupScalarCoefficient n β rho) ≤ rho/4 →
    β*vectorInterpolationDefect (n:=n) μ (lam/β) β (1-rho) (by linarith [hrho.1]) ≤
      C*(Real.log (2+(n:ℝ)))^2/((n:ℝ)*lam*rho^2)

theorem stableInterval_cutoff_lower_power (C eta lam : ℝ) (hC : 1 ≤ C)
    (hlam : lam∈Ioc (0:ℝ) 1) (heta : lam^5 ≤ eta) :
    lam^(5/7:ℝ) ≤ stableIntervalCutoff C eta := by
  have hb:=stableIntervalCutoff_bounds C eta lam hC hlam.1 heta
  apply le_trans _ hb.2.1
  apply le_min
  · exact Real.rpow_le_one hlam.1.le hlam.2 (by norm_num)
  · exact le_mul_of_one_le_left (Real.rpow_nonneg hlam.1.le _) (by linarith)

theorem stable_interval_integral_of_cavity_profile_bound (β : ℝ) (hβ : 1<β)
    (Cp : ℝ) (hCp : 0 ≤ Cp) (hProfile : StableCavityProfileBound β Cp) :
    ∃Cst Ct : ℝ,1 ≤ Cst ∧ 0<Ct ∧
      FourTermStableIntegralHypothesis β hβ (min 1 (β/4)) Cst Ct := by
  obtain ⟨Cst,hCst,hStable⟩:=stable_interval_budget_actual_minimizers β hβ
  refine ⟨Cst,Cp+1,hCst,by linarith,?_⟩
  intro n hn lam eta hlam hlamβ heta hTrial hcut
  have hn0 : 0<n:=by omega
  have hN : 0<(n:ℝ):=Nat.cast_pos.mpr hn0
  have hβp : 0<β:=zero_lt_one.trans hβ
  have hlp : 0<lam:=(inv_pos.mpr hN).trans_le hlam.1
  have hlunit : lam∈Ioc (0:ℝ) 1:=⟨hlp,hlam.2.trans (min_le_left 1 (β/4))⟩
  have hlSmall : lam∈Ioc (0:ℝ) (min 1 (β/4)):=⟨hlp,hlam.2⟩
  have hs : lam/β∈Ioo (0:ℝ) 1:=⟨div_pos hlp hβp,(div_lt_one hβp).mpr
    (by linarith [hlam.2.trans (min_le_right 1 (β/4))])⟩
  let a:=stableIntervalCutoff Cst eta
  have ha : 0<a:=(stableIntervalCutoff_bounds Cst eta lam hCst hlp heta).1
  have ha1 : a ≤ 1:=min_le_left _ _
  have hi : IntervalIntegrable (smallIntervalDefect n β lam) volume a 1:=
    (smallIntervalDefect_intervalIntegrable n hn0 β lam hβp hs).mono_set (by
      rw [uIcc_of_le zero_le_one,uIcc_of_le ha1]
      exact Icc_subset_Icc ha.le le_rfl)
  have hb : ∀ᵐrho ∂volume,rho∈Ioo a 1 →
      smallIntervalDefect n β lam rho ≤ (Cp*(Real.log (2+(n:ℝ)))^2/((n:ℝ)*lam))/rho^2 := by
    filter_upwards [smallInterval_ae_differentiable n hn0 β lam hβp hs] with rho hd
    intro hr
    have hrho : rho∈Ioo (0:ℝ) 1:=⟨ha.trans hr.1,hr.2⟩
    let μ:=vectorMeasureMinimizer n hn0 β (1-rho) (lam/β) (by linarith [hrho.1]) hs.2.le
    have hμ:=vectorMeasureMinimizer_mem n hn0 β (1-rho) (lam/β) (by linarith [hrho.1]) hs.2.le
    have hmin:=vectorMeasureMinimizer_minimal n hn0 β (1-rho) (lam/β) (by linarith [hrho.1]) hs.2.le
    have hstable:=hStable n hn lam eta hlam heta hTrial hcut rho ⟨hr.1.le,hr.2.le⟩ μ hμ hmin
    have hp:=hProfile n hn μ lam rho hlSmall ⟨hrho.1,hrho.2.le⟩ hμ hmin hstable.2.1 hstable.2.2
    unfold smallIntervalDefect
    rw [optimizedVectorInterpolationDefect_eq_of_minimizer hn0 μ β (lam/β) hs hμ hβp.ne'
      (1-rho) ⟨by linarith [hrho.2],by linarith [hrho.1]⟩ hmin (hd hrho)]
    exact hp.trans_eq (by rw [div_div,mul_assoc])
  let B:=Cp*(Real.log (2+(n:ℝ)))^2/((n:ℝ)*lam)
  have hB : 0 ≤ B:=by dsimp only [B];positivity
  have hInt:=stableInterval_integral_of_inverseSquare_bound
    (smallIntervalDefect n β lam) a B ha ha1 hB hi hb
  have hlow : lam^(5/7:ℝ) ≤ a:=stableInterval_cutoff_lower_power Cst eta lam hCst hlunit heta
  have hprod : lam*lam^(5/7:ℝ)=lam^(12/7:ℝ):=by
    calc
      _=lam^(1:ℝ)*lam^(5/7:ℝ):=by rw [Real.rpow_one]
      _=_:=by rw [←Real.rpow_add hlp];norm_num
  calc
    _ ≤ B/a:=hInt
    _ ≤ B/lam^(5/7:ℝ):=div_le_div_of_nonneg_left hB (Real.rpow_pos_of_pos hlp _) hlow
    _=Cp*(Real.log (2+(n:ℝ)))^2/((n:ℝ)*lam^(12/7:ℝ)):=by
      dsimp only [B]
      rw [div_div,mul_assoc,hprod]
    _ ≤ (Cp+1)*(Real.log (2+(n:ℝ)))^2/((n:ℝ)*lam^(12/7:ℝ)):=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)) (by positivity)

end QuantitativeFollowup
