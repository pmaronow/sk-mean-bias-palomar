module
public import QuantitativeFollowup.SmoothIsolationResponse
public import QuantitativeFollowup.RegularizedProbabilityDensity
public import QuantitativeFollowup.RegularizedTrialGeometry
public import QuantitativeFollowup.IsolationMidpointBudget
public import QuantitativeFollowup.RootAnyMinimizerRegularization

@[expose] public section

/-! The actual scalar-trial isolation endpoint, for every constrained
minimizer. The proof constructs a reflected profile and adaptive C¹
tests, uses the genuine weak-limit midpoint response, and then absorbs
the proved regularization cost. No second derivative of the limiting
functional or asserted response inequality is a hypothesis. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper FRSB
open scoped ENNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 3600000

theorem scalar_trial_isolation (beta : ℝ) (hbeta : 1<beta) :
    ∃K : ℝ,0<K ∧
      ∀n : ℕ,∀hn : 0<n,∀μ : Paper.ParisiMeasure,∀lam rho eta : ℝ,
      ∀hlam : lam∈Icc (0 : ℝ) beta,∀hrho : rho∈Ioc (0 : ℝ) 1,
      μ∈scalarFloor (lam/beta)→
      (∀ν∈scalarFloor (lam/beta),followupEnergyFunctional n beta lam rho μ≤
        followupEnergyFunctional n beta lam rho ν)→
      0≤eta→
      let ν := scalarClippedTrialMeasure (lam/beta)
        ⟨div_nonneg hlam.1 (zero_lt_one.trans hbeta).le,
          (div_le_one (zero_lt_one.trans hbeta)).mpr hlam.2⟩ (parisiMinimizer beta 0)
      followupEnergyFunctional n beta lam rho ν≤
        followupEnergyMinimum n hn beta lam rho (zero_lt_one.trans hbeta) hlam.2 hrho.1.le+eta→
      beta*parisiCDFDistance μ ν≤K*min 1 (rho^((-3/4 : ℝ))*eta^((1/4 : ℝ))) := by
  have hb : 0<beta := zero_lt_one.trans hbeta
  let scalar := parisiMinimizer beta 0
  have hscalar : IsParisiMinimizer beta 0 scalar := isParisiMinimizer_selected beta 0
  obtain ⟨q,hq,hsupp⟩ := minimizer_full_support beta hbeta scalar hscalar
  obtain ⟨L₁,hL₁,hLip⟩ := scalar_trial_lipschitz_below_terminal beta hb scalar hscalar q hq hsupp
  obtain ⟨L₂,hL₂,hDensity⟩ := regularized_probability_segment_density beta hb scalar hscalar q hq hsupp
  let L := max L₁ L₂
  have hL : 1≤L := hL₁.trans (le_max_left _ _)
  have hLpos : 0<L := zero_lt_one.trans_le hL
  let c := smoothIsolationConstant beta L
  have hc : 0<c := smoothIsolationConstant_pos beta L hb hLpos
  have ha : 0<c*isolationScale beta L c/8 := by
    have hh := isolationScale_pos beta L c hb hLpos hc
    positivity
  let K := isolationEndpointConstant beta (c*isolationScale beta L c/8)
  have hK : 0<K := isolationEndpointConstant_pos beta _ ha
  refine ⟨K,hK,?_⟩
  intro n hn μ lam rho eta hlam hrho hμ hminimal heta
  dsimp only
  intro hBudget
  have hs : lam/beta∈Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hlam.1 hb.le,(div_le_one hb).mpr hlam.2⟩
  let ν := scalarClippedTrialMeasure (lam/beta) hs scalar
  have hν : ν∈scalarFloor (lam/beta) := scalarClippedTrialMeasure_mem_floor _ hs scalar
  have hValue : followupEnergyFunctional n beta lam rho μ=
      followupEnergyMinimum n hn beta lam rho hb hlam.2 hrho.1.le := by
    apply le_antisymm
    · simpa only [followupMinimizer_value] using hminimal
        (followupMinimizer n hn beta lam rho hb hlam.2 hrho.1.le)
        (followupMinimizer_mem_floor n hn beta lam rho hb hlam.2 hrho.1.le)
    · exact followupEnergyMinimum_le hn beta lam rho hb hlam.2 hrho.1.le μ hμ
  have hTrial : followupEnergyFunctional n beta lam rho ν≤
      followupEnergyFunctional n beta lam rho μ+eta := by
    simpa only [ν,scalar,←hValue] using hBudget
  let D := beta*parisiCDFDistance μ ν
  have hD : D∈Icc (0 : ℝ) beta := by
    refine ⟨mul_nonneg hb.le (Paper.parisiCDFDistance_nonneg μ ν),?_⟩
    have hh := mul_le_mul_of_nonneg_left (FourPapersCommon.parisiCDFDistance_le_one μ ν) hb.le
    simpa only [mul_one] using hh
  change D≤K*min 1 (rho^((-3/4 : ℝ))*eta^((1/4 : ℝ)))
  by_cases hDz : D=0
  · rw [hDz]
    exact mul_nonneg hK.le (le_min zero_le_one
      (mul_nonneg (Real.rpow_nonneg hrho.1.le _) (Real.rpow_nonneg heta _)))
  have hDp : 0<D := lt_of_le_of_ne hD.1 (Ne.symm hDz)
  let h := isolationScale beta L c*rho*D^2
  obtain ⟨hh,hhu,hSmall,hScale⟩ := isolation_smoothing_scale_admissible beta L c rho D
    hbeta.le hL hc hrho ⟨hDp,hD.2⟩
  change 0<h at hh
  change h≤1/2 at hhu
  change 2*beta*h≤D at hSmall
  change h≤beta/L at hScale
  have hhI : h∈Ioc (0 : ℝ) (1/2) := ⟨hh,hhu⟩
  let bar := reflectedParisiMeasure μ (lam/beta) h hs hh
  have hbar : bar∈scalarFloor (lam/beta) := reflectedParisiMeasure_mem_floor μ _ h hs hhI
  have hroot : beta*(lam/beta)=lam := by field_simp
  have hPsi (x : ℝ) (hx : x∈Icc (0 : ℝ) 1) :
      beta*(parisiCDF ν x-parisiCDF bar x)=
        regularizedTrialDifference beta lam scalar μ (lam/beta) h hs hh x := by
    rw [mul_sub]
    change beta*parisiCDF (scalarClippedTrialMeasure (lam/beta) hs scalar) x-
      beta*parisiCDF (reflectedParisiMeasure μ (lam/beta) h hs hh) x=_
    rw [scalarClippedTrialMeasure_energy_cdf beta hb.le scalar _ hs x hx,hroot]
    rfl
  have hRootPsi : beta*(parisiCDF ν 0-parisiCDF bar 0)≤0 := by
    rw [hPsi 0 (by norm_num),regularizedTrialDifference_initial beta hb.ne' scalar μ hscalar
      q hq hsupp lam (lam/beta) h hlam.1 hs hhI hroot]
  have hSlope : ∀z x : ℝ,0≤z→z≤x→x<q→
      beta*(parisiCDF ν x-parisiCDF bar x)-beta*(parisiCDF ν z-parisiCDF bar z)≤L*(x-z) := by
    intro z x hz hzx hxq
    have hx : x∈Icc (0 : ℝ) 1 := ⟨hz.trans hzx,hxq.le.trans hq.2.le⟩
    have hz' : z∈Icc (0 : ℝ) 1 := ⟨hz,hzx.trans hx.2⟩
    rw [hPsi x hx,hPsi z hz']
    have hv := hLip lam z x ⟨hz,hzx.trans_lt hxq⟩ ⟨hx.1,hxq⟩
    simp only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hzx)] at hv
    have hm := mul_le_mul_of_nonneg_left (parisiCDF_monotone bar hzx) hb.le
    have hLe := mul_le_mul_of_nonneg_right (le_max_left L₁ L₂) (sub_nonneg.mpr hzx)
    dsimp only [regularizedTrialDifference]
    linarith [le_abs_self (scalarTrialProfile beta lam scalar x-scalarTrialProfile beta lam scalar z)]
  obtain ⟨hPost,hAnti⟩ := regularizedTrialDifference_post_terminal beta lam hb.le hlam.2 scalar μ
    q hsupp (lam/beta) h hs hh
  have hPost' : ∀x∈Icc q 1,0≤beta*(parisiCDF ν x-parisiCDF bar x) := by
    intro x hx
    rw [hPsi x ⟨hq.1.le.trans hx.1,hx.2⟩]
    exact hPost x hx.1
  have hAnti' : AntitoneOn (fun x=>beta*(parisiCDF ν x-parisiCDF bar x)) (Icc q 1) := by
    intro x hx y hy hxy
    change beta*(parisiCDF ν y-parisiCDF bar y)≤beta*(parisiCDF ν x-parisiCDF bar x)
    rw [hPsi x ⟨hq.1.le.trans hx.1,hx.2⟩,hPsi y ⟨hq.1.le.trans hy.1,hy.2⟩]
    exact hAnti hx.1 hy.1 hxy
  have hBound : ∀x∈Icc (0 : ℝ) 1,|beta*(parisiCDF ν x-parisiCDF bar x)|≤beta := by
    intro x hx
    rw [hPsi x hx]
    exact regularizedTrialDifference_norm_le beta lam hb.le hlam scalar μ _ h hs hh x
  have hIntegral : D/2≤∫x in (0 : ℝ)..1,|beta*(parisiCDF ν x-parisiCDF bar x)| := by
    have hhD := regularizedTrialDifference_distance_half beta hb.le scalar μ (lam/beta) h hs hμ hhI hSmall
    rw [hroot] at hhD
    apply hhD.trans_eq
    apply intervalIntegral.integral_congr
    intro x hx
    exact congrArg abs (hPsi x (by simpa only [uIcc_of_le zero_le_one] using hx)).symm
  have hscaleL : h*L≤beta := (le_div_iff₀ hLpos).mp hScale
  have hscaleL₂ : h*L₂≤beta :=
    (mul_le_mul_of_nonneg_left (le_max_right L₁ L₂) hh.le).trans hscaleL
  let C := c*rho^2*min (rho*D^4) (h*D^2)
  have hC : 0≤C := mul_nonneg (mul_nonneg hc.le (sq_nonneg rho))
    (le_min (mul_nonneg hrho.1.le (pow_nonneg hD.1 4)) (mul_nonneg hh.le (sq_nonneg D)))
  have hTests : ∀theta∈Ioo (0 : ℝ) 1,∃w : ResponseC1Test,∃Y : ℝ,0<Y ∧
      responseC1EnergyDenominator (n:=n) bar ν beta (1-rho) lam theta (by linarith [hrho.1]) w≤Y ∧
      C*Y≤(1-(1-rho))^3*(responseC1Signal (n:=n) bar ν beta (1-rho) lam theta
        (by linarith [hrho.1]) w)^2 := by
    intro theta htheta
    have ht : theta∈Icc (0 : ℝ) 1 := ⟨htheta.1.le,htheta.2.le⟩
    have hFloor := parisiMix_mem_scalarFloor hbar hν ht
    rw [mem_scalarFloor_iff,zeroMass_eq_parisiCDF_zero] at hFloor
    have hFloor' : lam≤beta*parisiCDF (parisiMix bar ν theta) 0 := by
      have hm := mul_le_mul_of_nonneg_left hFloor hb.le
      simpa only [hroot] using hm
    have hDensity' := hDensity μ lam h theta hlam hhI ht hscaleL₂
    have hhTest := smooth_isolation_response_tests hn bar ν beta lam rho theta q L h D
      hbeta.le hlam.1 hrho hFloor' hq hL hh hDp hRootPsi hSlope hAnti' hPost' hBound hIntegral hDensity'
    simpa only [C,c,show 1-(1-rho)=rho by ring] using hhTest
  have hGap0 := response_C1_family_full_midpoint_lower hn bar ν beta (1-rho) lam C
    hb (by linarith [hrho.1]) hlam.1 hC hTests
  have hminSmall : h*D^2≤rho*D^4 := by
    have hS := (isolationScale_bounds beta L c hbeta.le hL hc).1
    have hm := mul_le_mul_of_nonneg_right hS (mul_nonneg hrho.1.le (pow_nonneg hD.1 4))
    dsimp only [h]
    nlinarith only [hm]
  have hGap : c*isolationScale beta L c/4*rho^3*D^4≤
      followupEnergyFunctional n beta lam rho bar+followupEnergyFunctional n beta lam rho ν-
        2*followupEnergyFunctional n beta lam rho (parisiMix bar ν (1/2)) := by
    change C/4≤_ at hGap0
    have he : C/4=c*isolationScale beta L c/4*rho^3*D^4 := by
      dsimp only [C]
      rw [min_eq_right hminSmall]
      dsimp only [h]
      ring
    rw [he] at hGap0
    exact hGap0
  have hMin := hminimal _ (parisiMix_mem_scalarFloor hbar hν (by norm_num : (1/2 : ℝ)∈Icc 0 1))
  have hRegularized := reflected_followup_energy_cost_le n hn beta hb μ lam rho h hlam
    ⟨hrho.1.le,hrho.2⟩ hμ hhI
  have hCost : followupEnergyFunctional n beta lam rho bar-
      followupEnergyFunctional n beta lam rho μ≤rho*beta*h^2/12 := by
    apply hRegularized.trans
    nlinarith [mul_nonneg (mul_nonneg hrho.1.le hlam.1) (sq_nonneg h)]
  have hTotal : followupEnergyFunctional n beta lam rho bar+followupEnergyFunctional n beta lam rho ν-
      2*followupEnergyFunctional n beta lam rho μ≤rho*beta*h^2/12+eta := by
    linarith only [hTrial,hCost]
  exact isolation_rate_of_midpoint beta L c rho D eta
    (followupEnergyFunctional n beta lam rho μ) (followupEnergyFunctional n beta lam rho bar)
    (followupEnergyFunctional n beta lam rho ν)
    (followupEnergyFunctional n beta lam rho (parisiMix bar ν (1/2)))
    hbeta.le hL hc hrho hD hMin hGap hTotal

end QuantitativeFollowup
