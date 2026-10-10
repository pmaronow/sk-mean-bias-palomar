module
public import QuantitativeFollowup.ConcentratingAdmissibleCost
public import QuantitativeFollowup.ConcentratingEnergySegment
public import QuantitativeFollowup.VectorConcentratingStieltjes
public import QuantitativeFollowup.ConcentratingDeficitPairing
public import QuantitativeFollowup.ConcentratingMeasurePairing
public import QuantitativePaper.ResponseMeanUpper

@[expose] public section

/-! Literal concentrating source clauses. The profile relation needs only
the physical interval; the true CDF extension supplies it elsewhere. Both
one-sided derivatives are stated on ordinary left/right half-lines. -/
noncomputable section
open Set MeasureTheory Filter Paper FRSB QuantitativePaper
open scoped Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
variable {n : ℕ}

theorem concentrating_profile_eq_all_of_physical (μ ν : Paper.ParisiMeasure)
    (beta a ell tau : ℝ) (ha : 0<a) (he : a+ell<1) (hell : 0<ell)
    (hprofile : ∀x∈Icc (0:ℝ) 1,
      beta*parisiCDF ν x=beta*parisiCDF μ x-tau*concentratingIntervalIncrement a ell x) :
    ∀x,beta*parisiCDF ν x=beta*parisiCDF μ x-tau*concentratingIntervalIncrement a ell x := by
  intro x
  by_cases hx0 : x<0
  · rw [parisiCDF_eq_zero_of_lt_zero ν hx0,parisiCDF_eq_zero_of_lt_zero μ hx0,
      concentratingIntervalIncrement_zero_outside a ell x hell (fun hx=>by linarith [hx.1])]
    ring
  by_cases hx1 : 1≤x
  · rw [parisiCDF_eq_one_of_one_le ν hx1,parisiCDF_eq_one_of_one_le μ hx1,
      concentratingIntervalIncrement_zero_outside a ell x hell (fun hx=>by linarith [hx.2])]
    ring
  exact hprofile x ⟨le_of_not_gt hx0,(lt_of_not_ge hx1).le⟩

/-- The complete actual Stieltjes/curvature representation and range in
source equation `eq:lz-Delta`, with the energy response normalization. -/
theorem concentrating_delta_source (μ : Paper.ParisiMeasure) (beta t lam : ℝ)
    (hbeta : beta ≠ 0) (ht : t < 1) (a ell : ℝ)
    (ha : 0<a) (he : a+ell<1) (hell : 0<ell) :
    vectorConcentratingDelta (n:=n) μ beta t (lam/beta) ht.le a ell =
      ∫x, concentratingIntervalBump a ell x
        ∂(vectorOverlapStieltjes (n:=n) μ beta t (lam/beta) hbeta ht).measure ∧
    vectorConcentratingDelta (n:=n) μ beta t (lam/beta) ht.le a ell =
      (1-t)*(∫x in (0:ℝ)..1,
        responseAveragedCurvature (n:=n) μ beta t lam ht.le
          (projIcc (0:ℝ) 1 zero_le_one x)*concentratingIntervalBump a ell x) ∧
    0 ≤ vectorConcentratingDelta (n:=n) μ beta t (lam/beta) ht.le a ell ∧
    vectorConcentratingDelta (n:=n) μ beta t (lam/beta) ht.le a ell ≤
      vectorMeanOverlapReal (n:=n) μ beta t (lam/beta) ht.le (a+ell)-
        vectorMeanOverlapReal (n:=n) μ beta t (lam/beta) ht.le a ∧
    vectorConcentratingDelta (n:=n) μ beta t (lam/beta) ht.le a ell ≤ 1 := by
  have hb:=vectorConcentratingDelta_bounds (n:=n) μ beta t (lam/beta) hbeta ht a ell ha he hell
  refine ⟨vectorConcentratingDelta_eq_stieltjes μ beta t (lam/beta) hbeta ht a ell ha he hell,
    ?_,hb.1,hb.2,(vectorConcentratingDelta_mem_unit μ beta t (lam/beta) hbeta ht a ell ha he hell).2⟩
  let Z:=fun x : ℝ=>responseAveragedCurvature (n:=n) μ beta t lam ht.le
    (projIcc (0:ℝ) 1 zero_le_one x)*concentratingIntervalBump a ell x
  have hs : Function.support Z ⊆ Ioc (0:ℝ) 1 := by
    intro x hx
    have hi : x∈Ioo a (a+ell) := by
      by_contra hi
      apply hx
      dsimp [Z]
      rw [concentratingIntervalBump_zero_outside a ell x hell hi,mul_zero]
    exact ⟨ha.trans hi.1,hi.2.le.trans he.le⟩
  change concentratingDelta a ell _=(1-t)*(∫x in (0:ℝ)..1,Z x)
  rw [←concentrating_weighted_integral_eq _ a ell hell]
  calc
    _ = ∫x,(1-t)*Z x := by
      apply integral_congr_ae
      exact .of_forall (fun x=>by
        change vectorMeanOverlapDerivative (n:=n) μ beta t (lam/beta) ht.le
          (projIcc (0:ℝ) 1 zero_le_one x)*concentratingIntervalBump a ell x=(1-t)*Z x
        rw [vectorMeanOverlapDerivative_eq_responseCurvature]
        dsimp [Z]
        ring)
    _ = _ := by
      rw [integral_const_mul,←intervalIntegral.integral_eq_integral_of_support_subset hs]

/-- Both integrations by parts, with the signed Stieltjes pairing
represented by the difference of its two genuine positive-measure integrals. -/
theorem concentrating_ibp_source (μ : Paper.ParisiMeasure) (beta t outer : ℝ)
    (hbeta : beta ≠ 0) (ht : t < 1) (a ell : ℝ)
    (ha : 0<a) (he : a+ell<1) (hell : 0<ell) :
    (∫x in (0:ℝ)..1,vectorOverlapDeficit (n:=n) μ beta t outer ht.le x*
      deriv (concentratingIntervalIncrement a ell) x) =
      -(∫x in a..a+ell,(x-vectorMeanOverlapReal (n:=n) μ beta t outer ht.le x)*
        concentratingIntervalIncrement a ell x) ∧
    (∫x in (0:ℝ)..1,vectorOverlapDeficit (n:=n) μ beta t outer ht.le x*
      deriv (concentratingIntervalIncrement a ell) x) =
      (∫x in (0:ℝ)..1,concentratingIntervalBump a ell x)-
        ∫x,concentratingIntervalBump a ell x
          ∂(vectorOverlapStieltjes (n:=n) μ beta t outer hbeta ht).measure ∧
    (∫x in (0:ℝ)..1,vectorOverlapDeficit (n:=n) μ beta t outer ht.le x*
      deriv (concentratingIntervalIncrement a ell) x) =
      8*ell/15-vectorConcentratingDelta (n:=n) μ beta t outer ht.le a ell := by
  have hip:=vector_concentrating_deficit_second_pairing (n:=n) μ beta t outer hbeta ht a ell ha he hell
  have hp:=concentrating_pairing
    (vectorMeanOverlapReal (n:=n) μ beta t outer ht.le)
    (fun x=>vectorMeanOverlapDerivative (n:=n) μ beta t outer ht.le (projIcc 0 1 zero_le_one x))
    (continuous_vectorMeanOverlapReal μ beta t outer ht.le)
    (continuous_vectorMeanOverlapDerivativeReal μ beta t outer ht.le) a ell hell
    (fun x hx=>hasDerivAt_vectorMeanOverlapReal μ beta t outer hbeta ht
      ⟨ha.trans_le hx.1,hx.2.trans_lt he⟩)
  refine ⟨?_,?_,hip⟩
  · rw [hip]
    change 8*ell/15-concentratingDelta a ell _= -_
    rw [←hp,←intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only
    ring
  · rw [hip,concentratingIntervalBump_unit_integral a ell hell ha.le he.le,
      ←vectorConcentratingDelta_eq_stieltjes μ beta t outer hbeta ht a ell ha he hell]

/-- Literal Lemma 5.7, including both standard one-sided derivatives at
every allowed parameter of any actual admissible profile curve. -/
theorem concentrating_direction_source (hn : 0<n)
    (A : ℝ→Paper.ParisiMeasure) (base : Paper.ParisiMeasure)
    (beta lam rho a ell l u : ℝ) (hbeta : 0<beta) (hlam : 0≤lam) (hrho : 0<rho)
    (ha : 0<a) (he : a+ell<1) (hell : 0<ell)
    (hprofile : ∀v∈Icc l u,∀x∈Icc (0:ℝ) 1,
      beta*parisiCDF (A v) x=beta*parisiCDF base x-v*concentratingIntervalIncrement a ell x) :
    ConvexOn ℝ (Icc l u) (fun v=>followupEnergyFunctional n beta lam rho (A v)) ∧
    (∀tau∈Ico l u,HasDerivWithinAt (fun v=>followupEnergyFunctional n beta lam rho (A v))
      (rho/2*(vectorConcentratingDelta (n:=n) (A tau) beta (1-rho) (lam/beta)
        (by linarith) a ell-8*ell/15)) (Ici tau) tau) ∧
    (∀tau∈Ioc l u,HasDerivWithinAt (fun v=>followupEnergyFunctional n beta lam rho (A v))
      (rho/2*(vectorConcentratingDelta (n:=n) (A tau) beta (1-rho) (lam/beta)
        (by linarith) a ell-8*ell/15)) (Iic tau) tau) := by
  have hp : ∀v∈Icc l u,∀x,
      beta*parisiCDF (A v) x=beta*parisiCDF base x-v*concentratingIntervalIncrement a ell x :=
    fun v hv=>concentrating_profile_eq_all_of_physical base (A v) beta a ell v ha he hell (hprofile v hv)
  obtain ⟨hc,hr,hl⟩:=concentrating_direction hn A base beta lam rho a ell l u
    hbeta hlam hrho ha he hell hp
  refine ⟨hc,?_,?_⟩
  · intro tau htau
    have hs : Icc tau u=ᶠ[𝓝 tau] Ici tau := by
      filter_upwards [Iio_mem_nhds htau.2] with x hx
      have hxu : x < u := hx
      apply propext
      simp only [mem_Icc,mem_Ici,and_iff_left hxu.le]
    exact (hr tau htau).congr_set hs
  · intro tau htau
    have hs : Icc l tau=ᶠ[𝓝 tau] Iic tau := by
      filter_upwards [Ioi_mem_nhds htau.1] with x hx
      have hlx : l < x := hx
      apply propext
      simp only [mem_Icc,mem_Iic,and_iff_right hlx.le]
    exact (hl tau htau).congr_set hs

/-- Literal Lemma 5.8 for all actual admissible endpoints, with no
density-room or minimizing-measure requirement on the starting profile. -/
theorem concentrating_cost_nearmin_source (hn : 0<n) (μ ν : Paper.ParisiMeasure)
    (beta lam rho a ell tau : ℝ) (hbeta : 0<beta) (hlam : lam∈Icc (0:ℝ) beta)
    (hrho : 0<rho) (ha : 0<a) (he : a+ell<1) (hell : 0<ell) (htau : 0<tau)
    (hprofile : ∀x∈Icc (0:ℝ) 1,
      beta*parisiCDF ν x=beta*parisiCDF μ x-tau*concentratingIntervalIncrement a ell x)
    (hfloor : ν∈scalarFloor (lam/beta)) :
    followupEnergyFunctional n beta lam rho ν-followupEnergyFunctional n beta lam rho μ≤rho*tau/2 ∧
    ∀eta,0≤eta→
      followupEnergyFunctional n beta lam rho μ≤
        followupEnergyMinimum n hn beta lam rho hbeta hlam.2 hrho.le+eta→
          8*ell/15-2*eta/(rho*tau)≤
            vectorConcentratingDelta (n:=n) ν beta (1-rho) (lam/beta) (by linarith) a ell := by
  have hp:=concentrating_profile_eq_all_of_physical μ ν beta a ell tau ha he hell hprofile
  refine ⟨concentrating_admissible_cost_le hn μ ν beta lam rho a ell tau
    hbeta hlam.1 hrho ha he hell htau.le hp,?_⟩
  intro eta _heta hnear
  exact concentrating_admissible_nearmin_delta_lower hn μ ν beta lam rho a ell tau eta
    hbeta hlam hrho ha he hell htau hp hfloor hnear

end QuantitativeFollowup
