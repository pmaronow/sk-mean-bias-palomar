module
public import HexagonPaper.LocalDeficitArithmetic
public import HexagonPaper.LocalDeficitPush
public import QuantitativePaper.ResponseC1Midpoint

@[expose] public section

/-! Revised Lemma 5.6, on the actual finite-dimensional SK interpolation.
No smoothness outside the chosen interval, certificate premise, supplied
functional curvature, or hypothetical concentrating law is assumed. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper FourPapersCommon
open scoped ENNReal
namespace HexagonPaper
open QuantitativeFollowup
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

/-- The literal four-way local deficit certificate. The positive constant
is defined above in terms of beta alone; the endpoint hypotheses refer to
the genuine compact minimum and the genuine energy-coordinate measures. -/
theorem local_deficit_certificate (hn : 0 < n) (μ ν : Paper.ParisiMeasure)
    (beta lam rho a ell k A d0 d1 eta : ℝ) (hbeta : 0 < beta)
    (hlam : lam ∈ Icc (0 : ℝ) beta) (hrho : 0 < rho)
    (ha : 0 < a) (he : a+ell < 1) (hell : 0 < ell)
    (hk : 0 < k) (hA : 0 < A) (hd0 : 0 ≤ d0) (hd1 : 0 ≤ d1) (heta : 0 < eta)
    (hμ : μ ∈ scalarFloor (lam/beta)) (hν : ν ∈ scalarFloor (lam/beta))
    (hnearμ : followupEnergyFunctional n beta lam rho μ ≤
      followupEnergyMinimum n hn beta lam rho hbeta hlam.2 hrho.le+eta)
    (hnearν : followupEnergyFunctional n beta lam rho ν ≤
      followupEnergyMinimum n hn beta lam rho hbeta hlam.2 hrho.le+eta)
    (hdensity0 : ENNReal.ofReal beta • (parisiCDFPrimitive μ).measure.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal d0 • volume.restrict (Ioo a (a+ell)))
    (hdensity1 : ENNReal.ofReal beta • (parisiCDFPrimitive ν).measure.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal d1 • volume.restrict (Ioo a (a+ell)))
    (hlower : ENNReal.ofReal k • volume.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal beta • (parisiCDFPrimitive ν).measure.restrict (Ioo a (a+ell)))
    (hgap : ∀x∈Ioo a (a+ell), A ≤ beta*parisiCDF ν x-beta*parisiCDF μ x) :
    localDeficitCertificateConstant beta*localDeficitMinimum k ell A d0 d1 ≤ eta/rho := by
  let tau := 30*eta/(rho*ell)
  have htaupos : 0 < tau := by dsimp only [tau]; positivity
  have hbal : rho*tau*ell=30*eta := by
    dsimp only [tau]
    field_simp [hrho.ne',hell.ne']
  have hbal0 : tau*ell=30*(eta/rho) := by
    dsimp only [tau]
    field_simp [hrho.ne',hell.ne']
  have hbal16 : rho*tau*(8*ell/15)=16*eta := by nlinarith only [hbal]
  by_cases hroom : tau ≤ k*ell^2/64
  · by_cases hsign : tau ≤ A*ell/8
    · have hroom' : tau ∈ Icc (0 : ℝ) (k*ell^2/64) := ⟨htaupos.le,hroom⟩
      have hwhole := concentrating_half_room_parameter ell k tau hk.le hroom'
      let ν' := concentratingEnergyMeasure ν beta a ell k tau hbeta ha he hell hk.le hwhole hlower
      have hfν' : ν' ∈ scalarFloor (lam/beta) :=
        concentratingEnergyMeasure_preserves_floor ν beta a ell k tau (lam/beta)
          hbeta ha he hell hk.le hwhole hlower hν
      have hprofile : ∀x, beta*parisiCDF ν' x =
          beta*parisiCDF ν x-tau*concentratingIntervalIncrement a ell x :=
        concentratingEnergyMeasure_profile ν beta a ell k tau hbeta ha he hell hk.le hwhole hlower
      have hSignal : ∀x∈Ioo a (a+ell), A/2 ≤ beta*(parisiCDF ν' x-parisiCDF μ x) := by
        have hs := local_deficit_pushed_direction_sign μ ν beta a ell tau A hell htaupos.le hsign hgap
        intro x hx
        have hh := hs x hx
        have hp := hprofile x
        dsimp only [concentratingPushedDirection] at hh
        linarith
      have hContact : ∀theta∈Ioo (1/4 : ℝ) (3/4),
          4*ell/15 ≤ vectorConcentratingDelta (n:=n) (parisiMix μ ν' theta)
            beta (1-rho) (lam/beta) (by linarith) a ell := by
        intro theta ht
        have hh := local_deficit_pushed_delta_lower hn μ ν beta lam rho a ell k tau theta eta
          hbeta hlam hrho ha he hell hk.le hroom' htaupos ⟨ht.1.le,ht.2.le⟩
          heta.le hlower hμ hν hnearμ hnearν hbal16
        simpa only [concentratingPushedMix,ν'] using hh
      let d := d0+d1+k
      have hd : 0 < d := by dsimp only [d]; positivity
      have hDensity : ∀theta∈Ioo (1/4 : ℝ) (3/4),
          ENNReal.ofReal beta • (parisiCDFPrimitive (parisiMix μ ν' theta)).measure.restrict
            (Ioo a (a+ell)) ≤ ENNReal.ofReal d • volume.restrict (Ioo a (a+ell)) := by
        intro theta ht
        have ht01 : theta ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1],by linarith [ht.2]⟩
        have hp := concentratingPushedMix_density_upper μ ν beta a ell k tau theta d0 d1
          hbeta ha he hell hk.le hd0 hd1 hroom' ht01 hlower hdensity0 hdensity1
        have hp' : ENNReal.ofReal beta •
            (parisiCDFPrimitive (parisiMix μ ν' theta)).measure.restrict (Ioo a (a+ell)) ≤
            ENNReal.ofReal (d0+d1+k/2) • volume.restrict (Ioo a (a+ell)) := by
          simpa only [concentratingPushedMix,ν'] using hp
        apply hp'.trans
        intro S
        exact mul_le_mul_of_nonneg_right
          (ENNReal.ofReal_le_ofReal (show d0+d1+k/2 ≤ d by dsimp only [d]; linarith))
          (by positivity)
      let w := concentratingResponseTest a ell hell ha.le he.le
      let Y := fun theta => beta*512/(105*ell)+2*d*
        vectorConcentratingDelta (n:=n) (parisiMix μ ν' theta)
          beta (1-rho) (lam/beta) (by linarith) a ell
      have hEnvelope : ∀theta∈Ioo (1/4 : ℝ) (3/4),
          0 < Y theta ∧ responseC1EnergyDenominator (n:=n) μ ν' beta (1-rho) lam theta
            (by linarith) w ≤ Y theta ∧
          localDeficitResponseCurvature beta rho A ell d*Y theta ≤
            rho^3*(responseC1Signal (n:=n) μ ν' beta (1-rho) lam theta (by linarith) w)^2 := by
        intro theta ht
        exact local_deficit_concentrating_response_envelope hn μ ν' beta lam rho theta
          a ell A d hbeta hrho hell ha.le he.le hA.le hd
          (hContact theta ht) (hDensity theta ht) hSignal
      have hC : 0 ≤ localDeficitResponseCurvature beta rho A ell d := by
        unfold localDeficitResponseCurvature
        positivity
      have hMid := response_C1_middle_midpoint_lower hn μ ν' beta (1-rho) lam
        hbeta (by linarith) hlam.1 w Y (localDeficitResponseCurvature beta rho A ell d) hC
        (fun theta ht => (hEnvelope theta ht).1)
        (fun theta ht => (hEnvelope theta ht).2.1) (by
          intro theta ht
          have hh := (hEnvelope theta ht).2.2
          simpa only [show 1-(1-rho)=rho by ring] using hh)
      have hMid' : 3*localDeficitResponseCurvature beta rho A ell d/16 ≤
          followupEnergyFunctional n beta lam rho μ+followupEnergyFunctional n beta lam rho ν'-
            2*followupEnergyFunctional n beta lam rho (parisiMix μ ν' (1/2)) := by
        simpa only [responseEnergyFunctional,followupEnergyFunctional] using hMid
      have hCost := concentrating_admissible_cost_le hn ν ν' beta lam rho a ell tau
        hbeta hlam.1 hrho ha he hell htaupos.le hprofile
      have hMin := followupEnergyMinimum_le hn beta lam rho hbeta hlam.2 hrho.le
        (parisiMix μ ν' (1/2)) (parisiMix_mem_scalarFloor hμ hfν' (by norm_num))
      have hBudget : 3*localDeficitResponseCurvature beta rho A ell d/16 ≤
          2*eta+rho*tau/2 := by linarith only [hMid',hCost,hMin,hnearμ,hnearν]
      exact local_deficit_curvature_budget_bound beta rho k ell A d0 d1 eta tau
        hbeta hrho hell (by linarith) hA hk hd0 hd1 heta.le hbal hBudget
    · exact local_deficit_failed_sign_bound beta k ell A d0 d1 (eta/rho) tau
        hbeta hA hell hbal0 (lt_of_not_ge hsign)
  · exact local_deficit_failed_room_bound beta k ell A d0 d1 (eta/rho) tau
      hbeta hk hell hbal0 (lt_of_not_ge hroom)

end HexagonPaper
