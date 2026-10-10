module
public import QuantitativeFollowup.ConcentratingPushedContact
public import QuantitativeFollowup.ConcentratingPushedDirection

@[expose] public section

/-! The actual concentrating pushed segment on the root interval. This
assembles its admissibility, CDF direction, contact mass and density from
actual local profiles and actual constrained-minimum budgets. The genuine
second-response theorem is a separate dependency. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

def rootConcentratingStep (rho q eta : ℝ) : ℝ := 45*eta/(2*rho*q)

theorem rootConcentratingStep_pos (rho q eta : ℝ)
    (hrho : 0 < rho) (hq : 0 < q) (heta : 0 < eta) :
    0 < rootConcentratingStep rho q eta := by
  unfold rootConcentratingStep
  positivity

theorem rootConcentratingStep_balance (rho q eta : ℝ)
    (hrho : 0 < rho) (hq : 0 < q) :
    rho*rootConcentratingStep rho q eta*(8*(q/2)/15)=6*eta := by
  unfold rootConcentratingStep
  field_simp
  ring

theorem root_pushed_segment (n : ℕ) (hn : 0 < n) (bar ν : Paper.ParisiMeasure)
    (beta lam rho q eta k C m h : ℝ) (hbeta : 0 < beta)
    (hlam : lam ∈ Icc (0 : ℝ) beta) (hrho : 0 < rho)
    (hq : q ∈ Ioc (0 : ℝ) (1/4)) (heta : 0 < eta)
    (hk : 0 < k) (hC : 0 ≤ C) (hm : 0 ≤ m) (hh : 0 < h)
    (hbar : bar ∈ scalarFloor (lam/beta)) (hν : ν ∈ scalarFloor (lam/beta))
    (hnearbar : followupEnergyFunctional n beta lam rho bar ≤
      followupEnergyMinimum n hn beta lam rho hbeta hlam.2 hrho.le+eta/12)
    (hnearν : followupEnergyFunctional n beta lam rho ν ≤
      followupEnergyMinimum n hn beta lam rho hbeta hlam.2 hrho.le+eta)
    (hbarProfile : ∀x∈Ico (0 : ℝ) q, beta*parisiCDF bar x ≤ lam+m)
    (hνProfile : ∀x∈Icc (q/4) (3*q/4), k*x ≤ beta*parisiCDF ν x)
    (hlarge : 16*(lam+m) < k*q)
    (hLower : ENNReal.ofReal (k/2) • volume.restrict (Ioo (q/4) (3*q/4)) ≤
      ENNReal.ofReal beta • (parisiCDFPrimitive ν).measure.restrict (Ioo (q/4) (3*q/4)))
    (hUpperν : ENNReal.ofReal beta • (parisiCDFPrimitive ν).measure.restrict (Ioo (q/4) (3*q/4)) ≤
      ENNReal.ofReal C • volume.restrict (Ioo (q/4) (3*q/4)))
    (hUpperbar : ENNReal.ofReal beta • (parisiCDFPrimitive bar).measure.restrict (Ioo (q/4) (3*q/4)) ≤
      ENNReal.ofReal (m/h) • volume.restrict (Ioo (q/4) (3*q/4)))
    (hRoom : rootConcentratingStep rho q eta ≤ (k/2)*(q/2)^2/64) :
    ∃P : ℝ → Paper.ParisiMeasure,
      (∀theta∈Icc (0 : ℝ) 1,
        P theta ∈ scalarFloor (lam/beta) ∧
        ∀x : ℝ, beta*parisiCDF (P theta) x=beta*parisiCDF bar x+
          theta*concentratingPushedDirection bar ν beta (q/4) (q/2)
            (rootConcentratingStep rho q eta) x) ∧
      (∀theta∈Icc (1/4 : ℝ) (3/4),
        2*q/15 ≤ vectorConcentratingDelta (n:=n) (P theta) beta (1-rho) (lam/beta)
          (by linarith) (q/4) (q/2) ∧
        ENNReal.ofReal beta • (parisiCDFPrimitive (P theta)).measure.restrict (Ioo (q/4) (3*q/4)) ≤
          ENNReal.ofReal (m/h+C+k/4) • volume.restrict (Ioo (q/4) (3*q/4))) ∧
      (∀x∈Ioo (q/4) (3*q/4), k*q/16 ≤
        concentratingPushedDirection bar ν beta (q/4) (q/2) (rootConcentratingStep rho q eta) x) := by
  have ha : 0 < q/4 := by linarith [hq.1]
  have he : q/4+q/2 < 1 := by linarith [hq.2]
  have hell : 0 < q/2 := half_pos hq.1
  have hEnd : q/4+q/2=3*q/4 := by ring
  have hτp := rootConcentratingStep_pos rho q eta hrho hq.1 heta
  have hτ : rootConcentratingStep rho q eta ∈ Icc (0 : ℝ) ((k/2)*(q/2)^2/64) := ⟨hτp.le,hRoom⟩
  have hLow : ENNReal.ofReal (k/2) • volume.restrict (Ioo (q/4) (q/4+q/2)) ≤
      ENNReal.ofReal beta • (parisiCDFPrimitive ν).measure.restrict (Ioo (q/4) (q/4+q/2)) := by
    simpa only [hEnd] using hLower
  let P := fun theta => concentratingPushedMix bar ν beta (q/4) (q/2) (k/2)
    (rootConcentratingStep rho q eta) theta hbeta ha he hell (div_nonneg hk.le (by norm_num)) hτ hLow
  refine ⟨P,?_,?_,?_⟩
  · intro theta htheta
    exact ⟨concentratingPushedMix_mem_floor bar ν beta (q/4) (q/2) (k/2)
      (rootConcentratingStep rho q eta) theta (lam/beta) hbeta ha he hell
      (div_nonneg hk.le (by norm_num)) hτ htheta hLow hbar hν,
      concentratingPushedMix_direction bar ν beta (q/4) (q/2) (k/2)
        (rootConcentratingStep rho q eta) theta hbeta ha he hell
        (div_nonneg hk.le (by norm_num)) hτ htheta hLow⟩
  · intro theta htheta
    have hθ : theta ∈ Icc (0 : ℝ) 1 := ⟨by linarith [htheta.1],by linarith [htheta.2]⟩
    have hd := concentratingPushedMix_delta_lower hn bar ν beta lam rho (q/4) (q/2) (k/2)
      (rootConcentratingStep rho q eta) theta eta hbeta hlam hrho ha he hell
      (div_nonneg hk.le (by norm_num)) hτ hτp htheta heta.le hLow hbar hν hnearbar hnearν
      (rootConcentratingStep_balance rho q eta hrho hq.1)
    have hu := concentratingPushedMix_density_upper bar ν beta (q/4) (q/2) (k/2)
      (rootConcentratingStep rho q eta) theta (m/h) C hbeta ha he hell
      (div_nonneg hk.le (by norm_num)) (div_nonneg hm hh.le) hC hτ hθ hLow
      (by simpa only [hEnd] using hUpperbar) (by simpa only [hEnd] using hUpperν)
    refine ⟨?_,?_⟩
    · simpa only [P,show 4*(q/2)/15=2*q/15 by ring] using hd
    · simpa only [P,hEnd,show k/2/2=k/4 by ring] using hu
  · apply concentratingPushedDirection_root_sign bar ν beta q k
      (rootConcentratingStep rho q eta) hq.1 hτ _ hk.le
    intro x hx
    have hb := hbarProfile x ⟨by linarith [hx.1,hq.1],by linarith [hx.2,hq.1]⟩
    have hv := hνProfile x ⟨hx.1.le,hx.2.le⟩
    have hkx := mul_le_mul_of_nonneg_left hx.1.le hk.le
    nlinarith

end QuantitativeFollowup
