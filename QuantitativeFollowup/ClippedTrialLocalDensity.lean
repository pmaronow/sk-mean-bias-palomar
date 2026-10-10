module
public import QuantitativeFollowup.ClippedTrialMeasureDensity
public import QuantitativeFollowup.StieltjesLocalCongruence

@[expose] public section

/-! The true clipped probability trial agrees with the original scalar
measure on any interval where its floor is inactive. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

theorem scalarClippedTrialMeasure_local_density_eq (beta lam : ℝ)
    (hbeta : 0 < beta) (hlam : lam ∈ Icc (0 : ℝ) beta)
    (μ : Paper.ParisiMeasure) (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1)
    (hfloor : ∀x∈Icc a b, lam ≤ beta*parisiCDF μ x) :
    (parisiCDFPrimitive (scalarClippedTrialMeasure (lam/beta)
        ⟨div_nonneg hlam.1 hbeta.le,(div_le_one hbeta).mpr hlam.2⟩ μ)).measure.restrict (Ioo a b)=
      (parisiCDFPrimitive μ).measure.restrict (Ioo a b) := by
  have hs : lam/beta ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hlam.1 hbeta.le,(div_le_one hbeta).mpr hlam.2⟩
  apply stieltjes_restrict_Ioo_congr
  intro x hx
  change parisiCDF (scalarClippedTrialMeasure (lam/beta) hs μ) x=parisiCDF μ x
  rw [scalarClippedTrialMeasure_cdf (lam/beta) hs μ x ⟨ha.trans hx.1,hx.2.trans hb⟩]
  apply max_eq_right
  apply (div_le_iff₀ hbeta).mpr
  nlinarith [hfloor x hx]

theorem scalarClippedTrialMeasure_root_density_eq (beta lam k T q : ℝ)
    (hbeta : 0 < beta) (hlam : lam ∈ Icc (0 : ℝ) beta)
    (μ : Paper.ParisiMeasure) (hk : 0 ≤ k) (hq : q ∈ Ioc (0 : ℝ) T)
    (hT : T ≤ 1) (hlarge : 4*lam ≤ k*q)
    (hgrowth : ∀x∈Icc (0 : ℝ) T, k*x ≤ beta*parisiCDF μ x) :
    (parisiCDFPrimitive (scalarClippedTrialMeasure (lam/beta)
        ⟨div_nonneg hlam.1 hbeta.le,(div_le_one hbeta).mpr hlam.2⟩ μ)).measure.restrict (Ioo (q/4) (3*q/4))=
      (parisiCDFPrimitive μ).measure.restrict (Ioo (q/4) (3*q/4)) := by
  apply scalarClippedTrialMeasure_local_density_eq beta lam hbeta hlam μ (q/4) (3*q/4)
    (by linarith [hq.1]) (by linarith [hq.1,hq.2,hT])
  intro x hx
  have hxu : x ∈ Icc (0 : ℝ) T := ⟨by linarith [hx.1,hq.1],by linarith [hx.2,hq.1,hq.2]⟩
  have hg := hgrowth x hxu
  nlinarith [mul_nonneg hk (show 0 ≤ x-q/4 by linarith [hx.1])]

end QuantitativeFollowup
