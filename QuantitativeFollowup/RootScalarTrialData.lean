module
public import QuantitativeFollowup.ScalarRootLocalizationData

@[expose] public section

/-! Genuine beta-only root data, with the actual clipped probability
trial's local density bounds and profile growth already transported. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper FRSB
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

theorem root_scalar_trial_data (beta : ℝ) (hbeta : 1 < beta) :
    ∃qStar k C T : ℝ,
      qStar ∈ Ioo (0 : ℝ) 1 ∧ 0 < k ∧ 1 ≤ C ∧ k ≤ C ∧
      T ∈ Ioo (0 : ℝ) qStar ∧ T ≤ 1/4 ∧ k*T ≤ 2 ∧
      ∀lam q : ℝ, ∀hlam : lam ∈ Icc (0 : ℝ) beta,
      q ∈ Ioc (0 : ℝ) T → 4*lam ≤ k*q →
      let ν := scalarClippedTrialMeasure (lam/beta)
        ⟨div_nonneg hlam.1 (zero_lt_one.trans hbeta).le,
          (div_le_one (zero_lt_one.trans hbeta)).mpr hlam.2⟩ (parisiMinimizer beta 0)
      ν ∈ scalarFloor (lam/beta) ∧
      (∀x∈Icc (q/4) (3*q/4), k*x ≤ beta*parisiCDF ν x) ∧
      ENNReal.ofReal (k/2) • volume.restrict (Ioo (q/4) (3*q/4)) ≤
        ENNReal.ofReal beta • (parisiCDFPrimitive ν).measure.restrict (Ioo (q/4) (3*q/4)) ∧
      ENNReal.ofReal beta • (parisiCDFPrimitive ν).measure.restrict (Ioo (q/4) (3*q/4)) ≤
        ENNReal.ofReal C • volume.restrict (Ioo (q/4) (3*q/4)) := by
  have hb : 0 < beta := zero_lt_one.trans hbeta
  obtain ⟨qStar,k,C,T₀,T,hqStar,hSupp,hk,hC,hkC,hT₀,hT₀q,hCT₀,hT,hG,hLower,hUpper⟩ :=
    scalar_root_localization_data beta hbeta
  have hTu : T ≤ 1/4 := hT.2.trans hT₀q
  have hTstar : T < qStar := hT.2.trans_lt hT₀.2
  have hkT : k*T ≤ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hkC) hT.1.le,
      mul_nonneg (zero_lt_one.trans_le hC).le (sub_nonneg.mpr hT.2)]
  refine ⟨qStar,k,C,T,hqStar,hk,hC,hkC,⟨hT.1,hTstar⟩,hTu,hkT,?_⟩
  intro lam q hlam hq hLarge
  have hs : lam/beta ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hlam.1 hb.le,(div_le_one hb).mpr hlam.2⟩
  let ν := scalarClippedTrialMeasure (lam/beta) hs (parisiMinimizer beta 0)
  have hI : Ioo (q/4) (3*q/4) ⊆ Icc (0 : ℝ) T := by
    intro x hx
    exact ⟨by linarith [hx.1,hq.1],by linarith [hx.2,hq.1,hq.2]⟩
  have hIstar : Ioo (q/4) (3*q/4) ⊆ Ico (0 : ℝ) qStar := by
    intro x hx
    have hi := hI hx
    exact ⟨hi.1,hi.2.trans_lt hTstar⟩
  have hIio : Ioo (q/4) (3*q/4) ⊆ Iio qStar := fun x hx => (hIstar hx).2
  have hEq := scalarClippedTrialMeasure_root_density_eq beta lam k T q hb hlam
    (parisiMinimizer beta 0) hk.le hq (by linarith [hTu]) hLarge
    (fun x hx => hG x ⟨hx.1,hx.2.trans hT.2⟩)
  refine ⟨scalarClippedTrialMeasure_mem_floor _ hs _,?_,?_,?_⟩
  · intro x hx
    have hxT : x ∈ Icc (0 : ℝ) T :=
      ⟨by linarith [hx.1,hq.1],by linarith [hx.2,hq.1,hq.2]⟩
    have hxU : x ∈ Icc (0 : ℝ) 1 := ⟨hxT.1,by linarith [hxT.2,hTu]⟩
    have hm := scalarClippedTrialMeasure_cdf _ hs (parisiMinimizer beta 0) x hxU
    change k*x ≤ beta*parisiCDF ν x
    rw [hm]
    exact (hG x ⟨hxT.1,hxT.2.trans hT.2⟩).trans
      (mul_le_mul_of_nonneg_left (le_max_right _ _) hb.le)
  · change _ ≤ ENNReal.ofReal beta • (parisiCDFPrimitive ν).measure.restrict _
    rw [hEq]
    have hh := Measure.restrict_mono_measure hLower (Ioo (q/4) (3*q/4))
    simpa only [Measure.restrict_smul,Measure.restrict_restrict measurableSet_Ioo,
      inter_eq_left.mpr hI] using hh
  · have hh := Measure.restrict_mono_measure (hUpper lam) (Ioo (q/4) (3*q/4))
    have hd : (scalarTrialStieltjes beta hb.le lam (parisiMinimizer beta 0)).measure.restrict
        (Ioo (q/4) (3*q/4)) ≤ ENNReal.ofReal C • volume.restrict (Ioo (q/4) (3*q/4)) := by
      simpa only [Measure.restrict_smul,Measure.restrict_restrict measurableSet_Ioo,
        inter_eq_left.mpr hIio,inter_eq_left.mpr hIstar] using hh
    have hDensity := scalarClippedTrialMeasure_energy_density beta lam hb hlam
      (parisiMinimizer beta 0) (Ioo (q/4) (3*q/4)) measurableSet_Ioo
      (fun x hx => ⟨(hI hx).1,by linarith [(hI hx).2,hTu]⟩)
      (fun hx => by linarith [hx.1,hq.1])
    rw [Measure.restrict_smul] at hDensity
    change ENNReal.ofReal beta • (parisiCDFPrimitive ν).measure.restrict _ ≤ _
    rw [hDensity]
    exact hd

end QuantitativeFollowup
