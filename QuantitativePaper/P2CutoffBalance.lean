module
public import QuantitativePaper.P2ProfileMeasureBounds
public import QuantitativePaper.P2ResponseEnvelope
public import QuantitativeFollowup.FreeMeasureContact

@[expose] public section

/-! The physical midpoint budget for a genuine minimizing measure. The
trial is an actual probability measure with local profile/measure data. -/
noncomputable section
open Set MeasureTheory Paper QuantitativeFollowup
open scoped ENNReal
namespace QuantitativePaper
set_option maxHeartbeats 2000000

theorem p2_large_cutoff_balance (n : ℕ) (hn : 0 < n) (μ ν : Paper.ParisiMeasure)
    (β lam r q x u η k Cs T : ℝ) (hβ : 1 ≤ β) (hlam : lam ∈ Icc (0 : ℝ) β)
    (hr : r ∈ Ioc (0 : ℝ) 1) (hq : q ∈ Ioc (0 : ℝ) (1/4))
    (hx : x ∈ Icc (0 : ℝ) 1) (hqx : q ≤ x) (hqT : q ≤ T)
    (hu : u ∈ Ioc (0 : ℝ) 1) (hk : 0 < k) (hCs : 0 ≤ Cs)
    (hμ : μ ∈ scalarFloor (lam/β)) (hν : ν ∈ scalarFloor (lam/β))
    (hmin : ∀ρ ∈ scalarFloor (lam/β), responseEnergyFunctional n μ β (1-r) lam ≤
      responseEnergyFunctional n ρ β (1-r) lam)
    (hbudget : responseEnergyFunctional n ν β (1-r) lam-responseEnergyFunctional n μ β (1-r) lam ≤ η)
    (hsmall : β*parisiCDF μ x < 2*u) (hlarge : 16*u < k*q)
    (htrial : ∀y ∈ Icc (0 : ℝ) T, k*y ≤ β*parisiCDF ν y ∧ β*parisiCDF ν y ≤ 2)
    (hdensity : ENNReal.ofReal β • (parisiCDFPrimitive ν).measure.restrict (Ioo (0 : ℝ) T) ≤
      ENNReal.ofReal Cs • volume.restrict (Ioo (0 : ℝ) T)) :
    let m := β*(parisiFreeMeasure μ (lam/β)).real (overlapBelow q)
    0 ≤ m ∧ m ≤ 2*u ∧
      p2MidpointConstant k Cs*r^3*Real.sqrt r*q^5*Real.sqrt q ≤ η+r^2*q^3*m^3 := by
  let m := β*(parisiFreeMeasure μ (lam/β)).real (overlapBelow q)
  have hβp : 0 < β := by linarith
  have hm0 : 0 ≤ m := mul_nonneg hβp.le ENNReal.toReal_nonneg
  have hmle := p2_free_mass_le_profile μ β lam q x hβp hlam hμ hx hqx
  change m ≤ β*parisiCDF μ x-lam at hmle
  have hsum : lam+m < 2*u := by linarith
  have hqt : q ∈ Icc (0 : ℝ) T := ⟨hq.1.le,hqT⟩
  have hkq : k*q ≤ 2 := (htrial q hqt).1.trans (htrial q hqt).2
  have hmquart : m ≤ 1/4 := by linarith [hlam.1]
  obtain ⟨hhpos,hhq,hInv,bar,hbar,hRoot,hcost,hbarProfile,hbarDensity⟩ :=
    p2_regularized_profile_data n hn μ β lam r q hβp hlam hr hq hμ hmquart
  let h := p2SmoothingWidth r q m
  have hB : Ioo (q/4) (3*q/4) ⊆ Icc (q/4) (3*q/4) := Ioo_subset_Icc_self
  have hBT : Ioo (q/4) (3*q/4) ⊆ Ioo (0 : ℝ) T := by
    intro y hy
    exact ⟨by linarith [hy.1,hq.1],by linarith [hy.2,hq.1]⟩
  have hdbar : ENNReal.ofReal β • (parisiCDFPrimitive bar).measure.restrict (Ioo (q/4) (3*q/4)) ≤
      ENNReal.ofReal (1/(Real.sqrt r*q*Real.sqrt q)) • volume.restrict (Ioo (q/4) (3*q/4)) := by
    have hh := Measure.restrict_mono_measure hbarDensity (Ioo (q/4) (3*q/4))
    simp only [Measure.restrict_smul,Measure.restrict_restrict measurableSet_Ioo,
      inter_eq_left.mpr hB] at hh
    refine hh.trans ?_
    intro S
    simp only [Measure.smul_apply,smul_eq_mul]
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hInv) (by positivity)
  have hdν : ENNReal.ofReal β • (parisiCDFPrimitive ν).measure.restrict (Ioo (q/4) (3*q/4)) ≤
      ENNReal.ofReal Cs • volume.restrict (Ioo (q/4) (3*q/4)) := by
    have hh := Measure.restrict_mono_measure hdensity (Ioo (q/4) (3*q/4))
    simpa only [Measure.restrict_smul,Measure.restrict_restrict measurableSet_Ioo,
      inter_eq_left.mpr hBT] using hh
  have hbar2 (y : ℝ) (hy : y ∈ Icc (q/4) (3*q/4)) : β*parisiCDF bar y ≤ 2 := by
    have hb := hbarProfile y ⟨by linarith [hy.1,hq.1],by linarith [hy.2,hq.1]⟩
    linarith [hu.2]
  have hν2 (y : ℝ) (hy : y ∈ Icc (q/4) (3*q/4)) : β*parisiCDF ν y ≤ 2 :=
    (htrial y ⟨by linarith [hy.1,hq.1],by linarith [hy.2,hq.1]⟩).2
  have hsignal (y : ℝ) (hy : y ∈ Ioo (q/4) (3*q/4)) :
      k*q/8 ≤ β*(parisiCDF ν y-parisiCDF bar y) := by
    have hb := hbarProfile y ⟨by linarith [hy.1,hq.1],by linarith [hy.2,hq.1]⟩
    have hnν := (htrial y ⟨by linarith [hy.1,hq.1],by linarith [hy.2,hq.1]⟩).1
    have hky := mul_le_mul_of_nonneg_left hy.1.le hk.le
    nlinarith only [hb,hnν,hky,hsum,hlarge]
  have hGain := p2_midpoint_response_gain hn bar ν β lam r q k Cs hβ hr hq hk hCs hlam.1
    (fun θ hθ => by
      exact responseProfile_admissible_lower hβp
        (parisiMix_mem_scalarFloor hbar hν ⟨hθ.1.le,hθ.2.le⟩) le_rfl)
    (fun θ hθ y hy => by
      have he := responseProfile_mix bar ν β θ y ⟨hθ.1.le,hθ.2.le⟩
      unfold responseProfile at he
      rw [he]
      have h0 := hbar2 y hy
      have h1 := hν2 y hy
      nlinarith only [mul_nonneg (show 0 ≤ 1-θ by linarith [hθ.2]) (sub_nonneg.mpr h0),
        mul_nonneg hθ.1.le (sub_nonneg.mpr h1)])
    (fun θ hθ => by
      have hh := p2_mixed_density_upper bar ν β θ (1/(Real.sqrt r*q*Real.sqrt q)) Cs (q/4) (3*q/4)
        ⟨hθ.1.le,hθ.2.le⟩ (by positivity [hr.1,hq.1]) hCs hdbar hdν
      simpa only [add_comm] using hh)
    hsignal
  have hmid := hmin (parisiMix bar ν (1/2))
    (parisiMix_mem_scalarFloor hbar hν (by norm_num : (1/2 : ℝ) ∈ Icc 0 1))
  change responseEnergyFunctional n bar β (1-r) lam-responseEnergyFunctional n μ β (1-r) lam ≤
    r^2*q^3*m^3/12 at hcost
  refine ⟨hm0,by linarith [hlam.1],?_⟩
  have hnonneg : 0 ≤ r^2*q^3*m^3 := by positivity [hq.1]
  nlinarith only [hGain,hmid,hcost,hbudget,hnonneg]

end QuantitativePaper
