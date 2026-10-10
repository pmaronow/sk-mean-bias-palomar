module
public import QuantitativePaper.P2SmoothingWidth
public import QuantitativeFollowup.PartialLocalizationDensity
public import QuantitativeFollowup.PartialLocalizationProfile

@[expose] public section

/-! The sharper quantile argument uses an actual reflected regularization
of the free mass below its cutoff. This version smooths the whole lower
mass; its factor-two density change affects only the numerical constant.
Atoms at the cutoff and the prescribed root mass remain exact. -/
noncomputable section
open Set MeasureTheory Paper QuantitativeFollowup
open scoped ENNReal
namespace QuantitativePaper
set_option maxHeartbeats 1000000

theorem p2_partial_regularized_density_closed (β : ℝ) (hβ : 0 ≤ β)
    (μ : Paper.ParisiMeasure) (s q h : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
    (hq : q ∈ Ioo (0 : ℝ) 1) (hh : h ∈ Ioc (0 : ℝ) (1-q)) :
    ENNReal.ofReal β •
      (parisiCDFPrimitive (partialReflectedParisiMeasure μ s q h hs hh.1)).measure.restrict (Icc (q/4) (3*q/4)) ≤
    ENNReal.ofReal (β*(parisiFreeMeasure μ s).real (overlapBelow q)/h) •
      volume.restrict (Icc (q/4) (3*q/4)) := by
  have hfloor : partialReflectedParisiMeasure μ s q h hs hh.1 ∈ scalarFloor s := by
    rw [mem_scalarFloor_iff,partialReflectedParisiMeasure_root μ s q h hs hq hh]
  rw [parisiCDFPrimitive_free_restrict _ s hs hfloor (Icc (q/4) (3*q/4)) measurableSet_Icc
    (fun hz => by
      have hz0 : q/4 ≤ (0 : ℝ) := hz.1
      linarith [hq.1])]
  have hi : Icc (q/4) (3*q/4) ⊆ Iio q := by
    intro y hy
    change y < q
    linarith [hy.2,hq.1]
  have hd := Measure.restrict_mono_measure
    (partial_reflected_energy_density_le β hβ μ s q h hs hq hh) (Icc (q/4) (3*q/4))
  simpa only [Measure.restrict_smul,Measure.restrict_restrict measurableSet_Icc,
    inter_eq_left.mpr hi] using hd

theorem p2_regularized_profile_data (n : ℕ) (hn : 0 < n) (μ : Paper.ParisiMeasure)
    (β lam r q : ℝ) (hβ : 0 < β) (hlam : lam ∈ Icc (0 : ℝ) β)
    (hr : r ∈ Ioc (0 : ℝ) 1) (hq : q ∈ Ioc (0 : ℝ) (1/4))
    (hμ : μ ∈ scalarFloor (lam/β))
    (hm : β*(parisiFreeMeasure μ (lam/β)).real (overlapBelow q) ≤ 1/4) :
    let m := β*(parisiFreeMeasure μ (lam/β)).real (overlapBelow q)
    let h := p2SmoothingWidth r q m
    0 < h ∧ h ≤ q/8 ∧ m/h ≤ 1/(Real.sqrt r*q*Real.sqrt q) ∧
    ∃bar : Paper.ParisiMeasure,
      bar ∈ scalarFloor (lam/β) ∧ β*parisiCDF bar 0 = lam ∧
      followupEnergyFunctional n β lam r bar - followupEnergyFunctional n β lam r μ ≤ r^2*q^3*m^3/12 ∧
      (∀x ∈ Ico (0 : ℝ) q, β*parisiCDF bar x ≤ lam+m) ∧
      ENNReal.ofReal β • (parisiCDFPrimitive bar).measure.restrict (Icc (q/4) (3*q/4)) ≤
        ENNReal.ofReal (m/h) • volume.restrict (Icc (q/4) (3*q/4)) := by
  let m := β*(parisiFreeMeasure μ (lam/β)).real (overlapBelow q)
  let h := p2SmoothingWidth r q m
  have hm0 : 0 ≤ m := mul_nonneg hβ.le ENNReal.toReal_nonneg
  have hh := p2SmoothingWidth_pos_le r q m hr hq ⟨hm0,hm⟩
  have hhu : h ∈ Ioc (0 : ℝ) (1-q) := p2SmoothingWidth_mem r q m hr hq ⟨hm0,hm⟩
  have hqu : q ∈ Ioo (0 : ℝ) 1 := ⟨hq.1,by linarith [hq.2]⟩
  have hs : lam/β ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hlam.1 hβ.le,(div_le_one hβ).mpr hlam.2⟩
  let bar := partialReflectedParisiMeasure μ (lam/β) q h hs hh.1
  refine ⟨hh.1,hh.2,p2SmoothingWidth_density_bound r q m hr.1 hq.1 hm0,bar,?_,?_,?_,?_,?_⟩
  · rw [mem_scalarFloor_iff,partialReflectedParisiMeasure_root μ (lam/β) q h hs hqu hhu]
  · rw [partial_reflected_energy_root β μ (lam/β) q h hs hqu hhu]
    field_simp
  · have hc := partial_reflected_followup_energy_cost_le n hn β hβ μ lam r q h
      hlam ⟨hr.1.le,hr.2⟩ hμ hqu hhu
    change _ ≤ r*m*h^2/12 at hc
    rwa [p2SmoothingWidth_exact_cost r q m hr.1.le hq.1.le] at hc
  · exact partial_reflected_energy_profile_below β lam q h hβ hlam μ hh.1
  · exact p2_partial_regularized_density_closed β hβ.le μ (lam/β) q h hs hqu hhu

end QuantitativePaper
