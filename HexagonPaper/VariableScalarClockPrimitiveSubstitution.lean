module
public import HexagonPaper.VariableScalarClockPrimitiveCalculus
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-! Actual change of variables on every prefix of the coefficient clock. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HexagonPaper

theorem scalarCoefficientClockDensity_prefix_map (c : ℝ → ℝ)
    (hint : IntervalIntegrable c volume 0 1)
    (hpos : ∀ r ∈ Icc (0 : ℝ) 1, 0 < c r) (q : Paper.Overlap) :
    ((scalarCoefficientClockDensity c).restrict (Iic (q : ℝ))).map
      (scalarCoefficientRealClock c hint (fun r hr => hpos r ⟨hr.1.le, hr.2.le⟩)) =
        volume.restrict (Icc (0 : ℝ)
          (scalarCoefficientClock c hint (fun r hr => hpos r ⟨hr.1.le, hr.2.le⟩) q : ℝ)) := by
  let hp : ∀ r ∈ Ioo (0 : ℝ) 1, 0 < c r := fun r hr => hpos r ⟨hr.1.le, hr.2.le⟩
  let τ := scalarCoefficientClock c hint hp
  let f := scalarCoefficientRealClock c hint hp
  have hf : Measurable f := (continuous_scalarCoefficientRealClock c hint hp).measurable
  have hpre : f ⁻¹' Iic (τ q : ℝ) ∩ Icc (0 : ℝ) 1 =
      Iic (q : ℝ) ∩ Icc 0 1 := by
    ext x
    by_cases hx : x ∈ Icc (0 : ℝ) 1
    · have hfval : f x = (τ ⟨x, hx⟩ : ℝ) := by
        dsimp only [f, scalarCoefficientRealClock]
        rw [projIcc_of_mem zero_le_one hx]
      simp only [mem_inter_iff, mem_preimage, mem_Iic, hx, and_true, hfval]
      change τ ⟨x, hx⟩ ≤ τ q ↔ (⟨x, hx⟩ : Paper.Overlap) ≤ q
      exact τ.le_iff_le
    · simp only [mem_inter_iff, hx, and_false]
  have hrestr : (scalarCoefficientClockDensity c).restrict (f ⁻¹' Iic (τ q : ℝ)) =
      (scalarCoefficientClockDensity c).restrict (Iic (q : ℝ)) := by
    apply Measure.ext
    intro A hA
    rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
    apply scalarCoefficientClockDensity_congr_inter c _ _
      (hA.inter (measurableSet_Iic.preimage hf)) (hA.inter measurableSet_Iic)
    simpa only [inter_assoc] using congrArg (fun B : Set ℝ => A ∩ B) hpre
  have hI : Iic (τ q : ℝ) ∩ Icc (0 : ℝ) 1 = Icc 0 (τ q : ℝ) := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · rintro ⟨hxt, hx0, hx1⟩
      exact ⟨hx0, hxt⟩
    · rintro ⟨hx0, hxt⟩
      exact ⟨hxt, hx0, hxt.trans (τ q).property.2⟩
  have h := congrArg (fun P : Measure ℝ => P.restrict (Iic (τ q : ℝ)))
    (scalarCoefficientClockDensity_map c hint hpos)
  change ((scalarCoefficientClockDensity c).restrict (Iic (q : ℝ))).map f = _
  rw [Measure.restrict_map hf measurableSet_Iic, hrestr,
    Measure.restrict_restrict measurableSet_Iic, hI] at h
  exact h

theorem scalarCoefficientClock_prefix_integral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (c : ℝ → ℝ) (hint : IntervalIntegrable c volume 0 1)
    (hpos : ∀ r ∈ Icc (0 : ℝ) 1, 0 < c r) (q : Paper.Overlap)
    (F : ℝ → E)
    (hF : AEStronglyMeasurable F (volume.restrict (Icc (0 : ℝ)
      (scalarCoefficientClock c hint (fun r hr => hpos r ⟨hr.1.le, hr.2.le⟩) q : ℝ)))) :
    ∫ y in Icc (0 : ℝ)
        (scalarCoefficientClock c hint (fun r hr => hpos r ⟨hr.1.le, hr.2.le⟩) q : ℝ), F y =
      ∫ r in Icc (0 : ℝ) (q : ℝ),
        (c r / scalarCoefficientPrimitive c 1) •
          F (scalarCoefficientRealClock c hint (fun r hr => hpos r ⟨hr.1.le, hr.2.le⟩) r) := by
  let hp : ∀ r ∈ Ioo (0 : ℝ) 1, 0 < c r := fun r hr => hpos r ⟨hr.1.le, hr.2.le⟩
  let f := scalarCoefficientRealClock c hint hp
  let P := scalarCoefficientClockDensity c
  have hf : Measurable f := (continuous_scalarCoefficientRealClock c hint hp).measurable
  have hm := scalarCoefficientClockDensity_prefix_map c hint hpos q
  change (P.restrict (Iic (q : ℝ))).map f = _ at hm
  rw [← hm] at hF ⊢
  rw [integral_map hf.aemeasurable hF]
  have hi : IntegrableOn c (Icc (0 : ℝ) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).1 hint
  have hmeas : AEMeasurable (fun r => ENNReal.ofReal (c r / scalarCoefficientPrimitive c 1))
      (volume.restrict (Icc (0 : ℝ) 1)) :=
    (hi.div_const _).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hset : Iic (q : ℝ) ∩ Icc (0 : ℝ) 1 = Icc 0 (q : ℝ) := by
    ext r
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · rintro ⟨hrq, hr0, hr1⟩
      exact ⟨hr0, hrq⟩
    · rintro ⟨hr0, hrq⟩
      exact ⟨hrq, hr0, hrq.trans q.property.2⟩
  change ∫ r in Iic (q : ℝ), F (f r) ∂(volume.restrict (Icc (0 : ℝ) 1)).withDensity
    (fun r => ENNReal.ofReal (c r / scalarCoefficientPrimitive c 1)) = _
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀' (Iic (q : ℝ))
    (hmeas.mono_measure Measure.restrict_le_self)
    (ae_of_all _ (fun r => ENNReal.ofReal_lt_top)) (fun r => F (f r))]
  rw [Measure.restrict_restrict measurableSet_Iic, hset]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  rw [ENNReal.toReal_ofReal (div_nonneg (hpos r ⟨hr.1, hr.2.trans q.property.2⟩).le
    (scalarCoefficient_total_pos c hint hp).le)]

end HexagonPaper
