module
public import QuantitativePaper.VectorProfileRecursion
public import Paper.ParisiSchemeMeasure
public import Paper.JTVariational

@[expose] public section

/-! The actual affine mass scheme represents the actual convex mixture
of its finite atomic probability laws on a common overlap grid. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace QuantitativePaper
open SpinGlass.Targets
set_option maxHeartbeats 1300000
variable {k : ℕ}

theorem vectorProfileSchemeMeasure_mix (s₀ s₁ : RSBScheme k)
    (hq : ∀ i, i ≤ k+2 → s₀.q i = s₁.q i) (θ : ℝ) (hθ : θ ∈ Icc (0:ℝ) 1) :
    Paper.parisiSchemeMeasure (vectorProfileScheme s₀ s₁ θ hθ)=
      Paper.parisiMix (Paper.parisiSchemeMeasure s₀) (Paper.parisiSchemeMeasure s₁) θ := by
  apply Subtype.ext
  change Paper.parisiSchemeRawMeasure (vectorProfileScheme s₀ s₁ θ hθ)=
    (Paper.parisiMix (Paper.parisiSchemeMeasure s₀) (Paper.parisiSchemeMeasure s₁) θ :
      Measure Paper.Overlap)
  rw [Paper.parisiMix_measure _ _ θ hθ]
  change Paper.parisiSchemeRawMeasure (vectorProfileScheme s₀ s₁ θ hθ)=
    ENNReal.ofReal (1-θ) • Paper.parisiSchemeRawMeasure s₀+
      ENNReal.ofReal θ • Paper.parisiSchemeRawMeasure s₁
  simp only [Paper.parisiSchemeRawMeasure,Finset.smul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hatom : Paper.parisiSchemeAtom (vectorProfileScheme s₀ s₁ θ hθ) i=
      Paper.parisiSchemeAtom s₀ i:=by apply Subtype.ext;rfl
  have hatom1 : Paper.parisiSchemeAtom s₁ i=Paper.parisiSchemeAtom s₀ i:=by
    apply Subtype.ext
    exact (hq (i+1) (by omega)).symm
  have hd₀ : 0 ≤ s₀.m (i+1)-s₀.m i := sub_nonneg.mpr (s₀.m_mono i (by omega))
  have hd₁ : 0 ≤ s₁.m (i+1)-s₁.m i := sub_nonneg.mpr (s₁.m_mono i (by omega))
  have hm : (vectorProfileScheme s₀ s₁ θ hθ).m (i+1)-
      (vectorProfileScheme s₀ s₁ θ hθ).m i=
      (1-θ)*(s₀.m (i+1)-s₀.m i)+θ*(s₁.m (i+1)-s₁.m i):=by
    simp only [vectorProfileScheme,vectorProfileMass]
    ring
  rw [hatom,hatom1,hm,ENNReal.ofReal_add
    (mul_nonneg (sub_nonneg.mpr hθ.2) hd₀) (mul_nonneg hθ.1 hd₁),
    ENNReal.ofReal_mul (sub_nonneg.mpr hθ.2),ENNReal.ofReal_mul hθ.1,
    add_smul,smul_smul,smul_smul]

end QuantitativePaper
