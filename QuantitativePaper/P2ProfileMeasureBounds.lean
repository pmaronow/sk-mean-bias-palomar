module
public import QuantitativePaper.P2RegularizedProfile
public import QuantitativeFollowup.ConcentratingMixedDensity

@[expose] public section

/-! Genuine free-mass and local measure bounds used by the p2 quantile. -/
noncomputable section
open Set MeasureTheory Paper QuantitativeFollowup
open scoped ENNReal
namespace QuantitativePaper
set_option maxHeartbeats 1000000

theorem p2_free_mass_le_profile (μ : Paper.ParisiMeasure) (β lam q x : ℝ)
    (hβ : 0 < β) (hlam : lam ∈ Icc (0 : ℝ) β)
    (hμ : μ ∈ scalarFloor (lam/β)) (hx : x ∈ Icc (0 : ℝ) 1) (hqx : q ≤ x) :
    β*(parisiFreeMeasure μ (lam/β)).real (overlapBelow q) ≤ β*parisiCDF μ x-lam := by
  have hs : lam/β ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg hlam.1 hβ.le,(div_le_one hβ).mpr hlam.2⟩
  have hh : (parisiFreeMeasure μ (lam/β)).real (overlapBelow q) ≤
      (parisiFreeMeasure μ (lam/β)).real {p : Paper.Overlap | (p : ℝ) ≤ x} := by
    apply measureReal_mono (μ := parisiFreeMeasure μ (lam/β))
      (s₁ := overlapBelow q) (s₂ := {p : Paper.Overlap | (p : ℝ) ≤ x})
      (fun p hp => (show (p : ℝ) < q from hp).le.trans hqx) (measure_ne_top _ _)
  simp only [Measure.real] at hh
  rw [parisiFreeMeasure_cdf μ (lam/β) x hs hμ hx,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (scalarFloor_cdf_lower hμ hx.1))] at hh
  have hm := mul_le_mul_of_nonneg_left hh hβ.le
  change β*((parisiFreeMeasure μ (lam/β)) (overlapBelow q)).toReal ≤ _
  have he : β*parisiCDF μ x-lam = β*(parisiCDF μ x-lam/β) := by
    field_simp
  rw [he]
  exact hm

theorem p2_mixed_density_upper (μ ν : Paper.ParisiMeasure) (β θ d₀ d₁ a b : ℝ)
    (hθ : θ ∈ Icc (0 : ℝ) 1) (hd₀ : 0 ≤ d₀) (hd₁ : 0 ≤ d₁)
    (h₀ : ENNReal.ofReal β • (parisiCDFPrimitive μ).measure.restrict (Ioo a b) ≤
      ENNReal.ofReal d₀ • volume.restrict (Ioo a b))
    (h₁ : ENNReal.ofReal β • (parisiCDFPrimitive ν).measure.restrict (Ioo a b) ≤
      ENNReal.ofReal d₁ • volume.restrict (Ioo a b)) :
    ENNReal.ofReal β • (parisiCDFPrimitive (parisiMix μ ν θ)).measure.restrict (Ioo a b) ≤
      ENNReal.ofReal (d₀+d₁) • volume.restrict (Ioo a b) := by
  rw [parisiCDFPrimitive_mix_measure μ ν θ hθ,Measure.restrict_add,
    Measure.restrict_smul,Measure.restrict_smul,smul_add,
    smul_comm (ENNReal.ofReal β) (ENNReal.ofReal (1-θ)),
    smul_comm (ENNReal.ofReal β) (ENNReal.ofReal θ)]
  have hh₀ : ENNReal.ofReal (1-θ) •
      (ENNReal.ofReal β • (parisiCDFPrimitive μ).measure.restrict (Ioo a b)) ≤
      ENNReal.ofReal d₀ • volume.restrict (Ioo a b) := by
    intro S
    calc
      _ ≤ ENNReal.ofReal (1-θ)*(ENNReal.ofReal d₀ • volume.restrict (Ioo a b)) S :=
        mul_le_mul_of_nonneg_left (h₀ S) (by positivity)
      _ ≤ _ := by
        simpa only [Measure.smul_apply,smul_eq_mul,one_mul] using
          mul_le_mul_of_nonneg_right (show ENNReal.ofReal (1-θ) ≤ 1 by
            simpa using ENNReal.ofReal_le_ofReal (show 1-θ ≤ 1 by linarith [hθ.1])) (by positivity)
  have hh₁ : ENNReal.ofReal θ •
      (ENNReal.ofReal β • (parisiCDFPrimitive ν).measure.restrict (Ioo a b)) ≤
      ENNReal.ofReal d₁ • volume.restrict (Ioo a b) := by
    intro S
    calc
      _ ≤ ENNReal.ofReal θ*(ENNReal.ofReal d₁ • volume.restrict (Ioo a b)) S :=
        mul_le_mul_of_nonneg_left (h₁ S) (by positivity)
      _ ≤ _ := by
        simpa only [Measure.smul_apply,smul_eq_mul,one_mul] using
          mul_le_mul_of_nonneg_right (show ENNReal.ofReal θ ≤ 1 by
            simpa using ENNReal.ofReal_le_ofReal hθ.2) (by positivity)
  refine (add_le_add hh₀ hh₁).trans_eq ?_
  rw [←add_smul,ENNReal.ofReal_add hd₀ hd₁]

end QuantitativePaper
