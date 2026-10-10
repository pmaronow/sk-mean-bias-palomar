module
public import QuantitativePaper.VectorNoiseStatePath

@[expose] public section

/-! Pathwise uniqueness for the genuine continuous-noise Picard realization. -/
noncomputable section
open Set MeasureTheory FourPapersCommon
open scoped NNReal
namespace QuantitativePaper
set_option maxHeartbeats 1600000
variable {n : ℕ}

theorem vectorNoiseStatePath_unique (d : VectorAdditiveDriftData n) (σ : ℝ)
    (T : ℝ≥0) (z : VectorNoiseInitialData n) (X : ℝ→Field n)
    (hX : Continuous X)
    (he : ∀r∈Icc (0:ℝ) T,X r=z.1.2+σ • vectorContinuousNoise z.2 r+
      ∫s in 0..r,d.drift s.toNNReal z.1.1 (X s)) :
    ∀r∈Icc (0:ℝ) T,X r=vectorNoiseStatePath d σ T z r := by
  let Y : ℝ→Field n := fun r=>X r-z.1.2-σ • vectorContinuousNoise z.2 r
  have hY : Continuous Y := (hX.sub continuous_const).sub
    ((continuous_vectorContinuousNoise.comp (continuous_id.prodMk continuous_const)).const_smul σ)
  have hYe : ∀r∈Icc (0:ℝ) T,Y r=(0:Field n)+
      ∫s in 0..r,vectorContinuousNoiseDrift d σ z s (Y s) := by
    intro r hr
    have hi : (∫s in 0..r,vectorContinuousNoiseDrift d σ z s (Y s))=
        ∫s in 0..r,d.drift s.toNNReal z.1.1 (X s) := by
      congr 1
      funext s
      dsimp only [vectorContinuousNoiseDrift,Y]
      congr 1
      abel
    rw [hi,zero_add]
    dsimp only [Y]
    rw [he r hr]
    abel
  have hu:=VectorIntegralPicard.real_solution_unique (h:=(0:Field n)) T.coe_nonneg
    (bounded_vectorContinuousNoiseDrift d σ z) Y hY hYe
  intro r hr
  have hh:=hu r hr
  dsimp only [Y] at hh
  unfold vectorNoiseStatePath
  rw [←hh]
  abel

end QuantitativePaper
