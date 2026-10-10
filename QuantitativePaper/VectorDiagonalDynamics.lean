module
public import QuantitativePaper.VectorGaussianDiagonalShift
public import QuantitativePaper.VectorMeasureState

@[expose] public section

/-! The independent common diagonal completion noise changes the Parisi
potential by a spatial constant and leaves its actual gradient and
same-Wiener diffusion unchanged. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace QuantitativePaper
open FourPapersCommon
variable {n : ℕ}
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem vectorMeasureGradient_diagonal_shift (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n) :
    vectorMeasureGradient μ β t q p x = vectorMeasureGradient μ β t q (p.1,0) x := by
  have hd := (hasFDerivAt_vectorMeasureTailPotential μ β t ht q (p.1,0) x).const_add
    (β*Real.sqrt t*p.2)
  have he : (fun y => β*Real.sqrt t*p.2 + vectorMeasureTailPotential μ β t q (p.1,0) y) =
      vectorMeasureTailPotential μ β t q p := by
    funext y
    exact (vectorMeasureTailPotential_diagonal_shift μ β t ht q p y).symm
  rw [he] at hd
  exact (InnerProductSpace.toDual ℝ (Field n)).injective
    ((hasFDerivAt_vectorMeasureTailPotential μ β t ht q p x).unique hd)

def vectorRemoveDiagonalSample (sample : VectorDisorderBrownianSample n) :
    VectorDisorderBrownianSample n := ((sample.1.1,0),sample.2)

theorem measurable_vectorRemoveDiagonalSample : Measurable (vectorRemoveDiagonalSample (n:=n)) := by
  exact ((measurable_fst.comp measurable_fst).prodMk measurable_const).prodMk measurable_snd

theorem vectorMeasureState_diagonal_shift (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (r : ℝ≥0) (hr : r≤1)
    (sample : VectorDisorderBrownianSample n) :
    vectorMeasureState μ β t ht r sample =
      vectorMeasureState μ β t ht r (vectorRemoveDiagonalSample sample) := by
  let d := vectorMeasureDriftData (n:=n) μ β t ht
  let σ := Real.sqrt ((1-t)*β^2)
  let p := vectorRemoveDiagonalSample sample
  let Y := fun s : ℝ => (vectorAdditiveCorrection d σ 0 1 p).compProj s
  have hY : Continuous Y := ODE.FunSpace.continuous_compProj _
  have hDrift (s : ℝ) (y : Field n) :
      vectorNoiseCorrectionDrift d (vectorAdditiveNoiseReal σ) sample s y =
        vectorNoiseCorrectionDrift d (vectorAdditiveNoiseReal σ) p s y := by
    unfold vectorNoiseCorrectionDrift
    change ((1-t)*β^2*Paper.parisiCDF μ (s.toNNReal:ℝ)) •
      vectorMeasureGradient μ β t (projIcc (0:ℝ) 1 zero_le_one (s.toNNReal:ℝ)) sample.1
        (y+vectorAdditiveNoiseReal σ s sample) = _
    rw [vectorMeasureGradient_diagonal_shift μ β t ht]
    rfl
  have hYe (s : ℝ) (hs : s∈Icc (0:ℝ) 1) :
      Y s=0+∫u in 0..s,vectorNoiseCorrectionDrift d (vectorAdditiveNoiseReal σ) sample u (Y u) := by
    have he := VectorIntegralPicard.solution_compProj_equation (show (0:ℝ)≤1 by norm_num)
      (isBounded_vectorNoiseCorrectionDrift d (vectorAdditiveNoiseReal σ)
        (continuous_vectorAdditiveNoiseReal σ) p) (x0:=(0:Field n)) hs
    change Y s=0+∫u in 0..s,vectorNoiseCorrectionDrift d (vectorAdditiveNoiseReal σ) p u (Y u) at he
    simpa only [hDrift] using he
  have he := VectorIntegralPicard.real_solution_unique
    (h:=(0:Field n)) (T:=(1:ℝ)) zero_le_one
    (isBounded_vectorNoiseCorrectionDrift d (vectorAdditiveNoiseReal σ)
      (continuous_vectorAdditiveNoiseReal σ) sample)
    Y hY hYe r ⟨r.coe_nonneg,by exact_mod_cast hr⟩
  change Y r = (vectorAdditiveCorrection d σ 0 1 sample).compProj r at he
  change (vectorAdditiveCorrection d σ 0 1 sample).compProj r +
      σ • disorderVectorBrownian r sample =
    (vectorAdditiveCorrection d σ 0 1 p).compProj r + σ • disorderVectorBrownian r p
  rw [←he]
  rfl

end QuantitativePaper
